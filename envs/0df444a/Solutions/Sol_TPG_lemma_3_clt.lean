-- Prove2me | solution 1 for TPG.lemma_3_clt
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T05:04:11.63388+00:00
-- url     : https://prove2.me/submissions/769a8b27-2efd-4382-a0d8-828a3e29dae1

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference
import Theorems.Thm_TPG_exists_mds_decomposition
import Theorems.Thm_TPG_variance_sum_window_le
import Theorems.Thm_TPG_tendstoNormal_of_charFun
import Theorems.Thm_TPG_isProbabilityMeasure_trajLaw
import Theorems.Thm_Martingale_norm_charFun_sub_const_le
import Theorems.Thm_Martingale_integral_sq_sum_eq_sum_integral_sq

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

open TPG

/-! ### Generic analytic and probabilistic helpers -/

/-- `|e^{-x} - e^{-y}| ≤ |x - y|` for nonnegative `x, y`. -/
lemma tpgclt_abs_exp_neg_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · have h := this hy hx (le_of_not_ge hxy)
    rwa [abs_sub_comm, abs_sub_comm x y]
  have h1 : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  have h2 : Real.exp (-y) = Real.exp (-x) * Real.exp (-(y - x)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : 1 - (y - x) ≤ Real.exp (-(y - x)) := by
    have := Real.add_one_le_exp (-(y - x)); linarith
  have h4 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h5 : 0 < Real.exp (-x) := Real.exp_pos _
  nlinarith [mul_nonneg h5.le (sub_nonneg.2 h3), mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 hxy)]

/-- `E|X - v| ≤ √Var(X) + |E X - v|` on a probability space. -/
lemma tpgclt_integral_abs_sub_le {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P) (v : ℝ) :
    ∫ ω, |X ω - v| ∂P ≤ Real.sqrt (variance X P) + |∫ ω, X ω ∂P - v| := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ∫ ω, X ω ∂P := ⟨_, rfl⟩
  rw [← hm]
  have hY : MemLp (fun ω => |X ω - m|) 2 P := by
    have h := (hX.sub (memLp_const m)).norm
    simpa [Real.norm_eq_abs] using h
  have hYi : Integrable (fun ω => |X ω - m|) P := hY.integrable one_le_two
  have h1 : (∫ ω, |X ω - m| ∂P) ^ 2 ≤ variance X P := by
    have hv := variance_nonneg (fun ω => |X ω - m|) P
    rw [variance_eq_sub hY] at hv
    have h2 : (∫ ω, ((fun ω => |X ω - m|) ^ 2) ω ∂P) = variance X P := by
      rw [variance_eq_integral hX.aemeasurable, ← hm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp [sq_abs]
    linarith
  have h3 : ∫ ω, |X ω - m| ∂P ≤ Real.sqrt (variance X P) :=
    (le_abs_self _).trans (Real.abs_le_sqrt h1)
  calc ∫ ω, |X ω - v| ∂P ≤ ∫ ω, (|X ω - m| + |m - v|) ∂P := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _)
          (hYi.add (integrable_const _)) (Filter.Eventually.of_forall fun ω => ?_)
        exact abs_sub_le (X ω) m v
    _ = ∫ ω, |X ω - m| ∂P + |m - v| := by
        rw [integral_add hYi (integrable_const _), integral_const, probReal_univ, one_smul]
    _ ≤ _ := by linarith

/-- The filtration `ℱ` shifted by one step, with the trivial sigma-algebra in position `0`. -/
@[instance_reducible]
def tpgcltShift {Ω : Type*} {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0) :
    ℕ → MeasurableSpace Ω
  | 0 => ⊥
  | (i + 1) => ℱ i

/-- Orthogonality of bounded martingale differences (indexing adapted to this file). -/
lemma tpgclt_integral_sq_sum {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hadapt : ∀ j, Measurable[ℱ j] (D j))
    (hmds : ∀ j, P[D (j + 1) | ℱ j] =ᵐ[P] 0) (hcent : ∫ ω, D 0 ω ∂P = 0)
    (C : ℝ) (hbdd : ∀ j ω, |D j ω| ≤ C) (n : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range n, D j ω) ^ 2 ∂P
      = ∑ j ∈ Finset.range n, ∫ ω, (D j ω) ^ 2 ∂P := by
  let 𝒢 : Filtration ℕ m0 :=
    { seq := tpgcltShift ℱ
      mono' := monotone_nat_of_le_succ (fun j => by
        cases j with
        | zero => exact bot_le
        | succ i => exact ℱ.mono (Nat.le_succ i))
      le' := fun j => by
        cases j with
        | zero => exact bot_le
        | succ i => exact ℱ.le i }
  refine Martingale.integral_sq_sum_eq_sum_integral_sq P 𝒢 D ?_ ?_ ?_ n
  · intro j
    exact MemLp.of_bound ((hadapt j).mono (ℱ.le j) le_rfl).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbdd j ω)
  · intro j
    exact (hadapt j).stronglyMeasurable
  · intro j
    cases j with
    | zero =>
      change P[D 0 | ⊥] =ᵐ[P] 0
      rw [condExp_bot]
      exact Filter.Eventually.of_forall fun ω => by simpa using hcent
    | succ i => exact hmds i

/-- Characteristic-function bound for the normalized sum of a bounded martingale difference
sequence, in terms of the `L¹` distance of the normalized sum of squares from `v`. -/
lemma tpgclt_charFun_bound {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hadapt : ∀ j, Measurable[ℱ j] (D j))
    (hmds : ∀ j, P[D (j + 1) | ℱ j] =ᵐ[P] 0) (hcent : ∫ ω, D 0 ω ∂P = 0)
    (C : ℝ) (hbdd : ∀ j ω, |D j ω| ≤ C) (n : ℕ) (hn : 0 < n) (t v : ℝ) (hv : 0 ≤ v)
    (hsmall : |t| * C ≤ Real.sqrt n) :
    ‖(∫ ω, Complex.exp (Complex.I * (t : ℂ) *
          (((∑ j ∈ Finset.range n, D j ω) / Real.sqrt n : ℝ) : ℂ)) ∂P)
        - Complex.exp (-((v : ℂ) * (t : ℂ) ^ 2) / 2)‖
      ≤ Real.exp (t ^ 2 * C ^ 2 / 2) *
          (|t| ^ 3 * C ^ 3 / Real.sqrt n
            + t ^ 2 / 2 *
              ∫ ω, |(1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (D j ω) ^ 2 - v| ∂P) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt n := ⟨_, rfl⟩
  rw [← hs] at hsmall ⊢
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.2 hn'
  have hss : s * s = n := by rw [hs]; exact Real.mul_self_sqrt hn'.le
  have hDm : ∀ j, Measurable (D j) := fun j => (hadapt j).mono (ℱ.le j) le_rfl
  obtain ⟨Zf, hZf⟩ : ∃ Zf : ℕ → Ω → ℝ, ∀ j ω, Zf j ω = D j ω / s := ⟨_, fun _ _ => rfl⟩
  have hZfun : ∀ j, Zf j = fun ω => D j ω / s := fun j => funext (hZf j)
  have hZm : ∀ j, Measurable[ℱ j] (Zf j) := fun j => by
    rw [hZfun j]; exact (hadapt j).div_const s
  have hZm' : ∀ j, Measurable (Zf j) := fun j => (hZm j).mono (ℱ.le j) le_rfl
  have hZb : ∀ j ω, |Zf j ω| ≤ C / s := fun j ω => by
    rw [hZf, abs_div, abs_of_pos hs0]
    exact div_le_div_of_nonneg_right (hbdd j ω) hs0.le
  have hZi : ∀ j, Integrable (Zf j) P := fun j =>
    Integrable.of_bound (hZm' j).aestronglyMeasurable (C / s)
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hZb j ω)
  have hZmds : ∀ j, P[Zf (j + 1) | ℱ j] =ᵐ[P] 0 := fun j => by
    have h1 : Zf (j + 1) = (1 / s) • D (j + 1) := by
      ext ω; simp [hZf, div_eq_inv_mul]
    rw [h1]
    refine (condExp_smul (1 / s) (D (j + 1)) (ℱ j)).trans ?_
    filter_upwards [hmds j] with ω hω
    simp [hω]
  have hZc : ∫ ω, Zf 0 ω ∂P = 0 := by
    rw [hZfun 0, integral_div, hcent, zero_div]
  have hsq : ∀ ω, ∑ j ∈ Finset.range n, Zf j ω ^ 2
      = (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (D j ω) ^ 2 := by
    intro ω
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hZf, div_pow, sq s, hss]; ring
  have hDsq : ∀ ω, ∑ j ∈ Finset.range n, (D j ω) ^ 2 ≤ n * C ^ 2 := by
    intro ω
    calc ∑ j ∈ Finset.range n, (D j ω) ^ 2 ≤ ∑ j ∈ Finset.range n, C ^ 2 :=
          Finset.sum_le_sum fun j _ => by
            have h := hbdd j ω
            exact sq_le_sq' (by linarith [(abs_le.1 h).1]) (abs_le.1 h).2
      _ = n * C ^ 2 := by simp
  have hvar : ∀ ω, ∑ j ∈ Finset.range n, Zf j ω ^ 2 ≤ C ^ 2 := by
    intro ω
    rw [hsq, one_div, inv_mul_le_iff₀ hn']
    exact hDsq ω
  have hsm : ∀ j ∈ Finset.range n, ∀ ω, |t * Zf j ω| ≤ |t| * C / s := by
    intro j _ ω
    rw [abs_mul]
    calc |t| * |Zf j ω| ≤ |t| * (C / s) := mul_le_mul_of_nonneg_left (hZb j ω) (abs_nonneg t)
      _ = |t| * C / s := by ring
  have hsm1 : ∀ j ∈ Finset.range n, ∀ ω, |t * Zf j ω| ≤ 1 := fun j hj ω =>
    (hsm j hj ω).trans (by rw [div_le_one hs0]; exact hsmall)
  have key := Martingale.norm_charFun_sub_const_le P ℱ Zf hZm' hZm hZi hZmds hZc (C / s) hZb
    t (C ^ 2) n hvar hsm1 (Complex.exp (-((v : ℂ) * (t : ℂ) ^ 2) / 2))
  have hsum : ∀ ω, ∑ j ∈ Finset.range n, Zf j ω = (∑ j ∈ Finset.range n, D j ω) / s := fun ω => by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => hZf j ω
  simp only [hsum] at key
  refine key.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  have hc : Complex.exp (-((v : ℂ) * (t : ℂ) ^ 2) / 2)
      = ((Real.exp (-(t ^ 2 * v / 2)) : ℝ) : ℂ) := by
    push_cast; ring_nf
  have hQm : Measurable (fun ω => (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (D j ω) ^ 2) :=
    measurable_const.mul (Finset.measurable_sum _ fun j _ => (hDm j).pow_const 2)
  have hQ0 : ∀ ω, 0 ≤ (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (D j ω) ^ 2 := fun ω =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hQ1 : ∀ ω, (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (D j ω) ^ 2 ≤ C ^ 2 := fun ω => by
    rw [one_div, inv_mul_le_iff₀ hn']; exact hDsq ω
  have hQi : Integrable
      (fun ω => |(1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (D j ω) ^ 2 - v|) P := by
    refine Integrable.of_bound (hQm.sub measurable_const).abs.aestronglyMeasurable (C ^ 2 + v)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    constructor <;> nlinarith [hQ0 ω, hQ1 ω, sq_nonneg C]
  calc ∫ ω, ((∑ k ∈ Finset.range n, |t * Zf k ω| ^ 3)
          + ‖((Real.exp (-(t ^ 2 * ∑ k ∈ Finset.range n, Zf k ω ^ 2) / 2) : ℝ) : ℂ)
              - Complex.exp (-((v : ℂ) * (t : ℂ) ^ 2) / 2)‖) ∂P
      ≤ ∫ ω, (|t| ^ 3 * C ^ 3 / s
          + t ^ 2 / 2 * |(1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (D j ω) ^ 2 - v|) ∂P := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_)
          ((integrable_const _).add (hQi.const_mul _)) (Filter.Eventually.of_forall fun ω => ?_)
        · exact add_nonneg (Finset.sum_nonneg fun j _ => by positivity) (norm_nonneg _)
        · refine add_le_add ?_ ?_
          · calc ∑ k ∈ Finset.range n, |t * Zf k ω| ^ 3
                ≤ ∑ k ∈ Finset.range n, (|t| * C / s) ^ 3 :=
                  Finset.sum_le_sum fun j hj =>
                    pow_le_pow_left₀ (abs_nonneg _) (hsm j hj ω) 3
              _ = n * (|t| * C / s) ^ 3 := by simp
              _ = |t| ^ 3 * C ^ 3 / s := by rw [← hss]; field_simp
          · rw [hc, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hsq]
            have h := tpgclt_abs_exp_neg_sub_le
              (x := t ^ 2 * ((1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (D j ω) ^ 2) / 2)
              (y := t ^ 2 * v / 2)
              (by have := hQ0 ω; positivity) (by positivity)
            have h2 : -(t ^ 2 * ((1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (D j ω) ^ 2)) / 2
                = -(t ^ 2 * ((1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (D j ω) ^ 2) / 2) := by ring
            have h3 : ∀ q : ℝ, |t ^ 2 * q / 2 - t ^ 2 * v / 2| = t ^ 2 / 2 * |q - v| := fun q => by
              rw [show t ^ 2 * q / 2 - t ^ 2 * v / 2 = t ^ 2 / 2 * (q - v) by ring, abs_mul,
                abs_of_nonneg (by positivity)]
            rw [h2]
            exact h.trans (le_of_eq (h3 _))
    _ = |t| ^ 3 * C ^ 3 / s
          + t ^ 2 / 2 * ∫ ω, |(1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (D j ω) ^ 2 - v| ∂P := by
        rw [integral_add (integrable_const _) (hQi.const_mul _), integral_const, probReal_univ,
          one_smul, integral_const_mul]

/-! ### TPG-specific helpers -/

/-- The TPG estimator at `θ = 1/2` is the sample mean of the reward-time summands `B_t`. -/
lemma tpgclt_tpgEst_eq {S : Type} [Fintype S] (T k : ℕ) (ω : Traj S T) :
    tpgEst (1 / 2) T k ω = (1 / (T : ℝ)) * ∑ t : Fin T, Bt k t ω := by
  unfold tpgEst Bt
  congr 1
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hs : score (1 / 2) (Z u ω) = ipw (Z u ω) := by
    unfold score ipw; cases Z u ω <;> norm_num
  rw [hs]
  split_ifs <;> simp

lemma tpgclt_measurable_sumBt {S : Type} [Fintype S] [MeasurableSpace S] (T k : ℕ) :
    Measurable (fun ω : Traj S T => ∑ t : Fin T, Bt k t ω) := by
  refine Finset.measurable_sum _ fun t _ => ?_
  unfold Bt
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.ite (MeasurableSet.const _) ?_ measurable_const
  have hZ : Measurable (Z (S := S) i) := by unfold Z; exact (measurable_pi_apply i).snd.fst
  have hY : Measurable (Y (S := S) t) := by unfold Y; exact (measurable_pi_apply t).snd.snd
  exact ((Measurable.of_discrete (f := ipw)).comp hZ).mul hY

lemma tpgclt_sigmaWindow_mono {S : Type} [Fintype S] [MeasurableSpace S] (T : ℕ)
    {a b a' b' : ℕ} (ha : a' ≤ a) (hb : b ≤ b') :
    sigmaWindow (S := S) T a b ≤ sigmaWindow T a' b' := by
  unfold sigmaWindow
  refine iSup_mono fun t => iSup_le fun h => ?_
  exact le_iSup_of_le ⟨ha.trans h.1, h.2.trans hb⟩ le_rfl

lemma tpgclt_sigmaWindow_le {S : Type} [Fintype S] [MeasurableSpace S] (T a b : ℕ) :
    sigmaWindow (S := S) T a b ≤ (MeasurableSpace.pi : MeasurableSpace (Traj S T)) := by
  unfold sigmaWindow
  exact iSup_le fun t => iSup_le fun _ => (measurable_pi_apply t).comap_le

/-- The filtration `j ↦ F_0^j` on trajectories. -/
def tpgcltFilt (S : Type) [Fintype S] [MeasurableSpace S] (T : ℕ) :
    Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (Traj S T)) where
  seq j := sigmaWindow T 0 j
  mono' := fun _ _ hij => tpgclt_sigmaWindow_mono T le_rfl hij
  le' := fun j => tpgclt_sigmaWindow_le T 0 j

/-- Quantitative characteristic-function bound at a fixed horizon `T ≥ 1`. -/
lemma tpgclt_bound {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (k : ℕ) (γ M : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (T : ℕ) (hT : 0 < T)
    (hmix : E.Mixing T γ) (hM : E.RewardBound M)
    (C : ℝ) (D : ℕ → Traj S T → ℝ)
    (hDm : ∀ j : ℕ, Measurable[sigmaWindow T (j - (k + 1)) j] (D j))
    (hDb : ∀ (j : ℕ) (ω : Traj S T), |D j ω| ≤ C)
    (hD0 : ∫ ω, D 0 ω ∂(E.expLaw T (1 / 2)) = 0)
    (hDc : ∀ j : ℕ, (E.expLaw T (1 / 2))[D (j + 1) | sigmaWindow T 0 j]
              =ᵐ[E.expLaw T (1 / 2)] 0)
    (hDs : ∀ᵐ ω ∂(E.expLaw T (1 / 2)),
            ∑ j ∈ Finset.range T, D j ω
              = (∑ t : Fin T, Bt k t ω) - ∫ ω', ∑ t : Fin T, Bt k t ω' ∂(E.expLaw T (1 / 2)))
    (t v : ℝ) (hv : 0 ≤ v) (hsmall : |t| * C ≤ Real.sqrt T) :
    ‖(∫ ω, Complex.exp (Complex.I * (t : ℂ) *
          ((Real.sqrt (T : ℝ) * (tpgEst (1 / 2) T k ω
              - ∫ ω', tpgEst (1 / 2) T k ω' ∂(E.expLaw T (1 / 2))) : ℝ) : ℂ))
          ∂(E.expLaw T (1 / 2)))
        - Complex.exp (-((v : ℂ) * (t : ℂ) ^ 2) / 2)‖
      ≤ Real.exp (t ^ 2 * C ^ 2 / 2) *
          (|t| ^ 3 * C ^ 3 / Real.sqrt T
            + t ^ 2 / 2 * (Real.sqrt (C ^ 4 * (2 * ((k + 1 : ℕ) : ℝ) + 3 + 8 / (1 - γ)) / T)
                + |E.normVar T k - v|)) := by
  have hprob : IsProbabilityMeasure (E.expLaw T (1 / 2)) := by
    unfold Env.expLaw
    exact isProbabilityMeasure_trajLaw E T (fun _ => 1 / 2) (fun _ => ⟨by norm_num, by norm_num⟩)
  have hnv : E.normVar T k
      = (1 / (T : ℝ)) * variance (fun ω : Traj S T => ∑ t : Fin T, Bt k t ω)
          (E.expLaw T (1 / 2)) := rfl
  have hwin := variance_sum_window_le E T (k + 1) (1 / 2) γ M (C ^ 2) (by norm_num) (by norm_num)
    hγ0 hγ1 hmix hM (fun j ω => (D j ω) ^ 2) (fun j => (hDm j).pow_const 2)
    (fun j ω => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hDb j ω) 2)
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (Traj S T), μ = E.expLaw T (1 / 2) := ⟨_, rfl⟩
  rw [← hμ] at hD0 hDc hDs hnv hwin hprob ⊢
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hBm : Measurable (fun ω : Traj S T => ∑ t : Fin T, Bt k t ω) :=
    tpgclt_measurable_sumBt T k
  -- the statistic in terms of the centred sum of the `B_t`
  have hW : ∀ ω : Traj S T,
      Real.sqrt (T : ℝ) * (tpgEst (1 / 2) T k ω - ∫ ω', tpgEst (1 / 2) T k ω' ∂μ)
      = ((∑ t : Fin T, Bt k t ω) - ∫ ω', ∑ t : Fin T, Bt k t ω' ∂μ) / Real.sqrt T := by
    intro ω
    have h1 : ∫ ω', tpgEst (1 / 2) T k ω' ∂μ
        = (1 / (T : ℝ)) * ∫ ω', ∑ t : Fin T, Bt k t ω' ∂μ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω' => tpgclt_tpgEst_eq T k ω')
    rw [h1, tpgclt_tpgEst_eq]
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt T := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.2 hT'
    have hss : (T : ℝ) = s * s := by rw [hs]; exact (Real.mul_self_sqrt hT'.le).symm
    rw [← hs, hss]
    field_simp
  have hadapt : ∀ j, Measurable[(tpgcltFilt S T) j] (D j) := fun j =>
    (hDm j).mono (tpgclt_sigmaWindow_mono T (Nat.zero_le _) le_rfl) le_rfl
  have hmds : ∀ j, μ[D (j + 1) | (tpgcltFilt S T) j] =ᵐ[μ] 0 := hDc
  have key := tpgclt_charFun_bound μ (tpgcltFilt S T) D hadapt hmds hD0 C hDb T hT t v hv hsmall
  have hint_eq : ∫ ω, Complex.exp (Complex.I * (t : ℂ) *
        ((Real.sqrt (T : ℝ) * (tpgEst (1 / 2) T k ω
            - ∫ ω', tpgEst (1 / 2) T k ω' ∂μ) : ℝ) : ℂ)) ∂μ
      = ∫ ω, Complex.exp (Complex.I * (t : ℂ) *
        (((∑ j ∈ Finset.range T, D j ω) / Real.sqrt T : ℝ) : ℂ)) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hDs] with ω hω
    rw [hω, hW ω]
  rw [hint_eq]
  refine key.trans ?_
  have hDmeas : ∀ j, Measurable (D j) := fun j =>
    (hadapt j).mono ((tpgcltFilt S T).le j) le_rfl
  have hDsq_int : ∀ j, Integrable (fun ω => (D j ω) ^ 2) μ := fun j =>
    Integrable.of_bound ((hDmeas j).pow_const 2).aestronglyMeasurable (C ^ 2)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hDb j ω) 2)
  have hQm : Measurable (fun ω => (1 / (T : ℝ)) * ∑ j ∈ Finset.range T, (D j ω) ^ 2) :=
    measurable_const.mul (Finset.measurable_sum _ fun j _ => (hDmeas j).pow_const 2)
  have hQmem : MemLp (fun ω => (1 / (T : ℝ)) * ∑ j ∈ Finset.range T, (D j ω) ^ 2) 2 μ := by
    refine MemLp.of_bound hQm.aestronglyMeasurable (C ^ 2) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => sq_nonneg _)), one_div,
      inv_mul_le_iff₀ hT']
    calc ∑ j ∈ Finset.range T, (D j ω) ^ 2 ≤ ∑ j ∈ Finset.range T, C ^ 2 :=
          Finset.sum_le_sum fun j _ => by
            have h := hDb j ω
            exact sq_le_sq' (by linarith [(abs_le.1 h).1]) (abs_le.1 h).2
      _ = T * C ^ 2 := by simp
  have hL1 := tpgclt_integral_abs_sub_le μ _ hQmem v
  have hVar : variance (fun ω => (1 / (T : ℝ)) * ∑ j ∈ Finset.range T, (D j ω) ^ 2) μ
      ≤ C ^ 4 * (2 * ((k + 1 : ℕ) : ℝ) + 3 + 8 / (1 - γ)) / T := by
    rw [variance_const_mul]
    calc (1 / (T : ℝ)) ^ 2 * variance (fun ω => ∑ j ∈ Finset.range T, (D j ω) ^ 2) μ
        ≤ (1 / (T : ℝ)) ^ 2
            * ((T : ℝ) * (C ^ 2) ^ 2 * (2 * ((k + 1 : ℕ) : ℝ) + 3 + 8 / (1 - γ))) :=
          mul_le_mul_of_nonneg_left hwin (by positivity)
      _ = C ^ 4 * (2 * ((k + 1 : ℕ) : ℝ) + 3 + 8 / (1 - γ)) / T := by
          field_simp
  have hmean : ∫ ω, (1 / (T : ℝ)) * ∑ j ∈ Finset.range T, (D j ω) ^ 2 ∂μ = E.normVar T k := by
    rw [integral_const_mul, integral_finsetSum _ (fun j _ => hDsq_int j),
      ← tpgclt_integral_sq_sum μ (tpgcltFilt S T) D hadapt hmds hD0 C hDb T, hnv,
      variance_eq_integral hBm.aemeasurable]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hDs] with ω hω
    rw [hω]
  have hfin : ∫ ω, |(1 / (T : ℝ)) * ∑ j ∈ Finset.range T, (D j ω) ^ 2 - v| ∂μ
      ≤ Real.sqrt (C ^ 4 * (2 * ((k + 1 : ℕ) : ℝ) + 3 + 8 / (1 - γ)) / T)
        + |E.normVar T k - v| := by
    rw [hmean] at hL1
    exact hL1.trans (add_le_add (Real.sqrt_le_sqrt hVar) le_rfl)
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hfin (by positivity))) (Real.exp_pos _).le

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (k : ℕ) (γ M v : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hmix : ∀ T : ℕ, E.Mixing T γ) (hM : E.RewardBound M)
    (hvar : E.AsymptoticVariance k v) :
    E.TendstoNormal
      (fun (T : ℕ) (ω : Traj S T) =>
        Real.sqrt (T : ℝ) *
          (tpgEst (1 / 2) T k ω - ∫ ω', tpgEst (1 / 2) T k ω' ∂(E.expLaw T (1 / 2))))
      v := by
  obtain ⟨C, -, hD⟩ := exists_mds_decomposition E k γ M hγ0 hγ1 hmix hM
  refine tendstoNormal_of_charFun E _ ?_ v hvar.1.le ?_
  · intro T
    have h : (fun ω : Traj S T => tpgEst (1 / 2) T k ω)
        = fun ω => (1 / (T : ℝ)) * ∑ t : Fin T, Bt k t ω := funext (tpgclt_tpgEst_eq T k)
    have hm : Measurable (fun ω : Traj S T => tpgEst (1 / 2) T k ω) := by
      rw [h]; exact measurable_const.mul (tpgclt_measurable_sumBt T k)
    exact measurable_const.mul (hm.sub measurable_const)
  · intro t
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsqrt : Filter.Tendsto (fun T : ℕ => Real.sqrt (T : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hlim : Filter.Tendsto (fun T : ℕ => Real.exp (t ^ 2 * C ^ 2 / 2) *
          (|t| ^ 3 * C ^ 3 / Real.sqrt T
            + t ^ 2 / 2 * (Real.sqrt (C ^ 4 * (2 * ((k + 1 : ℕ) : ℝ) + 3 + 8 / (1 - γ)) / T)
                + |E.normVar T k - v|))) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun T : ℕ => |t| ^ 3 * C ^ 3 / Real.sqrt T) Filter.atTop
          (nhds 0) := tendsto_const_nhds.div_atTop hsqrt
      have h2 : Filter.Tendsto
          (fun T : ℕ => Real.sqrt (C ^ 4 * (2 * ((k + 1 : ℕ) : ℝ) + 3 + 8 / (1 - γ)) / T))
          Filter.atTop (nhds 0) := by
        have h := (Real.continuous_sqrt.tendsto 0).comp
          ((tendsto_const_nhds (x := C ^ 4 * (2 * ((k + 1 : ℕ) : ℝ) + 3 + 8 / (1 - γ)))).div_atTop
            (tendsto_natCast_atTop_atTop (R := ℝ)))
        rw [Real.sqrt_zero] at h
        exact h
      have h3 : Filter.Tendsto (fun T : ℕ => |E.normVar T k - v|) Filter.atTop (nhds 0) := by
        have h := (hvar.2.sub_const v).abs
        rwa [sub_self, abs_zero] at h
      have h4 := (h1.add ((h2.add h3).const_mul (t ^ 2 / 2))).const_mul
        (Real.exp (t ^ 2 * C ^ 2 / 2))
      rw [show (0 : ℝ) = Real.exp (t ^ 2 * C ^ 2 / 2) * (0 + t ^ 2 / 2 * (0 + 0)) by ring]
      exact h4
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [hsqrt.eventually_ge_atTop (|t| * C), Filter.eventually_gt_atTop 0]
      with T hT1 hT0
    obtain ⟨D, hDm, hDb, hD0, hDc, hDs⟩ := hD T
    exact tpgclt_bound E k γ M hγ0 hγ1 T hT0 (hmix T) hM C D hDm hDb hD0 hDc hDs t v
      hvar.1.le hT1

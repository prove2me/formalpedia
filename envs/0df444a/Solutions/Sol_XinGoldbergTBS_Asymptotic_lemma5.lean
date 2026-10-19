-- Prove2me | solution 1 for XinGoldbergTBS.Asymptotic.lemma5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T11:01:29.436973+00:00
-- url     : https://prove2.me/submissions/f5d2d6ca-b090-454a-b32d-8df2bf0cb06c

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants
import Definitions.Def_XinGoldbergTBS_Asymptotic_RandomWalk

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace XG5

open XinGoldbergTBS.Asymptotic

lemma ae_nonneg (μ : DemandLaw) : ∀ᵐ d ∂μ.law, 0 ≤ d := by
  have h := μ.nonneg
  rw [measure_eq_zero_iff_ae_notMem] at h
  filter_upwards [h] with d hd
  simpa using hd


lemma phi_nonneg (μ : DemandLaw) (ϵ θ : ℝ) : 0 ≤ phi μ ϵ θ :=
  mul_nonneg (Real.exp_pos _).le (integral_nonneg fun d => (Real.exp_pos _).le)

lemma gamma_le_phi (μ : DemandLaw) (ϵ θ : ℝ) (hθ : 0 ≤ θ) : gamma μ ϵ ≤ phi μ ϵ θ := by
  unfold gamma
  exact ciInf_le (f := fun t : Set.Ici (0 : ℝ) => phi μ ϵ t)
    ⟨0, by rintro _ ⟨t, rfl⟩; exact phi_nonneg _ _ _⟩ ⟨θ, hθ⟩

lemma gamma_nonneg (μ : DemandLaw) (ϵ : ℝ) : 0 ≤ gamma μ ϵ := by
  unfold gamma
  have : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.mem_Ici.mpr le_rfl⟩⟩
  exact le_ciInf fun t => phi_nonneg _ _ _

lemma exists_trunc (μ : DemandLaw) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 1 ≤ K ∧ μ.mean - δ < ∫ d, min d K ∂μ.law := by
  have ht : Tendsto (fun n : ℕ => ∫ d, min d ((n : ℝ) + 1) ∂μ.law) atTop
      (nhds (∫ d, d ∂μ.law)) := by
    refine tendsto_integral_of_dominated_convergence (fun d => |d|) (fun n => ?_)
      μ.integrable.abs (fun n => ?_) ?_
    · exact (measurable_id.min measurable_const).aestronglyMeasurable
    · filter_upwards [ae_nonneg μ] with d hd
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hd (by positivity))]
      exact (min_le_left _ _).trans (le_abs_self _)
    · refine Eventually.of_forall fun d => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
      have : d ≤ (n : ℝ) + 1 := by
        have := (Nat.le_ceil d).trans (Nat.cast_le.mpr hn)
        linarith
      exact (min_eq_left this).symm
  have hlt : μ.mean - δ < ∫ d, d ∂μ.law := by
    show μ.mean - δ < μ.mean; linarith
  obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds hlt)).exists
  exact ⟨(n : ℝ) + 1, by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)], hn⟩

lemma gamma_lt_one (μ : DemandLaw) (ϵ : ℝ) (hϵ : 0 < ϵ) : gamma μ ϵ < 1 := by
  obtain ⟨K, hK1, hK⟩ := exists_trunc μ (ϵ / 2) (by linarith)
  have hKpos : 0 < K := by linarith
  set θ := min (1 / K) (ϵ / (4 * K ^ 2)) with hθdef
  have hθpos : 0 < θ := lt_min (by positivity) (by positivity)
  have hθK : θ * K ≤ 1 := by
    have : θ ≤ 1 / K := min_le_left _ _
    calc θ * K ≤ 1 / K * K := mul_le_mul_of_nonneg_right this hKpos.le
      _ = 1 := by field_simp
  have hθ2 : θ * K ^ 2 ≤ ϵ / 4 := by
    have : θ ≤ ϵ / (4 * K ^ 2) := min_le_right _ _
    calc θ * K ^ 2 ≤ ϵ / (4 * K ^ 2) * K ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = ϵ / 4 := by field_simp
  have hpt : ∀ᵐ d ∂μ.law, Real.exp (-(θ * d)) ≤ 1 - θ * min d K + (θ * K) ^ 2 := by
    filter_upwards [ae_nonneg μ] with d hd
    have hm0 : 0 ≤ min d K := le_min hd hKpos.le
    have hu0 : 0 ≤ θ * min d K := mul_nonneg hθpos.le hm0
    have huK : θ * min d K ≤ θ * K := mul_le_mul_of_nonneg_left (min_le_right _ _) hθpos.le
    have hud : θ * min d K ≤ θ * d := mul_le_mul_of_nonneg_left (min_le_left _ _) hθpos.le
    have h1 : Real.exp (-(θ * d)) ≤ Real.exp (-(θ * min d K)) := Real.exp_le_exp.mpr (by linarith)
    have h2 := Real.abs_exp_sub_one_sub_id_le (x := -(θ * min d K))
      (by rw [abs_neg, abs_of_nonneg hu0]; linarith)
    have h3 := (abs_le.mp h2).2
    have h4 : (-(θ * min d K)) ^ 2 ≤ (θ * K) ^ 2 := by
      rw [neg_sq]; exact pow_le_pow_left₀ hu0 huK 2
    linarith
  have hint1 : Integrable (fun d => Real.exp (-(θ * d))) μ.law := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).measurable.aestronglyMeasurable
    · filter_upwards [ae_nonneg μ] with d hd
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hmin : Integrable (fun d => min d K) μ.law := by
    refine Integrable.mono' (μ.integrable.abs.add (integrable_const K)) ?_ ?_
    · exact (measurable_id.min measurable_const).aestronglyMeasurable
    · filter_upwards [ae_nonneg μ] with d hd
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hd hKpos.le)]
      have := (min_le_left d K).trans (le_abs_self d)
      simp only [Pi.add_apply, id]
      linarith
  have hint2 : Integrable (fun d => 1 - θ * min d K + (θ * K) ^ 2) μ.law :=
    ((integrable_const 1).sub (hmin.const_mul θ)).add (integrable_const _)
  have hE : ∫ d, Real.exp (-(θ * d)) ∂μ.law ≤ 1 - θ * ∫ d, min d K ∂μ.law + (θ * K) ^ 2 := by
    calc ∫ d, Real.exp (-(θ * d)) ∂μ.law ≤ ∫ d, (1 - θ * min d K + (θ * K) ^ 2) ∂μ.law :=
          integral_mono_ae hint1 hint2 hpt
      _ = 1 - θ * ∫ d, min d K ∂μ.law + (θ * K) ^ 2 := by
          rw [integral_add (f := fun d => 1 - θ * min d K) (g := fun _ => (θ * K) ^ 2)
            ((integrable_const 1).sub (hmin.const_mul θ)) (integrable_const _),
            integral_sub (f := fun _ => (1 : ℝ)) (g := fun d => θ * min d K)
              (integrable_const 1) (hmin.const_mul θ), integral_const_mul]
          simp
  have hlow : 1 - θ * (μ.mean - ϵ) ≤ Real.exp (-(θ * (μ.mean - ϵ))) := by
    linarith [Real.add_one_le_exp (-(θ * (μ.mean - ϵ)))]
  have hsq : (θ * K) ^ 2 = θ * (θ * K ^ 2) := by ring
  have hθ3 : θ * (θ * K ^ 2) ≤ θ * (ϵ / 4) := mul_le_mul_of_nonneg_left hθ2 hθpos.le
  have hK' : θ * (μ.mean - ϵ / 2) < θ * ∫ d, min d K ∂μ.law := mul_lt_mul_of_pos_left hK hθpos
  have hE' : ∫ d, Real.exp (-(θ * d)) ∂μ.law < Real.exp (-(θ * (μ.mean - ϵ))) := by
    nlinarith
  have hφ : phi μ ϵ θ < 1 := by
    unfold phi
    calc Real.exp (θ * (μ.mean - ϵ)) * ∫ d, Real.exp (-(θ * d)) ∂μ.law
        < Real.exp (θ * (μ.mean - ϵ)) * Real.exp (-(θ * (μ.mean - ϵ))) :=
          mul_lt_mul_of_pos_left hE' (Real.exp_pos _)
      _ = 1 := by rw [← Real.exp_add]; simp
  exact lt_of_le_of_lt (gamma_le_phi μ ϵ θ hθpos.le) hφ

lemma vartheta_ne_zero (μ : DemandLaw) (ϵ : ℝ) (hγ : gamma μ ϵ < 1) : vartheta μ ϵ ≠ 0 := by
  unfold vartheta
  split_ifs with h
  · obtain ⟨θ, hθ0, hθ⟩ := h
    intro h0
    have hle : ENNReal.ofReal θ ≤ ⨆ t ∈ phiMinimizers μ ϵ, ENNReal.ofReal t :=
      le_iSup₂_of_le (f := fun t (_ : t ∈ phiMinimizers μ ϵ) => ENNReal.ofReal t) θ ⟨hθ0, hθ⟩
        le_rfl
    rw [h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hle
    have : θ = 0 := le_antisymm hle hθ0
    subst this
    have h1 : phi μ ϵ 0 = 1 := by simp [phi]
    linarith
  · exact ENNReal.top_ne_zero


/-- Reading finitely many distinct coordinates of an i.i.d. path gives the product law. -/
lemma mp_idx (μ : DemandLaw) (k : ℕ) (σ : Fin k → ℕ) (hσ : Function.Injective σ) :
    MeasurePreserving (fun p : Path => fun j : Fin k => p (σ j))
      (pathLaw μ) (Measure.pi fun _ : Fin k => μ.law) := by
  refine ⟨by fun_prop, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  classical
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  set T : ℕ → Set ℝ := fun n => if h : ∃ j, σ j = n then s h.choose else Set.univ with hTdef
  have hT : ∀ j : Fin k, T (σ j) = s j := by
    intro j
    have hex : ∃ j', σ j' = σ j := ⟨j, rfl⟩
    simp only [hTdef, dif_pos hex]
    rw [hσ hex.choose_spec]
  have hpre : (fun p : Path => fun j : Fin k => p (σ j)) ⁻¹' Set.univ.pi s =
      Set.pi ↑(Finset.univ.image σ) T := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_pi, Finset.coe_image, Finset.coe_univ,
      Set.image_univ, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, hT]
    exact ⟨fun h a => h a (Set.mem_univ _), fun h a _ => h a⟩
  have hTm : ∀ n, MeasurableSet (T n) := by
    intro n; simp only [hTdef]; split_ifs
    · exact hs _
    · exact MeasurableSet.univ
  rw [hpre]
  unfold pathLaw
  rw [Measure.infinitePi_pi _ (fun n _ => hTm n),
    Finset.prod_image (fun a _ b _ h => hσ h)]
  exact Finset.prod_congr rfl fun j _ => by rw [hT j]

lemma mp_eval (μ : DemandLaw) (n : ℕ) :
    MeasurePreserving (fun p : Path => p n) (pathLaw μ) μ.law := by
  unfold pathLaw; exact measurePreserving_eval_infinitePi _ n

lemma ae_path_nonneg (μ : DemandLaw) : ∀ᵐ d ∂pathLaw μ, ∀ n, 0 ≤ d n :=
  ae_all_iff.2 fun n => ae_of_ae_map (mp_eval μ n).measurable.aemeasurable
    (by rw [(mp_eval μ n).map_eq]; exact ae_nonneg μ)

/-- Running maximum `Zb n = max_{i ≤ n} W^r_i`. -/
def Zb (r : ℝ) (d : Path) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max (Zb r d n) (W r d (n + 1))

/-- Shift of a path. -/
def sh (d : Path) : Path := fun n => d (n + 1)

lemma W_succ (r : ℝ) (d : Path) (k : ℕ) : W r d (k + 1) = (r - d 0) + W r (sh d) k := by
  unfold W sh; rw [Finset.sum_range_succ']; ring

lemma W_zero (r : ℝ) (d : Path) : W r d 0 = 0 := by simp [W]

lemma Zb_front (r : ℝ) (d : Path) (n : ℕ) :
    Zb r d (n + 1) = max 0 ((r - d 0) + Zb r (sh d) n) := by
  induction n with
  | zero => simp [Zb, W_succ, W_zero]
  | succ n ih =>
    rw [Zb, ih, W_succ, Zb, max_assoc, ← max_add_add_left]

lemma Zb_nonneg (r : ℝ) (d : Path) (n : ℕ) : 0 ≤ Zb r d n := by
  induction n with
  | zero => simp [Zb]
  | succ n ih => exact ih.trans (le_max_left _ _)

lemma Zb_mono (r : ℝ) (d : Path) : Monotone (fun n => Zb r d n) :=
  monotone_nat_of_le_succ fun n => le_max_left _ _

lemma W_le_Zb (r : ℝ) (d : Path) (n : ℕ) : W r d n ≤ Zb r d n := by
  cases n with
  | zero => simp [Zb, W_zero]
  | succ n => exact le_max_right _ _

lemma Zb_local (r : ℝ) (d d' : Path) (n : ℕ) (h : ∀ j < n, d j = d' j) : Zb r d n = Zb r d' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Zb]
    rw [ih fun j hj => h j (by omega)]
    congr 1
    unfold W
    exact Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]

lemma measurable_W' (r : ℝ) (i : ℕ) : Measurable (fun d : Path => W r d i) := by
  unfold W; fun_prop

lemma measurable_Zb (r : ℝ) (n : ℕ) : Measurable (fun d : Path => Zb r d n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.max (measurable_W' r (n + 1))

lemma measurable_Zinf' (r : ℝ) : Measurable (fun d : Path => Zinf r d) := by
  unfold Zinf
  exact Measurable.iSup fun i => ENNReal.measurable_ofReal.comp (measurable_W' r i)

lemma ofReal_Zb_le (r : ℝ) (d : Path) (n : ℕ) : ENNReal.ofReal (Zb r d n) ≤ Zinf r d := by
  induction n with
  | zero => simp [Zb]
  | succ n ih =>
    simp only [Zb]
    rw [ENNReal.ofReal_max]
    exact max_le ih (le_iSup (fun i => ENNReal.ofReal (W r d i)) (n + 1))

lemma Zinf_eq_iSup (r : ℝ) (d : Path) : Zinf r d = ⨆ n, ENNReal.ofReal (Zb r d n) :=
  le_antisymm (iSup_le fun i => (ENNReal.ofReal_le_ofReal (W_le_Zb r d i)).trans
    (le_iSup (fun n => ENNReal.ofReal (Zb r d n)) i)) (iSup_le fun n => ofReal_Zb_le r d n)


lemma W_exp (μ : DemandLaw) (θ r : ℝ) (n : ℕ) :
    ∫ d, Real.exp (θ * W r d n) ∂pathLaw μ = (∫ x, Real.exp (θ * (r - x)) ∂μ.law) ^ n := by
  have hmp := mp_idx μ n (fun j => (j : ℕ)) (fun a b h => Fin.ext h)
  set F : (Fin n → ℝ) → ℝ := fun z => ∏ j, Real.exp (θ * (r - z j)) with hF
  have hFm : Measurable F := by rw [hF]; fun_prop
  have hpt : ∀ d : Path, Real.exp (θ * W r d n) = F (fun j : Fin n => d j) := by
    intro d
    simp only [hF, W]
    rw [← Real.exp_sum, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun j => θ * (r - d j))]
  simp only [hpt]
  have hmap := integral_map (μ := pathLaw μ) hmp.measurable.aemeasurable
    (f := F) hFm.aestronglyMeasurable
  rw [hmp.map_eq] at hmap
  rw [← hmap, hF, integral_fintype_prod_eq_prod (f := fun _ : Fin n => fun x : ℝ =>
    Real.exp (θ * (r - x)))]
  simp

lemma Z_eq_Zb (r : ℝ) (d : Path) (n : ℕ) : Z r d (n + 1) = Zb r d n := by
  apply le_antisymm
  · unfold Z
    exact ciSup_le fun i => (W_le_Zb r d i).trans (Zb_mono r d (by omega : (i : ℕ) ≤ n))
  · obtain ⟨j, hj, hjeq⟩ : ∃ j ≤ n, Zb r d n = W r d j := by
      induction n with
      | zero => exact ⟨0, le_rfl, by simp [Zb, W_zero]⟩
      | succ n ih =>
        obtain ⟨j, hj, he⟩ := ih
        rcases le_total (Zb r d n) (W r d (n + 1)) with h | h
        · exact ⟨n + 1, le_rfl, by simp only [Zb]; rw [max_eq_right h]⟩
        · exact ⟨j, by omega, by simp only [Zb]; rw [max_eq_left h, he]⟩
    rw [hjeq]; unfold Z
    exact le_ciSup (Set.finite_range (fun i : Fin (n + 1) => W r d i)).bddAbove
      (⟨j, by omega⟩ : Fin (n + 1))

lemma measurable_sh : Measurable sh := measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1)

lemma mp_shift (μ : DemandLaw) : MeasurePreserving sh (pathLaw μ) (pathLaw μ) := by
  refine ⟨measurable_sh, ?_⟩
  conv_rhs => rw [pathLaw]
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  rw [Measure.map_apply measurable_sh (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have hpre : sh ⁻¹' (Set.pi ↑s t) = Set.pi ↑(s.image (· + 1)) (fun n => t (n - 1)) := by
    ext d
    simp [sh, Set.mem_pi]
  rw [hpre]
  unfold pathLaw
  rw [Measure.infinitePi_pi _ (fun n _ => ht (n - 1)),
    Finset.prod_image (fun a _ b _ h => by simpa using h)]
  simp
/-! ## Exchangeability and the Spitzer step -/

instance pathLaw_isProb (μ : DemandLaw) : IsProbabilityMeasure (pathLaw μ) := by
  unfold pathLaw; infer_instance

lemma mp_comp (μ : DemandLaw) (σ : ℕ → ℕ) (hσ : Function.Injective σ) :
    MeasurePreserving (fun p : Path => fun j => p (σ j)) (pathLaw μ) (pathLaw μ) := by
  refine ⟨by fun_prop, ?_⟩
  conv_rhs => rw [pathLaw]
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  set T : ℕ → Set ℝ := fun n => if h : ∃ j, σ j = n then t h.choose else Set.univ with hTdef
  have hT : ∀ j, T (σ j) = t j := by
    intro j
    have hex : ∃ j', σ j' = σ j := ⟨j, rfl⟩
    simp only [hTdef, dif_pos hex]
    rw [hσ hex.choose_spec]
  have hpre : (fun p : Path => fun j => p (σ j)) ⁻¹' Set.pi ↑s t = Set.pi ↑(s.image σ) T := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, hT]
  have hTm : ∀ n, MeasurableSet (T n) := by
    intro n; simp only [hTdef]; split_ifs
    · exact ht _
    · exact MeasurableSet.univ
  rw [hpre]
  unfold pathLaw
  rw [Measure.infinitePi_pi _ (fun n _ => hTm n), Finset.prod_image (fun a _ b _ h => hσ h)]
  exact Finset.prod_congr rfl fun j _ => by rw [hT j]

lemma int_comp (μ : DemandLaw) (σ : ℕ → ℕ) (hσ : Function.Injective σ) (F : Path → ℝ)
    (hF : Measurable F) :
    ∫ d, F (fun j => d (σ j)) ∂pathLaw μ = ∫ d, F d ∂pathLaw μ := by
  have hmp := mp_comp μ σ hσ
  have h := integral_map (μ := pathLaw μ) hmp.measurable.aemeasurable (f := F)
    hF.aestronglyMeasurable
  rw [hmp.map_eq] at h
  exact h.symm

lemma integrable_coord_path (μ : DemandLaw) (i : ℕ) :
    Integrable (fun d : Path => d i) (pathLaw μ) :=
  ((mp_eval μ i).integrable_comp (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable).2
    μ.integrable

lemma Zb_le_abs (r : ℝ) (d : Path) (m : ℕ) : Zb r d m ≤ ∑ j ∈ Finset.range m, |r - d j| := by
  induction m with
  | zero => simp [Zb]
  | succ m ih =>
    simp only [Zb]
    refine max_le ?_ ?_
    · rw [Finset.sum_range_succ]; linarith [abs_nonneg (r - d m)]
    · unfold W; exact Finset.sum_le_sum fun j _ => le_abs_self _

lemma integrable_absum (μ : DemandLaw) (r : ℝ) (m : ℕ) :
    Integrable (fun d : Path => ∑ j ∈ Finset.range m, |r - d j|) (pathLaw μ) :=
  integrable_finsetSum _ fun j _ => ((integrable_const r).sub (integrable_coord_path μ j)).abs

lemma integrable_Zb (μ : DemandLaw) (r : ℝ) (m : ℕ) :
    Integrable (fun d : Path => Zb r d m) (pathLaw μ) :=
  Integrable.mono' (integrable_absum μ r m) (measurable_Zb r m).aestronglyMeasurable
    (Eventually.of_forall fun d => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Zb_nonneg r d m)]; exact Zb_le_abs r d m)

lemma integrable_W (μ : DemandLaw) (r : ℝ) (k : ℕ) :
    Integrable (fun d : Path => W r d k) (pathLaw μ) := by
  unfold W
  exact integrable_finsetSum _ fun j _ => (integrable_const r).sub (integrable_coord_path μ j)

/-- Rotation of the first `m + 1` coordinates. -/
def rot (m : ℕ) (j : ℕ) : ℕ := if j < m then j + 1 else if j = m then 0 else j

lemma rot_inj (m : ℕ) : Function.Injective (rot m) := by
  intro a b h
  simp only [rot] at h
  split_ifs at h <;> omega

lemma W_rot (r : ℝ) (m : ℕ) (d : Path) :
    W r (fun j => d (rot m j)) (m + 1) = W r d (m + 1) := by
  simp only [W]
  rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun j => r - d j)]
  congr 1
  · exact Finset.sum_congr rfl fun j hj => by
      simp [rot, Finset.mem_range.1 hj]
  · simp [rot]

lemma Zb_rot (r : ℝ) (m : ℕ) (d : Path) :
    Zb r (fun j => d (rot m j)) m = Zb r (sh d) m :=
  Zb_local r _ _ m fun j hj => by simp [rot, sh, hj]

lemma W_swap (r : ℝ) (i m : ℕ) (hi : i ≤ m) (d : Path) :
    W r (fun j => d (Equiv.swap 0 i j)) (m + 1) = W r d (m + 1) := by
  simp only [W]
  refine Finset.sum_nbij' (Equiv.swap 0 i) (Equiv.swap 0 i) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    have ha' : a < m + 1 := by simpa using ha
    have : Equiv.swap 0 i a < m + 1 := by rw [Equiv.swap_apply_def]; split_ifs <;> omega
    simpa using this
  · intro a ha
    have ha' : a < m + 1 := by simpa using ha
    have : Equiv.swap 0 i a < m + 1 := by rw [Equiv.swap_apply_def]; split_ifs <;> omega
    simpa using this
  · intro a _; exact Equiv.swap_apply_self _ _ _
  · intro a _; exact Equiv.swap_apply_self _ _ _
  · intro a _; rfl

lemma meas_ite (r : ℝ) (k : ℕ) {g h : Path → ℝ} (hg : Measurable g) (hh : Measurable h) :
    Measurable (fun d : Path => if 0 < W r d k then g d else h d) :=
  Measurable.ite (measurableSet_lt measurable_const (measurable_W' r k)) hg hh

lemma int_ite (μ : DemandLaw) (r : ℝ) (k : ℕ) {g : Path → ℝ} (hg : Integrable g (pathLaw μ))
    (hgm : Measurable g) :
    Integrable (fun d : Path => if 0 < W r d k then g d else 0) (pathLaw μ) :=
  Integrable.mono' hg.norm (meas_ite r k hgm measurable_const).aestronglyMeasurable
    (Eventually.of_forall fun d => by split_ifs <;> simp)

lemma int_ite' (μ : DemandLaw) (r : ℝ) (k : ℕ) {g : Path → ℝ} (hg : Integrable g (pathLaw μ))
    (hgm : Measurable g) :
    Integrable (fun d : Path => if 0 < W r d k then 0 else g d) (pathLaw μ) :=
  Integrable.mono' hg.norm (meas_ite r k measurable_const hgm).aestronglyMeasurable
    (Eventually.of_forall fun d => by split_ifs <;> simp)

lemma measurable_coord (i : ℕ) : Measurable (fun d : Path => d i) := measurable_pi_apply i

lemma spitzer_real (μ : DemandLaw) (r : ℝ) (m : ℕ) :
    ∫ d, Zb r d (m + 1) ∂pathLaw μ = ∫ d, Zb r d m ∂pathLaw μ +
      (∫ d, max (W r d (m + 1)) 0 ∂pathLaw μ) / ((m : ℝ) + 1) := by
  have hc0 : Measurable (fun d : Path => r - d 0) := measurable_const.sub (measurable_coord 0)
  have hi0 : Integrable (fun d : Path => r - d 0) (pathLaw μ) :=
    (integrable_const r).sub (integrable_coord_path μ 0)
  have hshm : Measurable (fun d : Path => Zb r (sh d) m) := (measurable_Zb r m).comp measurable_sh
  have hshi : Integrable (fun d : Path => Zb r (sh d) m) (pathLaw μ) :=
    ((mp_shift μ).integrable_comp (g := fun d => Zb r d m)
      (measurable_Zb r m).aestronglyMeasurable).2 (integrable_Zb μ r m)
  have hpt : ∀ d : Path, Zb r d (m + 1) =
      (if 0 < W r d (m + 1) then r - d 0 else 0) +
      (if 0 < W r d (m + 1) then Zb r (sh d) m else 0) +
      (if 0 < W r d (m + 1) then 0 else Zb r d m) := by
    intro d
    split_ifs with h
    · rw [Zb_front]
      have h1 := W_le_Zb r (sh d) m
      rw [W_succ] at h
      rw [max_eq_right (by linarith)]
      ring
    · have h2 := Zb_nonneg r d m
      simp only [Zb]
      rw [max_eq_left (by linarith [not_lt.1 h])]
      ring
  have hI1 := int_ite μ r (m + 1) hi0 hc0
  have hI2 := int_ite μ r (m + 1) hshi hshm
  have hI3 := int_ite' μ r (m + 1) (integrable_Zb μ r m) (measurable_Zb r m)
  have hsplit : ∫ d, Zb r d (m + 1) ∂pathLaw μ =
      ∫ d, (if 0 < W r d (m + 1) then r - d 0 else 0) ∂pathLaw μ +
      ∫ d, (if 0 < W r d (m + 1) then Zb r (sh d) m else 0) ∂pathLaw μ +
      ∫ d, (if 0 < W r d (m + 1) then 0 else Zb r d m) ∂pathLaw μ := by
    have hI12 : Integrable (fun d : Path => (if 0 < W r d (m + 1) then r - d 0 else 0) +
        (if 0 < W r d (m + 1) then Zb r (sh d) m else 0)) (pathLaw μ) := hI1.add hI2
    rw [← integral_add hI1 hI2, ← integral_add hI12 hI3]
    exact integral_congr_ae (Eventually.of_forall fun d => hpt d)
  -- rotation: the shifted max has the law of the unshifted one jointly with `W`
  have hrot : ∫ d, (if 0 < W r d (m + 1) then Zb r (sh d) m else 0) ∂pathLaw μ =
      ∫ d, (if 0 < W r d (m + 1) then Zb r d m else 0) ∂pathLaw μ := by
    have h := int_comp μ (rot m) (rot_inj m)
      (fun d => if 0 < W r d (m + 1) then Zb r d m else 0)
      (meas_ite r (m + 1) (measurable_Zb r m) measurable_const)
    simp only [W_rot, Zb_rot] at h
    exact h
  have h23 : ∫ d, (if 0 < W r d (m + 1) then Zb r d m else 0) ∂pathLaw μ +
      ∫ d, (if 0 < W r d (m + 1) then 0 else Zb r d m) ∂pathLaw μ = ∫ d, Zb r d m ∂pathLaw μ := by
    rw [← integral_add (int_ite μ r (m + 1) (integrable_Zb μ r m) (measurable_Zb r m)) hI3]
    exact integral_congr_ae (Eventually.of_forall fun d => by
      simp only; split_ifs <;> ring)
  -- swaps: each coordinate contributes equally
  have hsw : ∀ i ∈ Finset.range (m + 1),
      ∫ d, (if 0 < W r d (m + 1) then r - d i else 0) ∂pathLaw μ =
      ∫ d, (if 0 < W r d (m + 1) then r - d 0 else 0) ∂pathLaw μ := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h := int_comp μ (Equiv.swap 0 i) (Equiv.injective _)
      (fun d => if 0 < W r d (m + 1) then r - d 0 else 0)
      (meas_ite r (m + 1) hc0 measurable_const)
    simp only [W_swap r i m hi', Equiv.swap_apply_left] at h
    exact h
  have hsum : ∫ d, max (W r d (m + 1)) 0 ∂pathLaw μ =
      ((m : ℝ) + 1) * ∫ d, (if 0 < W r d (m + 1) then r - d 0 else 0) ∂pathLaw μ := by
    have hint : ∀ i ∈ Finset.range (m + 1),
        Integrable (fun d : Path => if 0 < W r d (m + 1) then r - d i else 0) (pathLaw μ) :=
      fun i _ => int_ite μ r (m + 1) ((integrable_const r).sub (integrable_coord_path μ i))
        (measurable_const.sub (measurable_coord i))
    have h1 : ∫ d, max (W r d (m + 1)) 0 ∂pathLaw μ =
        ∫ d, ∑ i ∈ Finset.range (m + 1), (if 0 < W r d (m + 1) then r - d i else 0)
          ∂pathLaw μ := by
      refine integral_congr_ae (Eventually.of_forall fun d => ?_)
      simp only
      by_cases h : 0 < W r d (m + 1)
      · simp only [h, if_true]; rw [max_eq_left h.le]; rfl
      · simp only [h, if_false, Finset.sum_const_zero]; exact max_eq_right (not_lt.1 h)
    rw [h1, integral_finsetSum _ hint, Finset.sum_congr rfl hsw, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hI1eq : ∫ d, (if 0 < W r d (m + 1) then r - d 0 else 0) ∂pathLaw μ =
      (∫ d, max (W r d (m + 1)) 0 ∂pathLaw μ) / ((m : ℝ) + 1) := by
    rw [eq_div_iff hpos.ne', hsum]; ring
  rw [hsplit, hrot, hI1eq]
  linarith

lemma ofReal_max0 (a : ℝ) : ENNReal.ofReal a = ENNReal.ofReal (max a 0) := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

lemma M_succ (μ : DemandLaw) (r : ℝ) (n : ℕ) :
    M μ r (n + 1) = ∫⁻ d, ENNReal.ofReal (Zb r d n) ∂pathLaw μ := by
  unfold M; simp only [Z_eq_Zb]

lemma spitzer (μ : DemandLaw) (r : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    M μ r (k + 1) = M μ r k +
      ((k : ℝ≥0∞))⁻¹ * ∫⁻ d, ENNReal.ofReal (W r d k) ∂pathLaw μ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [M_succ, M_succ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_Zb μ r (m + 1))
      (Eventually.of_forall fun d => Zb_nonneg r d (m + 1)),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_Zb μ r m)
      (Eventually.of_forall fun d => Zb_nonneg r d m)]
  have hW : ∫⁻ d, ENNReal.ofReal (W r d (m + 1)) ∂pathLaw μ =
      ENNReal.ofReal (∫ d, max (W r d (m + 1)) 0 ∂pathLaw μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_W μ r (m + 1)).pos_part
      (Eventually.of_forall fun d => le_max_right _ _)]
    exact lintegral_congr fun d => ofReal_max0 _
  rw [hW, spitzer_real]
  have hP0 : 0 ≤ ∫ d, max (W r d (m + 1)) 0 ∂pathLaw μ :=
    integral_nonneg fun d => le_max_right _ _
  have hZ0 : 0 ≤ ∫ d, Zb r d m ∂pathLaw μ := integral_nonneg fun d => Zb_nonneg r d m
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [ENNReal.ofReal_add hZ0 (div_nonneg hP0 hpos.le)]
  congr 1
  have hc : ((m + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((m : ℝ) + 1) := by
    rw [← ENNReal.ofReal_natCast]; push_cast; rfl
  rw [hc, ← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_mul (inv_nonneg.2 hpos.le),
    div_eq_inv_mul]

lemma spitzer_sum (μ : DemandLaw) (r : ℝ) (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
    M μ r i = M μ r j + ∑ k ∈ Finset.Ico j i,
      ((k : ℝ≥0∞))⁻¹ * ∫⁻ d, ENNReal.ofReal (W r d k) ∂pathLaw μ := by
  induction i, hji using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, spitzer μ r n (by omega), ih, add_assoc]

lemma M_tendsto (μ : DemandLaw) (r : ℝ) :
    Tendsto (fun k => M μ r k) atTop (𝓝 (Minf μ r)) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  simp only [M_succ]
  have hMinf : Minf μ r = ⨆ n, ∫⁻ d, ENNReal.ofReal (Zb r d n) ∂pathLaw μ := by
    unfold Minf
    simp only [Zinf_eq_iSup]
    exact lintegral_iSup (fun n => ENNReal.measurable_ofReal.comp (measurable_Zb r n))
      (fun a b hab d => ENNReal.ofReal_le_ofReal (Zb_mono r d hab))
  rw [hMinf]
  exact tendsto_atTop_iSup fun a b hab =>
    lintegral_mono fun d => ENNReal.ofReal_le_ofReal (Zb_mono r d hab)

end XG5

namespace XG5

open XinGoldbergTBS.Asymptotic

/-! ## Chernoff tail -/

lemma Wpos_bound (μ : DemandLaw) (r θ : ℝ) (hθ : 0 < θ) (k : ℕ) :
    ∫⁻ d, ENNReal.ofReal (W r d k) ∂pathLaw μ ≤
      ENNReal.ofReal ((∫ x, Real.exp (θ * (r - x)) ∂μ.law) ^ k / θ) := by
  have hint : Integrable (fun d : Path => Real.exp (θ * W r d k) / θ) (pathLaw μ) := by
    refine (Integrable.of_bound (by
      exact ((Real.continuous_exp.measurable.comp ((measurable_W' r k).const_mul θ))).aestronglyMeasurable)
      (Real.exp (θ * (|r| * k))) ?_).div_const θ
    filter_upwards [ae_path_nonneg μ] with d hd
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hθ.le)
    unfold W
    calc ∑ j ∈ Finset.range k, (r - d j) ≤ ∑ _j ∈ Finset.range k, |r| :=
          Finset.sum_le_sum fun j _ => by linarith [hd j, le_abs_self r]
      _ = |r| * k := by simp [mul_comm]
  calc ∫⁻ d, ENNReal.ofReal (W r d k) ∂pathLaw μ
      ≤ ∫⁻ d, ENNReal.ofReal (Real.exp (θ * W r d k) / θ) ∂pathLaw μ := by
        refine lintegral_mono fun d => ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ hθ]
        linarith [Real.add_one_le_exp (θ * W r d k)]
    _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun d => by positivity), integral_div, W_exp]

lemma q_le_phi (μ : DemandLaw) (r ϵ θ : ℝ) (hθ : 0 ≤ θ) (hr : r ≤ μ.mean - ϵ) :
    ∫ x, Real.exp (θ * (r - x)) ∂μ.law ≤ phi μ ϵ θ := by
  have h : ∫ x, Real.exp (θ * (r - x)) ∂μ.law =
      Real.exp (θ * r) * ∫ x, Real.exp (-(θ * x)) ∂μ.law := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Real.exp_add]; congr 1; ring
  rw [h]
  unfold phi
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hr hθ))
    (integral_nonneg fun x => (Real.exp_pos _).le)

lemma tail_gen (μ : DemandLaw) (r ϵ θ : ℝ) (hθ : 0 < θ) (hp : phi μ ϵ θ < 1)
    (hr : r ≤ μ.mean - ϵ) (n : ℕ) (hn : 1 ≤ n) :
    Minf μ r ≤ M μ r n +
      ENNReal.ofReal (phi μ ϵ θ ^ n / ((1 - phi μ ϵ θ) * θ)) := by
  set p := phi μ ϵ θ with hpdef
  set q := ∫ x, Real.exp (θ * (r - x)) ∂μ.law with hqdef
  have hq0 : 0 ≤ q := integral_nonneg fun x => (Real.exp_pos _).le
  have hqp : q ≤ p := q_le_phi μ r ϵ θ hθ.le hr
  have hp0 : 0 ≤ p := phi_nonneg μ ϵ θ
  refine le_of_tendsto (M_tendsto μ r) ?_
  filter_upwards [eventually_ge_atTop n] with i hi
  rw [spitzer_sum μ r i n hn hi]
  gcongr
  calc ∑ k ∈ Finset.Ico n i, ((k : ℝ≥0∞))⁻¹ * ∫⁻ d, ENNReal.ofReal (W r d k) ∂pathLaw μ
      ≤ ∑ k ∈ Finset.Ico n i, ENNReal.ofReal (p ^ k / θ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk1 : 1 ≤ k := le_trans hn (Finset.mem_Ico.1 hk).1
        have hinv : ((k : ℝ≥0∞))⁻¹ ≤ 1 := ENNReal.inv_le_one.2 (by exact_mod_cast hk1)
        calc ((k : ℝ≥0∞))⁻¹ * ∫⁻ d, ENNReal.ofReal (W r d k) ∂pathLaw μ
            ≤ 1 * ∫⁻ d, ENNReal.ofReal (W r d k) ∂pathLaw μ := by gcongr
          _ ≤ ENNReal.ofReal (q ^ k / θ) := by rw [one_mul]; exact Wpos_bound μ r θ hθ k
          _ ≤ ENNReal.ofReal (p ^ k / θ) := ENNReal.ofReal_le_ofReal
              (div_le_div_of_nonneg_right (pow_le_pow_left₀ hq0 hqp k) hθ.le)
    _ = ENNReal.ofReal (∑ k ∈ Finset.Ico n i, p ^ k / θ) :=
        (ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.sum_div]
        have h1 := geom_sum_Ico_le_of_lt_one (m := n) (n := i) hp0 hp
        have h2 : 0 < 1 - p := by linarith
        calc (∑ k ∈ Finset.Ico n i, p ^ k) / θ ≤ p ^ n / (1 - p) / θ :=
              div_le_div_of_nonneg_right h1 hθ.le
          _ = p ^ n / ((1 - p) * θ) := by rw [div_div]

lemma M_one (μ : DemandLaw) (r : ℝ) : M μ r 1 = 0 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, M_succ]
  simp [Zb]

lemma phi_zero (μ : DemandLaw) (ϵ : ℝ) : phi μ ϵ 0 = 1 := by simp [phi]

lemma phi_contOn (μ : DemandLaw) (ϵ : ℝ) : ContinuousOn (phi μ ϵ) (Set.Ici 0) := by
  show ContinuousOn (fun θ => Real.exp (θ * (μ.mean - ϵ)) * ∫ d, Real.exp (-(θ * d)) ∂μ.law) _
  refine (Continuous.continuousOn (by fun_prop)).mul ?_
  refine continuousOn_of_dominated (bound := fun _ => (1 : ℝ))
    (fun θ _ => (by fun_prop : Measurable fun d : ℝ => Real.exp (-(θ * d))).aestronglyMeasurable)
    (fun θ hθ => ?_) (integrable_const 1)
    (Eventually.of_forall fun d =>
      (by fun_prop : Continuous fun θ : ℝ => Real.exp (-(θ * d))).continuousOn)
  filter_upwards [ae_nonneg μ] with d hd
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have : 0 ≤ θ := hθ
  exact Real.exp_le_one_iff.mpr (by nlinarith)

lemma exists_phi_lt_one (μ : DemandLaw) (ϵ : ℝ) (hϵ : 0 < ϵ) :
    ∃ θ, 0 < θ ∧ phi μ ϵ θ < 1 := by
  have hγ := gamma_lt_one μ ϵ hϵ
  unfold gamma at hγ
  obtain ⟨⟨θ, hθ⟩, hlt⟩ := exists_lt_of_ciInf_lt hγ
  refine ⟨θ, lt_of_le_of_ne hθ fun h0 => ?_, hlt⟩
  subst h0
  have h1 : phi μ ϵ 0 < 1 := hlt
  rw [phi_zero] at h1
  exact lt_irrefl _ h1

lemma far_min (μ : DemandLaw) (ϵ : ℝ) (hS : ¬ (phiMinimizers μ ϵ).Nonempty) (c : ℝ)
    (hc : gamma μ ϵ < c) (K : ℝ) (hK : 0 < K) : ∃ θ, K ≤ θ ∧ phi μ ϵ θ < c := by
  obtain ⟨θ0, hθ0mem, hmin⟩ := (isCompact_Icc : IsCompact (Set.Icc 0 K)).exists_isMinOn
    (Set.nonempty_Icc.2 hK.le) ((phi_contOn μ ϵ).mono Set.Icc_subset_Ici_self)
  have hgt : gamma μ ϵ < phi μ ϵ θ0 :=
    lt_of_le_of_ne (gamma_le_phi _ _ _ hθ0mem.1) (fun h => hS ⟨θ0, hθ0mem.1, h.symm⟩)
  have hlt0 : (⨅ t : Set.Ici (0 : ℝ), phi μ ϵ t) < min (phi μ ϵ θ0) c := lt_min hgt hc
  obtain ⟨⟨θ, hθ⟩, hlt⟩ := exists_lt_of_ciInf_lt hlt0
  refine ⟨θ, ?_, lt_of_lt_of_le hlt (min_le_right _ _)⟩
  by_contra hK'
  push Not at hK'
  have h1 := isMinOn_iff.1 hmin θ ⟨hθ, hK'.le⟩
  have h2 : phi μ ϵ θ < phi μ ϵ θ0 := lt_of_lt_of_le hlt (min_le_left _ _)
  linarith

theorem main (μ : DemandLaw) (r : ℝ) :
    (∀ i j : ℕ, 1 ≤ j → j ≤ i → M μ r j ≤ M μ r i) ∧
    Tendsto (fun k => M μ r k) atTop (nhds (Minf μ r)) ∧
    (∀ i j : ℕ, 1 ≤ j → j ≤ i →
      M μ r i = M μ r j + ∑ k ∈ Finset.Ico j i,
        ((k : ℝ≥0∞))⁻¹ * ∫⁻ d, ENNReal.ofReal (W r d k) ∂pathLaw μ) ∧
    (∀ ϵ : ℝ, 0 < ϵ → ϵ < μ.mean → r ≤ μ.mean - ϵ →
      Minf μ r < ⊤ ∧
      ∀ n : ℕ, 1 ≤ n →
        Minf μ r ≤ M μ r n +
          (vartheta μ ϵ * ENNReal.ofReal (1 - gamma μ ϵ))⁻¹ * ENNReal.ofReal (gamma μ ϵ) ^ n) := by
  refine ⟨fun i j hj hji => ?_, M_tendsto μ r, fun i j hj hji => spitzer_sum μ r i j hj hji, ?_⟩
  · rw [spitzer_sum μ r i j hj hji]; exact le_self_add
  intro ϵ hϵ _ hr
  have hγ := gamma_lt_one μ ϵ hϵ
  have hγ0 := gamma_nonneg μ ϵ
  obtain ⟨θ1, hθ1, hp1⟩ := exists_phi_lt_one μ ϵ hϵ
  have hfin : Minf μ r < ⊤ := by
    refine lt_of_le_of_lt (tail_gen μ r ϵ θ1 hθ1 hp1 hr 1 le_rfl) ?_
    rw [M_one, zero_add]; exact ENNReal.ofReal_lt_top
  refine ⟨hfin, fun n hn => ?_⟩
  have hMn : M μ r n ≤ Minf μ r := ge_of_tendsto (M_tendsto μ r) (by
    filter_upwards [eventually_ge_atTop n] with i hi
    rw [spitzer_sum μ r i n hn hi]; exact le_self_add)
  set Δ := Minf μ r - M μ r n with hΔdef
  have hΔtop : Δ ≠ ⊤ := ne_top_of_le_ne_top hfin.ne tsub_le_self
  have hΔle : ∀ θ, 0 < θ → phi μ ϵ θ < 1 →
      Δ ≤ ENNReal.ofReal (phi μ ϵ θ ^ n / ((1 - phi μ ϵ θ) * θ)) := fun θ hθ hp =>
    tsub_le_iff_left.2 (tail_gen μ r ϵ θ hθ hp hr n hn)
  have key : ∀ θ, 0 < θ → phi μ ϵ θ < 1 →
      Δ * ENNReal.ofReal (θ * (1 - phi μ ϵ θ)) ≤ ENNReal.ofReal (phi μ ϵ θ) ^ n := by
    intro θ hθ hp
    have h2 : 0 < 1 - phi μ ϵ θ := by linarith
    calc Δ * ENNReal.ofReal (θ * (1 - phi μ ϵ θ))
        ≤ ENNReal.ofReal (phi μ ϵ θ ^ n / ((1 - phi μ ϵ θ) * θ)) *
            ENNReal.ofReal (θ * (1 - phi μ ϵ θ)) := by gcongr; exact hΔle θ hθ hp
      _ = ENNReal.ofReal (phi μ ϵ θ ^ n) := by
          rw [← ENNReal.ofReal_mul (by have := phi_nonneg μ ϵ θ; positivity)]
          congr 1
          field_simp
      _ = ENNReal.ofReal (phi μ ϵ θ) ^ n := ENNReal.ofReal_pow (phi_nonneg μ ϵ θ) n
  have hc0 : ENNReal.ofReal (1 - gamma μ ϵ) ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hne0 : vartheta μ ϵ * ENNReal.ofReal (1 - gamma μ ϵ) ≠ 0 :=
    mul_ne_zero (vartheta_ne_zero μ ϵ hγ) hc0
  have hgtop : ENNReal.ofReal (gamma μ ϵ) ^ n ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  suffices hΔ : Δ ≤ (vartheta μ ϵ * ENNReal.ofReal (1 - gamma μ ϵ))⁻¹ *
      ENNReal.ofReal (gamma μ ϵ) ^ n by
    calc Minf μ r ≤ M μ r n + Δ := le_add_tsub
      _ ≤ _ := by gcongr
  rw [show (vartheta μ ϵ * ENNReal.ofReal (1 - gamma μ ϵ))⁻¹ * ENNReal.ofReal (gamma μ ϵ) ^ n =
      ENNReal.ofReal (gamma μ ϵ) ^ n / (vartheta μ ϵ * ENNReal.ofReal (1 - gamma μ ϵ)) from by
    rw [div_eq_mul_inv]; exact mul_comm _ _]
  rw [ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inr hgtop)]
  unfold vartheta
  split_ifs with hS
  · rw [ENNReal.iSup_mul, ENNReal.mul_iSup]
    refine iSup_le fun θ => ?_
    rw [ENNReal.iSup_mul, ENNReal.mul_iSup]
    refine iSup_le fun hθ => ?_
    obtain ⟨hθ0, hθγ⟩ := hθ
    have hθpos : 0 < θ := by
      refine lt_of_le_of_ne hθ0 fun h0 => ?_
      rw [← h0, phi_zero] at hθγ
      linarith
    have := key θ hθpos (by rw [hθγ]; exact hγ)
    rw [hθγ, ENNReal.ofReal_mul hθ0] at this
    exact this
  · suffices hΔ0 : Δ = 0 by rw [hΔ0, zero_mul]; exact bot_le
    set c := (1 + gamma μ ϵ) / 2 with hcdef
    have hc1 : gamma μ ϵ < c := by rw [hcdef]; linarith
    have hc2 : c < 1 := by rw [hcdef]; linarith
    have hbound : ∀ K : ℝ, 0 < K → Δ ≤ ENNReal.ofReal (1 / ((1 - c) * K)) := by
      intro K hK
      obtain ⟨θ, hKθ, hpθ⟩ := far_min μ ϵ hS c hc1 K hK
      have hθ : 0 < θ := lt_of_lt_of_le hK hKθ
      have hp0 := phi_nonneg μ ϵ θ
      refine (hΔle θ hθ (lt_trans hpθ hc2)).trans (ENNReal.ofReal_le_ofReal ?_)
      have h1 : phi μ ϵ θ ^ n ≤ 1 := pow_le_one₀ hp0 (by linarith)
      have h3 : (1 - c) * K ≤ (1 - phi μ ϵ θ) * θ :=
        mul_le_mul (by linarith) hKθ hK.le (by linarith)
      have h4 : 0 < (1 - c) * K := mul_pos (by linarith) hK
      calc phi μ ϵ θ ^ n / ((1 - phi μ ϵ θ) * θ) ≤ 1 / ((1 - phi μ ϵ θ) * θ) :=
            div_le_div_of_nonneg_right h1 (mul_pos (by linarith) hθ).le
        _ ≤ 1 / ((1 - c) * K) := one_div_le_one_div_of_le h4 h3
    by_contra hne
    have hx : 0 < Δ.toReal := ENNReal.toReal_pos hne hΔtop
    have h1c : 0 < 1 - c := by linarith
    have hK : 0 < 2 / ((1 - c) * Δ.toReal) := by positivity
    have h := ENNReal.toReal_le_of_le_ofReal (by positivity) (hbound _ hK)
    have he : 1 / ((1 - c) * (2 / ((1 - c) * Δ.toReal))) = Δ.toReal / 2 := by
      field_simp
    rw [he] at h
    linarith

end XG5

open MeasureTheory ProbabilityTheory Filter ENNReal NNReal XinGoldbergTBS.Asymptotic in
theorem solution (μ : DemandLaw) (r : ℝ) (hr : 0 < r) :
    (∀ i j : ℕ, 1 ≤ j → j ≤ i → M μ r j ≤ M μ r i) ∧
    Tendsto (fun k => M μ r k) atTop (nhds (Minf μ r)) ∧
    (∀ i j : ℕ, 1 ≤ j → j ≤ i →
      M μ r i = M μ r j + ∑ k ∈ Finset.Ico j i,
        ((k : ℝ≥0∞))⁻¹ * ∫⁻ d, ENNReal.ofReal (W r d k) ∂pathLaw μ) ∧
    (∀ ϵ : ℝ, 0 < ϵ → ϵ < μ.mean → r ≤ μ.mean - ϵ →
      Minf μ r < ⊤ ∧
      ∀ n : ℕ, 1 ≤ n →
        Minf μ r ≤ M μ r n +
          (vartheta μ ϵ * ENNReal.ofReal (1 - gamma μ ϵ))⁻¹ * ENNReal.ofReal (gamma μ ϵ) ^ n) := by
  exact XG5.main μ r

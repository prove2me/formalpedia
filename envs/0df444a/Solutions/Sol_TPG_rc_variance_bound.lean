-- Prove2me | solution 1 for TPG.rc_variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T05:06:49.791107+00:00
-- url     : https://prove2.me/submissions/cdc7458d-0b5a-43dc-82d9-c65fad97152b

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Theorems.Thm_TPG_integral_fun_actions
import Theorems.Thm_TPG_integral_head_mul_gap_tail
import Theorems.Thm_TPG_integral_head_mul_tail
import Theorems.Thm_TPG_mixing_contraction
import Theorems.Thm_TPG_isProbabilityMeasure_trajLaw
import Theorems.Thm_TPG_ae_abs_Y_le

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

namespace TPG_VR

/-! ### Part 1: summing a banded, geometrically decaying array -/

/-- A geometric sum over an injectively indexed finite family is at most `γ / (1 - γ)`. -/
lemma sum_geom_le {ι : Type} (s : Finset ι) (e : ι → ℕ) (hinj : Set.InjOn e s) {γ : ℝ}
    (h0 : 0 ≤ γ) (h1 : γ < 1) :
    ∑ j ∈ s, γ ^ (e j + 1) ≤ γ / (1 - γ) := by
  classical
  have hsum : Summable (fun n : ℕ => γ ^ n) := summable_geometric_of_lt_one h0 h1
  calc ∑ j ∈ s, γ ^ (e j + 1) = ∑ n ∈ s.image e, γ ^ (n + 1) :=
        (Finset.sum_image (f := fun n : ℕ => γ ^ (n + 1)) hinj).symm
    _ = γ * ∑ n ∈ s.image e, γ ^ n := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => pow_succ' γ n
    _ ≤ γ * ∑' n : ℕ, γ ^ n :=
        mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun n _ => pow_nonneg h0 n) h0
    _ = γ / (1 - γ) := by rw [tsum_geometric_of_lt_one h0 h1, div_eq_mul_inv]

/-- **Summation lemma.** If `c i j ≤ V` always and `c i j ≤ 2 V γ^{|i - j| - k - 1}` whenever
`|i - j| ≥ k + 2`, then `∑_{i,j < T} c i j ≤ T V (2k + 3 + 4γ/(1-γ))`. -/
lemma sum_sum_le_of_decay (T k : ℕ) (γ V : ℝ) (h0 : 0 ≤ γ) (h1 : γ < 1) (hV : 0 ≤ V)
    (c : Fin T → Fin T → ℝ)
    (hc : ∀ i j, c i j ≤ V)
    (hfar : ∀ i j : Fin T, (i : ℕ) + k + 2 ≤ j → c i j ≤ 2 * V * γ ^ ((j : ℕ) - i - k - 1))
    (hfar' : ∀ i j : Fin T, (j : ℕ) + k + 2 ≤ i → c i j ≤ 2 * V * γ ^ ((i : ℕ) - j - k - 1)) :
    ∑ i, ∑ j, c i j ≤ T * (V * (2 * k + 3 + 4 * γ / (1 - γ))) := by
  classical
  have hrow : ∀ i : Fin T, ∑ j, c i j ≤ V * (2 * k + 3 + 4 * γ / (1 - γ)) := by
    intro i
    have hpt : ∀ j : Fin T, c i j
        ≤ (if (j : ℕ) ≤ i + k + 1 ∧ (i : ℕ) ≤ j + k + 1 then V else 0)
          + (if (i : ℕ) + k + 2 ≤ j then 2 * V * γ ^ ((j : ℕ) - i - k - 2 + 1) else 0)
          + (if (j : ℕ) + k + 2 ≤ i then 2 * V * γ ^ ((i : ℕ) - j - k - 2 + 1) else 0) := by
      intro j
      by_cases hA : (i : ℕ) + k + 2 ≤ j
      · have hN : ¬ ((j : ℕ) ≤ i + k + 1 ∧ (i : ℕ) ≤ j + k + 1) := by omega
        have hB : ¬ ((j : ℕ) + k + 2 ≤ i) := by omega
        have he : (j : ℕ) - i - k - 2 + 1 = (j : ℕ) - i - k - 1 := by omega
        rw [if_neg hN, if_pos hA, if_neg hB, he, zero_add, add_zero]
        exact hfar i j hA
      · by_cases hB : (j : ℕ) + k + 2 ≤ i
        · have hN : ¬ ((j : ℕ) ≤ i + k + 1 ∧ (i : ℕ) ≤ j + k + 1) := by omega
          have he : (i : ℕ) - j - k - 2 + 1 = (i : ℕ) - j - k - 1 := by omega
          rw [if_neg hN, if_neg hA, if_pos hB, he, zero_add, zero_add]
          exact hfar' i j hB
        · have hN : (j : ℕ) ≤ i + k + 1 ∧ (i : ℕ) ≤ j + k + 1 := by omega
          rw [if_pos hN, if_neg hA, if_neg hB, add_zero, add_zero]
          exact hc i j
    have hnear : ∑ j : Fin T, (if (j : ℕ) ≤ i + k + 1 ∧ (i : ℕ) ≤ j + k + 1 then V else 0)
        ≤ V * (2 * k + 3) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ hV
      have hcard : (Finset.univ.filter
          (fun j : Fin T => (j : ℕ) ≤ i + k + 1 ∧ (i : ℕ) ≤ j + k + 1)).card
          ≤ (Finset.Icc ((i : ℕ) - (k + 1)) ((i : ℕ) + (k + 1))).card := by
        refine Finset.card_le_card_of_injOn (fun j : Fin T => (j : ℕ)) ?_ ?_
        · intro j hj
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj
          simp only [Finset.coe_Icc, Set.mem_Icc]
          omega
        · intro j _ j' _ hjj'
          exact Fin.ext hjj'
      rw [Nat.card_Icc] at hcard
      have hcard' : (Finset.univ.filter
          (fun j : Fin T => (j : ℕ) ≤ i + k + 1 ∧ (i : ℕ) ≤ j + k + 1)).card ≤ 2 * k + 3 := by
        omega
      exact_mod_cast hcard'
    have hup : ∑ j : Fin T,
        (if (i : ℕ) + k + 2 ≤ j then 2 * V * γ ^ ((j : ℕ) - i - k - 2 + 1) else 0)
        ≤ 2 * V * (γ / (1 - γ)) := by
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine sum_geom_le _ (fun j : Fin T => (j : ℕ) - i - k - 2) ?_ h0 h1
      intro j hj j' hj' hjj'
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj hj'
      exact Fin.ext (by simp only at hjj'; omega)
    have hdown : ∑ j : Fin T,
        (if (j : ℕ) + k + 2 ≤ i then 2 * V * γ ^ ((i : ℕ) - j - k - 2 + 1) else 0)
        ≤ 2 * V * (γ / (1 - γ)) := by
      rw [← Finset.sum_filter, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine sum_geom_le _ (fun j : Fin T => (i : ℕ) - j - k - 2) ?_ h0 h1
      intro j hj j' hj' hjj'
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj hj'
      exact Fin.ext (by simp only at hjj'; omega)
    calc ∑ j, c i j
        ≤ ∑ j : Fin T, ((if (j : ℕ) ≤ i + k + 1 ∧ (i : ℕ) ≤ j + k + 1 then V else 0)
          + (if (i : ℕ) + k + 2 ≤ j then 2 * V * γ ^ ((j : ℕ) - i - k - 2 + 1) else 0)
          + (if (j : ℕ) + k + 2 ≤ i then 2 * V * γ ^ ((i : ℕ) - j - k - 2 + 1) else 0)) :=
          Finset.sum_le_sum fun j _ => hpt j
      _ ≤ V * (2 * k + 3) + 2 * V * (γ / (1 - γ)) + 2 * V * (γ / (1 - γ)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          exact add_le_add (add_le_add hnear hup) hdown
      _ = V * (2 * k + 3 + 4 * γ / (1 - γ)) := by ring
  calc ∑ i, ∑ j, c i j ≤ ∑ _i : Fin T, V * (2 * k + 3 + 4 * γ / (1 - γ)) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = T * (V * (2 * k + 3 + 4 * γ / (1 - γ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Part 2: variance of an average of weakly dependent variables -/

section Abstract

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A bounded measurable real function is integrable for a finite measure. -/
lemma integrable_of_bdd [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (C : ℝ)
    (hb : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)

/-- A bounded measurable real function is in `L²` for a finite measure. -/
lemma memLp_two_of_bdd [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (C : ℝ)
    (hb : ∀ x, |f x| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)

/-- `E|f| ≤ √V` when `E[f²] ≤ V`. -/
lemma integral_abs_le_sqrt [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) {V : ℝ}
    (hV : ∫ ω, (f ω) ^ 2 ∂μ ≤ V) : ∫ ω, |f ω| ∂μ ≤ Real.sqrt V := by
  have habs : MemLp (fun ω => |f ω|) 2 μ := hf.abs
  have h1 := variance_nonneg (fun ω => |f ω|) μ
  rw [variance_eq_sub habs] at h1
  have h2 : ∫ ω, ((fun ω => |f ω|) ^ 2) ω ∂μ = ∫ ω, (f ω) ^ 2 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.pow_apply, sq_abs]
  rw [h2] at h1
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))

/-- `Cov(X, Y) ≤ V` when `E[X²] ≤ V` and `E[Y²] ≤ V`. -/
lemma covariance_le_of_sq_le [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) {V : ℝ} (hXV : ∫ ω, (X ω) ^ 2 ∂μ ≤ V) (hYV : ∫ ω, (Y ω) ^ 2 ∂μ ≤ V) :
    cov[X, Y; μ] ≤ V := by
  have hvX : Var[X; μ] ≤ V := (variance_le_expectation_sq hX.aestronglyMeasurable).trans hXV
  have hvY : Var[Y; μ] ≤ V := (variance_le_expectation_sq hY.aestronglyMeasurable).trans hYV
  have hXc : MemLp (fun ω => X ω - μ[X]) 2 μ := hX.sub (memLp_const _)
  have hYc : MemLp (fun ω => Y ω - μ[Y]) 2 μ := hY.sub (memLp_const _)
  have hi1 : Integrable (fun ω => (X ω - μ[X]) ^ 2) μ := hXc.integrable_sq
  have hi2 : Integrable (fun ω => (Y ω - μ[Y]) ^ 2) μ := hYc.integrable_sq
  have hle : ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ
      ≤ ∫ ω, ((X ω - μ[X]) ^ 2 + (Y ω - μ[Y]) ^ 2) / 2 ∂μ := by
    refine integral_mono (hXc.integrable_mul hYc) ((hi1.add hi2).div_const 2) fun ω => ?_
    show (X ω - μ[X]) * (Y ω - μ[Y]) ≤ ((X ω - μ[X]) ^ 2 + (Y ω - μ[Y]) ^ 2) / 2
    nlinarith [sq_nonneg ((X ω - μ[X]) - (Y ω - μ[Y]))]
  have heq : ∫ ω, ((X ω - μ[X]) ^ 2 + (Y ω - μ[Y]) ^ 2) / 2 ∂μ = (Var[X; μ] + Var[Y; μ]) / 2 := by
    rw [integral_div, integral_add hi1 hi2, variance_eq_integral hX.aemeasurable,
      variance_eq_integral hY.aemeasurable]
  rw [covariance]
  linarith

/-- **Variance of an average of weakly dependent variables.** If every `B t` has second moment
at most `V` and `|Cov(B i, B j)| ≤ 2 V γ^{j - i - k - 1}` whenever `j ≥ i + k + 2`, then
`Var((1/T) ∑_t B t) ≤ (V / T) (2k + 3 + 4γ/(1-γ))`. -/
lemma variance_avg_le [IsProbabilityMeasure μ] (T k : ℕ) (hT : 0 < T) (γ V : ℝ)
    (h0 : 0 ≤ γ) (h1 : γ < 1) (B : Fin T → Ω → ℝ) (hB : ∀ t, MemLp (B t) 2 μ)
    (hsq : ∀ t, ∫ ω, (B t ω) ^ 2 ∂μ ≤ V)
    (hdecay : ∀ i j : Fin T, (i : ℕ) + k + 2 ≤ j →
      |cov[B i, B j; μ]| ≤ 2 * V * γ ^ ((j : ℕ) - i - k - 1)) :
    Var[fun ω => (1 / (T : ℝ)) * ∑ t, B t ω; μ]
      ≤ V / T * (2 * k + 3 + 4 * γ / (1 - γ)) := by
  have hV : 0 ≤ V :=
    (integral_nonneg fun ω => sq_nonneg (B ⟨0, hT⟩ ω)).trans (hsq ⟨0, hT⟩)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [variance_const_mul, variance_fun_sum hB]
  have hsum := sum_sum_le_of_decay T k γ V h0 h1 hV (fun i j => cov[B i, B j; μ])
    (fun i j => covariance_le_of_sq_le (hB i) (hB j) (hsq i) (hsq j))
    (fun i j hij => (le_abs_self _).trans (hdecay i j hij))
    (fun i j hij => by
      rw [covariance_comm]
      exact (le_abs_self _).trans (hdecay j i hij))
  calc (1 / (T : ℝ)) ^ 2 * ∑ i, ∑ j, cov[B i, B j; μ]
      ≤ (1 / (T : ℝ)) ^ 2 * (T * (V * (2 * k + 3 + 4 * γ / (1 - γ)))) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = V / T * (2 * k + 3 + 4 * γ / (1 - γ)) := by
        field_simp

end Abstract


/-! ### Part 3: decay of the covariance between a head functional and a tail functional -/

section Decay

lemma measurable_X {S : Type} [MeasurableSpace S] {T : ℕ} (t : Fin T) : Measurable (X t : Traj S T → S) := by
  unfold X
  exact (measurable_pi_apply t).fst

lemma measurable_Z {S : Type} [MeasurableSpace S] {T : ℕ} (t : Fin T) :
    Measurable (Z t : Traj S T → Bool) := by
  unfold Z
  exact (measurable_pi_apply t).snd.fst

lemma measurable_Y {S : Type} [MeasurableSpace S] {T : ℕ} (t : Fin T) :
    Measurable (Y t : Traj S T → ℝ) := by
  unfold Y
  exact (measurable_pi_apply t).snd.snd

variable {S : Type} [Fintype S]

lemma P_le_one (E : Env S) (t : ℕ) (z : Bool) (x x' : S) : E.P t z x x' ≤ 1 := by
  rw [← E.P_row_sum t z x]
  exact Finset.single_le_sum (fun y _ => E.P_nonneg t z x y) (Finset.mem_univ x')

/-- **Covariance decay across a gap.** Let `F` be a bounded measurable function of the first
`m + 1` steps and `G` a bounded measurable function of the steps from time `m + 1 + h` on. If
`E|F| ≤ aF` under the law of the first `m + 1` steps and `|E_b[G]| ≤ cG` for the environment
restarted at time `m + 1 + h` from any state `b`, then under the mixing assumption
`|E[F G] - E[F] E[G]| ≤ 2 aF cG γ^h`. -/
lemma cov_head_gap_tail_le [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (m h n T : ℕ) (hT : m + 1 + h ≤ T) (γ : ℝ) (hγ : 0 ≤ γ) (hmix : E.Mixing T γ)
    (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (F : Traj S (m + 1) → ℝ) (G : Traj S n → ℝ) (hF : Measurable F) (hG : Measurable G)
    (CF CG : ℝ) (hFb : ∀ ω, |F ω| ≤ CF) (hGb : ∀ ω, |G ω| ≤ CG)
    (aF cG : ℝ) (hc0 : 0 ≤ cG)
    (ha : ∫ ω, |F ω| ∂(E.trajLaw (m + 1) q) ≤ aF)
    (hc : ∀ b : S,
      |∫ ω, G ω ∂((E.shift (m + 1 + h) b).trajLaw n (fun t => q (m + 1 + h + t)))| ≤ cG) :
    |(∫ ω, F (headTraj (m + 1) (h + n) ω) * G (tailTraj h n (tailTraj (m + 1) (h + n) ω))
          ∂(E.trajLaw (m + 1 + (h + n)) q))
      - (∫ ω, F (headTraj (m + 1) (h + n) ω) ∂(E.trajLaw (m + 1 + (h + n)) q))
        * (∫ ω, G (tailTraj h n (tailTraj (m + 1) (h + n) ω)) ∂(E.trajLaw (m + 1 + (h + n)) q))|
      ≤ 2 * aF * cG * γ ^ h := by
  have hμ₀ : IsProbabilityMeasure (E.trajLaw (m + 1) q) :=
    isProbabilityMeasure_trajLaw E (m + 1) q hq
  set Pa : S → Traj S (m + 1) → ℝ :=
    fun a ω => E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a with hPa
  set Pi : Matrix S S ℝ :=
    ((List.Ico (m + 1) (m + 1 + h)).map (fun s => E.PMix (q s) s)).prod with hPi
  set g : S → ℝ := fun b =>
    ∫ ω, G ω ∂((E.shift (m + 1 + h) b).trajLaw n (fun t => q (m + 1 + h + t))) with hg
  set φ : S → ℝ := fun a => ∫ ω, F ω * Pa a ω ∂(E.trajLaw (m + 1) q) with hφ
  set ψ : S → ℝ := fun a => ∫ ω, Pa a ω ∂(E.trajLaw (m + 1) q) with hψ
  have hPa_meas : ∀ a, Measurable (Pa a) := fun a =>
    (Measurable.of_discrete (f := fun p : Bool × S => E.P m p.1 p.2 a)).comp
      ((measurable_Z (Fin.last m)).prodMk (measurable_X (Fin.last m)))
  have hPa_nonneg : ∀ a ω, 0 ≤ Pa a ω := fun a ω => E.P_nonneg _ _ _ _
  have hPa_le : ∀ a ω, Pa a ω ≤ 1 := fun a ω => P_le_one E _ _ _ _
  have hPa_sum : ∀ ω, ∑ a, Pa a ω = 1 := fun ω => E.P_row_sum _ _ _
  -- the three integrals in matrix form
  have hFG : ∫ ω, F (headTraj (m + 1) (h + n) ω) * G (tailTraj h n (tailTraj (m + 1) (h + n) ω))
        ∂(E.trajLaw (m + 1 + (h + n)) q) = ∑ a, ∑ b, φ a * Pi a b * g b :=
    integral_head_mul_gap_tail E m h n q hq F G hF hG CF CG hFb hGb
  have hG1 : ∫ ω, G (tailTraj h n (tailTraj (m + 1) (h + n) ω)) ∂(E.trajLaw (m + 1 + (h + n)) q)
      = ∑ a, ∑ b, ψ a * Pi a b * g b := by
    have := integral_head_mul_gap_tail E m h n q hq (fun _ => 1) G measurable_const hG 1 CG
      (fun _ => by simp) hGb
    simpa only [one_mul] using this
  have hF1 : ∫ ω, F (headTraj (m + 1) (h + n) ω) ∂(E.trajLaw (m + 1 + (h + n)) q)
      = ∑ a, φ a := by
    have := integral_head_mul_tail E m (h + n) q hq F (fun _ => 1) hF measurable_const CF 1 hFb
      (fun _ => by simp)
    have hprob : ∀ a, IsProbabilityMeasure
        ((E.shift (m + 1) a).trajLaw (h + n) (fun t => q (m + 1 + t))) :=
      fun a => isProbabilityMeasure_trajLaw _ _ _ (fun t => hq _)
    simpa only [mul_one, integral_const, probReal_univ, smul_eq_mul] using this
  set d : S → ℝ := fun a => φ a - (∑ a', φ a') * ψ a with hd
  have hcov : (∫ ω, F (headTraj (m + 1) (h + n) ω) * G (tailTraj h n (tailTraj (m + 1) (h + n) ω))
          ∂(E.trajLaw (m + 1 + (h + n)) q))
      - (∫ ω, F (headTraj (m + 1) (h + n) ω) ∂(E.trajLaw (m + 1 + (h + n)) q))
        * (∫ ω, G (tailTraj h n (tailTraj (m + 1) (h + n) ω)) ∂(E.trajLaw (m + 1 + (h + n)) q))
      = ∑ b, Matrix.vecMul d Pi b * g b := by
    have hexp : ∑ b, Matrix.vecMul d Pi b * g b
        = ∑ a, ∑ b, (φ a * Pi a b * g b - (∑ a', φ a') * (ψ a * Pi a b * g b)) := by
      refine Eq.trans ?_ Finset.sum_comm
      refine Finset.sum_congr rfl fun b _ => ?_
      show (∑ a, d a * Pi a b) * g b = _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      show (φ a - (∑ a', φ a') * ψ a) * Pi a b * g b = _
      ring
    rw [hexp, hFG, hF1, hG1]
    simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  -- integrability
  have hφ_int : ∀ a, Integrable (fun ω => |F ω| * Pa a ω) (E.trajLaw (m + 1) q) := fun a =>
    integrable_of_bdd (hF.abs.mul (hPa_meas a)) CF (fun ω => by
      rw [abs_mul, abs_abs, abs_of_nonneg (hPa_nonneg a ω)]
      exact (mul_le_mul_of_nonneg_left (hPa_le a ω) (abs_nonneg _)).trans
        (by simpa using hFb ω))
  have hψ_int : ∀ a, Integrable (Pa a) (E.trajLaw (m + 1) q) := fun a =>
    integrable_of_bdd (hPa_meas a) 1 (fun ω => by
      rw [abs_of_nonneg (hPa_nonneg a ω)]
      exact hPa_le a ω)
  have hsumφ_abs : ∑ a, |φ a| ≤ aF := by
    calc ∑ a, |φ a| ≤ ∑ a, ∫ ω, |F ω| * Pa a ω ∂(E.trajLaw (m + 1) q) :=
          Finset.sum_le_sum fun a _ => by
            refine abs_integral_le_integral_abs.trans (le_of_eq ?_)
            refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
            simp only [abs_mul, abs_of_nonneg (hPa_nonneg a ω)]
      _ = ∫ ω, ∑ a, |F ω| * Pa a ω ∂(E.trajLaw (m + 1) q) :=
          (integral_finsetSum _ fun a _ => hφ_int a).symm
      _ = ∫ ω, |F ω| ∂(E.trajLaw (m + 1) q) := by
          simp only [← Finset.mul_sum, hPa_sum, mul_one]
      _ ≤ aF := ha
  have hsumψ : ∑ a, ψ a = 1 := by
    calc ∑ a, ψ a = ∫ ω, ∑ a, Pa a ω ∂(E.trajLaw (m + 1) q) :=
          (integral_finsetSum _ fun a _ => hψ_int a).symm
      _ = 1 := by simp only [hPa_sum, integral_const, probReal_univ, smul_eq_mul, mul_one]
  have hψ_nonneg : ∀ a, 0 ≤ ψ a := fun a => integral_nonneg (hPa_nonneg a)
  have hd_sum : ∑ a, d a = 0 := by
    simp only [hd, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumψ, mul_one, sub_self]
  have hd_abs : ∑ a, |d a| ≤ 2 * aF := by
    calc ∑ a, |d a| ≤ ∑ a, (|φ a| + |∑ a', φ a'| * ψ a) := Finset.sum_le_sum fun a _ => by
          simp only [hd]
          calc |φ a - (∑ a', φ a') * ψ a| = |φ a + -((∑ a', φ a') * ψ a)| := by
                rw [sub_eq_add_neg]
            _ ≤ |φ a| + |-((∑ a', φ a') * ψ a)| := abs_add_le _ _
            _ = |φ a| + |∑ a', φ a'| * ψ a := by
                rw [abs_neg, abs_mul, abs_of_nonneg (hψ_nonneg a)]
      _ = ∑ a, |φ a| + |∑ a', φ a'| := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumψ, mul_one]
      _ ≤ aF + aF :=
          add_le_add hsumφ_abs ((Finset.abs_sum_le_sum_abs _ _).trans hsumφ_abs)
      _ = 2 * aF := by ring
  have hcontr := mixing_contraction E T γ hγ hmix q hq (m + 1) (m + 1 + h)
    (Nat.le_add_right _ _) hT d hd_sum
  rw [Nat.add_sub_cancel_left] at hcontr
  rw [hcov]
  calc |∑ b, Matrix.vecMul d Pi b * g b| ≤ ∑ b, |Matrix.vecMul d Pi b * g b| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, |Matrix.vecMul d Pi b| * cG := Finset.sum_le_sum fun b _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hc b) (abs_nonneg _)
    _ = (∑ b, |Matrix.vecMul d Pi b|) * cG := by rw [Finset.sum_mul]
    _ ≤ (γ ^ h * ∑ x, |d x|) * cG := mul_le_mul_of_nonneg_right hcontr hc0
    _ ≤ (γ ^ h * (2 * aF)) * cG :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd_abs (pow_nonneg hγ h)) hc0
    _ = 2 * aF * cG * γ ^ h := by ring

end Decay


/-! ### Part 4: window functionals -/

section Window

/-- Clipping to `[-M, M]`. -/
noncomputable def clip (M y : ℝ) : ℝ := max (-M) (min M y)

lemma abs_clip_le (M y : ℝ) : |clip M y| ≤ |M| := by
  unfold clip
  rw [abs_le]
  constructor
  · exact (neg_le_neg (le_abs_self M)).trans (le_max_left _ _)
  · exact max_le (neg_le_abs M) ((min_le_left _ _).trans (le_abs_self M))

lemma clip_eq_self {M y : ℝ} (h : |y| ≤ M) : clip M y = y := by
  unfold clip
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

lemma measurable_clip (M : ℝ) : Measurable (clip M) := by
  unfold clip
  exact measurable_const.max (measurable_const.min measurable_id)

lemma abs_bool_le (f : Bool → ℝ) (z : Bool) : |f z| ≤ |f true| + |f false| := by
  cases z
  · linarith [abs_nonneg (f true)]
  · linarith [abs_nonneg (f false)]

/-- The window functional at time `t` with window start `lo`:
`clip(Y_t) · (a(Z_t) + b(Z_t) · ∑_{lo ≤ u < t} s_θ(Z_u))`. -/
noncomputable def win {S : Type} (θ M : ℝ) (a b : Bool → ℝ) (N lo : ℕ) (t : Fin N)
    (ω : Traj S N) : ℝ :=
  clip M (Y t ω) * (a (Z t ω) + b (Z t ω) *
    ∑ u : Fin N, if lo ≤ (u : ℕ) ∧ (u : ℕ) < (t : ℕ) then score θ (Z u ω) else 0)

lemma measurable_win {S : Type} [MeasurableSpace S] (θ M : ℝ) (a b : Bool → ℝ) (N lo : ℕ)
    (t : Fin N) : Measurable (win θ M a b N lo t : Traj S N → ℝ) := by
  unfold win
  refine ((measurable_clip M).comp (measurable_Y t)).mul ?_
  refine ((Measurable.of_discrete (f := a)).comp (measurable_Z t)).add ?_
  refine ((Measurable.of_discrete (f := b)).comp (measurable_Z t)).mul ?_
  refine Finset.measurable_fun_sum _ fun u _ => ?_
  by_cases hu : lo ≤ (u : ℕ) ∧ (u : ℕ) < (t : ℕ)
  · simp only [if_pos hu]
    exact (Measurable.of_discrete (f := score θ)).comp (measurable_Z u)
  · simp only [if_neg hu]
    exact measurable_const

/-- A uniform bound for the window functional. -/
noncomputable def winBound (θ M : ℝ) (a b : Bool → ℝ) (N : ℕ) : ℝ :=
  |M| * ((|a true| + |a false|)
    + (|b true| + |b false|) * (N * (|score θ true| + |score θ false|)))

lemma abs_win_le {S : Type} (θ M : ℝ) (a b : Bool → ℝ) (N lo : ℕ) (t : Fin N) (ω : Traj S N) :
    |win θ M a b N lo t ω| ≤ winBound θ M a b N := by
  unfold win winBound
  rw [abs_mul]
  refine mul_le_mul (abs_clip_le _ _) ?_ (abs_nonneg _) (abs_nonneg _)
  refine (abs_add_le _ _).trans (add_le_add (abs_bool_le a _) ?_)
  rw [abs_mul]
  refine mul_le_mul (abs_bool_le b _) ?_ (abs_nonneg _) (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ u : Fin N, |if lo ≤ (u : ℕ) ∧ (u : ℕ) < (t : ℕ) then score θ (Z u ω) else 0|
      ≤ ∑ _u : Fin N, (|score θ true| + |score θ false|) := Finset.sum_le_sum fun u _ => by
        split_ifs
        · exact abs_bool_le _ _
        · rw [abs_zero]
          positivity
    _ = N * (|score θ true| + |score θ false|) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The window functional at the last time of the head only depends on the head. -/
lemma win_head {S : Type} (θ M : ℝ) (a b : Bool → ℝ) (m r lo : ℕ) (ω : Traj S (m + 1 + r)) :
    win θ M a b (m + 1 + r) lo (Fin.castAdd r (Fin.last m)) ω
      = win θ M a b (m + 1) lo (Fin.last m) (headTraj (m + 1) r ω) := by
  unfold win
  have hsum : ∑ u : Fin (m + 1 + r),
        (if lo ≤ (u : ℕ) ∧ (u : ℕ) < ((Fin.castAdd r (Fin.last m) : Fin (m + 1 + r)) : ℕ)
          then score θ (Z u ω) else 0)
      = ∑ u : Fin (m + 1),
        (if lo ≤ (u : ℕ) ∧ (u : ℕ) < ((Fin.last m : Fin (m + 1)) : ℕ)
          then score θ (Z u (headTraj (m + 1) r ω)) else 0) := by
    rw [Fin.sum_univ_add]
    have hz : ∑ u : Fin r,
        (if lo ≤ ((Fin.natAdd (m + 1) u : Fin (m + 1 + r)) : ℕ)
            ∧ ((Fin.natAdd (m + 1) u : Fin (m + 1 + r)) : ℕ)
              < ((Fin.castAdd r (Fin.last m) : Fin (m + 1 + r)) : ℕ)
          then score θ (Z (Fin.natAdd (m + 1) u) ω) else 0) = 0 := by
      refine Finset.sum_eq_zero fun u _ => if_neg ?_
      simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_last]
      omega
    rw [hz, add_zero]
    rfl
  rw [hsum]
  rfl

/-- The window functional at a time of the tail, with window inside the tail, only depends on
the tail. -/
lemma win_tail {S : Type} (θ M : ℝ) (a b : Bool → ℝ) (p n lo : ℕ) (hlo : p ≤ lo) (t : Fin n)
    (ω : Traj S (p + n)) :
    win θ M a b (p + n) lo (Fin.natAdd p t) ω = win θ M a b n (lo - p) t (tailTraj p n ω) := by
  unfold win
  have hsum : ∑ u : Fin (p + n),
        (if lo ≤ (u : ℕ) ∧ (u : ℕ) < ((Fin.natAdd p t : Fin (p + n)) : ℕ)
          then score θ (Z u ω) else 0)
      = ∑ u : Fin n,
        (if lo - p ≤ (u : ℕ) ∧ (u : ℕ) < (t : ℕ)
          then score θ (Z u (tailTraj p n ω)) else 0) := by
    rw [Fin.sum_univ_add]
    have hz : ∑ u : Fin p,
        (if lo ≤ ((Fin.castAdd n u : Fin (p + n)) : ℕ)
            ∧ ((Fin.castAdd n u : Fin (p + n)) : ℕ) < ((Fin.natAdd p t : Fin (p + n)) : ℕ)
          then score θ (Z (Fin.castAdd n u) ω) else 0) = 0 := by
      refine Finset.sum_eq_zero fun u _ => if_neg ?_
      have := u.isLt
      simp only [Fin.val_castAdd]
      omega
    rw [hz, zero_add]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hiff : (lo ≤ ((Fin.natAdd p u : Fin (p + n)) : ℕ)
          ∧ ((Fin.natAdd p u : Fin (p + n)) : ℕ) < ((Fin.natAdd p t : Fin (p + n)) : ℕ))
        ↔ (lo - p ≤ (u : ℕ) ∧ (u : ℕ) < (t : ℕ)) := by
      simp only [Fin.val_natAdd]
      omega
    exact if_congr hiff rfl rfl
  rw [hsum]
  rfl

end Window


/-! ### Part 5: variance of an average of window functionals -/

section WindowVariance

variable {S : Type} [Fintype S]

/-- Covariance decay for two window functionals separated by a gap of `h` steps, written with
the horizon split as `(m + 1) + (h + n)`. -/
lemma cov_win_gap_le [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (θ γ M V : ℝ) (a b : Bool → ℝ) (k : ℕ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hγ : 0 ≤ γ)
    (hV : ∀ (E' : Env S) (N lo : ℕ) (t : Fin N), (t : ℕ) ≤ lo + k →
        ∫ ω, (win θ M a b N lo t ω) ^ 2 ∂(E'.trajLaw N (fun _ => θ)) ≤ V)
    (m h n lo₁ lo₂ : ℕ) (t : Fin n) (hmix : E.Mixing (m + 1 + (h + n)) γ)
    (h₁ : m ≤ lo₁ + k) (h₂ : m + 1 + h ≤ lo₂) (h₃ : (t : ℕ) + (m + 1 + h) ≤ lo₂ + k) :
    |cov[win θ M a b (m + 1 + (h + n)) lo₁ (Fin.castAdd (h + n) (Fin.last m)),
         win θ M a b (m + 1 + (h + n)) lo₂ (Fin.natAdd (m + 1) (Fin.natAdd h t));
         E.trajLaw (m + 1 + (h + n)) (fun _ => θ)]| ≤ 2 * V * γ ^ h := by
  have hq : ∀ t : ℕ, 0 ≤ (fun _ : ℕ => θ) t ∧ (fun _ : ℕ => θ) t ≤ 1 := fun _ => ⟨hθ0, hθ1⟩
  have hμ : IsProbabilityMeasure (E.trajLaw (m + 1 + (h + n)) (fun _ => θ)) :=
    isProbabilityMeasure_trajLaw _ _ _ hq
  have hμ₀ : IsProbabilityMeasure (E.trajLaw (m + 1) (fun _ => θ)) :=
    isProbabilityMeasure_trajLaw _ _ _ hq
  have hμb : ∀ b' : S, IsProbabilityMeasure
      ((E.shift (m + 1 + h) b').trajLaw n (fun _ => θ)) :=
    fun b' => isProbabilityMeasure_trajLaw _ _ _ hq
  set F : Traj S (m + 1) → ℝ := win θ M a b (m + 1) lo₁ (Fin.last m) with hF_def
  set G : Traj S n → ℝ := win θ M a b n (lo₂ - (m + 1) - h) t with hG_def
  have hA : win θ M a b (m + 1 + (h + n)) lo₁ (Fin.castAdd (h + n) (Fin.last m))
      = fun ω => F (headTraj (m + 1) (h + n) ω) :=
    funext fun ω => win_head θ M a b m (h + n) lo₁ ω
  have hB : win θ M a b (m + 1 + (h + n)) lo₂ (Fin.natAdd (m + 1) (Fin.natAdd h t))
      = fun ω => G (tailTraj h n (tailTraj (m + 1) (h + n) ω)) := funext fun ω => by
    rw [win_tail θ M a b (m + 1) (h + n) lo₂ (by omega) (Fin.natAdd h t) ω,
      win_tail θ M a b h n (lo₂ - (m + 1)) (by omega) t _]
  have hFmeas : Measurable F := measurable_win θ M a b (m + 1) lo₁ (Fin.last m)
  have hGmeas : Measurable G := measurable_win θ M a b n (lo₂ - (m + 1) - h) t
  have hFb : ∀ ω, |F ω| ≤ winBound θ M a b (m + 1) := fun ω => abs_win_le _ _ _ _ _ _ _ ω
  have hGb : ∀ ω, |G ω| ≤ winBound θ M a b n := fun ω => abs_win_le _ _ _ _ _ _ _ ω
  have hFsq : ∫ ω, (F ω) ^ 2 ∂(E.trajLaw (m + 1) (fun _ => θ)) ≤ V :=
    hV E (m + 1) lo₁ (Fin.last m) (by simpa using h₁)
  have hGsq : ∀ b' : S, ∫ ω, (G ω) ^ 2 ∂((E.shift (m + 1 + h) b').trajLaw n (fun _ => θ)) ≤ V :=
    fun b' => hV (E.shift (m + 1 + h) b') n _ t (by omega)
  have hV0 : 0 ≤ V := (integral_nonneg fun ω => sq_nonneg (F ω)).trans hFsq
  have haF : ∫ ω, |F ω| ∂(E.trajLaw (m + 1) (fun _ => θ)) ≤ Real.sqrt V :=
    integral_abs_le_sqrt (memLp_two_of_bdd hFmeas _ hFb) hFsq
  have hcG : ∀ b' : S,
      |∫ ω, G ω ∂((E.shift (m + 1 + h) b').trajLaw n (fun _ => θ))| ≤ Real.sqrt V :=
    fun b' => abs_integral_le_integral_abs.trans
      (integral_abs_le_sqrt (memLp_two_of_bdd hGmeas _ hGb) (hGsq b'))
  have key := cov_head_gap_tail_le E m h n (m + 1 + (h + n)) (by omega) γ hγ hmix
    (fun _ => θ) hq F G hFmeas hGmeas _ _ hFb hGb (Real.sqrt V) (Real.sqrt V)
    (Real.sqrt_nonneg V) haF hcG
  have hAmem : MemLp (fun ω : Traj S (m + 1 + (h + n)) => F (headTraj (m + 1) (h + n) ω)) 2
      (E.trajLaw (m + 1 + (h + n)) (fun _ => θ)) := by
    rw [← hA]
    exact memLp_two_of_bdd (measurable_win _ _ _ _ _ _ _) _ (abs_win_le _ _ _ _ _ _ _)
  have hBmem : MemLp
      (fun ω : Traj S (m + 1 + (h + n)) => G (tailTraj h n (tailTraj (m + 1) (h + n) ω))) 2
      (E.trajLaw (m + 1 + (h + n)) (fun _ => θ)) := by
    rw [← hB]
    exact memLp_two_of_bdd (measurable_win _ _ _ _ _ _ _) _ (abs_win_le _ _ _ _ _ _ _)
  have hmul : 2 * Real.sqrt V * Real.sqrt V * γ ^ h = 2 * V * γ ^ h := by
    rw [mul_assoc 2, Real.mul_self_sqrt hV0]
  rw [hA, hB, covariance_eq_sub hAmem hBmem, ← hmul]
  exact key

/-- Covariance decay for the window functionals at two times `i`, `j` of the horizon `T` with
`j ≥ i + k + 2`. -/
lemma cov_win_decay [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (θ γ M V : ℝ) (a b : Bool → ℝ) (T k : ℕ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hγ : 0 ≤ γ) (hmix : E.Mixing T γ)
    (hV : ∀ (E' : Env S) (N lo : ℕ) (t : Fin N), (t : ℕ) ≤ lo + k →
        ∫ ω, (win θ M a b N lo t ω) ^ 2 ∂(E'.trajLaw N (fun _ => θ)) ≤ V)
    (i j : Fin T) (hij : (i : ℕ) + k + 2 ≤ j) :
    |cov[win θ M a b T ((i : ℕ) - k) i, win θ M a b T ((j : ℕ) - k) j;
         E.trajLaw T (fun _ => θ)]| ≤ 2 * V * γ ^ ((j : ℕ) - i - k - 1) := by
  obtain ⟨iv, hi⟩ := i
  obtain ⟨jv, hj⟩ := j
  simp only at hij ⊢
  obtain ⟨h, rfl⟩ : ∃ h, jv = iv + 1 + h + k := ⟨jv - iv - 1 - k, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', T = iv + 1 + (h + (k + 1 + n')) :=
    ⟨T - (iv + 1 + h + k + 1), by omega⟩
  have hi' : (⟨iv, hi⟩ : Fin (iv + 1 + (h + (k + 1 + n'))))
      = Fin.castAdd (h + (k + 1 + n')) (Fin.last iv) := Fin.ext rfl
  have hj' : (⟨iv + 1 + h + k, hj⟩ : Fin (iv + 1 + (h + (k + 1 + n'))))
      = Fin.natAdd (iv + 1) (Fin.natAdd h (⟨k, by omega⟩ : Fin (k + 1 + n'))) :=
    Fin.ext (by simp [Nat.add_assoc])
  have he : iv + 1 + h + k - iv - k - 1 = h := by omega
  rw [hi', hj', he]
  exact cov_win_gap_le E θ γ M V a b k hθ0 hθ1 hγ hV iv h (k + 1 + n') (iv - k)
    (iv + 1 + h + k - k) ⟨k, by omega⟩ hmix (by omega) (by omega) (by simp; omega)

/-- **Variance bound for averages of window functionals.** If the window functionals have second
moment at most `V` under every environment, every horizon and every window of length at most
`k + 1`, then under mixing
`Var((1/T) ∑_t win_t) ≤ (V / T) (2k + 3 + 4γ/(1-γ))`. -/
theorem variance_win_avg_le [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (θ γ M V : ℝ) (a b : Bool → ℝ)
    (hT : 0 < T) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hmix : E.Mixing T γ)
    (hV : ∀ (E' : Env S) (N lo : ℕ) (t : Fin N), (t : ℕ) ≤ lo + k →
        ∫ ω, (win θ M a b N lo t ω) ^ 2 ∂(E'.trajLaw N (fun _ => θ)) ≤ V) :
    Var[fun ω => (1 / (T : ℝ)) * ∑ t : Fin T, win θ M a b T ((t : ℕ) - k) t ω;
        E.trajLaw T (fun _ => θ)]
      ≤ V / T * (2 * k + 3 + 4 * γ / (1 - γ)) := by
  classical
  have hμ : IsProbabilityMeasure (E.trajLaw T (fun _ => θ)) :=
    isProbabilityMeasure_trajLaw E T _ (fun _ => ⟨hθ0, hθ1⟩)
  exact variance_avg_le T k hT γ V hγ0 hγ1 (fun t => win θ M a b T ((t : ℕ) - k) t)
    (fun t => memLp_two_of_bdd (measurable_win _ _ _ _ _ _ _) _ (abs_win_le _ _ _ _ _ _ _))
    (fun t => hV E T _ t (by omega))
    (fun i j hij => cov_win_decay E θ γ M V a b T k hθ0 hθ1 hγ0 hmix hV i j hij)

end WindowVariance


/-! ### Part 6: second moments of window functionals -/

section ActionMoments

variable {S : Type} [Fintype S]

/-- Every function of the action path is integrable under a trajectory law. -/
lemma integrable_fun_actions [MeasurableSpace S] [MeasurableSingletonClass S]
    (E' : Env S) (N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (g : (Fin N → Bool) → ℝ) :
    Integrable (fun ω : Traj S N => g (fun s => Z s ω)) (E'.trajLaw N (fun _ => θ)) := by
  have hμ : IsProbabilityMeasure (E'.trajLaw N (fun _ => θ)) :=
    isProbabilityMeasure_trajLaw E' N _ (fun _ => ⟨hθ0, hθ1⟩)
  have hZ : Measurable (fun ω : Traj S N => (fun s => Z s ω : Fin N → Bool)) :=
    measurable_pi_lambda _ fun s => measurable_Z s
  refine integrable_of_bdd ((measurable_of_finite g).comp hZ) (∑ z, |g z|) (fun ω => ?_)
  exact Finset.single_le_sum (f := fun z => |g z|) (fun z _ => abs_nonneg (g z))
    (Finset.mem_univ (fun s => Z s ω))

/-- **Product formula.** Under `π_θ` the actions are independent Bernoulli(`θ`) variables:
`E[∏_s φ_s(Z_s)] = ∏_s (θ φ_s(1) + (1 - θ) φ_s(0))`. -/
lemma integral_prod_fun_Z [MeasurableSpace S] [MeasurableSingletonClass S]
    (E' : Env S) (N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (φ : Fin N → Bool → ℝ) :
    ∫ ω, ∏ s : Fin N, φ s (Z s ω) ∂(E'.trajLaw N (fun _ => θ))
      = ∏ s : Fin N, (θ * φ s true + (1 - θ) * φ s false) := by
  classical
  have h := integral_fun_actions E' N (fun _ => θ) (fun _ => ⟨hθ0, hθ1⟩)
    (fun z => ∏ s : Fin N, φ s (z s))
  refine h.trans ?_
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (s : Fin N) (b : Bool) => (if b then θ else 1 - θ) * φ s b)]
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]

/-- `E[f(Z_t)] = θ f(1) + (1 - θ) f(0)`. -/
lemma integral_fun_Z [MeasurableSpace S] [MeasurableSingletonClass S]
    (E' : Env S) (N : ℕ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (f : Bool → ℝ) (t : Fin N) :
    ∫ ω, f (Z t ω) ∂(E'.trajLaw N (fun _ => θ)) = θ * f true + (1 - θ) * f false := by
  classical
  have h := integral_prod_fun_Z E' N θ hθ0 hθ1 (fun s b => if s = t then f b else 1)
  have hL : ∀ ω : Traj S N, ∏ s : Fin N, (if s = t then f (Z s ω) else 1) = f (Z t ω) := by
    intro ω
    rw [Finset.prod_ite_eq']
    simp
  simp only [hL] at h
  rw [h, Finset.prod_eq_single t]
  · simp
  · intro s _ hs
    simp [hs]
  · intro ht
    exact absurd (Finset.mem_univ t) ht

/-- `E[f(Z_t) s_θ(Z_u)] = 0` for `u ≠ t`. -/
lemma integral_fun_mul_score [MeasurableSpace S] [MeasurableSingletonClass S]
    (E' : Env S) (N : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (f : Bool → ℝ) (t u : Fin N)
    (hut : u ≠ t) :
    ∫ ω, f (Z t ω) * score θ (Z u ω) ∂(E'.trajLaw N (fun _ => θ)) = 0 := by
  classical
  have hθ : θ ≠ 0 := hθ0.ne'
  have hθ' : 1 - θ ≠ 0 := by linarith
  have h := integral_prod_fun_Z E' N θ hθ0.le hθ1.le
    (fun s b => (if s = t then f b else 1) * (if s = u then score θ b else 1))
  have hL : ∀ ω : Traj S N,
      ∏ s : Fin N, ((if s = t then f (Z s ω) else 1) * (if s = u then score θ (Z s ω) else 1))
        = f (Z t ω) * score θ (Z u ω) := by
    intro ω
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp
  simp only [hL] at h
  rw [h]
  refine Finset.prod_eq_zero (Finset.mem_univ u) ?_
  simp only [if_neg hut, if_true, one_mul, score, Bool.false_eq_true, if_false]
  field_simp
  ring

/-- `E[f(Z_t) s_θ(Z_u) s_θ(Z_v)] = E[f(Z_t)] · 1{u = v} / (θ (1 - θ))` for `u, v ≠ t`. -/
lemma integral_fun_mul_score_mul_score [MeasurableSpace S] [MeasurableSingletonClass S]
    (E' : Env S) (N : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (f : Bool → ℝ) (t u v : Fin N)
    (hut : u ≠ t) (hvt : v ≠ t) :
    ∫ ω, f (Z t ω) * (score θ (Z u ω) * score θ (Z v ω)) ∂(E'.trajLaw N (fun _ => θ))
      = (θ * f true + (1 - θ) * f false) * (if u = v then 1 / (θ * (1 - θ)) else 0) := by
  classical
  have hθ : θ ≠ 0 := hθ0.ne'
  have hθ' : 1 - θ ≠ 0 := by linarith
  have h := integral_prod_fun_Z E' N θ hθ0.le hθ1.le
    (fun s b => (if s = t then f b else 1)
      * ((if s = u then score θ b else 1) * (if s = v then score θ b else 1)))
  have hL : ∀ ω : Traj S N,
      ∏ s : Fin N, ((if s = t then f (Z s ω) else 1)
          * ((if s = u then score θ (Z s ω) else 1) * (if s = v then score θ (Z s ω) else 1)))
        = f (Z t ω) * (score θ (Z u ω) * score θ (Z v ω)) := by
    intro ω
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq',
      Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp
  simp only [hL] at h
  rw [h]
  by_cases huv : u = v
  · subst huv
    rw [if_pos rfl, Finset.prod_eq_mul_of_mem t u (Finset.mem_univ _) (Finset.mem_univ _)
      (Ne.symm hut)]
    · simp only [if_neg (Ne.symm hut), if_neg hut, if_true, one_mul, mul_one, score,
        Bool.false_eq_true, if_false]
      field_simp
      ring
    · intro s _ hs
      simp [hs.1, hs.2]
  · rw [if_neg huv, mul_zero]
    refine Finset.prod_eq_zero (Finset.mem_univ u) ?_
    simp only [if_neg hut, if_neg huv, if_true, one_mul, mul_one, score, Bool.false_eq_true,
      if_false]
    field_simp
    ring

/-- Second moment of `a(Z_t) + b(Z_t) ∑_{u ∈ W} s_θ(Z_u)` when `t ∉ W`:
`E[a(Z_t)²] + E[b(Z_t)²] |W| / (θ (1 - θ))`. -/
lemma integral_sq_window [MeasurableSpace S] [MeasurableSingletonClass S]
    (E' : Env S) (N : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (a b : Bool → ℝ) (t : Fin N)
    (W : Finset (Fin N)) (hW : ∀ u ∈ W, u ≠ t) :
    ∫ ω, (a (Z t ω) + b (Z t ω) * ∑ u ∈ W, score θ (Z u ω)) ^ 2 ∂(E'.trajLaw N (fun _ => θ))
      = (θ * a true ^ 2 + (1 - θ) * a false ^ 2)
        + (θ * b true ^ 2 + (1 - θ) * b false ^ 2) * (W.card / (θ * (1 - θ))) := by
  classical
  have hint := integrable_fun_actions E' N θ hθ0.le hθ1.le
  have hexp : ∀ ω : Traj S N, (a (Z t ω) + b (Z t ω) * ∑ u ∈ W, score θ (Z u ω)) ^ 2
      = a (Z t ω) ^ 2
        + 2 * ∑ u ∈ W, (a (Z t ω) * b (Z t ω)) * score θ (Z u ω)
        + ∑ u ∈ W, ∑ v ∈ W, b (Z t ω) ^ 2 * (score θ (Z u ω) * score θ (Z v ω)) := by
    intro ω
    have h1 : ∑ u ∈ W, (a (Z t ω) * b (Z t ω)) * score θ (Z u ω)
        = a (Z t ω) * b (Z t ω) * ∑ u ∈ W, score θ (Z u ω) := (Finset.mul_sum _ _ _).symm
    have h2 : ∑ u ∈ W, ∑ v ∈ W, b (Z t ω) ^ 2 * (score θ (Z u ω) * score θ (Z v ω))
        = b (Z t ω) ^ 2 * ((∑ u ∈ W, score θ (Z u ω)) * ∑ v ∈ W, score θ (Z v ω)) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
    rw [h1, h2]
    ring
  have hi1 : Integrable (fun ω : Traj S N => a (Z t ω) ^ 2) (E'.trajLaw N (fun _ => θ)) :=
    hint (fun z => a (z t) ^ 2)
  have hi2 : ∀ u : Fin N, Integrable
      (fun ω : Traj S N => (a (Z t ω) * b (Z t ω)) * score θ (Z u ω))
      (E'.trajLaw N (fun _ => θ)) := fun u => hint (fun z => (a (z t) * b (z t)) * score θ (z u))
  have hi3 : ∀ u v : Fin N, Integrable
      (fun ω : Traj S N => b (Z t ω) ^ 2 * (score θ (Z u ω) * score θ (Z v ω)))
      (E'.trajLaw N (fun _ => θ)) :=
    fun u v => hint (fun z => b (z t) ^ 2 * (score θ (z u) * score θ (z v)))
  have hi2' : Integrable
      (fun ω : Traj S N => 2 * ∑ u ∈ W, (a (Z t ω) * b (Z t ω)) * score θ (Z u ω))
      (E'.trajLaw N (fun _ => θ)) := (integrable_finsetSum _ fun u _ => hi2 u).const_mul 2
  have hi3' : ∀ u : Fin N, Integrable
      (fun ω : Traj S N => ∑ v ∈ W, b (Z t ω) ^ 2 * (score θ (Z u ω) * score θ (Z v ω)))
      (E'.trajLaw N (fun _ => θ)) := fun u => integrable_finsetSum _ fun v _ => hi3 u v
  have hi3'' : Integrable
      (fun ω : Traj S N =>
        ∑ u ∈ W, ∑ v ∈ W, b (Z t ω) ^ 2 * (score θ (Z u ω) * score θ (Z v ω)))
      (E'.trajLaw N (fun _ => θ)) := integrable_finsetSum _ fun u _ => hi3' u
  have e1 : ∫ ω, a (Z t ω) ^ 2 ∂(E'.trajLaw N (fun _ => θ))
      = θ * a true ^ 2 + (1 - θ) * a false ^ 2 :=
    integral_fun_Z E' N θ hθ0.le hθ1.le (fun z => a z ^ 2) t
  have e2 : ∫ ω, 2 * ∑ u ∈ W, (a (Z t ω) * b (Z t ω)) * score θ (Z u ω)
      ∂(E'.trajLaw N (fun _ => θ)) = 0 := by
    rw [integral_const_mul, integral_finsetSum _ (fun u _ => hi2 u),
      Finset.sum_eq_zero fun u hu =>
        integral_fun_mul_score E' N θ hθ0 hθ1 (fun z => a z * b z) t u (hW u hu), mul_zero]
  have e3 : ∫ ω, ∑ u ∈ W, ∑ v ∈ W, b (Z t ω) ^ 2 * (score θ (Z u ω) * score θ (Z v ω))
      ∂(E'.trajLaw N (fun _ => θ))
      = (θ * b true ^ 2 + (1 - θ) * b false ^ 2) * (W.card / (θ * (1 - θ))) := by
    calc ∫ ω, ∑ u ∈ W, ∑ v ∈ W, b (Z t ω) ^ 2 * (score θ (Z u ω) * score θ (Z v ω))
          ∂(E'.trajLaw N (fun _ => θ))
        = ∑ u ∈ W, ∫ ω, ∑ v ∈ W, b (Z t ω) ^ 2 * (score θ (Z u ω) * score θ (Z v ω))
            ∂(E'.trajLaw N (fun _ => θ)) := integral_finsetSum _ fun u _ => hi3' u
      _ = ∑ u ∈ W, ∑ v ∈ W, ∫ ω, b (Z t ω) ^ 2 * (score θ (Z u ω) * score θ (Z v ω))
            ∂(E'.trajLaw N (fun _ => θ)) :=
          Finset.sum_congr rfl fun u _ => integral_finsetSum _ fun v _ => hi3 u v
      _ = ∑ u ∈ W, ∑ v ∈ W, ((θ * b true ^ 2 + (1 - θ) * b false ^ 2)
            * (if u = v then 1 / (θ * (1 - θ)) else 0)) :=
          Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv =>
            integral_fun_mul_score_mul_score E' N θ hθ0 hθ1 (fun z => b z ^ 2) t u v
              (hW u hu) (hW v hv)
      _ = ∑ _u ∈ W, (θ * b true ^ 2 + (1 - θ) * b false ^ 2) * (1 / (θ * (1 - θ))) :=
          Finset.sum_congr rfl fun u hu => by
            rw [← Finset.mul_sum, Finset.sum_ite_eq, if_pos hu]
      _ = (θ * b true ^ 2 + (1 - θ) * b false ^ 2) * (W.card / (θ * (1 - θ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hi12 : Integrable
      (fun ω : Traj S N =>
        a (Z t ω) ^ 2 + 2 * ∑ u ∈ W, (a (Z t ω) * b (Z t ω)) * score θ (Z u ω))
      (E'.trajLaw N (fun _ => θ)) := hi1.add hi2'
  simp only [hexp]
  rw [integral_add hi12 hi3'', integral_add hi1 hi2', e1, e2, e3, add_zero]

/-- Second moment of a window functional with window of length at most `k`. -/
lemma integral_sq_win_le [MeasurableSpace S] [MeasurableSingletonClass S]
    (E' : Env S) (θ M : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (a b : Bool → ℝ) (k N lo : ℕ)
    (t : Fin N) (ht : (t : ℕ) ≤ lo + k) :
    ∫ ω, (win θ M a b N lo t ω) ^ 2 ∂(E'.trajLaw N (fun _ => θ))
      ≤ M ^ 2 * ((θ * a true ^ 2 + (1 - θ) * a false ^ 2)
          + (θ * b true ^ 2 + (1 - θ) * b false ^ 2) * (k / (θ * (1 - θ)))) := by
  classical
  have hμ : IsProbabilityMeasure (E'.trajLaw N (fun _ => θ)) :=
    isProbabilityMeasure_trajLaw E' N _ (fun _ => ⟨hθ0.le, hθ1.le⟩)
  set W : Finset (Fin N) :=
    Finset.univ.filter (fun u : Fin N => lo ≤ (u : ℕ) ∧ (u : ℕ) < (t : ℕ)) with hW
  have hWt : ∀ u ∈ W, u ≠ t := by
    intro u hu h
    simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [h] at hu
    omega
  have hcard : W.card ≤ k := by
    have hle : W.card ≤ (Finset.Ico ((t : ℕ) - k) (t : ℕ)).card := by
      refine Finset.card_le_card_of_injOn (fun u : Fin N => (u : ℕ)) ?_ ?_
      · intro u hu
        simp only [hW, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu
        simp only [Finset.coe_Ico, Set.mem_Ico]
        omega
      · intro u _ u' _ huu'
        exact Fin.ext huu'
    rw [Nat.card_Ico] at hle
    omega
  have hsumW : ∀ ω : Traj S N,
      ∑ u : Fin N, (if lo ≤ (u : ℕ) ∧ (u : ℕ) < (t : ℕ) then score θ (Z u ω) else 0)
        = ∑ u ∈ W, score θ (Z u ω) := fun ω => by rw [hW, Finset.sum_filter]
  have hpt : ∀ ω : Traj S N, (win θ M a b N lo t ω) ^ 2
      ≤ M ^ 2 * (a (Z t ω) + b (Z t ω) * ∑ u ∈ W, score θ (Z u ω)) ^ 2 := by
    intro ω
    unfold win
    rw [hsumW ω, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    calc (clip M (Y t ω)) ^ 2 = |clip M (Y t ω)| ^ 2 := (sq_abs _).symm
      _ ≤ |M| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_clip_le M (Y t ω)) 2
      _ = M ^ 2 := sq_abs M
  have hval := integral_sq_window E' N θ hθ0 hθ1 a b t W hWt
  have hWint : Integrable
      (fun ω : Traj S N => (a (Z t ω) + b (Z t ω) * ∑ u ∈ W, score θ (Z u ω)) ^ 2)
      (E'.trajLaw N (fun _ => θ)) :=
    integrable_fun_actions E' N θ hθ0.le hθ1.le
      (fun z => (a (z t) + b (z t) * ∑ u ∈ W, score θ (z u)) ^ 2)
  have hpos : 0 < θ * (1 - θ) := mul_pos hθ0 (by linarith)
  have hB : 0 ≤ θ * b true ^ 2 + (1 - θ) * b false ^ 2 :=
    add_nonneg (mul_nonneg hθ0.le (sq_nonneg _)) (mul_nonneg (by linarith) (sq_nonneg _))
  calc ∫ ω, (win θ M a b N lo t ω) ^ 2 ∂(E'.trajLaw N (fun _ => θ))
      ≤ ∫ ω, M ^ 2 * (a (Z t ω) + b (Z t ω) * ∑ u ∈ W, score θ (Z u ω)) ^ 2
          ∂(E'.trajLaw N (fun _ => θ)) :=
        integral_mono
          (memLp_two_of_bdd (measurable_win _ _ _ _ _ _ _) _
            (abs_win_le _ _ _ _ _ _ _)).integrable_sq
          (hWint.const_mul _) hpt
    _ = M ^ 2 * ((θ * a true ^ 2 + (1 - θ) * a false ^ 2)
          + (θ * b true ^ 2 + (1 - θ) * b false ^ 2) * (W.card / (θ * (1 - θ)))) := by
        rw [integral_const_mul, hval]
    _ ≤ M ^ 2 * ((θ * a true ^ 2 + (1 - θ) * a false ^ 2)
          + (θ * b true ^ 2 + (1 - θ) * b false ^ 2) * (k / (θ * (1 - θ)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg M)
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hB)
        refine div_le_div_of_nonneg_right ?_ hpos.le
        exact_mod_cast hcard

end ActionMoments

/-! ### Part 7: the reward-corrected estimator -/

section RCEstimator

/-- The second-moment constant of the reward-corrected window functional. -/
lemma rc_second_moment_const (θ M : ℝ) (k : ℕ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    M ^ 2 * ((θ * score θ true ^ 2 + (1 - θ) * score θ false ^ 2)
        + (θ * rcWeight θ true ^ 2 + (1 - θ) * rcWeight θ false ^ 2) * (k / (θ * (1 - θ))))
      = M ^ 2 / (θ * (1 - θ)) * (1 + k * (1 + (1 - 2 * θ) ^ 2 / (θ * (1 - θ)))) := by
  have hθ : θ ≠ 0 := hθ0.ne'
  have hθ' : 1 - θ ≠ 0 := by linarith
  simp only [score, rcWeight, if_true, Bool.false_eq_true, if_false]
  field_simp
  ring

/-- On trajectories with rewards bounded by `M`, the reward-corrected estimator is the average
of the window functionals `Y_t (s_θ(Z_t) + w_θ(Z_t) ∑_{t - k ≤ u < t} s_θ(Z_u))`. -/
lemma rcEst_eq_win {S : Type} (θ M : ℝ) (T k : ℕ) (ω : Traj S T)
    (hω : ∀ t : Fin T, |Y t ω| ≤ M) :
    rcEst θ T k ω
      = (1 / (T : ℝ)) * ∑ t : Fin T,
          win θ M (score θ) (rcWeight θ) T ((t : ℕ) - k) t ω := by
  unfold rcEst win
  congr 1
  have hL : ∑ u : Fin T, score θ (Z u ω) * (Y u ω + ∑ t : Fin T,
        (if (u : ℕ) < (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then rcWeight θ (Z t ω) * Y t ω else 0))
      = ∑ t : Fin T, (Y t ω * score θ (Z t ω) + ∑ u : Fin T,
        (if (u : ℕ) < (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k
          then score θ (Z u ω) * (rcWeight θ (Z t ω) * Y t ω) else 0)) := by
    have hcomm : ∑ t : Fin T, ∑ u : Fin T,
          (if (u : ℕ) < (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k
            then score θ (Z u ω) * (rcWeight θ (Z t ω) * Y t ω) else 0)
        = ∑ u : Fin T, ∑ t : Fin T,
          (if (u : ℕ) < (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k
            then score θ (Z u ω) * (rcWeight θ (Z t ω) * Y t ω) else 0) := Finset.sum_comm
    rw [Finset.sum_add_distrib, hcomm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_add, Finset.mul_sum, mul_comm (Y u ω)]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp
  rw [hL]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [clip_eq_self (hω t), mul_add, ← mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h : (u : ℕ) < (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k
  · have h' : (t : ℕ) - k ≤ (u : ℕ) ∧ (u : ℕ) < (t : ℕ) := by omega
    rw [if_pos h, if_pos h']
    ring
  · have h' : ¬ ((t : ℕ) - k ≤ (u : ℕ) ∧ (u : ℕ) < (t : ℕ)) := by omega
    rw [if_neg h, if_neg h', mul_zero]

end RCEstimator

end TPG_VR

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T k : ℕ) (θ γ M : ℝ)
    (hT : 0 < T) (hk : k ≤ T) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hmix : E.Mixing T γ) (hM : E.RewardBound M) :
    variance (rcEst θ T k) (E.expLaw T θ)
      ≤ M ^ 2 / ((T : ℝ) * (θ * (1 - θ)))
          * (1 + (k : ℝ) * (1 + (1 - 2 * θ) ^ 2 / (θ * (1 - θ))))
          * (2 * (k : ℝ) + 3 + 4 * γ / (1 - γ)) := by
  show variance (rcEst θ T k) (E.trajLaw T (fun _ => θ)) ≤ _
  have hae : rcEst θ T k =ᵐ[E.trajLaw T (fun _ => θ)] fun ω =>
      (1 / (T : ℝ)) * ∑ t : Fin T,
        TPG_VR.win θ M (score θ) (rcWeight θ) T ((t : ℕ) - k) t ω := by
    filter_upwards [ae_abs_Y_le E T (fun _ => θ) M hM] with ω hω
    exact TPG_VR.rcEst_eq_win θ M T k ω hω
  rw [variance_congr hae]
  have hmain := TPG_VR.variance_win_avg_le E T k θ γ M
    (M ^ 2 / (θ * (1 - θ)) * (1 + k * (1 + (1 - 2 * θ) ^ 2 / (θ * (1 - θ)))))
    (score θ) (rcWeight θ) hT hθ0.le hθ1.le hγ0.le hγ1 hmix
    (fun E' N lo t ht =>
      (TPG_VR.integral_sq_win_le E' θ M hθ0 hθ1 (score θ) (rcWeight θ) k N lo t ht).trans
        (le_of_eq (TPG_VR.rc_second_moment_const θ M k hθ0 hθ1)))
  refine hmain.trans (le_of_eq ?_)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hθ' : (0 : ℝ) < 1 - θ := by linarith
  field_simp

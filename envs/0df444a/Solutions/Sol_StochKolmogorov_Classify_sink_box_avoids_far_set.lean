-- Prove2me | solution 1 for StochKolmogorov.Classify.sink_box_avoids_far_set
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T19:51:17.421994+00:00
-- url     : https://prove2.me/submissions/e7c16e01-fdc2-442d-9b5a-d43e30fd4182

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Classification
import Definitions.Def_StochKolmogorov_Classify_Faces
import Theorems.Thm_EthierKurtz_sde_markov_property_fd_conditional
import Definitions.Def_StochKolmogorov_Extinct_Extinction
import Theorems.Thm_StochKolmogorov_Extinct_one_step_5_11_5_12
import Theorems.Thm_StochKolmogorov_Extinct_proposition_5_1
import Theorems.Thm_StochKolmogorov_Extinct_lemma_5_2
import Theorems.Thm_StochKolmogorov_Extinct_inequalities_5_1_5_2
import Theorems.Thm_StochKolmogorov_Extinct_lemma_3_1
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Theorems.Thm_StochKolmogorov_Persist_orthant_invariance_closed
import Theorems.Thm_StochKolmogorov_Classify_short_time_positivity

set_option linter.all false
set_option Elab.async false


-- ===== Shift =====
section FlatM_Shift

/-! Path-shift invariance of the sink event (deterministic part of K4b): if the path `ω'` of `X'`
from `x'` is the path `ω` of `X` from `x` shifted by `t`, then `ω' ∈ extinctEvent C X' x' μ ↔
ω ∈ extinctEvent C X x μ`. The occupation measures differ by `O(t/T)`, the log rates by a factor
`(t+s)/s → 1`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.Shift

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

end StochKolmogorov.Classify.Shift

end FlatM_Shift
-- ===== K3 =====
section FlatM_K3

/-! K3 of theorem_1_3 (8f909832): each sink event is null-measurable, GIVEN the a.e. cover (K2) and
injectivity of `supp` on the measures (K1b). Idea: `E_μ ⊆ A_μ := Z_μ ∩ L_μ` with `A_μ` measurable, where
`Z_μ` = "the Cesaro means of `min 1 |X_i|` along integers tend to 0 for `i ∉ supp μ`" and
`L_μ` = "they have positive limsup for `i ∈ supp μ`" (both read at RATIONAL times, so `A_μ` is the preimage of a measurable path set `Gam`). `A_μ ∩ E_ν = ∅` for `ν ≠ μ` (it forces
`supp μ = supp ν`), so `A_μ \ E_μ` lies in the null set where the cover fails. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.K3

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- truncated coordinate size `min 1 |y_i|` -/
noncomputable def g (i : Fin n) (y : SDEState n) : ℝ := min 1 |y i|

/-- the path read at rational times (negative rationals read time 0) -/
def rpath (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω) : ℚ → SDEState n :=
  fun q => X x (q : ℝ).toNNReal ω

theorem measurable_rpath [MeasurableSpace Ω] (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (x : SDEState n) (hm : ∀ t, Measurable (X x t)) : Measurable (rpath X x) :=
  measurable_pi_lambda _ (fun q => hm _)

end StochKolmogorov.Classify.K3

end FlatM_K3
-- ===== PathMix =====
section FlatM_PathMix

/-! PM2b of K4b (8f909832): a mixture identity `P(Y ∈ Γ) = ∫ P(Z y ∈ Γ) dκ(y)` (with measurable
`y ↦ P(Z y ∈ Γ)`) that holds on measurable cylinders of the path space `ι → E` holds on every
set of the product σ-algebra (Dynkin's π-λ theorem). Used with `ι = ℚ`, `Y` = the time-`t`-shifted
rational path of `X x`, `Z y` = the rational path of `X y`, `κ = trans P X t x`. -/

set_option autoImplicit false

open MeasureTheory Filter MeasurableSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StochKolmogorov.Classify.PathMix

variable {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

end StochKolmogorov.Classify.PathMix

end FlatM_PathMix
-- ===== K4 =====
section FlatM_K4

/-! K4 of theorem_1_3 (8f909832): every sink has positive probability from every interior point, from
* `hinj` (K1b), `hcover` (K2), `h59` (sibling lemma_5_9), `hreach` (K4a irreducibility),
* `hFD` (PM1: finite-dimensional Markov identity for the rational path after time `t`).
Route: `E_x =ᵐ {shifted rational path ∈ Gam}` (K3 + path-shift invariance), the mixture identity on
the path σ-algebra (PathMix), and `P(E_y) ≥ 1/2` on an open box inside `Kbox μ 2 Δ`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.K4

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- the rational-time path after time `t` -/
def shiftPath (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (t : ℝ≥0) (ω : Ω) :
    ℚ → SDEState n :=
  fun q => X x (t + (q : ℝ).toNNReal) ω

open Classical in
/-- the rational-time path from `y` (a constant path off the orthant, where `X y` is unconstrained) -/
noncomputable def Zf (X : SDEState n → ℝ≥0 → Ω → SDEState n) (y : SDEState n) (ω : Ω) :
    ℚ → SDEState n :=
  if y ∈ orthant n then K3.rpath X y ω else fun _ => y

/-- PM1, the finite-dimensional Markov identity (open child). -/
def FDMarkov [MeasurableSpace Ω] (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Prop :=
  ∀ x ∈ openOrthant n, ∀ (t : ℝ≥0) (s : Finset ℚ) (F : (∀ i : s, SDEState n) →ᵇ ℝ≥0),
    (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
    Measurable (fun y => ∫⁻ ω, (F (s.restrict (Zf X y ω)) : ℝ≥0∞) ∂P) ∧
    ∫⁻ ω, (F (s.restrict (shiftPath X x t ω)) : ℝ≥0∞) ∂P =
      ∫⁻ y, ∫⁻ ω, (F (s.restrict (Zf X y ω)) : ℝ≥0∞) ∂P ∂(trans P X t x)

end StochKolmogorov.Classify.K4

end FlatM_K4
-- ===== FDM =====
section FlatM_FDM

/-! PM1 glue of K4b (8f909832): `K4.FDMarkov` (finite-dimensional Markov identity of the rational
path after time `t`, for Lipschitz test functions bounded by 1) from the child theorem
`EthierKurtz.sde_markov_property_fd_conditional` (case q = 0), applied to Lipschitz truncations of the Kolmogorov
coefficients (copied from the accepted `Persist.markov_property` reduction, namespace renamed). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.FDM

open StochKolmogorov.Classify EthierKurtz

theorem euc_norm_le_sum' {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖ ≤ ∑ k, |v k| := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ k, ‖v k‖ ^ 2) ≤ √((∑ k, |v k|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Real.norm_eq_abs]
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
    _ = ∑ k, |v k| := Real.sqrt_sq (Finset.sum_nonneg fun k _ => abs_nonneg _)

variable {d : ℕ}
theorem coord_abs_le_state (x : SDEState d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i; rwa [Real.norm_eq_abs] at this

theorem lipOn_of_locLip_compact {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {s K : Set α} {f : α → β} (hf : LocallyLipschitzOn s f) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, ∀ y ∈ K, dist (f x) (f y) ≤ L * dist x y := by
  classical
  have hloc : ∀ x : K, ∃ r > (0 : ℝ), ∃ L : ℝ≥0, LipschitzOnWith L f (Metric.ball (x : α) r ∩ s) := by
    intro x
    obtain ⟨L, t, ht, hL⟩ := hf (hKs x.2)
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhdsWithin_iff.1 ht
    exact ⟨r, hr, L, hL.mono hrt⟩
  choose r hr L hL using hloc
  have hcov : K ⊆ ⋃ x : K, Metric.ball (x : α) (r x / 2) := fun y hy =>
    Set.mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (half_pos (hr _))⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover _ (fun _ => Metric.isOpen_ball) hcov
  -- bound on `f` over `K`
  have hbdd : Bornology.IsBounded (f '' K) :=
    (hK.image_of_continuousOn (hf.continuousOn.mono hKs)).isBounded
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hbdd
  by_cases hTn : T.Nonempty
  · set δ : ℝ := T.inf' hTn (fun x => r x / 2) with hδ
    have hδpos : 0 < δ := by
      rw [hδ, Finset.lt_inf'_iff]; exact fun x _ => half_pos (hr x)
    set Lm : ℝ≥0 := T.sup L
    refine ⟨Lm + max C 0 / δ, by positivity, fun x hx y hy => ?_⟩
    by_cases hxy : dist x y < δ
    · obtain ⟨z, hzT, hxz⟩ : ∃ z ∈ T, x ∈ Metric.ball (z : α) (r z / 2) := by
        have := hT hx; simp only [Set.mem_iUnion] at this
        obtain ⟨z, hz, h⟩ := this; exact ⟨z, hz, h⟩
      have hδz : δ ≤ r z / 2 := Finset.inf'_le _ hzT
      have hx' : x ∈ Metric.ball (z : α) (r z) ∩ s :=
        ⟨Metric.ball_subset_ball (by linarith [hr z]) hxz, hKs hx⟩
      have hy' : y ∈ Metric.ball (z : α) (r z) ∩ s := by
        refine ⟨?_, hKs hy⟩
        rw [Metric.mem_ball] at hxz ⊢
        calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
          _ < δ + r z / 2 := by rw [dist_comm]; exact add_lt_add hxy hxz
          _ ≤ r z := by linarith
      have h1 := (hL z).dist_le_mul x hx' y hy'
      have h2 : (L z : ℝ) ≤ Lm := by exact_mod_cast Finset.le_sup (f := L) hzT
      have h3 : 0 ≤ max C 0 / δ * dist x y := by positivity
      nlinarith [dist_nonneg (x := x) (y := y)]
    · replace hxy := not_lt.1 hxy
      have h1 : dist (f x) (f y) ≤ max C 0 :=
        (hC ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩).trans (le_max_left _ _)
      have h2 : max C 0 ≤ max C 0 / δ * dist x y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
        exact mul_le_mul_of_nonneg_left hxy (le_max_right _ _)
      have h3 : 0 ≤ (Lm : ℝ) * dist x y := by positivity
      nlinarith
  · have hK0 : K = ∅ := by
      rw [Finset.not_nonempty_iff_eq_empty] at hTn
      subst hTn; simpa using hT
    exact ⟨0, le_rfl, fun x hx => by simp [hK0] at hx⟩


/-- Coordinatewise 1-Lipschitz maps are 1-Lipschitz in the Euclidean norm. -/
theorem norm_sub_le_of_coord {x y x' y' : SDEState d} (h : ∀ i, |x' i - y' i| ≤ |x i - y i|) :
    ‖x' - y'‖ ≤ ‖x - y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  simp only [PiLp.sub_apply, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

theorem clamp1_lip (M a b : ℝ) : |max (-M) (min M a) - max (-M) (min M b)| ≤ |a - b| := by
  rw [abs_le]
  have h1 := le_abs_self (a - b); have h2 := neg_abs_le (a - b)
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

/-- Coordinate clamp to the box `[-M, M]^d`. -/
noncomputable def clampM (M : ℝ) (x : SDEState d) : SDEState d :=
  WithLp.toLp 2 (fun i => max (-M) (min M (x i)))

theorem clampM_apply (M : ℝ) (x : SDEState d) (i : Fin d) :
    clampM M x i = max (-M) (min M (x i)) := rfl

theorem clampM_lip (M : ℝ) (x y : SDEState d) : ‖clampM M x - clampM M y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by rw [clampM_apply, clampM_apply]; exact clamp1_lip _ _ _

theorem clampM_abs_le {M : ℝ} (hM : 0 ≤ M) (x : SDEState d) (i : Fin d) : |clampM M x i| ≤ M := by
  rw [clampM_apply, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem clampM_eq {M : ℝ} {x : SDEState d} (hx : ‖x‖ ≤ M) : clampM M x = x := by
  ext i
  rw [clampM_apply]
  have := (coord_abs_le_state x i).trans hx
  rw [abs_le] at this
  rw [min_eq_right this.2, max_eq_right this.1]

theorem norm_le_card_mul {M : ℝ} {x : SDEState d} (hx : ∀ i, |x i| ≤ M) : ‖x‖ ≤ d * M := by
  calc ‖x‖ ≤ ∑ i, |x i| := euc_norm_le_sum' x
    _ ≤ ∑ _i : Fin d, M := Finset.sum_le_sum fun i _ => hx i
    _ = d * M := by simp

/-- b9: a truncation family for coordinate functions that are Lipschitz on every box. -/
theorem trunc_family {ι : Type*} [Fintype ι] (φ : ι → SDEState d → ℝ)
    (hL : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ k x y, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |φ k x - φ k y| ≤ L * ‖x - y‖) :
    ∃ (s₁ : ℕ → SDEState d → EuclideanSpace ℝ ι) (S L : ℕ → ℝ), (∀ R, Continuous (s₁ R)) ∧
      (∀ R, 0 ≤ L R) ∧ (∀ R x, ‖s₁ R x‖ ≤ S R) ∧
      (∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖) ∧
      (∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = WithLp.toLp 2 (fun k => φ k x)) := by
  classical
  choose Lb hLb0 hLb using fun R : ℕ => hL ((R : ℝ) + 3) (by positivity)
  set s₁ : ℕ → SDEState d → EuclideanSpace ℝ ι :=
    fun R x => WithLp.toLp 2 (fun k => φ k (clampM ((R : ℝ) + 3) x)) with hs₁
  have hM : ∀ R : ℕ, (0 : ℝ) ≤ (R : ℝ) + 3 := fun R => by positivity
  have hlip : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ (Fintype.card ι * Lb R) * ‖x - y‖ := by
    intro R x y
    calc ‖s₁ R x - s₁ R y‖ ≤ ∑ k, |(s₁ R x - s₁ R y) k| := euc_norm_le_sum' _
      _ ≤ ∑ _k : ι, Lb R * ‖x - y‖ := by
          apply Finset.sum_le_sum; intro k _
          simp only [hs₁, PiLp.sub_apply]
          exact (hLb R k _ _ (clampM_abs_le (hM R) x) (clampM_abs_le (hM R) y)).trans
            (mul_le_mul_of_nonneg_left (clampM_lip _ _ _) (hLb0 R))
      _ = (Fintype.card ι * Lb R) * ‖x - y‖ := by simp [mul_assoc]
  refine ⟨s₁, fun R => ∑ k : ι, (|φ k (clampM ((R : ℝ) + 3) 0)| + Lb R * (2 * (d * ((R : ℝ) + 3)))),
    fun R => Fintype.card ι * Lb R, fun R => ?_, fun R => by have := hLb0 R; positivity,
    fun R x => ?_, hlip, fun R x hx => ?_⟩
  · exact LipschitzWith.continuous (K := ⟨Fintype.card ι * Lb R, by have := hLb0 R; positivity⟩)
      (LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm]; exact hlip R x y)
  · calc ‖s₁ R x‖ ≤ ∑ k, |s₁ R x k| := euc_norm_le_sum' _
      _ ≤ _ := by
          apply Finset.sum_le_sum; intro k _
          simp only [hs₁]
          set M : ℝ := (R : ℝ) + 3
          have hc := hLb R k _ _ (clampM_abs_le (hM R) x) (clampM_abs_le (hM R) 0)
          have hn : ‖clampM M x - clampM M 0‖ ≤ 2 * (d * M) := by
            calc ‖clampM M x - clampM M 0‖ ≤ ‖clampM M x‖ + ‖clampM M 0‖ := norm_sub_le _ _
              _ ≤ d * M + d * M := add_le_add (norm_le_card_mul (clampM_abs_le (hM R) x))
                  (norm_le_card_mul (clampM_abs_le (hM R) 0))
              _ = 2 * (d * M) := by ring
          have := mul_le_mul_of_nonneg_left hn (hLb0 R)
          have h3 := abs_sub_abs_le_abs_sub (φ k (clampM M x)) (φ k (clampM M 0))
          linarith
  · simp only [hs₁, clampM_eq hx]

variable {n : ℕ}

theorem posPart_apply' (x : SDEState n) (i : Fin n) : posPart x i = max (x i) 0 := rfl

theorem posPart_lip (x y : SDEState n) : ‖posPart x - posPart y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by
    rw [posPart_apply', posPart_apply']; exact abs_max_sub_max_le_abs _ _ _

theorem posPart_mem_orthant (x : SDEState n) : posPart x ∈ orthant n := fun i => by
  rw [posPart_apply']; exact le_max_right _ _

theorem continuous_posPart : Continuous (posPart (n := n)) :=
  LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]; exact posPart_lip x y)

/-- A locally Lipschitz function on the orthant, read at `x⁺`, is Lipschitz and bounded on boxes. -/
theorem locLip_posPart_box {h : SDEState n → ℝ} (hh : LocallyLipschitzOn (orthant n) h)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ L G : ℝ, 0 ≤ L ∧ 0 ≤ G ∧ ∀ x y : SDEState n, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |h (posPart x) - h (posPart y)| ≤ L * ‖x - y‖ ∧ |h (posPart x)| ≤ G := by
  set K : Set (SDEState n) := {y | ∀ i, 0 ≤ y i ∧ y i ≤ M} with hKdef
  have hKc : IsClosed K := by
    have : K = ⋂ i, ({y : SDEState n | 0 ≤ y i} ∩ {y | y i ≤ M}) := by
      ext y; simp [hKdef, forall_and]
    rw [this]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)).inter
      (isClosed_le (PiLp.continuous_apply 2 _ i) continuous_const)
  have hKb : Bornology.IsBounded K := (Metric.isBounded_closedBall (x := (0 : SDEState n))
      (r := n * M)).subset fun y hy => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_card_mul fun i => by rw [abs_of_nonneg (hy i).1]; exact (hy i).2
  have hKo : K ⊆ orthant n := fun y hy i => (hy i).1
  obtain ⟨L, hL0, hL⟩ := lipOn_of_locLip_compact hh (Metric.isCompact_of_isClosed_isBounded hKc hKb) hKo
  have hpK : ∀ x : SDEState n, (∀ i, |x i| ≤ M) → posPart x ∈ K := fun x hx i => by
    rw [posPart_apply']
    exact ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hx i)) hM⟩
  have h0 : ∀ i, |(0 : SDEState n) i| ≤ M := fun i => by simpa using hM
  refine ⟨L, L * (n * M) + |h (posPart 0)|, hL0, by positivity, fun x y hx hy => ⟨?_, ?_⟩⟩
  · have := hL _ (hpK x hx) _ (hpK y hy)
    rw [Real.dist_eq, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_left (posPart_lip x y) hL0)
  · have h1 := hL _ (hpK x hx) _ (hpK 0 h0)
    rw [Real.dist_eq, dist_eq_norm] at h1
    have h2 : ‖posPart x - posPart (0 : SDEState n)‖ ≤ n * M := by
      calc ‖posPart x - posPart (0 : SDEState n)‖ ≤ ‖x - 0‖ := posPart_lip x 0
        _ = ‖x‖ := by rw [sub_zero]
        _ ≤ n * M := norm_le_card_mul hx
    have h3 := abs_sub_abs_le_abs_sub (h (posPart x)) (h (posPart 0))
    have h4 := mul_le_mul_of_nonneg_left h2 hL0
    linarith

/-- Products `x_i · h(x⁺) · c` are Lipschitz on boxes. -/
theorem prod_box_lip {h : SDEState n → ℝ} (hh : LocallyLipschitzOn (orthant n) h) (c : ℝ) (i : Fin n)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : SDEState n, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x i * h (posPart x) * c - y i * h (posPart y) * c| ≤ L * ‖x - y‖ := by
  obtain ⟨L, G, hL0, hG0, hLG⟩ := locLip_posPart_box hh hM
  refine ⟨|c| * (M * L + G), by positivity, fun x y hx hy => ?_⟩
  obtain ⟨h1, -⟩ := hLG x y hx hy
  obtain ⟨-, h2⟩ := hLG y x hy hx
  have hxy : |x i - y i| ≤ ‖x - y‖ := by
    have := coord_abs_le_state (x - y) i; rwa [PiLp.sub_apply] at this
  have e : x i * h (posPart x) * c - y i * h (posPart y) * c =
      c * (x i * (h (posPart x) - h (posPart y)) + h (posPart y) * (x i - y i)) := by ring
  rw [e, abs_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  calc |x i * (h (posPart x) - h (posPart y)) + h (posPart y) * (x i - y i)|
      ≤ |x i| * |h (posPart x) - h (posPart y)| + |h (posPart y)| * |x i - y i| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ M * (L * ‖x - y‖) + G * ‖x - y‖ := by
        gcongr
        · exact hx i
    _ = (M * L + G) * ‖x - y‖ := by ring

/-- b11: the Kolmogorov coefficients are continuous and have truncation families as needed by
`markov_core`. -/
theorem kolm_trunc (C : Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    Continuous (fun x : SDEState n => diffusion C (0, x)) ∧
    Continuous (fun x : SDEState n => drift C (0, x)) ∧
    ∃ (s₁ : ℕ → SDEState n → SDEDiffusion n) (b₁ : ℕ → SDEState n → SDEState n) (S L : ℕ → ℝ),
      (∀ R, Continuous (s₁ R)) ∧ (∀ R, Continuous (b₁ R)) ∧ (∀ R, 0 ≤ L R) ∧
      (∀ R x, ‖s₁ R x‖ ≤ S R ∧ ‖b₁ R x‖ ≤ S R) ∧
      (∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L R * ‖x - y‖) ∧
      (∀ (R : ℕ) (x : SDEState n), ‖x‖ ≤ (R : ℝ) + 3 →
        s₁ R x = diffusion C (0, x) ∧ b₁ R x = drift C (0, x)) := by
  have hgc : ∀ i, Continuous fun x : SDEState n => C.g i (posPart x) := fun i =>
    (hC i).2.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hfc : ∀ i, Continuous fun x : SDEState n => C.f i (posPart x) := fun i =>
    (hC i).1.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  refine ⟨(PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      (((PiLp.continuous_apply 2 _ k.1).mul (hgc k.1)).mul continuous_const)),
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      ((PiLp.continuous_apply 2 _ k).mul (hfc k))), ?_⟩
  -- the two coordinate families
  have hLs : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ (k : Fin n × Fin n) (x y : SDEState n),
      (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x k.1 * C.g k.1 (posPart x) * C.Γ k.2 k.1 - y k.1 * C.g k.1 (posPart y) * C.Γ k.2 k.1|
        ≤ L * ‖x - y‖ := by
    intro M hM
    choose L hL0 hL using fun k : Fin n × Fin n => prod_box_lip (hC k.1).2 (C.Γ k.2 k.1) k.1 hM
    refine ⟨∑ k, L k, Finset.sum_nonneg fun k _ => hL0 k, fun k x y hx hy => ?_⟩
    exact (hL k x y hx hy).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hL0 k) (Finset.mem_univ k)) (norm_nonneg _))
  have hLb : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ (k : Fin n) (x y : SDEState n),
      (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x k * C.f k (posPart x) * 1 - y k * C.f k (posPart y) * 1| ≤ L * ‖x - y‖ := by
    intro M hM
    choose L hL0 hL using fun k : Fin n => prod_box_lip (hC k).1 1 k hM
    refine ⟨∑ k, L k, Finset.sum_nonneg fun k _ => hL0 k, fun k x y hx hy => ?_⟩
    exact (hL k x y hx hy).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hL0 k) (Finset.mem_univ k)) (norm_nonneg _))
  obtain ⟨s₁, S1, L1, hs1c, hL1, hS1, hl1, he1⟩ := trunc_family _ hLs
  obtain ⟨b₁, S2, L2, hb1c, hL2, hS2, hl2, he2⟩ := trunc_family _ hLb
  refine ⟨s₁, b₁, fun R => max (S1 R) (S2 R), fun R => max (L1 R) (L2 R), hs1c, hb1c,
    fun R => (hL1 R).trans (le_max_left _ _), fun R x => ⟨(hS1 R x).trans (le_max_left _ _),
      (hS2 R x).trans (le_max_right _ _)⟩, fun R x y => ⟨(hl1 R x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)), (hl2 R x y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩, fun R x hx => ⟨?_, ?_⟩⟩
  · rw [he1 R x hx]; rfl
  · rw [he2 R x hx]; simp only [mul_one]; rfl

theorem orthant_isClosed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {y : SDEState n | 0 ≤ y i} := by ext y; simp [orthant]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

variable {n : ℕ}

theorem fdMarkov_of {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n) :
    K4.FDMarkov P X := by
  classical
  obtain ⟨hP, hB, hXs⟩ := hX
  haveI := hP
  obtain ⟨hσc, hbc, s₁, b₁, S, L, hs₁, hb₁, hL, hSg, hLg, hag⟩ := kolm_trunc C hC
  have hX' : ∀ y ∈ orthant n, SolvesBrownianSDE P (fun p => (fun x => diffusion C (0, x)) p.2)
      (fun p => (fun x => drift C (0, x)) p.2) B (fun _ => y) (X y) := fun y hy => hXs y hy
  intro x hx t s G hGL hG1
  obtain ⟨KG, hGL⟩ := hGL
  have hxo : x ∈ orthant n := fun i => (hx i).le
  let e : Fin s.card ≃ s := s.equivFin.symm
  let τ : Fin s.card → ℝ≥0 := fun i => (((e i : ℚ) : ℝ)).toNNReal
  let F : (Fin s.card → SDEState n) → ℝ := fun v => ((G (fun j => v (e.symm j)) : ℝ≥0) : ℝ)
  have hFc : Continuous F :=
    NNReal.continuous_coe.comp (G.continuous.comp (continuous_pi fun j => continuous_apply _))
  have hF0 : ∀ v, 0 ≤ F v := fun v => (G _).2
  have hFK : ∀ v, |F v| ≤ 1 := fun v => by
    rw [abs_of_nonneg (hF0 v)]; exact_mod_cast hG1 _
  have hFL : ∀ v v', |F v - F v'| ≤ (KG : ℝ) * ∑ i, ‖v i - v' i‖ := by
    intro v v'
    have h1 := hGL.dist_le_mul (fun j => v (e.symm j)) (fun j => v' (e.symm j))
    rw [NNReal.dist_eq] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ KG.2)
    refine (dist_pi_le_iff (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun j => ?_
    rw [dist_eq_norm]
    exact Finset.single_le_sum (f := fun i => ‖v i - v' i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ (e.symm j))
  obtain ⟨g, hgm, hgK, hgD, hgM'⟩ := EthierKurtz.sde_markov_property_fd_conditional hB hσc hbc s₁ b₁
    S L hs₁ hb₁ hL hSg hLg hag hX' τ hFc.measurable hFK KG.2 hFL
  have hgM := fun x hx s' hD => by
    have h1 := hgM' x hx s' hD 0 (fun j => j.elim0) (fun j => j.elim0) (fun _ => (1 : ℝ))
      measurable_const 1 0 (fun v => by simp) le_rfl (fun v v' => by simp)
    simpa only [one_mul] using h1
  have hGF : ∀ f : ℚ → SDEState n, ((G (s.restrict f) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (F (fun i => f (e i))) := by
    intro f
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 2
    congr 1
    funext j
    simp only [Equiv.apply_symm_apply, Finset.restrict]
  have hlin : ∀ Φ : Ω → (Fin s.card → SDEState n), Measurable Φ →
      ∫⁻ ω, ENNReal.ofReal (F (Φ ω)) ∂P = ENNReal.ofReal (∫ ω, F (Φ ω) ∂P) := by
    intro Φ hΦ
    refine (ofReal_integral_eq_lintegral_ofReal ?_ (Eventually.of_forall fun ω => hF0 _)).symm
    exact (integrable_const (1 : ℝ)).mono' (hFc.measurable.comp hΦ).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFK _)
  let h : SDEState n → ℝ≥0∞ := (orthant n).piecewise (fun y => ENNReal.ofReal (g y))
    (fun y => ((G (s.restrict (fun _ : ℚ => y)) : ℝ≥0) : ℝ≥0∞))
  have hhm : Measurable h := by
    refine Measurable.piecewise orthant_isClosed.measurableSet (ENNReal.measurable_ofReal.comp hgm) ?_
    exact measurable_coe_nnreal_ennreal.comp
      (G.continuous.comp (continuous_pi fun j => continuous_id)).measurable
  have hheq : ∀ y, ∫⁻ ω, ((G (s.restrict (K4.Zf X y ω)) : ℝ≥0) : ℝ≥0∞) ∂P = h y := by
    intro y
    by_cases hy : y ∈ orthant n
    · simp only [h, Set.piecewise_eq_of_mem _ _ _ hy, K4.Zf, if_pos hy]
      simp_rw [hGF]
      rw [hgD y hy]
      exact hlin (fun ω i => X y (τ i) ω) (measurable_pi_lambda _ fun i => (hXs y hy).1 _)
    · simp only [h, Set.piecewise_eq_of_notMem _ _ _ hy, K4.Zf, if_neg hy]
      simp
  have hgI : Integrable (fun ω => g (X x t ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hgm.comp ((hXs x hxo).1 t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgK _)
  have hg0 : 0 ≤ᵐ[P] fun ω => g (X x t ω) := by
    filter_upwards [hinv x hxo t] with ω hω
    show (0 : ℝ) ≤ g (X x t ω)
    rw [hgD _ hω]
    exact integral_nonneg fun ω' => hF0 (fun i => X (X x t ω) (τ i) ω')
  refine ⟨?_, ?_⟩
  · have : (fun y => ∫⁻ ω, ((G (s.restrict (K4.Zf X y ω)) : ℝ≥0) : ℝ≥0∞) ∂P) = h := funext hheq
    rw [this]; exact hhm
  calc ∫⁻ ω, ((G (s.restrict (K4.shiftPath X x t ω)) : ℝ≥0) : ℝ≥0∞) ∂P
        = ∫⁻ ω, ENNReal.ofReal (F (fun i => K4.shiftPath X x t ω (e i))) ∂P :=
          lintegral_congr fun ω => hGF _
    _ = ENNReal.ofReal (∫ ω, F (fun i => X x (t + τ i) ω) ∂P) :=
          hlin (fun ω i => X x (t + τ i) ω) (measurable_pi_lambda _ fun i => (hXs x hxo).1 _)
    _ = ENNReal.ofReal (∫ ω, g (X x t ω) ∂P) := by rw [hgM x hxo t (hinv x hxo t)]
    _ = ∫⁻ ω, ENNReal.ofReal (g (X x t ω)) ∂P := ofReal_integral_eq_lintegral_ofReal hgI hg0
    _ = ∫⁻ ω, h (X x t ω) ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hinv x hxo t] with ω hω
          simp only [h, Set.piecewise_eq_of_mem _ _ _ hω]
    _ = ∫⁻ y, h y ∂(trans P X t x) := by
          rw [trans, lintegral_map hhm ((hXs x hxo).1 t)]
    _ = ∫⁻ y, ∫⁻ ω, ((G (s.restrict (K4.Zf X y ω)) : ℝ≥0) : ℝ≥0∞) ∂P ∂(trans P X t x) :=
          lintegral_congr fun y => (hheq y).symm

end StochKolmogorov.Classify.FDM

end FlatM_FDM
-- ===== FDMC =====
section FlatM_FDMC

/-! K2-mc step 1 (8f909832): conditional finite-dimensional Markov identity, tested against a
Lipschitz functional `G` of finitely many past rational times in `(0, t]`, from child C
(`EthierKurtz.sde_markov_property_fd_conditional`) with `q = s'.card`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.FDMC

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- past rational times `q ∈ (0, t]` -/
def Past (t : ℝ≥0) : Type := {q : ℚ // 0 < q ∧ (q : ℝ) ≤ t}

/-- the past rational path up to time `t` -/
def past (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (t : ℝ≥0) (ω : Ω) :
    Past t → SDEState n :=
  fun q => X x ((q.1 : ℚ) : ℝ).toNNReal ω

theorem measurable_past [MeasurableSpace Ω] (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (x : SDEState n) (t : ℝ≥0) (hm : ∀ s, Measurable (X x s)) : Measurable (past X x t) :=
  measurable_pi_lambda _ fun _ => hm _

theorem fdMarkovCond_of [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n) :
    ∀ x ∈ openOrthant n, ∀ (t : ℝ≥0) (s' : Finset (Past t)) (G : (∀ i : s', SDEState n) →ᵇ ℝ≥0),
      (∃ K, LipschitzWith K G) → (∀ w, G w ≤ 1) →
      ∀ (s : Finset ℚ) (F : (∀ i : s, SDEState n) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      ∫⁻ ω, (G (s'.restrict (past X x t ω)) : ℝ≥0∞) * (F (s.restrict (K4.shiftPath X x t ω)) : ℝ≥0∞) ∂P =
        ∫⁻ ω, (G (s'.restrict (past X x t ω)) : ℝ≥0∞) *
          ∫⁻ ω', (F (s.restrict (K4.Zf X (X x t ω) ω')) : ℝ≥0∞) ∂P ∂P := by
  classical
  obtain ⟨hP, hB, hXs⟩ := hX
  haveI := hP
  obtain ⟨hσc, hbc, s₁, b₁, S, L, hs₁, hb₁, hL, hSg, hLg, hag⟩ := FDM.kolm_trunc C hC
  have hX' : ∀ y ∈ orthant n, SolvesBrownianSDE P (fun p => (fun x => diffusion C (0, x)) p.2)
      (fun p => (fun x => drift C (0, x)) p.2) B (fun _ => y) (X y) := fun y hy => hXs y hy
  intro x hx t s' G hGL hG1 s F hFL hF1
  obtain ⟨KG, hGL⟩ := hGL
  obtain ⟨KF, hFL⟩ := hFL
  have hxo : x ∈ orthant n := fun i => (hx i).le
  -- the future functional
  let e : Fin s.card ≃ s := s.equivFin.symm
  let τ : Fin s.card → ℝ≥0 := fun i => (((e i : ℚ) : ℝ)).toNNReal
  let Fr : (Fin s.card → SDEState n) → ℝ := fun v => ((F (fun j => v (e.symm j)) : ℝ≥0) : ℝ)
  have hFc : Continuous Fr :=
    NNReal.continuous_coe.comp (F.continuous.comp (continuous_pi fun j => continuous_apply _))
  have hF0 : ∀ v, 0 ≤ Fr v := fun v => (F _).2
  have hFK : ∀ v, |Fr v| ≤ 1 := fun v => by
    rw [abs_of_nonneg (hF0 v)]; exact_mod_cast hF1 _
  have hFLr : ∀ v v', |Fr v - Fr v'| ≤ (KF : ℝ) * ∑ i, ‖v i - v' i‖ := by
    intro v v'
    have h1 := hFL.dist_le_mul (fun j => v (e.symm j)) (fun j => v' (e.symm j))
    rw [NNReal.dist_eq] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ KF.2)
    refine (dist_pi_le_iff (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun j => ?_
    rw [dist_eq_norm]
    exact Finset.single_le_sum (f := fun i => ‖v i - v' i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ (e.symm j))
  -- the past functional
  let e' : Fin s'.card ≃ s' := s'.equivFin.symm
  let u : Fin s'.card → ℝ≥0 := fun j => ((((e' j).1).1 : ℚ) : ℝ).toNNReal
  have hu : ∀ j, 0 < u j ∧ u j ≤ t := fun j =>
    ⟨Real.toNNReal_pos.2 (by exact_mod_cast ((e' j).1).2.1),
      Real.toNNReal_le_iff_le_coe.2 ((e' j).1).2.2⟩
  let Gr : (Fin s'.card → SDEState n) → ℝ := fun v => ((G (fun j => v (e'.symm j)) : ℝ≥0) : ℝ)
  have hGc : Continuous Gr :=
    NNReal.continuous_coe.comp (G.continuous.comp (continuous_pi fun j => continuous_apply _))
  have hG0 : ∀ v, 0 ≤ Gr v := fun v => (G _).2
  have hGK : ∀ v, |Gr v| ≤ 1 := fun v => by
    rw [abs_of_nonneg (hG0 v)]; exact_mod_cast hG1 _
  have hGLr : ∀ v v', |Gr v - Gr v'| ≤ (KG : ℝ) * ∑ i, ‖v i - v' i‖ := by
    intro v v'
    have h1 := hGL.dist_le_mul (fun j => v (e'.symm j)) (fun j => v' (e'.symm j))
    rw [NNReal.dist_eq] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ KG.2)
    refine (dist_pi_le_iff (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun j => ?_
    rw [dist_eq_norm]
    exact Finset.single_le_sum (f := fun i => ‖v i - v' i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ (e'.symm j))
  obtain ⟨g, hgm, hgK, hgD, hgM⟩ := EthierKurtz.sde_markov_property_fd_conditional hB hσc hbc s₁ b₁
    S L hs₁ hb₁ hL hSg hLg hag hX' τ hFc.measurable hFK KF.2 hFLr
  have key := hgM x hxo t (hinv x hxo t) s'.card u hu Gr hGc.measurable 1 KG hGK KG.2 hGLr
  have hFeq : ∀ f : ℚ → SDEState n, ((F (s.restrict f) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (Fr (fun i => f (e i))) := by
    intro f
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 2
    congr 1
    funext j
    simp only [Equiv.apply_symm_apply, Finset.restrict]
  have hGeq : ∀ ω, ((G (s'.restrict (past X x t ω)) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (Gr (fun j => X x (u j) ω)) := by
    intro ω
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 2
    congr 1
    funext j
    simp only [u, past, Equiv.apply_symm_apply, Finset.restrict]
  have hlin : ∀ Φ : Ω → (Fin s.card → SDEState n), Measurable Φ →
      ∫⁻ ω, ENNReal.ofReal (Fr (Φ ω)) ∂P = ENNReal.ofReal (∫ ω, Fr (Φ ω) ∂P) := by
    intro Φ hΦ
    refine (ofReal_integral_eq_lintegral_ofReal ?_ (Eventually.of_forall fun ω => hF0 _)).symm
    exact (integrable_const (1 : ℝ)).mono' (hFc.measurable.comp hΦ).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFK _)
  let h : SDEState n → ℝ≥0∞ := (orthant n).piecewise (fun y => ENNReal.ofReal (g y))
    (fun y => ((F (s.restrict (fun _ : ℚ => y)) : ℝ≥0) : ℝ≥0∞))
  have hheq : ∀ y, ∫⁻ ω, ((F (s.restrict (K4.Zf X y ω)) : ℝ≥0) : ℝ≥0∞) ∂P = h y := by
    intro y
    by_cases hy : y ∈ orthant n
    · simp only [h, Set.piecewise_eq_of_mem _ _ _ hy, K4.Zf, if_pos hy]
      simp_rw [hFeq]
      rw [hgD y hy]
      exact hlin (fun ω i => X y (τ i) ω) (measurable_pi_lambda _ fun i => (hXs y hy).1 _)
    · simp only [h, Set.piecewise_eq_of_notMem _ _ _ hy, K4.Zf, if_neg hy]
      simp
  have hGm : Measurable fun ω => Gr (fun j => X x (u j) ω) :=
    hGc.measurable.comp (f := fun ω j => X x (u j) ω) (measurable_pi_lambda _ fun j => (hXs x hxo).1 _)
  have hFm : Measurable fun ω => Fr (fun i => X x (t + τ i) ω) :=
    hFc.measurable.comp (f := fun ω i => X x (t + τ i) ω)
      (measurable_pi_lambda _ fun i => (hXs x hxo).1 _)
  have hgXm : Measurable fun ω => g (X x t ω) := hgm.comp ((hXs x hxo).1 t)
  have hI1 : Integrable (fun ω => Gr (fun j => X x (u j) ω) * Fr (fun i => X x (t + τ i) ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hGm.mul hFm).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (hGK (fun j => X x (u j) ω)) (abs_nonneg _) (hFK (fun i => X x (t + τ i) ω)))
  have hI2 : Integrable (fun ω => Gr (fun j => X x (u j) ω) * g (X x t ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hGm.mul hgXm).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (hGK (fun j => X x (u j) ω)) (abs_nonneg _) (hgK (X x t ω)))
  have hg0 : ∀ᵐ ω ∂P, 0 ≤ g (X x t ω) := by
    filter_upwards [hinv x hxo t] with ω hω
    rw [hgD _ hω]
    exact integral_nonneg fun ω' => hF0 (fun i => X (X x t ω) (τ i) ω')
  calc ∫⁻ ω, (G (s'.restrict (past X x t ω)) : ℝ≥0∞) * (F (s.restrict (K4.shiftPath X x t ω)) : ℝ≥0∞) ∂P
        = ∫⁻ ω, ENNReal.ofReal (Gr (fun j => X x (u j) ω) * Fr (fun i => X x (t + τ i) ω)) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [hGeq, hFeq, ENNReal.ofReal_mul (hG0 (fun j => X x (u j) ω))]
          rfl
    _ = ENNReal.ofReal (∫ ω, Gr (fun j => X x (u j) ω) * Fr (fun i => X x (t + τ i) ω) ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hI1
            (Eventually.of_forall fun ω => mul_nonneg (hG0 (fun j => X x (u j) ω))
              (hF0 (fun i => X x (t + τ i) ω)))).symm
    _ = ENNReal.ofReal (∫ ω, Gr (fun j => X x (u j) ω) * g (X x t ω) ∂P) := by rw [key]
    _ = ∫⁻ ω, ENNReal.ofReal (Gr (fun j => X x (u j) ω) * g (X x t ω)) ∂P :=
          ofReal_integral_eq_lintegral_ofReal hI2
            (hg0.mono fun ω hω => mul_nonneg (hG0 (fun j => X x (u j) ω)) hω)
    _ = ∫⁻ ω, (G (s'.restrict (past X x t ω)) : ℝ≥0∞) *
          ∫⁻ ω', (F (s.restrict (K4.Zf X (X x t ω) ω')) : ℝ≥0∞) ∂P ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hinv x hxo t] with ω hω
          rw [hheq, hGeq, ENNReal.ofReal_mul (hG0 (fun j => X x (u j) ω))]
          simp only [h, Set.piecewise_eq_of_mem _ _ _ hω]

end StochKolmogorov.Classify.FDMC

end FlatM_FDMC
-- ===== PathMix2 =====
section FlatM_PathMix2

/-! K2-mc (8f909832): two-measure version of PathMix. `Q` (finite; e.g. `P` weighted by a past
functional) governs `Y`, the probability `P` governs `Z y`, and `κ` (finite, same mass as `Q`)
mixes: `Q(Y ∈ Γ) = ∫ P(Z y ∈ Γ) dκ(y)`. Used for the conditional (past-weighted) path Markov
identity: `Q = P.withDensity (G ∘ past)`, `κ = Q.map (X x s)`. -/

set_option autoImplicit false

open MeasureTheory Filter MeasurableSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StochKolmogorov.Classify.PathMix2

variable {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

def MixQ {W : Type*} [MeasurableSpace W] (Q P : Measure Ω) (Y : Ω → W) (Z : E → Ω → W)
    (κ : Measure E) (Γ : Set W) : Prop :=
  Measurable (fun y => P (Z y ⁻¹' Γ)) ∧ Q (Y ⁻¹' Γ) = ∫⁻ y, P (Z y ⁻¹' Γ) ∂κ

theorem mixQ_compl {W : Type*} [MeasurableSpace W] (Q P : Measure Ω) [IsFiniteMeasure Q]
    [IsProbabilityMeasure P] (Y : Ω → W) (hY : Measurable Y) (Z : E → Ω → W)
    (hZ : ∀ y, Measurable (Z y)) (κ : Measure E) [IsFiniteMeasure κ] (hmass : Q Set.univ = κ Set.univ)
    (t : Set W) (htm : MeasurableSet t) (hmix : MixQ Q P Y Z κ t) : MixQ Q P Y Z κ tᶜ := by
  obtain ⟨hm, heq⟩ := hmix
  have hc : ∀ y, P (Z y ⁻¹' tᶜ) = 1 - P (Z y ⁻¹' t) := fun y => by
    rw [Set.preimage_compl, prob_compl_eq_one_sub (htm.preimage (hZ y))]
  refine ⟨?_, ?_⟩
  · simp_rw [hc]; exact hm.const_sub 1
  · rw [Set.preimage_compl, measure_compl (htm.preimage hY) (measure_ne_top _ _), heq, hmass]
    simp_rw [hc]
    have hle : (fun y => P (Z y ⁻¹' t)) ≤ᵐ[κ] fun _ => (1 : ℝ≥0∞) :=
      Eventually.of_forall fun y => prob_le_one
    have hfin : ∫⁻ y, P (Z y ⁻¹' t) ∂κ ≠ ∞ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ℝ≥0∞) ∂κ) ?_ (lintegral_mono fun y => prob_le_one)
      simp
    rw [lintegral_sub hm hfin hle]
    simp

theorem mixQ_iUnion {W : Type*} [MeasurableSpace W] (Q P : Measure Ω) (Y : Ω → W)
    (hY : Measurable Y) (Z : E → Ω → W) (hZ : ∀ y, Measurable (Z y)) (κ : Measure E)
    (f : ℕ → Set W) (hd : Pairwise (Function.onFun Disjoint f)) (hfm : ∀ i, MeasurableSet (f i))
    (hmix : ∀ i, MixQ Q P Y Z κ (f i)) : MixQ Q P Y Z κ (⋃ i, f i) := by
  have hZd : ∀ y, P (Z y ⁻¹' ⋃ i, f i) = ∑' i, P (Z y ⁻¹' f i) := fun y => by
    rw [Set.preimage_iUnion]
    exact measure_iUnion (fun i j hij => (hd hij).preimage _) (fun i => (hfm i).preimage (hZ y))
  refine ⟨?_, ?_⟩
  · simp_rw [hZd]; exact Measurable.tsum fun i => (hmix i).1
  · rw [Set.preimage_iUnion, measure_iUnion (fun i j hij => (hd hij).preimage _)
      (fun i => (hfm i).preimage hY)]
    simp_rw [hZd]
    rw [lintegral_tsum fun i => (hmix i).1.aemeasurable]
    exact tsum_congr fun i => (hmix i).2

theorem mixQ_of_pi {W : Type*} [mW : MeasurableSpace W] (Q P : Measure Ω) [IsFiniteMeasure Q]
    [IsProbabilityMeasure P] (Y : Ω → W) (hY : Measurable Y) (Z : E → Ω → W)
    (hZ : ∀ y, Measurable (Z y)) (κ : Measure E) [IsFiniteMeasure κ]
    (hmass : Q Set.univ = κ Set.univ) {𝒮 : Set (Set W)} (hgen : mW = generateFrom 𝒮)
    (hpi : IsPiSystem 𝒮) (hS : ∀ t ∈ 𝒮, MixQ Q P Y Z κ t) :
    ∀ Γ : Set W, MeasurableSet Γ → MixQ Q P Y Z κ Γ := by
  intro Γ hΓ
  refine MeasurableSpace.induction_on_inter (C := fun Γ _ => MixQ Q P Y Z κ Γ)
    hgen hpi ?_ ?_ ?_ ?_ Γ hΓ
  · refine ⟨by simp, by simp⟩
  · intro t ht
    exact hS t ht
  · intro t htm hmix
    exact mixQ_compl Q P Y hY Z hZ κ hmass t htm hmix
  · intro f hd hfm hmix
    exact mixQ_iUnion Q P Y hY Z hZ κ f hd hfm hmix

theorem mixQ_closed {W : Type*} [PseudoEMetricSpace W] [MeasurableSpace W] [OpensMeasurableSpace W]
    (Q P : Measure Ω) [IsFiniteMeasure Q] [IsProbabilityMeasure P]
    (Y : Ω → W) (hY : Measurable Y) (Z : E → Ω → W) (hZ : ∀ y, Measurable (Z y)) (κ : Measure E)
    [IsFiniteMeasure κ]
    (hF : ∀ F : W →ᵇ ℝ≥0, (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      Measurable (fun y => ∫⁻ ω, (F (Z y ω) : ℝ≥0∞) ∂P) ∧
      ∫⁻ ω, (F (Y ω) : ℝ≥0∞) ∂Q = ∫⁻ y, ∫⁻ ω, (F (Z y ω) : ℝ≥0∞) ∂P ∂κ)
    (C : Set W) (hC : IsClosed C) : MixQ Q P Y Z κ C := by
  have δpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => Nat.one_div_pos_of_nat
  have δlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let F : ℕ → W →ᵇ ℝ≥0 := fun k => thickenedIndicator (δpos k) C
  have hF' := fun k => hF (F k) ⟨_, lipschitzWith_thickenedIndicator (δpos k) C⟩
    (fun w => thickenedIndicator_le_one (δpos k) C w)
  have hFm : ∀ k, Measurable fun w => ((F k w : ℝ≥0) : ℝ≥0∞) :=
    fun k => measurable_coe_nnreal_ennreal.comp (F k).continuous.measurable
  have hlim : ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (V : Ω → W), Measurable V →
      Tendsto (fun k => ∫⁻ ω, (F k (V ω) : ℝ≥0∞) ∂μ) atTop (𝓝 (μ (V ⁻¹' C))) := by
    intro μ _ V hV
    have e : ∀ k, ∫⁻ ω, (F k (V ω) : ℝ≥0∞) ∂μ = ∫⁻ w, (F k w : ℝ≥0∞) ∂(μ.map V) :=
      fun k => (lintegral_map (hFm k) hV).symm
    simp_rw [e]
    rw [← Measure.map_apply hV hC.measurableSet]
    haveI : IsFiniteMeasure (μ.map V) := Measure.isFiniteMeasure_map μ V
    exact tendsto_lintegral_thickenedIndicator_of_isClosed (μ.map V) hC δpos δlim
  have hmeas : Measurable fun y => P (Z y ⁻¹' C) :=
    measurable_of_tendsto_metrizable (fun k => (hF' k).1)
      (tendsto_pi_nhds.2 fun y => hlim P _ (hZ y))
  refine ⟨hmeas, ?_⟩
  have h1 := hlim Q Y hY
  have h2 : Tendsto (fun k => ∫⁻ y, ∫⁻ ω, (F k (Z y ω) : ℝ≥0∞) ∂P ∂κ) atTop
      (𝓝 (∫⁻ y, P (Z y ⁻¹' C) ∂κ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1) (fun k => (hF' k).1)
      (fun k => Eventually.of_forall fun y => ?_) (by simp)
      (Eventually.of_forall fun y => hlim P _ (hZ y))
    calc ∫⁻ ω, (F k (Z y ω) : ℝ≥0∞) ∂P ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂P :=
          lintegral_mono fun ω => by
            exact ENNReal.coe_le_one_iff.mpr (thickenedIndicator_le_one (δpos k) C (Z y ω))
      _ = 1 := by simp
  have h3 : Tendsto (fun k => ∫⁻ ω, (F k (Y ω) : ℝ≥0∞) ∂Q) atTop
      (𝓝 (∫⁻ y, P (Z y ⁻¹' C) ∂κ)) := by
    simp_rw [(hF' _).2]; exact h2
  exact tendsto_nhds_unique h1 h3

theorem mixQ_cylinders (Q P : Measure Ω) [IsFiniteMeasure Q] [IsProbabilityMeasure P]
    (Y : Ω → (ι → E)) (hY : Measurable Y) (Z : E → Ω → (ι → E)) (hZ : ∀ y, Measurable (Z y))
    (κ : Measure E) [IsFiniteMeasure κ] (hmass : Q Set.univ = κ Set.univ)
    (hcyl : ∀ (s : Finset ι) (S : Set (∀ i : s, E)), MeasurableSet S →
      MixQ Q P Y Z κ (cylinder s S)) :
    ∀ Γ : Set (ι → E), MeasurableSet Γ → MixQ Q P Y Z κ Γ := by
  refine mixQ_of_pi Q P Y hY Z hZ κ hmass generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders fun t ht => ?_
  obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders t).1 ht
  exact hcyl s S hS

/-- two-measure PM2: finite-dimensional Lipschitz test functions to the path σ-algebra. -/
theorem mixQ_all [PseudoMetricSpace E] [SecondCountableTopology E]
    [BorelSpace E] (Q P : Measure Ω) [IsFiniteMeasure Q] [IsProbabilityMeasure P]
    (Y : Ω → (ι → E)) (hY : Measurable Y) (Z : E → Ω → (ι → E)) (hZ : ∀ y, Measurable (Z y))
    (κ : Measure E) [IsFiniteMeasure κ] (hmass : Q Set.univ = κ Set.univ)
    (hFD : ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      Measurable (fun y => ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P) ∧
      ∫⁻ ω, (F (s.restrict (Y ω)) : ℝ≥0∞) ∂Q =
        ∫⁻ y, ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P ∂κ) :
    ∀ Γ : Set (ι → E), MeasurableSet Γ → MixQ Q P Y Z κ Γ := by
  refine mixQ_cylinders Q P Y hY Z hZ κ hmass fun s S hS => ?_
  have hYs : Measurable fun ω => s.restrict (Y ω) :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp hY
  have hZs : ∀ y, Measurable fun ω => s.restrict (Z y ω) :=
    fun y => measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp (hZ y)
  have hgen : (inferInstance : MeasurableSpace (∀ i : s, E)) = generateFrom {C | IsClosed C} :=
    BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed
  exact mixQ_of_pi Q P _ hYs _ hZs κ hmass hgen isPiSystem_isClosed
    (fun C hC => mixQ_closed Q P _ hYs _ hZs κ (hFD s) C hC) S hS

end StochKolmogorov.Classify.PathMix2

end FlatM_PathMix2
-- ===== CondMix =====
section FlatM_CondMix

/-! K2-mc steps 2-3 (8f909832), generic: from the conditional finite-dimensional Markov identity
(Lipschitz tests `G` of the past path `V`, `F` of the future path `Y`) to the conditional path
identity `P(Y ∈ Γ, V ∈ A) = ∫_{V ∈ A} P(Z (Xt ω) ∈ Γ) dP(ω)` for all measurable `A`, `Γ`. -/

set_option autoImplicit false

open MeasureTheory Filter MeasurableSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StochKolmogorov.Classify.CondMix

/-- Two finite Borel measures on a pseudo-emetric space agree if they agree on Lipschitz
bounded continuous functions with values in `[0, 1]`. -/
theorem ext_lip {W : Type*} [PseudoEMetricSpace W] [MeasurableSpace W] [BorelSpace W]
    (μ ν : Measure W) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ F : W →ᵇ ℝ≥0, (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      ∫⁻ w, (F w : ℝ≥0∞) ∂μ = ∫⁻ w, (F w : ℝ≥0∞) ∂ν) : μ = ν := by
  have δpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => Nat.one_div_pos_of_nat
  have δlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcl : ∀ C : Set W, IsClosed C → μ C = ν C := by
    intro C hC
    have h1 := tendsto_lintegral_thickenedIndicator_of_isClosed μ hC δpos δlim
    have h2 := tendsto_lintegral_thickenedIndicator_of_isClosed ν hC δpos δlim
    have e : ∀ k : ℕ, ∫⁻ w, (thickenedIndicator (δpos k) C w : ℝ≥0∞) ∂μ =
        ∫⁻ w, (thickenedIndicator (δpos k) C w : ℝ≥0∞) ∂ν := fun k =>
      h _ ⟨_, lipschitzWith_thickenedIndicator (δpos k) C⟩
        (fun w => thickenedIndicator_le_one (δpos k) C w)
    simp_rw [e] at h1
    exact tendsto_nhds_unique h1 h2
  refine ext_of_generate_finite _ ?_ isPiSystem_isClosed (fun C hC => hcl C hC)
    (hcl _ isClosed_univ)
  rw [BorelSpace.measurable_eq (α := W), borel_eq_generateFrom_isClosed]

/-- Two finite measures on a path space `ι → E` agree if they agree on Lipschitz `[0,1]`-valued
tests of finitely many coordinates. -/
theorem pi_ext_lip {ι E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ ν : Measure (ι → E)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      ∫⁻ w, (F (s.restrict w) : ℝ≥0∞) ∂μ = ∫⁻ w, (F (s.restrict w) : ℝ≥0∞) ∂ν) : μ = ν := by
  have hmap : ∀ s : Finset ι, μ.map s.restrict = ν.map s.restrict := by
    intro s
    refine ext_lip _ _ fun F hF hF1 => ?_
    have hFm : Measurable fun w : (∀ i : s, E) => ((F w : ℝ≥0) : ℝ≥0∞) :=
      measurable_coe_nnreal_ennreal.comp F.continuous.measurable
    rw [lintegral_map hFm (Finset.measurable_restrict s),
      lintegral_map hFm (Finset.measurable_restrict s)]
    exact h s F hF hF1
  have hcyl : ∀ t ∈ measurableCylinders (fun _ : ι => E), μ t = ν t := by
    intro t ht
    rw [mem_measurableCylinders] at ht
    obtain ⟨s, S, hS, rfl⟩ := ht
    have e : cylinder (α := fun _ : ι => E) s S = s.restrict ⁻¹' S := rfl
    rw [e, ← Measure.map_apply (Finset.measurable_restrict s) hS,
      ← Measure.map_apply (Finset.measurable_restrict s) hS, hmap s]
  refine ext_of_generate_finite _ generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders hcyl ?_
  have := hcyl _ (cylinder_mem_measurableCylinders (∅ : Finset ι) Set.univ MeasurableSet.univ)
  simpa using this

variable {Ω E ι ι' : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- The conditional path identity. -/
theorem condMix [PseudoMetricSpace E] [SecondCountableTopology E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Ω → (ι' → E)) (hV : Measurable V) (Y : Ω → (ι → E)) (hY : Measurable Y)
    (Xt : Ω → E) (hXt : Measurable Xt) (Z : E → Ω → (ι → E)) (hZ : ∀ y, Measurable (Z y))
    (hFD : ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      Measurable (fun y => ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P))
    (hC : ∀ (s' : Finset ι') (G : (∀ i : s', E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K G) → (∀ w, G w ≤ 1) →
      ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      ∫⁻ ω, (G (s'.restrict (V ω)) : ℝ≥0∞) * (F (s.restrict (Y ω)) : ℝ≥0∞) ∂P =
        ∫⁻ ω, (G (s'.restrict (V ω)) : ℝ≥0∞) *
          ∫⁻ ω', (F (s.restrict (Z (Xt ω) ω')) : ℝ≥0∞) ∂P ∂P)
    (A : Set (ι' → E)) (hA : MeasurableSet A) (Γ : Set (ι → E)) (hΓ : MeasurableSet Γ) :
    Measurable (fun y => P (Z y ⁻¹' Γ)) ∧
      P (Y ⁻¹' Γ ∩ V ⁻¹' A) = ∫⁻ ω in V ⁻¹' A, P (Z (Xt ω) ⁻¹' Γ) ∂P := by
  set Q : Measure Ω := P.restrict (V ⁻¹' A) with hQ
  set κ : Measure E := Q.map Xt with hκ
  haveI hQfin : IsFiniteMeasure Q := by rw [hQ]; infer_instance
  haveI : IsFiniteMeasure κ := Measure.isFiniteMeasure_map Q Xt
  have hmass : Q Set.univ = κ Set.univ := by
    rw [hκ, Measure.map_apply hXt MeasurableSet.univ, Set.preimage_univ]
  -- the finite-dimensional identity under `Q`
  have hFDQ : ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) →
      (∀ w, F w ≤ 1) →
      Measurable (fun y => ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P) ∧
      ∫⁻ ω, (F (s.restrict (Y ω)) : ℝ≥0∞) ∂Q =
        ∫⁻ y, ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P ∂κ := by
    intro s F hF hF1
    have hHm := hFD s F hF hF1
    refine ⟨hHm, ?_⟩
    set H : E → ℝ≥0∞ := fun y => ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P with hH
    have hFYm : Measurable fun ω => ((F (s.restrict (Y ω)) : ℝ≥0) : ℝ≥0∞) :=
      measurable_coe_nnreal_ennreal.comp
        (F.continuous.measurable.comp ((Finset.measurable_restrict s).comp hY))
    have hHXm : Measurable fun ω => H (Xt ω) := hHm.comp hXt
    have hH1 : ∀ y, H y ≤ 1 := fun y => by
      calc H y ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂P :=
            lintegral_mono fun ω => ENNReal.coe_le_one_iff.mpr (hF1 _)
        _ = 1 := by simp
    -- two measures on the past path space
    set μ1 : Measure (ι' → E) :=
      (P.withDensity fun ω => ((F (s.restrict (Y ω)) : ℝ≥0) : ℝ≥0∞)).map V with hμ1
    set μ2 : Measure (ι' → E) := (P.withDensity fun ω => H (Xt ω)).map V with hμ2
    have hfin1 : IsFiniteMeasure (P.withDensity fun ω => ((F (s.restrict (Y ω)) : ℝ≥0) : ℝ≥0∞)) := by
      refine isFiniteMeasure_withDensity ?_
      refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ℝ≥0∞) ∂P) (by simp) ?_
      exact lintegral_mono fun ω => ENNReal.coe_le_one_iff.mpr (hF1 _)
    have hfin2 : IsFiniteMeasure (P.withDensity fun ω => H (Xt ω)) := by
      refine isFiniteMeasure_withDensity ?_
      refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ℝ≥0∞) ∂P) (by simp) ?_
      exact lintegral_mono fun ω => hH1 _
    haveI : IsFiniteMeasure μ1 := Measure.isFiniteMeasure_map _ V
    haveI : IsFiniteMeasure μ2 := Measure.isFiniteMeasure_map _ V
    have hμ : μ1 = μ2 := by
      refine pi_ext_lip μ1 μ2 fun s' G hG hG1 => ?_
      have hGm : Measurable fun w : (ι' → E) => ((G (s'.restrict w) : ℝ≥0) : ℝ≥0∞) :=
        measurable_coe_nnreal_ennreal.comp
          (G.continuous.measurable.comp (Finset.measurable_restrict s'))
      have hGVm : Measurable fun ω => ((G (s'.restrict (V ω)) : ℝ≥0) : ℝ≥0∞) := hGm.comp hV
      rw [hμ1, hμ2, lintegral_map hGm hV, lintegral_map hGm hV,
        lintegral_withDensity_eq_lintegral_mul _ hFYm hGVm,
        lintegral_withDensity_eq_lintegral_mul _ hHXm hGVm]
      have := hC s' G hG hG1 s F hF hF1
      simp only [Pi.mul_apply]
      rw [lintegral_congr fun ω => mul_comm _ _, this]
      exact lintegral_congr fun ω => mul_comm _ _
    have hA1 : μ1 A = ∫⁻ ω in V ⁻¹' A, ((F (s.restrict (Y ω)) : ℝ≥0) : ℝ≥0∞) ∂P := by
      rw [hμ1, Measure.map_apply hV hA, withDensity_apply _ (hV hA)]
    have hA2 : μ2 A = ∫⁻ ω in V ⁻¹' A, H (Xt ω) ∂P := by
      rw [hμ2, Measure.map_apply hV hA, withDensity_apply _ (hV hA)]
    rw [hκ, lintegral_map hHm hXt, hQ, ← hA1, ← hA2, hμ]
  have hmix := PathMix2.mixQ_all Q P Y hY Z hZ κ hmass hFDQ Γ hΓ
  refine ⟨hmix.1, ?_⟩
  have h2 := hmix.2
  rw [hQ, Measure.restrict_apply (hY hΓ)] at h2
  rw [h2, hκ, lintegral_map hmix.1 hXt]

end StochKolmogorov.Classify.CondMix

end FlatM_CondMix
-- ===== FDMC2 =====
section FlatM_FDMC2

/-! K2-mc (8f909832): the conditional path Markov identity for the Kolmogorov solution family:
`P(shiftPath_t ∈ Γ, past_t ∈ A) = ∫_{past_t ∈ A} P(Zf (X x t ω) ∈ Γ) dP(ω)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.FDMC

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

theorem measurable_Zf [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (y : SDEState n) : Measurable (K4.Zf X y) := by
  unfold K4.Zf
  split_ifs with h
  · exact K3.measurable_rpath X y (hX.2.2 y h).1
  · exact measurable_const

theorem condPath_of [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n)
    (x : SDEState n) (hx : x ∈ openOrthant n) (t : ℝ≥0)
    (A : Set (Past t → SDEState n)) (hA : MeasurableSet A)
    (Γ : Set (ℚ → SDEState n)) (hΓ : MeasurableSet Γ) :
    Measurable (fun y => P (K4.Zf X y ⁻¹' Γ)) ∧
      P (K4.shiftPath X x t ⁻¹' Γ ∩ past X x t ⁻¹' A) =
        ∫⁻ ω in past X x t ⁻¹' A, P (K4.Zf X (X x t ω) ⁻¹' Γ) ∂P := by
  haveI : IsProbabilityMeasure P := hX.1
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hsol := hX.2.2 x hxo
  have hFD := FDM.fdMarkov_of P C B X hX hC hinv
  exact CondMix.condMix P (past X x t) (measurable_past X x t hsol.1)
    (K4.shiftPath X x t) (measurable_pi_lambda _ fun q => hsol.1 _) (X x t) (hsol.1 t)
    (K4.Zf X) (measurable_Zf P C B X hX)
    (fun s F hF hF1 => (hFD x hx t s F hF hF1).1)
    (fdMarkovCond_of P C B X hX hC hinv x hx t) A hA Γ hΓ

end StochKolmogorov.Classify.FDMC

end FlatM_FDMC2
-- ===== T1a =====
section FlatM_T1a

/-! T1a `grid_escape_bound` (a17b7893 s4): Hening-Nguyen 1704.06984 (5.29)-(5.30).
`Ũ(X(j T₀))` is a supermartingale along the grid (one step = Extinct.one_step_5_11_5_12 over
proposition_5_1, lemma_5_2, inequalities_5_1_5_2), so the kernel Doob inequality
`P(∃ j, Ũ(X(j T₀)) ≥ a) ≤ Ũ(x)/a` (induction on the horizon over the path Markov identity
`FDMC.condPath_of`) bounds the escape probability; `Ũ < a ≤ ς` forces `xᵢ < β` off `supp μ`. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace StochKolmogorov.Classify.GE
open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ}

/-- The same coefficients, read as `Extinct` coefficients. -/
def ec (C : Coeffs n) : StochKolmogorov.Extinct.Coeffs n := ⟨C.f, C.g, C.Γ⟩

theorem exists_isDelta0 (C : Coeffs n) (γb : ℝ) (hγ : 0 < γb) :
    ∃ δ₀ : ℝ, IsDelta0 C γb δ₀ := by
  set S : ℝ := ∑ i, ∑ j, |C.sig i j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsij : ∀ i j, |C.sig i j| ≤ S := by
    intro i j
    calc |C.sig i j| ≤ ∑ j', |C.sig i j'| :=
          Finset.single_le_sum (f := fun j' => |C.sig i j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ j', |C.sig i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hden : 0 < 3 * S * n + 3 := by positivity
  refine ⟨γb / (3 * S * n + 3), div_pos hγ hden, ?_, fun x _ => ?_⟩
  · rw [div_lt_div_iff₀ hden two_pos]
    nlinarith [mul_nonneg hS0 (Nat.cast_nonneg (α := ℝ) n)]
  · set δ := γb / (3 * S * n + 3) with hδ
    have hδ0 : 0 ≤ δ := (div_pos hγ hden).le
    set G : ℝ := ∑ i, C.g i x ^ 2 with hG
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hterm : ∀ i j, |C.g i x * C.g j x * C.sig i j|
        ≤ S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by
      intro i j
      rw [abs_mul, abs_mul]
      have h1 : |C.g i x| * |C.g j x| ≤ (C.g i x ^ 2 + C.g j x ^ 2) / 2 := by
        nlinarith [sq_nonneg (|C.g i x| - |C.g j x|), sq_abs (C.g i x), sq_abs (C.g j x)]
      calc |C.g i x| * |C.g j x| * |C.sig i j| ≤ ((C.g i x ^ 2 + C.g j x ^ 2) / 2) * S :=
            mul_le_mul h1 (hsij i j) (abs_nonneg _) (by positivity)
        _ = S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by ring
    have hsum : ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| ≤ S * n * G := by
      calc ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|
          ≤ ∑ i : Fin n, ∑ j : Fin n, S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
        _ = S * n * G := by
            simp only [← Finset.mul_sum, add_div, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hG, ← Finset.sum_div]
            ring
    have hkey : δ * (3 * S * n + 3) = γb := by rw [hδ, div_mul_cancel₀ _ hden.ne']
    calc 3 * δ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| + δ * G
        ≤ 3 * δ * (S * n * G) + δ * G := by nlinarith
      _ ≤ δ * (3 * S * n + 3) * G := by nlinarith [mul_nonneg hδ0 hG0]
      _ = γb * G := by rw [hkey]

/-- Extinct's `δ₀` must also be `< 1`; shrinking `δ₀` keeps (3.2). -/
theorem delta_small (C : Coeffs n) {γb δ₀ : ℝ} (h : IsDelta0 C γb δ₀) :
    StochKolmogorov.Extinct.IsDelta0 (ec C) γb (min δ₀ (1 / 2)) := by
  refine ⟨lt_min h.1 (by norm_num), lt_min (lt_of_le_of_lt (min_le_left _ _) h.2.1)
    (lt_of_le_of_lt (min_le_right _ _) (by norm_num)), fun x hx => ?_⟩
  show 3 * min δ₀ (1 / 2) * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|
      + min δ₀ (1 / 2) * ∑ i, C.g i x ^ 2 ≤ γb * ∑ i, C.g i x ^ 2
  have hS1 : 0 ≤ ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hS2 : 0 ≤ ∑ i, C.g i x ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hm : min δ₀ (1 / 2) ≤ δ₀ := min_le_left _ _
  have h3 := h.2.2 x hx
  have e1 := mul_le_mul_of_nonneg_right hm hS1
  have e2 := mul_le_mul_of_nonneg_right hm hS2
  linarith

/-! ### Deterministic facts about `Ũ` -/

theorem prod_le (c z : SDEState n) (hc : ∀ i, 0 < c i) (hz : ∀ i, 0 < z i) (S : Finset (Fin n))
    (p : Fin n → ℝ) (hp : ∀ i ∈ S, 0 ≤ p i) (hs : ∑ i ∈ S, p i ≤ 1) :
    ∏ i ∈ S, z i ^ p i ≤ (1 + ∑ j, c j * z j) * ∏ i ∈ S, (c i)⁻¹ ^ p i := by
  have hsum0 : 0 ≤ ∑ j, c j * z j :=
    Finset.sum_nonneg fun j _ => (mul_pos (hc j) (hz j)).le
  have hL1 : 1 ≤ 1 + ∑ j, c j * z j := by linarith
  have hL0 : 0 < 1 + ∑ j, c j * z j := by linarith
  have hzi : ∀ i, z i ≤ (1 + ∑ j, c j * z j) * (c i)⁻¹ := by
    intro i
    have h1 : c i * z i ≤ ∑ j, c j * z j :=
      Finset.single_le_sum (f := fun j => c j * z j) (fun j _ => (mul_pos (hc j) (hz j)).le)
        (Finset.mem_univ i)
    rw [← div_eq_mul_inv, le_div_iff₀ (hc i)]
    linarith [mul_comm (z i) (c i)]
  calc ∏ i ∈ S, z i ^ p i ≤ ∏ i ∈ S, ((1 + ∑ j, c j * z j) * (c i)⁻¹) ^ p i :=
        Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hz i).le _)
          (fun i hi => Real.rpow_le_rpow (hz i).le (hzi i) (hp i hi))
    _ = (∏ i ∈ S, (1 + ∑ j, c j * z j) ^ p i) * ∏ i ∈ S, (c i)⁻¹ ^ p i := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => Real.mul_rpow hL0.le (inv_nonneg.2 (hc i).le)
    _ ≤ (1 + ∑ j, c j * z j) * ∏ i ∈ S, (c i)⁻¹ ^ p i := by
        apply mul_le_mul_of_nonneg_right _
          (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (inv_nonneg.2 (hc i).le) _)
        rw [← Real.rpow_sum_of_pos hL0]
        calc (1 + ∑ j, c j * z j) ^ (∑ i ∈ S, p i) ≤ (1 + ∑ j, c j * z j) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hL1 hs
          _ = 1 + ∑ j, c j * z j := Real.rpow_one _

theorem Ui_nonneg (c : SDEState n) (hc : ∀ i, 0 < c i) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (pcheck : ℝ) (i : Fin n) (z : SDEState n) (hz : ∀ j, 0 < z j) :
    0 ≤ StochKolmogorov.Extinct.Ui c mu phat pcheck i z := by
  unfold StochKolmogorov.Extinct.Ui
  have : 0 ≤ ∑ j, c j * z j := Finset.sum_nonneg fun j _ => (mul_pos (hc j) (hz j)).le
  exact div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (hz i).le _))
    (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hz j).le _)

theorem Utheta_nonneg (c : SDEState n) (hc : ∀ i, 0 < c i) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (pcheck θ : ℝ) (z : SDEState n) (hz : ∀ j, 0 < z j) :
    0 ≤ StochKolmogorov.Extinct.Utheta c mu phat pcheck θ z :=
  Finset.sum_nonneg fun i _ => Real.rpow_nonneg (Ui_nonneg c hc mu phat pcheck i z hz) _

theorem CU_bdd (c : SDEState n) (hc : ∀ i, 0 < c i) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (hp : ∀ i ∈ StochKolmogorov.Extinct.supp mu, 0 ≤ phat i)
    (hs : ∑ i ∈ StochKolmogorov.Extinct.supp mu, phat i ≤ 1) :
    BddAbove ((fun x : SDEState n => (∏ i ∈ StochKolmogorov.Extinct.supp mu, x i ^ phat i) /
      (1 + ∑ i, c i * x i)) '' StochKolmogorov.Extinct.openOrthant n) := by
  refine ⟨∏ i ∈ StochKolmogorov.Extinct.supp mu, (c i)⁻¹ ^ phat i, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz' : ∀ i, 0 < z i := hz
  have hsum0 : 0 ≤ ∑ j, c j * z j := Finset.sum_nonneg fun j _ => (mul_pos (hc j) (hz' j)).le
  have hL0 : 0 < 1 + ∑ j, c j * z j := by linarith
  show (∏ i ∈ StochKolmogorov.Extinct.supp mu, z i ^ phat i) / (1 + ∑ i, c i * z i) ≤ _
  rw [div_le_iff₀ hL0]
  calc _ ≤ (1 + ∑ j, c j * z j) * ∏ i ∈ StochKolmogorov.Extinct.supp mu, (c i)⁻¹ ^ phat i :=
        prod_le c z hc hz' _ phat hp hs
    _ = _ := mul_comm _ _

theorem CU_pos (c : SDEState n) (hc : ∀ i, 0 < c i) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (hp : ∀ i ∈ StochKolmogorov.Extinct.supp mu, 0 ≤ phat i)
    (hs : ∑ i ∈ StochKolmogorov.Extinct.supp mu, phat i ≤ 1) :
    0 < StochKolmogorov.Extinct.CU c mu phat := by
  unfold StochKolmogorov.Extinct.CU
  have hsum0 : 0 ≤ ∑ j, c j * c j := Finset.sum_nonneg fun j _ => (mul_pos (hc j) (hc j)).le
  have hv : 0 < (∏ i ∈ StochKolmogorov.Extinct.supp mu, c i ^ phat i) / (1 + ∑ i, c i * c i) :=
    div_pos (Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hc j) _) (by linarith)
  exact lt_of_lt_of_le hv (le_csSup (CU_bdd c hc mu phat hp hs) ⟨c, hc, rfl⟩)

theorem varsigma_pos (c : SDEState n) (hc : ∀ i, 0 < c i) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (hp : ∀ i ∈ StochKolmogorov.Extinct.supp mu, 0 ≤ phat i)
    (hs : ∑ i ∈ StochKolmogorov.Extinct.supp mu, phat i ≤ 1) (pcheck θ δe : ℝ) (hδe : 0 < δe) :
    0 < StochKolmogorov.Extinct.varsigma c mu phat pcheck θ δe := by
  unfold StochKolmogorov.Extinct.varsigma
  exact div_pos (Real.rpow_pos_of_pos hδe _) (Real.rpow_pos_of_pos (CU_pos c hc mu phat hp hs) _)

theorem measurable_Utilde (c : SDEState n) (mu : Measure (SDEState n)) (phat : Fin n → ℝ)
    (pcheck θ δe : ℝ) : Measurable (StochKolmogorov.Extinct.Utilde c mu phat pcheck θ δe) := by
  have hco : ∀ i, Measurable fun z : SDEState n => z i :=
    fun i => (PiLp.continuous_apply 2 _ i).measurable
  unfold StochKolmogorov.Extinct.Utilde StochKolmogorov.Extinct.Utheta StochKolmogorov.Extinct.Ui
  refine measurable_const.min (Finset.measurable_sum _ fun i _ => ?_)
  refine Measurable.pow_const ?_ _
  exact ((measurable_const.add (Finset.measurable_sum _ fun j _ =>
    measurable_const.mul (hco j))).mul ((hco i).pow_const _)).div
    (Finset.measurable_prod _ fun j _ => (hco j).pow_const _)

/-- `U_θ(z) < a` forces `zᵢ^p̌ < a^{1/θ} K` off `supp μ`. -/
theorem coord_lt (c : SDEState n) (hc : ∀ i, 0 < c i) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (hp : ∀ i ∈ StochKolmogorov.Extinct.supp mu, 0 ≤ phat i)
    (hs : ∑ i ∈ StochKolmogorov.Extinct.supp mu, phat i ≤ 1)
    (pcheck θ : ℝ) (hθ : 0 < θ) (z : SDEState n) (hz : ∀ j, 0 < z j) (i : Fin n)
    (hi : i ∉ StochKolmogorov.Extinct.supp mu) (a : ℝ)
    (hU : StochKolmogorov.Extinct.Utheta c mu phat pcheck θ z < a) :
    z i ^ pcheck < a ^ θ⁻¹ * ∏ j ∈ StochKolmogorov.Extinct.supp mu, (c j)⁻¹ ^ phat j := by
  have hU0 : 0 ≤ StochKolmogorov.Extinct.Ui c mu phat pcheck i z :=
    Ui_nonneg c hc mu phat pcheck i z hz
  have hle : StochKolmogorov.Extinct.Ui c mu phat pcheck i z ^ θ ≤
      StochKolmogorov.Extinct.Utheta c mu phat pcheck θ z := by
    unfold StochKolmogorov.Extinct.Utheta
    exact Finset.single_le_sum
      (f := fun j => (StochKolmogorov.Extinct.Ui c mu phat pcheck j z) ^ θ)
      (fun j _ => Real.rpow_nonneg (Ui_nonneg c hc mu phat pcheck j z hz) _) (by simp [hi])
  have hlt : StochKolmogorov.Extinct.Ui c mu phat pcheck i z < a ^ θ⁻¹ := by
    have h1 := Real.rpow_lt_rpow (Real.rpow_nonneg hU0 θ) (lt_of_le_of_lt hle hU) (inv_pos.2 hθ)
    rwa [Real.rpow_rpow_inv hU0 hθ.ne'] at h1
  have hsum0 : 0 ≤ ∑ j, c j * z j := Finset.sum_nonneg fun j _ => (mul_pos (hc j) (hz j)).le
  have hL0 : 0 < 1 + ∑ j, c j * z j := by linarith
  have hPr0 : 0 < ∏ j ∈ StochKolmogorov.Extinct.supp mu, z j ^ phat j :=
    Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hz j) _
  have hK0 : 0 < ∏ j ∈ StochKolmogorov.Extinct.supp mu, (c j)⁻¹ ^ phat j :=
    Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (inv_pos.2 (hc j)) _
  have hK := prod_le c z hc hz _ phat hp hs
  have heq : StochKolmogorov.Extinct.Ui c mu phat pcheck i z *
      (∏ j ∈ StochKolmogorov.Extinct.supp mu, z j ^ phat j) / (1 + ∑ j, c j * z j) =
      z i ^ pcheck := by
    unfold StochKolmogorov.Extinct.Ui
    rw [div_mul_cancel₀ _ hPr0.ne', mul_div_cancel_left₀ _ hL0.ne']
  rw [← heq, div_lt_iff₀ hL0]
  calc StochKolmogorov.Extinct.Ui c mu phat pcheck i z *
        (∏ j ∈ StochKolmogorov.Extinct.supp mu, z j ^ phat j)
      ≤ StochKolmogorov.Extinct.Ui c mu phat pcheck i z * ((1 + ∑ j, c j * z j) *
          ∏ j ∈ StochKolmogorov.Extinct.supp mu, (c j)⁻¹ ^ phat j) :=
        mul_le_mul_of_nonneg_left hK hU0
    _ = StochKolmogorov.Extinct.Ui c mu phat pcheck i z *
          ((∏ j ∈ StochKolmogorov.Extinct.supp mu, (c j)⁻¹ ^ phat j) *
            (1 + ∑ j, c j * z j)) := by ring
    _ < a ^ θ⁻¹ * ((∏ j ∈ StochKolmogorov.Extinct.supp mu, (c j)⁻¹ ^ phat j) *
            (1 + ∑ j, c j * z j)) := mul_lt_mul_of_pos_right hlt (mul_pos hK0 hL0)
    _ = _ := by ring

/-- On the box `K^{k,Δ}_μ`, `U_θ` is at most `n (L Δ^p̌ / m)^θ`. -/
theorem Utheta_Kbox (c : SDEState n) (hc : ∀ i, 0 < c i) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (hp : ∀ i ∈ StochKolmogorov.Extinct.supp mu, 0 ≤ phat i)
    (pcheck θ : ℝ) (hpc : 0 ≤ pcheck) (hθ : 0 < θ) (k : ℕ) (hk : 1 ≤ k) (Δ : ℝ) (hΔ0 : 0 ≤ Δ)
    (hΔ1 : Δ ≤ 1) (x : SDEState n) (hx : x ∈ Kbox mu k Δ) :
    StochKolmogorov.Extinct.Utheta c mu phat pcheck θ x ≤
      n * ((1 + ∑ j, c j * k) * Δ ^ pcheck /
        ∏ j ∈ StochKolmogorov.Extinct.supp mu, ((k : ℝ)⁻¹) ^ phat j) ^ θ := by
  obtain ⟨hxo, hxs, hxn⟩ := hx
  have hxo' : ∀ j, 0 < x j := hxo
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hxk : ∀ j, x j ≤ k := by
    intro j
    by_cases hj : j ∈ supp mu
    · exact (hxs j hj).2
    · exact ((hxn j hj).le.trans hΔ1).trans hk1
  have hm0 : 0 < ∏ j ∈ StochKolmogorov.Extinct.supp mu, ((k : ℝ)⁻¹) ^ phat j :=
    Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (inv_pos.2 hk0) _
  have hmle : ∏ j ∈ StochKolmogorov.Extinct.supp mu, ((k : ℝ)⁻¹) ^ phat j ≤
      ∏ j ∈ StochKolmogorov.Extinct.supp mu, x j ^ phat j :=
    Finset.prod_le_prod (fun j _ => Real.rpow_nonneg (inv_nonneg.2 hk0.le) _)
      (fun j hj => Real.rpow_le_rpow (inv_nonneg.2 hk0.le) (hxs j hj).1 (hp j hj))
  have hLle : 1 + ∑ j, c j * x j ≤ 1 + ∑ j, c j * k := by
    have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hxk j) (hc j).le
    linarith
  have hsum0 : 0 ≤ ∑ j, c j * x j := Finset.sum_nonneg fun j _ => (mul_pos (hc j) (hxo' j)).le
  have hB0 : 0 ≤ (1 + ∑ j, c j * k) * Δ ^ pcheck /
      ∏ j ∈ StochKolmogorov.Extinct.supp mu, ((k : ℝ)⁻¹) ^ phat j :=
    div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hΔ0 _)) hm0.le
  have hterm : ∀ i, i ∉ StochKolmogorov.Extinct.supp mu →
      StochKolmogorov.Extinct.Ui c mu phat pcheck i x ^ θ ≤
        ((1 + ∑ j, c j * k) * Δ ^ pcheck /
          ∏ j ∈ StochKolmogorov.Extinct.supp mu, ((k : ℝ)⁻¹) ^ phat j) ^ θ := by
    intro i hi
    refine Real.rpow_le_rpow (Ui_nonneg c hc mu phat pcheck i x hxo') ?_ hθ.le
    unfold StochKolmogorov.Extinct.Ui
    have hnum : (1 + ∑ j, c j * x j) * x i ^ pcheck ≤ (1 + ∑ j, c j * k) * Δ ^ pcheck :=
      mul_le_mul hLle (Real.rpow_le_rpow (hxo' i).le (hxn i hi).le hpc)
        (Real.rpow_nonneg (hxo' i).le _) (by linarith)
    calc (1 + ∑ j, c j * x j) * x i ^ pcheck / ∏ j ∈ StochKolmogorov.Extinct.supp mu, x j ^ phat j
        ≤ (1 + ∑ j, c j * x j) * x i ^ pcheck /
            ∏ j ∈ StochKolmogorov.Extinct.supp mu, ((k : ℝ)⁻¹) ^ phat j :=
          div_le_div_of_nonneg_left (mul_nonneg (by linarith) (Real.rpow_nonneg (hxo' i).le _))
            hm0 hmle
      _ ≤ _ := div_le_div_of_nonneg_right hnum hm0.le
  unfold StochKolmogorov.Extinct.Utheta
  calc ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ∉ StochKolmogorov.Extinct.supp mu),
        StochKolmogorov.Extinct.Ui c mu phat pcheck i x ^ θ
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ∉ StochKolmogorov.Extinct.supp mu),
        ((1 + ∑ j, c j * k) * Δ ^ pcheck /
          ∏ j ∈ StochKolmogorov.Extinct.supp mu, ((k : ℝ)⁻¹) ^ phat j) ^ θ :=
        Finset.sum_le_sum fun i hi => hterm i (Finset.mem_filter.1 hi).2
    _ = ((Finset.univ.filter (fun i : Fin n => i ∉ StochKolmogorov.Extinct.supp mu)).card : ℝ) *
        ((1 + ∑ j, c j * k) * Δ ^ pcheck /
          ∏ j ∈ StochKolmogorov.Extinct.supp mu, ((k : ℝ)⁻¹) ^ phat j) ^ θ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hB0 _)
        have := Finset.card_filter_le (Finset.univ : Finset (Fin n))
          (fun i : Fin n => i ∉ StochKolmogorov.Extinct.supp mu)
        rw [Finset.card_univ, Fintype.card_fin] at this
        exact_mod_cast this

/-! ### Kernel Doob inequality along the grid -/

theorem doob_grid {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n)
    (hopen : ∀ x ∈ openOrthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ openOrthant n)
    (W : SDEState n → ℝ) (hWm : Measurable W) (hW0 : ∀ z ∈ openOrthant n, 0 ≤ W z)
    (q0 : ℚ) (hq0 : 0 ≤ q0)
    (hstep : ∀ z ∈ openOrthant n, Integrable (fun ω => W (X z ((q0 : ℝ).toNNReal) ω)) P ∧
      ∫ ω, W (X z ((q0 : ℝ).toNNReal) ω) ∂P ≤ W z)
    (a : ℝ) (ha : 0 < a) :
    ∀ N : ℕ, ∀ y ∈ openOrthant n,
      P {ω | ∃ j ≤ N, a ≤ W (X y ((j : ℝ≥0) * (q0 : ℝ).toNNReal) ω)} ≤
        ENNReal.ofReal (W y / a) := by
  haveI : IsProbabilityMeasure P := hX.1
  have hq0r : (0 : ℝ) ≤ (q0 : ℝ) := Rat.cast_nonneg.2 hq0
  have tq : ∀ j : ℕ, ((((j : ℚ) * q0 : ℚ) : ℝ)).toNNReal = (j : ℝ≥0) * (q0 : ℝ).toNNReal := by
    intro j
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hq0r, NNReal.coe_natCast,
      Real.coe_toNNReal _ (by push_cast; exact mul_nonneg (Nat.cast_nonneg _) hq0r)]
    push_cast; ring
  let Γ : ℕ → Set (ℚ → SDEState n) := fun N => {p | ∃ j ≤ N, a ≤ W (p ((j : ℚ) * q0))}
  have hΓ : ∀ N, MeasurableSet (Γ N) := by
    intro N
    have e : Γ N = ⋃ j ∈ Finset.range (N + 1),
        (fun p : ℚ → SDEState n => p ((j : ℚ) * q0)) ⁻¹' {z | a ≤ W z} := by
      ext p; simp [Γ, Nat.lt_succ_iff]
    rw [e]
    exact Finset.measurableSet_biUnion _ fun j _ =>
      (measurable_pi_apply _) (measurableSet_le measurable_const hWm)
  have hZ : ∀ N, ∀ z ∈ orthant n, K4.Zf X z ⁻¹' Γ N =
      {ω | ∃ j ≤ N, a ≤ W (X z ((j : ℝ≥0) * (q0 : ℝ).toNNReal) ω)} := by
    intro N z hz
    ext ω
    simp only [K4.Zf, if_pos hz, K3.rpath, Set.mem_preimage, Set.mem_setOf_eq, Γ, tq]
  have hS : ∀ N y, W y < a →
      {ω | ∃ j : ℕ, j ≤ N + 1 ∧ a ≤ W (X y ((j : ℝ≥0) * (q0 : ℝ).toNNReal) ω)} ⊆
        {ω | ¬ X y 0 ω = y} ∪ K4.shiftPath X y ((q0 : ℝ).toNNReal) ⁻¹' Γ N := by
    intro N y hWy ω ⟨j, hj, hw⟩
    rcases j with _ | j
    · left
      intro h0
      simp only [Nat.cast_zero, zero_mul] at hw
      rw [h0] at hw
      linarith
    · right
      refine ⟨j, Nat.succ_le_succ_iff.1 hj, ?_⟩
      simp only [K4.shiftPath, tq]
      convert hw using 3
      push_cast; ring
  have htriv : ∀ y, a ≤ W y → ∀ S : Set Ω, P S ≤ ENNReal.ofReal (W y / a) := by
    intro y hy S
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((one_le_div ha).2 hy)
  have hnull : ∀ y ∈ openOrthant n, P {ω | ¬ X y 0 ω = y} = 0 := by
    intro y hy
    exact ae_iff.1 (hX.2.2 y (fun i => (hy i).le)).2.2.2.1
  intro N
  induction N with
  | zero =>
    intro y hy
    by_cases hWy : a ≤ W y
    · exact htriv y hWy _
    · push Not at hWy
      refine le_of_eq_of_le (measure_mono_null ?_ (hnull y hy)) zero_le
      intro ω ⟨j, hj, hw⟩
      have hj0 : j = 0 := Nat.le_zero.1 hj
      subst hj0
      intro h0
      simp only [Nat.cast_zero, zero_mul] at hw
      rw [h0] at hw
      linarith
  | succ N ih =>
    intro y hy
    by_cases hWy : a ≤ W y
    · exact htriv y hWy _
    · push Not at hWy
      obtain ⟨-, hcp⟩ := FDMC.condPath_of P C B X hX hC hinv y hy ((q0 : ℝ).toNNReal) univ
        MeasurableSet.univ (Γ N) (hΓ N)
      rw [Set.preimage_univ, Set.inter_univ, Measure.restrict_univ] at hcp
      have hint := (hstep y hy).1
      have hle := (hstep y hy).2
      calc P {ω | ∃ j : ℕ, j ≤ N + 1 ∧ a ≤ W (X y ((j : ℝ≥0) * (q0 : ℝ).toNNReal) ω)}
          ≤ P ({ω | ¬ X y 0 ω = y} ∪ K4.shiftPath X y ((q0 : ℝ).toNNReal) ⁻¹' Γ N) :=
            measure_mono (hS N y hWy)
        _ ≤ P {ω | ¬ X y 0 ω = y} + P (K4.shiftPath X y ((q0 : ℝ).toNNReal) ⁻¹' Γ N) :=
            measure_union_le _ _
        _ = ∫⁻ ω, P (K4.Zf X (X y ((q0 : ℝ).toNNReal) ω) ⁻¹' Γ N) ∂P := by
            rw [hnull y hy, zero_add, hcp]
        _ ≤ ∫⁻ ω, ENNReal.ofReal (W (X y ((q0 : ℝ).toNNReal) ω) / a) ∂P := by
            refine lintegral_mono_ae ?_
            filter_upwards [hopen y hy ((q0 : ℝ).toNNReal)] with ω hω
            rw [hZ N _ (fun i => (hω i).le)]
            exact ih _ hω
        _ = ENNReal.ofReal (∫ ω, W (X y ((q0 : ℝ).toNNReal) ω) / a ∂P) := by
            rw [ofReal_integral_eq_lintegral_ofReal (hint.div_const a)]
            filter_upwards [hopen y hy ((q0 : ℝ).toNNReal)] with ω hω
            exact div_nonneg (hW0 _ hω) ha.le
        _ ≤ ENNReal.ofReal (W y / a) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [integral_div]
            exact div_le_div_of_nonneg_right hle ha.le

theorem doob_all {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n)
    (hopen : ∀ x ∈ openOrthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ openOrthant n)
    (W : SDEState n → ℝ) (hWm : Measurable W) (hW0 : ∀ z ∈ openOrthant n, 0 ≤ W z)
    (q0 : ℚ) (hq0 : 0 ≤ q0)
    (hstep : ∀ z ∈ openOrthant n, Integrable (fun ω => W (X z ((q0 : ℝ).toNNReal) ω)) P ∧
      ∫ ω, W (X z ((q0 : ℝ).toNNReal) ω) ∂P ≤ W z)
    (a : ℝ) (ha : 0 < a) :
    ∀ y ∈ openOrthant n,
      P {ω | ∃ j : ℕ, a ≤ W (X y ((j : ℝ≥0) * (q0 : ℝ).toNNReal) ω)} ≤
        ENNReal.ofReal (W y / a) := by
  intro y hy
  have e : {ω | ∃ j : ℕ, a ≤ W (X y ((j : ℝ≥0) * (q0 : ℝ).toNNReal) ω)} =
      ⋃ N : ℕ, {ω | ∃ j : ℕ, j ≤ N ∧ a ≤ W (X y ((j : ℝ≥0) * (q0 : ℝ).toNNReal) ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun ⟨j, h⟩ => ⟨j, j, le_rfl, h⟩, fun ⟨_, j, _, h⟩ => ⟨j, h⟩⟩
  rw [e, Monotone.measure_iUnion]
  · exact iSup_le fun N => doob_grid P C B X hX hC hinv hopen W hWm hW0 q0 hq0 hstep a ha N y hy
  · intro N M h ω ⟨j, hj, hw⟩
    exact ⟨j, hj.trans h, hw⟩

/-- T1a `grid_escape_bound` (paper (5.29)-(5.30)). -/
theorem grid_escape_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    ∀ μ ∈ M1 P C X, ∃ T0 : ℚ, 0 < T0 ∧ ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ β : ℝ, 0 < β →
      ∃ Δ : ℝ, 0 < Δ ∧ ∀ x ∈ Kbox μ k Δ, 1 - ε <
        (P {ω | ∀ j : ℕ, ∀ i, i ∉ supp μ → X x ((j : ℝ≥0) * ((T0 : ℝ)).toNNReal) ω i < β}).toReal := by
  intro μ hμ
  haveI : IsProbabilityMeasure P := hX.1
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    refine ⟨1, one_pos, fun k _ ε hε β _ => ⟨1, one_pos, fun x _ => ?_⟩⟩
    have e : {ω | ∀ j : ℕ, ∀ i : Fin 0, i ∉ supp μ →
        X x ((j : ℝ≥0) * (((1 : ℚ) : ℝ)).toNNReal) ω i < β} = univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro j i
      exact i.elim0
    rw [e, measure_univ, ENNReal.toReal_one]
    linarith
  have hc : ∀ i, 0 < c i := hA.2.2.1
  have hγ : 0 < γb := hA.2.2.2.1
  have hC := hA.2.1
  obtain ⟨δ₁, hδ₁⟩ := exists_isDelta0 C γb hγ
  have hδ₀ := delta_small C hδ₁
  set δ₀ := min δ₁ (1 / 2) with hδ₀def
  have hδ₀1 : δ₀ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨εA, hεA, R, hR⟩ := hA.2.2.2.2
  have hM : StochKolmogorov.Extinct.IsRadiusM (ec C) c γb (max R 1) :=
    ⟨lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx hl =>
      lt_of_le_of_lt (hR x hx ((le_max_left _ _).trans hl)) (by linarith)⟩
  have h13 : StochKolmogorov.Extinct.Assumption13 P (ec C) X μ := hμ
  have hXe : StochKolmogorov.Extinct.IsSolutionFamily P (ec C) B X := hX
  have hAe : StochKolmogorov.Extinct.Assumption11 (ec C) c γb := hA
  obtain ⟨phat, hphat, hsum, pcheck, hp0, hp1, ρe, hρe, h52⟩ :=
    StochKolmogorov.Extinct.inequalities_5_1_5_2 hn P (ec C) B X hXe c γb hAe μ h13 δ₀ hδ₀
  set H := StochKolmogorov.Extinct.Hconst (ec C) c γb δ₀ with hH
  obtain ⟨m, hm⟩ := exists_nat_gt (max (H / γb + 1) 1)
  have hm1 : (1 : ℝ) < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hmH : H < γb * ((m : ℝ) - 1) := by
    have h1 : H / γb < (m : ℝ) - 1 := by linarith [lt_of_le_of_lt (le_max_left _ _) hm]
    calc H = H / γb * γb := (div_mul_cancel₀ _ hγ.ne').symm
      _ < ((m : ℝ) - 1) * γb := mul_lt_mul_of_pos_right h1 hγ
      _ = γb * ((m : ℝ) - 1) := mul_comm _ _
  have hmH' : H < γb * (((m + 1 : ℕ) : ℝ) - 1) := by
    refine lt_of_lt_of_le hmH (mul_le_mul_of_nonneg_left ?_ hγ.le)
    push_cast
    linarith
  obtain ⟨Te, hTe, δe, hδe, h53⟩ := StochKolmogorov.Extinct.lemma_5_2 hn P (ec C) B X hXe c γb
    hAe μ h13 (max R 1) hM δ₀ hδ₀ phat ⟨hphat, hsum⟩ pcheck ⟨hp0, hp1⟩ ρe hρe h52 (m + 1) hmH'
  have hTe2 : ((m + 1 : ℕ) : ℝ) * Te = (m : ℝ) * Te + Te := by push_cast; ring
  obtain ⟨r, hr1, hr2⟩ :=
    exists_rat_btwn (show (m : ℝ) * Te < ((m + 1 : ℕ) : ℝ) * Te by linarith)
  have hr0 : (0 : ℝ) < r := lt_trans (mul_pos hm0 hTe) hr1
  have hrq : (0 : ℚ) ≤ r := (Rat.cast_pos.1 hr0).le
  have hTe'0 : 0 < (r : ℝ) / m := div_pos hr0 hm0
  have hmTe' : (m : ℝ) * ((r : ℝ) / m) = r := by field_simp
  have hTeTe' : Te ≤ (r : ℝ) / m := by
    rw [le_div_iff₀ hm0]
    linarith [mul_comm Te (m : ℝ)]
  have h53' := fun T (hT : T ∈ Set.Icc ((r : ℝ) / m) ((m : ℝ) * ((r : ℝ) / m))) =>
    h53 T ⟨hTeTe'.trans hT.1, hT.2.trans (by rw [hmTe']; exact hr2.le)⟩
  obtain ⟨θ, hθ0, hθ1, hcontract⟩ := StochKolmogorov.Extinct.proposition_5_1 hn P (ec C) B X hXe
    c γb hAe μ h13 (max R 1) hM δ₀ hδ₀ phat ⟨hphat, hsum⟩ pcheck ⟨hp0, hp1⟩ ρe hρe m hmH
    ((r : ℝ) / m) δe hTe'0 hδe h53'
  have hstep0 := StochKolmogorov.Extinct.one_step_5_11_5_12 hn P (ec C) B X hXe c γb hAe μ h13
    (max R 1) hM δ₀ hδ₀ phat ⟨hphat, hsum⟩ pcheck ⟨hp0, hp1⟩ ρe hρe m hmH ((r : ℝ) / m) δe θ
    hTe'0 hδe ⟨hθ0, hθ1⟩ hcontract
  rw [hmTe'] at hstep0
  have h31 := (StochKolmogorov.Extinct.lemma_3_1 hn P (ec C) B X hXe c γb hAe δ₀ hδ₀).2.1
  have hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n := by
    intro x hx s
    filter_upwards [h31 (Finset.univ.filter fun i => 0 < x i) x hx (fun i => by simp)] with ω hω
    show ∀ i, 0 ≤ X x s ω i
    intro i
    by_cases hi : 0 < x i
    · exact ((hω s).1 i (by simp [hi])).le
    · exact ((hω s).2 i (by simp [hi])).ge
  have hopen : ∀ x ∈ openOrthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ openOrthant n := by
    intro x hx s
    filter_upwards [h31 Finset.univ x (fun i => (hx i).le)
      (fun i => ⟨fun _ => hx i, fun _ => Finset.mem_univ i⟩)] with ω hω
    exact fun i => (hω s).1 i (Finset.mem_univ i)
  refine ⟨r, Rat.cast_pos.1 hr0, fun k hk ε hε β hβ => ?_⟩
  have hp : ∀ i ∈ StochKolmogorov.Extinct.supp μ, 0 ≤ phat i := fun i hi => (hphat i hi).1.le
  have hs : ∑ i ∈ StochKolmogorov.Extinct.supp μ, phat i ≤ 1 := hsum.trans (by linarith)
  have hς := varsigma_pos c hc μ phat hp hs pcheck θ δe hδe
  have hW0 : ∀ z ∈ openOrthant n, 0 ≤ StochKolmogorov.Extinct.Utilde c μ phat pcheck θ δe z :=
    fun z hz => le_min hς.le (Utheta_nonneg c hc μ phat pcheck θ z hz)
  have hK0 : 0 < ∏ j ∈ StochKolmogorov.Extinct.supp μ, (c j)⁻¹ ^ phat j :=
    Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (inv_pos.2 (hc j)) _
  have hβp : 0 < β ^ pcheck := Real.rpow_pos_of_pos hβ _
  set K := ∏ j ∈ StochKolmogorov.Extinct.supp μ, (c j)⁻¹ ^ phat j with hK
  set a := min (StochKolmogorov.Extinct.varsigma c μ phat pcheck θ δe) ((β ^ pcheck / K) ^ θ)
    with ha
  have ha0 : 0 < a := lt_min hς (Real.rpow_pos_of_pos (div_pos hβp hK0) _)
  have haK : a ^ θ⁻¹ * K ≤ β ^ pcheck := by
    have h1 : a ^ θ⁻¹ ≤ ((β ^ pcheck / K) ^ θ) ^ θ⁻¹ :=
      Real.rpow_le_rpow ha0.le (min_le_right _ _) (inv_nonneg.2 hθ0.le)
    rw [Real.rpow_rpow_inv (div_pos hβp hK0).le hθ0.ne'] at h1
    calc a ^ θ⁻¹ * K ≤ β ^ pcheck / K * K := mul_le_mul_of_nonneg_right h1 hK0.le
      _ = β ^ pcheck := div_mul_cancel₀ _ hK0.ne'
  have hgc : Continuous fun Δ : ℝ => (n : ℝ) * ((1 + ∑ j, c j * (k : ℝ)) * Δ ^ pcheck /
      ∏ j ∈ StochKolmogorov.Extinct.supp μ, ((k : ℝ)⁻¹) ^ phat j) ^ θ :=
    continuous_const.mul (((continuous_const.mul (Real.continuous_rpow_const hp0.le)).div_const
      _).rpow_const fun _ => Or.inr hθ0.le)
  have hεa : 0 < ε * a := mul_pos hε ha0
  have hev : ∀ᶠ Δ in 𝓝[>] (0 : ℝ), (n : ℝ) * ((1 + ∑ j, c j * (k : ℝ)) * Δ ^ pcheck /
      ∏ j ∈ StochKolmogorov.Extinct.supp μ, ((k : ℝ)⁻¹) ^ phat j) ^ θ < ε * a ∧
      Δ ∈ Set.Ioo (0 : ℝ) 1 := by
    refine Filter.Eventually.and ?_ (Ioo_mem_nhdsGT one_pos)
    refine ((hgc.tendsto 0).mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds ?_)
    simpa [Real.zero_rpow hp0.ne', Real.zero_rpow hθ0.ne'] using hεa
  obtain ⟨Δ, hgΔ, hΔ⟩ := hev.exists
  refine ⟨Δ, hΔ.1, fun x hx => ?_⟩
  have hxo : ∀ j, 0 < x j := hx.1
  have hU := Utheta_Kbox c hc μ phat hp pcheck θ hp0.le hθ0 k hk Δ hΔ.1.le hΔ.2.le x hx
  have hWx : StochKolmogorov.Extinct.Utilde c μ phat pcheck θ δe x < ε * a :=
    lt_of_le_of_lt (min_le_right _ _) (lt_of_le_of_lt hU hgΔ)
  have hsolx := hX.2.2 x (fun i => (hxo i).le)
  have hWm := measurable_Utilde c μ phat pcheck θ δe
  have hbadm : MeasurableSet {ω | ∃ j : ℕ, a ≤ StochKolmogorov.Extinct.Utilde c μ phat pcheck θ δe
      (X x ((j : ℝ≥0) * ((r : ℝ)).toNNReal) ω)} := by
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion fun j => measurableSet_le measurable_const (hWm.comp (hsolx.1 _))
  have hbadP := doob_all P C B X hX hC hinv hopen _ hWm hW0 r hrq hstep0 a ha0 x hxo
  have hG : ∀ᵐ ω ∂P, ∀ j : ℕ, X x ((j : ℝ≥0) * ((r : ℝ)).toNNReal) ω ∈ openOrthant n :=
    ae_all_iff.2 fun j => hopen x hxo _
  have hsub : {ω | ∃ j : ℕ, a ≤ StochKolmogorov.Extinct.Utilde c μ phat pcheck θ δe
      (X x ((j : ℝ≥0) * ((r : ℝ)).toNNReal) ω)}ᶜ ∩
      {ω | ∀ j : ℕ, X x ((j : ℝ≥0) * ((r : ℝ)).toNNReal) ω ∈ openOrthant n} ⊆
      {ω | ∀ j : ℕ, ∀ i, i ∉ supp μ → X x ((j : ℝ≥0) * ((r : ℝ)).toNNReal) ω i < β} := by
    rintro ω ⟨hb, hgo⟩ j i hi
    have hWj : StochKolmogorov.Extinct.Utilde c μ phat pcheck θ δe
        (X x ((j : ℝ≥0) * ((r : ℝ)).toNNReal) ω) < a := by
      by_contra hcon
      exact hb ⟨j, not_lt.1 hcon⟩
    have hUj : StochKolmogorov.Extinct.Utheta c μ phat pcheck θ
        (X x ((j : ℝ≥0) * ((r : ℝ)).toNNReal) ω) < a := by
      rcases min_lt_iff.1 hWj with h | h
      · exact absurd h (not_lt.2 (min_le_left _ _))
      · exact h
    have hz : ∀ l, 0 < X x ((j : ℝ≥0) * ((r : ℝ)).toNNReal) ω l := hgo j
    have h1 := coord_lt c hc μ phat hp hs pcheck θ hθ0 _ hz i hi a hUj
    have h2 := lt_of_lt_of_le h1 haK
    exact (Real.rpow_lt_rpow_iff (hz i).le hβ.le hp0).1 h2
  have hPbad := ENNReal.toReal_le_of_le_ofReal (div_nonneg (hW0 x hxo) ha0.le) hbadP
  have hWa : StochKolmogorov.Extinct.Utilde c μ phat pcheck θ δe x / a < ε := by
    rw [div_lt_iff₀ ha0]
    exact hWx
  have hcompl := congrArg ENNReal.toReal (prob_compl_eq_one_sub (μ := P) hbadm)
  rw [ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one] at hcompl
  have hconull := measure_inter_conull (μ := P) (s := {ω | ∃ j : ℕ, a ≤
      StochKolmogorov.Extinct.Utilde c μ phat pcheck θ δe
      (X x ((j : ℝ≥0) * ((r : ℝ)).toNNReal) ω)}ᶜ)
    (t := {ω | ∀ j : ℕ, X x ((j : ℝ≥0) * ((r : ℝ)).toNNReal) ω ∈ openOrthant n}) (ae_iff.1 hG)
  have hmono := ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (μ := P) hsub)
  rw [hconull] at hmono
  linarith

end StochKolmogorov.Classify.GE

end FlatM_T1a
-- ===== T1 =====
section FlatM_T1

/-! T1 `sink_box_avoids_far_set` glue (a17b7893 s4): Hening-Nguyen 1704.06984 (5.27)-(5.33).
First dyadic hitting time of the far set `O(R,η)`, the path Markov identity `FDMC.condPath_of`
and short-time positivity (T1b) give `P(hit O on grid m) ≤ 2 P(some grid value jT₀ has Xᵢ ≥ β)`;
continuity and openness of `O` pass to all times, and T1a bounds the right side. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace StochKolmogorov.Classify.SB
open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ}

theorem hit_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n)
    (μ : Measure (SDEState n)) (T0 : ℚ) (hT0 : 0 < T0) (β R η : ℝ)
    (hhalf : ∀ y ∈ orthant n, l1 y < R → ∀ i, η < y i →
      (2 : ℝ≥0∞)⁻¹ ≤ P {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T0 → β < X y t ω i})
    (x : SDEState n) (hx : x ∈ openOrthant n) (hxO : ∀ i, i ∉ supp μ → x i < η) :
    P {ω | ∃ t : ℝ≥0, l1 (X x t ω) < R ∧ ∃ i, i ∉ supp μ ∧ η < X x t ω i} ≤
      2 * P {ω | ∃ j : ℕ, ∃ i, i ∉ supp μ ∧
        β ≤ X x ((j : ℝ≥0) * ((T0 : ℝ)).toNNReal) ω i} := by
  classical
  haveI : IsProbabilityMeasure P := hX.1
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hsol := hX.2.2 x hxo
  have hT0r : (0 : ℝ) < T0 := by exact_mod_cast hT0
  have hco : ∀ i : Fin n, Continuous fun y : SDEState n => y i :=
    fun i => PiLp.continuous_apply 2 _ i
  set O : Set (SDEState n) := {y | l1 y < R ∧ ∃ i, i ∉ supp μ ∧ η < y i} with hOdef
  have hOo : IsOpen O := by
    have e : O = {y : SDEState n | l1 y < R} ∩
        ⋃ i, ⋃ (_ : i ∉ supp μ), {y : SDEState n | η < y i} := by
      ext y; simp [hOdef]
    rw [e]
    have hl : Continuous fun y : SDEState n => l1 y := by
      unfold l1
      exact continuous_finset_sum _ fun i _ => (hco i).abs
    exact (isOpen_lt hl continuous_const).inter
      (isOpen_iUnion fun i => isOpen_iUnion fun _ => isOpen_lt continuous_const (hco i))
  have hxO' : x ∉ O := fun ⟨_, i, hi, h⟩ => absurd (hxO i hi) (not_lt.2 h.le)
  set Bad := {ω | ∃ j : ℕ, ∃ i, i ∉ supp μ ∧
    β ≤ X x ((j : ℝ≥0) * ((T0 : ℝ)).toNNReal) ω i} with hBad
  have hBadm : MeasurableSet Bad := by
    simp only [hBad, Set.setOf_exists, Set.setOf_and]
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun i =>
      (MeasurableSet.const _).inter
        (measurableSet_le measurable_const ((hco i).measurable.comp (hsol.1 _)))
  have hnull : P {ω | ¬ X x 0 ω = x} = 0 := ae_iff.1 hsol.2.2.2.1
  let tm : ℕ → ℕ → ℝ≥0 := fun m l => (((l : ℚ) / 2 ^ m : ℚ) : ℝ).toNNReal
  let Am : ℕ → Set Ω := fun m => {ω | ∃ l : ℕ, X x (tm m l) ω ∈ O}
  have hcover : {ω | ∃ t : ℝ≥0, l1 (X x t ω) < R ∧ ∃ i, i ∉ supp μ ∧ η < X x t ω i} ⊆
      ⋃ m, Am m := by
    rintro ω ⟨t, ht⟩
    have hU : IsOpen {s : ℝ≥0 | X x s ω ∈ O} := hOo.preimage (hsol.2.1 ω)
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU t ht
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
    refine Set.mem_iUnion.2 ⟨m, ⌈(t : ℝ) * 2 ^ m⌉₊, hball ?_⟩
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    have ht0 : (0 : ℝ) ≤ t := t.2
    have hl1 : (t : ℝ) * 2 ^ m ≤ (⌈(t : ℝ) * 2 ^ m⌉₊ : ℝ) := Nat.le_ceil _
    have hl2 : (⌈(t : ℝ) * 2 ^ m⌉₊ : ℝ) < (t : ℝ) * 2 ^ m + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hq : ((((⌈(t : ℝ) * 2 ^ m⌉₊ : ℕ) : ℚ) / 2 ^ m : ℚ) : ℝ) =
        (⌈(t : ℝ) * 2 ^ m⌉₊ : ℝ) / 2 ^ m := by push_cast; ring
    have hge : (t : ℝ) ≤ (⌈(t : ℝ) * 2 ^ m⌉₊ : ℝ) / 2 ^ m := by
      rw [le_div_iff₀ h2]; exact hl1
    have e : (1 / 2 : ℝ) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
    have hlt : (⌈(t : ℝ) * 2 ^ m⌉₊ : ℝ) / 2 ^ m < t + (1 / 2) ^ m := by
      rw [div_lt_iff₀ h2, add_mul, e]; exact hl2
    rw [Metric.mem_ball, NNReal.dist_eq]
    show |(((((⌈(t : ℝ) * 2 ^ m⌉₊ : ℕ) : ℚ) / 2 ^ m : ℚ) : ℝ).toNNReal : ℝ) - t| < δ
    rw [Real.coe_toNNReal _ (by rw [hq]; positivity), hq, abs_of_nonneg (by linarith)]
    linarith
  have hmono : Monotone Am := by
    refine monotone_nat_of_le_succ fun m ω hω => ?_
    obtain ⟨l, hl⟩ := hω
    refine ⟨2 * l, ?_⟩
    have e : ((2 * l : ℕ) : ℚ) / 2 ^ (m + 1) = (l : ℚ) / 2 ^ m := by
      rw [pow_succ, div_eq_div_iff (by positivity) (by positivity)]
      push_cast; ring
    show X x ((((((2 * l : ℕ) : ℚ) / 2 ^ (m + 1)) : ℚ) : ℝ).toNNReal) ω ∈ O
    rw [e]
    exact hl
  let Γ : Set (ℚ → SDEState n) :=
    {p | ∃ i, i ∉ supp μ ∧ ∀ q : ℚ, 0 ≤ q → q ≤ T0 → β < p q i}
  have hΓ : MeasurableSet Γ := by
    have e : Γ = ⋃ i, ⋃ (_ : i ∉ supp μ), ⋂ q : ℚ, ⋂ (_ : 0 ≤ q), ⋂ (_ : q ≤ T0),
        {p : ℚ → SDEState n | β < p q i} := by
      ext p; simp [Γ]
    rw [e]
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
        measurableSet_lt measurable_const ((hco i).measurable.comp (measurable_pi_apply q))
  have hstepm : ∀ m, P (Am m) ≤ 2 * P Bad := by
    intro m
    let s : ℕ → ℚ := fun l => ((l + 1 : ℕ) : ℚ) / 2 ^ m
    have hs0 : ∀ l, 0 < s l := fun l => by positivity
    let tt : ℕ → ℝ≥0 := fun l => ((s l : ℚ) : ℝ).toNNReal
    have htt : ∀ l, (tt l : ℝ) = (s l : ℝ) :=
      fun l => Real.coe_toNNReal _ (by exact_mod_cast (hs0 l).le)
    have hsle : ∀ l l', l' ≤ l → s l' ≤ s l := by
      intro l l' h
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ h) (by positivity)
    let pt : ∀ l l', l' ≤ l → FDMC.Past (tt l) := fun l l' h =>
      ⟨s l', hs0 l', by rw [htt]; exact_mod_cast hsle l l' h⟩
    let A : ∀ l, Set (FDMC.Past (tt l) → SDEState n) := fun l =>
      {g | g (pt l l le_rfl) ∈ O ∧ ∀ l' (h : l' < l), g (pt l l' h.le) ∉ O}
    have hAm : ∀ l, MeasurableSet (A l) := by
      intro l
      have e : A l = (fun g : FDMC.Past (tt l) → SDEState n => g (pt l l le_rfl)) ⁻¹' O ∩
          ⋂ l', ⋂ (h : l' < l),
            (fun g : FDMC.Past (tt l) → SDEState n => g (pt l l' h.le)) ⁻¹' Oᶜ := by
        ext g; simp [A]
      rw [e]
      exact ((measurable_pi_apply (pt l l le_rfl)) hOo.measurableSet).inter
        (MeasurableSet.iInter fun l' => MeasurableSet.iInter fun (h : l' < l) =>
          (measurable_pi_apply (pt l l' h.le)) hOo.measurableSet.compl)
    let E : ℕ → Set Ω := fun l => FDMC.past X x (tt l) ⁻¹' A l
    have hEm : ∀ l, MeasurableSet (E l) := fun l =>
      (FDMC.measurable_past X x (tt l) hsol.1) (hAm l)
    have hdisj : Pairwise (Function.onFun Disjoint E) := by
      intro l l' hne
      refine Set.disjoint_left.2 fun ω h1 h2 => ?_
      rcases lt_or_gt_of_ne hne with h | h
      · exact h2.2 l h h1.1
      · exact h1.2 l' h h2.1
    have hcov : Am m ⊆ {ω | ¬ X x 0 ω = x} ∪ ⋃ l, E l := by
      rintro ω ⟨l, hl⟩
      by_cases h0 : X x 0 ω = x
      · right
        have hex : ∃ l, X x (tt l) ω ∈ O := by
          rcases l with _ | l
          · exfalso
            have e0 : tm m 0 = 0 := by simp [tm]
            rw [e0, h0] at hl
            exact hxO' hl
          · exact ⟨l, hl⟩
        exact Set.mem_iUnion.2 ⟨Nat.find hex, Nat.find_spec hex,
          fun l' h => Nat.find_min hex h⟩
      · left
        exact h0
    have hEl : ∀ l, P (E l) ≤ 2 * P (E l ∩ Bad) := by
      intro l
      obtain ⟨-, hcp⟩ := FDMC.condPath_of P C B X hX hC hinv x hx (tt l) (A l) (hAm l) Γ hΓ
      have hlow : (2 : ℝ≥0∞)⁻¹ * P (E l) ≤
          P (K4.shiftPath X x (tt l) ⁻¹' Γ ∩ FDMC.past X x (tt l) ⁻¹' A l) := by
        rw [hcp, ← setLIntegral_const]
        refine lintegral_mono_ae ?_
        rw [ae_restrict_iff' (hEm l)]
        filter_upwards [hinv x hxo (tt l)] with ω hωo hωA
        obtain ⟨hl1, i, hi, hηi⟩ := hωA.1
        refine (hhalf _ hωo hl1 i hηi).trans (measure_mono ?_)
        intro ω' hω'
        show K4.Zf X (X x (tt l) ω) ω' ∈ Γ
        simp only [K4.Zf, if_pos hωo]
        refine ⟨i, hi, fun q hq0 hqT => hω' _ ?_⟩
        rw [Real.coe_toNNReal _ (by exact_mod_cast hq0)]
        exact_mod_cast hqT
      have hsub : K4.shiftPath X x (tt l) ⁻¹' Γ ∩ FDMC.past X x (tt l) ⁻¹' A l ⊆ E l ∩ Bad := by
        rintro ω ⟨⟨i, hi, hq⟩, hA⟩
        refine ⟨hA, ?_⟩
        have hsl0 : (0 : ℝ) ≤ (s l : ℝ) := by exact_mod_cast (hs0 l).le
        obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌈(s l : ℝ) / T0⌉₊ := ⟨_, rfl⟩
        have hj1 : (s l : ℝ) ≤ j * T0 := by
          have := Nat.le_ceil ((s l : ℝ) / T0)
          rw [← hj, div_le_iff₀ hT0r] at this
          exact this
        have hj2 : (j : ℝ) * T0 < s l + T0 := by
          have := Nat.ceil_lt_add_one (div_nonneg hsl0 hT0r.le)
          rw [← hj] at this
          calc (j : ℝ) * T0 < ((s l : ℝ) / T0 + 1) * T0 := mul_lt_mul_of_pos_right this hT0r
            _ = s l + T0 := by rw [add_mul, div_mul_cancel₀ _ hT0r.ne', one_mul]
        obtain ⟨q, hqd⟩ : ∃ q : ℚ, q = (j : ℚ) * T0 - s l := ⟨_, rfl⟩
        have hq0 : 0 ≤ q := by
          have : (s l : ℚ) ≤ j * T0 := by exact_mod_cast hj1
          rw [hqd]; linarith
        have hqT : q ≤ T0 := by
          have : (j : ℚ) * T0 < s l + T0 := by exact_mod_cast hj2
          rw [hqd]; linarith
        have htime : tt l + ((q : ℚ) : ℝ).toNNReal = (j : ℝ≥0) * ((T0 : ℝ)).toNNReal := by
          apply NNReal.coe_injective
          rw [NNReal.coe_add, NNReal.coe_mul, htt, Real.coe_toNNReal _ (by exact_mod_cast hq0),
            Real.coe_toNNReal _ hT0r.le, NNReal.coe_natCast, hqd]
          push_cast; ring
        have h := hq q hq0 hqT
        simp only [K4.shiftPath] at h
        rw [htime] at h
        exact ⟨j, i, hi, h.le⟩
      have h2 : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
      calc P (E l) = 2 * ((2 : ℝ≥0∞)⁻¹ * P (E l)) := by rw [← mul_assoc, h2, one_mul]
        _ ≤ 2 * P (E l ∩ Bad) := by gcongr; exact hlow.trans (measure_mono hsub)
    calc P (Am m) ≤ P ({ω | ¬ X x 0 ω = x} ∪ ⋃ l, E l) := measure_mono hcov
      _ ≤ P {ω | ¬ X x 0 ω = x} + P (⋃ l, E l) := measure_union_le _ _
      _ = ∑' l, P (E l) := by rw [hnull, zero_add, measure_iUnion hdisj hEm]
      _ ≤ ∑' l, 2 * P (E l ∩ Bad) := ENNReal.tsum_le_tsum hEl
      _ = 2 * P (⋃ l, E l ∩ Bad) := by
          rw [ENNReal.tsum_mul_left, measure_iUnion
            (hdisj.mono fun _ _ h => h.mono inter_subset_left inter_subset_left)
            (fun l => (hEm l).inter hBadm)]
      _ ≤ 2 * P Bad := by
          gcongr
          exact iUnion_subset fun l => inter_subset_right
  calc P {ω | ∃ t : ℝ≥0, l1 (X x t ω) < R ∧ ∃ i, i ∉ supp μ ∧ η < X x t ω i}
      ≤ P (⋃ m, Am m) := measure_mono hcover
    _ = ⨆ m, P (Am m) := hmono.measure_iUnion
    _ ≤ 2 * P Bad := iSup_le hstepm

/-- T1 `sink_box_avoids_far_set` from T1a (grid escape, rational step) and T1b. -/
theorem sink_box {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n)
    (hT1a : ∀ μ ∈ M1 P C X, ∃ T0 : ℚ, 0 < T0 ∧ ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ β : ℝ, 0 < β →
      ∃ Δ : ℝ, 0 < Δ ∧ ∀ x ∈ Kbox μ k Δ, 1 - ε <
        (P {ω | ∀ j : ℕ, ∀ i, i ∉ supp μ →
          X x ((j : ℝ≥0) * ((T0 : ℝ)).toNNReal) ω i < β}).toReal)
    (hT1b : ∀ R T : ℝ, 0 < T → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → ∃ β : ℝ, 0 < β ∧
      ∀ i, ∀ x ∈ orthant n, l1 x ≤ R → ε₂ < x i →
        1 - ε₁ < (P {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T → β < X x t ω i}).toReal) :
    ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ R η : ℝ, 0 < η →
      ∃ Δ : ℝ, 0 < Δ ∧ ∀ x ∈ Kbox μ k Δ, 1 - ε < (P {ω | ∀ t : ℝ≥0,
        ¬ (l1 (X x t ω) < R ∧ ∃ i, i ∉ supp μ ∧ η < X x t ω i)}).toReal := by
  intro μ hμ k hk ε hε R η hη
  haveI : IsProbabilityMeasure P := hX.1
  obtain ⟨T0, hT0, hTa⟩ := hT1a μ hμ
  have hT0r : (0 : ℝ) < T0 := by exact_mod_cast hT0
  obtain ⟨β, hβ, hTb⟩ := hT1b R T0 hT0r (1 / 2) η (by norm_num) hη
  obtain ⟨Δ, hΔ, hTa'⟩ := hTa k hk (ε / 4) (by positivity) β hβ
  refine ⟨min Δ η, lt_min hΔ hη, fun x hx => ?_⟩
  have hxΔ : x ∈ Kbox μ k Δ :=
    ⟨hx.1, hx.2.1, fun i hi => (hx.2.2 i hi).trans_le (min_le_left _ _)⟩
  have hxη : ∀ i, i ∉ supp μ → x i < η := fun i hi => (hx.2.2 i hi).trans_le (min_le_right _ _)
  have hhalf : ∀ y ∈ orthant n, l1 y < R → ∀ i, η < y i →
      (2 : ℝ≥0∞)⁻¹ ≤ P {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T0 → β < X y t ω i} := by
    intro y hy hl i hi
    have h := hTb i y hy hl.le hi
    have h2 : ENNReal.ofReal (1 / 2) ≤ P {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T0 → β < X y t ω i} :=
      ENNReal.ofReal_le_of_le_toReal (by linarith)
    convert h2 using 1
    rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  have hmain := hit_le P C B X hX hC hinv μ T0 hT0 β R η hhalf x hx.1 hxη
  have hsol := hX.2.2 x (fun i => (hx.1 i).le)
  have hco : ∀ i : Fin n, Continuous fun y : SDEState n => y i :=
    fun i => PiLp.continuous_apply 2 _ i
  set Bad := {ω | ∃ j : ℕ, ∃ i, i ∉ supp μ ∧
    β ≤ X x ((j : ℝ≥0) * ((T0 : ℝ)).toNNReal) ω i} with hBad
  have hBadm : MeasurableSet Bad := by
    simp only [hBad, Set.setOf_exists, Set.setOf_and]
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun i =>
      (MeasurableSet.const _).inter
        (measurableSet_le measurable_const ((hco i).measurable.comp (hsol.1 _)))
  have hgood := hTa' x hxΔ
  have hBadc : {ω | ∀ j : ℕ, ∀ i, i ∉ supp μ →
      X x ((j : ℝ≥0) * ((T0 : ℝ)).toNNReal) ω i < β} = Badᶜ := by
    ext ω; simp [hBad]
  rw [hBadc, prob_compl_eq_one_sub hBadm, ENNReal.toReal_sub_of_le prob_le_one
    ENNReal.one_ne_top, ENNReal.toReal_one] at hgood
  set Hit := {ω | ∃ t : ℝ≥0, l1 (X x t ω) < R ∧ ∃ i, i ∉ supp μ ∧ η < X x t ω i} with hHit
  have hgoalset : {ω | ∀ t : ℝ≥0,
      ¬ (l1 (X x t ω) < R ∧ ∃ i, i ∉ supp μ ∧ η < X x t ω i)} = Hitᶜ := by
    ext ω; simp [hHit]
  rw [hgoalset]
  have hHit2 : (P Hit).toReal ≤ 2 * (P Bad).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (measure_ne_top _ _))
      hmain
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this
  have hun : (1 : ℝ≥0∞) ≤ P Hit + P Hitᶜ := by
    rw [← measure_univ (μ := P), ← Set.union_compl_self Hit]
    exact measure_union_le _ _
  have hun' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
    hun
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at hun'
  linarith

end StochKolmogorov.Classify.SB

end FlatM_T1
-- ===== ItoM1 =====
section FlatM_ItoM1

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace ItoLib
open EthierKurtz

variable {Ω : Type*} {d : ℕ}

section BM
variable [MeasurableSpace Ω]

end BM

section AEC
variable {mΩ : MeasurableSpace Ω}

end AEC

section CP
variable [MeasurableSpace Ω]

end CP

section M2

variable [MeasurableSpace Ω]

end M2

section M3
variable [MeasurableSpace Ω]

end M3

section M4
variable [MeasurableSpace Ω]

end M4


section StopCoef

end StopCoef

section M5
variable [MeasurableSpace Ω]

end M5


section M5b

end M5b

section M5c
variable [MeasurableSpace Ω]

end M5c


section M6refine

end M6refine


section M6osc

end M6osc


section M6cauchy
variable [MeasurableSpace Ω]

end M6cauchy


section M6limit
variable [MeasurableSpace Ω]

end M6limit


section M6trunc

end M6trunc

section M6exist
variable [MeasurableSpace Ω]

end M6exist


section M7grid

end M7grid

section M7zero
variable [MeasurableSpace Ω]

end M7zero


section M7qv
variable [MeasurableSpace Ω]

end M7qv

section M7c
variable [MeasurableSpace Ω]

end M7c

section M8a
variable [MeasurableSpace Ω]

end M8a

section M8b
variable [MeasurableSpace Ω]

end M8b

section M8c
variable [MeasurableSpace Ω]

end M8c

section M8d
variable [MeasurableSpace Ω]

end M8d

section M8e
variable [MeasurableSpace Ω]

end M8e


section M8f
variable [MeasurableSpace Ω]

end M8f


section M8f2
variable [MeasurableSpace Ω]

end M8f2


section M8f3
variable [MeasurableSpace Ω]

end M8f3


section M8gTaylor
open Set

end M8gTaylor

section M8g
variable [MeasurableSpace Ω]

end M8g


section M8g2

end M8g2


section M8g3
variable [MeasurableSpace Ω]

end M8g3

section M8g4
variable [MeasurableSpace Ω]

end M8g4

section M8g5
variable [MeasurableSpace Ω]

end M8g5

section M9a
variable [MeasurableSpace Ω]

end M9a


section M9c
/-! M9c: calculus for the pathwise-uniqueness test function (line derivatives, cutoff). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

end M9cF


section M9c2
/-! Packing `(x, y, a)` into `SDEState (d + d + 1)` and the structure of `Ff`. -/

end M9c2


section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

end M9d


section M9d2
/-! Global bounds for the generator and the integrands (compact support of `Ff` in (x, y)). -/

end M9d2



section M9e1
/-! Zero integral, measurability of time integrals, the exponential primitive identity, and the
pointwise generator bound with the localizing rate `kap`. -/

end M9e1


section M9e2
/-! Ito formula for `Ff r (X, Y, A)` and pathwise uniqueness for time-homogeneous, locally
Lipschitz coefficients (no stopping times: localization through the rate `kap`). -/

end M9e2


end ItoLib

end FlatM_ItoM1
-- ===== E =====
section FlatM_E
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10b1
/-! M10b-1: pathwise identification of Ito integrals. For an integrand that is an indefinite
integral in time (`h s = h 0 + ∫₀ˢ D`), left-point sums converge pathwise to the integration by
parts value `h t w t - h 0 w 0 - ∫₀ᵗ w D`; and pathwise limits of left-point sums are Ito
integrals in the sense of `HasBrownianItoIntegral`. -/

end M10b1

section M10b2
/-! M10b-2 (generic part): piecewise-linear interpolation of a sequence on the grid `k h`,
defined as a primitive of the piecewise-constant slope. -/

end M10b2

section M10b2s
/-! M10b-2: the truncated Euler scheme with lagged, linearly interpolated coefficients, driven by a
deterministic path `w`. `eulerZZ k = (Z_{k-1}, Z_k)`. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)
  (w : ℝ≥0 → SDEState d)

variable {s₁ b₁ h w}

end M10b2s


section M10b2w
/-! M10b-2 (random part): the scheme driven by a Brownian path is adapted, continuous, and an
Ito process. Measurability is proved for any monotone family `G` of σ-algebras that sees the
past of `W` (used with `G = completedBrownianPast` and with the ambient σ-algebra). -/

variable {W : ℝ≥0 → Ω → SDEState d} {G : ℝ≥0 → MeasurableSpace Ω}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10b2w


section M10b2i
/-! M10b-2: the scheme driven by standard Brownian motion is an Ito process in the sense of
`ito_formula`. -/

variable [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10b2i


section M10b4a
/-! M10b-4 (a): Ito formula for `Ff r` along `(X, Y, A)` where `X`, `Y` are general Ito
processes (matrix integrands `HX`, `HY`, drifts `bX`, `bY`), `A = ∫ κ(X, Y)`. -/

end M10b4a


section M10b4b
/-! M10b-4 (b): pathwise bounds for the generator `driftG` when `X` has coefficients
`σ₀(X), b₀(X)` and `Y` has arbitrary coefficients `σy, by'`. -/

end M10b4b

end ItoLib

end FlatM_E
-- ===== F =====
section FlatM_F
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c1
/-! M10c-1: the saturating profile `ψ(Q) = 1 - (1 - st(Q/4)) e^{-Q}` (`ψ(0) = 0`, `ψ = 1` for
`Q ≥ 4`, `ψ(Q) ≥ Q/5` on `[0,4]`) and the test function
`Gf r (x, y, a) = e^{-a} χ_r(|x|²) ψ(|x-y|²)` (cut-off in `x` only). -/

end M10c1

section M10c2
/-! M10c-2: the generator of `Gf r` along `(X, Y, A)` and its form inside the `x`-ball. -/

end M10c2

section M10c3
/-! M10c-3: pointwise bounds for the generator `driftH` of `Gf r`. -/

end M10c3

end ItoLib

end FlatM_F
-- ===== G =====
section FlatM_G
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c4
/-! M10c-4: the Ito formula along `(X, Y, A)` for an arbitrary `C²` test function `F` whose
martingale integrands are bounded (`ito_coupled_F`); applied to `Gf r`. -/

end M10c4


section M10c5
/-! M10c-5: expectation bound for `Gf r` along `(X, Y, A)`, `X` the SDE solution, `Y` a general
Ito process with globally bounded coefficients, clock rate `kapX` (penalising only `X`). -/

end M10c5


section M10c6
/-! M10c-6: pathwise error of the truncated Euler scheme: on `[0, T]` the coefficient errors
`s₁(Y_u) - H_u`, `b₁(Y_u) - b_u` are `O(osc_w(h) + h)` (lag start `a = y`). -/

theorem euc_norm_le_sum' {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖ ≤ ∑ k, |v k| := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ k, ‖v k‖ ^ 2) ≤ √((∑ k, |v k|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Real.norm_eq_abs]
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
    _ = ∑ k, |v k| := Real.sqrt_sq (Finset.sum_nonneg fun k _ => abs_nonneg _)

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c6

end ItoLib

end FlatM_G
-- ===== H =====
section FlatM_H
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c7
/-! M10c-7: the Euler scheme's coefficient error `‖s₁(Y_u) - H_u‖`, `‖b₁(Y_u) - b_u‖` is
`≤ 2 L K` with `K = d (3 d S δ + 2 S h)` (`δ` = oscillation of `w` over gaps `≤ h` on `[0, T]`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c7

section M10c8
/-! M10c-8: the coupled expectation bound `lintegral_Gf_le` with `Y` the truncated Euler scheme
driven by `W` (lag start `a = y = x₀`), `s₁ = σ₀`, `b₁ = b₀` on `B̄_{R+3}`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10c8

section M10c9
/-! M10c-9: `E ∫₀ᵗ eulerErr → 0` along any mesh sequence `hₙ → 0` (globally Lipschitz,
bounded truncated coefficients). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10c9

section M10c10
/-! M10c-10: the truncated Euler scheme converges to the SDE solution in probability on the
event that `X` stays in `B̄_R` (truncation radius `≥ R + 3`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10c10

end ItoLib

end FlatM_H
-- ===== I =====
section FlatM_I
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10d1
/-! M10d-1 (b5 groundwork): the cell noise `ζ_j = (1/h) ∫₀ʰ (W(s+h) - W(s+u)) du`: measurable for
the future-increment σ-algebra (so independent of the completed past), mean zero, `E ζ² ≤ h/2`. -/

end M10d1

section M10d2
/-! M10d-2: one cell of the L² stability estimate: for completed-past-measurable `D` (L²) and
bounded `A, B`, `E‖D + N‖² ≤ E‖D‖² + 2 d h E(‖A‖² + ‖B‖²)` with the cell noise
`N_i = Σⱼ (A_ij ξ_j + B_ij ζ_j)`. -/

end M10d2

end ItoLib

end FlatM_I
-- ===== J =====
section FlatM_J
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10d3
/-! M10d-3 (b5): one full cell of the Euler scheme in cell-noise form, and L² of the grid values. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

theorem coord_abs_le_state (x : SDEState d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i; rwa [Real.norm_eq_abs] at this

end M10d3

end ItoLib

end FlatM_J
-- ===== K =====
section FlatM_K
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10e1
/-! M10e-1 (b6 groundwork): the scheme as a deterministic recursion `zrec` driven by the cell
noises `(ξ_l, ζ_l)`; restart identity `Z_{m+k} = zrec_k(Z_{m-1}, Z_m; noises of cells m, m+1, ...)`;
the noises after cell `m` are measurable for the future-increment σ-algebra. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

variable {s₁ b₁ h}

end M10e1

section M10e2
/-! M10e-2 (b6): restart at a grid time. Independence of the past pair `(Z_{m-1}, Z_m)` and the
future noises gives `E f(Z_{m+k}) = E[ E' f(zrec_k(Z_{m-1}, Z_m; noises after m)) ]`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10e2

end ItoLib

end FlatM_K
-- ===== L =====
section FlatM_L
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10e3
/-! M10e-3 (b6): time homogeneity. The restarted Brownian motion is standard; the noises after
cell `m` are the noises of the restarted motion; any two standard Brownian motions have the same
finite-dimensional laws. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10e3

section M10e4
/-! M10e-4 (b6 DONE): restart in law at a grid time: `E f(Z_{m+k}) = E G(Z_{m-1}, Z_m)` with
`G(a, y) = E f(Z_k from (a, y))`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10e4

end ItoLib

end FlatM_L
-- ===== CB =====
section FlatM_CB
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CB (CORE route C2, s22): Cameron-Martin shift formula for centered Gaussians, one-dimensional
and for finite independent families (`Measure.pi`). -/

end ItoLib

end FlatM_CB
-- ===== CC =====
section FlatM_CC
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C2b
/-! CORE route C2b (s23): one-cell Cameron-Martin for the cell noise `(ξ, ζ)` with a constant shift:
weighting by `cmwPi h u ξ` and shifting `(ξ, ζ) ↦ (ξ + u, ζ + u/2)` preserves the law.
Route: dyadic increments are i.i.d. `N(0, h/2^n)` (`dInc_law`), the dyadic approximation of the
noise is a linear function `psiN` of them (`apx_eq_psiN`), finite-dimensional Cameron-Martin
(`gauss_pi_shift`) at each level, then the limit `n → ∞`. -/

end C2b

end ItoLib

end FlatM_CC
-- ===== CD =====
section FlatM_CD
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C3
/-! CORE route C3 (s23): adapted discrete Girsanov over the cells. The first `k` cell noises have
law `ν_k = ν_{k-1} ⊗ ν_1` (independence of the past and time homogeneity); shifting cell `l` by
`(u_l, u_l/2)` with `u_l` a measurable function of the earlier noises and weighting by
`∏ cmwPi h u_l ξ_l` preserves `ν_k` (`girsanov_cells`). -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end C3

end ItoLib

end FlatM_CD
-- ===== CE =====
section FlatM_CE
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {d : ℕ}

section C4a
/-! CORE route C4a (s23): the steered coupling, deterministic part. Two copies of the scheme are run
on one noise sequence; the second copy uses the shifted noise `n + (u, u/2)` with the adapted
steering `u_l = J(Ŷ pair)((X_l - Ŷ_l)/(m - l))`. The shift adds `avgApply p u` to a step
(`zstep_shift`), so with a right inverse `J` of `avgApply` the step adds `(X_l - Ŷ_l)/(m - l)`
(`cstep_steer`). The steered copy is the plain scheme driven by `shV (steerN ..)` (`shV_crec`). -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

variable (J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)) (m : ℕ)

variable {s₁ b₁ h J m}

end C4a

end ItoLib

end FlatM_CE
-- ===== CF =====
section FlatM_CF
open Filter Set
open scoped BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CORE route C4b (s23): the steered second-moment recursion. If
`e_{k+1} ≤ (1 - 1/(m-k))² e_k + c h (e_k + e_{k-1})` (with `e_{-1}` given by `e' 0`), then
`e_k ≤ G ((m-k)/m)² (1 + 13 c h)^k` for `k < m`. Key fact: `(j+1)² + (j+2)² ≤ 13 j²` for `j ≥ 1`. -/

end ItoLib

end FlatM_CF
-- ===== CG =====
section FlatM_CG
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C4c
/-! CORE route C4c (s24): the steered coupling driven by a Brownian motion. Past-measurability of
the coupled chain, the one-step identity `D_{k+1} = (1 - 1/(m-k)) D_k + h/2 Δb + cellNoise`,
and the second-moment step feeding `steer_rec` (CF.lean). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C4c

end ItoLib

end FlatM_CG
-- ===== CH =====
section FlatM_CH
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
variable {Ω : Type*}

section C4d
/-! CORE route C4d (s24): lower bound of a weighted event by the relative entropy, with no second
moment of the Girsanov martingale. If `f > 0`, `E f ≤ 1` and `E[-log f] ≤ K`, then
`E[1_E f] ≥ e^{-a} (P E - (K+1)/a)` (Markov on `-log f + f ≥ (-log f)⁺`). -/

end C4d

section C4d2
/-! C4d (s25): the relative entropy of the steering weight. -/
open EthierKurtz

variable {d : ℕ} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C4d2

end ItoLib

end FlatM_CH
-- ===== CI =====
section FlatM_CI
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
set_option autoImplicit false

namespace ItoLib

section C5a
/-! CORE route C5a (s25): Kolmogorov's maximal inequality in the abstract form needed for the
exit estimate of the Euler chain. The only probabilistic input is the orthogonality of the
"stopped" value `1_{F_k} M_k` to the remaining increment `M_m - M_k`. -/

variable {Ω : Type*} {d : ℕ}

end C5a

end ItoLib

end FlatM_CI
-- ===== CK =====
section FlatM_CK
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5c
/-! CORE route C5c (s26): exit estimate for the Euler chain with bounded coefficients.
`Z_k = Z_0 + M_k + D_k` with `M` the martingale part (orthogonal cell increments) and `D` the
drift part (`‖D_k‖ ≤ k h S`); Kolmogorov's maximal inequality on `M` gives
`(δ/2)^2 P(∃ k ≤ m, ‖Z_k - Z_0‖ ≥ δ) ≤ 16 d S^2 m h` once `m h S ≤ δ/2`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end C5c
end ItoLib

end FlatM_CK
-- ===== CL =====
section FlatM_CL
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5d
/-! CORE route C5d (s26): a global, measurable, bounded right inverse of `avgApply` for diffusions
of the form `s x (i, j) = a i x * Γ j i` (the Kolmogorov diffusion read through a projection),
when `Γ` is invertible and `|a i x + a i y| ≥ κ > 0`. -/

variable {d : ℕ}

end C5d
end ItoLib

end FlatM_CL
-- ===== M =====
section FlatM_M
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10f1
/-! M10f-1 (b7 groundwork): the restart function `G_k(a, y) = E f(Z_k from (a, y))` is Lipschitz
in the initial pair for Lipschitz `f`, uniformly in the mesh (via `euler_stab_exp`). -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10f1

end ItoLib

end FlatM_M
-- ===== N =====
section FlatM_N
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10f2
/-! M10f-2 (b7): uniform smallness of Euler cell increments, and the exit probability
`P(path leaves B̄_R before T) → 0`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {w : ℝ≥0 → SDEState d}

variable [MeasurableSpace Ω]

end M10f2

section M10f3
/-! M10f-3 (b7): the Euler scheme approximates `X_T` in law, up to the exit probability. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10f3

section M10f4
/-! M10f-4 (b7): the real-analysis wrap-up of the Chapman-Kolmogorov limit
(reverse Fatou in `n`, dominated convergence in `R`). -/

variable [MeasurableSpace Ω]

end M10f4

section M10f5
/-! M10f-5 (b7): the restart function `eulerG`, its bound and uniform Lipschitz property, and the
approximation `eulerG(y, y) ≈ E f(X^y_t)` up to the exit probability. -/

variable [MeasurableSpace Ω]

variable {P : Measure Ω} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10f5

section M10f6
/-! M10f-6 (b7 DONE): Chapman-Kolmogorov in integrated form for bounded Lipschitz test functions,
with a measurable version `g` of `y ↦ E f(X^y_t)`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10f6

end ItoLib

end FlatM_N
-- ===== O =====
section FlatM_O
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10g
/-! M10g: from integrated Chapman-Kolmogorov identities for thickened indicators (bounded
Lipschitz test functions) to a Markov kernel and set-wise Chapman-Kolmogorov. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10g

end ItoLib

end FlatM_O
-- ===== P =====
section FlatM_P
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10h
/-! M10h (b9/b11): local Lipschitz on compact sets, coordinate clamps, truncation families,
and the Kolmogorov coefficients. -/

/-- Local Lipschitz on `s` gives a Lipschitz bound on every compact `K ⊆ s`. -/
theorem lipOn_of_locLip_compact {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {s K : Set α} {f : α → β} (hf : LocallyLipschitzOn s f) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, ∀ y ∈ K, dist (f x) (f y) ≤ L * dist x y := by
  classical
  have hloc : ∀ x : K, ∃ r > (0 : ℝ), ∃ L : ℝ≥0, LipschitzOnWith L f (Metric.ball (x : α) r ∩ s) := by
    intro x
    obtain ⟨L, t, ht, hL⟩ := hf (hKs x.2)
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhdsWithin_iff.1 ht
    exact ⟨r, hr, L, hL.mono hrt⟩
  choose r hr L hL using hloc
  have hcov : K ⊆ ⋃ x : K, Metric.ball (x : α) (r x / 2) := fun y hy =>
    Set.mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (half_pos (hr _))⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover _ (fun _ => Metric.isOpen_ball) hcov
  -- bound on `f` over `K`
  have hbdd : Bornology.IsBounded (f '' K) :=
    (hK.image_of_continuousOn (hf.continuousOn.mono hKs)).isBounded
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hbdd
  by_cases hTn : T.Nonempty
  · set δ : ℝ := T.inf' hTn (fun x => r x / 2) with hδ
    have hδpos : 0 < δ := by
      rw [hδ, Finset.lt_inf'_iff]; exact fun x _ => half_pos (hr x)
    set Lm : ℝ≥0 := T.sup L
    refine ⟨Lm + max C 0 / δ, by positivity, fun x hx y hy => ?_⟩
    by_cases hxy : dist x y < δ
    · obtain ⟨z, hzT, hxz⟩ : ∃ z ∈ T, x ∈ Metric.ball (z : α) (r z / 2) := by
        have := hT hx; simp only [Set.mem_iUnion] at this
        obtain ⟨z, hz, h⟩ := this; exact ⟨z, hz, h⟩
      have hδz : δ ≤ r z / 2 := Finset.inf'_le _ hzT
      have hx' : x ∈ Metric.ball (z : α) (r z) ∩ s :=
        ⟨Metric.ball_subset_ball (by linarith [hr z]) hxz, hKs hx⟩
      have hy' : y ∈ Metric.ball (z : α) (r z) ∩ s := by
        refine ⟨?_, hKs hy⟩
        rw [Metric.mem_ball] at hxz ⊢
        calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
          _ < δ + r z / 2 := by rw [dist_comm]; exact add_lt_add hxy hxz
          _ ≤ r z := by linarith
      have h1 := (hL z).dist_le_mul x hx' y hy'
      have h2 : (L z : ℝ) ≤ Lm := by exact_mod_cast Finset.le_sup (f := L) hzT
      have h3 : 0 ≤ max C 0 / δ * dist x y := by positivity
      nlinarith [dist_nonneg (x := x) (y := y)]
    · replace hxy := not_lt.1 hxy
      have h1 : dist (f x) (f y) ≤ max C 0 :=
        (hC ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩).trans (le_max_left _ _)
      have h2 : max C 0 ≤ max C 0 / δ * dist x y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
        exact mul_le_mul_of_nonneg_left hxy (le_max_right _ _)
      have h3 : 0 ≤ (Lm : ℝ) * dist x y := by positivity
      nlinarith
  · have hK0 : K = ∅ := by
      rw [Finset.not_nonempty_iff_eq_empty] at hTn
      subst hTn; simpa using hT
    exact ⟨0, le_rfl, fun x hx => by simp [hK0] at hx⟩

variable {d : ℕ}

/-- Coordinatewise 1-Lipschitz maps are 1-Lipschitz in the Euclidean norm. -/
theorem norm_sub_le_of_coord {x y x' y' : SDEState d} (h : ∀ i, |x' i - y' i| ≤ |x i - y i|) :
    ‖x' - y'‖ ≤ ‖x - y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  simp only [PiLp.sub_apply, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

theorem clamp1_lip (M a b : ℝ) : |max (-M) (min M a) - max (-M) (min M b)| ≤ |a - b| := by
  rw [abs_le]
  have h1 := le_abs_self (a - b); have h2 := neg_abs_le (a - b)
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

/-- Coordinate clamp to the box `[-M, M]^d`. -/
noncomputable def clampM (M : ℝ) (x : SDEState d) : SDEState d :=
  WithLp.toLp 2 (fun i => max (-M) (min M (x i)))

theorem clampM_apply (M : ℝ) (x : SDEState d) (i : Fin d) :
    clampM M x i = max (-M) (min M (x i)) := rfl

theorem clampM_lip (M : ℝ) (x y : SDEState d) : ‖clampM M x - clampM M y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by rw [clampM_apply, clampM_apply]; exact clamp1_lip _ _ _

theorem clampM_abs_le {M : ℝ} (hM : 0 ≤ M) (x : SDEState d) (i : Fin d) : |clampM M x i| ≤ M := by
  rw [clampM_apply, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem clampM_eq {M : ℝ} {x : SDEState d} (hx : ‖x‖ ≤ M) : clampM M x = x := by
  ext i
  rw [clampM_apply]
  have := (coord_abs_le_state x i).trans hx
  rw [abs_le] at this
  rw [min_eq_right this.2, max_eq_right this.1]

theorem norm_le_card_mul {M : ℝ} {x : SDEState d} (hx : ∀ i, |x i| ≤ M) : ‖x‖ ≤ d * M := by
  calc ‖x‖ ≤ ∑ i, |x i| := euc_norm_le_sum' x
    _ ≤ ∑ _i : Fin d, M := Finset.sum_le_sum fun i _ => hx i
    _ = d * M := by simp

/-- b9: a truncation family for coordinate functions that are Lipschitz on every box. -/
theorem trunc_family {ι : Type*} [Fintype ι] (φ : ι → SDEState d → ℝ)
    (hL : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ k x y, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |φ k x - φ k y| ≤ L * ‖x - y‖) :
    ∃ (s₁ : ℕ → SDEState d → EuclideanSpace ℝ ι) (S L : ℕ → ℝ), (∀ R, Continuous (s₁ R)) ∧
      (∀ R, 0 ≤ L R) ∧ (∀ R x, ‖s₁ R x‖ ≤ S R) ∧
      (∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖) ∧
      (∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = WithLp.toLp 2 (fun k => φ k x)) := by
  classical
  choose Lb hLb0 hLb using fun R : ℕ => hL ((R : ℝ) + 3) (by positivity)
  set s₁ : ℕ → SDEState d → EuclideanSpace ℝ ι :=
    fun R x => WithLp.toLp 2 (fun k => φ k (clampM ((R : ℝ) + 3) x)) with hs₁
  have hM : ∀ R : ℕ, (0 : ℝ) ≤ (R : ℝ) + 3 := fun R => by positivity
  have hlip : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ (Fintype.card ι * Lb R) * ‖x - y‖ := by
    intro R x y
    calc ‖s₁ R x - s₁ R y‖ ≤ ∑ k, |(s₁ R x - s₁ R y) k| := euc_norm_le_sum' _
      _ ≤ ∑ _k : ι, Lb R * ‖x - y‖ := by
          apply Finset.sum_le_sum; intro k _
          simp only [hs₁, PiLp.sub_apply]
          exact (hLb R k _ _ (clampM_abs_le (hM R) x) (clampM_abs_le (hM R) y)).trans
            (mul_le_mul_of_nonneg_left (clampM_lip _ _ _) (hLb0 R))
      _ = (Fintype.card ι * Lb R) * ‖x - y‖ := by simp [mul_assoc]
  refine ⟨s₁, fun R => ∑ k : ι, (|φ k (clampM ((R : ℝ) + 3) 0)| + Lb R * (2 * (d * ((R : ℝ) + 3)))),
    fun R => Fintype.card ι * Lb R, fun R => ?_, fun R => by have := hLb0 R; positivity,
    fun R x => ?_, hlip, fun R x hx => ?_⟩
  · exact LipschitzWith.continuous (K := ⟨Fintype.card ι * Lb R, by have := hLb0 R; positivity⟩)
      (LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm]; exact hlip R x y)
  · calc ‖s₁ R x‖ ≤ ∑ k, |s₁ R x k| := euc_norm_le_sum' _
      _ ≤ _ := by
          apply Finset.sum_le_sum; intro k _
          simp only [hs₁]
          set M : ℝ := (R : ℝ) + 3
          have hc := hLb R k _ _ (clampM_abs_le (hM R) x) (clampM_abs_le (hM R) 0)
          have hn : ‖clampM M x - clampM M 0‖ ≤ 2 * (d * M) := by
            calc ‖clampM M x - clampM M 0‖ ≤ ‖clampM M x‖ + ‖clampM M 0‖ := norm_sub_le _ _
              _ ≤ d * M + d * M := add_le_add (norm_le_card_mul (clampM_abs_le (hM R) x))
                  (norm_le_card_mul (clampM_abs_le (hM R) 0))
              _ = 2 * (d * M) := by ring
          have := mul_le_mul_of_nonneg_left hn (hLb0 R)
          have h3 := abs_sub_abs_le_abs_sub (φ k (clampM M x)) (φ k (clampM M 0))
          linarith
  · simp only [hs₁, clampM_eq hx]

end M10h

section M10i
open StochKolmogorov.Persist
variable {n : ℕ}

theorem posPart_apply' (x : SDEState n) (i : Fin n) : posPart x i = max (x i) 0 := rfl

theorem posPart_lip (x y : SDEState n) : ‖posPart x - posPart y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by
    rw [posPart_apply', posPart_apply']; exact abs_max_sub_max_le_abs _ _ _

theorem posPart_mem_orthant (x : SDEState n) : posPart x ∈ orthant n := fun i => by
  rw [posPart_apply']; exact le_max_right _ _

theorem continuous_posPart : Continuous (posPart (n := n)) :=
  LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]; exact posPart_lip x y)

/-- A locally Lipschitz function on the orthant, read at `x⁺`, is Lipschitz and bounded on boxes. -/
theorem locLip_posPart_box {h : SDEState n → ℝ} (hh : LocallyLipschitzOn (orthant n) h)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ L G : ℝ, 0 ≤ L ∧ 0 ≤ G ∧ ∀ x y : SDEState n, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |h (posPart x) - h (posPart y)| ≤ L * ‖x - y‖ ∧ |h (posPart x)| ≤ G := by
  set K : Set (SDEState n) := {y | ∀ i, 0 ≤ y i ∧ y i ≤ M} with hKdef
  have hKc : IsClosed K := by
    have : K = ⋂ i, ({y : SDEState n | 0 ≤ y i} ∩ {y | y i ≤ M}) := by
      ext y; simp [hKdef, forall_and]
    rw [this]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)).inter
      (isClosed_le (PiLp.continuous_apply 2 _ i) continuous_const)
  have hKb : Bornology.IsBounded K := (Metric.isBounded_closedBall (x := (0 : SDEState n))
      (r := n * M)).subset fun y hy => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_card_mul fun i => by rw [abs_of_nonneg (hy i).1]; exact (hy i).2
  have hKo : K ⊆ orthant n := fun y hy i => (hy i).1
  obtain ⟨L, hL0, hL⟩ := lipOn_of_locLip_compact hh (Metric.isCompact_of_isClosed_isBounded hKc hKb) hKo
  have hpK : ∀ x : SDEState n, (∀ i, |x i| ≤ M) → posPart x ∈ K := fun x hx i => by
    rw [posPart_apply']
    exact ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hx i)) hM⟩
  have h0 : ∀ i, |(0 : SDEState n) i| ≤ M := fun i => by simpa using hM
  refine ⟨L, L * (n * M) + |h (posPart 0)|, hL0, by positivity, fun x y hx hy => ⟨?_, ?_⟩⟩
  · have := hL _ (hpK x hx) _ (hpK y hy)
    rw [Real.dist_eq, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_left (posPart_lip x y) hL0)
  · have h1 := hL _ (hpK x hx) _ (hpK 0 h0)
    rw [Real.dist_eq, dist_eq_norm] at h1
    have h2 : ‖posPart x - posPart (0 : SDEState n)‖ ≤ n * M := by
      calc ‖posPart x - posPart (0 : SDEState n)‖ ≤ ‖x - 0‖ := posPart_lip x 0
        _ = ‖x‖ := by rw [sub_zero]
        _ ≤ n * M := norm_le_card_mul hx
    have h3 := abs_sub_abs_le_abs_sub (h (posPart x)) (h (posPart 0))
    have h4 := mul_le_mul_of_nonneg_left h2 hL0
    linarith

/-- Products `x_i · h(x⁺) · c` are Lipschitz on boxes. -/
theorem prod_box_lip {h : SDEState n → ℝ} (hh : LocallyLipschitzOn (orthant n) h) (c : ℝ) (i : Fin n)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : SDEState n, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x i * h (posPart x) * c - y i * h (posPart y) * c| ≤ L * ‖x - y‖ := by
  obtain ⟨L, G, hL0, hG0, hLG⟩ := locLip_posPart_box hh hM
  refine ⟨|c| * (M * L + G), by positivity, fun x y hx hy => ?_⟩
  obtain ⟨h1, -⟩ := hLG x y hx hy
  obtain ⟨-, h2⟩ := hLG y x hy hx
  have hxy : |x i - y i| ≤ ‖x - y‖ := by
    have := coord_abs_le_state (x - y) i; rwa [PiLp.sub_apply] at this
  have e : x i * h (posPart x) * c - y i * h (posPart y) * c =
      c * (x i * (h (posPart x) - h (posPart y)) + h (posPart y) * (x i - y i)) := by ring
  rw [e, abs_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  calc |x i * (h (posPart x) - h (posPart y)) + h (posPart y) * (x i - y i)|
      ≤ |x i| * |h (posPart x) - h (posPart y)| + |h (posPart y)| * |x i - y i| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ M * (L * ‖x - y‖) + G * ‖x - y‖ := by
        gcongr
        · exact hx i
    _ = (M * L + G) * ‖x - y‖ := by ring

/-- b11: the Kolmogorov coefficients are continuous and allow truncation families as needed by
`markov_core`. -/
theorem kolm_trunc (C : Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    Continuous (fun x : SDEState n => diffusion C (0, x)) ∧
    Continuous (fun x : SDEState n => drift C (0, x)) ∧
    ∃ (s₁ : ℕ → SDEState n → SDEDiffusion n) (b₁ : ℕ → SDEState n → SDEState n) (S L : ℕ → ℝ),
      (∀ R, Continuous (s₁ R)) ∧ (∀ R, Continuous (b₁ R)) ∧ (∀ R, 0 ≤ L R) ∧
      (∀ R x, ‖s₁ R x‖ ≤ S R ∧ ‖b₁ R x‖ ≤ S R) ∧
      (∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L R * ‖x - y‖) ∧
      (∀ (R : ℕ) (x : SDEState n), ‖x‖ ≤ (R : ℝ) + 3 →
        s₁ R x = diffusion C (0, x) ∧ b₁ R x = drift C (0, x)) := by
  have hgc : ∀ i, Continuous fun x : SDEState n => C.g i (posPart x) := fun i =>
    (hC i).2.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hfc : ∀ i, Continuous fun x : SDEState n => C.f i (posPart x) := fun i =>
    (hC i).1.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  refine ⟨(PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      (((PiLp.continuous_apply 2 _ k.1).mul (hgc k.1)).mul continuous_const)),
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      ((PiLp.continuous_apply 2 _ k).mul (hfc k))), ?_⟩
  -- the two coordinate families
  have hLs : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ (k : Fin n × Fin n) (x y : SDEState n),
      (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x k.1 * C.g k.1 (posPart x) * C.Γ k.2 k.1 - y k.1 * C.g k.1 (posPart y) * C.Γ k.2 k.1|
        ≤ L * ‖x - y‖ := by
    intro M hM
    choose L hL0 hL using fun k : Fin n × Fin n => prod_box_lip (hC k.1).2 (C.Γ k.2 k.1) k.1 hM
    refine ⟨∑ k, L k, Finset.sum_nonneg fun k _ => hL0 k, fun k x y hx hy => ?_⟩
    exact (hL k x y hx hy).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hL0 k) (Finset.mem_univ k)) (norm_nonneg _))
  have hLb : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ (k : Fin n) (x y : SDEState n),
      (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x k * C.f k (posPart x) * 1 - y k * C.f k (posPart y) * 1| ≤ L * ‖x - y‖ := by
    intro M hM
    choose L hL0 hL using fun k : Fin n => prod_box_lip (hC k).1 1 k hM
    refine ⟨∑ k, L k, Finset.sum_nonneg fun k _ => hL0 k, fun k x y hx hy => ?_⟩
    exact (hL k x y hx hy).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hL0 k) (Finset.mem_univ k)) (norm_nonneg _))
  obtain ⟨s₁, S1, L1, hs1c, hL1, hS1, hl1, he1⟩ := trunc_family _ hLs
  obtain ⟨b₁, S2, L2, hb1c, hL2, hS2, hl2, he2⟩ := trunc_family _ hLb
  refine ⟨s₁, b₁, fun R => max (S1 R) (S2 R), fun R => max (L1 R) (L2 R), hs1c, hb1c,
    fun R => (hL1 R).trans (le_max_left _ _), fun R x => ⟨(hS1 R x).trans (le_max_left _ _),
      (hS2 R x).trans (le_max_right _ _)⟩, fun R x y => ⟨(hl1 R x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)), (hl2 R x y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩, fun R x hx => ⟨?_, ?_⟩⟩
  · rw [he1 R x hx]; rfl
  · rw [he2 R x hx]; simp only [mul_one]; rfl

end M10i

section M10j
open StochKolmogorov.Persist
variable {n : ℕ}

theorem orthant_isClosed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {y : SDEState n | 0 ≤ y i} := by ext y; simp [orthant]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

end M10j

end ItoLib

end FlatM_P
-- ===== CM =====
section FlatM_CM
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5dK
/-! CORE route C5d, Kolmogorov instance (s26): the coefficients read through the box clamp
`boxP α β` (box `[α, β]^n` inside the open orthant) are globally Lipschitz and bounded, have the
form `s x (i, j) = aK i x * Γ j i`, and `|aK i x + aK i y| ≥ κ > 0` (Assumption 1.1 part 1). -/

variable {n : ℕ}

open StochKolmogorov.Persist

end C5dK
end ItoLib

end FlatM_CM
-- ===== CN =====
section FlatM_CN
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5g
/-! CORE route, s27: (1) `Γ` is invertible under Assumption 1.1 part 1; (2) a generic discrete
martingale `gmart` built from bounded past-measurable cell coefficients: measurability, second
moment, orthogonality and the Kolmogorov maximal inequality (used for the tracking estimate of
the steered chain). -/

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0} {A B : ℕ → Ω → SDEDiffusion d}

end C5g
end ItoLib

end FlatM_CN
-- ===== QA =====
section FlatM_QA
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QA
/-! lemma_3_1 (aaf23e78) toolkit, part QA: continuous versions of Ito integrals.
Dyadic grid `gpt m l = l / 2^m`, the horizon-free step integral `stepM` (mesh `2^{-q}` on
`[0,q]`), its values at finer grid points, and a continuous-time maximal inequality for
differences of step integrals (via `gmart_max`). -/

noncomputable def hm (m : ℕ) : ℝ≥0 := 1 / 2 ^ m

end QA
end ItoLib

end FlatM_QA
-- ===== QB =====
section FlatM_QB
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QB
/-! lemma_3_1 toolkit, part QB: uniform `L²`-continuity of a bounded continuous integrand, and
the pathwise identification of `stepM q t` as the limit of `t`-grid Riemann sums whose
coefficients are the level-`q` left values (grid comparison, step 1). -/

end QB
end ItoLib

end FlatM_QB
-- ===== QC =====
section FlatM_QC
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QC
/-! lemma_3_1 toolkit, part QC: grid comparison in `L²` and `stepM q t → J t` in probability
for every fixed `t` (bounded continuous adapted integrand). -/

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

end QC
end ItoLib

end FlatM_QC
-- ===== QD =====
section FlatM_QD
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QDan
/-! Pure analysis: a sequence of continuous functions with geometrically small successive
differences on growing intervals converges pointwise to a continuous limit. -/

end QDan

section QD

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

end QD

end ItoLib

end FlatM_QD
-- ===== Q =====
section FlatM_Q
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10k
/-! M10k (b10 calculus): the cubic negative part `φ(v) = (v⁻)³` (C², `v φ' = 3φ`, `v² φ'' = 6φ`)
and the orthant test function `Hf r u = e^{-a} χ_r(|x|²) Σ_k φ(x_k)`. -/

variable {d : ℕ}

end M10k

section M10l
/-! M10l (b10 drift): generator of `Hf r` inside the ball and its global bound. -/
variable {d : ℕ}

end M10l

section M10m
/-! M10m (b10 expectation): `E Hf_r(X_t) ≤ Hf_r(x₀) + B/M` along `(X, X, A)`. -/
variable {Ω : Type*} {d : ℕ}

end M10m

end ItoLib

end FlatM_Q
-- ===== R =====
section FlatM_R
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10n
/-! M10n (b10 expectation and Markov step): `E Hf_r(X_t, A_t) ≤ Hf_r(x₀) + B/M`, and
`P{X stays in B̄_R on [0,t], ε < Φ(X_t)} ≤ (Hf_r(x₀) + B/M) / (e^{-ct} ε)`. -/
variable {Ω : Type*} {d : ℕ}

end M10n

end ItoLib

end FlatM_R
-- ===== S =====
section FlatM_S
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10o
/-! M10o (b10 done): orthant invariance of the Kolmogorov solutions, and the Markov statement. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M10o

end ItoLib

end FlatM_S
-- ===== U =====
section FlatM_U
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M11a
/-! M11a (lemma_3_1 clause 2): pathwise uniqueness for all times at once, and for the Kolmogorov
system. -/

theorem denseRange_rat_toNNReal : DenseRange fun q : ℚ => (q : ℝ).toNNReal := by
  have hs : DenseRange Real.toNNReal := Function.Surjective.denseRange fun x =>
    ⟨(x : ℝ), Real.toNNReal_coe⟩
  exact hs.comp Rat.denseRange_cast continuous_real_toNNReal

open StochKolmogorov.Persist

end M11a

section M11b
/-! M11b (lemma_3_1 clause 4a): `H < ∞`, i.e. `bracket35` is bounded above on the orthant. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M11b

end ItoLib

end FlatM_U
-- ===== QE =====
section FlatM_QE
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QEneg
variable {Ω : Type*} [MeasurableSpace Ω]

end QEneg

section QEF

end QEF

section QEface
open StochKolmogorov.Persist
variable {n : ℕ}

end QEface

end ItoLib

end FlatM_QE
-- ===== QF =====
section FlatM_QF
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QFgen
/-! Generic test function `F(x,y,a) = e^{-a} G(y)` along `(X, Y, A)`. -/
variable {d : ℕ}

end QFgen

section QFsat
/-! The concave saturation `h_m(u) = ∫₀ᵘ (1 - st(s - m)) ds`. -/

end QFsat

section QFell
/-! The logarithm `ℓ = log(1 + cᵀy) - Σ pᵢ log yᵢ` of `V`, its line derivatives, and bounds. -/
variable {n : ℕ}
open StochKolmogorov.Persist

end QFell

section QFalg
variable {n : ℕ}
open StochKolmogorov.Persist

end QFalg

section QFgenL
variable {n : ℕ}
open StochKolmogorov.Persist

end QFgenL

end ItoLib

end FlatM_QF
-- ===== QG =====
section FlatM_QG
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
open StochKolmogorov.Persist

section QG
/-! Clause 4b (3.6) of Lemma 3.1: `E V^δ₀(X_t) ≤ e^{δ₀ H t} V^δ₀(x)`. -/
variable {n : ℕ}

end QG

end ItoLib

end FlatM_QG
-- ===== QH =====
section FlatM_QH
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QH
/-! Clause 1 toolkit (E1): the Ito isometry as an upper bound, `E J_t² ≤ E ∫₀ᵗ H²`. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QH

end ItoLib

end FlatM_QH
-- ===== QI =====
section FlatM_QI
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QI
/-! Clause 1 toolkit (E3): weak maximal inequality for continuous versions of Ito integrals. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QI
end ItoLib

end FlatM_QI
-- ===== HK =====
section FlatM_HK
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section HK
/-! 7ade6a3f K3ito toolkit: uniform-in-time convergence in probability of the step integrals
`stepM` to a continuous version of the Ito integral, first for bounded, then (by localisation)
for unbounded continuous adapted integrands. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end HK
end ItoLib

end FlatM_HK
-- ===== Doob =====
section FlatM_Doob
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section Doob
/-! 73c0fc13 step D1: Doob's L² maximal inequality for continuous versions of Itô integrals of
bounded continuous adapted integrands, with the integrated second moment `E ∫₀ᴺ G²`. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end Doob
end ItoLib

end FlatM_Doob
-- ===== Doob2 =====
section FlatM_Doob2
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section Doob2
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end Doob2
end ItoLib

end FlatM_Doob2
-- ===== GateH =====
section FlatM_GateH
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

/-! 73c0fc13 step D2: gated Doob maximal inequality for Itô integrals of unbounded continuous
adapted integrands (helpers copied from 8f909832_hl/C3.lean). -/

end ItoLib.G73

end FlatM_GateH
-- ===== Gate =====
section FlatM_Gate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

section Gate
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end Gate
end ItoLib.G73

end FlatM_Gate
-- ===== Slln =====
section FlatM_Slln
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

section Slln
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end Slln
end ItoLib.G73

end FlatM_Slln
-- ===== GateSum =====
section FlatM_GateSum
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

/-! GateSum (a17b7893 s2): gated maximal inequality over DYADIC times for an Itô integral with no
continuity assumption (`gated_max_dy`, from ItoLib.G73.gated_max), its version for a continuous
modification `Y` of a finite sum of Itô integrals (`gated_max_Y`), and the continuous-time
martingale strong law under a pathwise linear bound on the quadratic variation (`slln_Y`). -/

namespace ItoLib.G73
open EthierKurtz ItoLib

section GateSum
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end GateSum
end ItoLib.G73

end FlatM_GateSum
-- ===== HLL =====
section FlatM_HLL

/-! Child `StochKolmogorov.Classify.log_lln_squares` (Hening-Nguyen arXiv:1704.06984v1, proof of Lemma 5.4 /
Theorem 5.2, p. 28): strong law of large numbers for `ln Xᵢ` along the times `m²`. Proof: Itô's formula for
`ln Xₖ` (smoothly floored), localized and de-localized by path continuity; gated L² bound for the martingale
part; Borel–Cantelli along `m²`. Uses the Proved platform theorems
`EthierKurtz.brownian_ito_integral_and_formula` and `EthierKurtz.brownian_ito_integral_locality_and_continuity`. -/

set_option autoImplicit false


section Part0
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace StochKolmogorov.Classify.HL

open StochKolmogorov.Classify EthierKurtz

end StochKolmogorov.Classify.HL

end Part0


section Part1
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.HL

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma continuous_posPart : Continuous (posPart (n := n)) := by
  unfold posPart
  first
  | fun_prop
  | exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun i => ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).max
        continuous_const)

end StochKolmogorov.Classify.HL

end Part1
section Part4
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.HL

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

end StochKolmogorov.Classify.HL

end Part4

end FlatM_HLL
-- ===== V =====
section FlatM_V
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M11c
/-! M11c: the orthant test-function machinery of Q.lean/R.lean with a general family of C²
nonnegative coordinate functions `φ k` in place of `(v⁻)³`. -/

variable {Ω : Type*} {d : ℕ}

variable {φ : Fin d → ℝ → ℝ} [hφ : Fact (∀ k, ContDiff ℝ 2 (φ k))]
  [hφ0 : Fact (∀ k v, 0 ≤ φ k v)]

end M11c

end ItoLib

end FlatM_V
-- ===== W =====
section FlatM_W
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M11d
/-! M11d (lemma_3_1 clause 3, interior part): a solution started with `x_k > 0` has `X_t k ≠ 0`
almost surely at every fixed time. Test function `φ_δ(v) = 1/(v² + δ)`, with
`|φ_δ'(v) v| ≤ 2 φ_δ(v)` and `φ_δ''(v) v² ≤ 8 φ_δ(v)`. -/
open StochKolmogorov.Persist

variable {δ : ℝ}

variable {n : ℕ}

/-- `orthant_inv` for one solution (no solution family needed). -/
theorem orthant_inv1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (hx₀ : x₀ ∈ orthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Y t ω ∈ orthant n := by
  exact StochKolmogorov.Persist.orthant_invariance_closed P C B hB hC hx₀ hY t

end M11d

end ItoLib

end FlatM_W
-- ===== Y =====
section FlatM_Y
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12a
/-! M12a: the test-function machinery of V.lean for a single C² nonnegative function `ψ` of a
linear form `ℓ(x) = Σ_k cv_k x_k`, `Φ(x) = ψ(ℓ x)` (used with `ψ ≈ log(1+·)`). -/

variable {Ω : Type*} {d : ℕ}

variable {ψ : ℝ → ℝ} {cv : SDEState d} [hψ : Fact (ContDiff ℝ 2 ψ)] [hψ0 : Fact (∀ v, 0 ≤ ψ v)]

end M12a


section M12b
/-! M12b: the Lyapunov function `log(1 + cᵀx)` for (1.1): `E ∫₀ᵗ w(X_u) du ≤ log(1 + cᵀx) + log 2 + K t`
with `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)` and `K = max H 0` (`H` of (3.5)). -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- A solution from `x₀ ∈ ℝⁿ₊` stays in `ℝⁿ₊` at all times, a.s. -/
theorem orthant_inv_all {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (hx₀ : x₀ ∈ orthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) :
    ∀ᵐ ω ∂P, ∀ u, Y u ω ∈ orthant n := by
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, Y ((q : ℝ).toNNReal) ω ∈ orthant n :=
    ae_all_iff.2 fun q => orthant_inv1 P C B hB hC hx₀ hY _
  filter_upwards [hq] with ω hω u
  have hcl : IsClosed {s : ℝ≥0 | Y s ω ∈ orthant n} := orthant_isClosed.preimage (hY.2.1 ω)
  have hsub : Set.range (fun q : ℚ => (q : ℝ).toNNReal) ⊆ {s : ℝ≥0 | Y s ω ∈ orthant n} := by
    rintro _ ⟨q, rfl⟩; exact hω q
  have := hcl.closure_subset_iff.2 hsub
  rw [denseRange_rat_toNNReal.closure_range] at this
  exact this (Set.mem_univ u)

end M12b

end ItoLib

end FlatM_Y
-- ===== Z =====
section FlatM_Z
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12c
/-! M12c: invariant measures integrate the weight `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)`:
`∫ w dμ ≤ max H 0`, hence the Lyapunov integrands `fᵢ − σᵢᵢ gᵢ²/2` are `μ`-integrable. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M12c

end ItoLib

end FlatM_Z
-- ===== L33 =====
section FlatM_L33
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section L33
/-! L33 (lemma_3_2/3_3/3_4 work, s1 2026-10-30): generic Lyapunov bounds for the Kolmogorov family. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end L33

end ItoLib


end FlatM_L33
-- ===== L32 =====
section FlatM_L32
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section L32
/-! L32 (lemma_3_2 work, 15eaca53 s2 2026-10-30): the power Lyapunov function `(1 + cᵀx)^δ`. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end L32

section L32T
/-! Dynkin bound keeping the terminal term (for (3.7)). -/
variable {Ω : Type*} {d : ℕ}
variable {ψ : ℝ → ℝ} {cv : SDEState d} [hψ : Fact (ContDiff ℝ 2 ψ)] [hψ0 : Fact (∀ v, 0 ≤ ψ v)]

end L32T

section L32U
open StochKolmogorov.Persist
variable {n : ℕ}

end L32U

section L32V
open StochKolmogorov.Persist
variable {n : ℕ}

end L32V

section L32G

end L32G

end ItoLib

end FlatM_L32
-- ===== Part2 =====
section FlatM_Part2
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib.G73
open EthierKurtz ItoLib

section Part2
variable {n : ℕ}

/-- The Persist copy of Classify coefficients (the two structures are identical). -/
def toP (C : StochKolmogorov.Classify.Coeffs n) : StochKolmogorov.Persist.Coeffs n :=
  ⟨C.f, C.g, C.Γ⟩

open StochKolmogorov.Classify

end Part2
end ItoLib.G73

end FlatM_Part2
-- ===== X41 =====
section FlatM_X41
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! X41 (eq_4_1, finite-`M` part): the minimax step of [SBA11, Lemma 4] for finitely many
boundary ergodic measures, by strict separation of a polytope from the closed negative orthant. -/

open StochKolmogorov.Persist EthierKurtz in
/-- `δ₀` of (3.2) exists: `δ₀ = γ_b / (3 S n + 3)` with `S = ∑ᵢⱼ |σᵢⱼ|`. -/
theorem exists_isDelta0 {n : ℕ} (C : Coeffs n) (γb : ℝ) (hγ : 0 < γb) :
    ∃ δ₀ : ℝ, IsDelta0 C γb δ₀ := by
  set S : ℝ := ∑ i, ∑ j, |C.sig i j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsij : ∀ i j, |C.sig i j| ≤ S := by
    intro i j
    calc |C.sig i j| ≤ ∑ j', |C.sig i j'| :=
          Finset.single_le_sum (f := fun j' => |C.sig i j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ j', |C.sig i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hden : 0 < 3 * S * n + 3 := by positivity
  refine ⟨γb / (3 * S * n + 3), div_pos hγ hden, ?_, fun x _ => ?_⟩
  · rw [div_lt_div_iff₀ hden two_pos]
    nlinarith [mul_nonneg hS0 (Nat.cast_nonneg (α := ℝ) n)]
  · set δ := γb / (3 * S * n + 3) with hδ
    have hδ0 : 0 ≤ δ := (div_pos hγ hden).le
    set G : ℝ := ∑ i, C.g i x ^ 2 with hG
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hterm : ∀ i j, |C.g i x * C.g j x * C.sig i j|
        ≤ S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by
      intro i j
      rw [abs_mul, abs_mul]
      have h1 : |C.g i x| * |C.g j x| ≤ (C.g i x ^ 2 + C.g j x ^ 2) / 2 := by
        nlinarith [sq_nonneg (|C.g i x| - |C.g j x|), sq_abs (C.g i x), sq_abs (C.g j x)]
      calc |C.g i x| * |C.g j x| * |C.sig i j| ≤ ((C.g i x ^ 2 + C.g j x ^ 2) / 2) * S :=
            mul_le_mul h1 (hsij i j) (abs_nonneg _) (by positivity)
        _ = S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by ring
    have hsum : ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| ≤ S * n * G := by
      calc ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|
          ≤ ∑ i : Fin n, ∑ j : Fin n, S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
        _ = S * n * G := by
            simp only [← Finset.mul_sum, add_div, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hG, ← Finset.sum_div]
            ring
    have hkey : δ * (3 * S * n + 3) = γb := by rw [hδ, div_mul_cancel₀ _ hden.ne']
    calc 3 * δ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| + δ * G
        ≤ 3 * δ * (S * n * G) + δ * G := by nlinarith
      _ ≤ δ * (3 * S * n + 3) * G := by nlinarith [mul_nonneg hδ0 hG0]
      _ = γb * G := by rw [hkey]

end ItoLib

end FlatM_X41
-- ===== T1b =====
section FlatM_T1b

/-! T1b `short_time_positivity` (a17b7893 s3): Hening-Nguyen 1704.06984 (5.15)/(5.19) at any radius.
For `x ∈ ℝⁿ₊` with `‖x‖₁ ≤ R` and `xᵢ > ε₂`, `P(Xᵢ(t) > β ∀ t ≤ T) > 1 - ε₁`, uniformly.
Proof: Itô for `ln Xᵢ` at dyadic times (`HL.log_ito`), Markov on the expected Lyapunov integral
(`clause38` = Persist.lemma_3_2 (3.8)) gating both `∫|hᵢ|` and `∫gᵢ²`, the gated dyadic maximal
inequality (`ItoLib.G73.gated_max_dy`), and a first-drop argument along dyadic times. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace StochKolmogorov.Classify.STP
open StochKolmogorov.Classify EthierKurtz ItoLib

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
/-- T1b (paper (5.15)/(5.19)): short-time positivity of a coordinate, uniformly on `‖x‖₁ ≤ R`. -/
theorem short_time_positivity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    ∀ R T : ℝ, 0 < T → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → ∃ β : ℝ, 0 < β ∧
      ∀ i, ∀ x ∈ orthant n, l1 x ≤ R → ε₂ < x i →
        1 - ε₁ < (P {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T → β < X x t ω i}).toReal := by
  exact StochKolmogorov.Classify.short_time_positivity P C B X hX c γb hA

end StochKolmogorov.Classify.STP

end FlatM_T1b
-- ===== T1full =====
section FlatM_T1full

/-! T1 `sink_box_avoids_far_set` (a17b7893 s4) assembled: `SB.sink_box` over T1a
(`GE.grid_escape_bound`), T1b (`STP.short_time_positivity`) and orthant invariance. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace StochKolmogorov.Classify.SBF
open StochKolmogorov.Classify EthierKurtz ItoLib

variable {n : ℕ}

theorem sink_box_avoids_far_set {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ R η : ℝ, 0 < η →
      ∃ Δ : ℝ, 0 < Δ ∧ ∀ x ∈ Kbox μ k Δ, 1 - ε < (P {ω | ∀ t : ℝ≥0,
        ¬ (l1 (X x t ω) < R ∧ ∃ i, i ∉ supp μ ∧ η < X x t ω i)}).toReal := by
  haveI : IsProbabilityMeasure P := hX.1
  have hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n := fun x hx s =>
    (ItoLib.orthant_inv_all P (G73.toP C) B hX.2.1 hA.2.1 hx (hX.2.2 x hx)).mono fun ω h => h s
  exact SB.sink_box P C B X hX hA.2.1 hinv (GE.grid_escape_bound P C B X hX c γb hA)
    (STP.short_time_positivity P C B X hX c γb hA)

end StochKolmogorov.Classify.SBF

end FlatM_T1full
-- ===== LogCont =====
section FlatM_LogCont

/-! NEW child `log_lln_continuous` (a17b7893 s2): the continuous-time strong law for `ln Xᵢ`
(Hening-Nguyen 1704.06984, (5.35) / proof of Lemma 5.9 p. 27, and (5.23) with Itô's formula).
`Yₖ(t) = ln Xₖ(t) − ln xₖ − ∫₀ᵗ hₖ(X)` is a continuous modification of `∑ⱼ ∫ gₖ(X)Γⱼₖ dBⱼ`
(`HL.log_rep`); the martingale strong law `ItoLib.G73.slln_Y` gives `Yₖ(t)/t → 0`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.LC

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

end StochKolmogorov.Classify.LC

end FlatM_LogCont
-- ===== K1a =====
section FlatM_K1a

/-! K1a of theorem_1_3 (8f909832): an ergodic invariant measure is concentrated on the interior of its
own face. Pure measure theory from face invariance (Extinct.lemma_3_1 clause 2 / Persist
kolmogorov_sde_face_invariance): open faces `F I` partition the orthant and are forward invariant, so
`μ|F I` (normalised) is invariant; extremality forces `μ (F I) ∈ {0,1}`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.K1a

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ}

/-- The open face whose positive coordinates are exactly `I`. -/
def F (I : Finset (Fin n)) : Set (SDEState n) := {x | x ∈ orthant n ∧ ∀ i, i ∈ I ↔ 0 < x i}

variable {Ω : Type*} [MeasurableSpace Ω]

end StochKolmogorov.Classify.K1a

end FlatM_K1a
-- ===== ErgSing =====
section FlatM_ErgSing

/-! Uniqueness core for K1b / K2b of theorem_1_3 (8f909832), pure measure theory:
* `dichotomy`: two ergodic invariant measures are equal or mutually singular (Hahn decomposition;
  `(μ-ν)⁺` is super-invariant, hence invariant, hence a multiple of `μ` by extremality). No
  measurability of `x ↦ trans t x A` is used (only superadditivity of the lower integral).
* `eq_of_overlap`: two ergodic measures charging a common set `K` on which the transition laws
  overlap (`ε ≤ P_t(x,A) + P_t(y,Aᶜ)`) are equal. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.ErgSing

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

end StochKolmogorov.Classify.ErgSing

end FlatM_ErgSing
-- ===== K1 =====
section FlatM_K1

/-! K1 of theorem_1_3 (8f909832): `M` is finite, modulo the analytic child `FaceOverlap` (TV overlap of
the transition laws on compact boxes inside each open face). K1b: two ergodic measures with the same
support are equal (both live on the same open face by K1a; they charge a common face box; overlap). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.K1

open StochKolmogorov.Classify EthierKurtz StochKolmogorov.Classify.K1a
  StochKolmogorov.Classify.ErgSing

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

end StochKolmogorov.Classify.K1

end FlatM_K1
-- ===== KinvConv =====
section FlatM_KinvConv

/-! K2b of theorem_1_3 (8f909832): an invariant probability measure with no mass on the open orthant
lies in `Conv(M)` (finite convex combination of boundary ergodic measures). Per open face `F I`
(`I ≠ univ`): two invariant probabilities living on `F I` are equal (Hahn split into singular
invariant parts + TV overlap on a face box), so the normalized restriction of `π` to `F I` is ergodic. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.KinvConv

open StochKolmogorov.Classify EthierKurtz StochKolmogorov.Classify.K1a
  StochKolmogorov.Classify.ErgSing StochKolmogorov.Classify.K1

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

end StochKolmogorov.Classify.KinvConv

end FlatM_KinvConv
-- ===== T2 =====
section FlatM_T2

/-! T2 of lemma_5_9 (a17b7893): there are `R` and `η > 0` such that every invariant probability `π`
with no mass on the open far set `O(R,η) = {y | l1 y < R ∧ ∃ i ∉ supp μ, η < y i}` lies in
`Conv(M_μ ∪ {μ})`. Per open face `F I` with `I ⊄ supp μ` the invariant probability living on `F I`
(unique by the TV overlap) charges some `O(R_I, η_I)`; take `R = ∑ |R_I|`, `η = (∑ η_I⁻¹)⁻¹`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.L59

open StochKolmogorov.Classify EthierKurtz StochKolmogorov.Classify.K1a
  StochKolmogorov.Classify.ErgSing StochKolmogorov.Classify.K1 StochKolmogorov.Classify.KinvConv

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

end StochKolmogorov.Classify.L59

end FlatM_T2
-- ===== Glue =====
section FlatM_Glue

/-! Glue of lemma_5_9 (a17b7893): the conclusion from lemma_5_7 (invariance of limit points),
lemma_5_8, the new child T1 (the path started in `K^{k,Δ}_μ` avoids the open far set with
probability `> 1 - ε`), the new child T3 (on `U(ω) = {μ}` the log rates are `λᵢ(μ)`) and T2. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.L59

open StochKolmogorov.Classify EthierKurtz StochKolmogorov.Classify.K1a
  StochKolmogorov.Classify.ErgSing StochKolmogorov.Classify.K1

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

end StochKolmogorov.Classify.L59

end FlatM_Glue
-- ===== UcGlue =====
section FlatM_UcGlue

/-! U-c of 8f909832 (paper p.28, "similar to Lemma 5.8"): a.s. no limit point of the occupation
measures lies in `Conv(M²)`. Formal Assumption 1.5 is pointwise (`∃ i, λᵢ(ν) > 0` on `Conv(M²)`),
so no minimax is needed: it suffices that `λᵢ(π) ≤ 0` for every `π ∈ U(ω)` and every `i`.
`lyap_nonpos` derives that from Lemma 5.6 (sibling), Lemma 5.4 clause 1 (sibling), Lemma 5.7
clause 2 (sibling) and two pathwise facts along INTEGER times (hB) and SQUARES (hL):
 hL: `ln Xᵢ(m²)/m² − ∫ hᵢ dΠ̃_{m²} → 0` (Itô for ln Xᵢ + L² martingale bound + Borel–Cantelli), and
 hB: `ln Xᵢ(N) ≤ εN` eventually (moment bound + Borel–Cantelli).
The limit sequence `t_k` is replaced by `⌊√t_k⌋²` (`occ_close`, `tendsto_sq`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.UcGlue

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

end StochKolmogorov.Classify.UcGlue

end FlatM_UcGlue
-- ===== Dfam =====
section FlatM_Dfam

/-! K2-Γ (8f909832): a countable convergence-determining family `hD s k` of bounded continuous
functions on a separable metric space: tents `min 1 ((k+1) · infDist x (U s)ᶜ)` on finite unions
`U s` of balls from a countable basis. If `∫ hD s k dμᵢ → ∫ hD s k dμ` for every `s, k`, then
`μᵢ → μ` weakly (portmanteau, liminf over open sets). -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StochKolmogorov.Classify.Dfam

variable {E : Type*} [MetricSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]

/-- countable family of balls: centre from a dense sequence, radius `1/(m+1)`. -/
noncomputable def ball' (j : ℕ) : Set E :=
  Metric.ball (TopologicalSpace.denseSeq E (Nat.unpair j).1) (1 / (((Nat.unpair j).2 : ℝ) + 1))

/-- finite unions of basic balls. -/
noncomputable def U (s : Finset ℕ) : Set E := ⋃ j ∈ s, ball' j

/-- the tent function. -/
noncomputable def tent (s : Finset ℕ) (k : ℕ) (x : E) : ℝ :=
  min 1 (((k : ℝ) + 1) * Metric.infDist x (U s)ᶜ)

theorem continuous_tent (s : Finset ℕ) (k : ℕ) : Continuous (tent (E := E) s k) :=
  continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt _))

theorem tent_nonneg (s : Finset ℕ) (k : ℕ) (x : E) : 0 ≤ tent s k x :=
  le_min zero_le_one (mul_nonneg (by positivity) Metric.infDist_nonneg)

theorem tent_le_one (s : Finset ℕ) (k : ℕ) (x : E) : tent s k x ≤ 1 := min_le_left _ _

theorem norm_tent_le (s : Finset ℕ) (k : ℕ) (x : E) : ‖tent s k x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg s k x)]; exact tent_le_one s k x

/-- the tent as a bounded continuous function. -/
noncomputable def hD (s : Finset ℕ) (k : ℕ) : E →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (tent s k) (continuous_tent s k) 1
    (norm_tent_le s k)

variable [MeasurableSpace E] [BorelSpace E]

end StochKolmogorov.Classify.Dfam

end FlatM_Dfam
-- ===== LimOcc =====
section FlatM_LimOcc

/-! K2-Γ (8f909832): occupation measures of a continuous path.
* `limitSet_eq_of_avg`: if the `Dfam.hD` averages of `occ X x T ω` converge to those of a probability
  measure `μ`, then `limitSet X x ω = {μ}` (portmanteau through the countable family).
* `avg_of_limitSet`: if `limitSet X x ω = {μ}` and `{occ X x t ω, t ≥ 1}` is tight (Lemma 5.7), then
  `∫ h d(occ X x T ω) → ∫ h dμ` for every bounded continuous `h` (Prokhorov). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.LimOcc

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

end StochKolmogorov.Classify.LimOcc

end FlatM_LimOcc
-- ===== HLglue =====
section FlatM_HLglue

/-! s13: parent-side glue for `hL`. The NEW child `log_lln_squares` (statement `LogLLNSq` below:
linear growth of `∫₀ᵗ gᵢ²` ⇒ `ln Xᵢ(m²)/m² − (1/m²)∫₀^{m²} hᵢ(X) → 0` a.s.) gives `hL` of
`UcGlue.lyap_nonpos` once `∫₀ᵗ gᵢ²` is bounded by lemma 5.4 clause 1 and the time average is
rewritten as an occupation integral. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.HLglue

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

end StochKolmogorov.Classify.HLglue

end FlatM_HLglue
-- ===== T3glue =====
section FlatM_T3glue

/-! T3 of lemma_5_9 (a17b7893): `ln Xᵢ(t)/t → λᵢ(μ)` (continuous time) on `{U(ω) = {μ}}`, from
* `LogLLNCont` (the NEW child `log_lln_continuous`: continuous-time strong law for `ln Xᵢ`,
  `ln Xᵢ(t)/t − t⁻¹∫₀ᵗ hᵢ(X) → 0` a.s. under a linear bound on `∫₀ᵗ gᵢ²`),
* lemma 5.4 cl. 1 (linear growth of `∫ growthWeight`), lemma 5.6 (uniform integrability along
  any sequence with weak convergence), lemma 5.7 (tightness of the occupation measures),
* `LimOcc.avg_of_limitSet` (`U = {μ}` + tight ⇒ `occ_T → μ` weakly, continuous `T`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.L59T3

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

end StochKolmogorov.Classify.L59T3

end FlatM_T3glue


open MeasureTheory ProbabilityTheory Filter EthierKurtz StochKolmogorov.Classify in
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction in
theorem solution {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ R η : ℝ, 0 < η →
      ∃ Δ : ℝ, 0 < Δ ∧ ∀ x ∈ Kbox μ k Δ, 1 - ε < (P {ω | ∀ t : ℝ≥0,
        ¬ (l1 (X x t ω) < R ∧ ∃ i, i ∉ supp μ ∧ η < X x t ω i)}).toReal := by
  exact StochKolmogorov.Classify.SBF.sink_box_avoids_far_set P C B X hX c γb hA

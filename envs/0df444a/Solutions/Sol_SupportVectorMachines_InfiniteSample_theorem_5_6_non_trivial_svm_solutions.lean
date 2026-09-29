-- Prove2me | solution 1 for SupportVectorMachines.InfiniteSample.theorem_5_6_non_trivial_svm_solutions
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:54:01.834899+00:00
-- url     : https://prove2.me/submissions/79dcee30-ead6-40f8-a608-c32bd526901b

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss
import Definitions.Def_SupportVectorMachines_InfiniteSample_NemitskiLoss
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- A two-point space carrying the trivial σ-algebra `{∅, univ}`. -/
def aux_svm56_X : Type := Bool

instance aux_svm56_inst : MeasurableSpace aux_svm56_X := ⊥

/-- On `aux_svm56_X × ℝ` the product σ-algebra only sees the second coordinate. -/
theorem aux_svm56_prod_eq :
    (Prod.instMeasurableSpace : MeasurableSpace (aux_svm56_X × ℝ)) =
      MeasurableSpace.comap Prod.snd Real.measurableSpace := by
  show MeasurableSpace.comap Prod.fst (⊥ : MeasurableSpace aux_svm56_X) ⊔
      MeasurableSpace.comap Prod.snd _ = _
  rw [MeasurableSpace.comap_bot, bot_sup_eq]

/-- A measurable function on `aux_svm56_X × ℝ` does not depend on the first coordinate. -/
theorem aux_svm56_meas_indep {g : aux_svm56_X × ℝ → ENNReal} (hg : Measurable g)
    (x c : aux_svm56_X) (y : ℝ) : g (x, y) = g (c, y) := by
  have hs : MeasurableSet (g ⁻¹' {g (c, y)}) := hg (measurableSet_singleton _)
  rw [aux_svm56_prod_eq] at hs
  obtain ⟨B, _, hB⟩ := hs
  have h1 : (c, y) ∈ Prod.snd ⁻¹' B := by rw [hB]; rfl
  have h2 : (x, y) ∈ g ⁻¹' {g (c, y)} := by rw [← hB]; exact h1
  exact h2

/-- Upper bound for the lower Lebesgue integral of an arbitrary (possibly non-measurable)
function: it is controlled by any single fibre `x = c`. -/
theorem aux_svm56_lintegral_le (P : Measure (aux_svm56_X × ℝ)) (F : aux_svm56_X × ℝ → ENNReal)
    (c : aux_svm56_X) (a : ENNReal) (hF : ∀ y, F (c, y) ≤ a) :
    ∫⁻ p, F p ∂P ≤ a * P Set.univ := by
  obtain ⟨g, hg, hgle, heq⟩ := exists_measurable_le_lintegral_eq P F
  rw [heq, ← lintegral_const]
  apply lintegral_mono
  intro p
  obtain ⟨x, y⟩ := p
  rw [aux_svm56_meas_indep hg x c y]
  exact (hgle (c, y)).trans (hF y)

/-- The loss: constant `1` on the fibre `true`, `|t - 2|` on the fibre `false`. -/
noncomputable def aux_svm56_L : Loss aux_svm56_X :=
  fun x _ t => cond (x : Bool) 1 |t - 2|

/-- Constant functions. -/
def aux_svm56_toFun : ℝ →ₗ[ℝ] (aux_svm56_X → ℝ) where
  toFun f := fun _ => f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem aux_svm56_real_ineq (g : ℝ) : 1 ≤ g ^ 2 + min 1 |g - 2| := by
  rcases le_total 1 |g - 2| with h | h
  · rw [min_eq_left h]; nlinarith [sq_nonneg g]
  · rw [min_eq_right h]
    have h1 : 1 ≤ g := by linarith [(abs_le.mp h).1]
    have h2 : 0 ≤ |g - 2| := abs_nonneg _
    nlinarith

end SupportVectorMachines.InfiniteSample

open SupportVectorMachines.InfiniteSample

theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (hLnn : ∀ x y t, 0 ≤ L x y t)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P] (hNem : PIntegrableNemitskiLoss L P)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∃ M : ℝ, ∀ x : X, k x x ≤ M)
    (hgap : (⨅ f : H, populationRisk L P (toFun f)) < populationRisk L P (fun _ => 0))
    (lam : ℝ) (hlam : 0 < lam) (fPlam : H)
    (hmin : ∀ g : H, ENNReal.ofReal (lam * ‖fPlam‖ ^ 2) + populationRisk L P (toFun fPlam) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g)),
    fPlam ≠ 0) := by
  intro h
  let P : Measure (aux_svm56_X × ℝ) := Measure.dirac ((true, 0) : aux_svm56_X × ℝ)
  have hPuniv : P Set.univ = 1 := measure_univ
  -- convexity
  have hL : ∀ x y, ConvexOn ℝ Set.univ (aux_svm56_L x y) := by
    intro x y
    cases x
    · have h1 : ConvexOn ℝ Set.univ (fun z : ℝ => dist z 2) := convexOn_univ_dist 2
      have e : (fun z : ℝ => dist z 2) = aux_svm56_L false y := by
        funext z; simp [aux_svm56_L, Real.dist_eq]
      rw [e] at h1
      exact h1
    · exact convexOn_const _ convex_univ
  have hLnn : ∀ x y t, 0 ≤ aux_svm56_L x y t := by
    intro x y t
    cases x
    · exact abs_nonneg _
    · exact zero_le_one
  have hNem : PIntegrableNemitskiLoss aux_svm56_L P := by
    refine ⟨fun _ _ => 2, fun s => max s 0, fun _ _ => by norm_num, fun t => le_max_right _ _,
      fun a b hab => max_le_max hab le_rfl, ?_, integrable_const _⟩
    intro x y t
    have h1 : |t| ≤ max |t| 0 := le_max_left _ _
    cases x
    · show |t - 2| ≤ 2 + max |t| 0
      have h2 : |t - 2| ≤ |t| + |(2:ℝ)| := abs_sub _ _
      rw [abs_of_pos (by norm_num : (0:ℝ) < 2)] at h2
      linarith
    · show (1:ℝ) ≤ 2 + max |t| 0
      linarith [abs_nonneg t]
  have hRKHS : IsRKHSOfKernel ℝ aux_svm56_toFun (fun _ _ => 1) := by
    refine ⟨?_, fun _ => (1 : ℝ), fun _ _ => rfl, ?_⟩
    · intro f f' hff
      exact congrFun hff (true : Bool)
    · intro f x
      show f = inner ℝ f (1 : ℝ)
      rw [Real.inner_apply, mul_one]
  have hkBdd : ∃ M : ℝ, ∀ x : aux_svm56_X, (fun _ _ => (1 : ℝ)) x x ≤ M := ⟨1, fun _ => le_rfl⟩
  -- risk of the zero function
  have hR0_ge : 1 ≤ populationRisk aux_svm56_L P (fun _ => 0) := by
    unfold populationRisk
    calc (1 : ENNReal) = ∫⁻ _, (1 : ENNReal) ∂P := by rw [lintegral_const, hPuniv, one_mul]
      _ ≤ _ := by
        apply lintegral_mono
        intro p
        obtain ⟨x, y⟩ := p
        cases x
        · show (1 : ENNReal) ≤ ENNReal.ofReal |0 - 2|
          rw [ENNReal.one_le_ofReal]; norm_num
        · show (1 : ENNReal) ≤ ENNReal.ofReal 1
          simp
  have hR_le_true : ∀ g : ℝ, populationRisk aux_svm56_L P (aux_svm56_toFun g) ≤ 1 := by
    intro g
    unfold populationRisk
    have := aux_svm56_lintegral_le P
      (fun p => ENNReal.ofReal (aux_svm56_L p.1 p.2 (aux_svm56_toFun g p.1)))
      (true : Bool) 1 (fun y => by show ENNReal.ofReal 1 ≤ 1; simp)
    rwa [hPuniv, mul_one] at this
  have hR2 : populationRisk aux_svm56_L P (aux_svm56_toFun 2) ≤ 0 := by
    unfold populationRisk
    have := aux_svm56_lintegral_le P
      (fun p => ENNReal.ofReal (aux_svm56_L p.1 p.2 (aux_svm56_toFun 2 p.1)))
      (false : Bool) 0 (fun y => by show ENNReal.ofReal |2 - 2| ≤ 0; simp)
    rwa [hPuniv, mul_one] at this
  have hgap : (⨅ f : ℝ, populationRisk aux_svm56_L P (aux_svm56_toFun f)) <
      populationRisk aux_svm56_L P (fun _ => 0) := by
    calc (⨅ f : ℝ, populationRisk aux_svm56_L P (aux_svm56_toFun f))
        ≤ populationRisk aux_svm56_L P (aux_svm56_toFun 2) := iInf_le _ 2
      _ ≤ 0 := hR2
      _ < 1 := zero_lt_one
      _ ≤ _ := hR0_ge
  have hR_ge : ∀ g : ℝ, ENNReal.ofReal (min 1 |g - 2|) ≤
      populationRisk aux_svm56_L P (aux_svm56_toFun g) := by
    intro g
    unfold populationRisk
    calc ENNReal.ofReal (min 1 |g - 2|) = ∫⁻ _, ENNReal.ofReal (min 1 |g - 2|) ∂P := by
          rw [lintegral_const, hPuniv, mul_one]
      _ ≤ _ := by
        apply lintegral_mono
        intro p
        obtain ⟨x, y⟩ := p
        apply ENNReal.ofReal_le_ofReal
        cases x
        · exact min_le_right _ _
        · exact min_le_left _ _
  have hmin : ∀ g : ℝ, ENNReal.ofReal (1 * ‖(0 : ℝ)‖ ^ 2) +
      populationRisk aux_svm56_L P (aux_svm56_toFun 0) ≤
      ENNReal.ofReal (1 * ‖g‖ ^ 2) + populationRisk aux_svm56_L P (aux_svm56_toFun g) := by
    intro g
    have hl : ENNReal.ofReal (1 * ‖(0 : ℝ)‖ ^ 2) = 0 := by simp
    rw [hl, zero_add]
    calc populationRisk aux_svm56_L P (aux_svm56_toFun 0) ≤ 1 := hR_le_true 0
      _ ≤ ENNReal.ofReal (1 * ‖g‖ ^ 2 + min 1 |g - 2|) := by
          rw [ENNReal.one_le_ofReal, one_mul, Real.norm_eq_abs, sq_abs]
          exact aux_svm56_real_ineq g
      _ = ENNReal.ofReal (1 * ‖g‖ ^ 2) + ENNReal.ofReal (min 1 |g - 2|) := by
          rw [ENNReal.ofReal_add (by positivity) (le_min zero_le_one (abs_nonneg _))]
      _ ≤ _ := add_le_add le_rfl (hR_ge g)
  exact h aux_svm56_L hL hLnn P hNem ℝ aux_svm56_toFun (fun _ _ => 1) hRKHS hkBdd hgap 1
    one_pos 0 hmin rfl

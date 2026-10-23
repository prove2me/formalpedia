-- Prove2me | solution 1 for RiskFunctionals.Duality.acceptanceSet_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:34:16.871816+00:00
-- url     : https://prove2.me/submissions/66b34960-15fe-4f6f-9402-5e68a72970dd

import Mathlib
import Definitions.Def_RiskFunctionals_Duality_Functionals
open RiskFunctionals.Duality

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (A : Lp ℝ p P → EReal) (hA1 : TranslationEquivariant P A) (hA_ne_top : ∀ Y, A Y ≠ ⊤) :
    (UpperSemicontinuous A → IsClosed (acceptanceSet A)) ∧
    (ConcaveFunctional A → _root_.Convex ℝ (acceptanceSet A)) ∧
    (PointwiseMonotone P A → MonotoneSet P (acceptanceSet A)) ∧
    (PositivelyHomogeneous A → IsConeSet (acceptanceSet A)) ∧
    (Strict A → ∀ Y : Lp ℝ p P, expectation Y < 0 → Y ∉ acceptanceSet A) := by
  refine ⟨fun h => h.isClosed_preimage 0, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · intro x hx y hy a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    have h1 := h x y a ha (by linarith)
    show 0 ≤ A (a • x + (1 - a) • y)
    refine le_trans ?_ h1
    have hx' : (0:EReal) ≤ A x := hx
    have hy' : (0:EReal) ≤ A y := hy
    exact add_nonneg (EReal.mul_nonneg (by exact_mod_cast ha) hx')
      (EReal.mul_nonneg (by exact_mod_cast hb) hy')
  · intro Y₁ Y₂ h1 h12
    exact le_trans h1 (h Y₁ Y₂ h12)
  · intro Y hY lam hl
    show 0 ≤ A (lam • Y)
    rw [h Y lam hl]
    exact EReal.mul_nonneg (by exact_mod_cast hl) hY
  · intro Y hY hmem
    have h1 : (0:EReal) ≤ A Y := hmem
    have h2 := h Y
    have h3 : ((expectation Y : ℝ) : EReal) < 0 := by exact_mod_cast hY
    exact absurd (lt_of_le_of_lt (h1.trans h2) h3) (lt_irrefl _)

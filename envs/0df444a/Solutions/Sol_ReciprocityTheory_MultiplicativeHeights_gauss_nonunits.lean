-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:13:15.959958+00:00
-- url     : https://prove2.me/submissions/57d73489-59b5-4ca9-bad7-fd0f32e852a1

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] (V : ValuationSubring U)
    (w : Ω) : algebraMap Ω U w ∈ V.nonunits ↔ w ∈ (V.comap (algebraMap Ω U)).nonunits := by
  have key : ∀ (A : ValuationSubring U) (x : U), x ∈ A.nonunits ↔ (x = 0 ∨ x⁻¹ ∉ A) := by
    intro A x
    rw [A.mem_nonunits_iff]
    by_cases hx : x = 0
    · simp [hx]
    · have hv : A.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
      simp only [hx, false_or, ← A.valuation_le_one_iff, map_inv₀, not_le]
      constructor
      · intro h; exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hv, h⟩
      · intro h; exact (one_lt_inv_iff₀.mp h).2
  have key' : ∀ (A : ValuationSubring Ω) (x : Ω), x ∈ A.nonunits ↔ (x = 0 ∨ x⁻¹ ∉ A) := by
    intro A x
    rw [A.mem_nonunits_iff]
    by_cases hx : x = 0
    · simp [hx]
    · have hv : A.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
      simp only [hx, false_or, ← A.valuation_le_one_iff, map_inv₀, not_le]
      constructor
      · intro h; exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hv, h⟩
      · intro h; exact (one_lt_inv_iff₀.mp h).2
  rw [key, key', ValuationSubring.mem_comap, map_inv₀]
  simp
end ReciprocityTheory.MultiplicativeHeights

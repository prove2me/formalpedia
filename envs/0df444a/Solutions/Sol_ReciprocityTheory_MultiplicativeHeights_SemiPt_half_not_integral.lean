-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.half_not_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:40:12.983743+00:00
-- url     : https://prove2.me/submissions/9c1aa89b-47a2-4964-9c6a-ad464c936138

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegW
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] : ¬ IsIntegralElt ((2 : K)⁻¹) := by
  rintro ⟨z, hz⟩
  have hint : IsIntegral ℤ ((2 : K)⁻¹) := by
    rw [← hz]
    exact NumberField.RingOfIntegers.isIntegral_coe z
  have e : ((2 : K)⁻¹) = algebraMap ℚ K ((2 : ℚ)⁻¹) := by simp
  rw [e, isIntegral_algebraMap_iff (algebraMap ℚ K).injective] at hint
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hm' : (m : ℚ) = 2⁻¹ := by simpa using hm
  have h2 : ((m * 2 : ℤ) : ℚ) = 1 := by
    push_cast
    rw [hm']
    norm_num
  have h3 : m * 2 = 1 := by exact_mod_cast h2
  omega
end ReciprocityTheory.MultiplicativeHeights.SemiPt

-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_abs_pos_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:23.06833+00:00
-- url     : https://prove2.me/submissions/69ec7a84-01da-45c5-b40f-ead6e14428c1

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_Lemmata_GeneralBFactLeftExtra_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_attained_at_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type*} [Field K] [NumberField K] {σ : Type*}
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (w : FinitePlace K) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    0 < gaussAbs w f := by
  obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
  rw [h]
  exact FinitePlace.pos_iff.2 (MvPolynomial.mem_support_iff.1 hs)
end ReciprocityTheory.MultiplicativeHeights

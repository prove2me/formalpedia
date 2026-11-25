-- Prove2me | solution 1 for ReciprocityTheory.CA.isCM_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:31.734407+00:00
-- url     : https://prove2.me/submissions/fd205c14-ab54-4346-9281-d316a0a3115b

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
universe u
namespace ReciprocityTheory.CA
theorem _root_.solution (K : Type*) [Field K] : IsCM K := by
  refine ⟨inferInstance, 0, by simp [ringKrullDim_eq_zero_of_field], [], rfl, by simp,
    RingTheory.Sequence.IsRegular.nil K K⟩
end ReciprocityTheory.CA

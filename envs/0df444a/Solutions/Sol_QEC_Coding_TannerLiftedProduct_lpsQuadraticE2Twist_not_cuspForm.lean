-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_not_cuspForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:11:06.969029+00:00
-- url     : https://prove2.me/submissions/f4ae13f9-f422-415f-abcb-639a918e57cd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_prime_cusp_not_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    ¬∃ f : CuspForm (CongruenceSubgroup.Gamma0 (q^2) : Subgroup (GL (Fin 2) ℝ)) 2,
      (f:ℍ→ℂ)=lpsQuadraticE2Twist q := by
  rintro ⟨f,hf⟩
  have h := CuspFormClass.zero_at_infty_slash f (g:=lpsE2PrimeCuspMatrix q)
  rw [hf] at h
  exact lpsQuadraticE2Twist_prime_cusp_not_zero q hq2 h
end QEC.Coding.TannerLiftedProduct

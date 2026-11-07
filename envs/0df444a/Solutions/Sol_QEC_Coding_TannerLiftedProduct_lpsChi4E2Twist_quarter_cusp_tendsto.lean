-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_quarter_cusp_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:16:28.785858+00:00
-- url     : https://prove2.me/submissions/adc2f753-161e-4d17-81ee-8ca51d4875ff

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Tendsto (lpsChi4E2Twist ∣[(2:ℤ)] lpsE2PrimeCuspMatrix 4) UpperHalfPlane.atImInfty
      (𝓝 (-12/gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))) := by
  have h := lpsChi4E2Twist_cusp_gcd_tendsto (lpsE2PrimeCuspMatrix 4)
  have he : (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹*
      (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
        (((Int.gcd ((4:ℤ)*(lpsE2PrimeCuspMatrix 4) 0 0+(r.val:ℤ)*(lpsE2PrimeCuspMatrix 4) 1 0)
          ((4:ℤ)*(lpsE2PrimeCuspMatrix 4) 1 0):ℕ):ℂ)^2/(4:ℂ)^2))=
      -12/gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)) := by
    norm_num [Fin.sum_univ_four,lpsE2PrimeCuspMatrix,Matrix.of_apply,
      lpsChi4E2Character_apply,ZMod.χ₄_apply]
    ring
  rw [he] at h
  exact h
end QEC.Coding.TannerLiftedProduct

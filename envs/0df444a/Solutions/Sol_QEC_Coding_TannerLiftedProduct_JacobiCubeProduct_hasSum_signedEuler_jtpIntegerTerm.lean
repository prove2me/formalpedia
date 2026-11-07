-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.hasSum_signedEuler_jtpIntegerTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:50:20.146032+00:00
-- url     : https://prove2.me/submissions/23909b37-183f-45e3-a7ee-feb2db1d5163

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_continuous_signedEulerHom
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_hasSum_jtpIntegerTerm_jacobiBilateral

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
theorem _root_.solution :
    letI : TopologicalSpace LaurentQ := ⊥
    HasSum (fun z : ℤ => signedEuler (jtpIntegerTerm z))
      (signedEuler jacobiBilateral) := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  exact hasSum_jtpIntegerTerm_jacobiBilateral.map
    signedEulerHom continuous_signedEulerHom
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct

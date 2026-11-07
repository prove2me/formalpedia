-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jacobiProd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:50:27.470427+00:00
-- url     : https://prove2.me/submissions/d3d9af5c-6358-4372-b93e-b35b68aefd02

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_qPochhammerInf_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_qPochhammerInf_neg_laurentZ

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
theorem _root_.solution :
    signedEuler jacobiProd = -(eulerProduct ^ 3) := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  rw [jacobiProd, qPochhammerInfX, qPochhammerInfNegZ,
    qPochhammerInfNegXMulZInv, signedEuler_mul, signedEuler_mul,
    map_mul]
  rw [evalNegOneSeries_qPochhammerInf_X,
    signedEuler_qPochhammerInf_X,
    evalNegOneSeries_qPochhammerInf_neg_laurentZ,
    signedEuler_qPochhammerInf_neg_laurentZ,
    evalNegOneSeries_qPochhammerInf_neg_X_mul_laurentZInv]
  ring
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct

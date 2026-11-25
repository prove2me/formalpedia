-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_integralPointClosure__8e8aa1bcee0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:51:20.425806+00:00
-- url     : https://prove2.me/submissions/75e44ff2-f2ca-44d3-8041-3322f305f915

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_fmul
import Theorems.Thm_Formalism_L2_Th1_C_Pts_endInt_zero
import Theorems.Thm_Formalism_L2_Th1_C_Pts_endInt_one
import Theorems.Thm_Formalism_L2_Th1_C_Pts_endInt_add
import Theorems.Thm_Formalism_L2_Th1_C_Pts_endInt_mul
import Theorems.Thm_Formalism_L2_Th1_C_Pts_endInt_neg_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Pts
namespace Formalism.L2.Th1.C
theorem _root_.solution : PtClosure := by
  intro K _ R l linv h hF
  exact ⟨fun σ x y hx hy => isPt_fadd h hF hx hy, fun a ha σ x hx => isPt_fmul h ha hx,
    endInt_zero h, endInt_one h, endInt_neg_one h hF, fun a b ha hb => endInt_add h hF ha hb,
    fun a b ha hb => endInt_mul h ha hb⟩
end Formalism.L2.Th1.C

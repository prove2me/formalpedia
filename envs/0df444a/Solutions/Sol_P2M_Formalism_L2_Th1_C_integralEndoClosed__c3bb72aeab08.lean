-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_integralEndoClosed__c3bb72aeab08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:13.301593+00:00
-- url     : https://prove2.me/submissions/702b9eff-9e06-4440-8662-20ab5fbdc477

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Clo_isClosed_intMv
import Theorems.Thm_Formalism_L2_Th1_C_Clo_coeffCont_fmul
import Theorems.Thm_Formalism_L2_Th1_C_Pts_intMv_of_intPS
import Theorems.Thm_Formalism_L2_Th1_C_Pts_intPS_of_intMv
import Theorems.Thm_Formalism_L2_Th1_C_Pts_mulBy_eq_fmul
import Theorems.Thm_Formalism_L2_Th1_C_USideB_intMv_of_intPS


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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Clo
namespace Formalism.L2.Th1.C
theorem _root_.solution : EndIntClosed := by
  intro K _ _ _ R hR l linv hl
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  have hc : CoeffCont fun a : K => fmul l linv a (PowerSeries.X : MvPowerSeries Unit K) :=
    coeffCont_fmul hl linv continuous_id hX
  have : {a : K | EndInt R l linv a} =
      {a : K | IntMv R (fmul l linv a (PowerSeries.X : MvPowerSeries Unit K))} := by
    ext a
    simp only [Set.mem_ofPred_eq, EndInt, Pts.mulBy_eq_fmul]
    exact ⟨Pts.intMv_of_intPS, Pts.intPS_of_intMv⟩
  rw [this]
  exact isClosed_intMv hR hc
end Formalism.L2.Th1.C

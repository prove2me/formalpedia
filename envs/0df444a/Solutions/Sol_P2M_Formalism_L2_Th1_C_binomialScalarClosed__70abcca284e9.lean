-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_binomialScalarClosed__70abcca284e9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:56.451395+00:00
-- url     : https://prove2.me/submissions/84921959-dd32-43f5-a929-98b215463c9b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_sub

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
theorem _root_.solution : BinomClosed := by
  intro K _ _ _ R hR
  simp only [IsBinomScalar, Set.ofPred_forall]
  refine isClosed_iInter fun n => hR.preimage ?_
  unfold binom
  exact (continuous_finsetProd _ fun i _ => continuous_id.sub continuous_const).div_const _
end Formalism.L2.Th1.C

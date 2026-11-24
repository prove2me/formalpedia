-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_scalarLinearClosed__d624c2f8cbb5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:28:06.102058+00:00
-- url     : https://prove2.me/submissions/0ec73274-b921-4d94-89f1-78741fc2e7ff

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_const
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_sub
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_smul
import Theorems.Thm_Formalism_L2_Th1_C_Clo_isClosed_LG
import Theorems.Thm_Formalism_L2_Th1_C_Clo_cc_smul
import Theorems.Thm_Formalism_L2_Th1_C_Clo_coeffCont_fmul
import Theorems.Thm_Formalism_L2_Th1_C_Clo_cc_fmul
import Theorems.Thm_Formalism_L2_Th1_C_Clo_constantCoeff_addDefect
import Theorems.Thm_Formalism_L2_Th1_C_Clo_coeffContinuous_addDefect

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
theorem _root_.solution : ZLinClosed := by
  intro K _ _ _ _ R hR l linv ph hl hli hph
  simp only [ZLinAt, Cong, Set.ofPred_forall]
  refine isClosed_iInter fun σ => isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_iInter fun hx => isClosed_iInter fun hy => ?_
  have hc : CoeffCont fun z : K => fmul l linv z y := coeffCont_fmul hl linv continuous_id hy.1
  refine isClosed_LG hR ((coeffContinuous_addDefect hl hli hx.1 hc fun z => cc_fmul hl hli z hy.1).sub
    (CoeffCont.smul continuous_id (CoeffCont.const _))) fun z => ?_
  rw [map_sub, constantCoeff_addDefect hl hli hph hx.1 (cc_fmul hl hli z hy.1),
    cc_smul (constantCoeff_addDefect hl hli hph hx.1 hy.1), sub_zero]
end Formalism.L2.Th1.C

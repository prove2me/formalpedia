-- Prove2me | solution 1 for P2M_GlobalTheory_T_isReduced_of_lieReg__e860e331fff2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:00.876566+00:00
-- url     : https://prove2.me/submissions/ab506c0d-0273-493a-a6c2-511d95ae8005

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfLieReg
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfLieRegStatement
import Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_isReduced_of_lieReg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.LieReg → IsReduced B.A := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg | exact GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg | (intros; apply GlobalTheory.UnitLemma.InvAlg.isReduced_of_lieReg <;> assumption)
end _root_.GlobalTheory.T

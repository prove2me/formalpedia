-- Prove2me | solution 1 for PI.BridgeMaxCptWork.bridgeMaxCpt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:48.249446+00:00
-- url     : https://prove2.me/submissions/cc076d28-39f4-468d-ba4b-ffd818c9f338

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MaximalCompactConjugacy_Assembly
import Theorems.Thm_PI_BridgeMaxCptWork_mem_KGA_iff
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.BridgeMaxCptWork
open NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
namespace PI.BridgeMaxCptWork
theorem _root_.solution (hR : PI.AdBridgeSteps.RealK) (hF : PI.AdBridgeSteps.FinK) :
    ∀ I : AutInst, AdBridgeK I := by
  intro I e hb
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_KGA_iff hR hF I e hb x).1 hx
  · intro hy
    refine ⟨e.symm y, (mem_KGA_iff hR hF I e hb _).2 ?_, by simp⟩
    simpa using hy
end PI.BridgeMaxCptWork

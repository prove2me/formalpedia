-- Prove2me | solution 1 for PI.BridgeMaxCptWork.mem_KGA_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:57:00.207037+00:00
-- url     : https://prove2.me/submissions/bb6c0627-427f-4c0d-925d-2ded29f383c1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MaximalCompactConjugacy_Assembly
import Theorems.Thm_PI_BridgeMaxCptWork_kinf_iff
import Theorems.Thm_PI_BridgeMaxCptWork_kf_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.BridgeMaxCptWork
open NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
namespace PI.BridgeMaxCptWork
theorem _root_.solution (hR : PI.AdBridgeSteps.RealK) (hF : PI.AdBridgeSteps.FinK) (I : AutInst)
    (e : I.GA ≃ₜ* HAd I) (hb : IsBridge I e) (x : I.GA) : x ∈ KGA I ↔ e x ∈ KHA I := by
  show ((∀ v, x.1 v ∈ KinfV I v) ∧ x.2 ∈ I.Kset) ↔ (e x ∈ KinfHA I ∧ e x ∈ KfHA I)
  exact and_congr (kinf_iff hR I e hb x) (kf_iff hF I e hb x)
end PI.BridgeMaxCptWork

-- Prove2me | solution 1 for PI.FinKW.LocTo.psiV_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:36:10.699776+00:00
-- url     : https://prove2.me/submissions/cca9373e-eefa-4472-b87a-aa388a810e7a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
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
open PI PI.FinKW PI.FinKW.LocTo
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.FinKW.LocTo
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) (a : Formalism.MainNotions.S.Af I.F) :
    psiV I v (e ⊗ₜ[I.F] a) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v a ⊗ₜ[I.F] e := by
  first
    | rfl
    | simp [psiV]
end PI.FinKW.LocTo

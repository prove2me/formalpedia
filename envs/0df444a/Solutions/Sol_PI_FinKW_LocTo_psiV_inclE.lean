-- Prove2me | solution 1 for PI.FinKW.LocTo.psiV_inclE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:58:40.842001+00:00
-- url     : https://prove2.me/submissions/0a65649a-7ea0-4543-9f54-6805fa1d8fe7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Theorems.Thm_PI_FinKW_LocTo_psiV_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinKW PI.FinKW.LocTo
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.FinKW.LocTo
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) :
    psiV I v (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) e) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) e := by
  show psiV I v (e ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)) = _
  rw [psiV_tmul, map_one]
  rfl
end PI.FinKW.LocTo

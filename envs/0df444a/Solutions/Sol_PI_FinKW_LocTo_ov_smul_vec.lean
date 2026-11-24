-- Prove2me | solution 1 for PI.FinKW.LocTo.ov_smul_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:57:22.529043+00:00
-- url     : https://prove2.me/submissions/bb8f29e1-a5fc-4340-90df-bcd5a62fb34b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Theorems.Thm_PI_FinKW_LocTo_ov_smul_eq

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
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : v.adicCompletionIntegers I.F)
    (z : Fin I.n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    c • z = ((c : v.adicCompletion I.F) ⊗ₜ[I.F] (1 : I.E)) • z := by
  funext i
  exact ov_smul_eq I v c (z i)
end PI.FinKW.LocTo

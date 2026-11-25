-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.incL_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:37:20.951144+00:00
-- url     : https://prove2.me/submissions/6878365c-be93-40d5-be50-b99f2e4414f6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPow
import Theorems.Thm_PI_FinKW_LocTo_ov_smul_vec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) {a : v.adicCompletion I.F}
    (ha : a ∈ v.adicCompletionIntegers I.F) {y : Fin I.n → Av I v}
    (hy : y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    incL I v a • y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
  have e : incL I v a • y = (⟨a, ha⟩ : v.adicCompletionIntegers I.F) • y := by
    rw [PI.FinKW.LocTo.ov_smul_vec]
    rfl
  rw [e]
  exact Submodule.smul_mem _ _ hy
end PI.UnitaryGroupMassFormula.AdIndexEq

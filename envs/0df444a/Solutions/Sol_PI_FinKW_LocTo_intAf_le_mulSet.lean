-- Prove2me | solution 1 for PI.FinKW.LocTo.intAf_le_mulSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:47:11.18914+00:00
-- url     : https://prove2.me/submissions/b8887b40-0dad-4bf7-ab4e-78e647532728

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Theorems.Thm_PI_FinKW_LocTo_psiV_tmul
import Theorems.Thm_PI_FinKW_LocTo_ov_smul_vec
import Theorems.Thm_PI_FinKW_LocTo_inclR_smul_mem

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
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.MainNotions.S.IntAf I.F I.E ≤ mulSet I v := by
  rw [Formalism.MainNotions.S.IntAf, Formalism.UG.tensInt, Subring.closure_le]
  rintro _ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
  · obtain ⟨o, rfl⟩ := he
    intro z hz
    rw [psiV_tmul, map_one]
    exact inclR_smul_mem I v o z hz
  · intro z hz
    rw [psiV_tmul]
    have h := Submodule.smul_mem _ (⟨a v, ha v⟩ : v.adicCompletionIntegers I.F) hz
    rw [ov_smul_vec] at h
    exact h
end PI.FinKW.LocTo

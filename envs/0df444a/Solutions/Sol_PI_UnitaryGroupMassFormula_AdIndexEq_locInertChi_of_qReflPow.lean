-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.locInertChi_of_qReflPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:41.679662+00:00
-- url     : https://prove2.me/submissions/7fdc0bec-715b-4e46-9d58-ed8c3f8a50a9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertQRG
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_q_reflection_generation

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
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (hP : QReflPow) : LocInertChi := by
  intro I v hv χ _ _ hK g
  have hq : {s : Uv I v | IsQRefl I v s} ⊆ (χ.ker : Set (Uv I v)) := by
    intro s hs
    obtain ⟨m, hm, hmK⟩ := hP I v hv s hs
    exact MonoidHom.mem_ker.mpr (hK s ⟨m, hm, hmK⟩)
  exact MonoidHom.mem_ker.mp ((Subgroup.closure_le _).mpr hq (q_reflection_generation I v hv g))
end PI.UnitaryGroupMassFormula.AdIndexEq

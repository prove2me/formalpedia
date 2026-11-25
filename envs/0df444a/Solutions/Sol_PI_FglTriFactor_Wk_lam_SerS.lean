-- Prove2me | solution 1 for PI.FglTriFactor.Wk.lam_SerS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:47.856917+00:00
-- url     : https://prove2.me/submissions/a22ac379-3e50-491c-b813-0a88cf0b3370

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglTriFactor PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglTriFactor.Wk
theorem _root_.solution {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hwq : ∀ n, PowerSeries.coeff n wq ∈ S) :
    lam wq ∈ SerS S (Fin 2) := by
  refine ⟨fun e => ⟨lam wq e, ?_⟩, ?_⟩
  · show PowerSeries.coeff (e 0 + e 1 + 1) (wser wq) ∈ S
    rw [wser, PowerSeries.coeff_X_pow_mul']
    split_ifs
    · exact hwq _
    · exact S.zero_mem
  · ext e
    rfl
end PI.FglTriFactor.Wk

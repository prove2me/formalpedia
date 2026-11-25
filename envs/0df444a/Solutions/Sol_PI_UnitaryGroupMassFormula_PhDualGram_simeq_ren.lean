-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhDualGram.simeq_ren
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:53:31.078408+00:00
-- url     : https://prove2.me/submissions/84a22c5b-6760-430f-91cc-5f24304fcd1f

import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_psubst
import Theorems.Thm_PI_FglPhSplit_Wk_allIn_subst_X
import Theorems.Thm_PI_FglPhSplit_Wk_expMv_eq_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhDualGram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime]
variable {σ τ : Type} [Finite σ] (r : σ → τ)
namespace PI.UnitaryGroupMassFormula.PhDualGram
theorem _root_.solution {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq (ren r f) (ren r g) := by
  obtain ⟨h0, h1⟩ := h
  have hs : ren r f - ren r g = ren r (f - g) := (map_sub _ _ _).symm
  have hc : constantCoeff (ren r (f - g)) = 0 := by
    rw [ren_apply]
    exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_ren r) (fun _ => constantCoeff_X _) h0
  refine ⟨by rw [hs, hc], fun n => ?_⟩
  have e1 : expMv (ren r (f - g)) = PI.FglPhSplit.expMv (ren r (f - g)) := rfl
  have e0 : expMv (f - g) = PI.FglPhSplit.expMv (f - g) := rfl
  have h1' : PI.FglPhSplit.Wk.AllIn (Wp p) (PI.FglPhSplit.expMv (f - g)) := fun n => by
    rw [← e0]; exact h1 n
  rw [hs, e1, PI.FglPhSplit.Wk.expMv_eq_subst hc, ← ren_psubst r _ h0,
    ← PI.FglPhSplit.Wk.expMv_eq_subst h0, ren_apply]
  exact PI.FglPhSplit.Wk.allIn_subst_X r (hasSubst_ren r) h1' n
end PI.UnitaryGroupMassFormula.PhDualGram

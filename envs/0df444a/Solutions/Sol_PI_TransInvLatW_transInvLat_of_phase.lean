-- Prove2me | solution 1 for PI.TransInvLatW.transInvLat_of_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:16.142708+00:00
-- url     : https://prove2.me/submissions/7d4d0bfb-6d70-4dc2-a4f9-d6c24db3989d

import Definitions.Def_Formalism_PeriodIntegrals_TransInvLat
import Definitions.Def_Formalism_PeriodIntegrals_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TranslationInvariantLattice_TransInvLatOfPhase
import Theorems.Thm_PI_TransInvLatW_shift_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical Complex
open PI PI.TransInvLatW
namespace PI.TransInvLatW
theorem _root_.solution (h : PhaseOne) : PI.TransInvLat := by
  intro w₁ w₂ hD G hG x ω m hm hx hω
  have hy : 2 * (m : ℂ) * ω ∈ lat2 w₁ w₂ := by
    have : 2 * (m : ℂ) * ω = (2 * m : ℕ) • ω := by rw [nsmul_eq_mul]; push_cast; ring
    rw [this]; exact AddSubgroup.nsmul_mem _ hω _
  have hy2 : 2 * (m : ℂ) * ω / 2 ∈ lat2 w₁ w₂ := by
    have : 2 * (m : ℂ) * ω / 2 = m • ω := by rw [nsmul_eq_mul]; ring
    rw [this]; exact AddSubgroup.nsmul_mem _ hω _
  have hG' := hG _ hy
  simp only [if_pos hy2, one_mul] at hG'
  funext z
  unfold U1
  rw [map_add]
  exact shift_core _ _ G x _ _ _ (fun z => hG' z) (h w₁ w₂ hD x ω m hm hx hω) z
end PI.TransInvLatW

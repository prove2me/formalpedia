-- Prove2me | solution 1 for PI.ExpIntWProof.div_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:03.651298+00:00
-- url     : https://prove2.me/submissions/facfcf94-2fce-4b67-996f-3b1e0cd4d33f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_StepIII
import Theorems.Thm_PI_ExpIntWProof_norm_p


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof
open PI
namespace PI.ExpIntWProof
theorem _root_.solution (h : KeyW) (p : ℕ) [hp : Fact p.Prime] :
    ∀ k : ℕ, ∀ y : ℂ_[p], y ∈ Wp p → ‖y‖ ≤ ((p : ℝ)⁻¹) ^ k → y / (p : ℂ_[p]) ^ k ∈ Wp p := by
  intro k
  induction k with
  | zero => intro y hy _; simpa using hy
  | succ k ih =>
    intro y hy hnorm
    have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
    have hpinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    have hlt : ‖y‖ < 1 :=
      lt_of_le_of_lt hnorm (pow_lt_one₀ hpos.le hpinv (Nat.succ_ne_zero k))
    have h1 : y / (p : ℂ_[p]) ∈ PI.Wp p := h p y hy hlt
    have h2 : ‖y / (p : ℂ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ k := by
      rw [norm_div, norm_p, div_le_iff₀ hpos, ← pow_succ]
      exact hnorm
    have h3 := ih _ h1 h2
    rwa [div_div, ← pow_succ'] at h3
end PI.ExpIntWProof

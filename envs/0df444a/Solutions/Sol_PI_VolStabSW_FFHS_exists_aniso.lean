-- Prove2me | solution 1 for PI.VolStabSW.FFHS.exists_aniso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:01.443802+00:00
-- url     : https://prove2.me/submissions/08ddec74-84b1-401c-9cc4-fa26a207fb4b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFHS
import Theorems.Thm_PI_VolStabSW_FFHS_IsSq_add_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FFHS
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}
namespace PI.VolStabSW.FFHS
theorem _root_.solution (h2 : (2 : K) ≠ 0) (hs : IsHS σ h) (x : V) (hx : x ≠ 0) :
    ∃ e, h e e ≠ 0 := by
  by_contra H
  push_neg at H
  obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
    by_contra H'
    push_neg at H'
    exact hx (hs.nondeg x H')
  have key : ∀ c : K, c * h x y + σ (c * h x y) = 0 := by
    intro c
    have e1 : h (x + c • y) (x + c • y) = h x x + h x (c • y) + (h (c • y) x + h (c • y) (c • y)) := by
      rw [hs.add_right, IsSq.add_left hs.toIsSq, IsSq.add_left hs.toIsSq]
      ring
    rw [H, H, H, hs.herm x (c • y), hs.smul_right] at e1
    linear_combination -e1
  have ha : h x y + σ (h x y) = 0 := by simpa using key 1
  by_cases hσ : ∃ c, σ c ≠ c
  · obtain ⟨c, hc⟩ := hσ
    have e2 := key c
    rw [map_mul] at e2
    have hsa : σ (h x y) = -(h x y) := by linear_combination ha
    rw [hsa] at e2
    have e3 : (c - σ c) * h x y = 0 := by linear_combination e2
    rcases mul_eq_zero.1 e3 with h0 | h0
    · exact hc (by linear_combination -h0)
    · exact hy h0
  · push_neg at hσ
    rw [hσ] at ha
    have e3 : (2 : K) * h x y = 0 := by linear_combination ha
    rcases mul_eq_zero.1 e3 with h0 | h0
    · exact h2 h0
    · exact hy h0
end PI.VolStabSW.FFHS

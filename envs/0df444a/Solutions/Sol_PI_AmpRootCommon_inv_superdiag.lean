-- Prove2me | solution 1 for PI.AmpRootCommon.inv_superdiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:01.109367+00:00
-- url     : https://prove2.me/submissions/6a74d00a-d47e-4051-925d-839781722077

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent
import Theorems.Thm_PI_AmpRootCommon_isUnit_unitri
import Theorems.Thm_PI_AmpRootCommon_inv_upper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.AmpRootCommon
variable {n : ℕ}
namespace PI.AmpRootCommon
theorem _root_.solution {u : Matrix (Fin n) (Fin n) ℂ} (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1)
    (m1 m : Fin n) (hm : m1.val + 1 = m.val) : u⁻¹ m1 m = - u m1 m := by
  have hdet := isUnit_unitri hu hud
  have hw := inv_upper hu hud
  have hne : m1 ≠ m := fun e => by rw [e] at hm; omega
  have h1 : (u⁻¹ * u) m1 m = 0 := by
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply, if_neg hne]
  have h2 : (u⁻¹ * u) m1 m1 = 1 := by
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply, if_pos rfl]
  rw [Matrix.mul_apply, Finset.sum_eq_single m1] at h2
  · rw [Matrix.mul_apply, Finset.sum_eq_add m1 m hne] at h1
    · rw [hud] at h2 h1
      rw [mul_one] at h2
      rw [h2, one_mul] at h1
      linear_combination h1
    · intro c _ hc
      by_cases hlt : c.val < m1.val
      · rw [hw (show id c < id m1 from hlt), zero_mul]
      · have : m.val < c.val := by
          have h3 : c.val ≠ m1.val := fun e => hc.1 (Fin.ext e)
          have h4 : c.val ≠ m.val := fun e => hc.2 (Fin.ext e)
          omega
        rw [hu (show id m < id c from this), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    by_cases hlt : b.val < m1.val
    · rw [hw (show id b < id m1 from hlt), zero_mul]
    · have : m1.val < b.val := by
        have h3 : b.val ≠ m1.val := fun e => hb (Fin.ext e)
        omega
      rw [hu (show id m1 < id b from this), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
end PI.AmpRootCommon

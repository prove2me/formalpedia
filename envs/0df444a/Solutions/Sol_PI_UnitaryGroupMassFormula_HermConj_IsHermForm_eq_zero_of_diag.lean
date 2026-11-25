-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.HermConj.IsHermForm.eq_zero_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:49:11.158148+00:00
-- url     : https://prove2.me/submissions/e433fe51-8d8d-4102-beb7-894537ef87ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_HermDiag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianDiagonalization_ExistsOrthogonalFamily
import Theorems.Thm_PI_UnitaryGroupMassFormula_HermConj_IsHermForm_add_left
import Theorems.Thm_PI_UnitaryGroupMassFormula_HermConj_IsHermForm_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.HermConj
open Matrix
variable {E : Type} [Field E]
variable {σ : E →+* E} {V : Type} [AddCommGroup V] [Module E V] {h : V → V → E}
namespace PI.UnitaryGroupMassFormula.HermConj
namespace IsHermForm
theorem _root_.solution [CharZero E] (hh : IsHermForm σ h)
    (hz : ∀ x, h x x = 0) (x y : V) : h x y = 0 := by
  have hsum : ∀ u v, h u v + h v u = 0 := by
    intro u v
    have e := hz (u + v)
    rw [hh.add_left, hh.add, hh.add, hz u, hz v] at e
    linear_combination e
  have hfix : ∀ a : E, (σ a - a) * h x y = 0 := by
    intro a
    have e := hsum (a • x) y
    rw [hh.smul_left, hh.smul] at e
    have e2 := hsum x y
    linear_combination e - a * e2
  by_contra hne
  have hσ : ∀ a, σ a = a := by
    intro a
    rcases mul_eq_zero.1 (hfix a) with h1 | h1
    · linear_combination h1
    · exact absurd h1 hne
  have e := hsum x y
  rw [hh.herm x y, hσ] at e
  have e2 : (2 : E) * h x y = 0 := by linear_combination e
  rcases mul_eq_zero.1 e2 with h2 | h2
  · norm_num at h2
  · exact hne h2
end IsHermForm
end PI.UnitaryGroupMassFormula.HermConj

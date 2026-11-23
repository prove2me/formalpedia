-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_MAlpha_M__isP0_c8d2d6fe8993
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:50:30.471703+00:00
-- url     : https://prove2.me/submissions/46d19eac-7d7b-4308-90f8-870ff9d05f46

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_M__det_nonneg_d173ab152aff
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_M__principalSubmatrix_9b037532404d

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix
namespace GroupTheoreticShannonCapacity.MAlpha
theorem _root_.solution (n : ℕ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    P0Matrix.IsP0Matrix n (Mα n α) := by
  intro S
  rw [Mα_principalSubmatrix]
  exact Mα_det_nonneg S.card α hα hα'
end GroupTheoreticShannonCapacity.MAlpha

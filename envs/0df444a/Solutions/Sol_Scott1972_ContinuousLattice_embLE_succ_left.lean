-- Prove2me | solution 1 for Scott1972.ContinuousLattice.embLE_succ_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:41:45.794805+00:00
-- url     : https://prove2.me/submissions/e3027ac0-0b24-411c-8382-d8c64f9aa96e

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Theorems.Thm_Scott1972_ContinuousLattice_Proposition313_con_apply
import Theorems.Thm_Scott1972_ContinuousLattice_Proposition313_min_apply
import Theorems.Thm_Scott1972_ContinuousLattice_Proposition314_fixMap_apply
attribute [local simp] Scott1972.ContinuousLattice.Proposition313.con_apply
attribute [local simp] Scott1972.ContinuousLattice.Proposition313.min_apply
attribute [local simp] Scott1972.ContinuousLattice.Proposition314.fixMap_apply



set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
namespace Scott1972.ContinuousLattice
theorem _root_.solution {n m : ℕ} (h1 : n ≤ m) (h2 : n + 1 ≤ m) (x : D n) :
    embLE D P h2 ((P n).incl x) = embLE D P h1 x := by
  simp only [embLE]
  exact Nat.leRecOn_succ_left x h1 h2
end Scott1972.ContinuousLattice

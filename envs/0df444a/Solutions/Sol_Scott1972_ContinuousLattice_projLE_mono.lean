-- Prove2me | solution 1 for Scott1972.ContinuousLattice.projLE_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:07.669673+00:00
-- url     : https://prove2.me/submissions/f07866b3-be7a-43ac-b8ef-aef89c40310f

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
namespace Scott1972.ContinuousLattice
theorem _root_.solution {m n : ℕ} (h : m ≤ n) {x y : D n} (hxy : x ≤ y) :
    projLE D P h x ≤ projLE D P h y := by
  induction n, h using Nat.le_induction with
  | base =>
      rw [projLE_self, projLE_self]
      exact hxy
  | succ k hk ih =>
      rw [projLE_succ D P hk (Nat.le_succ_of_le hk), projLE_succ D P hk (Nat.le_succ_of_le hk)]
      exact ih ((P k).retr.monotone hxy)
end Scott1972.ContinuousLattice

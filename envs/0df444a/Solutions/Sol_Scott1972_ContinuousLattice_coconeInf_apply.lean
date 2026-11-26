-- Prove2me | solution 1 for Scott1972.ContinuousLattice.coconeInf_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:42:14.834842+00:00
-- url     : https://prove2.me/submissions/da677ed9-7ba9-42be-9ab0-6e2f5b71f8bd

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
variable {D' : Type*} [CompleteLattice D']
namespace Scott1972.ContinuousLattice
theorem _root_.solution (f : ∀ n, ScottMap (D n) D') (x : InverseLimit D P) :
    coconeInf D P f x = ⨆ n, f n (x.1 n) := rfl
end Scott1972.ContinuousLattice

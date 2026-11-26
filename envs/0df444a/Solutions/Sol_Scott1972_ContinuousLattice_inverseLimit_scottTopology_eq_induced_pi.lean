-- Prove2me | solution 1 for Scott1972.ContinuousLattice.inverseLimit_scottTopology_eq_induced_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:44:13.013553+00:00
-- url     : https://prove2.me/submissions/67b74db1-e17d-4f1e-aa32-e799493b6e0b

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_t0Space
import Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_specializationLe_iff
import Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_isInjectiveSpace
import Theorems.Thm_Scott1972_ContinuousLattice_theorem_2_12_backward_exact


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hD : ∀ n, IsContinuousLattice (D n)) :
    (scottTopologicalSpace : TopologicalSpace (InverseLimit D P)) =
      inverseLimitTopology D P := by
  letI : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  letI : T0Space (InverseLimit D P) := inverseLimit_t0Space D P
  exact (theorem_2_12_backward_exact (inverseLimit_isInjectiveSpace D P hD)
    (inverseLimit_specializationLe_iff D P)).2
end Scott1972.ContinuousLattice

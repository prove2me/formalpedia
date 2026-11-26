-- Prove2me | solution 1 for Scott1972.ContinuousLattice.embInf_inverseLimitTopology_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:12.256089+00:00
-- url     : https://prove2.me/submissions/8d688582-dcb8-43a9-9532-54e1ae790591

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_scottTopology_eq_induced_pi
import Theorems.Thm_Scott1972_ContinuousLattice_ScottMap_continuous


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hD : ∀ n, IsContinuousLattice (D n)) (n : ℕ) :
    @Continuous (D n) (InverseLimit D P) scottTopologicalSpace
      (inverseLimitTopology D P) (embInf D P n) := by
  rw [← inverseLimit_scottTopology_eq_induced_pi D P hD]
  exact (embInf D P n).continuous
end Scott1972.ContinuousLattice

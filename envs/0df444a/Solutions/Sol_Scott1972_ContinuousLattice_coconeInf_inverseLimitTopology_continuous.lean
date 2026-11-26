-- Prove2me | solution 1 for Scott1972.ContinuousLattice.coconeInf_inverseLimitTopology_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:32.739487+00:00
-- url     : https://prove2.me/submissions/19d5e387-5aaa-44c6-b32d-d427f535ebd9

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_scottTopology_eq_induced_pi
import Theorems.Thm_Scott1972_ContinuousLattice_coconeInf_preservesDirectedSup
import Theorems.Thm_Scott1972_ContinuousLattice_continuous_of_preservesDirectedSup


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
variable {D' : Type*} [CompleteLattice D']
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hD : ∀ n, IsContinuousLattice (D n))
    (f : ∀ n, ScottMap (D n) D') :
    @Continuous (InverseLimit D P) D' (inverseLimitTopology D P)
      scottTopologicalSpace (coconeInf D P f) := by
  rw [← inverseLimit_scottTopology_eq_induced_pi D P hD]
  exact continuous_of_preservesDirectedSup (coconeInf_preservesDirectedSup D P f)
end Scott1972.ContinuousLattice

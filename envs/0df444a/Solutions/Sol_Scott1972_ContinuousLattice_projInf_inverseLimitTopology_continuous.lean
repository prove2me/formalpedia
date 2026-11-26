-- Prove2me | solution 1 for Scott1972.ContinuousLattice.projInf_inverseLimitTopology_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:12.718932+00:00
-- url     : https://prove2.me/submissions/cd7a521d-1f7f-453a-a4bf-f503e1ea7389

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_coordinate_continuous

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
namespace Scott1972.ContinuousLattice
theorem _root_.solution (n : ℕ) :
    @Continuous (InverseLimit D P) (D n) (inverseLimitTopology D P)
      scottTopologicalSpace (projInf D P n) :=
  inverseLimit_coordinate_continuous D P n
end Scott1972.ContinuousLattice

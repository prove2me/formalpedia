-- Prove2me | solution 1 for Scott1972.ContinuousLattice.idInf_eq_iSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:28.707179+00:00
-- url     : https://prove2.me/submissions/fd230cbc-7f57-4501-89b5-0bc32ee6eac3

import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Mathlib.Order.GaloisConnection.Basic
import Definitions.Def_Scott1972_ContinuousLattice_InverseLimits
import Theorems.Thm_Scott1972_ContinuousLattice_inverseLimit_eq_iSup

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set
universe u
variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))
namespace Scott1972.ContinuousLattice
theorem _root_.solution :
    (ScottMap.idMap : ScottMap (InverseLimit D P) (InverseLimit D P))
      = ⨆ n, (embInf D P n).comp (projInf D P n) := by
  apply ScottMap.ext
  intro x
  rw [show (⨆ n, (embInf D P n).comp (projInf D P n))
        = sSup (Set.range fun n => (embInf D P n).comp (projInf D P n)) from sSup_range.symm,
    ScottMap.sSup_apply, ScottMap.idMap_apply, ← Set.range_comp, sSup_range]
  exact inverseLimit_eq_iSup D P x
end Scott1972.ContinuousLattice

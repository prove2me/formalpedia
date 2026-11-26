-- Prove2me | solution 1 for Scott1972.ContinuousLattice.idemFix_isContinuousLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:41:19.728453+00:00
-- url     : https://prove2.me/submissions/ff7dad33-a479-4a5a-8ea0-5604db2cedbc

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Theorems.Thm_Scott1972_ContinuousLattice_preservesDirectedSup_monotone
import Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_10_a


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {L : Type*} [CompleteLattice L]
variable {e : L → L}
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e)
    (hL : IsContinuousLattice L) :
    @IsContinuousLattice (IdemFix e)
      (IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)) := by
  letI := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
  exact proposition_2_10_a (idemFixRetraction hidem hsc) hL
end Scott1972.ContinuousLattice

-- Prove2me | solution 1 for Scott1972.ContinuousLattice.idemFix_scottTopology
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:41:21.306633+00:00
-- url     : https://prove2.me/submissions/3c8418eb-901f-454e-a57f-7120331d36bf

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Definitions.Def_Scott1972_ContinuousLattice_Theorem212
import Theorems.Thm_Scott1972_ContinuousLattice_preservesDirectedSup_monotone
import Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_10_b


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {L : Type*} [CompleteLattice L]
variable {e : L → L}
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e)
    (hL : IsContinuousLattice L) :
    @scottTopologicalSpace (IdemFix e)
        (IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)) =
      TopologicalSpace.induced (Subtype.val : IdemFix e → L) scottTopologicalSpace := by
  letI := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
  exact proposition_2_10_b (idemFixRetraction hidem hsc) hL
end Scott1972.ContinuousLattice

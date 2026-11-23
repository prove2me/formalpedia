-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Tot.sum_fromBlocks_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:54.632266+00:00
-- url     : https://prove2.me/submissions/ef7c8f9c-2f23-47e7-bd19-00c6b6e4fdb3

import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthFrobeniusStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthProductStatementHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.Up.Tot
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.PGsh.Up.Tot
theorem _root_.solution {g : ℕ} {ι : Type} (s : Finset ι)
    (A D : ι → Matrix (Fin g) (Fin g) R) :
    ∑ i ∈ s, fromBlocks (A i) 0 0 (D i) = fromBlocks (∑ i ∈ s, A i) 0 0 (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fromBlocks_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih, fromBlocks_add,
      add_zero]
end ReciprocityTheory.PGsh.Up.Tot

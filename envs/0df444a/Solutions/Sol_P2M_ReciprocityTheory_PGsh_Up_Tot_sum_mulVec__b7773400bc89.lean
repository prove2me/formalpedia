-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_Up_Tot_sum_mulVec__b7773400bc89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:33:44.509131+00:00
-- url     : https://prove2.me/submissions/90016ea3-7e12-44ad-b4af-82a281a7ffcc

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
theorem _root_.solution {n : Type} [Fintype n] {ι : Type} (s : Finset ι) (A : ι → Matrix n n R)
    (w : n → R) : (∑ i ∈ s, A i) *ᵥ w = ∑ i ∈ s, A i *ᵥ w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, ih]
end ReciprocityTheory.PGsh.Up.Tot

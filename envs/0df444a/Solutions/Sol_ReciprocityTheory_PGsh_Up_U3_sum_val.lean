-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.sum_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:49:02.678259+00:00
-- url     : https://prove2.me/submissions/1697090a-83b3-4488-a01e-7c3dcb9e6101

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_VdetLeOfSpanLe
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_finZ_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {p : ℕ} [hp : Fact p.Prime]
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution [NeZero p] : ∑ j : ZMod p, j.val = p * (p - 1) / 2 := by
  rw [← Finset.sum_range_id, Finset.sum_range (fun i => i)]
  exact (Fintype.sum_equiv (finZ p) (fun i : Fin p => (i : ℕ)) (fun j => j.val)
    (fun i => (finZ_val i).symm)).symm
end ReciprocityTheory.PGsh.Up.U3

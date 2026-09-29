-- Prove2me | solution 2 for TarchaBraids.pureBraid_le_halfTwist_closure
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:18:09.658736+00:00
-- url     : https://prove2.me/submissions/0df7d1a1-a01a-418e-a323-99e7715f2d8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TarchaBraids_pureBraid_le_halfTwist_closure_step
import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG TarchaBraids

namespace PBSol

instance : Subsingleton (OrderedConfig 0) := ⟨fun p q => by
  apply Subtype.ext; funext i; exact absurd i.isLt (by omega)⟩

instance : Subsingleton (UnorderedConfig 0) := ⟨fun p q => by
  induction p using Quotient.ind with | _ a =>
  induction q using Quotient.ind with | _ b =>
  rw [Subsingleton.elim a b]⟩

instance : ContractibleSpace (UnorderedConfig 0) := by
  haveI : Unique (UnorderedConfig 0) := uniqueOfSubsingleton (baseUnordered 0)
  exact (Homeomorph.homeomorphOfUnique (UnorderedConfig 0) Unit).contractibleSpace

end PBSol

theorem _root_.solution (n : ℕ) :
    (FundamentalGroup.map (configProj n) (baseOrdered n)).range ≤
      Subgroup.closure (Set.range (fun i : Fin (n - 1) => halfTwistBraid n i)) := by
  induction n with
  | zero =>
    intro x _
    have h : Subsingleton (GeomBraidGroup 0) := by infer_instance
    rw [Subsingleton.elim x 1]
    exact one_mem _
  | succ m ih => exact TarchaBraids.pureBraid_le_halfTwist_closure_step m ih

#print axioms solution

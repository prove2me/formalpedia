-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.cosetCoordinates_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:32:01.121797+00:00
-- url     : https://prove2.me/submissions/445860f1-f2bb-4acb-8360-b6024ec80659

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFamilyValuationDetEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) {ι : Type}
    [Fintype ι] (g : ι → N → C) (x : N) :
    h3co K β (∑ i, g i) x = ∑ i, h3co K β (g i) x := by
  funext l
  simp only [h3co, Finset.sum_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_comm
end ReciprocityTheory.PGsh.L2

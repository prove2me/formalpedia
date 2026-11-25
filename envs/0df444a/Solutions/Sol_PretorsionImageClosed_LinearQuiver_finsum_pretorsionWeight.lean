-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.finsum_pretorsionWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:27:14.079196+00:00
-- url     : https://prove2.me/submissions/ef80d1ed-4034-47c8-94b4-e2cfefcd0f8f

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffCriterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_pretorsionWeight_eq

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution :
    ∑ᶠ P : PretorsionTheory (Statement.LinRep k n), pretorsionWeight k n P =
      ∑ p : CutoffPair n, cpWeight p := by
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl (fun P _ => pretorsionWeight_eq P)]
  exact Fintype.sum_equiv pretorsionEquiv _ _ (fun _ => rfl)
end PretorsionImageClosed.LinearQuiver

-- Prove2me | solution 1 for ThreeSum.SignedLeaf.mobius_eq_signed_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:37:26.845184+00:00
-- url     : https://prove2.me/submissions/cdbb5c4c-be9e-4eca-9741-8414313f9730

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Theorems.Thm_ThreeSum_SignedLeaf_neg_one_pow_sub

set_option autoImplicit false
open ThreeSum ThreeSum.SignedLeaf
open Finset ThreeSum.SubsetAddress
open scoped BigOperators
namespace ThreeSum.SignedLeaf
theorem _root_.solution {W : ℕ} (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (preL preR Q : Finset (Fin W)) :
    Subset.mobius
      (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
        SubsetStages.stageValue g stage (preR ∪ S)) Q =
      (-1 : ℤ)^Q.card * ∑ S ∈ Q.powerset, value f g stage preL preR S := by
  rw [Subset.mobius,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [neg_one_pow_sub (Finset.card_le_card (Finset.mem_powerset.mp hS)),value]
  ring
end ThreeSum.SignedLeaf

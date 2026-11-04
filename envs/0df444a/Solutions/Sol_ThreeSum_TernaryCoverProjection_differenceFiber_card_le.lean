-- Prove2me | solution 1 for ThreeSum.TernaryCoverProjection.differenceFiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:49.895607+00:00
-- url     : https://prove2.me/submissions/6ca515b5-d3ae-4482-b520-90b13c5ef11d

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
import Theorems.Thm_ThreeSum_TernaryCoverProjection_differenceCode_eq_of_field
import Theorems.Thm_ThreeSum_TernaryCoverProjection_cell_unique
import Theorems.Thm_ThreeSum_TernaryCoverProjection_marked_card
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data
import Theorems.Thm_ThreeSum_TernaryCoverLocal_endpoint_injective
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal
namespace ThreeSum.TernaryCoverProjection
theorem _root_.solution {L p : ℕ} (α π : DigitType)
    (hthirds : π 2 = 3 * α 2) (hp : 4 < p) (q : Fin L → ZMod p) :
    (differenceFiber α π q).card ≤ L.choose (π 2 / 3) := by
  classical
  have hcount : (differenceFiber α π q).card ≤
      ((univ : Finset (Fin L)).powersetCard (π 2 / 3)).card := by
    apply card_le_card_of_injOn marked
    · intro e _
      exact mem_powersetCard.mpr ⟨subset_univ _, marked_card e hthirds⟩
    · intro e he f hf hmark
      apply endpoint_injective α π
      apply Prod.ext
      · funext i
        have hproj := ((mem_filter.mp he).2 i).trans ((mem_filter.mp hf).2 i).symm
        have hcode := differenceCode_eq_of_field hp (left e i) (right e i)
          (left f i) (right f i) hproj
        have hmarked : (left e i = 1 ∧ right e i = 1) ↔
            (left f i = 1 ∧ right f i = 1) := by
          have hi := congrArg (fun s : Finset (Fin L) => i ∈ s) hmark
          simpa [marked] using hi
        have hs := (edge_data e).2.2.2 i
        have ht := (edge_data f).2.2.2 i
        exact (cell_unique (left e i) (right e i) (left f i) (right f i)
          (by have h := (output e i).isLt; omega)
          (by have h := (output f i).isLt; omega) hcode hmarked).1
      · funext i
        have hproj := ((mem_filter.mp he).2 i).trans ((mem_filter.mp hf).2 i).symm
        have hcode := differenceCode_eq_of_field hp (left e i) (right e i)
          (left f i) (right f i) hproj
        have hmarked : (left e i = 1 ∧ right e i = 1) ↔
            (left f i = 1 ∧ right f i = 1) := by
          have hi := congrArg (fun s : Finset (Fin L) => i ∈ s) hmark
          simpa [marked] using hi
        have hs := (edge_data e).2.2.2 i
        have ht := (edge_data f).2.2.2 i
        exact (cell_unique (left e i) (right e i) (left f i) (right f i)
          (by have h := (output e i).isLt; omega)
          (by have h := (output f i).isLt; omega) hcode hmarked).2
  simpa [card_powersetCard] using hcount
end ThreeSum.TernaryCoverProjection

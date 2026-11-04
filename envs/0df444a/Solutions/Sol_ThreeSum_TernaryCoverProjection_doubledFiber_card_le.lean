-- Prove2me | solution 1 for ThreeSum.TernaryCoverProjection.doubledFiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:38.467721+00:00
-- url     : https://prove2.me/submissions/da23dd3b-34ca-4dd8-9436-ae8d280a29a2

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
import Theorems.Thm_ThreeSum_TernaryCoverProjection_doubledCode_lt
import Theorems.Thm_ThreeSum_TernaryCoverProjection_doubled_cell_unique
import Theorems.Thm_ThreeSum_TernaryCoverProjection_doubledAmbiguous_card
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data
import Theorems.Thm_ThreeSum_TernaryCoverLocal_endpoint_injective
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal
namespace ThreeSum.TernaryCoverProjection
theorem _root_.solution {L p : ℕ} (swap : Bool) (α π : DigitType)
    (hthirds : π 2 = 3 * α 2) (hp : 4 < p) (q : Fin L → ZMod p) :
    (doubledFiber swap α π q).card ≤ 2 ^ (π 1 / 2 + π 2 / 3) := by
  classical
  have hcode {e f : LocalEdge L α π} (he : e ∈ doubledFiber swap α π q)
      (hf : f ∈ doubledFiber swap α π q) (i : Fin L) :
      doubledCode swap (left e i) (right e i) = doubledCode swap (left f i) (right f i) := by
    have heq := ((mem_filter.mp he).2 i).trans ((mem_filter.mp hf).2 i).symm
    have hlo (g : LocalEdge L α π) : doubledCode swap (left g i) (right g i) < p := by
      apply (doubledCode_lt swap _ _ ?_).trans_le (by omega)
      have hs := (edge_data g).2.2.2 i
      have hq := (output g i).isLt
      omega
    have hv := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast_of_lt (hlo e), ZMod.val_natCast_of_lt (hlo f)] using hv
  by_cases hz : (doubledFiber swap α π q).card = 0
  · simp [hz]
  obtain ⟨e0, he0⟩ := card_pos.mp (Nat.pos_of_ne_zero hz)
  have hcount : (doubledFiber swap α π q).card ≤ (doubledAmbiguous swap e0).powerset.card := by
    apply card_le_card_of_injOn (doubledMarked swap)
    · intro e he
      apply mem_powerset.mpr
      intro i hi
      have hm := (mem_filter.mp hi).2
      have hc : doubledCode swap (left e i) (right e i) = 2 := by
        cases swap <;> simp_all [doubledMark, doubledCode]
      exact mem_filter.mpr ⟨mem_univ _, (hcode he he0 i).symm.trans hc⟩
    · intro e he f hf hmarked
      apply endpoint_injective α π
      have hpair (i : Fin L) : left e i = left f i ∧ right e i = right f i := by
        have hm : doubledMark swap (left e i) (right e i) ↔
            doubledMark swap (left f i) (right f i) := by
          have hi := congrArg (fun s : Finset (Fin L) => i ∈ s) hmarked
          simpa [doubledMarked] using hi
        apply doubled_cell_unique swap _ _ _ _ ?_ ?_ (hcode he hf i) hm
        · have hs := (edge_data e).2.2.2 i; have hq := (output e i).isLt; omega
        · have hs := (edge_data f).2.2.2 i; have hq := (output f i).isLt; omega
      exact Prod.ext (funext fun i => (hpair i).1) (funext fun i => (hpair i).2)
  simpa [card_powerset, doubledAmbiguous_card swap e0 hthirds] using hcount
end ThreeSum.TernaryCoverProjection

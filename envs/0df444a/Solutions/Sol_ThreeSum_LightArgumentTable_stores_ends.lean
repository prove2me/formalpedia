-- Prove2me | solution 1 for ThreeSum.LightArgumentTable.stores_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:06:34.045395+00:00
-- url     : https://prove2.me/submissions/08326ec0-6302-45e6-a7b8-fd123f7d2585

import Definitions.Def_Submission_ThreeSum_LightFiniteTable
import Definitions.Def_Submission_ThreeSum_LightArgumentTable
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_storeLast
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_3f3326597d4f4ccd
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightArgumentTable
open Light
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightArgumentTable
theorem _root_.solution (xs : List ℤ) (base offset : ℕ) (loc μ : ℕ → ℤ) (hbase : loc 0 = (base : ℤ))
    (hread : ∀ (i : ℕ) (hi : i < xs.length), loc (offset + i + 1) = xs.getD i 0) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : base + offset + xs.length ≤ lim.space) :
    Ends lim P depth (stores offset xs.length) ⟨loc, μ⟩ (5 * xs.length)
      (fun σ => σ.loc = loc ∧ Seg σ.mem (base + offset) xs ∧ SameOutside μ σ.mem (base + offset) xs.length) :=
  by
  induction xs generalizing offset μ with
  | nil => exact Ends.skip ⟨rfl, Seg.nil, SameOutside.refl⟩
  | cons x xs
    ih =>
    have haddr : base + offset < lim.space := by simp only [List.length_cons] at hspace; omega
    have haddrWord : ((base + offset : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (Nat.le_of_lt haddr)).trans hw
    have hoff : (offset : ℤ) ≤ lim.word := by omega
    have hx : loc (offset + 1) = x := by simpa only [Nat.add_zero, List.getD_cons_zero] using hread 0 (by simp)
    simp only [List.length_cons, stores]
    refine Ends.seq 5 (5 * xs.length) ?_ (by omega)
    refine
      Ends.storeLast ?_ (hs := by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbase, hx, haddr, haddrWord, hoff] <;> omega))
        (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega)))
    have hrest :=
      ih (offset + 1) (Function.update μ (base + offset) x)
        (fun i hi => by
          simpa only [List.getD_cons_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            hread (i + 1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hi))
        (by simp only [List.length_cons] at hspace; omega)
    simp only [Expr.val, Op.eval, hbase, hx, ← Nat.cast_add, Int.toNat_natCast]
    apply hrest.mono le_rfl
    rintro σ ⟨hloc, hseg, hkeep⟩
    refine ⟨hloc, ?_, ?_⟩
    · rw [seg_cons]
      refine ⟨?_, ?_⟩
      · have hh := hkeep (base + offset) (Or.inl (by omega))
        simpa using hh
      · simpa only [Nat.add_assoc] using hseg
    · intro a ha
      rw [hkeep a (by omega)]
      exact Function.update_of_ne (by omega) _ _
end ThreeSum.LightArgumentTable

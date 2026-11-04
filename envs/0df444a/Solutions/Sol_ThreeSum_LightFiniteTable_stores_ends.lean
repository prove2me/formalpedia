-- Prove2me | solution 1 for ThreeSum.LightFiniteTable.stores_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:33:16.642986+00:00
-- url     : https://prove2.me/submissions/d6328b0f-2ca1-475a-b87b-a6d00e5e0a01

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightFiniteTable
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_storeTo
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
open ThreeSum ThreeSum.LightFiniteTable
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightFiniteTable
theorem _root_.solution (xs : List ℕ) (base offset : ℕ) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : base + offset + xs.length ≤ lim.space) (hvalues : ∀ x ∈ xs, (x : ℤ) ≤ lim.word) :
    Ends lim P d (stores offset xs) ⟨frame [base], μ⟩ (5 * xs.length)
      (fun σ =>
        σ.loc = frame [base] ∧
          Seg σ.mem (base + offset) (xs.map (fun (x : ℕ) => (x : ℤ))) ∧
            SameOutside μ σ.mem (base + offset) xs.length) :=
  by
  induction xs generalizing offset μ with
  | nil => exact Ends.skip ⟨rfl, Seg.nil, SameOutside.refl⟩
  | cons x xs
    ih =>
    have haddr : base + offset < lim.space := by simp only [List.length_cons] at hspace; omega
    have haddrWord : ((base + offset : ℕ) : ℤ) ≤ lim.word := by
      exact (show ((base + offset : ℕ) : ℤ) ≤ (lim.space : ℤ) by exact_mod_cast (Nat.le_of_lt haddr)).trans hw
    have hoffWord : (offset : ℤ) ≤ lim.word :=
      by
      have hle : (offset : ℤ) ≤ ((base + offset : ℕ) : ℤ) := by omega
      exact hle.trans haddrWord
    have hxWord := hvalues x (by simp)
    rw [stores]
    refine Ends.seq 5 (5 * xs.length) ?_ (by simp; omega)
    refine
      Ends.storeTo (base + offset) (x : ℤ) ?_
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddrWord, hoffWord, hxWord, haddr] <;>
              omega))
        (by
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
    · have hh :=
        ih (offset + 1) (Function.update μ (base + offset) (x : ℤ)) (by simp only [List.length_cons] at hspace; omega)
          (fun y hy => hvalues y (by simp [hy]))
      apply hh.mono le_rfl
      rintro σ ⟨hloc, hseg, hsame⟩
      refine ⟨hloc, ?_, ?_⟩
      · rw [List.map_cons, seg_cons]
        constructor
        · have ha := hsame (base + offset) (Or.inl (by omega))
          simpa using ha
        · simpa only [Nat.add_assoc] using hseg
      · intro a ha
        have houtside : a < base + (offset + 1) ∨ base + (offset + 1) + xs.length ≤ a :=
          by
          simp only [List.length_cons] at ha
          omega
        rw [hsame a houtside]
        exact Function.update_of_ne (by simp only [List.length_cons] at ha; omega) _ _
end ThreeSum.LightFiniteTable

-- Prove2me | solution 1 for ThreeSum.LightFiniteTable.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:37:02.041038+00:00
-- url     : https://prove2.me/submissions/4134a4e3-e844-4450-9f4a-6b7da0884e14

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightFiniteTable
import Theorems.Thm_ThreeSum_LightFiniteTable_stores_ends
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
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
theorem _root_.solution {p : ℕ} {xs : List ℕ} (hprog : P[p]? = some (body xs)) (base : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : base + xs.length ≤ lim.space) (hvalues : ∀ x ∈ xs, (x : ℤ) ≤ lim.word) :
    Meets lim P p d [base] μ (5 * xs.length + 2)
      (fun r ν =>
        r = (xs.length : ℤ) ∧ Seg ν base (xs.map (fun (x : ℕ) => (x : ℤ))) ∧ SameOutside μ ν base xs.length) :=
  by
  have hlenWord : (xs.length : ℤ) ≤ lim.word := by
    exact (show (xs.length : ℤ) ≤ (lim.space : ℤ) by exact_mod_cast (show xs.length ≤ lim.space by omega)).trans hw
  apply Meets.of_body hprog
  unfold body
  refine Ends.seq (5 * xs.length) 2 ?_ le_rfl
  have hh := stores_ends (P := P) (d := d) xs base 0 μ hw (by simpa using hspace) hvalues
  apply hh.mono le_rfl
  rintro σ ⟨hloc, hseg, hsame⟩
  cases σ with
  | mk loc mem =>
    dsimp only at hloc hseg hsame ⊢
    subst loc
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (xs.length : ℕ) ?_ ?_ ?_
      on_goal -1 =>
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
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨rfl, by simpa using hseg, by simpa using hsame⟩
end ThreeSum.LightFiniteTable

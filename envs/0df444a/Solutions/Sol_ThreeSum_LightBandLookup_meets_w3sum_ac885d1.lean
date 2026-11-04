-- Prove2me | solution 1 for ThreeSum.LightBandLookup.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:21:15.579847+00:00
-- url     : https://prove2.me/submissions/db62fec0-dafe-4c1c-8efa-84b476a13ff1

import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_WeightedCache3SUM_Alias_b3ed31058dd4b298
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_BinarySearch_upperBound_correct
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
open ThreeSum ThreeSum.LightBandLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandLookup
theorem _root_.solution {pMain pSearch a b n powers W L d : ℕ} {x : ℤ} (hmain : P[pMain]? = some (body pSearch))
    (hsearch : P[pSearch]? = some (searchBody pSearch)) (μ : ℕ → ℤ) (lo hi : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a + n ≤ lim.space) (hb : b + n ≤ lim.space) (hspace : powers + (W + 1) ≤ lim.space)
    (hword : ((n + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word) (hreadLo : ∀ i < n, μ (a + i) = lo i)
    (hreadHi : ∀ i < n, μ (b + i) = hi i) (hpowers : Powers μ powers W) (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j)
    (hL : L ≤ W) (hn : n < 2 ^ L) (hd : d + L + 1 ≤ lim.depth) :
    Meets lim P pMain d [a, b, n, x, powers, L] μ (time L) (fun r μ' => r = (result lo hi n x : ℤ) ∧ μ' = μ) :=
  by
  have hpart := BinarySearch.upperBound_correct lo n x hsorted
  have hkn := hpart.1
  have hcall :=
    search_meets hsearch μ lo (BinarySearch.upperBound lo n x) hw ha hspace hword hreadLo hpowers hpart L 0 hL
      (by omega) (by omega) (d + 1) (by omega)
  apply Meets.of_body hmain
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, searchTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [searchTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, searchTime] <;> omega)
    on_goal -1 => (rintro count μ' ⟨hcount, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ'
  subst count
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine
      _root_.Light.Ends.iteIffThen ((0 : ℤ) < (BinarySearch.upperBound lo n x : ℤ)) (fun hkZ => ?_) (fun hkZ => ?_) ?_
        ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, searchTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [searchTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, searchTime] <;> omega)
    all_goals
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_
  · have hk : 0 < BinarySearch.upperBound lo n x := by exact_mod_cast hkZ
    have hread := hreadHi (BinarySearch.upperBound lo n x - 1) (by omega)
    have haddr :
      (b : ℤ) + (BinarySearch.upperBound lo n x : ℤ) - 1 = ((b + (BinarySearch.upperBound lo n x - 1) : ℕ) : ℤ) := by
      omega
    have hnat : ((b : ℤ) + (BinarySearch.upperBound lo n x : ℤ) - 1).toNat = b + (BinarySearch.upperBound lo n x - 1) :=
      by rw [haddr, Int.toNat_natCast]
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine
        _root_.Light.Ends.iteIffThen (hi (BinarySearch.upperBound lo n x - 1) < x) (fun hh => ?_) (fun hh => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hnat, hread,
              searchTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hnat, hread, searchTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hnat, hread, searchTime] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, searchTime]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [searchTime] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, searchTime] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      exact ⟨by simp [result, BinarySearch.locate, hk, not_le.mpr hh], rfl⟩
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen (BinarySearch.upperBound lo n x : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, searchTime]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [searchTime] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, searchTime] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨?_, rfl⟩
      simp [result, BinarySearch.locate, hk, le_of_not_gt hh]
  · have hk : ¬0 < BinarySearch.upperBound lo n x := by exact_mod_cast hkZ
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, searchTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [searchTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, searchTime] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp [result, BinarySearch.locate, hk], rfl⟩
end ThreeSum.LightBandLookup

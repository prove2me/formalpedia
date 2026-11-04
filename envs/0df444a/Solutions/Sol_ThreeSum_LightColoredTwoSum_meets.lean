-- Prove2me | solution 1 for ThreeSum.LightColoredTwoSum.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:24:44.294934+00:00
-- url     : https://prove2.me/submissions/996d6a07-6f45-431e-9c1d-0271b85a2aa1

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightColoredTwoSum
import Theorems.Thm_ThreeSum_LightColoredTwoSum_lookup_positive_iff
import Theorems.Thm_ThreeSum_LightColoredTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightColoredTwoSum_flag_le_one
import Theorems.Thm_ThreeSum_LightColoredTwoSum_hit_succ
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightBandLookup_result_le
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
attribute [local simp] ThreeSum.LightColoredTwoSum.flag_zero
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightColoredTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightColoredTwoSum
theorem _root_.solution {pMain pLookup pSearch a n b m powers W L U d : ℕ} (bad sign : ℤ)
    (hmain : P[pMain]? = some (body pLookup)) (hlookup : P[pLookup]? = some (LightBandLookup.body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch)) (μ : ℕ → ℤ) (scan target : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + n ≤ lim.space) (hb : b + m ≤ lim.space)
    (hspace : powers + (W + 1) ≤ lim.space) (hword : ((m + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |scan i| ≤ U) (hbad : |bad| ≤ U) (hsign : |sign| ≤ 1) (hvalueWord : 2 * (U : ℤ) + 3 ≤ lim.word)
    (hread : ∀ i < n, μ (a + i) = scan i) (htarget : ∀ j < m, μ (b + j) = target j) (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i < j → j < m → target i < target j) (hL : L ≤ W) (hm : m < 2 ^ L) (hd : d + L + 2 ≤ lim.depth) :
    Meets lim P pMain d [a, n, b, m, powers, L, bad, sign] μ (time n L)
      (fun r ν => r = (flag scan target m n bad sign : ℤ) ∧ ν = μ) :=
  by
  have htargetSorted : ∀ i j, i ≤ j → j < m → target i ≤ target j :=
    by
    intro i j hij hj
    rcases eq_or_lt_of_le hij with rfl | hlt
    · rfl
    · exact (hsorted i j hlt hj).le
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
    refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBandLookup.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBandLookup.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBandLookup.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := n * (LightBandLookup.time L + 200) + 20) (Q := Inv μ a n b m powers L bad sign scan target n)
        (Inv μ a n b m powers L bad sign scan target) n (LightBandLookup.time L + 150) ?start ?round ?done ?bound (hT :=
        by
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
              | (ring_nf; omega))))
      ?after (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, 0, ?_⟩
    simp [update_frame_setLocal]
    change
      frame [(a : ℤ), n, b, m, powers, L, bad, sign, 0, 0] =
        frame ([(a : ℤ), n, b, m, powers, L, bad, sign, 0, 0] ++ [0, 0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨q, r, rfl⟩
    have hRead := hread j hj
    have hprod : |sign * scan j| ≤ U := by
      rw [abs_mul]
      exact (mul_le_mul hsign (hvalues j hj) (abs_nonneg _) (by omega)).trans_eq (one_mul _)
    have hquery : |sign * scan j + bad| ≤ 2 * (U : ℤ) := (abs_add_le _ _).trans (by linarith [hprod, hbad])
    have hQueryBounds := abs_le.mp hquery
    have hProdBounds := abs_le.mp hprod
    have hSignBounds := abs_le.mp hsign
    have hBadBounds := abs_le.mp hbad
    have hc :=
      LightBandLookup.meets (d := d + 1) (x := sign * scan j + bad) hlookup hsearch μ target target hw hb hb hspace
        hword htarget htarget hpowers htargetSorted hL hm (by omega)
    have hflag := flag_le_one scan target m j bad sign
    unfold roundBody
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (sign * scan j + bad) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hRead,
              LightBandLookup.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hRead, LightBandLookup.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hRead, LightBandLookup.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
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
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightBandLookup.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightBandLookup.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBandLookup.time] <;> omega)
      on_goal -1 => (rintro out ν ⟨hout, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν
    have hresult := LightBandLookup.result_le target target m (sign * scan j + bad) htargetSorted
    have hpos := lookup_positive_iff target m (sign * scan j + bad) hsorted
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
        _root_.Light.Ends.iteIffThen ((0 : ℤ) < (LightBandLookup.result target target m (sign * scan j + bad) : ℤ))
          (fun hp => ?_) (fun hn => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hout,
              LightBandLookup.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hout, LightBandLookup.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hout, LightBandLookup.time] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · have hcurrent : ∃ k < m, target k = sign * scan j + bad := hpos.mp (by exact_mod_cast hp)
      have hnext : flag scan target m (j + 1) bad sign = 1 :=
        by
        unfold flag
        rw [if_pos ((hit_succ scan target m j bad sign).mpr (Or.inr hcurrent))]
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen 1 ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                LightBandLookup.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [LightBandLookup.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBandLookup.time] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨by simp, sign * scan j + bad, out, ?_⟩
      simp [update_frame_setLocal, hnext]
    · have hcurrent : ¬∃ k < m, target k = sign * scan j + bad := fun hh => hn (by exact_mod_cast hpos.mpr hh)
      have hnext : flag scan target m (j + 1) bad sign = flag scan target m j bad sign := by
        simp only [flag, hit_succ, or_false, hcurrent]
      refine Ends.skip ⟨by simp, sign * scan j + bad, out, ?_⟩
      simp [update_frame_setLocal, hnext]
  case done => intro σ _ hshape; exact hshape
  case bound =>
    rintro j _ hj _ ⟨q, r, rfl⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨q, r, rfl⟩
    have hf := flag_le_one scan target m n bad sign
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (flag scan target m n bad sign : ℕ) ?_ ?_ ?_
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
    exact ⟨by simp, rfl⟩
end ThreeSum.LightColoredTwoSum

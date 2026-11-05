-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:20:06.346997+00:00
-- url     : https://prove2.me/submissions/b0908248-88fa-4742-9495-b2304e71a941

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_output_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_output_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_digits_low
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_digits_mid
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_digits_full
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_output_succ_low
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_output_succ_mid
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_output_succ_full
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_visits_low_succ
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_visits_mid_succ
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_visits_full_succ
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_visits_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_visits_child0
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_visits_child01
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_codes_child0
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_codes_child01
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_pow_two_even
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_of_sameOutside
import Theorems.Thm_Light_Seg_of_sameOutside
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_04c57512725a2a98
import Definitions.Def_WeightedCache3SUM_Alias_3f3326597d4f4ccd
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.output_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.output_zero
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration
theorem _root_.solution {pEnum W powers : ℕ} (hprog : P[pEnum]? = some (body pEnum)) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers + (2 * W + 1) ≤ lim.space) (hword : ((4 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hcontrol : ((2740 * W + 3000 : ℕ) : ℤ) ≤ lim.word) :
    ∀ N T pref dst : ℕ,
      ∀ μ : ℕ → ℤ,
        N ≤ W →
          T ≤ 2740 * W →
            pref + 4 ^ N ≤ 4 ^ W →
              dst + (codes N T).length ≤ powers →
                Powers μ powers (2 * W) →
                  ∀ d,
                    d + N ≤ lim.depth →
                      Meets lim P pEnum d [N, T, pref, dst, powers] μ (time N T)
                        (fun r μ' =>
                          r = ((codes N T).length : ℤ) ∧
                            Seg μ' dst (output N T pref) ∧ SameOutside μ μ' dst (codes N T).length) :=
  by
  have hpowWord : ((4 ^ W : ℕ) : ℤ) ≤ lim.word :=
    by
    have hn : (4 ^ W : ℕ) ≤ 4 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (show ((4 ^ W : ℕ) : ℤ) ≤ ((4 ^ (W + 1) : ℕ) : ℤ) by exact_mod_cast hn).trans hword
  intro N
  induction N with
  | zero =>
    intro T pref dst μ hN hT hprefix hdst hpowers d hd
    have htime : 300 ≤ 300 * visits 0 T := by simp [visits]
    have hdspace : dst + 1 ≤ lim.space := by simpa [codes] using hdst.trans (by omega)
    have hprefZ : (pref : ℤ) ≤ lim.word := by
      exact (show (pref : ℤ) ≤ ((4 ^ W : ℕ) : ℤ) by exact_mod_cast (show pref ≤ 4 ^ W by omega)).trans hpowWord
    apply Meets.of_body hprog
    unfold body time
    refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simpa using h))
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.storeToThen dst (pref : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, visits]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [visits] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, visits] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, visits]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [visits] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, visits] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp [codes], ?_, ?_⟩
    · simp [output_zero, seg_cons]
    · intro a ha
      simp only [codes, List.length_singleton] at ha
      change Function.update μ dst (pref : ℤ) a = _
      exact Function.update_of_ne (by omega) _ _
  | succ N ih =>
    intro T pref dst μ hN hT hprefix hdst hpowers d hd
    have hNW : N ≤ W := by omega
    have hp4Z : (0 : ℤ) ≤ ((4 ^ N : ℕ) : ℤ) := Int.natCast_nonneg _
    have hp4Int : (0 : ℤ) ≤ (4 : ℤ) ^ N := by positivity
    have he : 4 ^ (N + 1) = 4 ^ N + 4 ^ N + 4 ^ N + 4 ^ N := by rw [pow_succ] <;> omega
    have hprefZ : (pref : ℤ) ≤ lim.word := by
      exact (show (pref : ℤ) ≤ ((4 ^ W : ℕ) : ℤ) by exact_mod_cast (show pref ≤ 4 ^ W by omega)).trans hpowWord
    have hn0le := codes_child0 N T
    have hdst0 : dst + (codes N T).length ≤ powers := by omega
    have hdst0Words : dst + (words N T).length ≤ powers := by simpa using hdst0
    have hprefix0 : pref + 4 ^ N ≤ 4 ^ W := by omega
    have hchild0 := ih T pref dst μ hNW hT hprefix0 hdst0 hpowers (d + 1) (by omega)
    have htime : 300 ≤ 300 * visits (N + 1) T := Nat.mul_le_mul_left 300 (visits_pos _ _)
    have hv0 := visits_child0 N T
    apply Meets.of_body hprog
    unfold body time
    refine Ends.iteLast (fun h => False.elim (by simp at h <;> omega)) (fun _ => ?_)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (N : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, visits]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [visits] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, visits] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      first
      | refine _root_.Light.Ends.callToThen (hchild0 _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hchild0 ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, hv0]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [time, hv0] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, hv0] <;> omega)
      on_goal -1 => (rintro n0 μ1 ⟨hn0, hseg0, hsame0⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hpowers1 : Powers μ1 powers (2 * W) := by
      intro i hi
      rw [hsame0 (powers + i) (Or.inr (by omega))]
      exact hpowers i hi
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.iteIffThen ((T : ℤ) < 1369) (fun hzeroZ => ?_) (fun hposZ => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, hv0]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [time, hv0] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, hv0] <;> omega)
      all_goals
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
    · have hzero : T < 1369 := by omega
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.setToThen ((codes N T).length : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, hn0,
                visits_low_succ hzero]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [time, hn0, visits_low_succ hzero] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, hn0, visits_low_succ hzero] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨by simpa [codes, digits_low hzero, digitCode] using hn0, ?_, ?_⟩
      · simpa [output_succ_low hzero] using hseg0
      · simpa [codes, digits_low hzero, digitCode] using hsame0
    · have hpos : 1369 ≤ T := by omega
      have hv01 := visits_child01 hpos N
      have hn01le := codes_child01 hpos N
      have hdst1 : dst + (codes N T).length + (codes N (T - 1369)).length ≤ powers := by omega
      have hdst1Words : dst + (words N T).length + (words N (T - 1369)).length ≤ powers := by simpa using hdst1
      have hprefix1 : pref + 4 ^ N + 4 ^ N ≤ 4 ^ W := by omega
      have hpowerRead := hpowers1 (2 * N) (by omega)
      rw [pow_two_even] at hpowerRead
      have haddrCast : (powers : ℤ) + 2 * (N : ℤ) = ((powers + 2 * N : ℕ) : ℤ) := by push_cast; rfl
      have hpowerReadZ : μ1 ((powers : ℤ) + 2 * (N : ℤ)).toNat = ((4 ^ N : ℕ) : ℤ) := by
        rw [haddrCast, Int.toNat_natCast, hpowerRead]
      have hargPrefix1 : (pref : ℤ) + μ1 (powers + 2 * N) = ((pref + 4 ^ N : ℕ) : ℤ) := by
        rw [hpowerRead]; push_cast
        rfl
      have hprefixArg1 : (pref : ℤ) + μ1 (powers + 2 * N) ≤ lim.word :=
        by
        rw [hargPrefix1]
        exact
          (show ((pref + 4 ^ N : ℕ) : ℤ) ≤ ((4 ^ W : ℕ) : ℤ) by
                exact_mod_cast (show pref + 4 ^ N ≤ 4 ^ W by omega)).trans
            hpowWord
      have hprefixInt1 : (pref : ℤ) + (4 : ℤ) ^ N ≤ lim.word := by simpa [hpowerRead] using hprefixArg1
      have hreadNonneg : (0 : ℤ) ≤ μ1 (powers + 2 * N) := by rw [hpowerRead]; positivity
      have hreadWord : μ1 (powers + 2 * N) ≤ lim.word :=
        by
        rw [hpowerRead]
        exact
          (show ((4 ^ N : ℕ) : ℤ) ≤ ((4 ^ W : ℕ) : ℤ) by
                exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ 4) hNW)).trans
            hpowWord
      have hchild1 :=
        ih (T - 1369) (pref + 4 ^ N) (dst + (codes N T).length) μ1 hNW (by omega) hprefix1 hdst1 hpowers1 (d + 1)
          (by omega)
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        first
        | refine _root_.Light.Ends.callToThen (hchild1 _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hchild1 ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, hv01, hn0,
                hargPrefix1, hpowerRead, hpowerReadZ]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [time, hv01, hn0, hargPrefix1, hpowerRead, hpowerReadZ] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, hv01, hn0, hargPrefix1, hpowerRead,
                hpowerReadZ] <;> omega)
        on_goal -1 => (rintro n1 μ2 ⟨hn1, hseg1, hsame1⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      have hseg0' : Seg μ2 dst (output N T pref) := hseg0.of_sameOutside hsame1 (Or.inl (by simp))
      have hsame01 : SameOutside μ μ2 dst ((codes N T).length + (codes N (T - 1369)).length) :=
        hsame0.then hsame1 (fun a ha => by constructor <;> omega)
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.iteIffThen ((T : ℤ) < 2740) (fun honeZ => ?_) (fun htwoZ => ?_) ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, hv01]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [time, hv01] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, hv01] <;> omega)
        all_goals
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
      · have hone : T < 2740 := by omega
        have htotalBound : (((codes N T).length + (codes N (T - 1369)).length : ℕ) : ℤ) ≤ lim.word := by
          exact
            (show (((codes N T).length + (codes N (T - 1369)).length : ℕ) : ℤ) ≤ (lim.space : ℤ) by
                  exact_mod_cast (show (codes N T).length + (codes N (T - 1369)).length ≤ lim.space by omega)).trans
              hw
        have htotalWords : (((words N T).length + (words N (T - 1369)).length : ℕ) : ℤ) ≤ lim.word := by
          simpa using htotalBound
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            (repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_))
          refine _root_.Light.Ends.setToThen ((codes N T).length + (codes N (T - 1369)).length : ℕ) ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, hn0, hn1,
                  visits_mid_succ hpos hone]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [time, hn0, hn1, visits_mid_succ hpos hone] <;> first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, hn0, hn1,
                  visits_mid_succ hpos hone] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        refine ⟨?_, ?_, ?_⟩
        · simp [codes, digits_mid hpos hone, digitCode]
        · rw [output_succ_mid hpos hone, seg_append, output_length]
          exact ⟨hseg0', by simpa using hseg1⟩
        · simpa [codes, digits_mid hpos hone, digitCode] using hsame01
      · have htwo : 2740 ≤ T := by omega
        have hcount :
          (codes (N + 1) T).length = (codes N T).length + (codes N (T - 1369)).length + (codes N (T - 2740)).length :=
          by simp [codes, digits_full htwo, digitCode, Nat.add_assoc]
        have hdst2 : dst + (codes N T).length + (codes N (T - 1369)).length + (codes N (T - 2740)).length ≤ powers := by
          omega
        have hdst2Words :
          dst + (words N T).length + (words N (T - 1369)).length + (words N (T - 2740)).length ≤ powers := by
          simpa using hdst2
        have hpowers2 : Powers μ2 powers (2 * W) := by
          intro i hi
          rw [hsame1 (powers + i) (Or.inr (by omega))]
          exact hpowers1 i hi
        have hpowerRead2 := hpowers2 (2 * N) (by omega)
        rw [pow_two_even] at hpowerRead2
        have hpowerRead2Z : μ2 ((powers : ℤ) + 2 * (N : ℤ)).toNat = ((4 ^ N : ℕ) : ℤ) := by
          rw [haddrCast, Int.toNat_natCast, hpowerRead2]
        have hargPrefix2 : (pref : ℤ) + 3 * μ2 (powers + 2 * N) = ((pref + 3 * 4 ^ N : ℕ) : ℤ) := by
          rw [hpowerRead2]
          push_cast; rfl
        have hprefixArg2 : (pref : ℤ) + 3 * μ2 (powers + 2 * N) ≤ lim.word :=
          by
          rw [hargPrefix2]
          exact
            (show ((pref + 3 * 4 ^ N : ℕ) : ℤ) ≤ ((4 ^ W : ℕ) : ℤ) by
                  exact_mod_cast (show pref + 3 * 4 ^ N ≤ 4 ^ W by omega)).trans
              hpowWord
        have hprefixInt2 : (pref : ℤ) + 3 * (4 : ℤ) ^ N ≤ lim.word := by simpa [hpowerRead2] using hprefixArg2
        have hreadNonneg2 : (0 : ℤ) ≤ μ2 (powers + 2 * N) := by rw [hpowerRead2]; positivity
        have hreadTripleWord : 3 * μ2 (powers + 2 * N) ≤ lim.word :=
          by
          rw [hpowerRead2]
          exact
            (show 3 * ((4 ^ N : ℕ) : ℤ) ≤ ((4 ^ W : ℕ) : ℤ) by exact_mod_cast (show 3 * 4 ^ N ≤ 4 ^ W by omega)).trans
              hpowWord
        have hprefix2 : pref + 3 * 4 ^ N + 4 ^ N ≤ 4 ^ W := by omega
        have hchild2 :=
          ih (T - 2740) (pref + 3 * 4 ^ N) (dst + (codes N T).length + (codes N (T - 1369)).length) μ2 hNW (by omega)
            hprefix2 hdst2 hpowers2 (d + 1) (by omega)
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            (repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_))
          first
          | refine _root_.Light.Ends.callToThen (hchild2 _ (by omega)) ?_ ?_ ?_ ?_
          | refine _root_.Light.Ends.callToThen hchild2 ?_ ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time,
                  visits_full_succ htwo, hn0, hn1, hargPrefix2, hpowerRead2, hpowerRead2Z]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [time, visits_full_succ htwo, hn0, hn1, hargPrefix2, hpowerRead2, hpowerRead2Z] <;> first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 => omega
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, visits_full_succ htwo, hn0, hn1,
                  hargPrefix2, hpowerRead2, hpowerRead2Z] <;> omega)
          on_goal -1 => (rintro n2 μ3 ⟨hn2, hseg2, hsame2⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
        have htotalBound :
          (((codes N T).length + (codes N (T - 1369)).length + (codes N (T - 2740)).length : ℕ) : ℤ) ≤ lim.word := by
          exact
            (show
                  (((codes N T).length + (codes N (T - 1369)).length + (codes N (T - 2740)).length : ℕ) : ℤ) ≤
                    (lim.space : ℤ)
                  by
                  exact_mod_cast
                    (show (codes N T).length + (codes N (T - 1369)).length + (codes N (T - 2740)).length ≤ lim.space by
                      omega)).trans
              hw
        have hseg01 : Seg μ2 dst (output N T pref ++ output N (T - 1369) (pref + 4 ^ N)) :=
          by
          rw [seg_append, output_length]
          exact ⟨hseg0', hseg1⟩
        have hseg01' : Seg μ3 dst (output N T pref ++ output N (T - 1369) (pref + 4 ^ N)) :=
          hseg01.of_sameOutside hsame2 (Or.inl (by simp [Nat.add_assoc]))
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            (repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_))
          refine
            _root_.Light.Ends.setToThen
              ((codes N T).length + (codes N (T - 1369)).length + (codes N (T - 2740)).length : ℕ) ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time,
                  visits_full_succ htwo, hn0, hn1, hn2]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [time, visits_full_succ htwo, hn0, hn1, hn2] <;> first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, visits_full_succ htwo, hn0, hn1,
                  hn2] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        refine ⟨by simp [hcount], ?_, ?_⟩
        · rw [output_succ_full htwo, seg_append, List.length_append, output_length, output_length]
          exact ⟨hseg01', by simpa [Nat.add_assoc] using hseg2⟩
        · rw [hcount]
          exact hsame01.then hsame2 (fun a ha => by constructor <;> omega)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration

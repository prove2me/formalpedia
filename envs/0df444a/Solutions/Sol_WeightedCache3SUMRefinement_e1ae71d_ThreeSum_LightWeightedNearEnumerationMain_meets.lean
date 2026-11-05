-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumerationMain.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:22:31.920442+00:00
-- url     : https://prove2.me/submissions/b5be39c8-3ad3-41a8-8e74-26fa401a07ae

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightNearEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightNearEnumerationMain
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
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_branch_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_output_cons
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_output_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_visits_cons
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearEnumeration_mem_digits
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration.branchOutput_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration.output_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearEnumeration.mem_digits
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum
  WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumerationMain
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.WeightedNearEnumeration ThreeSum.LightWeightedNearEnumeration
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumerationMain
theorem _root_.solution {pMain pBranch W powers : ℕ} (hmain : P[pMain]? = some (body pBranch))
    (hbranch : P[pBranch]? = some (branchBody pMain)) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers + (2 * W + 1) ≤ lim.space) (hword : ((4 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hcontrol : ((2740 * W + 3000 : ℕ) : ℤ) ≤ lim.word) :
    ∀ qs : List ℕ,
      ∀ D pref dst caps : ℕ,
        ∀ μ : ℕ → ℤ,
          (∀ q ∈ qs, q < 3) →
            qs.length ≤ W →
              D ≤ 2740 * W →
                pref + 4 ^ qs.length ≤ 4 ^ W →
                  dst + (words qs D).length ≤ powers →
                    dst + (words qs D).length ≤ caps →
                      caps + qs.length ≤ lim.space →
                        Powers μ powers (2 * W) →
                          Seg μ caps (qs.map (fun q => (digitCost q : ℤ))) →
                            ∀ d,
                              d + 2 * qs.length ≤ lim.depth →
                                Meets lim P pMain d [qs.length, D, pref, dst, powers, caps] μ (time qs D)
                                  (fun count μ' =>
                                    count = ((words qs D).length : ℤ) ∧
                                      Seg μ' dst (output qs D pref) ∧ SameOutside μ μ' dst (words qs D).length) :=
  by
  have hpowWord : ((4 ^ W : ℕ) : ℤ) ≤ lim.word :=
    (show ((4 ^ W : ℕ) : ℤ) ≤ ((4 ^ (W + 1) : ℕ) : ℤ) by
          exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 4) (Nat.le_succ W)).trans
      hword
  intro qs
  induction qs with
  | nil =>
    intro D pref dst caps μ hqs hN hD hprefix hdstP hdstC hcspace hpowers hcaps d hd
    simp only [List.length_nil, pow_zero] at hprefix
    have hdspace : dst + 1 ≤ lim.space := by simpa [words] using hdstP.trans (by omega)
    have htime : 900 ≤ 900 * visits [] D := by simp [visits]
    have hprefZ : (pref : ℤ) ≤ lim.word :=
      (show (pref : ℤ) ≤ ((4 ^ W : ℕ) : ℤ) by exact_mod_cast (show pref ≤ 4 ^ W by omega)).trans hpowWord
    apply Meets.of_body hmain
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
    refine ⟨by simp [words], ?_, ?_⟩
    · simp [output, words, code, seg_cons]
    · intro a ha
      simp only [words, List.length_singleton] at ha
      change Function.update μ dst (pref : ℤ) a = _
      exact Function.update_of_ne (by omega) _ _
  | cons q qs ih =>
    intro D pref dst caps μ hqs hN hD hprefix hdstP hdstC hcspace hpowers hcaps d hd
    have hq : q < 3 := hqs q (by simp)
    let qF : Fin 3 := ⟨q, hq⟩
    have hqF : qF.val = q := rfl
    have hlen : (q :: qs).length = qs.length + 1 := rfl
    have htail : ∀ r ∈ qs, r < 3 := fun r hr => hqs r (by simp [hr])
    have hNW : qs.length ≤ W := by simpa using Nat.le_of_succ_le hN
    have htime : 900 ≤ 900 * visits (q :: qs) D := by simp [visits]
    have hv : visits (q :: qs) D = 1 + branchVisits qs D q 0 + branchVisits qs D q 1 + branchVisits qs D q 2 := by
      simpa [hqF] using visits_cons qF qs D
    have hout :
      output (q :: qs) D pref =
        branchOutput qs D pref q 0 ++ branchOutput qs D pref q 1 ++ branchOutput qs D pref q 2 :=
      by simpa [hqF] using output_cons qF qs D pref
    have hcount : (words (q :: qs) D).length = branchCount qs D q 0 + branchCount qs D q 1 + branchCount qs D q 2 :=
      by
      have hh := congrArg List.length hout
      simpa [output_length, branchOutput_length, Nat.add_assoc] using hh
    have he : 4 ^ (qs.length + 1) = 4 ^ qs.length + 4 ^ qs.length + 4 ^ qs.length + 4 ^ qs.length := by
      rw [pow_succ]
      omega
    have hp4 : (0 : ℤ) ≤ ((4 ^ qs.length : ℕ) : ℤ) := Int.natCast_nonneg _
    have hprefix' : pref + 4 ^ (qs.length + 1) ≤ 4 ^ W := by simpa using hprefix
    have hprefZ : (pref : ℤ) ≤ lim.word :=
      (show (pref : ℤ) ≤ ((4 ^ W : ℕ) : ℤ) by exact_mod_cast (show pref ≤ 4 ^ W by omega)).trans hpowWord
    have hcapHead : μ caps = (digitCost q : ℤ) :=
      by
      have hh := hcaps 0 (by simp)
      simpa using hh
    have hcapTail : Seg μ (caps + 1) (qs.map (fun q => (digitCost q : ℤ))) :=
      by
      have hh : μ caps = (digitCost q : ℤ) ∧ Seg μ (caps + 1) (qs.map (fun q => (digitCost q : ℤ))) := by
        simpa [seg_cons] using hcaps
      exact hh.2
    have hdst0P : dst + branchCount qs D q 0 ≤ powers := by omega
    have hdst0C : dst + branchCount qs D q 0 ≤ caps := by omega
    have hprefix0 : pref + digitCode (0 : Fin 3).val * 4 ^ qs.length + 4 ^ qs.length ≤ 4 ^ W := by
      norm_num [digitCode]
      omega
    have hchild0 :
      Allowed q 0 D →
        Meets lim P pMain (d + 2)
          [qs.length, D - (digitCost q - digitCost 0), pref + digitCode (0 : Fin 3).val * 4 ^ qs.length, dst, powers,
            caps + 1]
          μ (time qs (D - (digitCost q - digitCost 0)))
          (fun count μ' =>
            count = ((words qs (D - (digitCost q - digitCost 0))).length : ℤ) ∧
              Seg μ' dst
                  (output qs (D - (digitCost q - digitCost 0)) (pref + digitCode (0 : Fin 3).val * 4 ^ qs.length)) ∧
                SameOutside μ μ' dst (words qs (D - (digitCost q - digitCost 0))).length) :=
      by
      intro ha
      have hbudget : ((D - (digitCost q - digitCost 0) : ℕ) : ℤ) = (D : ℤ) - ((digitCost q : ℤ) - (digitCost 0 : ℤ)) :=
        by
        unfold Allowed at ha
        omega
      have hc : branchCount qs D q 0 = (words qs (D - (digitCost q - digitCost 0))).length := by simp [branchCount, ha]
      have child :=
        ih (D - (digitCost q - digitCost 0)) (pref + digitCode (0 : Fin 3).val * 4 ^ qs.length) dst (caps + 1) μ htail
          hNW (by omega) hprefix0 (by simpa [hc] using hdst0P) (by rw [← hc]; omega) (by simp at hcspace ⊢; omega)
          hpowers hcapTail (d + 2) (by simp at hd ⊢; omega)
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, hbudget] using child
    have hb0 :=
      branch_meets (W := W) (N := qs.length) (D := D) (pref := pref) (dst := dst) (powers := powers) (caps := caps + 1)
        (d := d + 1) hbranch qs qF (0 : Fin 3) μ hw hspace hword hcontrol hpowers hNW rfl hD (by omega)
        (by simp at hcspace; omega) hprefix0 (by simpa [hqF] using hchild0) (by simp at hd; omega)
    norm_num [hqF] at hb0
    apply Meets.of_body hmain
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
      refine _root_.Light.Ends.setToThen (qs.length : ℕ) ?_ ?_ ?_
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
      refine _root_.Light.Ends.setToThen (digitCost q : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcapHead, visits]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hcapHead, visits] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcapHead, visits] <;> omega)
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
      | refine _root_.Light.Ends.callToThen (hb0 _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hb0 ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, branchTime,
              hv, hqF, hcapHead]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [time, branchTime, hv, hqF, hcapHead] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, branchTime, hv, hqF, hcapHead] <;> omega)
      on_goal -1 => (rintro n0 μ1 ⟨hn0, hseg0, hsame0⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hpowers1 : Powers μ1 powers (2 * W) := by
      intro i hi
      rw [hsame0 (powers + i) (Or.inr (by omega))]
      exact hpowers i hi
    have hcapTail1 : Seg μ1 (caps + 1) (qs.map (fun q => (digitCost q : ℤ))) :=
      hcapTail.of_sameOutside hsame0 (Or.inr (by omega))
    have hdst1P : dst + branchCount qs D q 0 + branchCount qs D q 1 ≤ powers := by omega
    have hdst1C : dst + branchCount qs D q 0 + branchCount qs D q 1 ≤ caps := by omega
    have hprefix1 : pref + digitCode (1 : Fin 3).val * 4 ^ qs.length + 4 ^ qs.length ≤ 4 ^ W := by
      norm_num [digitCode]
      omega
    have hchild1 :
      Allowed q 1 D →
        Meets lim P pMain (d + 2)
          [qs.length, D - (digitCost q - digitCost 1), pref + digitCode (1 : Fin 3).val * 4 ^ qs.length,
            dst + branchCount qs D q 0, powers, caps + 1]
          μ1 (time qs (D - (digitCost q - digitCost 1)))
          (fun count μ' =>
            count = ((words qs (D - (digitCost q - digitCost 1))).length : ℤ) ∧
              Seg μ' (dst + branchCount qs D q 0)
                  (output qs (D - (digitCost q - digitCost 1)) (pref + digitCode (1 : Fin 3).val * 4 ^ qs.length)) ∧
                SameOutside μ1 μ' (dst + branchCount qs D q 0) (words qs (D - (digitCost q - digitCost 1))).length) :=
      by
      intro ha
      have hbudget : ((D - (digitCost q - digitCost 1) : ℕ) : ℤ) = (D : ℤ) - ((digitCost q : ℤ) - (digitCost 1 : ℤ)) :=
        by
        unfold Allowed at ha
        omega
      have hc : branchCount qs D q 1 = (words qs (D - (digitCost q - digitCost 1))).length := by simp [branchCount, ha]
      have child :=
        ih (D - (digitCost q - digitCost 1)) (pref + digitCode (1 : Fin 3).val * 4 ^ qs.length)
          (dst + branchCount qs D q 0) (caps + 1) μ1 htail hNW (by omega) hprefix1 (by simpa [hc] using hdst1P)
          (by rw [← hc]; omega) (by simp at hcspace ⊢; omega) hpowers1 hcapTail1 (d + 2) (by simp at hd ⊢; omega)
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, hbudget] using child
    have hb1 :=
      branch_meets (W := W) (N := qs.length) (D := D) (pref := pref) (dst := dst + branchCount qs D q 0) (powers :=
        powers) (caps := caps + 1) (d := d + 1) hbranch qs qF (1 : Fin 3) μ1 hw hspace hword hcontrol hpowers1 hNW rfl
        hD (by omega) (by simp at hcspace; omega) hprefix1 (by simpa [hqF] using hchild1) (by simp at hd; omega)
    norm_num [hqF] at hb1
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
      | refine _root_.Light.Ends.callToThen (hb1 _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hb1 ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, branchTime,
              hv, hqF, hn0]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [time, branchTime, hv, hqF, hn0] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, branchTime, hv, hqF, hn0] <;> omega)
      on_goal -1 => (rintro n1 μ2 ⟨hn1, hseg1, hsame1⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hpowers2 : Powers μ2 powers (2 * W) := by
      intro i hi
      rw [hsame1 (powers + i) (Or.inr (by omega))]
      exact hpowers1 i hi
    have hcapTail2 : Seg μ2 (caps + 1) (qs.map (fun q => (digitCost q : ℤ))) :=
      hcapTail1.of_sameOutside hsame1 (Or.inr (by omega))
    have hdst2P : dst + branchCount qs D q 0 + branchCount qs D q 1 + branchCount qs D q 2 ≤ powers := by omega
    have hdst2C : dst + branchCount qs D q 0 + branchCount qs D q 1 + branchCount qs D q 2 ≤ caps := by omega
    have hprefix2 : pref + digitCode (2 : Fin 3).val * 4 ^ qs.length + 4 ^ qs.length ≤ 4 ^ W := by
      norm_num [digitCode]
      omega
    have hchild2 :
      Allowed q 2 D →
        Meets lim P pMain (d + 2)
          [qs.length, D - (digitCost q - digitCost 2), pref + digitCode (2 : Fin 3).val * 4 ^ qs.length,
            dst + branchCount qs D q 0 + branchCount qs D q 1, powers, caps + 1]
          μ2 (time qs (D - (digitCost q - digitCost 2)))
          (fun count μ' =>
            count = ((words qs (D - (digitCost q - digitCost 2))).length : ℤ) ∧
              Seg μ' (dst + branchCount qs D q 0 + branchCount qs D q 1)
                  (output qs (D - (digitCost q - digitCost 2)) (pref + digitCode (2 : Fin 3).val * 4 ^ qs.length)) ∧
                SameOutside μ2 μ' (dst + branchCount qs D q 0 + branchCount qs D q 1)
                  (words qs (D - (digitCost q - digitCost 2))).length) :=
      by
      intro ha
      have hbudget : ((D - (digitCost q - digitCost 2) : ℕ) : ℤ) = (D : ℤ) - ((digitCost q : ℤ) - (digitCost 2 : ℤ)) :=
        by
        unfold Allowed at ha
        omega
      have hc : branchCount qs D q 2 = (words qs (D - (digitCost q - digitCost 2))).length := by simp [branchCount, ha]
      have child :=
        ih (D - (digitCost q - digitCost 2)) (pref + digitCode (2 : Fin 3).val * 4 ^ qs.length)
          (dst + branchCount qs D q 0 + branchCount qs D q 1) (caps + 1) μ2 htail hNW (by omega) hprefix2
          (by simpa [hc] using hdst2P) (by rw [← hc]; omega) (by simp at hcspace ⊢; omega) hpowers2 hcapTail2 (d + 2)
          (by simp at hd ⊢; omega)
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, hbudget] using child
    have hb2 :=
      branch_meets (W := W) (N := qs.length) (D := D) (pref := pref) (dst :=
        dst + branchCount qs D q 0 + branchCount qs D q 1) (powers := powers) (caps := caps + 1) (d := d + 1) hbranch qs
        qF (2 : Fin 3) μ2 hw hspace hword hcontrol hpowers2 hNW rfl hD (by omega) (by simp at hcspace; omega) hprefix2
        (by simpa [hqF] using hchild2) (by simp at hd; omega)
    norm_num [hqF] at hb2
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
      | refine _root_.Light.Ends.callToThen (hb2 _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hb2 ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, branchTime,
              hv, hqF, hn0, hn1]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [time, branchTime, hv, hqF, hn0, hn1] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, branchTime, hv, hqF, hn0, hn1] <;> omega)
      on_goal -1 => (rintro n2 μ3 ⟨hn2, hseg2, hsame2⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have htotal : ((branchCount qs D q 0 + branchCount qs D q 1 + branchCount qs D q 2 : ℕ) : ℤ) ≤ lim.word :=
      (show ((branchCount qs D q 0 + branchCount qs D q 1 + branchCount qs D q 2 : ℕ) : ℤ) ≤ (lim.space : ℤ) by
            exact_mod_cast
              (show branchCount qs D q 0 + branchCount qs D q 1 + branchCount qs D q 2 ≤ lim.space by omega)).trans
        hw
    have hseg0' : Seg μ2 dst (branchOutput qs D pref q 0) := hseg0.of_sameOutside hsame1 (Or.inl (by simp))
    have hseg01 : Seg μ2 dst (branchOutput qs D pref q 0 ++ branchOutput qs D pref q 1) :=
      by
      rw [seg_append, branchOutput_length]
      exact ⟨hseg0', hseg1⟩
    have hseg01' : Seg μ3 dst (branchOutput qs D pref q 0 ++ branchOutput qs D pref q 1) :=
      hseg01.of_sameOutside hsame2 (Or.inl (by simp [Nat.add_assoc]))
    have hsame01 : SameOutside μ μ2 dst (branchCount qs D q 0 + branchCount qs D q 1) :=
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
      refine
        _root_.Light.Ends.setToThen (branchCount qs D q 0 + branchCount qs D q 1 + branchCount qs D q 2 : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, branchTime,
              hv, hn0, hn1, hn2]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [time, branchTime, hv, hn0, hn1, hn2] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, branchTime, hv, hn0, hn1, hn2] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp [hcount], ?_, ?_⟩
    · rw [hout, seg_append, List.length_append, branchOutput_length, branchOutput_length]
      exact ⟨hseg01', by simpa [Nat.add_assoc] using hseg2⟩
    · rw [hcount]
      exact hsame01.then hsame2 (fun a ha => by constructor <;> omega)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumerationMain

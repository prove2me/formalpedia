-- Prove2me | solution 1 for ThreeSum.LightTernaryNearEnumeration.branch_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:41:11.074798+00:00
-- url     : https://prove2.me/submissions/6ec0c9f9-b6a9-4fb0-9ab0-2ff0e700ed2e

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_branchOutput_length
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_pow_two_even
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
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
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.LightTernaryNearEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryNearEnumeration.branchOutput_length
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryNearEnumeration
theorem _root_.solution {pBranch pSelf W N D pref dst powers caps d : ℕ} (hprog : P[pBranch]? = some (branchBody pSelf))
    (qs : List ℕ) (q r : Fin 3) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers + (2 * W + 1) ≤ lim.space) (hword : ((4 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers (2 * W)) (hN : N ≤ W) (hlen : qs.length = N) (hDmax : D ≤ 2 * W) (hdst : dst ≤ lim.space)
    (hcaps : caps ≤ lim.space) (hpref : pref + digitCode r.val * 4 ^ N + 4 ^ N ≤ 4 ^ W)
    (hChild :
      Allowed q.val r.val D →
        Meets lim P pSelf (d + 1) [N, D - (q.val - r.val), pref + digitCode r.val * 4 ^ N, dst, powers, caps] μ
          (time qs (D - (q.val - r.val)))
          (fun count μ' =>
            count = ((words qs (D - (q.val - r.val))).length : ℤ) ∧
              Seg μ' dst (output qs (D - (q.val - r.val)) (pref + digitCode r.val * 4 ^ N)) ∧
                SameOutside μ μ' dst (words qs (D - (q.val - r.val))).length))
    (hd : d + 1 ≤ lim.depth) :
    Meets lim P pBranch d [N, D, pref, dst, powers, caps, q.val, r.val] μ (branchTime qs D q.val r.val)
      (fun count μ' =>
        count = (branchCount qs D q.val r.val : ℤ) ∧
          Seg μ' dst (branchOutput qs D pref q.val r.val) ∧ SameOutside μ μ' dst (branchCount qs D q.val r.val)) :=
  by
  have hpow := hpowers (2 * N) (by omega)
  rw [ThreeSum.LightTernaryEnumeration.pow_two_even] at hpow
  have haddr : ((powers : ℤ) + 2 * (N : ℤ)).toNat = powers + 2 * N := by
    rw [show (2 : ℤ) * (N : ℤ) = ((2 * N : ℕ) : ℤ) by push_cast; rfl, ← Nat.cast_add, Int.toNat_natCast]
  have hpowerNonneg : (0 : ℤ) ≤ μ (powers + 2 * N) := by rw [hpow]; positivity
  have hpowWord : ((4 ^ W : ℕ) : ℤ) ≤ lim.word :=
    (show ((4 ^ W : ℕ) : ℤ) ≤ ((4 ^ (W + 1) : ℕ) : ℤ) by
          exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 4) (Nat.le_succ W)).trans
      hword
  have htritWord : 3 ≤ lim.word :=
    by
    have h4 : 4 ^ 1 ≤ 4 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hh : (4 : ℤ) ≤ ((4 ^ (W + 1) : ℕ) : ℤ) := by exact_mod_cast h4
    omega
  have hpowerWord : μ (powers + 2 * N) ≤ lim.word := by
    rw [hpow]
    exact
      (show ((4 ^ N : ℕ) : ℤ) ≤ ((4 ^ W : ℕ) : ℤ) by exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 4) hN).trans
        hpowWord
  have harg : (pref : ℤ) + (digitCode r.val : ℤ) * μ (powers + 2 * N) = ((pref + digitCode r.val * 4 ^ N : ℕ) : ℤ) := by
    rw [hpow]; push_cast; rfl
  have hargWord : ((pref + digitCode r.val * 4 ^ N : ℕ) : ℤ) ≤ lim.word :=
    (show ((pref + digitCode r.val * 4 ^ N : ℕ) : ℤ) ≤ ((4 ^ W : ℕ) : ℤ) by
          exact_mod_cast (show pref + digitCode r.val * 4 ^ N ≤ 4 ^ W by omega)).trans
      hpowWord
  have hprodWord : (digitCode r.val : ℤ) * μ (powers + 2 * N) ≤ lim.word :=
    by
    rw [hpow]
    exact
      (show (digitCode r.val : ℤ) * ((4 ^ N : ℕ) : ℤ) ≤ ((4 ^ W : ℕ) : ℤ) by
            exact_mod_cast (show digitCode r.val * 4 ^ N ≤ 4 ^ W by omega)).trans
        hpowWord
  have hprodNonneg : 0 ≤ (digitCode r.val : ℤ) * μ (powers + 2 * N) := by positivity
  apply Meets.of_body hprog
  unfold branchBody branchTime
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.iteIffThen ((r.val : ℤ) ≤ (q.val : ℤ)) (fun hle => ?_) (fun hnle => ?_) ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, branchVisits, time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [branchVisits, time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, branchVisits, time] <;> omega)
    all_goals
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_
  · have hrq : r.val ≤ q.val := by exact_mod_cast hle
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.iteIffThen ((q.val : ℤ) - (r.val : ℤ) ≤ (D : ℤ)) (fun hD => ?_) (fun hnD => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, branchVisits, time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [branchVisits, time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, branchVisits, time] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · have hallow : Allowed q.val r.val D := by unfold Allowed; omega
      have hbudget : (D : ℤ) - ((q.val : ℤ) - (r.val : ℤ)) = ((D - (q.val - r.val) : ℕ) : ℤ) := by omega
      have hc := hChild hallow
      have hbranch : branchVisits qs D q.val r.val = visits qs (D - (q.val - r.val)) := by simp [branchVisits, hallow]
      fin_cases r
      all_goals norm_num [digitCode] at harg hargWord hprodWord hprodNonneg hc hpref hbranch hbudget hallow
      · focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.iteIffThen ((0 : ℤ) = 2) (fun he => ?_) (fun hne => ?_) ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbranch, time]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hbranch, time] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbranch, time] <;> omega)
          all_goals
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_
        · exfalso; norm_num at he
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
                    _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbranch, time]
                  first
                  | omega
                  | (ring_nf; omega))
              | omega
              |
                (simp [hbranch, time] <;>
                    first
                    | omega
                    | (ring_nf; omega))
            on_goal -1 =>
              ( (try have := _root_.Light.Std.space_le (by assumption))
                (try have := _root_.Light.Std.const_le (by assumption))
                simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbranch, time] <;> omega)
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
                    _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbranch, time,
                    hbudget, haddr, hpow, harg]
                  first
                  | omega
                  | (ring_nf; omega))
              | omega
              |
                (simp [hbranch, time, hbudget, haddr, hpow, harg] <;>
                    first
                    | omega
                    | (ring_nf; omega))
            on_goal -1 => omega
            on_goal -1 =>
              ( (try have := _root_.Light.Std.space_le (by assumption))
                (try have := _root_.Light.Std.const_le (by assumption))
                simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbranch, time, hbudget, haddr, hpow,
                    harg] <;>
                  omega)
            on_goal -1 => (rintro count μ' ⟨hr, hseg, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
          exact
            ⟨by simpa [branchCount, hallow] using hr, by simpa [branchOutput, hallow, hlen, digitCode] using hseg, by
              simpa [branchCount, hallow] using hkeep⟩
      · focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.iteIffThen ((1 : ℤ) = 2) (fun he => ?_) (fun hne => ?_) ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbranch, time]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hbranch, time] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbranch, time] <;> omega)
          all_goals
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_
        · exfalso; norm_num at he
        · focus
            ((first
                | refine _root_.Light.Ends.seqSelf ?_
                | refine _root_.Light.Ends.skipLast ?_);
              repeat
                with_unfolding_none
                  first
                  | refine _root_.Light.Ends.seqAssoc ?_
                  | refine _root_.Light.Ends.skipThen ?_)
            refine _root_.Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_
            on_goal -1 =>
              first
              | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                    _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbranch, time]
                  first
                  | omega
                  | (ring_nf; omega))
              | omega
              |
                (simp [hbranch, time] <;>
                    first
                    | omega
                    | (ring_nf; omega))
            on_goal -1 =>
              ( (try have := _root_.Light.Std.space_le (by assumption))
                (try have := _root_.Light.Std.const_le (by assumption))
                simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbranch, time] <;> omega)
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
                    _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbranch, time,
                    hbudget, haddr, hpow, harg]
                  first
                  | omega
                  | (ring_nf; omega))
              | omega
              |
                (simp [hbranch, time, hbudget, haddr, hpow, harg] <;>
                    first
                    | omega
                    | (ring_nf; omega))
            on_goal -1 => omega
            on_goal -1 =>
              ( (try have := _root_.Light.Std.space_le (by assumption))
                (try have := _root_.Light.Std.const_le (by assumption))
                simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbranch, time, hbudget, haddr, hpow,
                    harg] <;>
                  omega)
            on_goal -1 => (rintro count μ' ⟨hr, hseg, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
          exact
            ⟨by simpa [branchCount, hallow] using hr, by simpa [branchOutput, hallow, hlen, digitCode] using hseg, by
              simpa [branchCount, hallow] using hkeep⟩
      · focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.iteIffThen ((2 : ℤ) = 2) (fun he => ?_) (fun hne => ?_) ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbranch, time]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hbranch, time] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbranch, time] <;> omega)
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
            refine _root_.Light.Ends.setToThen (3 : ℕ) ?_ ?_ ?_
            on_goal -1 =>
              first
              | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                    _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbranch, time]
                  first
                  | omega
                  | (ring_nf; omega))
              | omega
              |
                (simp [hbranch, time] <;>
                    first
                    | omega
                    | (ring_nf; omega))
            on_goal -1 =>
              ( (try have := _root_.Light.Std.space_le (by assumption))
                (try have := _root_.Light.Std.const_le (by assumption))
                simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbranch, time] <;> omega)
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
                    _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbranch, time,
                    hbudget, haddr, hpow, harg]
                  first
                  | omega
                  | (ring_nf; omega))
              | omega
              |
                (simp [hbranch, time, hbudget, haddr, hpow, harg] <;>
                    first
                    | omega
                    | (ring_nf; omega))
            on_goal -1 => omega
            on_goal -1 =>
              ( (try have := _root_.Light.Std.space_le (by assumption))
                (try have := _root_.Light.Std.const_le (by assumption))
                simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbranch, time, hbudget, haddr, hpow,
                    harg] <;>
                  omega)
            on_goal -1 => (rintro count μ' ⟨hr, hseg, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
          exact
            ⟨by simpa [branchCount, hallow] using hr, by simpa [branchOutput, hallow, hlen, digitCode] using hseg, by
              simpa [branchCount, hallow] using hkeep⟩
        · exfalso; exact hne rfl
    · have hallow : ¬Allowed q.val r.val D := by unfold Allowed; omega
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
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, branchVisits,
                hallow, time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [branchVisits, hallow, time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, branchVisits, hallow, time] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      exact ⟨by simp [branchCount, hallow], by simp [branchOutput, hallow, Seg], SameOn.refl⟩
  · have hallow : ¬Allowed q.val r.val D := by unfold Allowed; omega
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
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, branchVisits,
              hallow, time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [branchVisits, hallow, time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, branchVisits, hallow, time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp [branchCount, hallow], by simp [branchOutput, hallow, Seg], SameOn.refl⟩
end ThreeSum.LightTernaryNearEnumeration

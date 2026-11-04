-- Prove2me | solution 1 for ThreeSum.LightTernaryFrozenQuery.branches_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:57.764853+00:00
-- url     : https://prove2.me/submissions/a76ab27e-ae6b-48d7-9a41-49cd186b358d

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQuery
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryBranches
import Theorems.Thm_Light_Limits_Addr_abs_le
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
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
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
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light ThreeSum.TernaryQuery
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryFrozenQuery
theorem _root_.solution {pSelf d : ℕ}
    (N K rank cut bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ) (code c0 c1 : ℤ)
    (q : Fin 3) (f : Fin 3 → ℤ) (t : Fin 3 → ℕ) (μ : ℕ → ℤ)
    (hargs :
      ∀
        x ∈
          preparedInputs N K rank cut code bankCodes bankCount bankValues nearCodes nearCount nearValues powers L q c0
            c1,
        |x| ≤ lim.word)
    (hword : 4 * (max (|f 0|) (max (|f 1|) (|f 2|))) + 3 ≤ lim.word) (hrank : q.val ≤ rank) (hd : d + 1 ≤ lim.depth)
    (hchild :
      ∀ r : Fin 3,
        r ≤ q →
          Meets lim P pSelf (d + 1)
            (inputs N K (rank - (q.val - r.val)) cut (if r = 0 then c0 else if r = 1 then c1 else code) bankCodes
              bankCount bankValues nearCodes nearCount nearValues powers L)
            μ (t r) (fun v μ' => v = f r ∧ μ' = μ)) :
    Ends lim P d (branches pSelf)
      ⟨frame
          (preparedInputs N K rank cut code bankCodes bankCount bankValues nearCodes nearCount nearValues powers L q c0
            c1),
        μ⟩
      (t 0 + t 1 + t 2 + 200) (fun σ => σ.loc 0 = inverseDigit f q ∧ σ.mem = μ) :=
  by
  have ha (x : ℤ)
    (hx :
      x ∈
        preparedInputs N K rank cut code bankCodes bankCount bankValues nearCodes nearCount nearValues powers L q c0
          c1) :=
    abs_le.mp (hargs x hx)
  have hN := ha N (by simp [preparedInputs, inputs])
  have hK := ha K (by simp [preparedInputs, inputs])
  have hR := ha rank (by simp [preparedInputs, inputs])
  have hT := ha cut (by simp [preparedInputs, inputs])
  have hC := ha code (by simp [preparedInputs, inputs])
  have hBC := ha bankCodes (by simp [preparedInputs, inputs])
  have hBN := ha bankCount (by simp [preparedInputs, inputs])
  have hBV := ha bankValues (by simp [preparedInputs, inputs])
  have hNC := ha nearCodes (by simp [preparedInputs, inputs])
  have hNN := ha nearCount (by simp [preparedInputs, inputs])
  have hNV := ha nearValues (by simp [preparedInputs, inputs])
  have hP := ha powers (by simp [preparedInputs, inputs])
  have hL := ha L (by simp [preparedInputs, inputs])
  have hC0 := ha c0 (by simp [preparedInputs, inputs])
  have hC1 := ha c1 (by simp [preparedInputs, inputs])
  have hf0 := abs_le.mp (le_max_left (|f 0|) (max (|f 1|) (|f 2|)))
  have hf1 := abs_le.mp ((le_max_left (|f 1|) (|f 2|)).trans (le_max_right (|f 0|) (max (|f 1|) (|f 2|))))
  have hf2 := abs_le.mp ((le_max_right (|f 1|) (|f 2|)).trans (le_max_right (|f 0|) (max (|f 1|) (|f 2|))))
  have hm : 0 ≤ max (|f 0|) (max (|f 1|) (|f 2|)) := (abs_nonneg (f 0)).trans (le_max_left _ _)
  have hcast (a : ℕ) (ha : a ≤ rank) : (rank : ℤ) - (a : ℤ) = ((rank - a : ℕ) : ℤ) := by omega
  have hdropFirst (a : ℕ) (ha : a ≤ q.val) := hcast a (ha.trans hrank)
  unfold branches childArgs preparedInputs inputs
  fin_cases q
  · have hc := hchild 0 (by decide)
    simp [inputs] at hc
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.iteIffThen ((0 : ℤ) = 0) (fun he => ?_) (fun hn => ?_) ?_ ?_
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
        first
        | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, inputs]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [inputs] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, inputs] <;> omega)
        on_goal -1 => (rintro v μ' ⟨hv, hm⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      exact ⟨by simpa [inverseDigit] using hv, hm⟩
    · exfalso; exact hn rfl
  · have hc0 := hchild 0 (by decide)
    have hc1 := hchild 1 (by decide)
    norm_num [inputs] at hc0 hc1 hrank
    have hdrop := hdropFirst 1 (by decide)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.iteIffThen ((1 : ℤ) = 0) (fun he => ?_) (fun hn => ?_) ?_ ?_
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
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · exfalso; omega
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.iteIffThen ((1 : ℤ) = 1) (fun he => ?_) (fun hn => ?_) ?_ ?_
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
          first
          | refine _root_.Light.Ends.callToThen (hc0 _ (by omega)) ?_ ?_ ?_ ?_
          | refine _root_.Light.Ends.callToThen hc0 ?_ ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hdrop]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hdrop] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 => omega
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdrop] <;> omega)
          on_goal -1 => (rintro v0 μ0 ⟨hv0, hm0⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
        subst μ0
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
          | refine _root_.Light.Ends.callToThen (hc1 _ (by omega)) ?_ ?_ ?_ ?_
          | refine _root_.Light.Ends.callToThen hc1 ?_ ?_ ?_ ?_
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
          on_goal -1 => omega
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
          on_goal -1 => (rintro v1 μ1 ⟨hv1, hm1⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
        subst μ1
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.setToThen (f 1 - f 0) ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hv0, hv1]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hv0, hv1] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hv0, hv1] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        exact ⟨by simp [inverseDigit], rfl⟩
      · exfalso; exact hn rfl
  · have hc0 := hchild 0 (by decide)
    have hc1 := hchild 1 (by decide)
    have hc2 := hchild 2 (by decide)
    norm_num [inputs] at hc0 hc1 hc2 hrank
    have hdrop1 := hdropFirst 1 (by decide)
    have hdrop2 := hdropFirst 2 (by decide)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.iteIffThen ((2 : ℤ) = 0) (fun he => ?_) (fun hn => ?_) ?_ ?_
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
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · exfalso; omega
    · focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.iteIffThen ((2 : ℤ) = 1) (fun he => ?_) (fun hn => ?_) ?_ ?_
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
        all_goals
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_
      · exfalso; omega
      · focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          first
          | refine _root_.Light.Ends.callToThen (hc0 _ (by omega)) ?_ ?_ ?_ ?_
          | refine _root_.Light.Ends.callToThen hc0 ?_ ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hdrop2]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hdrop2] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 => omega
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdrop2] <;> omega)
          on_goal -1 => (rintro v0 μ0 ⟨hv0, hm0⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
        subst μ0
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
          | refine _root_.Light.Ends.callToThen (hc1 _ (by omega)) ?_ ?_ ?_ ?_
          | refine _root_.Light.Ends.callToThen hc1 ?_ ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hdrop1]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hdrop1] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 => omega
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdrop1] <;> omega)
          on_goal -1 => (rintro v1 μ1 ⟨hv1, hm1⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
        subst μ1
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
          | refine _root_.Light.Ends.callToThen (hc2 _ (by omega)) ?_ ?_ ?_ ?_
          | refine _root_.Light.Ends.callToThen hc2 ?_ ?_ ?_ ?_
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
          on_goal -1 => omega
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
          on_goal -1 => (rintro v2 μ2 ⟨hv2, hm2⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
        subst μ2
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.setToThen (f 2 - 2 * f 1 + f 0) ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hv0, hv1, hv2]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hv0, hv1, hv2] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hv0, hv1, hv2] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        exact ⟨by simp [inverseDigit], rfl⟩
end ThreeSum.LightTernaryFrozenQuery

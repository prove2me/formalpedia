-- Prove2me | solution 1 for ThreeSum.LightTernaryMomentRow.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:25.604187+00:00
-- url     : https://prove2.me/submissions/d45a4dc0-1534-40a1-842f-7fddce0f1dc5

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentGather
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentRow
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_target
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryMomentGather_meets
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
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_prodCircuits
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_sumCircuits
attribute [local simp] ThreeSum.LightMomentZeroDetector.atoms_target
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryMomentRow
open Light FiniteMomentZeroDetector
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryMomentRow
namespace Procs
theorem _root_.solution {H pMain : ℕ} (S : Procs H P pMain) {μ : ℕ → ℤ}
    {record originalA originalCount matrix count row scratch position U t : ℕ} (a : ℤ) (v w : Fin t → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hr : row < count) (hpos : position < originalCount)
    (hrecord : record + 3 ≤ scratch) (hAarray : originalA + originalCount ≤ scratch)
    (hmatrix : matrix + (2 * H + 1) * count ≤ scratch) (hspace : scratch + (2 * H + 1) ≤ lim.space)
    (hposition : μ record = (position : ℤ)) (hAread : μ (originalA + position) = a) (ha : |a| ≤ (U : ℤ))
    (hword : max (U : ℤ) (LightMomentDeterminant.wordBound U H) ≤ lim.word) (hv : Function.Injective v)
    (hweights : ∀ s, w s ≠ 0) (ht : t ≤ H) (hmabs : ∀ k ≤ 2 * H, |moment v w k| ≤ (U : ℤ))
    (hm : ∀ k ≤ 2 * H, μ (matrix + k * count + row) = moment v w k) :
    Meets lim P pMain d [record, originalA, originalCount, matrix, count, row, scratch] μ (time H)
      (fun r ν => r = (if ∃ s, v s = a then 1 else 0 : ℤ) ∧ Kept μ ν scratch) :=
  by
  classical
  have hU : (U : ℤ) ≤ lim.word := (le_max_left _ _).trans hword
  have hdet : LightMomentDeterminant.wordBound (U : ℤ) H ≤ lim.word := (le_max_right _ _).trans hword
  have hb := abs_le.mp ha
  have hpword : (position : ℤ) ≤ lim.word :=
    by
    have hh : position ≤ lim.space := by omega
    exact (Int.ofNat_le.mpr hh).trans hw
  apply Meets.of_body S.main
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
    refine _root_.Light.Ends.setToThen (position : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hposition, LightTernaryMomentGather.time,
            LightMomentDeterminant.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hposition, LightTernaryMomentGather.time, LightMomentDeterminant.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hposition, LightTernaryMomentGather.time,
            LightMomentDeterminant.time] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hAreadCast : μ (((originalA : ℤ) + (position : ℤ)).toNat) = a := by
    simpa only [Light.toNat_natCast_add_natCast] using hAread
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen a ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hAreadCast, LightTernaryMomentGather.time,
            LightMomentDeterminant.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hAreadCast, LightTernaryMomentGather.time, LightMomentDeterminant.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hAreadCast, LightTernaryMomentGather.time,
            LightMomentDeterminant.time] <;>
          omega)
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightTernaryMomentGather.meets (d := d + 1) (μ := μ) (matrix := matrix) (count := count) (row := row)
              (scratch := scratch) (terms := 2 * H + 1) (U := U) S.gather (fun k => moment v w k) hw hr hmatrix hspace
              (fun k hk => hm k (by omega)) (fun k hk => hmabs k (by omega)) hU)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightTernaryMomentGather.meets (d := d + 1) (μ := μ) (matrix := matrix) (count := count) (row := row)
            (scratch := scratch) (terms := 2 * H + 1) (U := U) S.gather (fun k => moment v w k) hw hr hmatrix hspace
            (fun k hk => hm k (by omega)) (fun k hk => hmabs k (by omega)) hU)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryMomentGather.time,
            LightMomentDeterminant.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryMomentGather.time, LightMomentDeterminant.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryMomentGather.time,
            LightMomentDeterminant.time] <;>
          omega)
    on_goal -1 => (rintro r ν ⟨hgather, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hread : ∀ k ≤ 2 * H, ν (scratch + k) = moment v w k := fun k hk => hgather k (by omega)
  have hbound : ∀ k ≤ 2 * H, |ν (scratch + k)| ≤ (U : ℤ) :=
    by
    intro k hk
    rw [hread k hk]
    exact hmabs k hk
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightMomentZeroDetector.meets H scratch a ν v w hv hweights ht S.detector hspace hw (U : ℤ)
              (Int.natCast_nonneg U) ha hdet hbound hread)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightMomentZeroDetector.meets H scratch a ν v w hv hweights ht S.detector hspace hw (U : ℤ)
            (Int.natCast_nonneg U) ha hdet hbound hread)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryMomentGather.time,
            LightMomentDeterminant.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryMomentGather.time, LightMomentDeterminant.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryMomentGather.time,
            LightMomentDeterminant.time] <;>
          omega)
    on_goal -1 => (rintro flag ξ ⟨hflag, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ξ
  refine ⟨?_, ?_⟩
  · exact hflag
  · intro i hi
    exact hkeep i (Or.inl hi)
end Procs
end ThreeSum.LightTernaryMomentRow

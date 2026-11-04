-- Prove2me | solution 1 for ThreeSum.LightLocalCounts.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:05.640377+00:00
-- url     : https://prove2.me/submissions/d94a0d92-562d-419b-9ee0-f80c6fd3e970

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCounts
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_3f3326597d4f4ccd
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightSubsetAddress_cell_offset_lt
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
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
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCounts
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open Light LocalCoverBounds LightPascal LightSubsetAddress
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalCounts
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {h dst work : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 512 * h + 4 ≤ lim.depth) (hout : dst + 6 ≤ work) (hspace : space work h ≤ lim.space)
    (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h, dst, work] μ (time h)
      (fun r μ' => r = (localThreshold h : ℤ) ∧ Seg μ' dst (values h) ∧ KeptBut μ μ' work dst 6) :=
  by
  have htableSpace : work + tableSize (512 * h) ≤ lim.space := by unfold space at hspace; omega
  have hbasePos : 0 < (2 : ℕ) ^ (512 * h + 1) := Nat.two_pow_pos _
  have hbaseWord : ((2 ^ (512 * h + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hb : 2 ^ (512 * h + 1) ≤ word h := by unfold word; nlinarith
    exact (Int.ofNat_le.mpr hb).trans hword
  have hchoose (i j : ℕ) (hi : i ≤ 512 * h) : i.choose j ≤ 2 ^ (512 * h + 1) :=
    (Nat.choose_le_two_pow i j).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hchooseWord (i j : ℕ) (hi : i ≤ 512 * h) : (i.choose j : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (hchoose i j hi)).trans hbaseWord
  have hMWord := hchooseWord (512 * h) (2 * h) le_rfl
  have hVWord := hchooseWord (512 * h) h le_rfl
  have hDeltaWord := hchooseWord (512 * h - h) h (by omega)
  have hGWord := hchooseWord (2 * h) h (by omega)
  have hDle : 2 ^ (2 * h) ≤ 2 ^ (512 * h + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hDWord : ((2 ^ (2 * h) : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hDle).trans hbaseWord
  have hNle : localThreshold h ≤ word h :=
    by
    have hm := Nat.mul_le_mul (hchoose (512 * h) (2 * h) le_rfl) hDle
    change (512 * h).choose (2 * h) * 2 ^ (2 * h) ≤ _
    unfold word
    nlinarith
  have hNWord : (localThreshold h : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hNle).trans hword
  have hconstant : (512 : ℤ) ≤ lim.word :=
    by
    have hc : 512 ≤ word h := by unfold word; omega
    exact (Int.ofNat_le.mpr hc).trans hword
  have hproduct : ((512 * h).choose (2 * h) : ℤ) * (2 : ℤ) ^ (2 * h) = (localThreshold h : ℤ) := by
    simp [localThreshold, outputCount]
  have hproductWord : ((512 * h).choose (2 * h) : ℤ) * (2 : ℤ) ^ (2 * h) ≤ lim.word :=
    by
    rw [hproduct]
    exact hNWord
  have hproductNonneg : (0 : ℤ) ≤ ((512 * h).choose (2 * h) : ℤ) * (2 : ℤ) ^ (2 * h) := by positivity
  have hsize : 512 * h + 1 ≤ tableSize (512 * h) := by unfold tableSize; nlinarith
  have hsub : ((512 * h : ℕ) : ℤ) - (h : ℤ) = ((512 * h - h : ℕ) : ℤ) := by omega
  have hMaddr := cell_offset_lt (W := 512 * h) (i := 512 * h) (j := 2 * h) le_rfl (by omega)
  have hVaddr := cell_offset_lt (W := 512 * h) (i := 512 * h) (j := h) le_rfl (by omega)
  have hDeltaAddr := cell_offset_lt (W := 512 * h) (i := 512 * h - h) (j := h) (by omega) (by omega)
  have hGaddr := cell_offset_lt (W := 512 * h) (i := 2 * h) (j := h) (by omega) (by omega)
  have hrowNZ : (0 : ℤ) ≤ 512 * (h : ℤ) * (512 * (h : ℤ) + 1) := by positivity
  have hrowAddr : (work : ℤ) + 512 * (h : ℤ) * (512 * (h : ℤ) + 1) + 2 * (h : ℤ) < (lim.space : ℤ) := by
    exact_mod_cast (show work + 512 * h * (512 * h + 1) + 2 * h < lim.space by omega)
  have hdeltaNZ : (0 : ℤ) ≤ (512 * (h : ℤ) - (h : ℤ)) * (512 * (h : ℤ) + 1) := by apply mul_nonneg <;> omega
  have hdeltaAddr : (work : ℤ) + (512 * (h : ℤ) - (h : ℤ)) * (512 * (h : ℤ) + 1) + (h : ℤ) < (lim.space : ℤ) :=
    by
    rw [show 512 * (h : ℤ) - (h : ℤ) = ((512 * h - h : ℕ) : ℤ) by omega]
    exact_mod_cast (show work + (512 * h - h) * (512 * h + 1) + h < lim.space by omega)
  have hgroupNZ : (0 : ℤ) ≤ 2 * (h : ℤ) * (512 * (h : ℤ) + 1) := by positivity
  have hgroupAddr : (work : ℤ) + 2 * (h : ℤ) * (512 * (h : ℤ) + 1) + (h : ℤ) < (lim.space : ℤ) := by
    exact_mod_cast (show work + 2 * h * (512 * h + 1) + h < lim.space by omega)
  have hMcast :
    (work : ℤ) + 512 * (h : ℤ) * (512 * (h : ℤ) + 1) + 2 * (h : ℤ) =
      ((work + 512 * h * (512 * h + 1) + 2 * h : ℕ) : ℤ) :=
    by push_cast; rfl
  have hVcast :
    (work : ℤ) + 512 * (h : ℤ) * (512 * (h : ℤ) + 1) + (h : ℤ) = ((work + 512 * h * (512 * h + 1) + h : ℕ) : ℤ) := by
    push_cast; rfl
  have hDeltaCast :
    (work : ℤ) + (512 * (h : ℤ) - (h : ℤ)) * (512 * (h : ℤ) + 1) + (h : ℤ) =
      ((work + (512 * h - h) * (512 * h + 1) + h : ℕ) : ℤ) :=
    by
    rw [show 512 * (h : ℤ) - (h : ℤ) = ((512 * h - h : ℕ) : ℤ) by omega]
    push_cast
    rfl
  have hGcast :
    (work : ℤ) + 2 * (h : ℤ) * (512 * (h : ℤ) + 1) + (h : ℤ) = ((work + 2 * h * (512 * h + 1) + h : ℕ) : ℤ) := by
    push_cast; rfl
  have hDcast :
    (work : ℤ) + (512 * (h : ℤ) + 1) * (512 * (h : ℤ) + 1) + 2 * (h : ℤ) =
      ((work + tableSize (512 * h) + 2 * h : ℕ) : ℤ) :=
    by simp [tableSize, pow_two]
  have hDaddrZ : (work : ℤ) + (512 * (h : ℤ) + 1) * (512 * (h : ℤ) + 1) + 2 * (h : ℤ) < (lim.space : ℤ) :=
    by
    rw [hDcast]
    exact_mod_cast
      (show work + tableSize (512 * h) + 2 * h < lim.space
        by
        unfold space at hspace
        omega)
  have hSquareNZ : (0 : ℤ) ≤ (512 * (h : ℤ) + 1) * (512 * (h : ℤ) + 1) := by positivity
  have hMnat :
    ((work : ℤ) + 512 * (h : ℤ) * (512 * (h : ℤ) + 1) + 2 * (h : ℤ)).toNat = work + 512 * h * (512 * h + 1) + 2 * h :=
    by rw [hMcast, Int.toNat_natCast]
  have hVnat :
    ((work : ℤ) + 512 * (h : ℤ) * (512 * (h : ℤ) + 1) + (h : ℤ)).toNat = work + 512 * h * (512 * h + 1) + h := by
    rw [hVcast, Int.toNat_natCast]
  have hDeltaNat :
    ((work : ℤ) + (512 * (h : ℤ) - (h : ℤ)) * (512 * (h : ℤ) + 1) + (h : ℤ)).toNat =
      work + (512 * h - h) * (512 * h + 1) + h :=
    by rw [hDeltaCast, Int.toNat_natCast]
  have hGnat : ((work : ℤ) + 2 * (h : ℤ) * (512 * (h : ℤ) + 1) + (h : ℤ)).toNat = work + 2 * h * (512 * h + 1) + h := by
    rw [hGcast, Int.toNat_natCast]
  have hDnat :
    ((work : ℤ) + (512 * (h : ℤ) + 1) * (512 * (h : ℤ) + 1) + 2 * (h : ℤ)).toNat = work + tableSize (512 * h) + 2 * h :=
    by rw [hDcast, Int.toNat_natCast]
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
    refine _root_.Light.Ends.setToThen (512 * h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime] <;>
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
    refine _root_.Light.Ends.setToThen (2 * h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime] <;>
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
          ((LightSubsetSetup.meets (d := d + 1) (μ := μ) (L := 512 * h) (k := 0) (m := 0) (work := work) S.setup hw
              hspace hbaseWord (by simp) (by omega))
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightSubsetSetup.meets (d := d + 1) (μ := μ) (L := 512 * h) (k := 0) (m := 0) (work := work) S.setup hw
            hspace hbaseWord (by simp) (by omega))
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime] <;>
          omega)
    on_goal -1 =>
      (rintro result μ₁ ⟨hr, htable, hpowers, hkept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hMread := htable (512 * h) le_rfl (2 * h) (by omega)
  have hVread := htable (512 * h) le_rfl h (by omega)
  have hDeltaRead := htable (512 * h - h) (by omega) h (by omega)
  have hGread := htable (2 * h) (by omega) h (by omega)
  have hDread := hpowers (2 * h) (by omega)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen ((512 * h).choose (2 * h) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hMnat, hMread, LightSubsetSetup.time,
            buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hMnat, hMread, LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime,
              rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hMnat, hMread, LightSubsetSetup.time, buildTime,
            rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
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
    refine _root_.Light.Ends.setToThen ((512 * h).choose h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hVnat, hVread, LightSubsetSetup.time,
            buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hVnat, hVread, LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime,
              rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hVnat, hVread, LightSubsetSetup.time, buildTime,
            rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
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
    refine _root_.Light.Ends.setToThen ((512 * h - h).choose h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hDeltaNat, hDeltaRead,
            LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hDeltaNat, hDeltaRead, LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime,
              rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hDeltaNat, hDeltaRead, LightSubsetSetup.time,
            buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
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
    refine _root_.Light.Ends.setToThen ((2 * h).choose h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hGnat, hGread, LightSubsetSetup.time,
            buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hGnat, hGread, LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime,
              rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hGnat, hGread, LightSubsetSetup.time, buildTime,
            rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
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
    refine _root_.Light.Ends.setToThen (2 ^ (2 * h) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hDnat, hDread, LightSubsetSetup.time,
            buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hDnat, hDread, LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime,
              rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hDnat, hDread, LightSubsetSetup.time, buildTime,
            rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
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
    refine _root_.Light.Ends.setToThen (localThreshold h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hproduct, LightSubsetSetup.time, buildTime,
            rowTime, LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hproduct, LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hproduct, LightSubsetSetup.time, buildTime,
            rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
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
    refine _root_.Light.Ends.storeToThen dst ((512 * h).choose (2 * h) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime] <;>
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
    refine _root_.Light.Ends.storeToThen (dst + 1) ((512 * h).choose h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime] <;>
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
    refine _root_.Light.Ends.storeToThen (dst + 2) ((512 * h - h).choose h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime] <;>
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
    refine _root_.Light.Ends.storeToThen (dst + 3) ((2 * h).choose h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime] <;>
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
    refine _root_.Light.Ends.storeToThen (dst + 4) (2 ^ (2 * h) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime] <;>
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
    refine _root_.Light.Ends.storeToThen (dst + 5) (localThreshold h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime] <;>
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
    refine _root_.Light.Ends.setToThen (localThreshold h : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, buildTime, rowTime,
            LightArray.linearTime, powTableTime, rankTime] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨rfl, ?_, ?_⟩
  · simp [values, outputCount, vertexCount, degree, groupSize, seg_cons]
  · intro a ha
    change Function.update _ _ _ a = _
    repeat rw [Function.update_of_ne (by omega)]
    exact hkept a ha.1
end Procs
end ThreeSum.LightLocalCounts

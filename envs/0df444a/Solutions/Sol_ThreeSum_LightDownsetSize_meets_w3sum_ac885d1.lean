-- Prove2me | solution 1 for ThreeSum.LightDownsetSize.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:18.889062+00:00
-- url     : https://prove2.me/submissions/f94fea72-23f1-48a0-8b67-e34328a596bf

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Theorems.Thm_ThreeSum_LightDownsetSize_cap_eq
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightSubsetAddress_cell_offset_lt
import Theorems.Thm_ThreeSum_LightSubsetOffset_layerOffset_bound
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
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
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetSize
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDownsetSize
theorem _root_.solution {pMain pSetup pBuild pFill pRow pLinear pPowers pRank pOffset : ℕ}
    (hmain : P[pMain]? = some (body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body) {μ : ℕ → ℤ} {L cut work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : work + tableSize L + (L + 1) ≤ lim.space)
    (hword : (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word) (hcut : cut ≤ L) (hd : d + L + 4 ≤ lim.depth) :
    Meets lim P pMain d [L, cut, work] μ (time L) (fun r μ' => r = (downsetCap L cut : ℤ) ∧ Kept μ μ' work) :=
  by
  have hword₀ : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ (L + 1) : ℕ) ≤ (L + 1) * 2 ^ (L + 1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ)).trans hword
  have hpow : (2 ^ L : ℕ) ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hsmall := LightSubsetOffset.layerOffset_bound L cut
  have hchoose := Nat.choose_le_two_pow L cut
  have hprod := Nat.mul_le_mul hcut hpow
  have hbound : downsetCap L cut ≤ (L + 1) * 2 ^ (L + 1) :=
    by
    rw [cap_eq hcut]
    nlinarith
  have hboundZ : (downsetCap L cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hbound : (downsetCap L cut : ℤ) ≤ (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ)).trans hword
  have hcast : (L : ℤ) * ((L : ℤ) + 1) = ((L * (L + 1) : ℕ) : ℤ) := by push_cast; rfl
  apply Meets.of_body hmain
  unfold body time
  have hs :=
    LightSubsetSetup.meets (d := d + 1) (μ := μ) (L := L) (k := 0) (m := 0) C hw hspace hword₀ (by simp) (by omega)
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
    | refine _root_.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time,
            LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime,
              rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, LightSubsetOffset.time,
            buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
          omega)
    on_goal -1 => (rintro _ μ₁ ⟨_, hTable, _, hKept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have ho := LightSubsetOffset.meets (d := d + 1) hOffset μ₁ hw (by omega) hword hTable le_rfl hcut
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
    | refine _root_.Light.Ends.callToThen (ho _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen ho ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSubsetSetup.time,
            LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSubsetSetup.time, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime,
              rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSubsetSetup.time, LightSubsetOffset.time,
            buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
          omega)
    on_goal -1 => (rintro off μ₂ ⟨hoff, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₂
  have hread := hTable L le_rfl cut hcut
  have hcell := cell_offset_lt (show L ≤ L from le_rfl) hcut
  have haddr : ((work : ℤ) + (L : ℤ) * ((L : ℤ) + 1) + (cut : ℤ)).toNat = work + L * (L + 1) + cut :=
    by
    have hh : (work : ℤ) + (L : ℤ) * ((L : ℤ) + 1) + (cut : ℤ) = ((work + L * (L + 1) + cut : ℕ) : ℤ) :=
      by
      push_cast
      rfl
    rw [hh, Int.toNat_natCast]
  have hreadZ : μ₁ (((work : ℤ) + (L : ℤ) * ((L : ℤ) + 1) + (cut : ℤ)).toNat) = (L.choose cut : ℤ) := by
    rw [haddr, hread]
  have hsum : (layerOffset L cut : ℤ) + (L.choose cut : ℤ) = (downsetCap L cut : ℤ) := by rw [cap_eq hcut, Nat.cast_add]
  have hn₁ : (0 : ℤ) ≤ layerOffset L cut := Int.natCast_nonneg _
  have hn₂ : (0 : ℤ) ≤ L.choose cut := Int.natCast_nonneg _
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (downsetCap L cut : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hoff, hreadZ, hsum, LightSubsetSetup.time,
            LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hoff, hreadZ, hsum, LightSubsetSetup.time, LightSubsetOffset.time, buildTime, rowTime,
              LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hoff, hreadZ, hsum, LightSubsetSetup.time,
            LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact ⟨by simp, hKept⟩
end ThreeSum.LightDownsetSize

-- Prove2me | solution 1 for ThreeSum.LightSubsetSetup.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:35:29.837468+00:00
-- url     : https://prove2.me/submissions/af6ca543-aee5-449b-a80a-7289a5793687

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_4eb33ef6f1e27fd8
import Theorems.Thm_ThreeSum_LightSubsetAddress_cell_offset_lt
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
import Definitions.Def_WeightedCache3SUM_Alias_9a3b2d25906ae04a
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
open ThreeSum ThreeSum.LightSubsetSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSubsetSetup
theorem _root_.solution {pMain pBuild pFill pRow pLinear pPowers pRank : ℕ}
    (C : Procs P pMain pBuild pFill pRow pLinear pPowers pRank) {μ : ℕ → ℤ} {L k m work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : work + tableSize L + (L + 1) ≤ lim.space)
    (hword : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word) (hm : IsMask L k m) (hd : d + L + 3 ≤ lim.depth) :
    Meets lim P pMain d [L, k, m, work] μ (time L)
      (fun r μ' => r = (layerRank L k m : ℤ) ∧ Table μ' work L ∧ Powers μ' (work + tableSize L) L ∧ Kept μ μ' work) :=
  by
  have hsize : L + 1 ≤ tableSize L := by unfold tableSize; nlinarith
  have hcastSize : ((L : ℤ) + 1) * ((L : ℤ) + 1) = (tableSize L : ℤ) := by simp [tableSize, pow_two]
  apply Meets.of_body C.main
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
    refine _root_.Light.Ends.setToThen (work + tableSize L : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, buildTime, rowTime, LightArray.linearTime,
            powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, buildTime, rowTime, LightArray.linearTime,
            powTableTime, rankTime] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hbuild :=
    build_meets (d := d + 1) (μ := μ) (dst := work) (L := L) C.build C.fill C.row C.linear hw (by omega) (by omega)
      hword
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
    | refine _root_.Light.Ends.callToThen (hbuild _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hbuild ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, buildTime, rowTime, LightArray.linearTime,
            powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, buildTime, rowTime, LightArray.linearTime,
            powTableTime, rankTime] <;>
          omega)
    on_goal -1 => (rintro _ μ₁ ⟨htable, hkept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpowers :=
    powTable_meets (d := d + 1) (μ := μ₁) (dst := work + tableSize L) (L := L + 1) (b := 2) C.powers hw hspace
      (by
        intro j hj
        have hb : (2 ^ j : ℕ) ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by decide) hj
        have hbZ : ((2 ^ j : ℕ) : ℤ) ≤ ((2 ^ (L + 1) : ℕ) : ℤ) := by exact_mod_cast hb
        exact hbZ.trans hword)
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
    | refine _root_.Light.Ends.callToThen (hpowers _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hpowers ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, buildTime, rowTime, LightArray.linearTime,
            powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, buildTime, rowTime, LightArray.linearTime,
            powTableTime, rankTime] <;>
          omega)
    on_goal -1 => (rintro _ μ₂ ⟨hpSeg, hkept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have htable₂ : Table μ₂ work L := by
    intro i hi j hj
    have hb := cell_offset_lt hi hj
    rw [hkept₂ _ (by omega)]
    exact htable i hi j hj
  have hpowSpec := powers_of_segment hpSeg
  have hrank := rank_meets C.rank μ₂ hw (by omega) hspace hword htable₂ hpowSpec L k m le_rfl hm (d + 1) (by omega)
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
    | refine _root_.Light.Ends.callToThen (hrank _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hrank ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, buildTime, rowTime, LightArray.linearTime,
            powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, buildTime, rowTime, LightArray.linearTime,
            powTableTime, rankTime] <;>
          omega)
    on_goal -1 => (rintro res μ₃ ⟨hres, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₃
  refine ⟨by simpa using hres, htable₂, hpowSpec, ?_⟩
  intro a ha
  exact (hkept₂ a (by omega)).trans (hkept₁ a (by omega))
end ThreeSum.LightSubsetSetup

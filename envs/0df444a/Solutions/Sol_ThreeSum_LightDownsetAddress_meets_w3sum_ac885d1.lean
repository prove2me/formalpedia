-- Prove2me | solution 1 for ThreeSum.LightDownsetAddress.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:24.738202+00:00
-- url     : https://prove2.me/submissions/17612fc3-75fb-46aa-aa56-d1ee7a47e0be

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetAddress
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightSubsetOffset_layerOffset_bound
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_le_width
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Definitions.Def_WeightedCache3SUM_Alias_a5ea34939403d75f
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
open ThreeSum ThreeSum.LightDownsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDownsetAddress
theorem _root_.solution {pMain pFresh pBuild pFill pRow pLinear pPowers pRank pOffset : ℕ}
    (hmain : P[pMain]? = some (body pFresh pOffset))
    (C : LightSubsetSetup.Procs P pFresh pBuild pFill pRow pLinear pPowers pRank)
    (hoff : P[pOffset]? = some LightSubsetOffset.body) {μ : ℕ → ℤ} {L k m work d : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work + tableSize L + (L + 1) ≤ lim.space) (hword : (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word)
    (hm : IsMask L k m) (hd : d + L + 4 ≤ lim.depth) :
    Meets lim P pMain d [L, k, m, work] μ (time L) (fun r μ' => r = (downsetRank L m : ℤ) ∧ Kept μ μ' work) :=
  by
  have hk := hm.le_width
  have hword₀ : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hb : (2 ^ (L + 1) : ℕ) ≤ (L + 1) * 2 ^ (L + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have hbZ : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ) := by exact_mod_cast hb
    exact hbZ.trans hword
  have hrank := (layerRank_lt hm).trans_le (Nat.choose_le_two_pow L k)
  have hoffset := LightSubsetOffset.layerOffset_bound L k
  have hscale := Nat.mul_le_mul_right (2 ^ L) hk
  have hdouble :=
    Nat.mul_le_mul_left (L + 1) (show (2 ^ L : ℕ) ≤ 2 ^ (L + 1) from Nat.pow_le_pow_right (by decide) (by omega))
  have hsumNat : layerRank L k m + layerOffset L k ≤ (L + 1) * 2 ^ (L + 1) := by nlinarith
  have hsum : (layerRank L k m : ℤ) + (layerOffset L k : ℤ) ≤ lim.word :=
    by
    have hbZ : (layerRank L k m : ℤ) + (layerOffset L k : ℤ) ≤ (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ) := by
      exact_mod_cast hsumNat
    exact hbZ.trans hword
  have hrNonneg : (0 : ℤ) ≤ (layerRank L k m : ℤ) := Int.natCast_nonneg _
  have hoNonneg : (0 : ℤ) ≤ (layerOffset L k : ℤ) := Int.natCast_nonneg _
  apply Meets.of_body hmain
  unfold body time
  have hsetup := LightSubsetSetup.meets (d := d + 1) (μ := μ) C hw hspace hword₀ hm (by omega)
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
    | refine _root_.Light.Ends.callToThen (hsetup _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hsetup ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro rank μ₁ ⟨hr, hT, hPow, hKept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hscan := LightSubsetOffset.meets (d := d + 1) hoff μ₁ hw (by omega) hword hT le_rfl hk
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
    | refine _root_.Light.Ends.callToThen (hscan _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hscan ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro offset μ₂ ⟨ho, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₂
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen ((layerRank L k m + layerOffset L k : ℕ)) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr, ho, LightSubsetSetup.time,
            LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hr, ho, LightSubsetSetup.time, LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime,
              powTableTime, rankTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, ho, LightSubsetSetup.time,
            LightSubsetOffset.time, buildTime, rowTime, LightArray.linearTime, powTableTime, rankTime] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨?_, hKept⟩
  simp [downsetRank, hm.2, Nat.add_comm]
end ThreeSum.LightDownsetAddress

-- Prove2me | solution 1 for ThreeSum.LightDownsetEnumerationSetup.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:39.390374+00:00
-- url     : https://prove2.me/submissions/194fb78a-2ca3-426c-bdb3-127b20c40e3a

import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumerationSetup
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_2ae6d2b4167e20c4
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
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
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetEnumerationSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDownsetEnumerationSetup
theorem _root_.solution {pMain pPowers pDownset pEnum : ℕ} (hmain : P[pMain]? = some (body pPowers pDownset))
    (hpowers : P[pPowers]? = some powTableBody) (hdownset : P[pDownset]? = some (LightDownsetEnumeration.body pEnum))
    (henum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum)) {μ : ℕ → ℤ} {L cut dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : work + (L + 1) ≤ lim.space) (hword : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hdst : dst + downsetCap L cut ≤ work) (hd : d + L + 2 ≤ lim.depth) :
    Meets lim P pMain d [L, cut, dst, work] μ (time L cut)
      (fun r μ' =>
        r = (downsetCap L cut : ℤ) ∧
          SegN μ' dst (enumerateDownset L cut) ∧ Powers μ' work L ∧ KeptBut μ μ' work dst (downsetCap L cut)) :=
  by
  have hbase : (2 : ℤ) ≤ lim.word :=
    by
    have hb : (2 ^ 1 : ℕ) ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hz : (2 : ℤ) ≤ ((2 ^ (L + 1) : ℕ) : ℤ) := by exact_mod_cast hb
    exact hz.trans hword
  apply Meets.of_body hmain
  unfold body time
  have hpow :=
    powTable_meets (d := d + 1) (μ := μ) (dst := work) (L := L + 1) (b := 2) hpowers hw hspace
      (by
        intro j hj
        have hb : (2 ^ j : ℕ) ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by decide) hj
        have hz : ((2 ^ j : ℕ) : ℤ) ≤ ((2 ^ (L + 1) : ℕ) : ℤ) := by exact_mod_cast hb
        exact hz.trans hword)
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
    | refine _root_.Light.Ends.callToThen (hpow _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hpow ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, LightDownsetEnumeration.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightDownsetEnumeration.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, LightDownsetEnumeration.time] <;>
          omega)
    on_goal -1 => (rintro _ μ₁ ⟨hpowSeg, hsame₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpowSpec := powers_of_segment hpowSeg
  have hcall := LightDownsetEnumeration.meets (d := d + 1) hdownset henum hw hspace hword hcut hdst hpowSpec (by omega)
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
    | refine _root_.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, LightDownsetEnumeration.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightDownsetEnumeration.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, LightDownsetEnumeration.time] <;>
          omega)
    on_goal -1 => (rintro res μ₂ ⟨hres, hseg, hsame₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨by simpa using hres, hseg, ?_, ?_⟩
  · intro i hi
    change μ₂ (work + i) = _
    rw [hsame₁ (work + i) (Or.inr (by omega))]
    exact hpowSpec i hi
  · intro a ha
    exact (hsame₁ a ha.2).trans (hsame₀ a (Or.inl ha.1))
end ThreeSum.LightDownsetEnumerationSetup

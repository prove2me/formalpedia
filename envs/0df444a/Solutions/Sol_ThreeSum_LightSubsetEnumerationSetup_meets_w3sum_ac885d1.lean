-- Prove2me | solution 1 for ThreeSum.LightSubsetEnumerationSetup.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:35:43.104996+00:00
-- url     : https://prove2.me/submissions/33b57624-6597-4069-b026-f4ef5f479051

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_work_pos
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
open ThreeSum ThreeSum.LightSubsetEnumerationSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSubsetEnumerationSetup
theorem _root_.solution {pMain pPowers pEnum : ℕ} (hmain : P[pMain]? = some (body pPowers pEnum))
    (hpowers : P[pPowers]? = some powTableBody) (henum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    {μ : ℕ → ℤ} {L k dst work d : ℕ} (hw : (lim.space : ℤ) ≤ lim.word) (hspace : work + (L + 1) ≤ lim.space)
    (hword : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word) (hk : k ≤ L + 1) (hdst : dst + L.choose k ≤ work)
    (hd : d + L + 1 ≤ lim.depth) :
    Meets lim P pMain d [L, k, dst, work] μ (time L k)
      (fun r μ' =>
        r = (L.choose k : ℤ) ∧
          SegN μ' dst (enumerateLayer L k) ∧ Powers μ' work L ∧ KeptBut μ μ' work dst (L.choose k)) :=
  by
  have hpositive := LightSubsetEnumeration.work_pos L k
  have htime : 150 ≤ LightSubsetEnumeration.time L k := Nat.mul_le_mul_left 150 hpositive
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, LightSubsetEnumeration.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightSubsetEnumeration.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, LightSubsetEnumeration.time] <;>
          omega)
    on_goal -1 => (rintro _ μ₁ ⟨hpowSeg, hsame₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpowSpec := powers_of_segment hpowSeg
  have hcall :=
    LightSubsetEnumeration.meets henum hw hspace hword L k 0 dst μ₁ le_rfl hk (by simp) hdst hpowSpec (d + 1) (by omega)
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableTime, LightSubsetEnumeration.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableTime, LightSubsetEnumeration.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, powTableTime, LightSubsetEnumeration.time] <;>
          omega)
    on_goal -1 => (rintro res μ₂ ⟨hres, hseg, hsame₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨by simpa using hres, ?_, ?_, ?_⟩
  · simpa [LightSubsetEnumeration.output] using hseg
  · intro i hi
    change μ₂ (work + i) = _
    rw [hsame₁ (work + i) (Or.inr (by omega))]
    exact hpowSpec i hi
  · intro a ha
    exact (hsame₁ a ha.2).trans (hsame₀ a (Or.inl ha.1))
end ThreeSum.LightSubsetEnumerationSetup

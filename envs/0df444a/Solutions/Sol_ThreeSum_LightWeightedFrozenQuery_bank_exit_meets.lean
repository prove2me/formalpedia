-- Prove2me | solution 1 for ThreeSum.LightWeightedFrozenQuery.bank_exit_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:15.758737+00:00
-- url     : https://prove2.me/submissions/32c82ce4-ff81-4d3a-adfd-bf58dcf68403

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_Weighted_Frozen
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
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
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
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
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedFrozenQuery
theorem _root_.solution {pMain pLookup pSelf pDigit pZero pErase d t : ℕ}
    (hmain : P[pMain]? = some (body pSelf pLookup pDigit pZero pErase))
    (N K rank cut bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ) (code value : ℤ)
    (μ : ℕ → ℤ) (hbank : rank ≤ cut) (hone : 1 ≤ lim.word) (hcutWord : (cut : ℤ) + 1 ≤ lim.word)
    (hargs :
      ∀ x ∈ inputs N K rank cut code bankCodes bankCount bankValues nearCodes nearCount nearValues powers L,
        |x| ≤ lim.word)
    (hd : d + 1 ≤ lim.depth)
    (hlookup :
      Meets lim P pLookup (d + 1) [bankCodes, bankCount, code, bankValues, powers, L, K] μ t
        (fun r μ' => r = value ∧ μ' = μ)) :
    Meets lim P pMain d
      (inputs N K rank cut code bankCodes bankCount bankValues nearCodes nearCount nearValues powers L) μ (t + 80)
      (fun r μ' => r = value ∧ μ' = μ) :=
  by
  have hr := abs_le.mp (hargs rank (by simp [inputs]))
  have ht := abs_le.mp (hargs cut (by simp [inputs]))
  have hb := abs_le.mp (hargs bankCodes (by simp [inputs]))
  have hn := abs_le.mp (hargs bankCount (by simp [inputs]))
  have hc := abs_le.mp (hargs code (by simp [inputs]))
  have hv := abs_le.mp (hargs bankValues (by simp [inputs]))
  have hp := abs_le.mp (hargs powers (by simp [inputs]))
  have hL := abs_le.mp (hargs L (by simp [inputs]))
  have hK := abs_le.mp (hargs K (by simp [inputs]))
  apply Meets.of_body hmain
  unfold body inputs
  refine
    Ends.iteLast (fun hyes => ?_) (fun hno => ?_)
      (by (
          (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
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
      | refine _root_.Light.Ends.callToThen (hlookup _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hlookup ?_ ?_ ?_ ?_
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
      on_goal -1 => (rintro r μ' hout; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    exact hout
  · exfalso
    apply hno
    simpa using (show (rank : ℤ) ≤ (cut : ℤ) by exact_mod_cast hbank)
end ThreeSum.LightWeightedFrozenQuery

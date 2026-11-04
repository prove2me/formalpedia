-- Prove2me | solution 1 for ThreeSum.LightTernaryQueryLookup.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:31:17.901624+00:00
-- url     : https://prove2.me/submissions/be5d7b38-bf48-43bf-b6a4-7c654ed98b28

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightTernaryLookup_code_meets
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
open ThreeSum ThreeSum.LightTernaryQueryLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryQueryLookup
theorem _root_.solution {pMain pSearch a n powers W L src stage j d U : ℕ} (hmain : P[pMain]? = some (body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch)) (μ : ℕ → ℤ) (codes : ℕ → ℤ) (value : ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + n ≤ lim.space) (hsrc : src + (stage + 1) * n ≤ lim.space)
    (hspace : powers + (W + 1) ≤ lim.space) (hword : ((n + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a + i) = codes i) (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < n → codes i < codes k) (hj : j < n) (hvalue : μ (src + stage * n + j) = value)
    (hval : |value| ≤ U) (hU : (U : ℤ) ≤ lim.word) (hL : L ≤ W) (hn : n < 2 ^ L) (hd : d + L + 1 ≤ lim.depth) :
    Meets lim P pMain d [a, n, codes j, src, powers, L, stage] μ (time L) (fun r μ' => r = value ∧ μ' = μ) :=
  by
  have hc :=
    LightTernaryLookup.code_meets (d := d + 1) hsearch μ codes hw ha hspace hword hread hpowers hsorted hj hL hn
      (by omega)
  have haddr : (src : ℤ) + (stage : ℤ) * (n : ℤ) + ((j + 1 : ℕ) : ℤ) - 1 = ((src + stage * n + j : ℕ) : ℤ) := by
    push_cast; ring
  have haddrNat : ((src : ℤ) + (stage : ℤ) * (n : ℤ) + ((j + 1 : ℕ) : ℤ) - 1).toNat = src + stage * n + j := by
    rw [haddr, Int.toNat_natCast]
  have haddrNat' : ((src : ℤ) + (stage : ℤ) * (n : ℤ) + ((j + 1 : ℕ) : ℤ)).toNat - 1 = src + stage * n + j :=
    by
    have hp : (src : ℤ) + (stage : ℤ) * (n : ℤ) + ((j + 1 : ℕ) : ℤ) = ((src + stage * n + j + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [hp, Int.toNat_natCast]
    omega
  have haddrNat'' : ((src : ℤ) + (stage : ℤ) * (n : ℤ) + ((j : ℤ) + 1)).toNat - 1 = src + stage * n + j := by
    simpa only [Nat.cast_add, Nat.cast_one] using haddrNat'
  have hvalue' : μ (((src : ℤ) + (stage : ℤ) * (n : ℤ) + ((j : ℤ) + 1)).toNat - 1) = value :=
    by
    rw [haddrNat'']
    exact hvalue
  have hbounds := abs_le.mp (hval.trans hU)
  have hmul : stage * n ≤ (stage + 1) * n := Nat.mul_le_mul_right n (Nat.le_succ stage)
  have hmulWord : (stage : ℤ) * (n : ℤ) ≤ lim.word :=
    by
    have hh : stage * n ≤ lim.space := by omega
    exact (show (stage : ℤ) * (n : ℤ) ≤ (lim.space : ℤ) by exact_mod_cast hh).trans hw
  have hsum : src + stage * n + j + 1 ≤ lim.space :=
    by
    rw [Nat.succ_mul] at hsrc
    omega
  apply Meets.of_body hmain
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
    first
    | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBandLookup.searchTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBandLookup.searchTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBandLookup.searchTime] <;> omega)
    on_goal -1 => (rintro r μ' ⟨hr, hm⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ'
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen value ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr, haddrNat, haddrNat', haddrNat'', hvalue,
            hvalue', LightBandLookup.searchTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hr, haddrNat, haddrNat', haddrNat'', hvalue, hvalue', LightBandLookup.searchTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, haddrNat, haddrNat', haddrNat'', hvalue,
            hvalue', LightBandLookup.searchTime] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact ⟨rfl, rfl⟩
end ThreeSum.LightTernaryQueryLookup

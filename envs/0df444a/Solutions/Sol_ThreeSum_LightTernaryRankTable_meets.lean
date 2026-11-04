-- Prove2me | solution 1 for ThreeSum.LightTernaryRankTable.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:55:02.773998+00:00
-- url     : https://prove2.me/submissions/08a38704-5574-4a71-b662-72cc5d730baa

import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_Light_wrote_rest
import Theorems.Thm_Light_wrote_succ
import Theorems.Thm_Light_wrote_zero
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_partialRank_le
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRankTable
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryRankTable
theorem _root_.solution {pMain pRank pDigit pErase N a n powers dst d : ℕ} (hmain : P[pMain]? = some (body pRank))
    (hrank : P[pRank]? = some (LightTernaryRank.body pDigit))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase)) (μ : ℕ → ℤ) (codes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + n ≤ dst) (hp : powers + (2 * N + 1) ≤ dst) (hdst : dst + n ≤ lim.space)
    (hword : ((2 ^ (2 * N + 1) : ℕ) : ℤ) ≤ lim.word) (hscalar : ((2 * N + 16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (a + j) = (codes j : ℤ)) (hpowers : Powers μ powers (2 * N))
    (hcodes : ∀ j < n, codes j < 2 ^ (2 * N)) (hdepth : d + 2 * N + 3 ≤ lim.depth) :
    Meets lim P pMain d [N, a, n, powers, dst] μ (time N n)
      (fun _ ν => (∀ j < n, ν (dst + j) = values N codes j) ∧ SameOutside μ ν dst n) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ N a n powers dst codes) n (LightTernaryRank.time N + 85) ?start ?round ?done ?bound (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, 0, ?_⟩
    simp [Inv, update_frame_setLocal, wrote_zero]
    change frame [(N : ℤ), a, n, powers, dst, 0] = frame ([(N : ℤ), a, n, powers, dst, 0] ++ [0, 0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨code, result, rfl⟩
    let μj := wrote μ dst (values N codes) j
    have hkeep : ∀ x < dst, μj x = μ x := fun x hx => wrote_rest (Or.inl hx)
    have hreadj : μj (a + j) = (codes j : ℤ) := by rw [hkeep _ (by omega), hread j hj]
    have hpj : Powers μj powers (2 * N) := by
      intro k hk
      rw [hkeep _ (by omega), hpowers k hk]
    have hm := hcodes j hj
    have hpow : 2 ^ (2 * N) ≤ 2 ^ (2 * N + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hcodeWord : (codes j : ℤ) < lim.word := (Int.ofNat_lt.mpr hm).trans_le ((Int.ofNat_le.mpr hpow).trans hword)
    have hv := LightTernaryRank.partialRank_le N (codes j) N
    have hvalueWord : (LightTernaryRank.partialRank N (codes j) N : ℤ) ≤ lim.word := by omega
    have hc := LightTernaryRank.meets (d := d + 1) hrank hdigit herase μj hw (by omega) hword hscalar hpj hm (by omega)
    unfold roundBody
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (codes j : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, μj, hreadj,
              LightTernaryRank.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [μj, hreadj, LightTernaryRank.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, μj, hreadj, LightTernaryRank.time] <;> omega)
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
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, μj,
              LightTernaryRank.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [μj, LightTernaryRank.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, μj, LightTernaryRank.time] <;> omega)
      on_goal -1 => (rintro out ν ⟨hout, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + j) (values N codes j) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hout, values,
              LightTernaryRank.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hout, values, LightTernaryRank.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hout, values, LightTernaryRank.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, (codes j : ℤ), out, ?_⟩
    simp [Inv, update_frame_setLocal, wrote_succ, μj]
  case done =>
    rintro _ _ ⟨code, result, rfl⟩
    exact ⟨fun j hj => wrote_done hj, fun x hx => wrote_rest hx⟩
  case bound =>
    rintro j _ hj _ ⟨code, result, rfl⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightTernaryRankTable

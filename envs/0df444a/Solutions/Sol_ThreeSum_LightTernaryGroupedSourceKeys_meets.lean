-- Prove2me | solution 1 for ThreeSum.LightTernaryGroupedSourceKeys.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:31:54.49297+00:00
-- url     : https://prove2.me/submissions/0ea77e6a-a320-4164-8478-30edce75963b

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSourceKeys
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
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
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
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupedSourceKeys
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryGroupedSourceKeys
theorem _root_.solution {pMain pSearch a bank powers W L pairs count words wordCount dst groupBase groups d : ℕ}
    (hmain : P[pMain]? = some (body pSearch)) (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (codes : ℕ → ℕ) (position key group : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + bank ≤ dst)
    (hpair : pairs + 2 * count ≤ dst) (hwords : words + wordCount ≤ dst) (hpows : powers + (W + 1) ≤ dst)
    (hgroups : groupBase + wordCount ≤ dst) (hgroupRead : ∀ i < count, μ (groupBase + position i) = (group i : ℤ))
    (hgroupLt : ∀ i < count, group i < groups) (hgroupWord : ((groups * bank + 1 : ℕ) : ℤ) ≤ lim.word)
    (hgroupSpace : groups * bank + 1 ≤ lim.space) (hdst : dst + count ≤ lim.space)
    (hword : ((bank + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word) (hcodes : ∀ i < bank, μ (a + i) = (codes i : ℤ))
    (hpairRead : ∀ i < count, μ (pairs + 2 * i + 1) = (position i : ℤ))
    (hposition : ∀ i < count, position i < wordCount)
    (hwordRead : ∀ i < count, μ (words + position i) = (codes (key i) : ℤ)) (hkey : ∀ i < count, key i < bank)
    (hcodeBound : ∀ i < bank, codes i < 2 ^ W) (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < bank → codes i < codes k) (hL : L ≤ W) (hn : bank < 2 ^ L)
    (hd : d + L + 1 ≤ lim.depth) :
    Meets lim P pMain d [a, bank, powers, L, pairs, count, words, wordCount, dst, groupBase, groups] μ (time L count)
      (fun _ μ' => (∀ i < count, μ' (dst + i) = ((group i * bank + key i : ℕ) : ℤ)) ∧ SameOutside μ μ' dst count) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ a bank powers L pairs count words wordCount dst groupBase groups key group) count
      (LightBandLookup.searchTime L + 185) ?start ?round ?done ?bound (hT := by
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
    refine ⟨0, ?_⟩
    simp [Inv, update_frame_setLocal, wrote_zero]
    change
      frame [(a : ℤ), bank, powers, L, pairs, count, words, wordCount, dst, groupBase, groups, 0] =
        frame ([(a : ℤ), bank, powers, L, pairs, count, words, wordCount, dst, groupBase, groups, 0] ++ [0])
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro j _ hj _ ⟨r, rfl⟩
    let μj := wrote μ dst (fun i => ((group i * bank + key i : ℕ) : ℤ)) j
    have hkeep : ∀ x < dst, μj x = μ x := by
      intro x hx
      exact wrote_rest (Or.inl hx)
    have hcodesj : ∀ i < bank, μj (a + i) = (codes i : ℤ) :=
      by
      intro i hi
      rw [hkeep _ (by omega), hcodes i hi]
    have hpairj : μj (pairs + 2 * j + 1) = (position j : ℤ) := by rw [hkeep _ (by omega), hpairRead j hj]
    have hwordj : μj (words + position j) = (codes (key j) : ℤ) := by
      rw [hkeep _ (by have hh := hposition j hj; omega), hwordRead j hj]
    have hgroupj : μj (groupBase + position j) = (group j : ℤ) := by
      rw [hkeep _ (by have hh := hposition j hj; omega), hgroupRead j hj]
    have hp : Powers μj powers W := by
      intro i hi
      rw [hkeep _ (by omega), hpowers i hi]
    have hsort : ∀ i k, i < k → k < bank → (codes i : ℤ) < (codes k : ℤ) :=
      by
      intro i k hik hk
      exact_mod_cast hsorted i k hik hk
    have hc :=
      LightTernaryLookup.code_meets (d := d + 1) hsearch μj (fun i => (codes i : ℤ)) hw (by omega) (by omega) hword
        hcodesj hp hsort (hkey j hj) hL hn (by omega)
    have hpj := hposition j hj
    have hkj := hkey j hj
    have hcb := hcodeBound (key j) hkj
    have hpow : 2 ^ W ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hcodeWord : (codes (key j) : ℤ) ≤ lim.word :=
      by
      have hh : codes (key j) ≤ bank + 2 ^ (W + 1) + 16 := by omega
      exact (Int.ofNat_le.mpr hh).trans hword
    have hpairAddr : ((pairs : ℤ) + 2 * (j : ℤ) + 1).toNat = pairs + 2 * j + 1 := by norm_cast
    have hwordAddr : ((words : ℤ) + (position j : ℤ)).toNat = words + position j := by norm_cast
    have hgroupAddr : ((groupBase : ℤ) + (position j : ℤ)).toNat = groupBase + position j := by norm_cast
    have hglt := hgroupLt j hj
    have hgkey : group j * bank + key j ≤ groups * bank := by nlinarith
    have hgprod : (group j : ℤ) * (bank : ℤ) ≤ lim.word :=
      by
      have hh : group j * bank ≤ groups * bank := by nlinarith
      exact (Int.ofNat_le.mpr (hh.trans (by omega))).trans hgroupWord
    have hgkeyword : ((group j * bank + key j : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hgkey.trans (by omega))).trans hgroupWord
    have hcounter :
      (frame [(a : ℤ), bank, powers, L, pairs, count, words, wordCount, dst, groupBase, groups, j, r]) 11 = (j : ℤ) :=
      by rfl
    have hpairNorm :
      wrote μ dst (fun i => (group i : ℤ) * (bank : ℤ) + (key i : ℤ)) j (pairs + 2 * j + 1) = (position j : ℤ) := by
      simpa only [μj, Nat.cast_add, Nat.cast_mul] using hpairj
    have hwordNorm :
      wrote μ dst (fun i => (group i : ℤ) * (bank : ℤ) + (key i : ℤ)) j (words + position j) = (codes (key j) : ℤ) := by
      simpa only [μj, Nat.cast_add, Nat.cast_mul] using hwordj
    have hgroupNorm :
      wrote μ dst (fun i => (group i : ℤ) * (bank : ℤ) + (key i : ℤ)) j (groupBase + position j) = (group j : ℤ) := by
      simpa only [μj, Nat.cast_add, Nat.cast_mul] using hgroupj
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
      first
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, μj, frame, hcounter,
              hpairAddr, hwordAddr, hpairj, hwordj, hpairNorm, hwordNorm, LightBandLookup.searchTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [μj, frame, hcounter, hpairAddr, hwordAddr, hpairj, hwordj, hpairNorm, hwordNorm,
                LightBandLookup.searchTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, μj, frame, hcounter, hpairAddr, hwordAddr,
              hpairj, hwordj, hpairNorm, hwordNorm, LightBandLookup.searchTime] <;>
            omega)
      on_goal -1 => (rintro out μ' ⟨hout, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
      refine _root_.Light.Ends.storeToThen (dst + j) (group j * bank + key j : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, μj, frame, hcounter,
              hout, hgroupj, hpairj, hpairNorm, hgroupNorm, hwordNorm, hwordj, hpairAddr, hgroupAddr, hgprod, hgkeyword,
              LightBandLookup.searchTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [μj, frame, hcounter, hout, hgroupj, hpairj, hpairNorm, hgroupNorm, hwordNorm, hwordj, hpairAddr,
                hgroupAddr, hgprod, hgkeyword, LightBandLookup.searchTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, μj, frame, hcounter, hout, hgroupj, hpairj,
              hpairNorm, hgroupNorm, hwordNorm, hwordj, hpairAddr, hgroupAddr, hgprod, hgkeyword,
              LightBandLookup.searchTime] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, out, ?_⟩
    simp [Inv, update_frame_setLocal, wrote_succ, μj]
  case done =>
    rintro _ _ ⟨r, rfl⟩
    refine ⟨?_, ?_⟩
    · intro j hj
      change
        wrote μ dst (fun i => ((group i * bank + key i : ℕ) : ℤ)) count (dst + j) = ((group j * bank + key j : ℕ) : ℤ)
      exact wrote_done hj
    · intro x hx
      change wrote μ dst (fun i => ((group i * bank + key i : ℕ) : ℤ)) count x = μ x
      exact wrote_rest hx
  case bound =>
    rintro j _ hj _ ⟨r, rfl⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightTernaryGroupedSourceKeys

-- Prove2me | solution 1 for ThreeSum.LightSourceFlagArray.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:07.493101+00:00
-- url     : https://prove2.me/submissions/9d84bf46-904b-4366-b887-da9e17a46467

import Definitions.Def_Submission_ThreeSum_LightSourceMaskFlags
import Definitions.Def_Submission_ThreeSum_LightSourceFlagArray
import Theorems.Thm_ThreeSum_LightSourceFlagArray_flag_le
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightSourceFlagTest_flag_le
import Definitions.Def_WeightedCache3SUM_Alias_8f9b8fc511f535d5
import Definitions.Def_WeightedCache3SUM_Alias_4bb45babfe810a30
import Theorems.Thm_ThreeSum_LightSourceRowFlag_flag_le
import Definitions.Def_WeightedCache3SUM_Alias_e80b8f80e26e0eba
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_zero
import Theorems.Thm_ThreeSum_LightSourceRowScan_hash_zero
import Definitions.Def_WeightedCache3SUM_Alias_d4ec36c7dcd9fa6e
import Definitions.Def_WeightedCache3SUM_Alias_b9dca0c4b48e489f
import Theorems.Thm_ThreeSum_SourceFlagProduct_product_zero
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
attribute [local simp] ThreeSum.LightSourceRowScan.count_zero
attribute [local simp] ThreeSum.LightSourceRowScan.hash_zero
attribute [local simp] ThreeSum.SourceFlagProduct.product_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceFlagArray
open Light SourceFlagProduct
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceFlagArray
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ}
    {J L h p cap occ maps candidates histL histR masks n dst bitBase rowOut work U V M K : ℕ}
    (sel candidate mask : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + J * L + 4 ≤ lim.depth) (hp : 0 < p) (hh : h ≤ L) (hocc : occ + J ≤ dst) (hmaps : maps + 2 * L * M ≤ dst)
    (hcandidates : candidates + M ≤ dst) (hleft : histL + K * p ≤ dst) (hright : histR + K * p ≤ dst)
    (hmasks : masks + n ≤ dst) (hdst : dst + 2 * n + 2 ≤ bitBase) (hbits : bitBase + J * L ≤ rowOut)
    (hrowOut : rowOut + 2 ≤ work) (hspace : LightSourceMaskFlags.space work J L U ≤ lim.space)
    (hword : (LightSourceMaskFlags.word J L p U V cap : ℤ) ≤ lim.word) (hsel : ∀ j < J, sel j < M)
    (hcandidate : ∀ s < M, candidate s < K) (hoccRead : ∀ j < J, μ (occ + j) = (sel j : ℤ))
    (hcandidateRead : ∀ s < M, μ (candidates + s) = (candidate s : ℤ))
    (hread0 : ∀ s < M, ∀ a < L, μ (maps + 2 * L * s + a) = (w0 s a : ℤ))
    (hread1 : ∀ s < M, ∀ a < L, μ (maps + 2 * L * s + L + a) = (w1 s a : ℤ)) (hbound0 : ∀ s < M, ∀ a < L, w0 s a ≤ U)
    (hbound1 : ∀ s < M, ∀ a < L, w1 s a ≤ U) (hcountL : ∀ k < K, ∀ r < p, μ (histL + k * p + r) = (leftCount k r : ℤ))
    (hcountR : ∀ k < K, ∀ r < p, μ (histR + k * p + r) = (rightCount k r : ℤ))
    (hcountBoundL : ∀ k < K, ∀ r < p, leftCount k r ≤ V) (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V)
    (hmaskRead : ∀ i < n, μ (masks + i) = (mask i : ℤ)) (hmaskBound : ∀ i < n, mask i < 2 ^ (J * L)) :
    Meets lim P pMain d [J, L, h, p, cap, occ, maps, candidates, histL, histR, masks, n, dst, bitBase, rowOut, work] μ
      (time n J L U)
      (fun _ ν =>
        (∀ i < n, ν (dst + i) = (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ)) ∧
          (∀ i < n, ν (dst + n + i) = (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ)) ∧
            KeptBut μ ν bitBase dst (2 * n + 2)) :=
  by
  have hspace' : work ≤ lim.space := by
    unfold LightSourceMaskFlags.space at hspace
    omega
  have hone : (1 : ℤ) ≤ lim.word := by exact (Int.ofNat_le.mpr (show 1 ≤ lim.space by omega)).trans hw
  apply Meets.of_body S.main
  unfold body time
  refine
    Ends.for
      (Inv μ J L h p cap occ maps candidates histL histR masks n dst bitBase rowOut work sel candidate mask w0 w1
        leftCount rightCount)
      n (LightSourceMaskFlags.time J L U + 192) ?start ?round ?done ?bound
  case start =>
    refine ⟨0, μ, ?_, ?_, ?_, fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj; omega
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨r, ν, rfl, leftWritten, rightWritten, kept⟩
    have hkeep : Kept μ ν dst := by
      intro a ha
      exact kept a ⟨by omega, Or.inl ha⟩
    have hocc' : ∀ j < J, ν (occ + j) = (sel j : ℤ) := by
      intro j hj
      exact (hkeep _ (by omega)).trans (hoccRead j hj)
    have hcan' : ∀ s < M, ν (candidates + s) = (candidate s : ℤ) :=
      by
      intro s hs
      exact (hkeep _ (by omega)).trans (hcandidateRead s hs)
    have hread0' : ∀ s < M, ∀ a < L, ν (maps + 2 * L * s + a) = (w0 s a : ℤ) :=
      by
      intro s hs a ha
      have he := Nat.mul_le_mul_left (2 * L) (show s + 1 ≤ M by omega)
      exact (hkeep _ (by nlinarith)).trans (hread0 s hs a ha)
    have hread1' : ∀ s < M, ∀ a < L, ν (maps + 2 * L * s + L + a) = (w1 s a : ℤ) :=
      by
      intro s hs a ha
      have he := Nat.mul_le_mul_left (2 * L) (show s + 1 ≤ M by omega)
      exact (hkeep _ (by nlinarith)).trans (hread1 s hs a ha)
    have hcountL' : ∀ k < K, ∀ r < p, ν (histL + k * p + r) = (leftCount k r : ℤ) :=
      by
      intro k hk r hr
      have he := Nat.mul_le_mul_right p (show k + 1 ≤ K by omega)
      exact (hkeep _ (by nlinarith)).trans (hcountL k hk r hr)
    have hcountR' : ∀ k < K, ∀ r < p, ν (histR + k * p + r) = (rightCount k r : ℤ) :=
      by
      intro k hk r hr
      have he := Nat.mul_le_mul_right p (show k + 1 ≤ K by omega)
      exact (hkeep _ (by nlinarith)).trans (hcountR k hk r hr)
    have hmask : ν (masks + i) = (mask i : ℤ) := (hkeep _ (by omega)).trans (hmaskRead i hi)
    have hrun :=
      S.flagProcs.meets (d := d + 1) (μ := ν) (J := J) (L := L) (h := h) (p := p) (cap := cap) (occ := occ) (maps :=
        maps) (candidates := candidates) (histL := histL) (histR := histR) (mask := mask i) (dst := dst + 2 * n)
        (bitBase := bitBase) (rowOut := rowOut) (work := work) (U := U) (V := V) (M := M) (K := K) sel candidate w0 w1
        leftCount rightCount hw (by omega) hp hh (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hbits
        hrowOut hspace hword (hmaskBound i hi) hsel hcandidate hocc' hcan' hread0' hread1' hbound0 hbound1 hcountL'
        hcountR' hcountBoundL hcountBoundR
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      first
      | refine _root_.Light.Ends.callToThen (hrun _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hrun ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmask,
              LightSourceMaskFlags.time, LightMaskBits.time, LightMaskErase.time, LightSourceTrim.time,
              LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hmask, LightSourceMaskFlags.time, LightMaskBits.time, LightMaskErase.time, LightSourceTrim.time,
                LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmask, LightSourceMaskFlags.time,
              LightMaskBits.time, LightMaskErase.time, LightSourceTrim.time, LightSourceRowFlag.time,
              LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time] <;> omega)
      on_goal -1 => (rintro q ν₁ ⟨left, right, kept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hl : ν₁ (dst + 2 * n) = (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ) := left
    have hr : ν₁ (dst + 2 * n + 1) = (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ) := right
    have hlB := flag_le J L h p cap sel candidate w0 w1 leftCount (mask i)
    have hrB := flag_le J L h p cap sel candidate w1 w0 rightCount (mask i)
    have haddr : ((dst : ℤ) + 2 * (n : ℤ)).toNat = dst + 2 * n := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using Int.toNat_natCast (dst + 2 * n)
    have haddrR : ((dst : ℤ) + 2 * (n : ℤ) + 1).toNat = dst + 2 * n + 1 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using Int.toNat_natCast (dst + 2 * n + 1)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine
        _root_.Light.Ends.storeToThen (dst + i) (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hl, haddr,
              LightSourceMaskFlags.time, LightMaskBits.time, LightMaskErase.time, LightSourceTrim.time,
              LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hl, haddr, LightSourceMaskFlags.time, LightMaskBits.time, LightMaskErase.time, LightSourceTrim.time,
                LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hl, haddr, LightSourceMaskFlags.time,
              LightMaskBits.time, LightMaskErase.time, LightSourceTrim.time, LightSourceRowFlag.time,
              LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    have hr' :
      Function.update ν₁ (dst + i) (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ) (dst + 2 * n + 1) =
        (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ) :=
      by
      rw [Function.update_of_ne (by omega)]
      exact hr
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine
        _root_.Light.Ends.storeToThen (dst + n + i) (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℕ) ?_ ?_
          ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr', haddrR,
              LightSourceMaskFlags.time, LightMaskBits.time, LightMaskErase.time, LightSourceTrim.time,
              LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hr', haddrR, LightSourceMaskFlags.time, LightMaskBits.time, LightMaskErase.time, LightSourceTrim.time,
                LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget,
                LightSourceFlagTest.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr', haddrR, LightSourceMaskFlags.time,
              LightMaskBits.time, LightMaskErase.time, LightSourceTrim.time, LightSourceRowFlag.time,
              LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, q,
        Function.update (Function.update ν₁ (dst + i) (flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ))
          (dst + n + i) (flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ),
        by simp [update_frame_setLocal], ?_, ?_, ?_⟩
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega)]
        exact (kept₁ _ ⟨by omega, Or.inl (by omega)⟩).trans (leftWritten j hj)
      · simp
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact (kept₁ _ ⟨by omega, Or.inl (by omega)⟩).trans (rightWritten j hj)
      · simp
    · intro a ⟨ha, hout⟩
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact (kept₁ a ⟨ha, by omega⟩).trans (kept a ⟨ha, hout⟩)
  case done =>
    rintro _ _ ⟨r, ν, rfl, left, right, kept⟩
    exact ⟨left, right, kept⟩
  case bound =>
    rintro i _ _ _ ⟨r, ν, rfl, _, _, _⟩
    simp
end Procs
end ThreeSum.LightSourceFlagArray

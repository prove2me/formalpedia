-- Prove2me | solution 1 for ThreeSum.LightWeightedBankSweep.meets_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:59:15.026204+00:00
-- url     : https://prove2.me/submissions/34836a9e-c0cd-4380-af7c-cfbcda9cde29

import Definitions.Def_Submission_Weighted_BankCoordinate
import Definitions.Def_Submission_Weighted_BankSweep
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
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
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_coords_zero
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_high_step
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_low_step
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_zero
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
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.coords_zero
attribute [local simp] ThreeSum.TernaryFrozenQueryStages.stageValue_zero
attribute [local simp] ThreeSum.WeightedBankStageModel.forwardStage_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankSweep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedBankSweep
theorem _root_.solution {N T n pMain pCoord a powers L keyBase base d : ℕ} (hmain : P[pMain]? = some (body pCoord))
    (E : Enumeration N T n) (φ : ℕ → TritWord N → ℤ) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a + n ≤ keyBase) (hmeta : keyBase + 4 * n ≤ powers) (hpows : powers + (2 * N + 1) ≤ base)
    (hspace : base + (N + 1) * n ≤ lim.space) (hNword : 2 * (N : ℤ) + 3 ≤ lim.word) (hL : L ≤ 2 * N)
    (hcodes : ∀ j < n, μ (a + j) = (address (E.word j) : ℤ)) (hsource : ∀ j < n, μ (base + j) = φ 0 (E.word j))
    (hpowers : Powers μ powers (2 * N)) (hd : d + 1 ≤ lim.depth)
    (hcoord :
      ∀ k (hk : k < N),
        ∀ μ' : ℕ → ℤ,
          (∀ j < n, μ' (a + j) = (address (E.word j) : ℤ)) →
            Powers μ' powers (2 * N) →
              (∀ j < n, μ' (base + k * n + j) = φ k (E.word j)) →
                Meets lim P pCoord (d + 1)
                  [N, low (⟨k, hk⟩ : Fin N), high (⟨k, hk⟩ : Fin N), a, n, powers, L, keyBase, base + k * n,
                    base + (k + 1) * n]
                  μ' (LightWeightedBankCoordinate.time N L n)
                  (fun _ μ'' =>
                    (∀ j < n, μ'' (base + (k + 1) * n + j) = φ (k + 1) (E.word j)) ∧
                      LightWeightedBankCoordinate.Preserved μ' μ'' keyBase n (base + (k + 1) * n))) :
    Meets lim P pMain d [N, a, n, powers, L, keyBase, base] μ (time N L n)
      (fun _ μ' => Stages E φ base N μ' ∧ Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2 * N)) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv E φ μ a powers L keyBase base) N (LightWeightedBankCoordinate.time N L n + 80) ?start ?round ?done
      ?bound (hT := by
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
    refine ⟨0, μ, ?_, ?_, ?_, hpowers⟩
    · simp only [update_frame_setLocal]
      congr 1
      simp only [setLocal, List.length_cons, List.length_nil, List.set_cons_succ, List.set_nil, List.replicate_zero,
        List.append_nil]
      change
        frame [(N : ℤ), a, n, powers, L, keyBase, base, 0] = frame ([(N : ℤ), a, n, powers, L, keyBase, base, 0] ++ [0])
      exact (frame_append_zeros _ 1).symm
    · intro s hs j hj
      have hz : s = 0 := by omega
      subst s
      simpa using hsource j hj
    · intro x _ _
      rfl
  case round =>
    rintro k _ hk _ ⟨r, μ', rfl, hstages, hkeep, hp⟩
    have hcm : ∀ j < n, μ' (a + j) = (address (E.word j) : ℤ) :=
      by
      intro j hj
      exact (hkeep _ (Or.inl (by omega)) (Or.inl (by omega))).trans (hcodes j hj)
    have hc := hcoord k hk μ' hcm hp (hstages k le_rfl)
    have hlow := low_step hk
    have hhigh := high_step hk
    have hsub : (N : ℤ) - ((k : ℤ) + 1) = ((N - (k + 1) : ℕ) : ℤ) := by omega
    have hnext : base + (k + 1) * n + n ≤ base + (N + 1) * n :=
      by
      have hm := Nat.mul_le_mul_right n (show k + 2 ≤ N + 1 by omega)
      rw [Nat.add_mul] at hm
      nlinarith
    have hsrcWord : ((base + k * n : ℕ) : ℤ) ≤ lim.word :=
      by
      have hm := Nat.mul_le_mul_right n (show k ≤ N + 1 by omega)
      exact (Int.ofNat_le.mpr (show base + k * n ≤ lim.space by omega)).trans hw
    have hdstWord : ((base + (k + 1) * n : ℕ) : ℤ) ≤ lim.word :=
      by
      have hm := Nat.mul_le_mul_right n (show k + 1 ≤ N + 1 by omega)
      exact (Int.ofNat_le.mpr (show base + (k + 1) * n ≤ lim.space by omega)).trans hw
    have hmulWord : (k : ℤ) * (n : ℤ) ≤ lim.word :=
      by
      have hm := Nat.mul_le_mul_right n (show k ≤ N + 1 by omega)
      exact (by exact_mod_cast (show k * n ≤ lim.space by omega) : (k : ℤ) * (n : ℤ) ≤ (lim.space : ℤ)).trans hw
    have hmulNextWord : ((k : ℤ) + 1) * (n : ℤ) ≤ lim.word :=
      by
      have hm := Nat.mul_le_mul_right n (show k + 1 ≤ N + 1 by omega)
      exact
        (by exact_mod_cast (show (k + 1) * n ≤ lim.space by omega) : ((k : ℤ) + 1) * (n : ℤ) ≤ (lim.space : ℤ)).trans hw
    have hdstWord' : (base : ℤ) + ((k : ℤ) + 1) * (n : ℤ) ≤ lim.word := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hdstWord
    have hmulNextNonneg : 0 ≤ ((k : ℤ) + 1) * (n : ℤ) := mul_nonneg (by omega) (by omega)
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlow, hhigh, hsub,
              LightWeightedBankCoordinate.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hlow, hhigh, hsub, LightWeightedBankCoordinate.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlow, hhigh, hsub,
              LightWeightedBankCoordinate.time] <;>
            omega)
      on_goal -1 => (rintro out μ'' ⟨hout, hcoordKeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, out, μ'', ?_, ?_, ?_, ?_⟩
    · simp [Inv, update_frame_setLocal]
    · intro s hs j hj
      by_cases he : s = k + 1
      · subst s
        exact hout j hj
      · have hsk : s ≤ k := by omega
        have hm := Nat.mul_le_mul_right n hsk
        have hpres :=
          hcoordKeep (base + s * n + j) (Or.inr (by omega))
            (Or.inl
              (by
                rw [Nat.succ_mul]
                omega))
        exact hpres.trans (hstages s hsk j hj)
    · intro x hxMeta hxStages
      have hxOut : x < base + (k + 1) * n ∨ base + (k + 1) * n + n ≤ x :=
        by
        rcases hxStages with hx | hx
        · left
          rw [Nat.succ_mul]
          omega
        · right
          omega
      exact (hcoordKeep x hxMeta hxOut).trans (hkeep x hxMeta hxStages)
    · intro j hj
      exact
        (hcoordKeep (powers + j) (Or.inr (by omega))
              (Or.inl
                (by
                  rw [Nat.succ_mul]
                  omega))).trans
          (hp j hj)
  case done =>
    rintro _ _ ⟨r, μ', rfl, hstages, hkeep, hp⟩
    exact ⟨hstages, hkeep, hp⟩
  case bound =>
    rintro k _ hk _ ⟨r, μ', rfl, hstages, hkeep, hp⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightWeightedBankSweep

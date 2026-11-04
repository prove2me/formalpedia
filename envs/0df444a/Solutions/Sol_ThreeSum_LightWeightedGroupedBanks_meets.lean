-- Prove2me | solution 1 for ThreeSum.LightWeightedGroupedBanks.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:34:17.563025+00:00
-- url     : https://prove2.me/submissions/911fd904-e90f-400f-806c-56756a299eb5

import Definitions.Def_Submission_Weighted_GroupBankStep
import Definitions.Def_Submission_Weighted_GroupedBanks
import Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_program_length
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
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_meets
import Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_program_length
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
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_stageValue_zero
import Theorems.Thm_ThreeSum_WeightedBankStageModel_forwardStage_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
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
attribute [local simp] ThreeSum.LightWeightedGroupedBanks.program_length
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGroupedBanks
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}
namespace ThreeSum.LightWeightedGroupedBanks
theorem _root_.solution {N T n a powers L keyBase groups fsource gsource fbase gbase hbase d V : ℕ}
    (E : Enumeration N T n) (F G : ℕ → TritWord N → ℤ) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a + n ≤ keyBase) (hfs : fsource + groups * n ≤ keyBase) (hgs : gsource + groups * n ≤ keyBase)
    (hmeta : keyBase + 4 * n ≤ powers) (hpows : powers + (2 * N + 1) ≤ fbase)
    (hfg : fbase + groups * ((N + 1) * n) ≤ gbase) (hgh : gbase + groups * ((N + 1) * n) ≤ hbase)
    (hspace : hbase + groups * ((N + 1) * n) ≤ lim.space) (hword : ((n + 2 ^ (2 * N + 1) + 16 : ℕ) : ℤ) ≤ lim.word)
    (hNword : 2 * (N : ℤ) + 3 ≤ lim.word) (hgroupsWord : (groups : ℤ) + 1 ≤ lim.word)
    (hcodes : ∀ j < n, μ (a + j) = (address (E.word j) : ℤ))
    (hsourceF : ∀ g < groups, ∀ j < n, μ (fsource + g * n + j) = F g (E.word j))
    (hsourceG : ∀ g < groups, ∀ j < n, μ (gsource + g * n + j) = G g (E.word j)) (hpowers : Powers μ powers (2 * N))
    (hsorted : ∀ j k, j < k → k < n → address (E.word j) < address (E.word k))
    (hF : ∀ g < groups, ∀ R, |F g R| ≤ (V : ℤ)) (hG : ∀ g < groups, ∀ R, |G g R| ≤ (V : ℤ))
    (hforwardWord : 4 * ((4 ^ N * V : ℕ) : ℤ) + 3 ≤ lim.word)
    (hproductWord : (LightWeightedBankAssembly.valueBound N V : ℤ) ≤ lim.word)
    (hinverseWord : 4 * ((4 ^ N * LightWeightedBankAssembly.valueBound N V : ℕ) : ℤ) + 3 ≤ lim.word) (hL : L ≤ 2 * N)
    (hn : n < 2 ^ L) (hd : d + 2 * N + L + 8 ≤ lim.depth) :
    Meets lim program 19 d [N, a, n, powers, L, keyBase, groups, fsource, gsource, fbase, gbase, hbase] μ
      (time groups N L n)
      (fun _ μ' =>
        GroupStages E (fun g s => forwardStage s (F g)) fbase groups μ' ∧
          GroupStages E (fun g s => forwardStage s (G g)) gbase groups μ' ∧
            GroupStages E (fun g s => stageValue s (LightWeightedBankAssembly.product (F g) (G g))) hbase groups μ' ∧
              Preserved μ μ' keyBase n fbase gbase hbase N groups ∧ Powers μ' powers (2 * N)) :=
  by
  apply Meets.of_body (show program[19]? = some (body 17) from rfl)
  unfold body time
  refine
    Ends.for (Inv E F G μ a powers L keyBase groups fsource gsource fbase gbase hbase) groups
      (LightWeightedGroupBankStep.time N L n + 180) ?start ?round ?done ?bound (hT := by
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
    refine ⟨0, μ, ?_, ?_, ?_, ?_, ?_, hpowers⟩
    · simp only [update_frame_setLocal]
      congr 1
      simp only [setLocal]
      change
        frame [(N : ℤ), a, n, powers, L, keyBase, groups, fsource, gsource, fbase, gbase, hbase, 0] =
          frame ([(N : ℤ), a, n, powers, L, keyBase, groups, fsource, gsource, fbase, gbase, hbase, 0] ++ [0])
      exact (frame_append_zeros _ 1).symm
    · intro g hg; omega
    · intro g hg; omega
    · intro g hg; omega
    · intro x _ _ _ _; rfl
  case round =>
    rintro g _ hg _ ⟨r, μ', rfl, hstF, hstG, hstH, hkeep, hpow⟩
    let stride := (N + 1) * n
    have hnext : g * stride + stride ≤ groups * stride :=
      by
      have hm := Nat.mul_le_mul_right stride (show g + 1 ≤ groups by omega)
      simpa only [Nat.add_mul, Nat.one_mul] using hm
    have hsrcNext : g * n + n ≤ groups * n :=
      by
      have hm := Nat.mul_le_mul_right n (show g + 1 ≤ groups by omega)
      simpa only [Nat.add_mul, Nat.one_mul] using hm
    have hcode' : ∀ j < n, μ' (a + j) = (address (E.word j) : ℤ) :=
      by
      intro j hj
      exact
        (hkeep _ (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans (hcodes j hj)
    have hsf : ∀ j < n, μ' (fsource + g * n + j) = F g (E.word j) :=
      by
      intro j hj
      exact
        (hkeep _ (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
          (hsourceF g hg j hj)
    have hsg : ∀ j < n, μ' (gsource + g * n + j) = G g (E.word j) :=
      by
      intro j hj
      exact
        (hkeep _ (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
          (hsourceG g hg j hj)
    have hc :=
      LightWeightedGroupBankStep.meets (tail := [LightWeightedGroupBankStep.body 18, copyBody, body 17]) (pMain := 17)
        (pCopy := 18) (d := d + 1) (fsource := fsource + g * n) (gsource := gsource + g * n) (fbase :=
        fbase + g * stride) (gbase := gbase + g * stride) (hbase := hbase + g * stride) rfl rfl E (F g) (G g) μ' hw ha
        (by omega) (by omega) hmeta (by omega) (by dsimp [stride] at *; omega) (by dsimp [stride] at *; omega)
        (by dsimp [stride] at *; omega) hword hNword hcode' hsf hsg hpow hsorted (hF g hg) (hG g hg) hforwardWord
        hproductWord hinverseWord hL hn (by omega)
    have hgstride : ((g : ℤ) * ((N : ℤ) + 1) * (n : ℤ)) ≤ lim.word :=
      by
      have : g * stride ≤ lim.space := by dsimp [stride] at *; omega
      exact
        (by
              dsimp [stride] at this
              simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, mul_assoc] using Int.ofNat_le.mpr this :
              (g : ℤ) * ((N : ℤ) + 1) * (n : ℤ) ≤ (lim.space : ℤ)).trans
          hw
    have hstrideWord : ((N : ℤ) + 1) * (n : ℤ) ≤ lim.word :=
      by
      have : stride ≤ lim.space := by dsimp [stride] at *; omega
      exact
        (by
              dsimp [stride] at this
              simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, mul_assoc] using Int.ofNat_le.mpr this :
              ((N : ℤ) + 1) * (n : ℤ) ≤ (lim.space : ℤ)).trans
          hw
    have haddr (b : ℕ) (hb : b ≤ hbase) : (b : ℤ) + (g : ℤ) * ((N : ℤ) + 1) * (n : ℤ) ≤ lim.word :=
      by
      have : b + g * stride ≤ lim.space := by dsimp [stride] at *; omega
      exact
        (by
              dsimp [stride] at this
              simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, mul_assoc] using Int.ofNat_le.mpr this :
              (b : ℤ) + (g : ℤ) * ((N : ℤ) + 1) * (n : ℤ) ≤ (lim.space : ℤ)).trans
          hw
    have hfaddr := haddr fbase (by omega)
    have hgaddr := haddr gbase (by omega)
    have hhaddr := haddr hbase le_rfl
    have hsrcMulWord : (g : ℤ) * (n : ℤ) ≤ lim.word := by
      exact (by exact_mod_cast (show g * n ≤ lim.space by omega) : (g : ℤ) * (n : ℤ) ≤ (lim.space : ℤ)).trans hw
    have hfsaddr : (fsource : ℤ) + (g : ℤ) * (n : ℤ) ≤ lim.word := by
      exact
        (by exact_mod_cast (show fsource + g * n ≤ lim.space by omega) :
              (fsource : ℤ) + (g : ℤ) * (n : ℤ) ≤ (lim.space : ℤ)).trans
          hw
    have hgsaddr : (gsource : ℤ) + (g : ℤ) * (n : ℤ) ≤ lim.word := by
      exact
        (by exact_mod_cast (show gsource + g * n ≤ lim.space by omega) :
              (gsource : ℤ) + (g : ℤ) * (n : ℤ) ≤ (lim.space : ℤ)).trans
          hw
    have hstrideNN : 0 ≤ ((N : ℤ) + 1) * (n : ℤ) := by positivity
    have hmulNN : 0 ≤ (g : ℤ) * ((N : ℤ) + 1) * (n : ℤ) := by positivity
    have hmulAssoc : (g : ℤ) * (((N : ℤ) + 1) * (n : ℤ)) = (g : ℤ) * ((N : ℤ) + 1) * (n : ℤ) := by ring
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, stride,
              LightWeightedGroupBankStep.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [stride, LightWeightedGroupBankStep.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, stride, LightWeightedGroupBankStep.time] <;>
            omega)
      on_goal -1 =>
        (rintro out ν ⟨houtF, houtG, houtH, hstepKeep, hpow'⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, out, ν, ?_, ?_, ?_, ?_, ?_, hpow'⟩
    · simp [Inv, update_frame_setLocal]
    · intro j hj
      by_cases he : j = g
      · subst j; exact houtF
      · have hjg : j < g := by omega
        intro s hs k hk
        have hm := Nat.mul_le_mul_right stride (show j + 1 ≤ g by omega)
        have hs' := Nat.mul_le_mul_right n hs
        have hlen : stride = N * n + n := by dsimp [stride]; ring
        have hpart : s * n + k < stride := by omega
        have hprior : j * stride + s * n + k < g * stride :=
          by
          rw [Nat.add_mul, Nat.one_mul] at hm
          omega
        have hFtoG : fbase + g * stride + stride ≤ gbase := by dsimp [stride] at *; omega
        have hGtoH : gbase + g * stride + stride ≤ hbase := by dsimp [stride] at *; omega
        exact
          (hstepKeep _ (Or.inr (by dsimp only [stride] at *; omega)) (Or.inl (by dsimp only [stride] at *; omega))
                (Or.inl (by dsimp only [stride] at *; omega)) (Or.inl (by dsimp only [stride] at *; omega))).trans
            (hstF j hjg s hs k hk)
    · intro j hj
      by_cases he : j = g
      · subst j; exact houtG
      · have hjg : j < g := by omega
        intro s hs k hk
        have hm := Nat.mul_le_mul_right stride (show j + 1 ≤ g by omega)
        have hs' := Nat.mul_le_mul_right n hs
        have hlen : stride = N * n + n := by dsimp [stride]; ring
        have hpart : s * n + k < stride := by omega
        have hprior : j * stride + s * n + k < g * stride :=
          by
          rw [Nat.add_mul, Nat.one_mul] at hm
          omega
        have hFtoG : fbase + g * stride + stride ≤ gbase := by dsimp [stride] at *; omega
        have hGtoH : gbase + g * stride + stride ≤ hbase := by dsimp [stride] at *; omega
        exact
          (hstepKeep _ (Or.inr (by dsimp only [stride] at *; omega)) (Or.inr (by dsimp only [stride] at *; omega))
                (Or.inl (by dsimp only [stride] at *; omega)) (Or.inl (by dsimp only [stride] at *; omega))).trans
            (hstG j hjg s hs k hk)
    · intro j hj
      by_cases he : j = g
      · subst j; exact houtH
      · have hjg : j < g := by omega
        intro s hs k hk
        have hm := Nat.mul_le_mul_right stride (show j + 1 ≤ g by omega)
        have hs' := Nat.mul_le_mul_right n hs
        have hlen : stride = N * n + n := by dsimp [stride]; ring
        have hpart : s * n + k < stride := by omega
        have hprior : j * stride + s * n + k < g * stride :=
          by
          rw [Nat.add_mul, Nat.one_mul] at hm
          omega
        have hFtoG : fbase + g * stride + stride ≤ gbase := by dsimp [stride] at *; omega
        have hGtoH : gbase + g * stride + stride ≤ hbase := by dsimp [stride] at *; omega
        exact
          (hstepKeep _ (Or.inr (by dsimp only [stride] at *; omega)) (Or.inr (by dsimp only [stride] at *; omega))
                (Or.inr (by dsimp only [stride] at *; omega)) (Or.inl (by dsimp only [stride] at *; omega))).trans
            (hstH j hjg s hs k hk)
    · intro x hm hf hg' hh
      have hfgap : x < fbase + g * stride ∨ fbase + g * stride + stride ≤ x := by dsimp [stride] at *; omega
      have hggap : x < gbase + g * stride ∨ gbase + g * stride + stride ≤ x := by dsimp [stride] at *; omega
      have hhgap : x < hbase + g * stride ∨ hbase + g * stride + stride ≤ x := by dsimp [stride] at *; omega
      exact (hstepKeep x hm hfgap hggap hhgap).trans (hkeep x hm hf hg' hh)
  case done =>
    rintro _ _ ⟨r, μ', rfl, hF', hG', hH', hkeep, hpow⟩
    exact ⟨hF', hG', hH', hkeep, hpow⟩
  case bound =>
    rintro g _ hg _ ⟨r, μ', rfl, hF', hG', hH', hkeep, hpow⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightWeightedGroupedBanks

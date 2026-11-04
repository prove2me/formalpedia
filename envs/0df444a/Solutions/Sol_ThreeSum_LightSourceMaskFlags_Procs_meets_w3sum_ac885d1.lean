-- Prove2me | solution 1 for ThreeSum.LightSourceMaskFlags.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:42.26606+00:00
-- url     : https://prove2.me/submissions/051bc2a4-6df5-43ab-8566-9ee49c694843

import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightSourceMaskFlags
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightMaskBits_bit_le
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_8f9b8fc511f535d5
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
open ThreeSum ThreeSum.LightSourceMaskFlags
open Light SourceFlagProduct
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceMaskFlags
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ}
    {J L h p cap occ maps candidates histL histR mask dst bitBase rowOut work U V M K : ℕ} (sel candidate : ℕ → ℕ)
    (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + J * L + 3 ≤ lim.depth)
    (hp : 0 < p) (hh : h ≤ L) (hocc : occ + J ≤ bitBase) (hmaps : maps + 2 * L * M ≤ bitBase)
    (hcandidates : candidates + M ≤ bitBase) (hleft : histL + K * p ≤ bitBase) (hright : histR + K * p ≤ bitBase)
    (hdst : dst + 2 ≤ bitBase) (hbits : bitBase + J * L ≤ rowOut) (hrowOut : rowOut + 2 ≤ work)
    (hspace : space work J L U ≤ lim.space) (hword : (word J L p U V cap : ℤ) ≤ lim.word) (hmask : mask < 2 ^ (J * L))
    (hsel : ∀ j < J, sel j < M) (hcandidate : ∀ s < M, candidate s < K) (hoccRead : ∀ j < J, μ (occ + j) = (sel j : ℤ))
    (hcandidateRead : ∀ s < M, μ (candidates + s) = (candidate s : ℤ))
    (hread0 : ∀ s < M, ∀ a < L, μ (maps + 2 * L * s + a) = (w0 s a : ℤ))
    (hread1 : ∀ s < M, ∀ a < L, μ (maps + 2 * L * s + L + a) = (w1 s a : ℤ)) (hbound0 : ∀ s < M, ∀ a < L, w0 s a ≤ U)
    (hbound1 : ∀ s < M, ∀ a < L, w1 s a ≤ U) (hcountL : ∀ k < K, ∀ r < p, μ (histL + k * p + r) = (leftCount k r : ℤ))
    (hcountR : ∀ k < K, ∀ r < p, μ (histR + k * p + r) = (rightCount k r : ℤ))
    (hcountBoundL : ∀ k < K, ∀ r < p, leftCount k r ≤ V) (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V) :
    Meets lim P pMain d [J, L, h, p, cap, occ, maps, candidates, histL, histR, mask, dst, bitBase, rowOut, work] μ
      (time J L U)
      (fun _ ν =>
        ν dst =
            (product (LightSourceTrim.rowFlag L h p cap sel candidate (LightMaskBits.bit (J * L) mask) w0 w1 leftCount)
                J :
              ℤ) ∧
          ν (dst + 1) =
              (product
                  (LightSourceTrim.rowFlag L h p cap sel candidate (LightMaskBits.bit (J * L) mask) w1 w0 rightCount)
                  J :
                ℤ) ∧
            KeptBut μ ν bitBase dst 2) :=
  by
  have hspaceBits : work + (J * L + 1) ≤ lim.space := (Nat.add_le_add_left (le_max_left _ _) work).trans hspace
  have hspaceTrim : LightSourceRowFlag.space work L U ≤ lim.space :=
    by
    have hh := (Nat.add_le_add_left (le_max_right (J * L + 1) (3 + (Nat.log 2 (L * U + 1) + 2))) work).trans hspace
    simpa only [LightSourceRowFlag.space, Nat.add_assoc] using hh
  have hwordBits : ((2 ^ (J * L + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : 2 ^ (J * L + 1) ≤ word J L p U V cap := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwordTrim : (LightSourceRowFlag.word L p U V cap : ℤ) ≤ lim.word :=
    by
    have hh : LightSourceRowFlag.word L p U V cap ≤ word J L p U V cap := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwidth : (J : ℤ) * (L : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast (show J * L ≤ lim.space by omega) : (J : ℤ) * (L : ℤ) ≤ lim.space).trans hw
  apply Meets.of_body S.main
  unfold body time
  have hb :=
    LightMaskBits.meets (d := d + 1) (μ := μ) (L := J * L) (m := mask) (dst := bitBase) (work := work) S.bits S.powers
      S.erase hw (by omega) hspaceBits (by omega) hwordBits hmask
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
    | refine _root_.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskBits.time, LightMaskErase.time,
            LightSourceTrim.time, LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget,
            LightSourceFlagTest.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightMaskBits.time, LightMaskErase.time, LightSourceTrim.time, LightSourceRowFlag.time,
              LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskBits.time, LightMaskErase.time,
            LightSourceTrim.time, LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget,
            LightSourceFlagTest.time] <;> omega)
    on_goal -1 => (rintro r ν₁ ⟨bitsRead, _, kept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hkeep : Kept μ ν₁ bitBase := by
    intro a ha
    exact kept₁ a ⟨by omega, Or.inl ha⟩
  have hoccRead₁ : ∀ j < J, ν₁ (occ + j) = (sel j : ℤ) :=
    by
    intro j hj
    exact (hkeep _ (by omega)).trans (hoccRead j hj)
  have hcandRead₁ : ∀ s < M, ν₁ (candidates + s) = (candidate s : ℤ) :=
    by
    intro s hs
    exact (hkeep _ (by omega)).trans (hcandidateRead s hs)
  have hread0₁ : ∀ s < M, ∀ a < L, ν₁ (maps + 2 * L * s + a) = (w0 s a : ℤ) :=
    by
    intro s hs a ha
    have he := Nat.mul_le_mul_left (2 * L) (show s + 1 ≤ M by omega)
    exact (hkeep _ (by nlinarith)).trans (hread0 s hs a ha)
  have hread1₁ : ∀ s < M, ∀ a < L, ν₁ (maps + 2 * L * s + L + a) = (w1 s a : ℤ) :=
    by
    intro s hs a ha
    have he := Nat.mul_le_mul_left (2 * L) (show s + 1 ≤ M by omega)
    exact (hkeep _ (by nlinarith)).trans (hread1 s hs a ha)
  have hcountL₁ : ∀ k < K, ∀ r < p, ν₁ (histL + k * p + r) = (leftCount k r : ℤ) :=
    by
    intro k hk r hr
    have he := Nat.mul_le_mul_right p (show k + 1 ≤ K by omega)
    exact (hkeep _ (by nlinarith)).trans (hcountL k hk r hr)
  have hcountR₁ : ∀ k < K, ∀ r < p, ν₁ (histR + k * p + r) = (rightCount k r : ℤ) :=
    by
    intro k hk r hr
    have he := Nat.mul_le_mul_right p (show k + 1 ≤ K by omega)
    exact (hkeep _ (by nlinarith)).trans (hcountR k hk r hr)
  have ht :=
    S.trim.meets (d := d + 1) (μ := ν₁) (J := J) (L := L) (h := h) (p := p) (cap := cap) (occ := occ) (maps := maps)
      (candidates := candidates) (histL := histL) (histR := histR) (bitBase := bitBase) (rowOut := rowOut) (work :=
      work) (dst := dst) (U := U) (V := V) (M := M) (K := K) sel candidate (LightMaskBits.bit (J * L) mask) w0 w1
      leftCount rightCount hw (by omega) hp hh (by omega) (by omega) (by omega) (by omega) (by omega) hbits hrowOut
      (by omega) hspaceTrim hwordTrim hsel hcandidate hoccRead₁ hcandRead₁ bitsRead
      (fun i _ => LightMaskBits.bit_le _ _ i) hread0₁ hread1₁ hbound0 hbound1 hcountL₁ hcountR₁ hcountBoundL
      hcountBoundR
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
    | refine _root_.Light.Ends.callToThen (ht _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen ht ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskBits.time, LightMaskErase.time,
            LightSourceTrim.time, LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget,
            LightSourceFlagTest.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightMaskBits.time, LightMaskErase.time, LightSourceTrim.time, LightSourceRowFlag.time,
              LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskBits.time, LightMaskErase.time,
            LightSourceTrim.time, LightSourceRowFlag.time, LightSourceRowScan.time, LightResidues.residueBudget,
            LightSourceFlagTest.time] <;> omega)
    on_goal -1 => (rintro r ν₂ ⟨left, right, kept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨left, right, ?_⟩
  intro a ⟨ha, hout⟩
  exact (kept₂ a ⟨by omega, hout⟩).trans (hkeep a ha)
end Procs
end ThreeSum.LightSourceMaskFlags

-- Prove2me | solution 1 for ThreeSum.LightSourcePreparation.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:17:00.444319+00:00
-- url     : https://prove2.me/submissions/5931f03b-226e-4e55-9c7d-0ed2c131d27f

import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightSourceFlagArray
import Definitions.Def_Submission_ThreeSum_LightSourcePreparation
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_bff01fd4b2900a53
import Definitions.Def_WeightedCache3SUM_Alias_8f9b8fc511f535d5
import Definitions.Def_WeightedCache3SUM_Alias_4bb45babfe810a30
import Definitions.Def_WeightedCache3SUM_Alias_e80b8f80e26e0eba
import Definitions.Def_WeightedCache3SUM_Alias_d4ec36c7dcd9fa6e
import Definitions.Def_WeightedCache3SUM_Alias_b9dca0c4b48e489f
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourcePreparation
open Light BlockCoefficientRows
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourcePreparation
namespace Procs
theorem _root_.solution {pMain : ℕ} (C : Procs P pMain) {μ : ℕ → ℤ}
    {J L h p cap occ maps candidates histL histR masks n coeff0 coeff1 rawLeft rawRight flags bitBase rowOut work U V M
      K : ℕ}
    (sel candidate mask : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + J * L + 5 ≤ lim.depth) (hp : 0 < p) (hh : h ≤ L) (hocc : occ + J ≤ coeff0)
    (hmaps : maps + 2 * L * M ≤ coeff0) (hcandidates : candidates + M ≤ coeff0) (hleft : histL + K * p ≤ coeff0)
    (hright : histR + K * p ≤ coeff0) (hmasks : masks + n ≤ coeff0) (hc0 : coeff0 + J * L ≤ coeff1)
    (hc1 : coeff1 + J * L ≤ rawLeft) (hrawLeft : rawLeft + n ≤ rawRight) (hrawRight : rawRight + n ≤ flags)
    (hflags : flags + 2 * n + 2 ≤ bitBase) (hbits : bitBase + J * L ≤ rowOut) (hrowOut : rowOut + 2 ≤ work)
    (hspace : space work J L U ≤ lim.space) (hword : (word J L p U V cap : ℤ) ≤ lim.word) (hsel : ∀ j < J, sel j < M)
    (hcandidate : ∀ s < M, candidate s < K) (hoccRead : ∀ j < J, μ (occ + j) = (sel j : ℤ))
    (hcandidateRead : ∀ s < M, μ (candidates + s) = (candidate s : ℤ))
    (hread0 : ∀ s < M, ∀ a < L, μ (maps + 2 * L * s + a) = (w0 s a : ℤ))
    (hread1 : ∀ s < M, ∀ a < L, μ (maps + 2 * L * s + L + a) = (w1 s a : ℤ)) (hbound0 : ∀ s < M, ∀ a < L, w0 s a ≤ U)
    (hbound1 : ∀ s < M, ∀ a < L, w1 s a ≤ U) (hcountL : ∀ k < K, ∀ r < p, μ (histL + k * p + r) = (leftCount k r : ℤ))
    (hcountR : ∀ k < K, ∀ r < p, μ (histR + k * p + r) = (rightCount k r : ℤ))
    (hcountBoundL : ∀ k < K, ∀ r < p, leftCount k r ≤ V) (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V)
    (hmaskRead : ∀ i < n, μ (masks + i) = (mask i : ℤ)) (hmaskBound : ∀ i < n, mask i < 2 ^ (J * L)) :
    Meets lim P pMain d
      [J, L, h, p, cap, occ, maps, candidates, histL, histR, masks, n, coeff0, coeff1, rawLeft, rawRight, flags,
        bitBase, rowOut, work]
      μ (time n J L U)
      (fun _ ν =>
        (∀ i < n, ν (rawLeft + i) = (OneHotMask.eval (flat J L p sel w0) (flat J L p sel w1) (J * L) (mask i) : ℤ)) ∧
          (∀ i < n, ν (rawRight + i) = (OneHotMask.eval (flat J L p sel w1) (flat J L p sel w0) (J * L) (mask i) : ℤ)) ∧
            (∀ i < n,
                ν (flags + i) = (LightSourceFlagArray.flag J L h p cap sel candidate w0 w1 leftCount (mask i) : ℤ)) ∧
              (∀ i < n,
                  ν (flags + n + i) =
                    (LightSourceFlagArray.flag J L h p cap sel candidate w1 w0 rightCount (mask i) : ℤ)) ∧
                Kept μ ν coeff0) :=
  by
  have hsHash : LightBlockSourceHashes.space work J L ≤ lim.space := (le_max_left _ _).trans hspace
  have hsFlag : LightSourceMaskFlags.space work J L U ≤ lim.space := (le_max_right _ _).trans hspace
  have hwHash : (LightBlockSourceHashes.word J L p U : ℤ) ≤ lim.word :=
    by
    have hh : LightBlockSourceHashes.word J L p U ≤ word J L p U V cap := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwFlag : (LightSourceMaskFlags.word J L p U V cap : ℤ) ≤ lim.word :=
    by
    have hh : LightSourceMaskFlags.word J L p U V cap ≤ word J L p U V cap := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  apply Meets.of_body C.main
  unfold body time
  have hhash :=
    C.hashes.meets (d := d + 1) (μ := μ) (J := J) (L := L) (p := p) (occ := occ) (maps := maps) (coeff0 := coeff0)
      (coeff1 := coeff1) (masks := masks) (rawLeft := rawLeft) (rawRight := rawRight) (n := n) (work := work) (U := U)
      (M := M) sel mask w0 w1 hw hp (by omega) hsHash hocc hmaps hmasks hc0 hc1 hrawLeft (by omega) hwHash hsel hoccRead
      hread0 hread1 hbound0 hbound1 hmaskRead hmaskBound
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
    | refine _root_.Light.Ends.callToThen (hhash _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hhash ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBlockSourceHashes.time,
            LightBlockCoefficients.time, LightBlockCoefficients.roundTime, LightMaskHashes.time, LightOneHot.time,
            LightScaleArray.time, LightSourceFlagArray.time, LightSourceMaskFlags.time, LightMaskBits.time,
            LightSourceTrim.time, LightSourceRowFlag.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBlockSourceHashes.time, LightBlockCoefficients.time, LightBlockCoefficients.roundTime,
              LightMaskHashes.time, LightOneHot.time, LightScaleArray.time, LightSourceFlagArray.time,
              LightSourceMaskFlags.time, LightMaskBits.time, LightSourceTrim.time, LightSourceRowFlag.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBlockSourceHashes.time,
            LightBlockCoefficients.time, LightBlockCoefficients.roundTime, LightMaskHashes.time, LightOneHot.time,
            LightScaleArray.time, LightSourceFlagArray.time, LightSourceMaskFlags.time, LightMaskBits.time,
            LightSourceTrim.time, LightSourceRowFlag.time] <;> omega)
    on_goal -1 => (rintro r ν₁ ⟨rawL, rawR, rows, kept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hocc' : ∀ j < J, ν₁ (occ + j) = (sel j : ℤ) := by
    intro j hj
    exact (kept₁ _ (by omega)).trans (hoccRead j hj)
  have hcan' : ∀ s < M, ν₁ (candidates + s) = (candidate s : ℤ) :=
    by
    intro s hs
    exact (kept₁ _ (by omega)).trans (hcandidateRead s hs)
  have hread0' : ∀ s < M, ∀ a < L, ν₁ (maps + 2 * L * s + a) = (w0 s a : ℤ) :=
    by
    intro s hs a ha
    have he := Nat.mul_le_mul_left (2 * L) (show s + 1 ≤ M by omega)
    exact (kept₁ _ (by nlinarith)).trans (hread0 s hs a ha)
  have hread1' : ∀ s < M, ∀ a < L, ν₁ (maps + 2 * L * s + L + a) = (w1 s a : ℤ) :=
    by
    intro s hs a ha
    have he := Nat.mul_le_mul_left (2 * L) (show s + 1 ≤ M by omega)
    exact (kept₁ _ (by nlinarith)).trans (hread1 s hs a ha)
  have hcountL' : ∀ k < K, ∀ r < p, ν₁ (histL + k * p + r) = (leftCount k r : ℤ) :=
    by
    intro k hk r hr
    have he := Nat.mul_le_mul_right p (show k + 1 ≤ K by omega)
    exact (kept₁ _ (by nlinarith)).trans (hcountL k hk r hr)
  have hcountR' : ∀ k < K, ∀ r < p, ν₁ (histR + k * p + r) = (rightCount k r : ℤ) :=
    by
    intro k hk r hr
    have he := Nat.mul_le_mul_right p (show k + 1 ≤ K by omega)
    exact (kept₁ _ (by nlinarith)).trans (hcountR k hk r hr)
  have hmask' : ∀ i < n, ν₁ (masks + i) = (mask i : ℤ) :=
    by
    intro i hi
    exact (kept₁ _ (by omega)).trans (hmaskRead i hi)
  have hf :=
    C.flags.meets (d := d + 1) (μ := ν₁) (J := J) (L := L) (h := h) (p := p) (cap := cap) (occ := occ) (maps := maps)
      (candidates := candidates) (histL := histL) (histR := histR) (masks := masks) (n := n) (dst := flags) (bitBase :=
      bitBase) (rowOut := rowOut) (work := work) (U := U) (V := V) (M := M) (K := K) sel candidate mask w0 w1 leftCount
      rightCount hw (by omega) hp hh (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hflags hbits
      hrowOut hsFlag hwFlag hsel hcandidate hocc' hcan' hread0' hread1' hbound0 hbound1 hcountL' hcountR' hcountBoundL
      hcountBoundR hmask' hmaskBound
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
    | refine _root_.Light.Ends.callToThen (hf _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hf ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightBlockSourceHashes.time,
            LightBlockCoefficients.time, LightBlockCoefficients.roundTime, LightMaskHashes.time, LightOneHot.time,
            LightScaleArray.time, LightSourceFlagArray.time, LightSourceMaskFlags.time, LightMaskBits.time,
            LightSourceTrim.time, LightSourceRowFlag.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightBlockSourceHashes.time, LightBlockCoefficients.time, LightBlockCoefficients.roundTime,
              LightMaskHashes.time, LightOneHot.time, LightScaleArray.time, LightSourceFlagArray.time,
              LightSourceMaskFlags.time, LightMaskBits.time, LightSourceTrim.time, LightSourceRowFlag.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightBlockSourceHashes.time,
            LightBlockCoefficients.time, LightBlockCoefficients.roundTime, LightMaskHashes.time, LightOneHot.time,
            LightScaleArray.time, LightSourceFlagArray.time, LightSourceMaskFlags.time, LightMaskBits.time,
            LightSourceTrim.time, LightSourceRowFlag.time] <;> omega)
    on_goal -1 => (rintro r ν₂ ⟨leftFlags, rightFlags, kept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, ?_, leftFlags, rightFlags, ?_⟩
  · intro i hi
    exact (kept₂ _ ⟨by omega, Or.inl (by omega)⟩).trans (rawL i hi)
  · intro i hi
    exact (kept₂ _ ⟨by omega, Or.inl (by omega)⟩).trans (rawR i hi)
  · intro a ha
    exact (kept₂ a ⟨by omega, Or.inl (by omega)⟩).trans (kept₁ a ha)
end Procs
end ThreeSum.LightSourcePreparation

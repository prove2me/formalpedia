-- Prove2me | solution 1 for ThreeSum.LightTernaryProductChannel.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:49:31.635528+00:00
-- url     : https://prove2.me/submissions/24f0c077-3247-4144-8916-f4d5ea7cb6a9

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_LightTernaryProductChannel
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_Light_wrote_rest
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryWeightChannels_leftMoment_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_powerCircuit_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_rightMoment_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_scalarPower_eval
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryWeightChannels.leftMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.powerCircuit_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.rightMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.scalarPower_eval
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryProductChannel
open Light TernaryWeightChannels
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryProductChannel
theorem _root_.solution {p src n width a b dst U : ℕ} (hmain : P[p]? = some body) (μ : ℕ → ℤ) (F : ℕ → ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (ha : a < width) (hb : b < width) (hsrc : src + n * width ≤ dst)
    (hdst : dst + n ≤ lim.space) (hread : ∀ i < n, ∀ j < width, μ (src + i * width + j) = F i j)
    (hf : ∀ i < n, ∀ j < width, |F i j| ≤ (U : ℤ)) (hword : ((U : ℤ) + 1) ^ 2 ≤ lim.word) :
    Meets lim P p d [src, n, width, a, b, dst] μ (time n)
      (fun _ ν => (∀ i < n, ν (dst + i) = F i a * F i b) ∧ SameOutside μ ν dst n) :=
  by
  have hU : (U : ℤ) ≤ lim.word := by
    have hu : (0 : ℤ) ≤ U := by positivity
    nlinarith
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.pass (fun i => F i a * F i b) ?round
      ⟨fun i hi => by dsimp only; exact wrote_done hi, by
        ( try refine _root_.Light.SameOn.cell ?_
          intro x_p2m_13949945568761573396 hx_p2m_13949945568761573396
          first
          | ((  repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_9146430557733125380);
                    (try have := h_p2m_9146430557733125380 x_p2m_13949945568761573396 (by omega));
                    revert h_p2m_9146430557733125380)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          |
            (simp [] at hx_p2m_13949945568761573396;
              ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_5639388193974934293);
                    (try have := h_p2m_5639388193974934293 x_p2m_13949945568761573396 (by omega));
                    revert h_p2m_5639388193974934293)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          | ( ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_169112293001390194);
                    (try have := h_p2m_169112293001390194 x_p2m_13949945568761573396 (by omega));
                    revert h_p2m_169112293001390194)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
              fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                          its condition K x does not follow from the hypotheses."))⟩
      hw hdst rfl rfl
  case round =>
    intro i hi
    have hm := Nat.mul_le_mul_right width (show i + 1 ≤ n by omega)
    simp only [Nat.add_mul, one_mul] at hm
    have hlowA : src + i * width + a < dst := by omega
    have hlowB : src + i * width + b < dst := by omega
    have hrA : wrote μ dst (fun i => F i a * F i b) i (src + i * width + a) = F i a :=
      (wrote_rest (Or.inl hlowA)).trans (hread i hi a ha)
    have hrB : wrote μ dst (fun i => F i a * F i b) i (src + i * width + b) = F i b :=
      (wrote_rest (Or.inl hlowB)).trans (hread i hi b hb)
    have hwidth : width ≤ lim.space := by omega
    have hwidthW : (width : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hwidth).trans hw
    have hmulW : (i : ℤ) * (width : ℤ) ≤ lim.word :=
      by
      have hh : i * width ≤ lim.space := by omega
      have hhZ : (i : ℤ) * (width : ℤ) ≤ (lim.space : ℤ) := by exact_mod_cast hh
      exact hhZ.trans hw
    have hA := abs_le.mp (hf i hi a ha)
    have hB := abs_le.mp (hf i hi b hb)
    have hprod : |F i a * F i b| ≤ lim.word := by
      rw [abs_mul]
      have hh := mul_le_mul (hf i hi a ha) (hf i hi b hb) (abs_nonneg _) (Int.natCast_nonneg U)
      exact hh.trans (by nlinarith [Int.natCast_nonneg U])
    have hprod' := abs_le.mp hprod
    have haddrA : ((src : ℤ) + (i : ℤ) * (width : ℤ) + (a : ℤ)).toNat = src + i * width + a := by norm_cast
    have haddrB : ((src : ℤ) + (i : ℤ) * (width : ℤ) + (b : ℤ)).toNat = src + i * width + b := by norm_cast
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrA, hrB, haddrA, haddrB] <;> omega)
end ThreeSum.LightTernaryProductChannel

-- Prove2me | solution 1 for TaoFivePrimes.short_interval_zero_moment_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T19:28:07.562552+00:00
-- url     : https://prove2.me/submissions/335b32e3-c7f2-4a0c-a28e-c612ec5cf622

import Mathlib
import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Theorems.Thm_TaoFivePrimes_positive_zero_nineteenth_moment_tail
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterWeights

set_option maxHeartbeats 1000000
noncomputable section
open ExplicitPNT.DusartTable1
namespace ShortPrimeIntervalZeroMoments

/-- The actual positive-zero estimate gives both signs of the imaginary part. -/
theorem finite_absolute_tail (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ)
    (H : ℝ) (hH : (10 : ℝ)^8 ≤ H) (hlog : Real.log H ≤ 22)
    (hγ : ∀ ρ ∈ Z, H < |ρ.im|) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*(1/|ρ.im|^19)) ≤ 1/(2*H^18) := by
  classical
  let W : ℝ → ℝ := fun t => if H < t then 1/t^19 else 0
  have hpos (S : Finset ℂ)
      (hS : ∀ ρ ∈ S, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
      (∑ ρ ∈ S, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*W ρ.im) ≤ 1/(4*H^18) := by
    let F := S.filter (fun ρ => H < ρ.im)
    have hF : ∀ ρ ∈ F, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im :=
      fun ρ hρ => hS ρ (Finset.mem_filter.mp hρ).1
    have h := TaoFivePrimes.positive_zero_nineteenth_moment_tail F hF H hH hlog
      (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
    simpa only [F, W, Finset.sum_filter, mul_ite, mul_zero] using h
  have h := ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights.1 W (1/(4*H^18)) hpos Z hZ
  have he : (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*W |ρ.im|) =
      ∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*(1/|ρ.im|^19) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [W, if_pos (hγ ρ hρ)]
  rw [he] at h
  exact h.trans_eq (by ring)

theorem absolute_tail (H : ℝ) (hH : (10 : ℝ)^8 ≤ H) (hlog : Real.log H ≤ 22) :
    (∑' ρ : StrictHighAbsoluteZero H,
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*(1/|ρ.val.im|^19)) ≤ 1/(2*H^18) := by
  classical
  apply Real.tsum_le_of_sum_le
  · intro ρ
    positivity
  · intro S
    let Z : Finset ℂ := S.image (fun ρ : StrictHighAbsoluteZero H => ρ.val)
    have hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.1
    have hγ : ∀ ρ ∈ Z, H < |ρ.im| := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.2
    have h := finite_absolute_tail Z hZ H hH hlog hγ
    dsimp [Z] at h
    rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at h
    exact h

/-- Finite RH is kept as a hypothesis: below H the weight is x^(-1/2),
and above H the unconditional absolute moment suffices. -/
theorem finite_weighted_tail_of_finite_rh (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ)
    (x T H : ℝ) (hx : 1 ≤ x) (hT : (10 : ℝ)^8 ≤ T) (hTH : T ≤ H)
    (hlog : Real.log H ≤ 22) (hγ : ∀ ρ ∈ Z, T < |ρ.im|)
    (hRH : ∀ ρ : ℂ, DusartSmoothing.RvM.IsNontrivialZero ρ → |ρ.im| ≤ H → ρ.re = 1/2) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*
      x^(ρ.re-1)*(1/|ρ.im|^19)) ≤ 1/(2*Real.sqrt x*T^18)+1/(2*H^18) := by
  classical
  let Zlo := Z.filter (fun ρ => |ρ.im| ≤ H)
  let Zhi := Z.filter (fun ρ => ¬|ρ.im| ≤ H)
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hT0 : 0 < T := by norm_num at hT; linarith
  have hTlog : Real.log T ≤ 22 := (Real.log_le_log hT0 hTH).trans hlog
  have hlow := finite_absolute_tail Zlo
    (fun ρ hρ => hZ ρ (Finset.mem_filter.mp hρ).1) T hT hTlog
    (fun ρ hρ => hγ ρ (Finset.mem_filter.mp hρ).1)
  have hhigh := finite_absolute_tail Zhi
    (fun ρ hρ => hZ ρ (Finset.mem_filter.mp hρ).1) H (hT.trans hTH) hlog
    (fun ρ hρ => lt_of_not_ge (Finset.mem_filter.mp hρ).2)
  have hsqrt : x^((1/2 : ℝ)-1) = 1/Real.sqrt x := by
    rw [show (1/2 : ℝ)-1 = -(1/2 : ℝ) by ring, Real.rpow_neg hx0.le,
      ← Real.sqrt_eq_rpow, one_div]
  have hl : (∑ ρ ∈ Zlo, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*
      x^(ρ.re-1)*(1/|ρ.im|^19)) ≤ 1/(2*Real.sqrt x*T^18) := by
    have he : (∑ ρ ∈ Zlo, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*
        x^(ρ.re-1)*(1/|ρ.im|^19)) =
        (1/Real.sqrt x)*(∑ ρ ∈ Zlo, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*(1/|ρ.im|^19)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [hRH ρ (hZ ρ (Finset.mem_filter.mp hρ).1) (Finset.mem_filter.mp hρ).2, hsqrt]
      ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left hlow (by positivity)).trans_eq (by ring)
  have hh : (∑ ρ ∈ Zhi, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*
      x^(ρ.re-1)*(1/|ρ.im|^19)) ≤ 1/(2*H^18) := by
    apply le_trans (Finset.sum_le_sum (fun ρ hρ => ?_)) hhigh
    have hβ : x^(ρ.re-1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx
      (by linarith [(hZ ρ (Finset.mem_filter.mp hρ).1).2.2])
    calc
      _ ≤ (DusartSmoothing.RvM.zeroMult ρ : ℝ)*1*(1/|ρ.im|^19) := by gcongr
      _ = _ := by ring
  have hsplit := Finset.sum_filter_add_sum_filter_not Z (fun ρ : ℂ => |ρ.im| ≤ H)
    (fun ρ => (DusartSmoothing.RvM.zeroMult ρ : ℝ)*x^(ρ.re-1)*(1/|ρ.im|^19))
  dsimp only [Zlo, Zhi] at hl hh
  rw [← hsplit]
  exact add_le_add hl hh

theorem weighted_tail_of_finite_rh (x T H : ℝ) (hx : 1 ≤ x)
    (hT : (10 : ℝ)^8 ≤ T) (hTH : T ≤ H) (hlog : Real.log H ≤ 22)
    (hRH : ∀ ρ : ℂ, DusartSmoothing.RvM.IsNontrivialZero ρ → |ρ.im| ≤ H → ρ.re = 1/2) :
    (∑' ρ : StrictHighAbsoluteZero T, (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*
      x^(ρ.val.re-1)*(1/|ρ.val.im|^19)) ≤ 1/(2*Real.sqrt x*T^18)+1/(2*H^18) := by
  classical
  apply Real.tsum_le_of_sum_le
  · intro ρ
    positivity
  · intro S
    let Z : Finset ℂ := S.image (fun ρ : StrictHighAbsoluteZero T => ρ.val)
    have hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.1
    have hγ : ∀ ρ ∈ Z, T < |ρ.im| := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.2
    have h := finite_weighted_tail_of_finite_rh Z hZ x T H hx hT hTH hlog hγ hRH
    dsimp [Z] at h
    rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at h
    exact h

theorem absolute_tail_summable (H : ℝ) (hH : (10 : ℝ)^8 ≤ H) (hlog : Real.log H ≤ 22) :
    Summable (fun ρ : StrictHighAbsoluteZero H =>
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*(1/|ρ.val.im|^19)) := by
  classical
  apply summable_of_sum_le (c := 1/(2*H^18))
  · intro ρ
    positivity
  · intro S
    let Z : Finset ℂ := S.image (fun ρ : StrictHighAbsoluteZero H => ρ.val)
    have hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.1
    have hγ : ∀ ρ ∈ Z, H < |ρ.im| := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.2
    have h := finite_absolute_tail Z hZ H hH hlog hγ
    dsimp [Z] at h
    rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at h
    exact h

theorem weighted_tail_summable (x T : ℝ) (hx : 1 ≤ x)
    (hT : (10 : ℝ)^8 ≤ T) (hlog : Real.log T ≤ 22) :
    Summable (fun ρ : StrictHighAbsoluteZero T =>
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*x^(ρ.val.re-1)*(1/|ρ.val.im|^19)) := by
  apply (absolute_tail_summable T hT hlog).of_nonneg_of_le
  · intro ρ
    positivity
  · intro ρ
    have hβ : x^(ρ.val.re-1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx
      (by linarith [ρ.property.1.2.2])
    calc
      _ ≤ (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*1*(1/|ρ.val.im|^19) := by gcongr
      _ = _ := by ring

end ShortPrimeIntervalZeroMoments

theorem solution :
(
  ∀ (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ)
    (H : ℝ) (hH : (10 : ℝ)^8 ≤ H) (hlog : Real.log H ≤ 22)
    (hγ : ∀ ρ ∈ Z, H < |ρ.im|),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*(1/|ρ.im|^19)) ≤ 1/(2*H^18)
) ∧ (
  ∀ (H : ℝ) (hH : (10 : ℝ)^8 ≤ H) (hlog : Real.log H ≤ 22),
    Summable (fun ρ : StrictHighAbsoluteZero H =>
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*(1/|ρ.val.im|^19)) ∧
    (∑' ρ : StrictHighAbsoluteZero H,
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*(1/|ρ.val.im|^19)) ≤ 1/(2*H^18)
) ∧ (
  ∀ (x T H : ℝ) (hx : 1 ≤ x) (hT : (10 : ℝ)^8 ≤ T) (hTH : T ≤ H)
    (hlog : Real.log H ≤ 22)
    (hRH : ∀ ρ : ℂ, DusartSmoothing.RvM.IsNontrivialZero ρ → |ρ.im| ≤ H → ρ.re = 1/2),
    Summable (fun ρ : StrictHighAbsoluteZero T =>
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*x^(ρ.val.re-1)*(1/|ρ.val.im|^19)) ∧
    (∑' ρ : StrictHighAbsoluteZero T, (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*
      x^(ρ.val.re-1)*(1/|ρ.val.im|^19)) ≤ 1/(2*Real.sqrt x*T^18)+1/(2*H^18)
) := by
  refine ⟨ShortPrimeIntervalZeroMoments.finite_absolute_tail, ?_, ?_⟩
  · intro H hH hlog
    exact ⟨ShortPrimeIntervalZeroMoments.absolute_tail_summable H hH hlog,
      ShortPrimeIntervalZeroMoments.absolute_tail H hH hlog⟩
  · intro x T H hx hT hTH hlog hRH
    have hT0 : 0 < T := by norm_num at hT; linarith
    have hTlog : Real.log T ≤ 22 := (Real.log_le_log hT0 hTH).trans hlog
    exact ⟨ShortPrimeIntervalZeroMoments.weighted_tail_summable x T hx hT hTlog,
      ShortPrimeIntervalZeroMoments.weighted_tail_of_finite_rh x T H hx hT hTH hlog hRH⟩

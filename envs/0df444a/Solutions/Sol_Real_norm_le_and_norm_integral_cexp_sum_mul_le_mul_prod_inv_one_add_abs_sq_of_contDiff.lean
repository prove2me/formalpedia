-- Prove2me | solution 1 for Real.norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/acd53eae-ba95-5466-8438-6fbcdf1e80a6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Real_norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff

set_option autoImplicit false

open MeasureTheory Real Complex
open scoped FourierTransform

namespace R4WinBox

variable {r : ℕ}

def box (r : ℕ) (R : ℝ) : Set (Fin r → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-R) R

theorem mem_box_iff {R : ℝ} {x : Fin r → ℝ} : x ∈ box r R ↔ ∀ k, |x k| ≤ R := by
  simp only [box, Set.mem_univ_pi, Set.mem_Icc, abs_le]

theorem not_mem_box_iff {R : ℝ} {x : Fin r → ℝ} : x ∉ box r R ↔ ∃ k, R < |x k| := by
  rw [mem_box_iff]; push Not; rfl

theorem isCompact_box (R : ℝ) : IsCompact (box r R) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem isClosed_box (R : ℝ) : IsClosed (box r R) := (isCompact_box R).isClosed

theorem measurableSet_box (R : ℝ) : MeasurableSet (box r R) := (isClosed_box R).measurableSet

theorem volume_box {R : ℝ} (hR : 0 ≤ R) : volume (box r R) = ENNReal.ofReal ((2 * R) ^ r) := by
  rw [box, volume_pi_pi]
  simp only [Real.volume_Icc, sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← two_mul, ENNReal.ofReal_pow (by positivity)]

theorem volume_real_box {R : ℝ} (hR : 0 ≤ R) : volume.real (box r R) = (2 * R) ^ r := by
  rw [Measure.real, volume_box hR, ENNReal.toReal_ofReal (by positivity)]

variable {g : (Fin r → ℝ) → ℂ} {R M : ℝ}

theorem eq_zero_of_not_mem (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0)
    {x : Fin r → ℝ} (hx : x ∉ box r R) : g x = 0 :=
  hsupp x (not_mem_box_iff.mp hx)

theorem support_subset (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0) :
    Function.support g ⊆ box r R := by
  intro x hx
  by_contra h
  exact hx (eq_zero_of_not_mem hsupp h)

theorem tsupport_subset (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0) :
    tsupport g ⊆ box r R :=
  closure_minimal (support_subset hsupp) (isClosed_box R)

theorem hasCompactSupport (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0) :
    HasCompactSupport g :=
  HasCompactSupport.intro (isCompact_box R) fun _ hx => eq_zero_of_not_mem hsupp hx

theorem iteratedFDeriv_eq_zero (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0) (n : ℕ)
    {x : Fin r → ℝ} (hx : x ∉ box r R) : iteratedFDeriv ℝ n g x = 0 := by
  have h : x ∉ Function.support (iteratedFDeriv ℝ n g) := fun h =>
    hx (tsupport_subset hsupp (support_iteratedFDeriv_subset n h))
  simpa [Function.mem_support] using h

theorem norm_iteratedFDeriv_le_indicator (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0)
    {n : ℕ} (hM : ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ M) (x : Fin r → ℝ) :
    ‖iteratedFDeriv ℝ n g x‖ ≤ (box r R).indicator (fun _ => M) x := by
  by_cases hx : x ∈ box r R
  · rw [Set.indicator_of_mem hx]; exact hM x
  · rw [Set.indicator_of_notMem hx, iteratedFDeriv_eq_zero hsupp n hx, norm_zero]

theorem integrable_iteratedFDeriv {N : ℕ∞} (hg : ContDiff ℝ N g)
    (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0) {n : ℕ} (hn : (n : ℕ∞) ≤ N) :
    Integrable (iteratedFDeriv ℝ n g) :=
  (hg.continuous_iteratedFDeriv (by exact_mod_cast hn)).integrable_of_hasCompactSupport
    ((hasCompactSupport hsupp).iteratedFDeriv n)

theorem integral_norm_iteratedFDeriv_le (hR : 0 ≤ R)
    (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0)
    {n : ℕ} (hM : ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ M) :
    ∫ x, ‖iteratedFDeriv ℝ n g x‖ ≤ M * (2 * R) ^ r := by
  have hind : Integrable ((box r R).indicator fun _ : Fin r → ℝ => M) volume :=
    (integrable_indicator_iff (measurableSet_box R)).mpr
      (integrableOn_const (by rw [volume_box hR]; exact ENNReal.ofReal_ne_top))
  calc ∫ x, ‖iteratedFDeriv ℝ n g x‖
      ≤ ∫ x, (box r R).indicator (fun _ : Fin r → ℝ => M) x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hind
          (Filter.Eventually.of_forall (norm_iteratedFDeriv_le_indicator hsupp hM))
    _ = M * (2 * R) ^ r := by
        rw [integral_indicator_const _ (measurableSet_box R), volume_real_box hR, smul_eq_mul, mul_comm]

noncomputable def dotL (r : ℕ) : (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) →L[ℝ] ℝ :=
  ∑ k : Fin r, (ContinuousLinearMap.proj k : (Fin r → ℝ) →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj k : (Fin r → ℝ) →L[ℝ] ℝ)

theorem dotL_apply (v w : Fin r → ℝ) : dotL r v w = ∑ k, v k * w k := by
  simp [dotL, ContinuousLinearMap.sum_apply]

theorem dotL_single (k : Fin r) (w : Fin r → ℝ) : dotL r (Pi.single k 1) w = w k := by
  classical
  rw [dotL_apply]
  simp [Pi.single_apply, Finset.sum_ite_eq']

noncomputable abbrev four (g : (Fin r → ℝ) → ℂ) : (Fin r → ℝ) → ℂ :=
  VectorFourier.fourierIntegral 𝐞 volume (dotL r).toLinearMap₁₂ g

theorem integral_kernel_eq_four (g : (Fin r → ℝ) → ℂ) (ξ : Fin r → ℝ) :
    ∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * g x =
      four g ξ := by
  rw [four, VectorFourier.fourierIntegral]
  congr 1
  ext x
  rw [Circle.smul_def, Real.fourierChar_apply, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, dotL_apply]
  congr 1
  have : (∑ k, ξ k * x k) = ∑ k, x k * ξ k := Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [this]
  push_cast
  ring_nf

theorem norm_four_le (g : (Fin r → ℝ) → ℂ) (ξ : Fin r → ℝ) : ‖four g ξ‖ ≤ ∫ x, ‖g x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem key (hR : 0 ≤ R) (hg : ContDiff ℝ ((2 * r : ℕ) : ℕ∞) g)
    (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0)
    (hM : ∀ n : ℕ, n ≤ 2 * r → ∀ x : Fin r → ℝ, ‖iteratedFDeriv ℝ n g x‖ ≤ M)
    (S : Finset (Fin r)) (ξ : Fin r → ℝ) :
    (4 * Real.pi ^ 2) ^ S.card * (∏ k ∈ S, ξ k ^ 2) * ‖four g ξ‖ ≤ M * (2 * R) ^ r := by
  classical
  set s := S.card with hs

  let v : Fin s → (Fin r → ℝ) := fun i => Pi.single ((S.equivFin.symm i : S) : Fin r) 1
  let m : Fin (s + s) → (Fin r → ℝ) := Fin.append v v
  have hsr : s ≤ r := by simpa using S.card_le_univ
  have hn : ((s + s : ℕ) : ℕ∞) ≤ ((2 * r : ℕ) : ℕ∞) := by exact_mod_cast (by omega : s + s ≤ 2 * r)
  have h'f : ∀ n : ℕ, (n : ℕ∞) ≤ ((2 * r : ℕ) : ℕ∞) → Integrable (iteratedFDeriv ℝ n g) volume :=
    fun n hn' => integrable_iteratedFDeriv hg hsupp hn'
  have H := VectorFourier.fourierIntegral_iteratedFDeriv (dotL r) hg h'f hn
  have Hm := congrArg (fun F => F ξ m) H
  simp only [VectorFourier.fourierPowSMulRight_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.flip_apply] at Hm

  have hprod : (∏ i : Fin (s + s), -((dotL r) (m i) ξ)) = ∏ k ∈ S, ξ k ^ 2 := by
    rw [Fin.prod_univ_add]
    simp only [m, Fin.append_left, Fin.append_right, v, dotL_single]
    rw [← Finset.prod_mul_distrib]
    have : ∀ k : Fin r, -ξ k * -ξ k = ξ k ^ 2 := fun k => by ring
    simp_rw [this]
    rw [show (∏ i : Fin s, ξ ((S.equivFin.symm i : S) : Fin r) ^ 2) =
        ∏ x : S, ξ (x : Fin r) ^ 2 from
      Fintype.prod_equiv S.equivFin.symm _ (fun x : S => ξ (x : Fin r) ^ 2) fun _ => rfl]
    exact Finset.prod_coe_sort S fun k => ξ k ^ 2
  rw [hprod] at Hm

  have hnormL : ‖VectorFourier.fourierIntegral 𝐞 volume (dotL r).toLinearMap₁₂ (iteratedFDeriv ℝ (s + s) g) ξ m‖
      ≤ M * (2 * R) ^ r := by
    calc ‖VectorFourier.fourierIntegral 𝐞 volume (dotL r).toLinearMap₁₂ (iteratedFDeriv ℝ (s + s) g) ξ m‖
        ≤ ‖VectorFourier.fourierIntegral 𝐞 volume (dotL r).toLinearMap₁₂ (iteratedFDeriv ℝ (s + s) g) ξ‖ *
            ∏ i, ‖m i‖ := ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖VectorFourier.fourierIntegral 𝐞 volume (dotL r).toLinearMap₁₂ (iteratedFDeriv ℝ (s + s) g) ξ‖ := by
            have : ∀ i, ‖m i‖ = 1 := by
              intro i
              refine Fin.addCases (fun j => ?_) (fun j => ?_) i
              · simp only [m, v, Fin.append_left, Pi.norm_single, norm_one]
              · simp only [m, v, Fin.append_right, Pi.norm_single, norm_one]
            simp [this]
      _ ≤ ∫ x, ‖iteratedFDeriv ℝ (s + s) g x‖ := VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
      _ ≤ M * (2 * R) ^ r := integral_norm_iteratedFDeriv_le hR hsupp (hM (s + s) (by omega))
  have hnormR : ‖(-(2 * (Real.pi : ℂ) * Complex.I)) ^ (s + s) • ((∏ k ∈ S, ξ k ^ 2 : ℝ) • four g ξ)‖ =
      (4 * Real.pi ^ 2) ^ S.card * (∏ k ∈ S, ξ k ^ 2) * ‖four g ξ‖ := by
    rw [norm_smul, norm_smul, norm_pow, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg pi_pos.le, Real.norm_of_nonneg
        (Finset.prod_nonneg fun k _ => sq_nonneg (ξ k)), ← hs, pow_add, ← mul_assoc]
    congr 1
    congr 1
    rw [← mul_pow]
    rw [show (4 * Real.pi ^ 2) = (2 * Real.pi) * (2 * Real.pi) by ring, mul_pow]
  rw [← hnormR, ← Hm]
  exact hnormL

theorem prod_mul_norm_four_le (hR : 0 ≤ R) (hg : ContDiff ℝ ((2 * r : ℕ) : ℕ∞) g)
    (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0)
    (hM : ∀ n : ℕ, n ≤ 2 * r → ∀ x : Fin r → ℝ, ‖iteratedFDeriv ℝ n g x‖ ≤ M) (ξ : Fin r → ℝ) :
    (∏ k, (1 + 4 * Real.pi ^ 2 * ξ k ^ 2)) * ‖four g ξ‖ ≤ M * (4 * R) ^ r := by
  classical
  have hexp : (∏ k : Fin r, (1 + 4 * Real.pi ^ 2 * ξ k ^ 2)) =
      ∑ S ∈ (Finset.univ : Finset (Fin r)).powerset, (4 * Real.pi ^ 2) ^ S.card * ∏ k ∈ S, ξ k ^ 2 := by
    have := Finset.prod_add (fun k : Fin r => 4 * Real.pi ^ 2 * ξ k ^ 2) (fun _ => (1 : ℝ)) Finset.univ
    simp only [Finset.prod_const_one, mul_one] at this
    rw [show (∏ k : Fin r, (1 + 4 * Real.pi ^ 2 * ξ k ^ 2)) = ∏ k : Fin r, (4 * Real.pi ^ 2 * ξ k ^ 2 + 1)
      from Finset.prod_congr rfl fun k _ => add_comm _ _, this]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [hexp, Finset.sum_mul]
  calc ∑ S ∈ (Finset.univ : Finset (Fin r)).powerset, (4 * Real.pi ^ 2) ^ S.card * (∏ k ∈ S, ξ k ^ 2) * ‖four g ξ‖
      ≤ ∑ S ∈ (Finset.univ : Finset (Fin r)).powerset, M * (2 * R) ^ r :=
        Finset.sum_le_sum fun S _ => key hR hg hsupp hM S ξ
    _ = M * (4 * R) ^ r := by
        rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          show ((4 : ℝ) * R) ^ r = 2 ^ r * (2 * R) ^ r by rw [← mul_pow]; congr 1; ring]
        push_cast
        ring

theorem inv_one_add_le (t : ℝ) : (1 + 4 * Real.pi ^ 2 * t ^ 2)⁻¹ ≤ 2 * (1 + |t|)⁻¹ ^ 2 := by
  have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have h1 : 0 < 1 + |t| := by positivity
  have h2 : 0 < 1 + 4 * Real.pi ^ 2 * t ^ 2 := by positivity
  have h3 : 0 < (1 + |t|) ^ 2 := by positivity
  have habs : |t| ^ 2 = t ^ 2 := sq_abs t
  have key : (1 + |t|) ^ 2 ≤ 2 * (1 + 4 * Real.pi ^ 2 * t ^ 2) := by
    nlinarith [abs_nonneg t, sq_nonneg (|t| - 1), mul_nonneg (sub_nonneg.mpr hpi) (sq_nonneg t)]
  calc (1 + 4 * Real.pi ^ 2 * t ^ 2)⁻¹ = 1 / (1 + 4 * Real.pi ^ 2 * t ^ 2) := (one_div _).symm
    _ ≤ 2 / (1 + |t|) ^ 2 := by rw [div_le_div_iff₀ h2 h3]; linarith [key]
    _ = 2 * ((1 + |t|) ^ 2)⁻¹ := div_eq_mul_inv _ _
    _ = 2 * (1 + |t|)⁻¹ ^ 2 := by rw [inv_pow]

theorem one_le_mul_prod {x : Fin r → ℝ} (hx : x ∈ box r R) :
    1 ≤ (1 + R) ^ (2 * r) * ∏ k, (1 + |x k|)⁻¹ ^ 2 := by
  rw [mem_box_iff] at hx
  have : (1 + R) ^ (2 * r) = ∏ _k : Fin r, (1 + R) ^ 2 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
  rw [this, ← Finset.prod_mul_distrib]
  calc (1 : ℝ) = ∏ _k : Fin r, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun k _ => ?_
  have hk := hx k
  have h0 : 0 < 1 + |x k| := by positivity
  rw [inv_pow, ← div_eq_mul_inv, one_le_div (by positivity)]
  exact pow_le_pow_left₀ h0.le (by linarith : 1 + |x k| ≤ 1 + R) 2

theorem main (hR : 0 ≤ R) (hg : ContDiff ℝ ((2 * r : ℕ) : ℕ∞) g)
    (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0)
    (hM : ∀ n : ℕ, n ≤ 2 * r → ∀ x : Fin r → ℝ, ‖iteratedFDeriv ℝ n g x‖ ≤ M) :
    (∀ x : Fin r → ℝ, ‖g x‖ ≤ (M * ((1 + R) ^ (2 * r) + (8 * R) ^ r)) * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
    (∀ ξ : Fin r → ℝ,
      ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * g x‖ ≤
        (M * ((1 + R) ^ (2 * r) + (8 * R) ^ r)) * ∏ k, (1 + |ξ k|)⁻¹ ^ 2) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  have hprod_nonneg : ∀ y : Fin r → ℝ, 0 ≤ ∏ k, (1 + |y k|)⁻¹ ^ 2 :=
    fun y => Finset.prod_nonneg fun k _ => by positivity
  refine ⟨fun x => ?_, fun ξ => ?_⟩
  ·
    have hgx : ‖g x‖ ≤ M := by simpa [norm_iteratedFDeriv_zero] using hM 0 (Nat.zero_le _) x
    by_cases hx : x ∈ box r R
    · calc ‖g x‖ ≤ M * 1 := by rw [mul_one]; exact hgx
        _ ≤ M * ((1 + R) ^ (2 * r) * ∏ k, (1 + |x k|)⁻¹ ^ 2) :=
            mul_le_mul_of_nonneg_left (one_le_mul_prod hx) hM0
        _ = (M * (1 + R) ^ (2 * r)) * ∏ k, (1 + |x k|)⁻¹ ^ 2 := by ring
        _ ≤ (M * ((1 + R) ^ (2 * r) + (8 * R) ^ r)) * ∏ k, (1 + |x k|)⁻¹ ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (hprod_nonneg x)
            have : 0 ≤ M * (8 * R) ^ r := by positivity
            nlinarith
    · rw [eq_zero_of_not_mem hsupp hx, norm_zero]
      exact mul_nonneg (by positivity) (hprod_nonneg x)
  ·
    rw [integral_kernel_eq_four]
    have hP : 0 < ∏ k : Fin r, (1 + 4 * Real.pi ^ 2 * ξ k ^ 2) :=
      Finset.prod_pos fun k _ => by positivity
    have h1 : ‖four g ξ‖ ≤ M * (4 * R) ^ r * ∏ k, (1 + 4 * Real.pi ^ 2 * ξ k ^ 2)⁻¹ := by
      rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hP, mul_comm]
      exact prod_mul_norm_four_le hR hg hsupp hM ξ
    have h2 : (∏ k : Fin r, (1 + 4 * Real.pi ^ 2 * ξ k ^ 2)⁻¹) ≤ 2 ^ r * ∏ k, (1 + |ξ k|)⁻¹ ^ 2 := by
      rw [show (2 : ℝ) ^ r = ∏ _k : Fin r, (2 : ℝ) by simp, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun k _ => by positivity) fun k _ => inv_one_add_le (ξ k)
    calc ‖four g ξ‖ ≤ M * (4 * R) ^ r * ∏ k, (1 + 4 * Real.pi ^ 2 * ξ k ^ 2)⁻¹ := h1
      _ ≤ M * (4 * R) ^ r * (2 ^ r * ∏ k, (1 + |ξ k|)⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (M * (8 * R) ^ r) * ∏ k, (1 + |ξ k|)⁻¹ ^ 2 := by
          rw [show ((8 : ℝ) * R) ^ r = 2 ^ r * (4 * R) ^ r by rw [← mul_pow]; congr 1; ring]; ring
      _ ≤ (M * ((1 + R) ^ (2 * r) + (8 * R) ^ r)) * ∏ k, (1 + |ξ k|)⁻¹ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (hprod_nonneg ξ)
          have : 0 ≤ M * (1 + R) ^ (2 * r) := by positivity
          nlinarith

end R4WinBox

theorem solution
    {r : ℕ} (g : (Fin r → ℝ) → ℂ) (R M : ℝ) (hR : 0 ≤ R)
    (hg : ContDiff ℝ ((2 * r : ℕ) : ℕ∞) g)
    (hsupp : ∀ x : Fin r → ℝ, (∃ k, R < |x k|) → g x = 0)
    (hM : ∀ n : ℕ, n ≤ 2 * r → ∀ x : Fin r → ℝ, ‖iteratedFDeriv ℝ n g x‖ ≤ M) :
    (∀ x : Fin r → ℝ, ‖g x‖ ≤ (M * ((1 + R) ^ (2 * r) + (8 * R) ^ r)) * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
    (∀ ξ : Fin r → ℝ,
      ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * g x‖ ≤
        (M * ((1 + R) ^ (2 * r) + (8 * R) ^ r)) * ∏ k, (1 + |ξ k|)⁻¹ ^ 2) :=
  R4WinBox.main hR hg hsupp hM

end S_Real_norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff
end P2MW
export P2MW.S_Real_norm_le_and_norm_integral_cexp_sum_mul_le_mul_prod_inv_one_add_abs_sq_of_contDiff (solution)

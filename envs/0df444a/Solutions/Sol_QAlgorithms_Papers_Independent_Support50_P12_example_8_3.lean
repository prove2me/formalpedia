-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.example_8_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:34:39.540538+00:00
-- url     : https://prove2.me/submissions/8b2478cc-972b-4215-8b2e-4d4c7e33f024

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12
noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

theorem S200E_beta_real {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    ∫ u in Ioo (0:ℝ) 1, u ^ (s - 1) * (1 - u) ^ (-s) = Real.pi / Real.sin (Real.pi * s) := by
  have h1 := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (s:ℂ)) (t := 1 - (s:ℂ))
    (by simpa using hs.1) (by simpa using hs.2)
  rw [add_sub_cancel, Complex.Gamma_one, one_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_mul,
    Real.Gamma_mul_Gamma_one_sub] at h1
  have h2 : Complex.betaIntegral (s:ℂ) ((1:ℝ) - s : ℝ) =
      ((∫ u in (0:ℝ)..1, u ^ (s - 1) * (1 - u) ^ (-s) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal, Complex.betaIntegral]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [uIcc_of_le zero_le_one] at hu
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hu.1, Complex.ofReal_cpow (by linarith [hu.2])]
    push_cast
    ring_nf
  rw [h2] at h1
  have h3 := Complex.ofReal_injective h1
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at h3
  exact h3.symm

theorem S200E_K_one {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    ∫ t in Ioi (0:ℝ), t ^ (s - 1) / (1 + t) = Real.pi / Real.sin (Real.pi * s) := by
  rw [← S200E_beta_real hs]
  have himg : (fun t : ℝ => t / (1 + t)) '' Ioi 0 = Ioo 0 1 := by
    ext u; constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : (0:ℝ) < t := ht
      refine ⟨by positivity, ?_⟩
      rw [div_lt_one (by linarith)]; linarith
    · rintro ⟨h0, h1⟩
      refine ⟨u / (1 - u), div_pos h0 (by linarith), ?_⟩
      have : (1 - u) ≠ 0 := by linarith
      field_simp
      ring
  rw [← himg, integral_image_eq_integral_abs_deriv_smul (f' := fun t => 1 / (1 + t) ^ 2)
    measurableSet_Ioi]
  · refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : (0:ℝ) < t := ht
    have h1t : (0:ℝ) < 1 + t := by linarith
    simp only [smul_eq_mul]
    have e1 : 1 - t / (1 + t) = (1 + t)⁻¹ := by field_simp; ring
    rw [e1, Real.div_rpow ht'.le h1t.le, Real.inv_rpow h1t.le, Real.rpow_neg h1t.le, inv_inv,
      Real.rpow_sub_one h1t.ne', abs_of_pos (by positivity)]
    have : (0:ℝ) < (1 + t) ^ s := Real.rpow_pos_of_pos h1t s
    field_simp
  · intro t ht
    have ht' : (0:ℝ) < t := ht
    have h1t : (1:ℝ) + t ≠ 0 := by linarith
    apply HasDerivAt.hasDerivWithinAt
    have := (hasDerivAt_id' t).div ((hasDerivAt_id' t).const_add 1) h1t
    refine this.congr_deriv ?_
    ring
  · intro t ht u hu h
    have ht' : (0:ℝ) < t := ht
    have hu' : (0:ℝ) < u := hu
    simp only at h
    field_simp at h
    linarith

theorem S200E_Kc_pos {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) : 0 < Real.pi / Real.sin (Real.pi * s) := by
  apply div_pos Real.pi_pos
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hs.1)
  nlinarith [Real.pi_pos, hs.2]

theorem S200E_K {s x : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) (hx : 0 < x) :
    ∫ t in Ioi (0:ℝ), t ^ (s - 1) / (x + t) = x ^ (s - 1) * (Real.pi / Real.sin (Real.pi * s)) := by
  have h := integral_comp_mul_left_Ioi (fun t : ℝ => t ^ (s - 1) / (x + t)) 0 hx
  rw [mul_zero, smul_eq_mul] at h
  have h2 : ∫ τ in Ioi (0:ℝ), (x * τ) ^ (s - 1) / (x + x * τ) =
      ∫ τ in Ioi (0:ℝ), (x ^ (s - 1) / x) * (τ ^ (s - 1) / (1 + τ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : (0:ℝ) < t := ht
    rw [Real.mul_rpow hx.le ht'.le]
    have : (0:ℝ) < 1 + t := by linarith
    field_simp
  rw [h2, integral_const_mul, S200E_K_one hs] at h
  have hx' : x ≠ 0 := hx.ne'
  have h3 := congrArg (fun y => x * y) h
  rw [← mul_assoc x x⁻¹, mul_inv_cancel₀ hx', one_mul] at h3
  rw [← h3]
  field_simp

theorem S200E_K_int {s x : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) / (x + t)) (Ioi 0) := by
  by_contra hc
  have := S200E_K hs hx
  rw [integral_undef hc] at this
  have : 0 < x ^ (s - 1) * (Real.pi / Real.sin (Real.pi * s)) :=
    mul_pos (Real.rpow_pos_of_pos hx _) (S200E_Kc_pos hs)
  linarith


theorem S200E_part1 (x : ℝ) (hx0 : x ≥ 0) :
      IntegrableOn (fun t : ℝ => x / (1 + t) - x / (x + t)) (Ioi 0) ∧
      x * Real.log x = ∫ t in Ioi (0 : ℝ), x / (1 + t) - x / (x + t) := by
  rcases hx0.lt_or_eq with hx | rfl
  · set g : ℝ → ℝ := fun t => x * (Real.log (1 + t) - Real.log (x + t)) with hg
    have hderiv : ∀ t ∈ Ici (0:ℝ), HasDerivAt g (x / (1 + t) - x / (x + t)) t := by
      intro t ht
      have ht' : (0:ℝ) ≤ t := ht
      have h1 : (1:ℝ) + t ≠ 0 := by linarith
      have h2 : x + t ≠ 0 := by linarith
      have := (((hasDerivAt_id' t).const_add 1).log h1).sub
        (((hasDerivAt_id' t).const_add x).log h2) |>.const_mul x
      refine this.congr_deriv ?_
      field_simp
    have hlim : Tendsto g atTop (𝓝 0) := by
      have hinv := tendsto_inv_atTop_zero (𝕜 := ℝ)
      have hA : Tendsto (fun t : ℝ => x * (Real.log (1 + t⁻¹) - Real.log (1 + x * t⁻¹))) atTop
          (𝓝 (x * (Real.log (1 + 0) - Real.log (1 + x * 0)))) := by
        refine Tendsto.const_mul _ (Tendsto.sub ?_ ?_)
        · exact (hinv.const_add 1).log (by norm_num)
        · exact ((hinv.const_mul x).const_add 1).log (by norm_num)
      simp only [add_zero, mul_zero, Real.log_one, sub_self] at hA
      refine hA.congr' ?_
      filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      simp only [hg]
      have e1 : 1 + t = t * (1 + t⁻¹) := by field_simp; ring
      have e2 : x + t = t * (1 + x * t⁻¹) := by field_simp; ring
      rw [e1, e2, Real.log_mul ht.ne' (by positivity), Real.log_mul ht.ne' (by positivity)]
      ring
    have hg0 : g 0 = - (x * Real.log x) := by simp [hg]
    rcases le_or_gt 1 x with h1 | h1
    · have hpos : ∀ t ∈ Ioi (0:ℝ), 0 ≤ x / (1 + t) - x / (x + t) := by
        intro t ht
        have ht' : (0:ℝ) < t := ht
        rw [sub_nonneg]
        exact div_le_div_of_nonneg_left hx.le (by linarith) (by linarith)
      refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩
      rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim, hg0]; ring
    · have hneg : ∀ t ∈ Ioi (0:ℝ), x / (1 + t) - x / (x + t) ≤ 0 := by
        intro t ht
        have ht' : (0:ℝ) < t := ht
        rw [sub_nonpos]
        exact div_le_div_of_nonneg_left hx.le (by linarith) (by linarith)
      refine ⟨integrableOn_Ioi_deriv_of_nonpos' hderiv hneg hlim, ?_⟩
      rw [integral_Ioi_of_hasDerivAt_of_nonpos' hderiv hneg hlim, hg0]; ring
  · simp

theorem S200E_part2 (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (x : ℝ) (hx0 : x ≥ (0 : ℝ)) :
      IntegrableOn (fun t : ℝ => -x / (x + t) * Real.rpow t (a - 1)) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => (x / (1 + t) - x / (x + t)) * Real.rpow t (a - 1)) (Ioi 0) ∧
      -Real.rpow x a = Real.sin (a * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), -x / (x + t) * Real.rpow t (a - 1) ∧
      Real.sin (a * Real.pi) / Real.pi *
        (∫ t in Ioi (0 : ℝ), x * Real.rpow t (a - 1) / (1 + t)) = x ∧
      -Real.rpow x a = -x + Real.sin (a * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), (x / (1 + t) - x / (x + t)) * Real.rpow t (a - 1) := by
  simp only [Real.rpow_eq_pow]
  have hsin : 0 < Real.sin (Real.pi * a) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ha.1) (by nlinarith [Real.pi_pos, ha.2])
  have hpi := Real.pi_pos
  have hsc : Real.sin (a * Real.pi) = Real.sin (Real.pi * a) := by rw [mul_comm]
  rw [hsc]
  have hsin2 : Real.sin (a * Real.pi) ≠ 0 := hsc ▸ hsin.ne'
  have hK1 := S200E_K_one ha
  have hI1 := S200E_K_int ha one_pos
  have e4 : (fun t : ℝ => x * t ^ (a - 1) / (1 + t)) = fun t => x * (t ^ (a - 1) / (1 + t)) := by
    funext t; ring
  have h4 : Real.sin (Real.pi * a) / Real.pi *
      (∫ t in Ioi (0 : ℝ), x * t ^ (a - 1) / (1 + t)) = x := by
    rw [e4, integral_const_mul, hK1]; field_simp
  rcases hx0.lt_or_eq with hx | rfl
  · have hK := S200E_K ha hx
    have hI := S200E_K_int ha hx
    have e1 : (fun t : ℝ => -x / (x + t) * t ^ (a - 1)) = fun t => -x * (t ^ (a - 1) / (x + t)) := by
      funext t; ring
    have e2 : (fun t : ℝ => (x / (1 + t) - x / (x + t)) * t ^ (a - 1)) =
        fun t => x * (t ^ (a - 1) / (1 + t)) - x * (t ^ (a - 1) / (x + t)) := by
      funext t; ring
    have hxa : x * x ^ (a - 1) = x ^ a := by
      rw [Real.rpow_sub_one hx.ne']; field_simp
    refine ⟨?_, ?_, ?_, h4, ?_⟩
    · rw [e1]; exact hI.const_mul _
    · rw [e2]; exact (hI1.const_mul x).sub (hI.const_mul x)
    · rw [e1, integral_const_mul, hK]
      rw [← hxa]; field_simp
    · rw [e2, integral_sub (hI1.const_mul x) (hI.const_mul x), integral_const_mul,
        integral_const_mul, hK, hK1, ← hxa]
      field_simp; ring
  · have ha0 : a ≠ 0 := ha.1.ne'
    simp [Real.zero_rpow ha0]

theorem S200E_part3 (a : ℝ) (ha : a ∈ Ioo (1 : ℝ) 2) (x : ℝ) (hx0 : x ≥ (0 : ℝ)) :
      IntegrableOn (fun t : ℝ => x ^ 2 * Real.rpow t (a - 2) / (x + t)) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => (x / t - x / (x + t)) * Real.rpow t (a - 1)) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => (x / (1 + t) - x / (x + t)) * Real.rpow t (a - 1)) (Ioi 0) ∧
      Real.rpow x a = Real.sin ((a - 1) * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), x ^ 2 * Real.rpow t (a - 2) / (x + t) ∧
      Real.rpow x a = Real.sin ((a - 1) * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), (x / t - x / (x + t)) * Real.rpow t (a - 1) ∧
      Real.sin ((a - 1) * Real.pi) / Real.pi *
        (∫ t in Ioi (0 : ℝ), (x / t - x / (1 + t)) * Real.rpow t (a - 1)) = x ∧
      Real.rpow x a = x + Real.sin ((a - 1) * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), (x / (1 + t) - x / (x + t)) * Real.rpow t (a - 1) := by
  simp only [Real.rpow_eq_pow]
  have hs : a - 1 ∈ Ioo (0:ℝ) 1 := ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hsin : 0 < Real.sin (Real.pi * (a - 1)) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hs.1) (by nlinarith [Real.pi_pos, hs.2])
  have hpi := Real.pi_pos
  rw [mul_comm (a - 1) Real.pi]
  have e2 : a - 1 - 1 = a - 2 := by ring
  have hK1 := S200E_K_one hs
  have hI1 := S200E_K_int hs one_pos
  rw [e2] at hK1 hI1
  -- pointwise identity on Ioi 0
  have eq3 : EqOn (fun t : ℝ => (x / t - x / (1 + t)) * t ^ (a - 1))
      (fun t => x * (t ^ (a - 2) / (1 + t))) (Ioi 0) := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    have : t ^ (a - 1) = t ^ (a - 2) * t := by
      rw [← e2, Real.rpow_sub_one ht'.ne' (a - 1)]; field_simp
    simp only
    rw [this]
    have : (0:ℝ) < 1 + t := by linarith
    field_simp
    ring
  have hI3 : IntegrableOn (fun t : ℝ => (x / t - x / (1 + t)) * t ^ (a - 1)) (Ioi 0) :=
    IntegrableOn.congr_fun (hI1.const_mul x) eq3.symm measurableSet_Ioi
  have hJ3 : ∫ t in Ioi (0 : ℝ), (x / t - x / (1 + t)) * t ^ (a - 1) =
      x * (Real.pi / Real.sin (Real.pi * (a - 1))) := by
    rw [setIntegral_congr_fun measurableSet_Ioi eq3, integral_const_mul, hK1]
  have h6 : Real.sin (Real.pi * (a - 1)) / Real.pi *
      (∫ t in Ioi (0 : ℝ), (x / t - x / (1 + t)) * t ^ (a - 1)) = x := by
    rw [hJ3]; field_simp
  rcases hx0.lt_or_eq with hx | rfl
  · have hK := S200E_K hs hx
    have hI := S200E_K_int hs hx
    rw [e2] at hK hI
    have e1 : (fun t : ℝ => x ^ 2 * t ^ (a - 2) / (x + t)) =
        fun t => x ^ 2 * (t ^ (a - 2) / (x + t)) := by
      funext t; ring
    have eq2 : EqOn (fun t : ℝ => (x / t - x / (x + t)) * t ^ (a - 1))
        (fun t => x ^ 2 * (t ^ (a - 2) / (x + t))) (Ioi 0) := by
      intro t ht
      have ht' : (0:ℝ) < t := ht
      have : t ^ (a - 1) = t ^ (a - 2) * t := by
        rw [← e2, Real.rpow_sub_one ht'.ne' (a - 1)]; field_simp
      simp only
      rw [this]
      have : (0:ℝ) < x + t := by linarith
      field_simp
      ring
    have hI2 : IntegrableOn (fun t : ℝ => (x / t - x / (x + t)) * t ^ (a - 1)) (Ioi 0) :=
      IntegrableOn.congr_fun (hI.const_mul (x ^ 2)) eq2.symm measurableSet_Ioi
    have hJ2 : ∫ t in Ioi (0 : ℝ), (x / t - x / (x + t)) * t ^ (a - 1) =
        x ^ 2 * (x ^ (a - 2) * (Real.pi / Real.sin (Real.pi * (a - 1)))) := by
      rw [setIntegral_congr_fun measurableSet_Ioi eq2, integral_const_mul, hK]
    have e4 : (fun t : ℝ => (x / (1 + t) - x / (x + t)) * t ^ (a - 1)) =
        fun t => (x / t - x / (x + t)) * t ^ (a - 1) - (x / t - x / (1 + t)) * t ^ (a - 1) := by
      funext t; ring
    have hxa : x ^ 2 * x ^ (a - 2) = x ^ a := by
      rw [Real.rpow_sub hx, Real.rpow_two]; field_simp
    refine ⟨?_, hI2, ?_, ?_, ?_, h6, ?_⟩
    · rw [e1]; exact hI.const_mul _
    · rw [e4]; exact hI2.sub hI3
    · rw [e1, integral_const_mul, hK, ← hxa]; field_simp
    · rw [hJ2, ← hxa]; field_simp
    · rw [e4, integral_sub hI2 hI3, hJ2, hJ3, ← hxa]
      field_simp; ring
  · have ha0 : a ≠ 0 := by linarith [ha.1]
    simp only [Real.zero_rpow ha0] at *
    simp

end QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Support50.P12 in
/-- Example 8.3, PDF pp.39–40: natural-log and both power regimes, including
all converted representations and their integrability. The sin((a-1)pi) sign is retained. -/
theorem solution :
    (∀ x ≥ (0 : ℝ),
      IntegrableOn (fun t : ℝ => x / (1 + t) - x / (x + t)) (Ioi 0) ∧
      x * Real.log x = ∫ t in Ioi (0 : ℝ), x / (1 + t) - x / (x + t)) ∧
    (∀ a ∈ Ioo (0 : ℝ) 1, ∀ x ≥ (0 : ℝ),
      IntegrableOn (fun t : ℝ => -x / (x + t) * Real.rpow t (a - 1)) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => (x / (1 + t) - x / (x + t)) * Real.rpow t (a - 1)) (Ioi 0) ∧
      -Real.rpow x a = Real.sin (a * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), -x / (x + t) * Real.rpow t (a - 1) ∧
      Real.sin (a * Real.pi) / Real.pi *
        (∫ t in Ioi (0 : ℝ), x * Real.rpow t (a - 1) / (1 + t)) = x ∧
      -Real.rpow x a = -x + Real.sin (a * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), (x / (1 + t) - x / (x + t)) * Real.rpow t (a - 1)) ∧
    (∀ a ∈ Ioo (1 : ℝ) 2, ∀ x ≥ (0 : ℝ),
      IntegrableOn (fun t : ℝ => x ^ 2 * Real.rpow t (a - 2) / (x + t)) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => (x / t - x / (x + t)) * Real.rpow t (a - 1)) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => (x / (1 + t) - x / (x + t)) * Real.rpow t (a - 1)) (Ioi 0) ∧
      Real.rpow x a = Real.sin ((a - 1) * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), x ^ 2 * Real.rpow t (a - 2) / (x + t) ∧
      Real.rpow x a = Real.sin ((a - 1) * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), (x / t - x / (x + t)) * Real.rpow t (a - 1) ∧
      Real.sin ((a - 1) * Real.pi) / Real.pi *
        (∫ t in Ioi (0 : ℝ), (x / t - x / (1 + t)) * Real.rpow t (a - 1)) = x ∧
      Real.rpow x a = x + Real.sin ((a - 1) * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), (x / (1 + t) - x / (x + t)) * Real.rpow t (a - 1)) :=
  ⟨S200E_part1, S200E_part2, S200E_part3⟩



end

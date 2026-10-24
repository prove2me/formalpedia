-- Prove2me | solution 1 for UniversalBarrier.NSC.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:59:13.990989+00:00
-- url     : https://prove2.me/submissions/78a22148-ce23-41b5-8380-b7b38dd4427f

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model

set_option maxHeartbeats 0

namespace UniversalBarrier.NSC.AffineDensityProof

/-- A nonzero affine change of variable preserves the normalized affine-power family. -/
theorem affine_isKAffine (k : ℕ) (hk : 2 ≤ k) (p : ℝ → ℝ)
    (hp : IsKAffine k p) (c d : ℝ) (hc : c ≠ 0) :
    IsKAffine k (fun t => |c| * p (c * t + d)) := by
  classical
  have _ := hk
  obtain ⟨a, b, α, β, hab, hnonneg, hpos, hp⟩ := hp
  let f : ℝ → ℝ := fun u => (α * u + β) ^ (k - 1)
  have ha : c * ((a - d) / c) + d = a := by field_simp; ring
  have hb : c * ((b - d) / c) + d = b := by field_simp; ring
  obtain ⟨A, B, hAB, hmem, hint⟩ : ∃ A B : ℝ,
      A < B ∧ (∀ t : ℝ, t ∈ Set.Icc A B ↔ c * t + d ∈ Set.Icc a b) ∧
      (∫ u in A..B, f (c * u + d)) = (∫ u in a..b, f u) / |c| := by
    rcases lt_or_gt_of_ne hc with hcneg | hcpos
    · refine ⟨(b - d) / c, (a - d) / c, ?_, ?_, ?_⟩
      · exact (div_lt_div_right_of_neg hcneg).2 (by linarith)
      · intro t
        simp only [Set.mem_Icc, div_le_iff_of_neg hcneg, le_div_iff_of_neg hcneg]
        constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith
      · rw [intervalIntegral.integral_comp_mul_add f hc d, ha, hb,
          intervalIntegral.integral_symm, abs_of_neg hcneg]
        simp only [smul_eq_mul, div_eq_mul_inv]
        ring
    · refine ⟨(a - d) / c, (b - d) / c, ?_, ?_, ?_⟩
      · exact (div_lt_div_iff_of_pos_right hcpos).2 (by linarith)
      · intro t
        simp only [Set.mem_Icc, div_le_iff₀ hcpos, le_div_iff₀ hcpos]
        constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith
      · rw [intervalIntegral.integral_comp_mul_add f hc d, ha, hb, abs_of_pos hcpos]
        simp only [smul_eq_mul, div_eq_mul_inv]
        ring
  have hpoly (u : ℝ) : α * c * u + (α * d + β) = α * (c * u + d) + β := by ring
  have hint' : (∫ u in A..B, (α * c * u + (α * d + β)) ^ (k - 1)) =
      (∫ u in a..b, (α * u + β) ^ (k - 1)) / |c| := by
    simpa only [hpoly] using hint
  refine ⟨A, B, α * c, α * d + β, hAB, ?_, ?_, ?_⟩
  · intro t ht
    rw [hpoly]
    exact hnonneg (c * t + d) ((hmem t).1 ht)
  · rw [hint']
    exact div_pos hpos (abs_pos.mpr hc)
  · funext t
    rw [hp, hint']
    dsimp only
    by_cases ht : t ∈ Set.Icc A B
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ((hmem t).1 ht), hpoly]
      field_simp
    · rw [Set.indicator_of_notMem ht,
          Set.indicator_of_notMem (fun h => ht ((hmem t).2 h))]
      simp

end UniversalBarrier.NSC.AffineDensityProof

open MeasureTheory

namespace UniversalBarrier.NSC.AffineProof

theorem weighted_integrable {k : ℕ} {p : ℝ → ℝ} (hp : IsKAffine k p)
    (g : ℝ → ℝ) (hg : Continuous g) : Integrable (fun t => g t * p t) := by
  obtain ⟨a, b, A, B, _, _, _, rfl⟩ := hp
  have hcont : Continuous (fun t : ℝ => g t * (A * t + B) ^ (k - 1)) := by fun_prop
  have h := (hcont.integrableOn_Icc (μ := volume) (a := a) (b := b)).integrable_indicator measurableSet_Icc
  convert h.div_const (∫ u in a..b, (A * u + B) ^ (k - 1)) using 1
  ext t
  by_cases ht : t ∈ Set.Icc a b <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, ht, mul_div_assoc]

theorem mass_one {k : ℕ} {p : ℝ → ℝ} (hp : IsKAffine k p) : (∫ t, p t) = 1 := by
  obtain ⟨a, b, A, B, hab, _, hpos, rfl⟩ := hp
  rw [integral_div, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le, div_self hpos.ne']

theorem affine_integral (F : ℝ → ℝ) (c d : ℝ) (hc : c ≠ 0) :
    (∫ t, |c| * F (c * t + d)) = ∫ u, F u := by
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun u => F (u + d)),
    integral_add_right_eq_self F d]
  simp [abs_inv, hc]

theorem mean_affine {k : ℕ} {p : ℝ → ℝ} (hp : IsKAffine k p)
    (c d : ℝ) (hc : c ≠ 0) :
    mu1 (fun t => |c| * p (c * t + d)) = (mu1 p - d) / c := by
  have h1 : Integrable (fun t => t * p t) := weighted_integrable hp _ continuous_id
  have h0 : Integrable p := by simpa using weighted_integrable hp (fun _ => 1) continuous_const
  calc
    _ = ∫ u, ((u - d) / c) * p u := by
      rw [← affine_integral (fun u => ((u - d) / c) * p u) c d hc]
      unfold mu1
      congr 1
      ext t
      field_simp
      ring
    _ = (∫ u, u * p u - d * p u) / c := by
      rw [← integral_div]
      congr 1
      ext u
      ring
    _ = (mu1 p - d) / c := by
      rw [integral_sub h1 (h0.const_mul d), integral_const_mul, mass_one hp, mul_one]
      rfl

theorem central_affine {k : ℕ} {p : ℝ → ℝ} (hp : IsKAffine k p)
    (c d : ℝ) (hc : c ≠ 0) (j : ℕ) :
    (∫ t, (t - mu1 (fun t => |c| * p (c * t + d))) ^ j *
      (|c| * p (c * t + d))) = (∫ u, (u - mu1 p) ^ j * p u) / c ^ j := by
  rw [mean_affine hp c d hc, ← integral_div]
  rw [← affine_integral (fun u => ((u - mu1 p) ^ j * p u) / c ^ j) c d hc]
  congr 1
  ext t
  have heq : t - (mu1 p - d) / c = (c * t + d - mu1 p) / c := by field_simp; ring
  rw [heq, div_pow]
  ring

theorem Xi_affine {k : ℕ} {p : ℝ → ℝ} (hp : IsKAffine k p)
    (c d : ℝ) (hc : c ≠ 0) : Xi p = Xi (fun t => |c| * p (c * t + d)) := by
  have h2 : mu2sq (fun t => |c| * p (c * t + d)) = mu2sq p / c ^ 2 :=
    central_affine hp c d hc 2
  have h3 : mu3cube (fun t => |c| * p (c * t + d)) = mu3cube p / c ^ 3 :=
    central_affine hp c d hc 3
  unfold Xi
  rw [h2, h3, Real.sqrt_div' _ (sq_nonneg c), Real.sqrt_sq_eq_abs, div_pow]
  simp only [abs_div, abs_pow, abs_abs]
  exact (div_div_div_cancel_right₀ (pow_ne_zero 3 (abs_ne_zero.mpr hc)) _ _).symm

end UniversalBarrier.NSC.AffineProof

open UniversalBarrier.NSC

theorem solution (k : ℕ) (hk : 2 ≤ k) (p : ℝ → ℝ) (hp : IsKAffine k p) (α' β' : ℝ) (hα' : α' ≠ 0) :
    IsKAffine k (fun t => |α'| * p (α' * t + β')) ∧
      Xi p = Xi (fun t => |α'| * p (α' * t + β')) := by
  exact ⟨AffineDensityProof.affine_isKAffine k hk p hp α' β' hα',
    AffineProof.Xi_affine hp α' β' hα'⟩

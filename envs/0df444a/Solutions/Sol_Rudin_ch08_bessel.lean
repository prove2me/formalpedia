-- Prove2me | solution 1 for Rudin.ch08_bessel
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-13T20:27:54.056989+00:00
-- url     : https://prove2.me/submissions/dc22702a-9630-4de2-a057-4ca0c354f72d

import Mathlib
import Definitions.Def_Rudin_ch08_fourier
set_option autoImplicit false
open Filter Topology Rudin MeasureTheory
theorem solution : ¬ (∀ (a b : ℝ) (hab : a ≤ b) (φ : ℕ → ℝ → ℂ) (hφ : IsOrthonormalSystem φ a b)
    (f : ℝ → ℂ) (n : ℕ) (γ : ℕ → ℂ),
    (∫ x in a..b, ‖f x - ∑ m ∈ Finset.range n, genFourierCoeff f φ a b m * φ m x‖ ^ 2) ≤
      (∫ x in a..b, ‖f x - ∑ m ∈ Finset.range n, γ m * φ m x‖ ^ 2) ∧
    (∑ m ∈ Finset.range n, ‖genFourierCoeff f φ a b m‖ ^ 2) ≤ ∫ x in a..b, ‖f x‖ ^ 2 ) := by
  intro h
  letI : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
  let φ : ℕ → ℝ → ℂ := fun n x => _root_.fourier (T := 1) (n : ℤ) (x : AddCircle (1 : ℝ))
  have hφ : IsOrthonormalSystem φ 0 1 := by
    constructor
    · intro m n hmn
      have hne : (m : ℤ) ≠ (n : ℤ) := by exact_mod_cast hmn
      have hh := congrFun (_root_.fourierCoeff_fourier (T := 1) (n : ℤ)) (m : ℤ)
      rw [_root_.fourierCoeff_eq_intervalIntegral _ _ 0] at hh
      have hstar (x : ℝ) : _root_.fourier (T := 1) (-(m : ℤ)) (x : AddCircle (1 : ℝ)) =
          (starRingEnd ℂ) (φ m x) := _root_.fourier_neg
      simp only [zero_add, one_div, inv_one, one_smul, smul_eq_mul, hstar,
        Pi.single_eq_of_ne hne] at hh
      simpa only [φ, mul_comm] using hh
    · intro n
      have hn (x : ℝ) : ‖φ n x‖ = 1 := by exact Circle.norm_coe _
      simp [hn]
  let f : ℝ → ℂ := fun x => (x ^ (-(3 / 4 : ℝ)) : ℝ)
  have hcoeff : genFourierCoeff f φ 0 1 0 = (4 : ℂ) := by
    simp only [genFourierCoeff, φ, Nat.cast_zero, _root_.fourier_zero, map_one, mul_one]
    rw [show (fun x => f x) = (fun x => ((x ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ)) from rfl]
    rw [intervalIntegral.integral_ofReal, integral_rpow (Or.inl (by norm_num))]
    norm_num
  have hbad : ¬ IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume 0 1 := by
    intro hh
    have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hh
    have heq : (fun x => ‖f x‖ ^ 2) =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 1)]
        (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      simp only [f, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
      rw [← Real.rpow_mul_natCast hx.1.le]
      norm_num
    have hp := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mp (hi.congr heq)
    norm_num at hp
  have hb := (h 0 1 (by norm_num) φ hφ f 1 (fun _ => 0)).2
  rw [intervalIntegral.integral_undef hbad] at hb
  norm_num [hcoeff] at hb

#print axioms solution

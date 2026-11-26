-- Prove2me | solution 1 for P2M_QuadraticFloor_floorSum_eq_of_sq_modEq__0734c730f8f6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:37.596829+00:00
-- url     : https://prove2.me/submissions/40b760f4-35a1-4651-8a24-d898f70742f7

module
public import Definitions.Def_QuadraticFloor_SquareClass
public import Definitions.Def_QuadraticFloor_Corollaries
public import Theorems.Thm_P2M_QuadraticFloor_root_count__8bce20a9a3c2
public import Theorems.Thm_QuadraticFloor_admissible_data


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {A : ℕ} (hA : Odd A) (hpA : ¬ p ∣ A)
    {B C B' C' : ℤ} (h : Admissible A B C) (h' : Admissible A B' C')
    (hBB : B ^ 2 ≡ B' ^ 2 [ZMOD A]) :
    floorSum A B C p = floorSum A B' C' p ∧ C.negOnePow = C'.negOnePow := by
  obtain ⟨d, hdD, hd1, hd4A, hd4, hd8⟩ := admissible_data hA h
  obtain ⟨d', hdD', hd1', hd4A', hd4', hd8'⟩ := admissible_data hA h'
  have hdvdA : (A : ℤ) ∣ (d' : ℤ) - d := by
    rw [hdD, hdD']
    have := hBB.dvd
    obtain ⟨k, hk⟩ := this
    exact ⟨k - 4 * (C' - C), by linear_combination hk⟩
  have hdvd4 : (4 : ℤ) ∣ (d' : ℤ) - d := by omega
  have hcop : IsCoprime (4 : ℤ) A := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime 4 A := by
      have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hA); simpa using this
    simpa [Int.gcd] using this
  have hdvd := hcop.mul_dvd hdvd4 hdvdA
  have heq : (d' : ℤ) - d = 0 := Int.eq_zero_of_abs_lt_dvd hdvd (by
    rw [abs_lt]; constructor <;> omega)
  have hdd : d = d' := by omega
  subst hdd
  have hC : C.negOnePow = C'.negOnePow := by
    rw [Int.negOnePow_eq_iff, Int.even_sub]
    rw [hd8] at hd8'
    by_cases hc : Even C <;> by_cases hc' : Even C' <;>
      simp only [hc, hc', ite_true, ite_false] at hd8' <;>
      first | exact iff_of_true hc hc' | exact iff_of_false hc hc' | omega
  refine ⟨?_, hC⟩
  have hAB : Even ((A : ℤ) + B) := (show Odd (A : ℤ) by exact_mod_cast hA).add_odd h.1
  have hAB' : Even ((A : ℤ) + B') := (show Odd (A : ℤ) by exact_mod_cast hA).add_odd h'.1
  have hpA' : ¬ (p : ℤ) ∣ (A : ℤ) := by exact_mod_cast hpA
  rw [root_count' hp2 C hAB hpA', root_count' hp2 C' hAB' hpA', ← hdD, ← hdD', hC]
end QuadraticFloor

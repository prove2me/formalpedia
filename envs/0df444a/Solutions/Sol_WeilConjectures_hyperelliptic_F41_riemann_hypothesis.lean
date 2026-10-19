-- Prove2me | solution 1 for WeilConjectures.hyperelliptic_F41_riemann_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:28:54.37083+00:00
-- url     : https://prove2.me/submissions/fe8a2865-d30f-453e-9753-99b7ea45283e

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction

open Polynomial

namespace WERH

lemma quad (a : ℂ) (t : ℝ) (h1 : a + (starRingEnd ℂ) a = t) (h2 : a * (starRingEnd ℂ) a = 41) :
    (1 - C a * X) * (1 - C ((starRingEnd ℂ) a) * X) = (1 - C (t : ℂ) * X + 41 * X ^ 2 : ℂ[X]) := by
  have e1 : C a + C ((starRingEnd ℂ) a) = C (t : ℂ) := by rw [← C_add, h1]
  have e2 : C a * C ((starRingEnd ℂ) a) = (41 : ℂ[X]) := by
    rw [← C_mul, h2]; exact map_ofNat C 41
  linear_combination (-X) * e1 + X ^ 2 * e2

lemma prod2 (u v : ℂ) (h1 : u + v = 9) (h2 : u * v = -11) :
    (1 - C u * X + 41 * X ^ 2 : ℂ[X]) * (1 - C v * X + 41 * X ^ 2) =
      1 - 9 * X + 71 * X ^ 2 - 9 * 41 * X ^ 3 + 41 ^ 2 * X ^ 4 := by
  have e1 : C u + C v = (9 : ℂ[X]) := by rw [← C_add, h1]; exact map_ofNat C 9
  have e2 : C u * C v = (-11 : ℂ[X]) := by
    rw [← C_mul, h2, C_neg]; exact congrArg Neg.neg (map_ofNat C 11)
  linear_combination (-X - 41 * X ^ 3) * e1 + X ^ 2 * e2

lemma root (t : ℝ) (ht : t ^ 2 < 164) :
    ∃ a : ℂ, a + (starRingEnd ℂ) a = t ∧ a * (starRingEnd ℂ) a = 41 ∧ ‖a‖ = Real.sqrt 41 := by
  set r := Real.sqrt (164 - t ^ 2) with hr
  have hr2 : r ^ 2 = 164 - t ^ 2 := Real.sq_sqrt (by linarith)
  refine ⟨⟨t / 2, r / 2⟩, ?_, ?_, ?_⟩
  · apply Complex.ext <;> simp
  · apply Complex.ext <;> simp
    · nlinarith
    · ring
  · rw [Complex.norm_def, Complex.normSq_mk]
    congr 1; nlinarith

theorem main : ∃ α : Multiset ℂ, Multiset.card α = 4 ∧
      (1 - 9 * Polynomial.X + 71 * Polynomial.X ^ 2 - 9 * 41 * Polynomial.X ^ 3 +
          41 ^ 2 * Polynomial.X ^ 4 : ℂ[X]) = (α.map fun a => 1 - C a * Polynomial.X).prod ∧
      ∀ a ∈ α, ‖a‖ = Real.sqrt 41 := by
  set s := Real.sqrt 5 with hs
  have hs2 : s ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 5
  have hs3 : s < 3 := by nlinarith
  set t1 : ℝ := (9 + 5 * s) / 2
  set t2 : ℝ := (9 - 5 * s) / 2
  obtain ⟨a, ha1, ha2, ha3⟩ := root t1 (by simp only [t1]; nlinarith)
  obtain ⟨b, hb1, hb2, hb3⟩ := root t2 (by simp only [t2]; nlinarith)
  refine ⟨{a, (starRingEnd ℂ) a, b, (starRingEnd ℂ) b}, by simp, ?_, ?_⟩
  · simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton]
    rw [← mul_assoc, quad a t1 ha1 ha2, quad b t2 hb1 hb2]
    symm
    apply prod2
    · simp only [t1, t2]; push_cast; ring
    · simp only [t1, t2]; push_cast
      have : ((s : ℂ)) ^ 2 = 5 := by exact_mod_cast hs2
      linear_combination (-25 / 4 : ℂ) * this
  · intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha3
    · rw [Complex.norm_conj]; exact ha3
    · exact hb3
    · rw [Complex.norm_conj]; exact hb3

end WERH

open Polynomial in
theorem solution  :
    ∃ α : Multiset ℂ, Multiset.card α = 4 ∧
      (1 - 9 * Polynomial.X + 71 * Polynomial.X ^ 2 - 9 * 41 * Polynomial.X ^ 3 +
          41 ^ 2 * Polynomial.X ^ 4 : ℂ[X]) = (α.map fun a => 1 - C a * Polynomial.X).prod ∧
      ∀ a ∈ α, ‖a‖ = Real.sqrt 41 := WERH.main

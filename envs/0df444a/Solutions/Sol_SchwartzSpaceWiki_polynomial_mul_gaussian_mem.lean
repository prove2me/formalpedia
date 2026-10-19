-- Prove2me | solution 1 for SchwartzSpaceWiki.polynomial_mul_gaussian_mem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:12:05.208545+00:00
-- url     : https://prove2.me/submissions/abae2cd0-c8e4-45bc-8c17-21c0066eb9ce

import Theorems.Thm_SchwartzSpaceWiki_monomial_mul_gaussian_mem
import Theorems.Thm_SchwartzSpaceWiki_schwartzSpace_isSubspace
import Mathlib.Algebra.MvPolynomial.Funext

open SchwartzSpaceWiki

private lemma eval_monomial_real (n : ℕ) (d : Fin n →₀ ℕ) (c : ℂ) (x : Rn n) :
    MvPolynomial.eval (fun i => (x i : ℂ)) (MvPolynomial.monomial d c) =
      c * (monomial (fun i => d i) x : ℂ) := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [monomial]

theorem solution (n : ℕ) (a : ℝ) (ha : 0 < a) :
    (∀ P : MvPolynomial (Fin n) ℂ,
      (fun x : Rn n => MvPolynomial.eval (fun i => (x i : ℂ)) P *
        Complex.exp (-(a * ‖x‖ ^ 2 : ℝ))) ∈ schwartzSpace n) ∧
    Function.Injective (fun (P : MvPolynomial (Fin n) ℂ) (x : Rn n) =>
      MvPolynomial.eval (fun i => (x i : ℂ)) P * Complex.exp (-(a * ‖x‖ ^ 2 : ℝ))) := by
  classical
  obtain ⟨hzero, hadd, hsmul⟩ := schwartzSpace_isSubspace n
  constructor
  · intro P
    induction P using MvPolynomial.induction_on' with
    | monomial d c =>
      convert hsmul c _ (monomial_mul_gaussian_mem n (fun i => d i) a ha) using 1
      ext x
      simp [eval_monomial_real, mul_assoc]
    | add P Q hP hQ =>
      convert hadd _ hP _ hQ using 1
      ext x
      simp [add_mul]
  · intro P Q h
    apply MvPolynomial.funext_set (fun _ : Fin n => Set.range Complex.ofReal)
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
    intro z hz
    have hz' : ∀ i, ∃ r : ℝ, (r : ℂ) = z i := fun i => hz i (Set.mem_univ i)
    choose r hr using hz'
    let x : Rn n := WithLp.toLp 2 r
    have hx : (fun i => (x i : ℂ)) = z := by funext i; exact hr i
    have he := congrFun h x
    have he' := (mul_right_cancel₀ (Complex.exp_ne_zero _)) he
    rwa [hx] at he'

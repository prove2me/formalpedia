-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartz_even_radial_weight_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T04:18:53.320557+00:00
-- url     : https://prove2.me/submissions/80968f8f-1385-4178-a241-67b37fb9a380

-- New supporting theorem for Appendix D, Lemma D.1.3.4, radial generating family.
import Mathlib

theorem solution {m r : ℕ} (k l : ℕ) :
    ∃ p : MvPolynomial (Fin m ⊕ Fin r) ℂ,
      ∀ (x : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin r)),
      MvPolynomial.eval (Sum.elim (fun i => (x i : ℂ)) (fun j => (y j : ℂ))) p =
        (((1+‖x‖^(2*k))*(1+‖y‖^(2*l)) : ℝ) : ℂ) := by
  classical
  let A : MvPolynomial (Fin m ⊕ Fin r) ℂ := ∑ i : Fin m,MvPolynomial.X (.inl i)^2
  let B : MvPolynomial (Fin m ⊕ Fin r) ℂ := ∑ j : Fin r,MvPolynomial.X (.inr j)^2
  refine ⟨(1+A^k)*(1+B^l),?_⟩
  intro x y
  let e := Sum.elim (fun i => (x i : ℂ)) (fun j => (y j : ℂ))
  have ha : MvPolynomial.eval e A = ((‖x‖^2:ℝ):ℂ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [A,e]
  have hb : MvPolynomial.eval e B = ((‖y‖^2:ℝ):ℂ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [B,e]
  change MvPolynomial.eval e _ = _
  simp only [map_mul,map_add,map_one,map_pow,ha,hb,pow_mul,Complex.ofReal_mul,
    Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_pow]

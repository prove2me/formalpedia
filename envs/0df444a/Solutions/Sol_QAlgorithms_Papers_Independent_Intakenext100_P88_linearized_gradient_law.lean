-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P88.linearized_gradient_law
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:30:28.638051+00:00
-- url     : https://prove2.me/submissions/c56a6bbd-0f03-4f09-87d1-0f55a7d820e6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

open QAlgorithms.Papers.Independent.Intakenext100.P88 in
theorem solution {D T I : Type*} [Fintype T] [Fintype I]
    {h L : ℕ} (M : ExpectationNetwork D I h L) (embed : T ↪ D)
    (theta : Fin L → ℝ) (y : T × I → ℝ) (eta : ℝ) (heta : 0 < eta) :
    (let e := fun b : T × I => expectationOutput M theta (trainingIndex embed b) - y b
     let dp := fun l => -eta * ∑ b, e b *
       coordinateDerivative (fun u => expectationOutput M u (trainingIndex embed b)) theta l
     ∀ a, (∑ l, coordinateDerivative (fun u => expectationOutput M u a) theta l * dp l) =
       -eta * ∑ b, expectationKernel M theta a (trainingIndex embed b) * e b) ∧
    (∀ (N : AmplitudeModel D h L) (labels : T × Fin h → ℂ),
      let e := fun b : T × Fin h => basisAmplitude N theta (embed b.1, b.2) - labels b
      let dp := fun l => -eta * (∑ b, e b *
        star (coordinateDerivative (fun u => basisAmplitude N u (embed b.1, b.2)) theta l)).re
      let de := fun b : T × Bool × Fin h =>
        if b.2.1 then star (e (b.1, b.2.2)) else e (b.1, b.2.2)
      ∀ a, (∑ l, coordinateDerivative (fun u => doubledAmplitude N u a) theta l * (dp l : ℂ)) =
        -(eta / 2 : ℝ) • (∑ b : T × Bool × Fin h,
          amplitudeKernel N theta a (embed b.1, b.2.1, b.2.2) * de b)) := by
  constructor
  · intro e dp a
    simp only [dp, expectationKernel, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun l _ => by ring))
  · intro N labels e dp de a
    have hGf : ∀ (t : T) (k : Fin h) (l : Fin L),
        coordinateDerivative (fun u => doubledAmplitude N u (embed t, false, k)) theta l =
          coordinateDerivative (fun u => basisAmplitude N u (embed t, k)) theta l :=
      fun t k l => rfl
    have hGt : ∀ (t : T) (k : Fin h) (l : Fin L),
        coordinateDerivative (fun u => doubledAmplitude N u (embed t, true, k)) theta l =
          star (coordinateDerivative (fun u => basisAmplitude N u (embed t, k)) theta l) := by
      intro t k l
      show deriv (fun s => star (basisAmplitude N (Function.update theta l s) (embed t, k)))
          (theta l) =
        star (deriv (fun s => basisAmplitude N (Function.update theta l s) (embed t, k))
          (theta l))
      exact deriv.star
    have hS : ∀ l, ((dp l : ℝ) : ℂ) = -(eta : ℂ) *
        (((∑ b, e b * star (coordinateDerivative
            (fun u => basisAmplitude N u (embed b.1, b.2)) theta l)) +
          star (∑ b, e b * star (coordinateDerivative
            (fun u => basisAmplitude N u (embed b.1, b.2)) theta l))) / 2) := by
      intro l
      simp only [dp]
      rw [Complex.ofReal_mul, Complex.re_eq_add_conj, Complex.ofReal_neg]
      rfl
    have hinner : ∀ l, (∑ b : T × Bool × Fin h,
        star (coordinateDerivative (fun u => doubledAmplitude N u (embed b.1, b.2.1, b.2.2))
          theta l) * de b) =
        (∑ b, e b * star (coordinateDerivative
            (fun u => basisAmplitude N u (embed b.1, b.2)) theta l)) +
          star (∑ b, e b * star (coordinateDerivative
            (fun u => basisAmplitude N u (embed b.1, b.2)) theta l)) := by
      intro l
      simp only [de, star_sum, star_mul, star_star, Fintype.sum_prod_type, Fintype.sum_bool,
        hGf, hGt, if_true, if_false, Bool.false_eq_true, ↓reduceIte]
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k _ => by ring))
    rw [Complex.real_smul]
    simp only [amplitudeKernel, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [hinner l, hS l]
    push_cast
    ring

end

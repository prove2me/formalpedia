-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P88.expectation_kernel_psd
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T07:18:53.507302+00:00
-- url     : https://prove2.me/submissions/4e974f13-6c01-4f01-825c-2493b9bfa005

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

open QAlgorithms.Papers.Independent.Intakenext100.P88 in
theorem solution {D I : Type*} [Fintype I] {h L : ℕ}
    (M : ExpectationNetwork D I h L) (theta : Fin L → ℝ) :
    (∀ a b, expectationKernel M theta a b = expectationKernel M theta b a) ∧
    ∀ (n : ℕ) (a : Fin n → D × I),
      Matrix.PosSemidef (fun i j => expectationKernel M theta (a i) (a j)) := by
  refine ⟨fun a b => ?_, fun n a => ?_⟩
  · unfold expectationKernel
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  · let V : Matrix (Fin n) (Fin L) ℝ := fun i l =>
      coordinateDerivative (fun u => expectationOutput M u (a i)) theta l
    have hV : (fun i j => expectationKernel M theta (a i) (a j) : Matrix (Fin n) (Fin n) ℝ) =
        V * V.conjTranspose := by
      ext i j
      rfl
    rw [hV]
    exact Matrix.posSemidef_self_mul_conjTranspose V

end

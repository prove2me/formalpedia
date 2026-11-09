-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P88.amplitude_kernel_psd
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T12:32:45.403739+00:00
-- url     : https://prove2.me/submissions/9390ccb1-dc68-4bcd-a211-d645b1abe809

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

open QAlgorithms.Papers.Independent.Intakenext100.P88 in
theorem solution {D : Type*} {h L : ℕ}
    (M : AmplitudeModel D h L) (theta : Fin L → ℝ) :
    (∀ a b, star (amplitudeKernel M theta b a) = amplitudeKernel M theta a b) ∧
    ∀ (n : ℕ) (a : Fin n → D × Bool × Fin h),
      Matrix.PosSemidef (fun i j => amplitudeKernel M theta (a i) (a j)) := by
  refine ⟨fun a b => ?_, fun n a => ?_⟩
  · unfold amplitudeKernel
    rw [star_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [star_mul', star_star, mul_comm]
  · let V : Matrix (Fin n) (Fin L) ℂ := fun i l =>
      coordinateDerivative (fun u => doubledAmplitude M u (a i)) theta l
    have hV : (fun i j => amplitudeKernel M theta (a i) (a j) : Matrix (Fin n) (Fin n) ℂ) =
        V * V.conjTranspose := by
      ext i j
      rfl
    rw [hV]
    exact Matrix.posSemidef_self_mul_conjTranspose V

end

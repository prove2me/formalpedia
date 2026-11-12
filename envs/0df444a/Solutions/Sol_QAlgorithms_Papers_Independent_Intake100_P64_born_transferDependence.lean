-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.born_transferDependence
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:09:37.267199+00:00
-- url     : https://prove2.me/submissions/d741cd40-e0b5-4d9f-b8dd-736651703ead

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology ComplexConjugate

open QAlgorithms.Papers.Independent.Intake100.P64 in
theorem solution (d : CollisionData) (V : Momentum → ℝ)
    (hV : Integrable V)
    (hf : ∀ pf pi, d.amplitude pf pi = bornMatrixAmplitude d.parameters V pf pi) :
    (∀ pf pi, bornMatrixAmplitude d.parameters V pf pi =
      bornAmplitude d.parameters V (pf - pi)) ∧
    (∀ p P Q, collisionCoefficient d p P Q =
      (Real.sqrt (prefactor d.parameters Q) : ℂ) * bornAmplitude d.parameters V (-Q) *
        (Real.sqrt (d.gas.value (gasArgument d.parameters p P Q)) : ℂ)) ∧
    (∀ Q, bornAmplitude d.parameters V (-Q) = star (bornAmplitude d.parameters V Q)) := by
  have hdot : ∀ pf pi x : Momentum,
      momentumDot pf x - momentumDot pi x = momentumDot (pf - pi) x := by
    intro pf pi x
    simp only [momentumDot, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [PiLp.sub_apply]
    ring
  have hneg : ∀ Q x : Momentum, momentumDot (-Q) x = - momentumDot Q x := by
    intro Q x
    simp only [momentumDot, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [PiLp.neg_apply]
    ring
  have h1 : ∀ pf pi, bornMatrixAmplitude d.parameters V pf pi =
      bornAmplitude d.parameters V (pf - pi) := by
    intro pf pi
    unfold bornMatrixAmplitude bornAmplitude
    simp only [hdot]
  refine ⟨h1, ?_, ?_⟩
  · intro p P Q
    unfold collisionCoefficient
    by_cases hQ : Q = 0
    · rw [if_pos hQ]
      subst hQ
      simp [prefactor]
    · rw [if_neg hQ, hf, h1]
      have hsub : ∀ T : Momentum, T - (1 / 2 : ℝ) • Q - (T + (1 / 2 : ℝ) • Q) = -Q := by
        intro T
        module
      rw [hsub]
  · intro Q
    have key : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun z => rfl
    unfold bornAmplitude
    rw [star_mul', key, key, ← integral_conj, Complex.conj_ofReal]
    congr 1
    congr 1
    funext x
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I,
      Complex.conj_ofReal, hneg, neg_div, Complex.ofReal_neg]
    ring_nf

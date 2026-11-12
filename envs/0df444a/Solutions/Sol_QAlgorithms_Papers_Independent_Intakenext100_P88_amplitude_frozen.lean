-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P88.amplitude_frozen
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:15:42.290197+00:00
-- url     : https://prove2.me/submissions/eea172e7-2846-462e-9c95-cda4085a0248

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

namespace Aux_AF88

open QAlgorithms.Papers.Independent.Intakenext100.P88

theorem frozen_eq {𝕜 T : Type*} [RCLike 𝕜] [Fintype T] [DecidableEq T]
    (K : Matrix T T 𝕜) (step : ℝ) (e : EuclideanSpace 𝕜 T) (t : ℕ) :
    frozenResidual K step e t = l2Action ((1 - step • K) ^ t) e := by
  induction t with
  | zero => simp [frozenResidual, l2Action]
  | succ t ih =>
    simp only [frozenResidual, ih, l2Action, WithLp.ofLp_toLp, Matrix.mulVec_mulVec, pow_succ']

end Aux_AF88

open QAlgorithms.Papers.Independent.Intakenext100.P88 in
theorem solution {D T : Type*} [Fintype T] [DecidableEq T] {h L : ℕ}
    (M : AmplitudeModel D h L) (embed : T ↪ D)
    (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 < eta)
    (v : Fin L → ℝ) (y : T × Fin h → ℂ) (t : ℕ) :
    let incl := fun a : T × Bool × Fin h => (embed a.1, a.2.1, a.2.2)
    let K : Matrix (T × Bool × Fin h) (T × Bool × Fin h) ℂ := fun a b =>
      frozenAmplitudeKernel M delta (incl a) (incl b)
    let e : EuclideanSpace ℂ (T × Bool × Fin h) := WithLp.toLp 2 (fun a =>
      doubledAmplitude M 0 (incl a) + (∑ l, amplitudeJet M delta (incl a) l * (v l : ℂ)) -
        (if a.2.1 then star (y (a.1, a.2.2)) else y (a.1, a.2.2)))
    frozenResidual K (eta / 2) e t = l2Action ((1 - (eta / 2) • K) ^ t) e := by
  intro incl K e
  exact Aux_AF88.frozen_eq K (eta / 2) e t

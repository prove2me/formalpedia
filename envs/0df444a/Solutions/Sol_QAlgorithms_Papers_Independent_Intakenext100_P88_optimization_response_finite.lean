-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P88.optimization_response_finite
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T23:32:14.304589+00:00
-- url     : https://prove2.me/submissions/61137ec1-6d63-4e12-b330-07c29f992cbd

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

namespace Aux_P88_orf
open QAlgorithms.Papers.Independent.Intakenext100.P88

theorem hl2 (A : Matrix Unit Unit ℝ) (w : EuclideanSpace ℝ Unit) :
    (l2Action A w) () = A () () * w () := by
  simp [l2Action, Matrix.mulVec, dotProduct]

theorem aux (Km Dm : Matrix Unit Unit ℝ) (eta e : ℝ) :
    let R := retainedResidual Km Dm eta (WithLp.toLp 2 (fun _ : Unit => e))
    (∀ t, (R t).1 () = (1 - eta * Km () ()) ^ t * e) ∧
    (R 0).2 = 0 ∧
    ∀ t : ℕ, (R (t + 1)).2 () =
      -eta * ((t : ℝ) + 1) * (1 - eta * Km () ()) ^ t * Dm () () * e := by
  intro R
  have step1 : ∀ t, (R (t + 1)).1 = l2Action (1 - eta • Km) (R t).1 := fun t => rfl
  have step2 : ∀ t, (R (t + 1)).2 =
      l2Action (1 - eta • Km) (R t).2 - eta • l2Action Dm (R t).1 := fun t => rfl
  have hcoef : (1 - eta • Km) () () = 1 - eta * Km () () := by
    simp [Matrix.sub_apply, Matrix.smul_apply]
  have hx : ∀ t, (R t).1 () = (1 - eta * Km () ()) ^ t * e := by
    intro t
    induction t with
    | zero =>
      rw [pow_zero, one_mul]
      rfl
    | succ t ih =>
      rw [step1, hl2, ih, hcoef, pow_succ]
      ring
  have hstep : ∀ t, (R (t + 1)).2 () =
      (1 - eta * Km () ()) * (R t).2 () - eta * (Dm () () * (R t).1 ()) := by
    intro t
    rw [step2, PiLp.sub_apply, PiLp.smul_apply, hl2, hl2, hcoef, smul_eq_mul]
  have hy0 : (R 0).2 = 0 := rfl
  refine ⟨hx, hy0, ?_⟩
  intro t
  induction t with
  | zero =>
    rw [hstep, hy0, hx, PiLp.zero_apply]
    push_cast
    ring
  | succ t ih =>
    rw [hstep, ih, hx]
    push_cast
    ring

end Aux_P88_orf

open QAlgorithms.Papers.Independent.Intakenext100.P88 in
theorem solution {h L : ℕ} (M : OptimizationModel h L)
    (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 < eta) (v : Fin L → ℝ) :
    let K := frozenKernel M.model delta ((), ()) ((), ())
    let D := deltaKernel M.model delta v ((), ()) ((), ())
    let e := quadraticOutput M.model delta v ((), ()) - M.minimum
    let R := retainedResidual (fun _ _ : Unit => K) (fun _ _ : Unit => D)
      eta (WithLp.toLp 2 (fun _ : Unit => e))
    (∀ t, (R t).1 () = (1 - eta * K) ^ t * e) ∧
    (R 0).2 = 0 ∧
    ∀ t : ℕ, (R (t + 1)).2 () =
      -eta * ((t : ℝ) + 1) * (1 - eta * K) ^ t * D * e := by
  intro K D e R
  exact Aux_P88_orf.aux (fun _ _ => K) (fun _ _ => D) eta e

end

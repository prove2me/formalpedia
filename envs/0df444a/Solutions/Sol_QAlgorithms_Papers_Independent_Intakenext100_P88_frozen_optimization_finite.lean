-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P88.frozen_optimization_finite
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:33:19.251261+00:00
-- url     : https://prove2.me/submissions/e2d0b50a-b542-433a-9bd8-e0f1c3594231

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

namespace Aux_Q01_frozen_optimization_finite
open QAlgorithms.Papers.Independent.Intakenext100.P88

theorem scalar (K eta e : ℝ) (t : ℕ) :
    frozenResidual (fun _ _ : Unit => K) eta (WithLp.toLp 2 (fun _ : Unit => e)) t () =
      (1 - eta * K) ^ t * e := by
  induction t with
  | zero =>
    rw [pow_zero, one_mul]
    rfl
  | succ n ih =>
    have h : frozenResidual (fun _ _ : Unit => K) eta (WithLp.toLp 2 (fun _ : Unit => e)) (n + 1) =
        l2Action (1 - eta • (fun _ _ : Unit => K : Matrix Unit Unit ℝ))
          (frozenResidual (fun _ _ : Unit => K) eta (WithLp.toLp 2 (fun _ : Unit => e)) n) := rfl
    rw [h]
    have hM : (1 - eta • (fun _ _ : Unit => K : Matrix Unit Unit ℝ)) () () = 1 - eta * K := by
      first
        | rfl
        | simp [Matrix.one_apply]
    simp only [l2Action, PiLp.toLp_apply, Matrix.mulVec, dotProduct, Fintype.univ_unit,
      Finset.sum_singleton]
    show (1 - eta • (fun _ _ : Unit => K : Matrix Unit Unit ℝ)) () () * _ = _
    rw [hM, ih, pow_succ]
    ring

end Aux_Q01_frozen_optimization_finite

open QAlgorithms.Papers.Independent.Intakenext100.P88 in
theorem solution {h L : ℕ} (M : OptimizationModel h L)
    (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 < eta)
    (v : Fin L → ℝ) (t : ℕ) :
    let K := frozenKernel M.model delta ((), ()) ((), ())
    let e := linearOutput M.model delta v ((), ()) - M.minimum
    frozenResidual (fun _ _ : Unit => K) eta (WithLp.toLp 2 (fun _ : Unit => e)) t () =
      (1 - eta * K) ^ t * e := by
  intro K e
  exact Aux_Q01_frozen_optimization_finite.scalar K eta e t

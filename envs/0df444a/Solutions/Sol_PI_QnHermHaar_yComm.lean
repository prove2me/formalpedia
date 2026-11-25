-- Prove2me | solution 1 for PI.QnHermHaar.yComm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:10:31.647034+00:00
-- url     : https://prove2.me/submissions/ab9cee3b-ef01-471d-af6f-92f3fa77a957

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SmoothLevZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnOfEq
import Theorems.Thm_PI_QnHermHaar_Gen_A_ext
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_mul
import Theorems.Thm_PI_QnHermHaar_repY

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset MeasureTheory
open scoped ContDiff
noncomputable section
namespace PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}
private theorem eq_of_repOn_of_agree_on_test (H : Hyp k r z z' i μ) {S T : A (hI H)}
    {Φ Ψ : (Mx k r → ℂ) → Mx k r → ℂ} (hS : RepOn (hI H) S Φ) (hT : RepOn (hI H) T Ψ)
    (e : ∀ f, TestF k r i f → ∀ g ∈ Glev k r i, Φ f g = Ψ f g) : S = T :=
  A_ext (hI H) fun f hf => by
    rw [(hS f hf).2, (hT f hf).2]
    exact mk'_eq_of_eqOn (hI H) (Glev k r i) (hG H) (hS f hf).1 (hT f hf).1 (e f hf)
end PI.QnHermHaar
end
end

set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}
namespace PI.QnHermHaar
theorem _root_.solution (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : YA H a * YA H b = YA H b * YA H a := by
  refine eq_of_repOn_of_agree_on_test H (repOn_mul _ (repY H a) (repY H b)) (repOn_mul _ (repY H b) (repY H a)) fun f _ g _ => ?_
  simp only [MOp]
  ring
end PI.QnHermHaar

-- Prove2me | solution 1 for PI.QnHermHaar.repOn_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:52:44.651081+00:00
-- url     : https://prove2.me/submissions/9a93a706-86a2-43e4-981b-d7df9aec3901

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SmoothLevZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnOfEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}
namespace PI.QnHermHaar
theorem _root_.solution {hI' : IntOn μ (ιo k r) (testSub k r i)} {T : A hI'} {Φ Ψ : (Mx k r → ℂ) → Mx k r → ℂ}
    (h : RepOn hI' T Φ) (e : ∀ f, Φ f = Ψ f) : RepOn hI' T Ψ := by
  have hΦΨ : Φ = Ψ := funext e
  subst hΦΨ
  exact h
end PI.QnHermHaar

-- Prove2me | solution 1 for PI.InLieN.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:29.786359+00:00
-- url     : https://prove2.me/submissions/2f2d5141-cc16-47e4-9f3d-d4a98e5aee04

import Definitions.Def_Formalism_PeriodIntegrals_HaarDefs
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_ContinuousExpLie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
noncomputable section
open PI
open Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI
namespace InLieN
theorem _root_.solution {X : Mx k r} (hX : InLieN k r X) (c : ℝ) : InLieN k r ((c : ℂ) • X) := by
  refine ⟨?_, ?_, ?_⟩
  · show ((c : ℂ) • X)ᴴ * Hpk k r + Hpk k r * ((c : ℂ) • X) = 0
    have h1 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX.1
    have hst : star (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
    rw [Matrix.conjTranspose_smul, hst, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · intro a i hai
    rw [Matrix.smul_apply, hX.2.1 a i hai, smul_zero]
  · intro i j h1 h2 h3
    rw [Matrix.smul_apply, hX.2.2 i j h1 h2 h3, smul_zero]
end InLieN
end PI

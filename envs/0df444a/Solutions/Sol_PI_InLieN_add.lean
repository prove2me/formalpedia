-- Prove2me | solution 1 for PI.InLieN.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:15:37.693182+00:00
-- url     : https://prove2.me/submissions/6d7c0673-da5a-447b-88ac-f6477778524f

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
theorem _root_.solution {X Y : Mx k r} (hX : InLieN k r X) (hY : InLieN k r Y) : InLieN k r (X + Y) := by
  refine ⟨?_, ?_, ?_⟩
  · show (X + Y)ᴴ * Hpk k r + Hpk k r * (X + Y) = 0
    have h1 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX.1
    have h2 : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY.1
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y)
        = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [h1, h2, add_zero]
  · intro a i hai
    rw [Matrix.add_apply, hX.2.1 a i hai, hY.2.1 a i hai, add_zero]
  · intro i j h1 h2 h3
    rw [Matrix.add_apply, hX.2.2 i j h1 h2 h3, hY.2.2 i j h1 h2 h3, add_zero]
end InLieN
end PI

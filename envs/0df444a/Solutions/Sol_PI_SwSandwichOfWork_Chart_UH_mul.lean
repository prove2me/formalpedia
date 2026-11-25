-- Prove2me | solution 1 for PI.SwSandwichOfWork.Chart_UH_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:58.476805+00:00
-- url     : https://prove2.me/submissions/78459f46-40d4-4dbe-b58c-5fe4d12f151e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_UnrealifyRL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_ChartZeroEqOneOfLongWeylSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}
namespace PI.SwSandwichOfWork
theorem _root_.solution {A B : Mat k r} (hA : A ∈ UH (Hpk k r)) (hB : B ∈ UH (Hpk k r)) :
    A * B ∈ UH (Hpk k r) := by
  have hA' : Aᴴ * Hpk k r * A = Hpk k r := hA
  have hB' : Bᴴ * Hpk k r * B = Hpk k r := hB
  show (A * B)ᴴ * Hpk k r * (A * B) = Hpk k r
  rw [Matrix.conjTranspose_mul, show Bᴴ * Aᴴ * Hpk k r * (A * B) = Bᴴ * (Aᴴ * Hpk k r * A) * B by
    simp only [mul_assoc], hA', hB']
end PI.SwSandwichOfWork

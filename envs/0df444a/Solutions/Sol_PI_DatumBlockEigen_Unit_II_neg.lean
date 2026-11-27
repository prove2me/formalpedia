-- Prove2me | solution 1 for PI.DatumBlockEigen.Unit.II_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:23:19.592748+00:00
-- url     : https://prove2.me/submissions/e73e7887-72f1-47eb-8de0-9c02f162bed9

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Unit
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
variable {O ϖ}
namespace PI.DatumBlockEigen.Unit
theorem _root_.solution {p q : ℕ} {y : Matrix (Fin p) (Fin q) F} (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ) :
    -y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by
  intro i j
  obtain ⟨o, ho, e⟩ := hy i j
  exact ⟨-o, O.neg_mem ho, by rw [Matrix.neg_apply, e, mul_neg]⟩
end PI.DatumBlockEigen.Unit

-- Prove2me | solution 1 for PI.DatumBlockEigen.Unit.II_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:19:59.496954+00:00
-- url     : https://prove2.me/submissions/5a27ccc3-bde2-4759-be21-0445add86435

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
theorem _root_.solution {p q : ℕ} {y z : Matrix (Fin p) (Fin q) F} (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ)
    (hz : z ∈ Formalism.DoubleCosetMeasures.IIset O ϖ) : y + z ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by
  intro i j
  obtain ⟨o, ho, e⟩ := hy i j
  obtain ⟨o', ho', e'⟩ := hz i j
  exact ⟨o + o', O.add_mem ho ho', by rw [Matrix.add_apply, e, e', mul_add]⟩
end PI.DatumBlockEigen.Unit

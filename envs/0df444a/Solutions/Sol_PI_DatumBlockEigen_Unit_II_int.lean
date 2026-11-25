-- Prove2me | solution 1 for PI.DatumBlockEigen.Unit.II_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:35:17.696613+00:00
-- url     : https://prove2.me/submissions/f5d25a1f-ae86-498e-ac2b-de3aa8f2b773

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
theorem _root_.solution {p q : ℕ} (hϖ : ϖ ∈ O) {y : Matrix (Fin p) (Fin q) F}
    (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ) : ∀ i j, y i j ∈ O := fun i j => by
  obtain ⟨o, ho, e⟩ := hy i j
  rw [e]; exact O.mul_mem hϖ ho
end PI.DatumBlockEigen.Unit

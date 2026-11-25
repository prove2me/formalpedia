-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.WbDefC.cT_eq_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:38.672445+00:00
-- url     : https://prove2.me/submissions/52567fd0-e6d9-4ac4-a35a-a55a79516306

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_MiscLemmasI_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_CTEqConjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.WbDefC
namespace PI.UnitaryGroupMassFormula.CntFormula.WbDefC
theorem _root_.solution {m k : Type} (P : Matrix m k ℂ) :
    Formalism.UG.cT (starRingEnd ℂ) P = Pᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
end PI.UnitaryGroupMassFormula.CntFormula.WbDefC

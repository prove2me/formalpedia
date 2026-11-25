-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.WbDefC.jpq_mulVec_of_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:42.233059+00:00
-- url     : https://prove2.me/submissions/34ae85c7-1eb0-4df8-800b-401195f21b22

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
theorem _root_.solution {p q : ℕ} (w : Fin p ⊕ Fin q → ℂ) (hw : ∀ j, w (Sum.inr j) = 0) :
    Formalism.UG.Jpq p q *ᵥ w = w := by
  have hr : w ∘ Sum.inr = 0 := funext hw
  ext x
  rcases x with i | j
  · simp [Formalism.UG.Jpq, Matrix.fromBlocks_mulVec, hr]
  · simp [Formalism.UG.Jpq, Matrix.fromBlocks_mulVec, hr, hw]
end PI.UnitaryGroupMassFormula.CntFormula.WbDefC

-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.Jpq_mulVec_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:41.764731+00:00
-- url     : https://prove2.me/submissions/1df16f48-bbe7-449c-82ed-6a8933020313

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_HasSignatureExistsNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
theorem _root_.solution {p q : ℕ} (u : Fin p ⊕ Fin q → ℂ) (hu : ∀ j, u (Sum.inr j) = 0) :
    Jpq p q *ᵥ u = u := by
  have h0 : (u ∘ Sum.inr) = 0 := funext hu
  rw [Jpq, Matrix.fromBlocks_mulVec, h0]
  funext i
  cases i <;> simp [hu]
end PI.UnitaryGroupMassFormula.FlagGramNonneg

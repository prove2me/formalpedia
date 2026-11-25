-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.form_Jpq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:48.741954+00:00
-- url     : https://prove2.me/submissions/49ad8cde-5e58-4699-a597-ee755229dbca

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_SylvesterLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Matrix
namespace PI.AutLzFinite.SlopeTestRemainingChoices
theorem _root_.solution (p q : ℕ) (y : Fin p ⊕ Fin q → ℂ) :
    star y ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ y) =
      (∑ i, star (y (Sum.inl i)) * y (Sum.inl i)) - ∑ j, star (y (Sum.inr j)) * y (Sum.inr j) := by
  unfold Formalism.UG.Jpq
  simp [dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec,
    Function.comp_def, sub_eq_add_neg] <;> ring
end PI.AutLzFinite.SlopeTestRemainingChoices

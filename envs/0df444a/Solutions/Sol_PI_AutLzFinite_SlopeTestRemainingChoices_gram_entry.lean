-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.gram_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:13.834713+00:00
-- url     : https://prove2.me/submissions/754e7dcd-75bf-4946-8d89-6d695e2fe818

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_SylvesterLe
import Definitions.Def_Lemmata_GeneralBFactUpperAltForm_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_hT_expand
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Matrix Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
namespace PI.AutLzFinite.SlopeTestRemainingChoices
theorem _root_.solution (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    {k : Type} (τ : E →+* ℂ) (u : k → S.V) (a b : k) :
    ((coordC S τ u)ᴴ * S.gram.map τ * coordC S τ u) a b = τ (S.hT (u a) (u b)) := by
  rw [hT_expand, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, coordC, Matrix.of_apply, Matrix.map_apply,
    map_sum, map_mul, hstar, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl
end PI.AutLzFinite.SlopeTestRemainingChoices

-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.coord_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:58.194164+00:00
-- url     : https://prove2.me/submissions/d2f77c6b-0c16-4f55-b910-5d063c80769f

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_SylvesterLe
import Definitions.Def_Lemmata_GeneralBFactUpperAltForm_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective
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
theorem _root_.solution {k : Type} [Fintype k] (u : k → S.V) (hu : LinearIndependent E u) :
    Function.Injective (Matrix.of fun i a => S.frame.repr (u a) i).mulVec := by
  intro c d hcd
  have key : ∀ c : k → E, (Matrix.of fun i a => S.frame.repr (u a) i) *ᵥ c = S.frame.repr (∑ a, c a • u a) := by
    intro c; ext i
    simp [Matrix.mulVec, dotProduct, map_sum, mul_comm]
  rw [key, key] at hcd
  have h2 := S.frame.repr.injective (Finsupp.ext fun i => congrFun hcd i)
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h2
  simp_rw [← sub_smul] at h2
  have h3 := (Fintype.linearIndependent_iff.mp hu) (fun a => c a - d a) h2
  funext a; exact sub_eq_zero.mp (h3 a)
end PI.AutLzFinite.SlopeTestRemainingChoices

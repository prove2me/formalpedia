-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.hT_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:54.393457+00:00
-- url     : https://prove2.me/submissions/3b38dbb0-e111-4c4d-8b91-cc3bbcabca6f

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
theorem _root_.solution (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * S.gram i j * S.frame.repr y j := by
  have hx : ∀ w, S.hT x w = ∑ i, star (S.frame.repr x i) * S.hT (S.frame i) w := by
    intro w
    conv_lhs => rw [← S.frame.sum_repr x]
    rw [map_sum, LinearMap.sum_apply]
    simp [LinearMap.map_smulₛₗ, starRingEnd_apply]
  have hy : ∀ w, S.hT w y = ∑ j, S.hT w (S.frame j) * S.frame.repr y j := by
    intro w
    conv_lhs => rw [← S.frame.sum_repr y]
    rw [map_sum]
    simp [mul_comm]
  rw [hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [HSpace.gram, mul_assoc]
end PI.AutLzFinite.SlopeTestRemainingChoices

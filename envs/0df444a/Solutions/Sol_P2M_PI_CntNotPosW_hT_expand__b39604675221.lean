-- Prove2me | solution 1 for P2M_PI_CntNotPosW_hT_expand__b39604675221
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:36.426903+00:00
-- url     : https://prove2.me/submissions/51184a3a-2f0b-42b7-95ca-b7bf9fc12250

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountPositivity_CardLeOfNegFamily
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
open PI PI.CntNotPosW
open Matrix
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.CntNotPosW
theorem _root_.solution (S : Formalism.BasicNotions.HSpace E) (x y : S.V) :
    S.hT x y = ∑ a, ∑ b, star (S.frame.repr x a) * S.gram a b * S.frame.repr y b := by
  have hx := S.frame.sum_repr x
  have hy := S.frame.sum_repr y
  conv_lhs => rw [← hx, ← hy]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Finset.mul_sum, Formalism.BasicNotions.HSpace.gram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [RingHom.id_apply]
  ring
end PI.CntNotPosW

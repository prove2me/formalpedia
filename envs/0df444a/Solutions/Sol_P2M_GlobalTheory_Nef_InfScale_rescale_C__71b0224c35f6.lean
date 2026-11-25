-- Prove2me | solution 1 for P2M_GlobalTheory_Nef_InfScale_rescale_C__71b0224c35f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:51:00.296799+00:00
-- url     : https://prove2.me/submissions/c36022ab-721f-4a43-b3f1-d2ccaae47734

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsScalingCompatibleExpansionAtInfinity
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.InfScale
variable {F : Type} [Field F]
namespace GlobalTheory.Nef.InfScale
theorem _root_.solution (c a : F) : PowerSeries.rescale c (PowerSeries.C a) = PowerSeries.C a := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  rcases n with _ | n <;> simp
end GlobalTheory.Nef.InfScale

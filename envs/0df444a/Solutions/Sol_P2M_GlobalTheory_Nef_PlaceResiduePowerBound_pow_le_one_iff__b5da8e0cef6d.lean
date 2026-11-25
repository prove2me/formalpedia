-- Prove2me | solution 1 for P2M_GlobalTheory_Nef_PlaceResiduePowerBound_pow_le_one_iff__b5da8e0cef6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:51:02.716333+00:00
-- url     : https://prove2.me/submissions/8b7fa4cf-ea65-49e2-bb90-b6ffc5c79576

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceRestrictionExistsPow
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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PlaceResiduePowerBound
open WithZero
variable {F : Type} [Field F]
namespace GlobalTheory.Nef.PlaceResiduePowerBound
theorem _root_.solution {e : ℕ} (he : e ≠ 0) {a : ℤᵐ⁰} : a ^ e ≤ 1 ↔ a ≤ 1 := by
  simpa using (pow_le_pow_iff_left₀ (zero_le' (a := a)) (zero_le' (a := (1 : ℤᵐ⁰))) he)
end GlobalTheory.Nef.PlaceResiduePowerBound

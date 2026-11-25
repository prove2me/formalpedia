-- Prove2me | solution 1 for PI.CntNotPosW.hT_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:39.000369+00:00
-- url     : https://prove2.me/submissions/5ae9d5ca-c615-434a-87ca-3e4ce1eadc2d

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountPositivity_CardLeOfNegFamily
import Theorems.Thm_P2M_PI_CntNotPosW_hT_expand__b39604675221

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CntNotPosW
open Matrix
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.CntNotPosW
theorem _root_.solution (S : Formalism.BasicNotions.HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (x y : S.V) :
    τ (S.hT x y) = ∑ a, ∑ b, star (τ (S.frame.repr x a)) * (S.gram.map τ) a b * τ (S.frame.repr y b) := by
  rw [hT_expand', map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, map_mul, hτ, Matrix.map_apply, starRingEnd_apply]
end PI.CntNotPosW

-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.mj_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:57.289815+00:00
-- url     : https://prove2.me/submissions/455b4ec4-bb9c-4da7-95aa-e24a4bbbc40a

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MjSmulRight
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
open Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
variable {S}
namespace PI.AutLzFinite.SlopeTestRemainingChoices
theorem _root_.solution (z x y : S.V) : mj S z y x = star (mj S z x y) := by
  have hs : ∀ a b : S.V, star (S.hT a b) = S.hT b a := fun a b => by
    have h := S.herm.eq a b
    rwa [starRingEnd_apply] at h
  simp only [mj, star_sub, star_mul', star_div₀, hs, star_ofNat]
  ring
end PI.AutLzFinite.SlopeTestRemainingChoices

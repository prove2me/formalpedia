-- Prove2me | solution 1 for PI.SqPairLocal.FixD.irr_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:20:16.913255+00:00
-- url     : https://prove2.me/submissions/9a4faa21-06de-434f-b464-803bd5a7cd40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnitIffSub
import Theorems.Thm_PI_SqPairLocal_FixD_isUnit_iff_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open PI PI.SqPairLocal PI.SqPairLocal.FixD
variable {R : Type} [CommRing R] [IsDomain R] (σ : R ≃+* R)
namespace PI.SqPairLocal.FixD
theorem _root_.solution {ϖ : R} (hϖ : Irreducible ϖ) (h : ϖ ∈ fixSub σ) :
    Irreducible (⟨ϖ, h⟩ : fixSub σ) := by
  refine ⟨fun hu => hϖ.not_isUnit ((isUnit_iff_sub σ _).1 hu), fun a b hab => ?_⟩
  have h' : ϖ = (a : R) * b := congrArg Subtype.val hab
  rcases hϖ.isUnit_or_isUnit h' with ha | hb
  · exact Or.inl (isUnit_sub σ ha)
  · exact Or.inr (isUnit_sub σ hb)
end PI.SqPairLocal.FixD

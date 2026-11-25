-- Prove2me | solution 1 for PI.SqPairLocal.FixD.dvr_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:30.968664+00:00
-- url     : https://prove2.me/submissions/d1339f24-94ca-4d1e-b4b4-b4256a68c8b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnitIffSub
import Theorems.Thm_PI_SqPairLocal_FixD_irr_sub
import Theorems.Thm_PI_SqPairLocal_FixD_assoc_sub

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
theorem _root_.solution [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) (h : ϖ ∈ fixSub σ) :
    IsDiscreteValuationRing (fixSub σ) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨⟨ϖ, h⟩, irr_sub σ hϖ h, fun hx => assoc_sub σ hϖ h hx⟩
end PI.SqPairLocal.FixD

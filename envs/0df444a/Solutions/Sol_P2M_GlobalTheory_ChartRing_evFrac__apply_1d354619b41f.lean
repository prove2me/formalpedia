-- Prove2me | solution 1 for P2M_GlobalTheory_ChartRing_evFrac__apply_1d354619b41f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:49:22.28238+00:00
-- url     : https://prove2.me/submissions/b365a1a3-035a-4418-a4cc-1dbc54bfde37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsPrincipalIdealRingOfIsLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries IsLocalRing
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable [IsAdicComplete (maximalIdeal O) O]
variable (hπ : Irreducible π)
variable (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]
  (U : Type*) [CommRing U] [Algebra O⟦X⟧ U] [IsLocalization.Away (C π * X : O⟦X⟧) U]
namespace GlobalTheory.ChartRing
theorem _root_.solution [Algebra O U] [IsScalarTower O O⟦X⟧ U] (z : U) :
    evFracₐ hπ K U z = evFrac hπ K U z := rfl
end GlobalTheory.ChartRing

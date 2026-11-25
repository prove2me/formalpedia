-- Prove2me | solution 1 for PI.GreenHCLabel.basics_lin_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:42:09.53433+00:00
-- url     : https://prove2.me/submissions/5385e7ce-f4e2-4a45-ae67-545ce138eef4

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_SupportExistsOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_Basics

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
noncomputable section
open PI PI.GreenHCLabel
variable {Γ : Type} [Group Γ]
namespace PI.GreenHCLabel
theorem _root_.solution {σ τ υ : FDRep ℂ Γ} (f : σ ⟶ τ) (h : τ ⟶ υ) :
    basicsLin (f ≫ h) = basicsLin h ∘ₗ basicsLin f := rfl
end PI.GreenHCLabel

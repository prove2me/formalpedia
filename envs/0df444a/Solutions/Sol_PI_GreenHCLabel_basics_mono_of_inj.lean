-- Prove2me | solution 1 for PI.GreenHCLabel.basics_mono_of_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:53.682808+00:00
-- url     : https://prove2.me/submissions/a7b1d617-45a7-49dc-904e-27b16527a98f

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_SupportExistsOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_Basics
import Theorems.Thm_PI_GreenHCLabel_basics_hom_ext

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
theorem _root_.solution {σ τ : FDRep ℂ Γ} (f : σ ⟶ τ) (hf : Function.Injective (basicsLin f)) :
    Mono f := by
  refine ⟨fun {Z} a b hab => basics_hom_ext (LinearMap.ext fun x => hf ?_)⟩
  have := congrArg (fun k => basicsLin k x) hab
  exact this
end PI.GreenHCLabel

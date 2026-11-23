-- Prove2me | solution 1 for PI.GreenHCLabel.basics_hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:19.331493+00:00
-- url     : https://prove2.me/submissions/21766510-bc5d-48cf-ba11-9a3265956cc3

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
theorem _root_.solution {σ τ : FDRep ℂ Γ} {f h : σ ⟶ τ} (e : basicsLin f = basicsLin h) : f = h := by
  first
  | exact Action.Hom.ext (FGModuleCat.hom_ext e)
  | (apply Action.Hom.ext; apply FGModuleCat.hom_ext; exact e)
  | (ext1; ext1; exact e)
end PI.GreenHCLabel

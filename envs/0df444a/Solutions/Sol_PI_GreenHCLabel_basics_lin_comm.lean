-- Prove2me | solution 1 for PI.GreenHCLabel.basics_lin_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:19.650394+00:00
-- url     : https://prove2.me/submissions/020a58ac-e858-4a06-b2c5-f65a50625b6a

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
theorem _root_.solution {σ τ : FDRep ℂ Γ} (f : σ ⟶ τ) (g : Γ) :
    basicsLin f ∘ₗ σ.ρ g = τ.ρ g ∘ₗ basicsLin f := by
  first
  | exact congrArg (fun x => x.hom.hom) (f.comm g)
  | exact congrArg (fun x => x.hom) (f.comm g)
  | (have h := f.comm g; exact (FGModuleCat.hom_ext_iff.1 h))
end PI.GreenHCLabel

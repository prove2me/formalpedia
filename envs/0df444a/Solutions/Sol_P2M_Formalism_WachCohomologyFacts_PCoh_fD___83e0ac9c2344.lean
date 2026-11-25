-- Prove2me | solution 1 for P2M_Formalism_WachCohomologyFacts_PCoh_fD___83e0ac9c2344
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:47:39.659012+00:00
-- url     : https://prove2.me/submissions/95b0da80-c03a-4438-b664-897f117c5c87

import Definitions.Def_Formalism_FrobeniusContraction_Statement
import Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_FiniteCocyclesLeCocycles
import Theorems.Thm_P2M_Formalism_WachCohomologyFacts_PCoh___apply_7b9df26caa1f
import Theorems.Thm_Formalism_WachCohomologyFacts_PCoh_fD_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WachCohomologyFacts Formalism.WachCohomologyFacts.PCoh
open Formalism.WachCohomologyFacts
variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : Base O A} {E : Amb B AA} {n : ℕ}
  {V₁ : Type} [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
  [Module O V₁] [IsScalarTower O AA V₁]
  {V₂ : Type} [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
  [Module O V₂] [IsScalarTower O AA V₂]
  {W₁ : WachDatum E n V₁} {W₂ : WachDatum E n V₂} (h : Hom W₁ W₂)
namespace Formalism.WachCohomologyFacts.PCoh
theorem _root_.solution (x : ZMod n → V₁) : h.fD (W₁.Φ x) = W₂.Φ (h.fD x) := by
  funext j
  simp only [fD_apply, Φ_apply, h.φ_comm]
end Formalism.WachCohomologyFacts.PCoh

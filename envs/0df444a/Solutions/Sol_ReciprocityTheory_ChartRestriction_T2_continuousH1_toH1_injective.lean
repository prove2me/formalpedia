-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.T2.continuousH1_toH1_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:28:43.455644+00:00
-- url     : https://prove2.me/submissions/9f13cd64-038c-4910-8be2-a234befdf9f3

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Formalism_WachLatticeTwists_CharacterSplitJumps_Statement
import Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_Statement
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_TraceFormulas_LatDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.T2
open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {O Γ M : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module O M]
variable [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M]
namespace ReciprocityTheory.ChartRestriction.T2
theorem _root_.solution (ρ : Representation O Γ M) : Function.Injective (toH1Cocycles ρ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : (Submodule.Quotient.mk (continuousCocycleInclusion ρ z) : H1z ρ) = 0 := hx
  rw [Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨v, hv⟩ := h1
  rw [Submodule.Quotient.mk_eq_zero]
  exact (ReciprocityTheory.Gal.mem_coboundaries1 ρ _).2 ⟨v, fun g => (congrFun hv g).symm⟩
end ReciprocityTheory.ChartRestriction.T2

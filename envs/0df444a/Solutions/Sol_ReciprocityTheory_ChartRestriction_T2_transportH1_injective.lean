-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.T2.transportH1_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:28:38.494834+00:00
-- url     : https://prove2.me/submissions/7b2af6b2-2fbe-4b1c-92b7-fb629fa692dc

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
variable {O Γ Γ' M M' : Type} [CommRing O] [Group Γ] [Group Γ'] [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
namespace ReciprocityTheory.ChartRestriction.T2
theorem _root_.solution (e : Γ ≃* Γ') (u : M ≃ₗ[O] M') (ρ : Representation O Γ M) (ρ' : Representation O Γ' M')
    (hu : ∀ g m, u (ρ g m) = ρ' (e g) (u m)) : Function.Injective (traceH1 e u ρ ρ' hu) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : (Submodule.Quotient.mk (transportCocycles e u ρ ρ' hu z) : H1z ρ) = 0 := hx
  rw [Submodule.Quotient.mk_eq_zero] at h1 ⊢
  obtain ⟨v, hv⟩ := h1
  refine ⟨u v, funext fun g' => ?_⟩
  obtain ⟨g, rfl⟩ := e.surjective g'
  have h2 : ρ g v - v = u.symm (z.1 (e g)) := congrFun hv g
  show ρ' (e g) (u v) - u v = z.1 (e g)
  rw [← hu, ← map_sub, h2, LinearEquiv.apply_symm_apply]
end ReciprocityTheory.ChartRestriction.T2

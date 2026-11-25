-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.pair_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:48:29.331218+00:00
-- url     : https://prove2.me/submissions/c8b40737-f768-4ed1-b5a8-405caaa31ab0

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HomFInjective
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_SubsingletonHOfSubsingleton
import Theorems.Thm_ReciprocityTheory_Coh_shp_qi_of_bij
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_hom_f_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
theorem _root_.solution {M : TRep R G} {M' : TRep R G'} (P : Pair M M') (hφ : IsHomeomorph P.φ)
    (hu : IsHomeomorph P.u) (n : ℕ) : Bijective (P.hom.H n) := by
  refine shp_qi_of_bij P.hom (fun n => ⟨hom_f_injective P hφ.surjective hu.injective n, fun t' => ?_⟩) n
  let eφ := IsHomeomorph.homeomorph _ hφ
  let eu := IsHomeomorph.homeomorph _ hu
  have hc : Continuous fun v : Fin n → G => eu.symm (t'.1 fun i => eφ.symm (v i)) :=
    eu.symm.continuous.comp ((show Continuous t'.1 from t'.2).comp
      (continuous_pi fun i => eφ.symm.continuous.comp (continuous_apply i)))
  refine ⟨⟨_, hc⟩, Subtype.ext (funext fun g => ?_)⟩
  show eu (eu.symm (t'.1 fun i => eφ.symm (eφ (g i)))) = t'.1 g
  rw [eu.apply_symm_apply]
  exact congrArg t'.1 (funext fun i => eφ.symm_apply_apply (g i))
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.trivial_inflation_h1_rat_mod_int_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:09:27.172181+00:00
-- url     : https://prove2.me/submissions/30557e34-1d06-4d9a-bac0-cd86cf46ac01

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_BrUnrA
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_exists_cls
import Theorems.Thm_ReciprocityTheory_Coh_LongExactSequenceMaps_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_ProjectiveLinePlaces_H_cls
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_h1_equiv_characters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section
variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G']
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (φ : G' →* G) (hφ : Continuous φ) (hs : Surjective φ) :
    Injective ((trivInfl φ hφ QZ).hom.H 1) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, hx, rfl⟩ := Cx.exists_cls c
  obtain ⟨e, he⟩ := exists_h1_equiv_characters G
  obtain ⟨e', he'⟩ := exists_h1_equiv_characters G'
  apply e.injective
  rw [map_zero]
  refine Subtype.ext (AddMonoidHom.ext fun a => ?_)
  obtain ⟨g', hg'⟩ := hs a.toMul
  rw [Cx.Hom.H_cls] at hc
  have h1 := he' _ ((trivInfl φ hφ QZ).hom.d_f_eq_zero hx) g'
  rw [hc, map_zero] at h1
  have h2 := he x hx (φ g')
  rw [hg'] at h2
  have h3 : (fun i => φ ((![g'] : Fin 1 → G') i)) = ![a.toMul] := by
    funext i; fin_cases i; exact hg'
  have h4 : (((trivInfl φ hφ QZ).hom.f 1 x).1 ![g'] : QZ) = x.1 ![a.toMul] := congrArg x.1 h3
  exact h2.trans (h4.symm.trans h1.symm)
end ReciprocityTheory.DiscreteGroups.LocalClassField

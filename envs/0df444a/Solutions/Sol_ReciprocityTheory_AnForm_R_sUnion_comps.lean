-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.sUnion_comps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:34:21.877938+00:00
-- url     : https://prove2.me/submissions/54c6c3f8-d372-4358-8454-414f4d56e56b

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace IrreducibleComponentPreimages
noncomputable section
section Top
variable {α : Type*} [TopologicalSpace α]
private theorem isIrreducible_preimage_coe_of_subset (T D : Set α) (hDT : D ⊆ T) (hD : IsIrreducible D) :
    IsIrreducible ((↑) ⁻¹' D : Set T) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy⟩ := hD.1
    exact ⟨⟨y, hDT hy⟩, hy⟩
  · intro u v hu hv hau hbv
    obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.1 hu
    obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.1 hv
    obtain ⟨a, ha, hau⟩ := hau
    obtain ⟨b, hb, hbv⟩ := hbv
    obtain ⟨c, hc, hcu, hcv⟩ := hD.2 u' v' hu' hv' ⟨a.1, ha, hau⟩ ⟨b.1, hb, hbv⟩
    exact ⟨⟨c, hDT hc⟩, hc, hcu, hcv⟩
end Top
variable {W : Scheme.{0}}
section Chart
variable {s : W ⟶ Spec (.of ℂ)}
end Chart
end
end ReciprocityTheory.AnForm.R
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace IrreducibleComponentPreimages
noncomputable section
variable {α : Type*} [TopologicalSpace α]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (T : Set α) : ⋃₀ comps T = T := by
  refine Set.Subset.antisymm (Set.sUnion_subset fun C hC => hC.1.2) fun x hx => ?_
  let y : T := ⟨x, hx⟩
  have hI : IsIrreducible (irreducibleComponent y) := isIrreducible_irreducibleComponent
  refine ⟨(↑) '' irreducibleComponent y,
    ⟨⟨hI.image _ continuous_subtype_val.continuousOn, by rintro _ ⟨z, -, rfl⟩; exact z.2⟩, ?_⟩,
    ⟨y, mem_irreducibleComponent, rfl⟩⟩
  intro D hD hCD
  have hpre := isIrreducible_preimage_coe_of_subset T D hD.2 hD.1
  have hsub : irreducibleComponent y ⊆ (↑) ⁻¹' D := fun z hz => hCD ⟨z, hz, rfl⟩
  have hle := (irreducibleComponent_mem_irreducibleComponents y).2 hpre hsub
  intro d hd
  exact ⟨⟨d, hD.2 hd⟩, hle hd, rfl⟩
end ReciprocityTheory.AnForm.R

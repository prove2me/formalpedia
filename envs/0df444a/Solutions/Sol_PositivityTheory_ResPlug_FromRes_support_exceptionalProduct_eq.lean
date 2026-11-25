-- Prove2me | solution 1 for PositivityTheory.ResPlug.FromRes.support_exceptionalProduct_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:29:00.544145+00:00
-- url     : https://prove2.me/submissions/ee2d1489-fb18-4d12-b0b3-48c0118506c9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Statements
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsClopen
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_WeilBound_CoreStatements_ResolutionCharZero_FromResSnc
import Theorems.Thm_PositivityTheory_ResPlug_FromRes_support_list_prod
import Theorems.Thm_PositivityTheory_ResPlug_FromRes_coe_support_comap
import Theorems.Thm_PositivityTheory_ResPlug_FromRes_preimage_union_eq_strictTransform_union
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open PositivityTheory PositivityTheory.ResPlug PositivityTheory.ResPlug.FromRes
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace PositivityTheory.ResPlug.FromRes
theorem _root_.solution {k : Type} [Field k] {X : Scheme.{0}}
    {p : X ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType p] {I : X.IdealSheafData} {s : BlowupSequence X}
    (h : IsPrincipalizingSequence p I [] s) :
    ∃ boundary : ∀ i : ℕ, List (s.obj i).IdealSheafData,
      (∀ i, i ≤ s.length → HasSimpleNormalCrossings (s.structMap i ≫ p) (boundary i)) ∧
      ((s.exceptionalProduct s.length).support : Set s.top) = ((boundary s.length).prod.support : Set s.top) := by
  obtain ⟨ideal, bd, -, hb0, -, -, -, -, hbsucc, -, -, hsm, hsnc⟩ := h
  refine ⟨bd, hsnc, ?_⟩
  have key : ∀ i, i ≤ s.length →
      ((s.exceptionalProduct i).support : Set (s.obj i)) = ((bd i).prod.support : Set (s.obj i)) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hb0]
      simp only [List.map_nil, List.prod_nil, Scheme.IdealSheafData.one_eq_top]
      rfl
    | succ n ih =>
      intro hn
      have hlt : n < s.length := hn
      have : Smooth (s.structMap (n + 1) ≫ p) := hsm (n + 1) hn
      have : IsLocallyNoetherian (s.obj (n + 1)) :=
        LocallyOfFiniteType.isLocallyNoetherian (s.structMap (n + 1) ≫ p)
      have hE : s.exceptionalProduct (n + 1) =
          (s.exceptionalProduct n).comap (s.blowupMap n) * (s.center n).comap (s.blowupMap n) := rfl
      rw [hE, hbsucc n hlt, List.prod_append, List.prod_singleton, Scheme.IdealSheafData.support_mul,
        Scheme.IdealSheafData.support_mul]
      simp only [TopologicalSpace.Closeds.coe_sup]
      rw [coe_support_comap, ih hlt.le, support_list_prod, support_list_prod, Set.preimage_iUnion₂,
        coe_support_comap]
      simp only [List.mem_map]
      ext x
      simp only [Set.mem_union, Set.mem_iUnion, exists_prop]
      constructor
      · rintro (⟨D, hD, hx⟩ | hx)
        · have := (preimage_union_eq_strictTransform_union (s.blowupMap n) (s.center n) D).subset
            (Or.inl hx : x ∈ _ ∪ _)
          rcases this with h1 | h1
          · exact Or.inl ⟨_, ⟨D, hD, rfl⟩, h1⟩
          · exact Or.inr h1
        · exact Or.inr hx
      · rintro (⟨_, ⟨D, hD, rfl⟩, hx⟩ | hx)
        · have := (preimage_union_eq_strictTransform_union (s.blowupMap n) (s.center n) D).superset
            (Or.inl hx : x ∈ _ ∪ _)
          rcases this with h1 | h1
          · exact Or.inl ⟨D, hD, h1⟩
          · exact Or.inr h1
        · exact Or.inr hx
  exact key s.length le_rfl
end PositivityTheory.ResPlug.FromRes

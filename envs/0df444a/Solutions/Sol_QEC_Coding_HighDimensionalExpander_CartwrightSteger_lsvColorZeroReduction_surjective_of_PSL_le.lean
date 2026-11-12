-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvColorZeroReduction_surjective_of_PSL_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:39:26.373779+00:00
-- url     : https://prove2.me/submissions/18750fb2-80f5-4958-8ce6-975f59a151cd

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_PSL_commutator_eq_top


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level) :
    ∀ x : IndexCartwrightStegerColorZero P r level,
      ∃ g : (lsvBuildingLatticeColor P r).ker,
        buildingLatticeReduction P r level g.1 = x.1 := by
  let L := BuildingCartwrightStegerLattice P r
  let F := IndexCartwrightStegerImage P r level
  let K := IndexCartwrightStegerColorZero P r level
  let color := lsvBuildingLatticeColor P r
  let reduction := buildingLatticeReduction P r level
  have hcommL : commutator L ≤ color.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hrange : reduction.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      (buildingLatticeReduction_surjective P r level)
  have hmapped : (commutator L).map reduction = commutator F := by
    rw [map_commutator_eq, hrange]
    rfl
  have hcommF : commutator F ≤ color.ker.map reduction := by
    rw [← hmapped]
    exact Subgroup.map_mono hcommL
  let e := indexCartwrightStegerColorZeroEquivPSLOfLe P r level hPSL
  letI : Group.IsPerfect (PSL P r level) :=
    ⟨PSL_commutator_eq_top P r level⟩
  letI : Group.IsPerfect K :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
      e.symm.surjective
  intro x
  have hxcommK : x ∈ commutator K := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top x
  have hxmap : (x : F) ∈ (commutator K).map K.subtype :=
    ⟨x, hxcommK, rfl⟩
  rw [K.map_subtype_commutator] at hxmap
  have hxcommF : (x : F) ∈ commutator F :=
    (Subgroup.commutator_mono le_top le_top) hxmap
  obtain ⟨g, hg, hgreduction⟩ := hcommF hxcommF
  exact ⟨⟨g, hg⟩, hgreduction⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger

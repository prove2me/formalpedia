-- Prove2me | solution 1 for PeriodicConstantApprox.replicated_cell_packing_density_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/88b16abd-c3de-429d-bbdf-9d918d80f776

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicSpherePacking_encard_centers_in_fundamental_region
import Theorems.Thm_replicated_centers_intersection_of_subset
import Theorems.Thm_PeriodicConstant_axis_cell_is_bounded
import Theorems.Thm_PeriodicConstant_inset_cell_subset_axis_cell
import Theorems.Thm_PeriodicConstantApprox_translated_axis_cells_cover_uniquely
import Theorems.Thm_PeriodicConstantApprox_ball_subset_translated_cell_of_interior

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
open PeriodicConstantApprox
open Filter
variable {d : ℕ}
open scoped ENNReal Pointwise
open SpherePacking EuclideanSpace MeasureTheory Metric Bornology
variable {d : ℕ}
namespace PeriodicConstantApprox
theorem _root_.solution (hd : 0 < d) (S : SpherePacking d) (hSsep : S.separation = 1)
    {L : ℝ} (hL : 0 < L) {g : axisCellLattice (d := d) L hL}
    (F : Finset (EuclideanSpace ℝ (Fin d)))
    (hF_centers : ∀ x ∈ F, x ∈ S.centers)
    (hF_inner : ∀ x ∈ F, x ∈ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)) :
    ∃ P : PeriodicSpherePacking d,
      P.separation = 1 ∧
        P.upperPackingDensity =
          (F.card : ℝ≥0∞) *
              volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) /
            Real.toNNReal (ZLattice.covolume (axisCellLattice (d := d) L hL) volume) := by
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)) := axisCellLattice (d := d) L hL
  let D : Set (EuclideanSpace ℝ (Fin d)) := g +ᵥ axisAlignedCell (d := d) L
  let Fset : Set (EuclideanSpace ℝ (Fin d)) := (F : Set (EuclideanSpace ℝ (Fin d)))
  letI : DiscreteTopology Λ :=
    ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfFinite
      (axisCellBasis (d := d) L hL)
  letI : IsZLattice ℝ Λ :=
    instIsZLatticeRealSpan (axisCellBasis (d := d) L hL)
  let P : PeriodicSpherePacking d :=
    replicate_to_periodic_packing (d := d) S (Λ := Λ) D Fset
      (hD_unique_covers := PeriodicConstantApprox.translated_axis_cells_cover_uniquely (d := d) L hL g)
      (hF_centers := by
        assumption)
      (hF_ball := by
        intro x hx
        have hx' : x ∈ F := by simpa [Fset] using! hx
        have hxInner : x ∈ g +ᵥ insetAxisAlignedCell (d := d) L (S.separation / 2) := by
          simpa [hSsep] using! (hF_inner x hx')
        exact ball_subset_translated_cell_of_interior hL hxInner)
  have hPsep : P.separation = 1 := by simpa [P, hSsep]
  refine ⟨P, hPsep, ?_⟩
  have hD_bounded : IsBounded D := by
    simpa [D, Submodule.vadd_def, vadd_eq_add] using!
      (PeriodicConstant.axis_cell_is_bounded (d := d) L hL).vadd (g : EuclideanSpace ℝ (Fin d))
  have hD_unique : ∀ x, ∃! g0 : (axisCellLattice (d := d) L hL), g0 +ᵥ x ∈ D :=
    PeriodicConstantApprox.translated_axis_cells_cover_uniquely (d := d) L hL g
  have hF_sub : Fset ⊆ D := by
    intro x hx
    have hx' : x ∈ F := by simpa [Fset] using! hx
    rcases (hF_inner x hx') with ⟨a, ha, rfl⟩
    have ha' : a ∈ axisAlignedCell (d := d) L :=
      PeriodicConstant.inset_cell_subset_axis_cell (d := d) (L := L) (r := (2⁻¹ : ℝ))
        (by norm_num) ha
    exact ⟨a, ha', rfl⟩
  have hcenters_inter :
      P.centers ∩ D = Fset := by
    simpa [P, replicate_to_periodic_packing, Fset] using!
      (replicated_centers_intersection_of_subset (d := d) (Λ := axisCellLattice (d := d) L hL) (D := D)
        (F := Fset) hF_sub hD_unique)
  have hnumReps : P.centerOrbitCardinality = F.card := by
    have h' : (P.centerOrbitCardinality : ENat) = (F.card : ENat) := by
      simpa [hcenters_inter, Fset, Set.encard_coe_eq_coe_finsetCard] using!
        (P.encard_centers_in_fundamental_region (d := d) (D := D) hD_bounded hD_unique hd).symm
    exact_mod_cast h'
  simpa [hnumReps, hPsep] using! P.density_eq_numReps_mul_volume_ball_div_covolume (d := d) hd
end PeriodicConstantApprox

-- Prove2me | solution 1 for PeriodicSpherePacking.packing_density_zero_of_empty_centers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/84b38870-84bd-42d9-93dd-39bc1b385c4e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicSpherePacking_card_centers_in_fundamental_region

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open Filter
open scoped Pointwise
open scoped Topology
variable {d : ℕ}
namespace PeriodicSpherePacking
theorem _root_.solution (S : PeriodicSpherePacking d)
    (hd : 0 < d) [instEmpty : IsEmpty S.centers] : S.upperPackingDensity = 0 := by
  rw [S.density_eq_numReps_mul_volume_ball_div_covolume hd]
  let b := S.canonicalPackingLatticeBasis
  let D := fundamentalDomain (Basis.ofZLatticeBasis ℝ S.lattice b)
  have hD_isBounded : IsBounded D :=
    fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b)
  have hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D :=
    S.basis_region_translates_cover_uniquely b
  rw [← S.card_centers_in_fundamental_region D hD_isBounded hD_unique_covers hd]
  simp only [Set.toFinset_card, ENat.toENNReal_coe, ENNReal.div_eq_zero_iff, mul_eq_zero,
    Nat.cast_eq_zero, ENNReal.coe_ne_top, or_false]
  left
  letI := @Fintype.ofFinite _ <| finite_centers_in_bounded_region S D hD_isBounded hd
  haveI : IsEmpty (↥(S.centers ∩ D)) := ⟨fun x => instEmpty.false ⟨x.1, x.2.1⟩⟩
  simp
end PeriodicSpherePacking

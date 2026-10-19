-- Prove2me | solution 1 for SpherePacking.exists_periodic_unit_packing_above_density_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/cbbb6455-0f2b-4680-abcc-509d739f4c47

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstant_axis_cell_volume_formula
import Theorems.Thm_PeriodicConstantApprox_axis_cell_subset_enclosing_ball
import Theorems.Thm_PeriodicConstantApprox_negated_cover_index_mem_enlarged_ball
import Theorems.Thm_PeriodicConstantApprox_mem_translated_cell_iff_cover_index
import Theorems.Thm_PeriodicConstantApprox_lattice_count_mul_cell_volume_le_ball_volume
import Theorems.Thm_SpherePacking_frequently_local_density_exceeds_threshold
import Theorems.Thm_SpherePacking_finite_center_ball_intersection_set
import Theorems.Thm_PeriodicConstantApprox_boundary_count_mul_ball_volume_le_shell
import Theorems.Thm_PeriodicConstantApprox_axis_lattice_covolume_toNNReal
import Theorems.Thm_PeriodicConstantApprox_replicated_cell_packing_density_formula
import Theorems.Thm_PeriodicConstantApprox_axis_shell_relative_cell_volume_tends_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
open SpherePacking
open Filter
open scoped ENNReal BigOperators
variable {d : ℕ}
namespace SpherePacking
theorem _root_.solution (hd : 0 < d)
    (S : SpherePacking d) (hSsep : S.separation = 1) {b : ℝ≥0∞} (hb : b < S.upperPackingDensity) :
    ∃ P : PeriodicSpherePacking d, P.separation = 1 ∧ b < P.upperPackingDensity := by
  classical
  by_contra hnone
  push Not at hnone
  obtain ⟨c, hbc, hc⟩ := exists_between hb
  let cell : ℝ → ℝ≥0∞ := fun L =>
    volume (axisAlignedCell (d := d) L)
  let shell : ℝ → ℝ≥0∞ := fun L =>
    volume (((PeriodicConstantApprox.uniformShellShift d (-(1 / 2 : ℝ))) +ᵥ
      insetAxisAlignedCell (d := d) (L + 1) 0) \
      insetAxisAlignedCell (d := d) L 1)
  have hshell : Tendsto (fun L : ℝ => shell L / cell L) atTop (𝓝 0) := by
    simpa [shell, cell] using
      (PeriodicConstantApprox.axis_shell_relative_cell_volume_tends_zero (d := d))
  have hsmall : ∀ᶠ L : ℝ in atTop, b + shell L / cell L < c := by
    have hlim : Tendsto (fun L : ℝ => b + shell L / cell L) atTop (𝓝 b) := by
      simpa using tendsto_const_nhds.add hshell
    exact hlim.eventually (Iio_mem_nhds hbc)
  obtain ⟨L, hL, hsmallL⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and hsmall).exists
  have hcell_top : cell L ≠ ∞ := by
    simp [cell, PeriodicConstant.axis_cell_volume_formula]
  have hcell_zero : cell L ≠ 0 := by
    simp [cell, PeriodicConstant.axis_cell_volume_formula, hL]
  have hden :
      (↑(Real.toNNReal (ZLattice.covolume (axisCellLattice (d := d) L hL) volume)) : ℝ≥0∞) =
        cell L := by
    rw [PeriodicConstantApprox.axis_lattice_covolume_toNNReal (d := d) L hL]
    exact ENNReal.coe_toNNReal hcell_top
  obtain ⟨C, hC⟩ := PeriodicConstantApprox.axis_cell_subset_enclosing_ball (d := d) L hL
  let A : ℝ≥0∞ := b + shell L / cell L
  have hAc : A < c := hsmallL
  have hratio :
      Tendsto (fun R : ℝ => A *
        (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 + 2 * C))) /
          volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + 0)))) atTop (𝓝 A) := by
    simpa using
      (ENNReal.Tendsto.const_mul
        (volume_ball_add_div_volume_ball_add_tendsto_one
          (d := d) (C := 1 / 2 + 2 * C) (C' := 0) hd)
        (Or.inl one_ne_zero))
  have hratio_small : ∀ᶠ R : ℝ in atTop, A *
      (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 + 2 * C))) /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + 0))) < c :=
    hratio.eventually (Iio_mem_nhds hAc)
  obtain ⟨R, hR_density, hR_ratio⟩ :=
    ((S.frequently_local_density_exceeds_threshold hc).and_eventually hratio_small).exists
  let huSet := S.finite_center_ball_intersection_set (R + (1 / 2 : ℝ))
  let u : Finset (EuclideanSpace ℝ (Fin d)) := huSet.toFinset
  let htSet := PeriodicConstantApprox.lattice_points_in_ball_finite (d := d) L hL
    (R + (1 / 2 : ℝ) + C)
  let t : Finset (axisCellLattice (d := d) L hL) := htSet.toFinset
  let index (x : EuclideanSpace ℝ (Fin d)) : axisCellLattice (d := d) L hL :=
    -PeriodicConstantApprox.axisCellCoverIndex (d := d) L hL x
  have hindex : ∀ x ∈ u, index x ∈ t := by
    intro x hx
    have hxball : x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 : ℝ)) :=
      (huSet.mem_toFinset.mp (by simpa [u] using hx)).2
    apply htSet.mem_toFinset.mpr
    simpa [index, t] using
      (PeriodicConstantApprox.negated_cover_index_mem_enlarged_ball
        (d := d) L hL (C := C) (R := R + (1 / 2 : ℝ)) hC hxball)
  let piece (g : axisCellLattice (d := d) L hL) : Finset (EuclideanSpace ℝ (Fin d)) :=
    u.filter fun x => index x = g
  let inner (g : axisCellLattice (d := d) L hL) : Finset (EuclideanSpace ℝ (Fin d)) :=
    (piece g).filter fun x =>
      x ∈ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)
  let boundary (g : axisCellLattice (d := d) L hL) : Finset (EuclideanSpace ℝ (Fin d)) :=
    (piece g).filter fun x =>
      x ∉ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)
  let V : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ))
  have hpiece_center {g : axisCellLattice (d := d) L hL}
      {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ piece g) : x ∈ S.centers := by
    have hx' : x ∈ u.filter (fun y => index y = g) := by
      simpa only [piece] using hx
    have hxu : x ∈ u := (Finset.mem_filter.mp hx').1
    exact (huSet.mem_toFinset.mp (by simpa [u] using hxu)).1
  have hpiece_cell {g : axisCellLattice (d := d) L hL}
      {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ piece g) :
      x ∈ g +ᵥ axisAlignedCell (d := d) L := by
    have hx' : x ∈ u.filter (fun y => index y = g) := by
      simpa only [piece] using hx
    have hidx : index x = g := (Finset.mem_filter.mp hx').2
    apply (PeriodicConstantApprox.mem_translated_cell_iff_cover_index
      (d := d) L hL g x).2
    simpa [index] using hidx.symm
  have hinner_bound (g : axisCellLattice (d := d) L hL) :
      ((inner g).card : ℝ≥0∞) * V ≤ b * cell L := by
    obtain ⟨P, hPsep, hPdensity⟩ :=
      PeriodicConstantApprox.replicated_cell_packing_density_formula
        (d := d) hd S hSsep hL (inner g)
        (by
          intro x hx
          exact hpiece_center (Finset.mem_filter.mp (by simpa [inner] using hx)).1)
        (by
          intro x hx
          exact (Finset.mem_filter.mp (by simpa [inner] using hx)).2)
    have hPbound : P.upperPackingDensity ≤ b := hnone P hPsep
    rw [hPdensity, hden] at hPbound
    exact (ENNReal.div_le_iff hcell_zero hcell_top).mp (by simpa [V] using hPbound)
  have hboundary_bound (g : axisCellLattice (d := d) L hL) :
      ((boundary g).card : ℝ≥0∞) * V ≤ shell L := by
    apply PeriodicConstantApprox.boundary_count_mul_ball_volume_le_shell
      (d := d) S hL hSsep
    · intro x hx
      have hx' : x ∈ (piece g).filter (fun y =>
          y ∉ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)) := by
        simpa only [boundary] using hx
      exact hpiece_center (Finset.mem_filter.mp hx').1
    · intro x hx
      have hx' : x ∈ (piece g).filter (fun y =>
          y ∉ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)) := by
        simpa only [boundary] using hx
      have hx' := Finset.mem_filter.mp hx'
      exact ⟨hpiece_cell hx'.1, by simpa [one_div] using hx'.2⟩
  have hpiece_bound (g : axisCellLattice (d := d) L hL) :
      ((piece g).card : ℝ≥0∞) * V ≤ A * cell L := by
    have hcard : (inner g).card + (boundary g).card = (piece g).card := by
      simpa [inner, boundary] using
        (Finset.card_filter_add_card_filter_not
          (s := piece g)
          (fun x : EuclideanSpace ℝ (Fin d) =>
            x ∈ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)))
    have hcard' : ((piece g).card : ℝ≥0∞) =
        ((inner g).card : ℝ≥0∞) + (boundary g).card := by
      exact_mod_cast hcard.symm
    calc
      ((piece g).card : ℝ≥0∞) * V =
          ((inner g).card : ℝ≥0∞) * V +
            ((boundary g).card : ℝ≥0∞) * V := by
              rw [hcard', add_mul]
      _ ≤ b * cell L + shell L :=
        add_le_add (hinner_bound g) (hboundary_bound g)
      _ = A * cell L := by
        simp [A, add_mul, ENNReal.div_mul_cancel hcell_zero hcell_top]
  have hpartition : ∑ g ∈ t, (piece g).card = u.card := by
    simpa [piece, Finset.filter_eq_self.mpr hindex] using
      (Finset.sum_card_fiberwise_eq_card_filter u t index)
  have hsum_bound :
      (u.card : ℝ≥0∞) * V ≤ (t.card : ℝ≥0∞) * (A * cell L) := by
    have hcast : (u.card : ℝ≥0∞) =
        ∑ g ∈ t, ((piece g).card : ℝ≥0∞) := by
      exact_mod_cast hpartition.symm
    calc
      (u.card : ℝ≥0∞) * V =
          (∑ g ∈ t, ((piece g).card : ℝ≥0∞)) * V := by rw [hcast]
      _ = ∑ g ∈ t, ((piece g).card : ℝ≥0∞) * V := by
        simp_rw [Finset.sum_mul]
      _ ≤ ∑ _g ∈ t, A * cell L :=
        Finset.sum_le_sum fun g _ => hpiece_bound g
      _ = (t.card : ℝ≥0∞) * (A * cell L) := by
        simp [nsmul_eq_mul]
  have ht_volume : (t.card : ℝ≥0∞) * cell L ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin d))
        ((R + (1 / 2 : ℝ)) + 2 * C)) := by
    simpa [t, htSet, cell] using
      (PeriodicConstantApprox.lattice_count_mul_cell_volume_le_ball_volume
        (d := d) (hL := hL) (R := R + (1 / 2 : ℝ)) (C := C) hC)
  have hcenter_bound : (u.card : ℝ≥0∞) * V ≤
      A * volume (ball (0 : EuclideanSpace ℝ (Fin d))
        (R + (1 / 2 + 2 * C))) := by
    calc
      (u.card : ℝ≥0∞) * V ≤ (t.card : ℝ≥0∞) * (A * cell L) := hsum_bound
      _ = A * ((t.card : ℝ≥0∞) * cell L) := by ac_rfl
      _ ≤ A * volume (ball (0 : EuclideanSpace ℝ (Fin d))
            (R + (1 / 2 + 2 * C))) := by
          gcongr
          simpa [add_assoc] using ht_volume
  have hlocal_bound : S.densityInsideRadius R ≤
      (u.card : ℝ≥0∞) * V /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    have h := S.local_density_upper_bound hd R
    simp only [hSsep, one_div] at h
    have henc :
        (S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d))
          (R + (2⁻¹ : ℝ))).encard = (u.card : ENat) := by
      simpa [u, huSet, one_div] using huSet.encard_eq_coe_toFinset_card
    rw [henc] at h
    simpa [V] using h
  have hfinal : S.densityInsideRadius R ≤ A *
      (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 + 2 * C))) /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + 0))) := by
    calc
      S.densityInsideRadius R ≤
          (u.card : ℝ≥0∞) * V /
            volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := hlocal_bound
      _ ≤ (A * volume (ball (0 : EuclideanSpace ℝ (Fin d))
            (R + (1 / 2 + 2 * C)))) /
              volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
          gcongr
      _ = A *
          (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 + 2 * C))) /
            volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + 0))) := by
          simp [div_eq_mul_inv, mul_assoc]
  exact (not_lt_of_ge (le_of_lt (lt_of_le_of_lt hfinal hR_ratio))) hR_density
end SpherePacking

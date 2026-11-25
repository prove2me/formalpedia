-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_proof_775875bd000c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:35:35.899033+00:00
-- url     : https://prove2.me/submissions/94a0942a-f527-4df2-8d38-ecae0daa629b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_mem_of_map_mem_d2fb0cf9bb94
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_dvd_of_map_dvd_1e28fee41c49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_vanishes_cone_iff_7e7b75a722b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_vanishes_zero_iff_dvd_e8d9621446a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coeff_coordPoly_539797cde10d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_C_mul_map_9d8219af7fc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_mem_of_mem_map_75eab8a0118b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_sum_8ff9631ad41f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_incidenceIdeal_map_8d93a5362789
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_mem_zeroLocus_incidenceIdeal_a3506a649f6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_proof_14040d77a0cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_radical_map_eq_9ece7ec07417
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_sum_coordPoly_903079f12110
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_vanishes_incidence_iff_796d408552b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RadicalBaseChange_proof_fda9669ff964


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk conePts)
open ChowFormExtend (incidenceIdeal coordPoly coeff_coordPoly coordPoly_C_mul_map coordPoly_mem_of_mem_map
  mem_zeroLocus_incidenceIdeal vanishes_incidence_iff incidenceIdeal_map radical_map_eq coordSupport
  sum_coordPoly coordPoly_sum)
open GroundTheory.Heights₂.Heights.ObjectsChow.ComplexChowFormToChowForm
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow.ComplexChowFormToChowForm
theorem _root_.solution : ComplexChowFormToChowForm.Statement := by
  intro n e δ P g _ hg
  obtain ⟨-, hsq, hzero⟩ := hg
  set R := (incidenceIdeal (genericIdeal P) (e + 1)).radical with hR
  have hradC : (incidenceIdeal ((genericIdeal P).map (map (algebraMap ℚ ℂ))) (e + 1)).radical =
      R.map (map (algebraMap ℚ ℂ)) := by
    rw [incidenceIdeal_map, radical_map_eq RadicalBaseChange.proof]
  have hZ : ∀ v : Fin (e + 1) × Fin n → ℂ, eval v g = 0 ↔
      ∃ z ∈ conePts (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P), ∀ i, ∑ j, v (i, j) * z j = 0 :=
    fun v => hzero (fun i j => v (i, j))
  have hC : ∀ p : MvPolynomial (Fin (e + 1) × Fin n) ℂ,
      g ∣ p ↔ ∀ j, X (Sum.inr j) * rename Sum.inl p ∈ R.map (map (algebraMap ℚ ℂ)) := by
    intro p
    rw [← vanishes_zero_iff_dvd hsq, ← hradC, ← vanishes_cone_iff]
    exact forall_congr' fun v => by rw [hZ v]
  have hQ : ∀ h : MvPolynomial (Fin (e + 1) × Fin n) ℚ,
      (∀ u ∈ incidence (genericIdeal P) (e + 1), aeval u h = 0) ↔ g ∣ map (algebraMap ℚ ℂ) h := by
    intro h
    refine (vanishes_incidence_iff _ _ h).trans ?_
    rw [hC]
    refine forall_congr' fun j => ?_
    rw [show X (Sum.inr j) * rename Sum.inl (map (algebraMap ℚ ℂ) h) =
        map (algebraMap ℚ ℂ) (X (Sum.inr j) * rename Sum.inl h) by rw [map_mul, map_X, map_rename]]
    exact ⟨fun hm => Ideal.mem_map_of_mem _ hm, mem_of_map_mem R⟩
  have hg0 : g ≠ 0 := hsq.ne_zero
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hg0
  classical
  let b := Module.Basis.ofVectorSpace ℚ ℂ
  obtain ⟨c, hc⟩ : ∃ c, b.coord c (coeff m g) ≠ 0 := by
    by_contra! h
    have h0 : b.repr (coeff m g) = 0 := Finsupp.ext fun c => by rw [← Module.Basis.coord_apply]; exact h c
    exact hm (b.repr.map_eq_zero_iff.mp h0)
  have hcS : c ∈ coordSupport b g :=
    Finset.mem_biUnion.2 ⟨m, mem_support_iff.2 hm,
      Finsupp.mem_support_iff.2 (by rwa [← Module.Basis.coord_apply])⟩
  set h := coordPoly (b.coord c) g with hh_def
  have hh : g ∣ map (algebraMap ℚ ℂ) h := by
    refine (hQ h).mp ((vanishes_incidence_iff _ _ h).mpr fun j => ?_)
    have e' : X (Sum.inr j) * rename Sum.inl g = ∑ c' ∈ coordSupport b g,
        C (b c') * map (algebraMap ℚ ℂ) (X (Sum.inr j) * rename Sum.inl (coordPoly (b.coord c') g)) := by
      conv_lhs => rw [← sum_coordPoly b g]
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [map_mul, rename_C, map_mul, map_X, map_rename]
      ring
    have hmem := coordPoly_mem_of_mem_map b R (e' ▸ (hC g).mp dvd_rfl j) c
    rwa [coordPoly_sum, if_pos hcS] at hmem
  obtain ⟨q, hq⟩ := hh
  have hmh : coeff m (map (algebraMap ℚ ℂ) h) ≠ 0 := by
    rw [coeff_map, hh_def, coeff_coordPoly]
    exact (map_ne_zero _).mpr hc
  have hmh0 : map (algebraMap ℚ ℂ) h ≠ 0 := fun h0 => hmh (by rw [h0, coeff_zero])
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hmh0 hq
  have hsupp : (map (algebraMap ℚ ℂ) h).support ⊆ g.support := by
    intro m' hm'
    rw [mem_support_iff] at hm' ⊢
    intro h0
    rw [coeff_map, hh_def, coeff_coordPoly, h0, map_zero, map_zero] at hm'
    exact hm' rfl
  have hdeg : q.totalDegree = 0 := by
    have h1 := totalDegree_mul_of_isDomain hg0 hq0
    have h2 := totalDegree_le_of_support_subset hsupp
    rw [← hq] at h1
    omega
  rw [totalDegree_eq_zero_iff_eq_C] at hdeg
  set a := q.coeff 0
  have ha : a ≠ 0 := fun h0 => hq0 (by rw [hdeg, h0, C_0])
  have hgm : g = C a⁻¹ * map (algebraMap ℚ ℂ) h := by
    rw [hq, hdeg, mul_comm g, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul]
  have hu : IsUnit (C a⁻¹ : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero ha)).map C
  refine ⟨a⁻¹, inv_ne_zero ha, h, ?_, ?_⟩
  · rw [show Rat.castHom ℂ = algebraMap ℚ ℂ from Subsingleton.elim _ _]
    exact hgm
  · refine ⟨fun h0 => hmh0 (by rw [h0, map_zero]), fun h' => ?_⟩
    refine (hQ h').trans ?_
    rw [hgm, hu.mul_left_dvd]
    exact ⟨dvd_of_map_dvd, map_dvd _⟩
end GroundTheory.Heights₂.Heights.ObjectsChow.ComplexChowFormToChowForm

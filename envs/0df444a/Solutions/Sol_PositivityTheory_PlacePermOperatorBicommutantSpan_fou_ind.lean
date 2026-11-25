-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.fou_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:38:02.176731+00:00
-- url     : https://prove2.me/submissions/e2ed00d1-3c8d-426c-a335-f12b45358407

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_ind_of_mem
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_ind_of_not
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_ind_congr
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_ind_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}
variable (h : NADual V χ μ)
include h
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {L : AddSubgroup V} (hL : CO L) (a y : V) :
    fou χ μ (ind a L) y = ((μ L).toReal : ℂ) * χ a y * ind 0 (perpG h L) y := by
  have hh := h
  obtain ⟨_, _, _, _, _, _, -⟩ := hh
  have e1 : fou χ μ (ind a L) y = χ a y * ∫ x, ind 0 L x * χ x y ∂μ := by
    rw [fou, ← integral_add_right_eq_self _ a, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [chi_add h]
    rw [ind_congr (b := 0) (y := x) (L' := L) (by rw [add_sub_cancel_right, sub_zero])]
    ring
  rw [e1]
  by_cases hy : y ∈ perpG h L
  · rw [ind_of_mem (by simpa using hy)]
    have e2 : (fun x => ind 0 L x * χ x y) = Set.indicator (L : Set V) fun _ => (1 : ℂ) := by
      funext x
      by_cases hx : x ∈ L
      · rw [ind_of_mem (by simpa using hx), hy x hx, Set.indicator_of_mem (s := (L : Set V)) hx, one_mul]
      · rw [ind_of_not (by simpa using hx), Set.indicator_of_notMem (s := (L : Set V)) hx, zero_mul]
    rw [e2, integral_indicator_const _ hL.2.measurableSet]
    simp [Measure.real, mul_comm]
  · rw [ind_of_not (by simpa using hy), mul_zero]
    obtain ⟨l, hl, hne⟩ : ∃ l ∈ L, χ l y ≠ 1 := by
      by_contra h'
      push Not at h'
      exact hy h'
    have e2 : ∫ x, ind 0 L x * χ x y ∂μ = χ l y * ∫ x, ind 0 L x * χ x y ∂μ := by
      conv_lhs => rw [← integral_add_right_eq_self _ l]
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [chi_add h, ind_add x hl]
      ring
    have e3 : (1 - χ l y) * ∫ x, ind 0 L x * χ x y ∂μ = 0 := by rw [sub_mul, one_mul, ← e2, sub_self]
    rw [(mul_eq_zero.1 e3).resolve_left (sub_ne_zero.2 hne.symm), mul_zero]
end PositivityTheory.PlacePermOperatorBicommutantSpan

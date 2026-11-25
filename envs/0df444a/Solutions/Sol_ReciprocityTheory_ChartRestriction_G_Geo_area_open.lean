-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.area_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:17:45.50438+00:00
-- url     : https://prove2.me/submissions/b0a5f464-3811-4ac4-8cd8-286ef9bb68d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_piece_change
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_inj_cover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_integrable_tsum_of_summable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_tsum_finsum_disjointed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Set Filter Topology Function
variable {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {O : Set (Fin e → ℂ)} (hO : IsOpen O) {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    {h : (Fin e → ℂ) → ℝ} (hh : IntegrableOn h O) (hfin : ∀ᵐ y, (O ∩ Q ⁻¹' {y}).Finite) :
    Integrable (fibSum O Q h) ∧ ∫ u in O, h u = ∫ y, fibSum O Q h y := by
  obtain ⟨W, hWo, hWO, hWinj, hWU⟩ := exists_inj_cover hQ hO
  set D := disjointed W with hDdef
  have hDm : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed fun n => (hWo n).measurableSet
  have hDsub : ∀ n, D n ⊆ W n := disjointed_subset W
  have hDU : ⋃ n, D n = O := iUnion_disjointed.trans hWU
  have hDd : Pairwise (Disjoint on D) := disjoint_disjointed W
  have hDO : ∀ n, D n ⊆ O := fun n => (hDsub n).trans (hWO n)
  have hp : ∀ n, Integrable (fibSum (D n) Q h) ∧ ∫ y, fibSum (D n) Q h y = ∫ u in D n, h u ∧
      ∫ y, ‖fibSum (D n) Q h y‖ = ∫ u in D n, ‖h u‖ := fun n =>
    piece_change (hDm n) (fun u hu => (hQ u (hDO n hu)).1.differentiableAt)
      (fun u hu => (hQ u (hDO n hu)).2) ((hWinj n).mono (hDsub n)) (hh.mono_set (hDO n))
  have hhO : IntegrableOn h (⋃ n, D n) := by rw [hDU]; exact hh
  have hs1 := hasSum_integral_iUnion hDm hDd hhO
  have hs2 := hasSum_integral_iUnion hDm hDd hhO.norm
  have hn2 : ∀ n, ∫ y, ‖fibSum (D n) Q h y‖ = ∫ u in D n, ‖h u‖ := fun n => (hp n).2.2
  have hn1 : ∀ n, ∫ y, fibSum (D n) Q h y = ∫ u in D n, h u := fun n => (hp n).2.1
  have hsumm : Summable fun n => ∫ y, ‖fibSum (D n) Q h y‖ := by
    simp_rw [hn2]; exact hs2.summable
  have htsum : ∫ y, ∑' n, fibSum (D n) Q h y = ∑' n, ∫ y, fibSum (D n) Q h y :=
    (integral_tsum_of_summable_integral_norm (fun n => (hp n).1) hsumm).symm
  have hae : (fun y => ∑' n, fibSum (D n) Q h y) =ᵐ[volume] fibSum O Q h := by
    filter_upwards [hfin] with y hy
    simp only [fibSum]
    exact tsum_finsum_disjointed hDd hDU hy (fun u => h u / jacN Q u)
  refine ⟨(integrable_tsum_of_summable (fun n => (hp n).1) hsumm).congr hae, ?_⟩
  rw [← integral_congr_ae hae, htsum]
  simp_rw [hn1]
  rw [hs1.tsum_eq, hDU]
end ReciprocityTheory.ChartRestriction.G.Geo

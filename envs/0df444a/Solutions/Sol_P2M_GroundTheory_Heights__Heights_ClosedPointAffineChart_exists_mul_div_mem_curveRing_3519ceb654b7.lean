-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_exists_mul_div_mem_curveRing_3519ceb654b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:38.955166+00:00
-- url     : https://prove2.me/submissions/a671d2e3-c7b1-40e8-a3cf-99d0aa065844

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_mem_chart_of_mem_curveRing_93a3946b1876
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_mem_curveRing_of_forall_780a7c40c442
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_exists_mul_inv_mem_ad6467638384

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointAffineChart
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
namespace GroundTheory.Heights₂.Heights.ClosedPointAffineChart
theorem _root_.solution {m : Ideal (curveRing y)} (hm : m.IsMaximal) {e : ℕ} {g : K'}
    (hg0 : g ≠ 0) (hgL : g ∈ chartLat y 1 e)
    (hW : ∀ W : ValuationSubring K', (∀ b : curveRing y, (b : K') ∈ W) →
      (∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1) → ∀ u : T, y ⟨(), u⟩ ^ e / g ∈ W)
    {h : K'} (hh : ∀ t : T, y ⟨(), t⟩ ≠ 0 → h / y ⟨(), t⟩ ^ e ∈ chartRingZ y (fun _ => t)) :
    ∃ s : curveRing y, s ∉ m ∧ (s : K') * (h / g) ∈ curveRing y := by
  classical
  have := hm.isPrime
  have key : ∀ t : T, ∃ s : curveRing y, s ∉ m ∧
      (y ⟨(), t⟩ ≠ 0 → (s : K') * (h / g) ∈ chartRingZ y (fun _ => t)) := by
    intro t
    by_cases ht : y ⟨(), t⟩ = 0
    · exact ⟨1, fun h1 => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun h' => (h' ht).elim⟩
    · obtain ⟨s, hs, hsm⟩ := exists_mul_inv_mem y hg0 hgL hW t ht
      refine ⟨s, hs, fun _ => ?_⟩
      have e1 : (s : K') * (h / g) = h / y ⟨(), t⟩ ^ e * ((s : K') * (y ⟨(), t⟩ ^ e / g)) := by
        field_simp
      rw [e1]
      exact mul_mem (hh t ht) hsm
  choose S hSm hS using key
  refine ⟨∏ t, S t, fun hmem => ?_, ?_⟩
  · obtain ⟨t, -, ht⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hSm t ht
  · apply mem_curveRing_of_forall
    intro t ht
    have e1 : ((∏ u, S u : curveRing y) : K') * (h / g) =
        (∏ u ∈ Finset.univ.erase t, (S u : K')) * ((S t : K') * (h / g)) := by
      push_cast
      rw [← Finset.mul_prod_erase Finset.univ (fun u => (S u : K')) (Finset.mem_univ t)]
      ring
    rw [e1]
    exact mul_mem (prod_mem fun u _ => mem_chart_of_mem_curveRing y (S u).2 t ht) (hS t ht)
end GroundTheory.Heights₂.Heights.ClosedPointAffineChart

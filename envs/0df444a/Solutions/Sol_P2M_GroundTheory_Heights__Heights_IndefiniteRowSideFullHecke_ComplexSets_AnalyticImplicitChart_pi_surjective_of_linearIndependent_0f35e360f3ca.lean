-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticImplicitChart_pi_surjective_of_linearIndependent_0f35e360f3ca
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:08.492968+00:00
-- url     : https://prove2.me/submissions/7b40a87c-5756-44db-ab5d-0b6c9bd9cb43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticImplicitChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart
theorem _root_.solution {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype ι] {φ : ι → E →L[ℂ] ℂ} (hφ : LinearIndependent ℂ φ) :
    Function.Surjective (LinearMap.pi fun j => (φ j : E →ₗ[ℂ] ℂ)) := by
  classical
  rw [← LinearMap.dualMap_injective_iff, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have hfx : ∀ x : ι → ℂ, f x = ∑ j, x j * f (Pi.single j 1) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    ext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [hi]
  have h0 : ∑ j, f (Pi.single j 1) • φ j = 0 := by
    ext z
    have := LinearMap.congr_fun hf z
    simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at this
    rw [hfx] at this
    simpa [mul_comm] using this
  have hc := Fintype.linearIndependent_iff.1 hφ _ h0
  refine LinearMap.ext fun x => ?_
  rw [hfx x]
  simp [hc]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_segre_chartLift_cde5bc6f2110
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:42.586669+00:00
-- url     : https://prove2.me/submissions/5f7550dd-e593-4f67-a4b6-d88ec03f90dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StokesObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9

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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing mcPts segre PBlk)
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (z : (Σ k, ι k) → ℂ) (hz : segre z i = 1) :
    segre (chartLift σ i (fun a => segre z (σ a))) = segre z := by
  funext i'
  show ∏ k, chartLift σ i (fun a => segre z (σ a)) ⟨k, i' k⟩ = ∏ k, z ⟨k, i' k⟩
  simp only [chartLift_segre_apply σ i z hz, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have : ∏ k, z ⟨k, i k⟩ = 1 := hz
  rw [this, inv_one, mul_one]
end GroundTheory.Heights₂.Heights

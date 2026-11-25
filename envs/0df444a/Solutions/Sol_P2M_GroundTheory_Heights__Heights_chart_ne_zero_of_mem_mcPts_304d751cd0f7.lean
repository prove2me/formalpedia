-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chart_ne_zero_of_mem_mcPts_304d751cd0f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:45.257799+00:00
-- url     : https://prove2.me/submissions/92925916-c48c-4c91-a7d4-6b21689a8d7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegreeRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatioLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_homogForm_9c410c1834c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_int_relation_bf34191512a6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_homogForm_mem_orbitIdeal_fdc7dade412e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_homog_sum_zero_e8577340b774


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι]
variable [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ}
    (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x)) (k : ι) : z ⟨k, c k⟩ ≠ 0 := by
  intro h0
  obtain ⟨i, hi⟩ := hz.1 k
  obtain ⟨g, hg0, hg⟩ := exists_int_relation (flatCone x ⟨k, i⟩ / flatCone x ⟨k, c k⟩)
  have h := hz.2 _ (homogForm_mem_orbitIdeal x g ⟨k, i⟩ ⟨k, c k⟩ rfl (hc k) hg)
  rw [eval_homogForm, h0, homog_sum_zero] at h
  exact mul_ne_zero (Int.cast_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hg0))
    (pow_ne_zero _ hi) h
end GroundTheory.Heights₂.Heights

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitConjSum_chart_ne_zero_10cb68d2f03b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:33.414199+00:00
-- url     : https://prove2.me/submissions/c77c340c-1e9f-4e64-acac-5d12115a953b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitConjSumLemmas
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
open GroundTheory.Heights₂.Heights.OrbitConjSum
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.OrbitConjSum
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ}
    (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x)) (k : ι) : z ⟨k, c k⟩ ≠ 0 := by
  intro h0
  obtain ⟨i, hi⟩ := hz.1 k
  obtain ⟨g, hg0, hg⟩ := exists_int_relation (flatCone x ⟨k, i⟩ / flatCone x ⟨k, c k⟩)
  have := hz.2 _ (homogForm_mem_orbitIdeal x g ⟨k, i⟩ ⟨k, c k⟩ rfl (hc k) hg)
  rw [eval_homogForm, h0, homog_sum_zero] at this
  exact mul_ne_zero (Int.cast_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hg0))
    (pow_ne_zero _ hi) this
end GroundTheory.Heights₂.Heights.OrbitConjSum

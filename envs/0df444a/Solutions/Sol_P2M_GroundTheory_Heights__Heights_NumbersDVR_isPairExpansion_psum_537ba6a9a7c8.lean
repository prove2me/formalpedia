-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_psum_537ba6a9a7c8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:34.403807+00:00
-- url     : https://prove2.me/submissions/722f3314-3947-4200-8bb7-650ec4928af1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_psumExpansion_217a129f2629

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (N k : ℕ) :
    IsPairExpansion k (psum (Fin N) ℤ k) (psumExpansion N k) := by
  refine ⟨?_, isHomogeneous_psumExpansion N k⟩
  unfold psumExpansion
  simp only [psum, map_sum, map_pow, rename_X, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, (Commute.all _ _).geom_sum₂_mul]
end GroundTheory.Heights₂.Heights.NumbersDVR

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_omitProduct_mul_prod_geomSeries_ae43fa042c17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:53:10.87644+00:00
-- url     : https://prove2.me/submissions/d761e3d0-8630-4a5e-8552-f187995fe510

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_geomSeries_mul_1ea14b2a3afd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
theorem _root_.solution (j : σ) :
    omitProduct j * ∏ i : σ, geomSeries (X i : MvPolynomial σ ℚ) = geomSeries (X j) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ j), omitProduct, mul_left_comm,
    ← prod_mul_distrib, prod_eq_one, mul_one]
  intro i _
  rw [mul_comm, geomSeries_mul]
end GroundTheory.Heights₂.Heights.RestTerms.Schur

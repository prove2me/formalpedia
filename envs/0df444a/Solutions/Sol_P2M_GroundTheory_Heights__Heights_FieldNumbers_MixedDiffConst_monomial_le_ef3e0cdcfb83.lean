-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_monomial_le_ef3e0cdcfb83
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:52:54.209444+00:00
-- url     : https://prove2.me/submissions/70a4b28f-547b-4ec6-871d-13f9529a7434

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMixedDiffConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst
theorem _root_.solution (p : MvPolynomial K ℚ) {v : K →₀ ℕ} (hv : v ∈ p.support) :
    (monomial v (coeff v p)).totalDegree ≤ p.totalDegree :=
  (totalDegree_monomial_le _ _).trans (le_totalDegree hv)
end GroundTheory.Heights₂.Heights.FieldNumbers.MixedDiffConst

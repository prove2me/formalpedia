-- Prove2me | solution 1 for PositivityTheory.RgJS.NewtonIdentitiesAlt.newton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:01:05.120714+00:00
-- url     : https://prove2.me/submissions/c082a539-a576-439d-ac57-29677b90d586

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLowerBounds_NewtonIdentitiesLowDegree
import Theorems.Thm_PositivityTheory_RgJS_NewtonIdentitiesAlt_aeval_esymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.NewtonIdentitiesAlt
variable {A : Type} [Fintype A]
namespace PositivityTheory.RgJS.NewtonIdentitiesAlt
theorem _root_.solution [DecidableEq A] (a : A → ℂ) (j : ℕ) :
    (j : ℂ) * ev a j = (-1) ^ (j + 1) *
      ∑ x ∈ antidiagonal j with x.1 < j, (-1) ^ x.1 * ev a x.1 * ∑ i, a i ^ x.2 := by
  have h := congrArg (aeval a) (MvPolynomial.mul_esymm_eq_sum A ℂ j)
  simpa [map_mul, map_sum, aeval_esymm, MvPolynomial.psum] using h
end PositivityTheory.RgJS.NewtonIdentitiesAlt

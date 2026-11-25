-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf.eval_mul_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:41.2153+00:00
-- url     : https://prove2.me/submissions/d55f00c6-e878-491f-83f6-6ae69c27c35d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_aeval_mul_homog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
noncomputable section
open MvPolynomial
variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
theorem _root_.solution {K : Type*} [CommRing K] (q : ι → K) (t : K) {G : MvPolynomial ι K} {m : ℕ}
    (hG : G.IsHomogeneous m) : eval (fun i => q i * t) G = t ^ m * eval q G := by
  simpa using aeval_mul_homog (R := K) q t hG
end ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf

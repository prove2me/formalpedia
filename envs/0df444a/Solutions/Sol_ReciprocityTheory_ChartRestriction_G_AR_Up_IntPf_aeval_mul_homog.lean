-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf.aeval_mul_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:53.55467+00:00
-- url     : https://prove2.me/submissions/beba8958-056f-4c1f-9b9a-275a6c28bd3f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_cone_homog

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
theorem _root_.solution (q : ι → E) (t : E) {G : MvPolynomial ι R} {m : ℕ} (hG : G.IsHomogeneous m) :
    aeval (fun i => q i * t) G = t ^ m * aeval q G := by
  have h := congrArg ((Polynomial.aeval t : Polynomial E →ₐ[E] E).restrictScalars R)
    (cone_homog (R := R) q hG)
  rw [cone, MvPolynomial.comp_aeval_apply] at h
  simp only [AlgHom.restrictScalars_apply, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    Polynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply] at h
  rw [h, mul_comm]
end ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf

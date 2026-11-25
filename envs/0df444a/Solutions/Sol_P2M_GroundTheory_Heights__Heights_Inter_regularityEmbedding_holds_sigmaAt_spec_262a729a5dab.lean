-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_sigmaAt_spec_262a729a5dab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:24.862081+00:00
-- url     : https://prove2.me/submissions/565a5c0a-49a7-4f75-b37e-e7db41caa250

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
theorem _root_.solution {P : Ideal (MRing ι)} [P.IsPrime] {t : (Σ k, ι k) → ℂ} (ht : t ∈ mcPts P)
    (hne : ∀ (v : MRing ι) (a : K → ℕ), IsMultiHomog v a → v ∉ P → eval t (map (Int.castRingHom ℂ) v) ≠ 0)
    (x : funField P) {u v : MRing ι}
    (hx : (x : FractionRing (MRing ι ⧸ P)) * toFrac P v = toFrac P u) :
    sigmaAt P t ht hne x * eval t (map (Int.castRingHom ℂ) v) = eval t (map (Int.castRingHom ℂ) u) := by
  have key : (Subring.inclusion (funField_le P) x : locForms P) *
      algebraMap (MRing ι ⧸ P) (locForms P) (Ideal.Quotient.mk P v) =
      algebraMap (MRing ι ⧸ P) (locForms P) (Ideal.Quotient.mk P u) := Subtype.ext hx
  have := congrArg (IsLocalization.lift (M := formSub P) (S := locForms P) (isUnit_evalQ ht hne)) key
  rw [map_mul, IsLocalization.lift_eq, IsLocalization.lift_eq, evalQ_mk, evalQ_mk] at this
  exact this
end GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds

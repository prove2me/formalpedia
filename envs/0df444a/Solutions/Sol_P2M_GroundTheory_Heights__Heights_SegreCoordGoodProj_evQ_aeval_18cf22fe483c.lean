-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_aeval_18cf22fe483c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:15:53.007803+00:00
-- url     : https://prove2.me/submissions/527114b8-0c10-4baa-8301-67e7dbf69b45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreCoordGoodProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreCoordGoodProj

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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.SegreCoordGoodProj
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.SegreCoordGoodProj
theorem _root_.solution (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) {r : ℕ}
    (ℓ : Fin r → MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P) (F : MvPolynomial (Fin r) ℚ) :
    evQ P z hz (aeval ℓ F) = aeval (fun j => evQ P z hz (ℓ j)) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp]
end GroundTheory.Heights₂.Heights.SegreCoordGoodProj

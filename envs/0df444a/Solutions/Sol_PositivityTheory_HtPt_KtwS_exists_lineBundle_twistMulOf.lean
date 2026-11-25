-- Prove2me | solution 1 for PositivityTheory.HtPt.KtwS.exists_lineBundle_twistMulOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:26.15543+00:00
-- url     : https://prove2.me/submissions/6ce683b4-22e4-4111-900e-9f71848e42cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_ExistsLineBundleTwistMulOf
import Theorems.Thm_PositivityTheory_HtPt_KtwS_exists_lineBundle_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.HtPt PositivityTheory.HtPt.KtwS
open GroundTheory.Heights₂.Heights.Kleiman MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace PositivityTheory.HtPt.KtwS
theorem _root_.solution (hLT : LineTwist.Statement.{u, w}) (M : LineBundle S x) (a : ℕ)
    (c : ℤ) : ∃ Q : LineBundle S x, Q.toSubSystem = twistMul M.toSubSystem a c := by
  obtain ⟨P, hP⟩ := exists_lineBundle_pow hLT M a
  obtain ⟨Q, hQ⟩ := hLT S Ω N x P (twistBundle S x c)
  exact ⟨Q, by rw [hQ, hP]; rfl⟩
end PositivityTheory.HtPt.KtwS

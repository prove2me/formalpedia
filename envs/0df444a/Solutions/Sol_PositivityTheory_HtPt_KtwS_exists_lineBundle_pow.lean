-- Prove2me | solution 1 for PositivityTheory.HtPt.KtwS.exists_lineBundle_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:56:45.624293+00:00
-- url     : https://prove2.me/submissions/56b0c40e-70c3-4997-b392-286e632dcba5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_ExistsLineBundleTwistMulOf

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
theorem _root_.solution (hLT : LineTwist.Statement.{u, w}) (Q : LineBundle S x) (n : ℕ) :
    ∃ Q' : LineBundle S x, Q'.toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => exact ⟨twistBundle S x 0, rfl⟩
  | succ n ih =>
    obtain ⟨Q', hQ'⟩ := ih
    obtain ⟨Q'', hQ''⟩ := hLT S Ω N x Q' Q
    exact ⟨Q'', by rw [hQ'', hQ']; rfl⟩
end PositivityTheory.HtPt.KtwS

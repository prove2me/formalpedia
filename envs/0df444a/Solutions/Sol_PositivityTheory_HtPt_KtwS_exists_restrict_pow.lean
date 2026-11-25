-- Prove2me | solution 1 for PositivityTheory.HtPt.KtwS.exists_restrict_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:26:23.699149+00:00
-- url     : https://prove2.me/submissions/db461773-3229-4732-8137-2f01cf9262ab

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
variable {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
namespace PositivityTheory.HtPt.KtwS
theorem _root_.solution (hLT : LineTwist.Statement.{u, w}) (hRT : RestrictTwist.Statement.{u, w})
    (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (hle : primeOf (S := S) x ≤ primeOf (S := S) y)
    (M : LineBundle S x) (M' : LineBundle S y) (r : Ω → K')
    (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (n : ℕ) :
    ∃ (Q : LineBundle S x) (Q' : LineBundle S y) (r' : Ω → K'), Q.toSubSystem = M.toSubSystem.pow n ∧
      Q'.toSubSystem = M'.toSubSystem.pow n ∧ RestrictData Q.toSubSystem hxy Q'.toSubSystem r' := by
  induction n with
  | zero =>
    obtain ⟨r', hr'⟩ := hRT.1 S Ω N x K' y hxy hle 0
    exact ⟨twistBundle S x 0, twistBundle S y 0, r', rfl, rfl, hr'⟩
  | succ n ih =>
    obtain ⟨Q, Q', r', hQ, hQ', hr⟩ := ih
    obtain ⟨Qn, hQn⟩ := hLT S Ω N x Q M
    obtain ⟨Qn', hQn'⟩ := hLT S K' N y Q' M'
    obtain ⟨r'', hr''⟩ := hRT.2 S Ω N x K' y hxy Q M Q' M' r' r hr h
    refine ⟨Qn, Qn', r'', by rw [hQn, hQ]; rfl, by rw [hQn', hQ']; rfl, ?_⟩
    rw [hQn, hQn']
    exact hr''
end PositivityTheory.HtPt.KtwS

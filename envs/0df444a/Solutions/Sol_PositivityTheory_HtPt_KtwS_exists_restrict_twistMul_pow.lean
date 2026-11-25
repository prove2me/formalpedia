-- Prove2me | solution 1 for PositivityTheory.HtPt.KtwS.exists_restrict_twistMul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:39:58.885908+00:00
-- url     : https://prove2.me/submissions/afcfb484-d694-407f-afb7-6ed67006b08f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_ExistsLineBundleTwistMulOf
import Theorems.Thm_PositivityTheory_HtPt_KtwS_exists_restrict_pow

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
theorem _root_.solution (hLT : LineTwist.Statement.{u, w})
    (hRT : RestrictTwist.Statement.{u, w}) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (M : LineBundle S x) (M' : LineBundle S y)
    (r : Ω → K') (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (a : ℕ) (c : ℤ) (b : ℕ) :
    ∃ (Q : LineBundle S x) (Q' : LineBundle S y) (r' : Ω → K'),
      Q.toSubSystem = (twistMul M.toSubSystem a c).pow b ∧
      Q'.toSubSystem = (twistMul M'.toSubSystem a c).pow b ∧
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r' := by
  obtain ⟨P, P', rP, hP, hP', hrP⟩ := exists_restrict_pow hLT hRT hxy hle M M' r h a
  obtain ⟨rc, hrc⟩ := hRT.1 S Ω N x K' y hxy hle c
  obtain ⟨L, hL⟩ := hLT S Ω N x P (twistBundle S x c)
  obtain ⟨L', hL'⟩ := hLT S K' N y P' (twistBundle S y c)
  obtain ⟨rL, hrL⟩ := hRT.2 S Ω N x K' y hxy P (twistBundle S x c) P' (twistBundle S y c) rP rc hrP hrc
  obtain ⟨Q, Q', r', hQ, hQ', hr'⟩ := exists_restrict_pow hLT hRT hxy hle L L' rL
    (by rw [hL, hL']; exact hrL) b
  refine ⟨Q, Q', r', ?_, ?_, hr'⟩
  · rw [hQ, hL, hP]; rfl
  · rw [hQ', hL', hP']; rfl
end PositivityTheory.HtPt.KtwS

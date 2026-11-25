-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_position_nsmul_f2c745582da5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:33.998802+00:00
-- url     : https://prove2.me/submissions/db3a03e5-e8a5-461a-9b9c-76b17b7da3ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRankOfSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections
theorem _root_.solution {d : ℕ} {A : Type*} [AddCommGroup A] (f : (Fin d → A) → ℤ)
    (hf : ∀ (bs : Fin d → A) (j : Fin d) (x y : A),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y))
    (bs : Fin d → A) (j : Fin d) (m : ℕ) (y : A) :
    f (Function.update bs j (m • y)) = (m : ℤ) * f (Function.update bs j y) := by
  induction m with
  | zero =>
    have h0 := hf bs j 0 0
    simp only [add_zero] at h0
    simp only [zero_smul, Nat.cast_zero, zero_mul]
    linarith
  | succ m ih =>
    rw [succ_nsmul, hf, ih]
    push_cast
    ring
end GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections

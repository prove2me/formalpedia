-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_const_nsmul_a1ffba80053a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:34.373969+00:00
-- url     : https://prove2.me/submissions/8283428c-da7c-44d0-94d8-19290078cce8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRankOfSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RankOfSections_position_nsmul_f2c745582da5

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
    (n : ℕ) (x : A) :
    f (fun _ => n • x) = (n : ℤ) ^ d * f (fun _ => x) := by
  classical
  have key : ∀ s : Finset (Fin d),
      f (fun i => if i ∈ s then n • x else x) = (n : ℤ) ^ s.card * f (fun _ => x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      have e : (fun i => if i ∈ insert j s then n • x else x) =
          Function.update (fun i => if i ∈ s then n • x else x) j (n • x) := by
        funext i
        by_cases hi : i = j
        · subst hi
          simp
        · simp [hi]
      have e2 : Function.update (fun i => if i ∈ s then n • x else x) j x =
          (fun i => if i ∈ s then n • x else x) := by
        funext i
        by_cases hi : i = j
        · subst hi
          simp [hj]
        · simp [Function.update_of_ne hi]
      rw [e, position_nsmul f hf, e2, ih, Finset.card_insert_of_notMem hj, pow_succ]
      ring
  simpa using key Finset.univ
end GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections

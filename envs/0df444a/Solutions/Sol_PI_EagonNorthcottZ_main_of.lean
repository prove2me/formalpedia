-- Prove2me | solution 1 for PI.EagonNorthcottZ.main_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:16:13.7151+00:00
-- url     : https://prove2.me/submissions/c45a4365-04d8-4858-ac72-1536dd1a663c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_ExactSecondDegreeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_EagonNorthcottExactOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EagonNorthcottZ
open MvPolynomial PI.EagonNorthcott
namespace PI.EagonNorthcottZ
theorem _root_.solution (hA : Anti) (hS : Sq) (hL : KLin) (hG : GrLin) (hGX : GrX) (hGY : GrY) (hX : ExX) (hY : ExY) (hYz : ExYz) :
    Main := by
  intro D a
  induction a with
  | zero =>
    intro j ω hω hy _
    have h0 := hYz D j ω hω hy
    refine ⟨0, ⟨fun _ _ => rfl, fun J m hm => by simp at hm⟩, ?_, ?_⟩
    · have := (hL D ys (0 : W D) 0).1; simpa using this
    · have := (hL D xs (0 : W D) 0).1; rw [h0]; simpa using this
  | succ a ih =>
    intro j ω hω hy hx
    obtain ⟨θ, hθ, hθω⟩ := hY D a j ω hω hy
    have h1 : K ys (K xs θ) = 0 := by rw [hA D ys xs θ, hθω, hx, neg_zero]
    obtain ⟨η', hη', hη'y, hη'x⟩ := ih j (K xs θ) (hGX D a (j + 1) θ hθ) h1 (hS D xs θ)
    have h2 : K xs (θ - η') = 0 := by rw [(hL D xs θ η').1, hη'x, sub_self]
    obtain ⟨ζ, hζ, hζx⟩ := hX D a (j + 1) (θ - η') (hG D a (j + 2) θ η' hθ hη').1 h2
    refine ⟨-K ys ζ, (hG D (a + 1) (j + 2) _ _ (hGY D a (j + 2) ζ hζ) (hGY D a (j + 2) ζ hζ)).2, ?_, ?_⟩
    · rw [(hL D ys (K ys ζ) 0).2, hS D ys ζ, neg_zero]
    · rw [(hL D xs (K ys ζ) 0).2, hA D xs ys ζ, neg_neg, hζx, (hL D ys θ η').1, hθω, hη'y, sub_zero]
end PI.EagonNorthcottZ

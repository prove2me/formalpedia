-- Prove2me | solution 1 for RH.Transport.supremum_le_of_uniform_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:53.421202+00:00
-- url     : https://prove2.me/submissions/b4d0534e-5016-4e00-aef3-1be9ece24434

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_Transport_Continuation
import Theorems.Thm_RH_Transport_continuationBoundary_eq_sub_margin
import Theorems.Thm_RH_Transport_continuationMargin_pos
import Theorems.Thm_OAI_SevenEighths_Supremum_continuationMargin_pos
import Theorems.Thm_OAI_SevenEighths_Supremum_uniform_bound_below_supremum_false


set_option autoImplicit false
open RH RH.Transport
noncomputable section
open Filter Asymptotics MeasureTheory
open OAI.SevenEighths.Continuation
namespace RH.Transport
theorem _root_.solution (B : ℝ) (S : Set ℝ)
    (hne : S.Nonempty) (hbounded : BddAbove S)
    (hbound : B < sSup S → ∃ ω σ : ℝ,
      ω < sSup S - B ∧ 0 < σ ∧
      ∀ x ∈ S, x ≤ continuationBoundary B (sSup S) ω σ) :
    sSup S ≤ B := by
  by_contra hn
  obtain ⟨ω, σ, hω, hσ, hbound⟩ := hbound (lt_of_not_ge hn)
  apply OAI.SevenEighths.Supremum.uniform_bound_below_supremum_false hne hbounded
    (continuationMargin_pos hω hσ)
  intro x hx
  simpa only [continuationBoundary_eq_sub_margin] using hbound x hx
end RH.Transport

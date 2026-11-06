-- Prove2me | solution 1 for RH.Transport.common_signal_bound_at_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:02:07.705211+00:00
-- url     : https://prove2.me/submissions/3796b30c-a5ee-41c8-ba57-759dbc7366a9

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_Transport_Continuation
import Theorems.Thm_OAI_SevenEighths_Continuation_common_signal_bound


set_option autoImplicit false
open RH RH.Transport
noncomputable section
open Filter Asymptotics MeasureTheory
open OAI.SevenEighths.Continuation
namespace RH.Transport
theorem _root_.solution
    (J f : ℝ → ℂ) (B β ω σ c : ℝ)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (B + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ))) :
    f =O[atTop] (fun x : ℝ => x ^ (continuationBoundary B β ω σ + c)) := by
  have hexp : max (B + c + ω) (β + c - σ) =
      continuationBoundary B β ω σ + c := by
    unfold continuationBoundary
    rcases le_total (B + ω) (β - σ) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]
      linarith
    · rw [max_eq_left h, max_eq_left (by linarith)]
      linarith
  simpa only [hexp] using
    common_signal_bound J f (B + c + ω) (β + c - σ) hJ herror
end RH.Transport

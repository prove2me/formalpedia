-- Prove2me | solution 1 for SchwartzSpaceWiki.mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:34:53.294744+00:00
-- url     : https://prove2.me/submissions/f975b66e-96a7-45e4-9e51-a429b261718c

import Theorems.Thm_SchwartzSpaceWiki_mul_bounded_smooth_mem

open SchwartzSpaceWiki
open scoped ENNReal

theorem solution (n : ℕ) (f g : Rn n → ℂ) (hf : f ∈ schwartzSpace n)
    (hg : g ∈ schwartzSpace n) : f * g ∈ schwartzSpace n := by
  apply mul_bounded_smooth_mem n f g hf hg.1
  intro β
  refine ⟨(schwartzSeminorm 0 β g).toReal, fun x => ?_⟩
  have h : ‖iteratedPartialDeriv β g x‖ₑ ≤ schwartzSeminorm 0 β g := by
    simpa [monomial, schwartzSeminorm] using le_iSup (fun y : Rn n =>
      ‖(monomial (0 : MultiIndex n) y : ℂ) * iteratedPartialDeriv β g y‖ₑ) x
  exact_mod_cast ENNReal.toReal_mono (hg.2 0 β).ne h

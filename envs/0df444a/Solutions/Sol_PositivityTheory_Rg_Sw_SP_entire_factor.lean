-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.entire_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:22:29.646866+00:00
-- url     : https://prove2.me/submissions/1eae25d2-fcb8-4725-b87e-f3dd05c59c9b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_WROrdA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Function
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (f : ℂ → ℂ) (hf : Differentiable ℂ f) (r : ℕ)
    (h : ∀ j < r, iteratedDeriv j f 0 = 0) : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = z ^ r * g z := by
  have hdiff : ∀ k : ℕ, Differentiable ℂ ((swap dslope (0 : ℂ))^[k] f) := by
    intro k
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have := (Complex.differentiableOn_dslope (f := (swap dslope (0 : ℂ))^[k] f) (s := Set.univ) (c := 0)
        Filter.univ_mem).2 ih.differentiableOn
      simpa [swap, differentiableOn_univ] using this
  obtain ⟨p, hp⟩ := hf.analyticAt 0
  obtain ⟨R, hR⟩ := hp
  have hcoeff : ∀ k < r, p.coeff k = 0 := by
    intro k hk
    have h1 := hR.factorial_smul (y := (1 : ℂ)) k
    have h2 : iteratedDeriv k f 0 = iteratedFDeriv ℂ k f 0 (fun _ => 1) := by
      rw [iteratedDeriv_eq_iteratedFDeriv]
    rw [← h2, h k hk] at h1
    have h3 : p.coeff k = p k (fun _ => 1) := rfl
    rw [h3]
    rw [nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h4 | h4
    · exact absurd h4 (by exact_mod_cast Nat.factorial_ne_zero k)
    · exact h4
  have hzero : ∀ k < r, (swap dslope (0 : ℂ))^[k] f 0 = 0 := by
    intro k hk
    have := (hR.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope k).coeff_zero 1
    rw [← this, ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope, zero_add]
    exact hcoeff k hk
  refine ⟨(swap dslope (0 : ℂ))^[r] f, hdiff r, fun z => ?_⟩
  have := pow_sub_smul_iterate_dslope_of_zero r hzero z
  simpa [smul_eq_mul] using this.symm
end PositivityTheory.Rg.Sw.SP

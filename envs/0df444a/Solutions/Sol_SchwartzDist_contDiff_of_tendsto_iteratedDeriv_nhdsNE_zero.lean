-- Prove2me | solution 1 for SchwartzDist.contDiff_of_tendsto_iteratedDeriv_nhdsNE_zero
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T18:47:24.221409+00:00
-- url     : https://prove2.me/submissions/4772411c-fba5-420b-a378-0f1c71e660a4

import Mathlib

open Topology Filter
open scoped ContDiff

set_option autoImplicit false

theorem solution
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F)
    (hf : ContDiffOn ℝ ∞ f {0}ᶜ) (h0 : f 0 = 0)
    (hlim : ∀ k : ℕ, Tendsto (iteratedDeriv k f) (𝓝[≠] 0) (𝓝 0)) :
    ContDiff ℝ ∞ f ∧ ∀ k : ℕ, iteratedDeriv k f 0 = 0 := by
  have hopen : IsOpen ({0}ᶜ : Set ℝ) := isOpen_compl_singleton
  -- away from `0`, each iterated derivative has the next one as derivative
  have hdiff : ∀ k : ℕ, ∀ y : ℝ, y ≠ 0 →
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f y) y := by
    intro k y hy
    have hk : ((k : ℕ) : WithTop ℕ∞) < ∞ := by
      exact_mod_cast ENat.natCast_lt_top k
    have h1 : DifferentiableOn ℝ (iteratedDerivWithin k f {0}ᶜ) {0}ᶜ :=
      hf.differentiableOn_iteratedDerivWithin hk hopen.uniqueDiffOn
    have hy' : y ∈ ({0}ᶜ : Set ℝ) := hy
    have h2 : DifferentiableAt ℝ (iteratedDeriv k f) y := by
      have := (h1 y hy').differentiableAt (hopen.mem_nhds hy')
      apply this.congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds hy'] with z hz
      exact (iteratedDerivWithin_of_isOpen hopen hz).symm
    rw [iteratedDeriv_succ]
    exact h2.hasDerivAt
  -- continuity at `0` from the limit and the value at `0`
  have hcont : ∀ k : ℕ, iteratedDeriv k f 0 = 0 → ContinuousAt (iteratedDeriv k f) 0 := by
    intro k hk
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hk]
    exact hlim k
  -- all iterated derivatives vanish at `0`
  have hz : ∀ k : ℕ, iteratedDeriv k f 0 = 0 := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      set g : ℝ → F := Function.update (iteratedDeriv (k + 1) f) 0 0 with hg
      have hgne : ∀ y, y ≠ 0 → g y = iteratedDeriv (k + 1) f y := by
        intro y hy
        simp [hg, Function.update_of_ne hy]
      have hg0 : g 0 = 0 := by simp [hg]
      have hgc : ContinuousAt g 0 := by
        rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hg0]
        apply (hlim (k + 1)).congr'
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (hgne y hy).symm
      have hD : HasDerivAt (iteratedDeriv k f) (g 0) 0 := by
        apply hasDerivAt_of_hasDerivAt_of_ne _ (hcont k ih) hgc
        intro y hy
        rw [hgne y hy]
        exact hdiff k y hy
      rw [iteratedDeriv_succ, hD.deriv, hg0]
  refine ⟨?_, hz⟩
  have hD : ∀ k : ℕ, Differentiable ℝ (iteratedDeriv k f) := by
    intro k y
    exact (hasDerivAt_of_hasDerivAt_of_ne' (hdiff k) (hcont k (hz k))
      (hcont (k + 1) (hz (k + 1))) y).differentiableAt
  exact contDiff_of_differentiable_iteratedDeriv (n := ⊤) (fun m _ => hD m)

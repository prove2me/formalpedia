-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.gTilde_inner_adjoint_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T06:13:28.181434+00:00
-- url     : https://prove2.me/submissions/194a6395-8d40-44e5-8215-f1000073a2bd

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod
import Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_B_comp_A

open ShorNonsmooth.SpaceDilation

/-- Step 0 of Theorem 3.3: `⟨g̃_k, A_k v⟩ = ⟨g(x_k), v⟩`. -/
theorem solution {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (hδ : 0 < δ)
    (hα : ∀ k : ℕ, 1 ≤ k → 1 + δ ≤ α k)
    (k : ℕ) (hstop : ∀ j : ℕ, j < k → g (sdg g h α x₀ B₀ j).x ≠ 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (gTilde g h α x₀ B₀ k) ((sdg g h α x₀ B₀ k).A v)
      = inner ℝ (g (sdg g h α x₀ B₀ k).x) v := by
  classical
  -- Repair of candidate 7129, which named the right lemma and got one step further than
  -- any previous attempt on this target.
  --
  -- 7129 used `LinearMap.comp_apply`, and it worked: `hone` came back as
  --
  --   hone : ↑B (↑A v) = v
  --   goal :        B (A v) = v
  --
  -- The remaining difference is only the *coercion notation* `↑B` versus the application
  -- `B`. There is no lemma to bridge them — the pinned index confirms that
  -- `ContinuousLinearMap.coe_apply` and `ContinuousLinearMap.coe_toLinearMap` are both
  -- absent — because `↑B` and `B` are the same function definitionally. `simp only` did
  -- not close it because the simplification set contained only `LinearMap.comp_apply`,
  -- which no longer had anything to do, so the coercion stayed in `hone`'s type and
  -- `simpa`'s normalisation refused the definitional step.
  --
  -- This repair therefore rewrites the composition in `hone` with `LinearMap.comp_apply`
  -- and then closes the goal with `exact`, letting definitional unfolding handle the
  -- coercion instead of asking `simp` to.
  rw [gTilde, ContinuousLinearMap.adjoint_inner_left]
  have hpt := sdg_B_comp_A hn g h α x₀ B₀ δ hδ hα k hstop
  have hBA : (sdg g h α x₀ B₀ k).B ((sdg g h α x₀ B₀ k).A v) = v := by
    have hone := LinearMap.congr_fun hpt v
    rw [LinearMap.comp_apply] at hone
    exact hone
  rw [hBA]

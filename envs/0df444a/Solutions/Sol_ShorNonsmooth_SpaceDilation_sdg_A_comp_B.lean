-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.sdg_A_comp_B
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T17:37:55.986987+00:00
-- url     : https://prove2.me/submissions/34422a23-3196-49ca-8093-0f91ac8a1522

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod
import Theorems.Thm_ShorNonsmooth_SpaceDilation_dilation_compose_inv
import Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_gTilde_ne_zero

open ShorNonsmooth.SpaceDilation

theorem solution {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (δ : ℝ) (hδ : 0 < δ)
    (hα : ∀ k : ℕ, 1 ≤ k → 1 + δ ≤ α k)
    (k : ℕ) (hstop : ∀ j : ℕ, j < k → g (sdg g h α x₀ B₀ j).x ≠ 0) :
    (sdg g h α x₀ B₀ k).A.toLinearMap.comp
      ((sdg g h α x₀ B₀ k).B.toLinearMap) = LinearMap.id := by
  classical
  have key : ∀ (j : ℕ), j ≤ k → ∀ v : EuclideanSpace ℝ (Fin n),
      (sdg g h α x₀ B₀ j).A ((sdg g h α x₀ B₀ j).B v) = v := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        intro hj v
        rcases j with _ | jm
        · have hA0 : (sdg g h α x₀ B₀ 0).A = (B₀.symm : EuclideanSpace ℝ (Fin n) →L[ℝ]
              EuclideanSpace ℝ (Fin n)) := by simp [sdg]
          have hB0 : (sdg g h α x₀ B₀ 0).B = (B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ]
              EuclideanSpace ℝ (Fin n)) := by simp [sdg]
          rw [hA0, hB0]
          exact B₀.symm_apply_apply v
        have hgj : g (sdg g h α x₀ B₀ jm).x ≠ 0 := hstop jm (by omega)
        set a : ℝ := α (jm + 1) with ha
        set gt : EuclideanSpace ℝ (Fin n) :=
          ContinuousLinearMap.adjoint (sdg g h α x₀ B₀ jm).B
            (g (sdg g h α x₀ B₀ jm).x) with hgt
        set ξ : EuclideanSpace ℝ (Fin n) := ‖gt‖⁻¹ • gt with hξ
        -- `a = α (jm+1) >= 1 + δ > 1`, so `a ≠ 0`.  `linarith` reads `ha` and `hδ`
        -- directly, so no rewrite is needed.
        have ha0 : a ≠ 0 := by
          have h1 := hα (jm + 1) (by omega)
          linarith
        have hgn0 : gt ≠ 0 := by
          have hgj' : ∀ i : ℕ, i ≤ jm → g (sdg g h α x₀ B₀ i).x ≠ 0 := by
            intro i hi
            exact hstop i (by omega)
          have := sdg_gTilde_ne_zero hn g h α x₀ B₀ δ hδ hα jm hgj'
          simpa [gt, gTilde] using this
        -- `‖ξ‖ = 1`.  `norm_inv` is `‖x⁻¹‖ = ‖x‖⁻¹`, which turns `‖‖gt‖⁻¹‖` into
        -- `‖‖gt‖‖⁻¹`.  The remaining goal is exactly `x⁻¹ * x = 1`, so `inv_mul_cancel₀`
        -- (not `mul_inv_cancel₀`, which proves `x * x⁻¹ = 1`) closes it.
        -- `norm_inv : ‖x⁻¹‖ = ‖x‖⁻¹` turns `‖‖gt‖⁻¹‖` into `‖‖gt‖‖⁻¹`; the double
        -- norm is removed by `Real.norm_eq_abs` + `abs_of_pos (norm_nonneg _)`, which
        -- supplies the needed *equation* `‖‖gt‖‖ = ‖gt‖`.  (`norm_nonneg` by itself is a
        -- proof of `0 ≤ ‖gt‖`, so it cannot be a `rw` argument.)
        have hdouble : ‖‖gt‖‖ = ‖gt‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        have hξnorm : ‖ξ‖ = 1 := by
          rw [hξ, norm_smul, norm_inv, hdouble]
          exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hgn0)
        have hsucc : sdg g h α x₀ B₀ (jm + 1)
            = sdgStep g h α jm (sdg g h α x₀ B₀ jm) := by simp [sdg]
        have hstep : sdgStep g h α jm (sdg g h α x₀ B₀ jm)
            = { x := (sdg g h α x₀ B₀ jm).x - h (jm + 1) (sdg g h α x₀ B₀ jm).x gt •
                    (sdg g h α x₀ B₀ jm).B ξ,
                B := (sdg g h α x₀ B₀ jm).B ∘SL dilation (1 / a) ξ,
                A := dilation a ξ ∘SL (sdg g h α x₀ B₀ jm).A } := by
          simp [sdgStep, hgj, ha, hgt, hξ]
        rw [hsucc, hstep]
        simp only
        -- `simp only` leaves `dilation a ξ (A_{jm} ((B_{jm} ∘SL dilation (1/a) ξ) v)) = v`.
        -- `∘SL` is a coercion, so the *B* application is still hidden and the induction
        -- hypothesis (stated on applied maps) has no match.  `comp_apply` unfolds every
        -- `∘L` coercion, so a bare `simp only [ContinuousLinearMap.comp_apply]` exposes
        -- both intermediate vectors at once.
        simp only [ContinuousLinearMap.comp_apply]
        rw [ih jm (by omega) (by omega) (dilation (1 / a) ξ v)]
        exact congrFun (dilation_compose_inv a ha0 ξ hξnorm) v
  -- `∘L` is the composition of `ContinuousLinearMap`s, so it must be extensionalised
  -- with `ContinuousLinearMap.ext`; `funext` would instead produce a function equality
  -- `↑(A ∘L B) = ↑id`, which does not unify with the `∘SL`-shaped goal.
  have hk : (sdg g h α x₀ B₀ k).A ∘L (sdg g h α x₀ B₀ k).B
      = (ContinuousLinearMap.id ℝ _) := by
    apply ContinuousLinearMap.ext
    intro v
    exact key k (Nat.le_refl k) v
  -- `↑(A ∘L B) = ↑A ∘ₗ ↑B` is `ContinuousLinearMap.toLinearMap_comp`, so rewriting with
  -- it turns the target into the `∘L` statement `hk`.  A bare `ext` could not do this: on
  -- an `∘L` equality it tries to extensionalise into a *function* equality and fails to
  -- unify with the goal.
  -- Unfold *everything* definitionally instead of rewriting, then close pointwise.
  -- Candidates 6945/6946/6947 cleared the `toLinearMap_comp` direction fault and each then
  -- failed on the *identity* side: `rw` cannot match `ContinuousLinearMap.id ℝ E` against a
  -- goal whose RHS is `LinearMap.id` (6945), and `simp only` does not reduce
  -- `↑(ContinuousLinearMap.id)` either (6946) — there is no `toLinearMap_id` here.
  --
  -- `simp only [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.comp_apply,
  -- LinearMap.id_apply]` unfolds the composition and both identity sides by *definitional*
  -- reduction, leaving `A (B v) = v`, which is exactly `key`.  Unlike `rfl` on the whole
  -- goal (which cannot cross the `↑`-coercion), this leaves each side a plain application.
  refine LinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.comp_apply,
    LinearMap.id_apply]
  exact key k (Nat.le_refl k) v

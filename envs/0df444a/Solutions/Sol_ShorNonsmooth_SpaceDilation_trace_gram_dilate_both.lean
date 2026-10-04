-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.trace_gram_dilate_both
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T09:08:26.393709+00:00
-- url     : https://prove2.me/submissions/6d7e553a-0ff6-4546-b8fa-7771c83dd35d

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

/-!
# Shor (1985), p. 55: `tr(R (A A) R) = tr(A A) + (a^2 - 1) * ‖A ξ‖^2`

The corrected replacement for the published (and false) `trace_mul_dilation`, which
dilated on only one side; exact rational counterexamples to that statement are recorded in
`.prove2me/DEFECT-notes/2026-10-04-trace-mul-dilation-false.md`.

Let `S v = ⟪ξ, v⟫ • ξ`, the orthogonal projection onto `span ξ`. Then

* `dilation a ξ = id + (a - 1) S`, directly from the authoritative definition;
* `S ∘ S = S` when `‖ξ‖ = 1`, because `⟪ξ, ⟪ξ,w⟫ • ξ⟫ = ⟪ξ,w⟫ ⋅ ‖ξ‖^2 = ⟪ξ,w⟫`;
* hence `R^2 = id + (a^2 - 1) S`, since `2(a-1) + (a-1)^2 = a^2 - 1`.

By cyclicity of the trace, `tr(R (A A) R) = tr((A A) R^2)`, so the excess over
`tr(A A)` is `(a^2 - 1) tr((A A) S)`. For self-adjoint `A`,
`tr((A A) S) = ⟪ξ, A (A ξ)⟫ = ⟨A ξ, A ξ⟩ = ‖A ξ‖^2` by `adjoint_inner_left`.

Every algebraic step above is checked in exact rational arithmetic by
`/tmp/p2m/tgdb_check.py`.
-/

open ShorNonsmooth.SpaceDilation
open ContinuousLinearMap

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

/-- The rank-one projection `S w = ⟪ξ, w⟫ • ξ` is idempotent when `‖ξ‖ = 1`. -/
theorem projection_idem {n : ℕ} (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1)
    (w : EuclideanSpace ℝ (Fin n)) :
    (innerSL ℝ ξ).smulRight ξ ((innerSL ℝ ξ).smulRight ξ w)
      = (innerSL ℝ ξ).smulRight ξ w := by
  have hxi : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq, hξ]
    norm_num
  simp only [smulRight_apply, innerSL_apply_apply]
  -- `⟪ξ, ⟪ξ,w⟫ • ξ⟫ • ξ = ⟪ξ,w⟫ • ξ`, since `⟪ξ, ⟪ξ,w⟫ • ξ⟫ = ⟪ξ,w⟫ * ⟪ξ,ξ⟫`.
  rw [inner_smul_right, hxi, mul_one]

/-- `tr(P ∘ₗ S) = ⟪ξ, P ξ⟫`: the trace of a rank-one map is its value at the generator,
by `LinearMap.trace_smulRight`. -/
theorem trace_comp_projection {n : ℕ} (ξ : EuclideanSpace ℝ (Fin n))
    (P : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (P ∘ₗ (innerₛₗ ℝ ξ).smulRight ξ)
      = inner ℝ ξ (P ξ) := by
  have hdecomp : P ∘ₗ (innerₛₗ ℝ ξ).smulRight ξ
      = (innerₛₗ ℝ ξ).smulRight (P ξ) := by
    apply LinearMap.ext
    intro w
    simp only [LinearMap.smulRight_apply, LinearMap.comp_apply, map_smul]
  rw [hdecomp, LinearMap.trace_smulRight]
  rfl

theorem solution {n : ℕ} (a : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : A.adjoint = A) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
          ((dilation a ξ).toLinearMap ∘ₗ ((A.toLinearMap ∘ₗ A.toLinearMap) ∘ₗ
            (dilation a ξ).toLinearMap))
      = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (A.toLinearMap.comp A.toLinearMap)
        + (a ^ 2 - 1) * ‖A ξ‖ ^ 2 := by
  classical
  -- Notation for the two linear maps that recur throughout.
  set S : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := innerₛₗ ℝ ξ |>.smulRight ξ with hS
  set R : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (dilation a ξ).toLinearMap
  set P : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    A.toLinearMap ∘ₗ A.toLinearMap
  -- `R = id + (a - 1) • S` and `S ∘ₗ S = S`, so `R ∘ₗ R = id + (a^2 - 1) • S`.
  have hR : R = LinearMap.id + (a - 1) • S := by
    show ((dilation a ξ).toLinearMap) = LinearMap.id + (a - 1) • S
    simp only [R, dilation, ContinuousLinearMap.toLinearMap_add,
      ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_sub,
      smul_smul]
    -- Bridge the `ContinuousLinearMap.smulRight` form produced by unfolding `dilation`
    -- to the `LinearMap.smulRight` form in `S`; `(innerSL ℝ ξ).toLinearMap = innerₛₗ ℝ ξ`
    -- holds by `rfl`.
    rw [show ((innerSL ℝ ξ).smulRight ξ).toLinearMap
      = (innerₛₗ ℝ ξ).smulRight ξ by rfl, ← hS]
    -- `dilation` also unfolds a `ContinuousLinearMap.id`, whose `toLinearMap` is a
    -- different atom from `LinearMap.id` until bridged here.
    have hid : (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).toLinearMap
        = LinearMap.id := by
      apply LinearMap.ext
      intro x
      rfl
    rw [hid]
    module
  have hSS : S ∘ₗ S = S := by
    apply LinearMap.ext
    intro w
    exact projection_idem ξ hξ w
  have hR2 : R ∘ₗ R = LinearMap.id + (a ^ 2 - 1) • S := by
    rw [hR]
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.smul_comp, LinearMap.comp_smul,
      smul_smul, LinearMap.id_comp, LinearMap.comp_id, LinearMap.zero_comp,
      smul_zero, add_zero, zero_add, hSS]
    module
  -- Cyclicity, applied as `trace_comp_comm'` with `f = R`, `g = R ∘ₗ P`:
  -- `tr((R ∘ₗ P) ∘ₗ R) = tr(R ∘ₗ (R ∘ₗ P)) = tr(R^2 ∘ₗ P)`.
  have hcyc : LinearMap.trace ℝ _ ((R ∘ₗ P) ∘ₗ R)
      = LinearMap.trace ℝ _ (R ∘ₗ (R ∘ₗ P)) :=
    LinearMap.trace_comp_comm' R (R ∘ₗ P)
  -- `R ∘ₗ (R ∘ₗ P)` is `(R ∘ₗ R) ∘ₗ P` definitionally (`comp_assoc` is `rfl`),
  -- so a `show` reassoc lets `hR2` apply without fragile explicit assoc args.
  have hcyc2 : LinearMap.trace ℝ _ ((R ∘ₗ P) ∘ₗ R)
      = LinearMap.trace ℝ _ ((LinearMap.id + (a ^ 2 - 1) • S) ∘ₗ P) := by
    have e2 : R ∘ₗ (R ∘ₗ P) = (LinearMap.id + (a ^ 2 - 1) • S) ∘ₗ P := by
      show (R ∘ₗ R) ∘ₗ P = (LinearMap.id + (a ^ 2 - 1) • S) ∘ₗ P
      rw [hR2]
    rw [hcyc, e2]
  have hcyc3 : LinearMap.trace ℝ _ ((R ∘ₗ P) ∘ₗ R)
      = LinearMap.trace ℝ _ P + (a ^ 2 - 1) * LinearMap.trace ℝ _ (S ∘ₗ P) := by
    rw [hcyc2, LinearMap.add_comp, LinearMap.id_comp, map_add, LinearMap.smul_comp,
      map_smul, smul_eq_mul]
  -- `tr((A A) ∘ₗ S) = ⟪ξ, A (A ξ)⟫ = ‖A ξ‖^2` for self-adjoint `A`.
  have htr : LinearMap.trace ℝ _ (P ∘ₗ S)
      = ‖A ξ‖ ^ 2 := by
    have h1 := trace_comp_projection ξ P
    rw [h1]
    -- `⟪ξ, (A ∘ₗ A) ξ⟫ = ⟪A ξ, A ξ⟫` because `A.adjoint = A`.
    have hadj : ∀ x y : EuclideanSpace ℝ (Fin n),
        inner ℝ (A x) y = inner ℝ x (A y) := by
      intro x y
      rw [← ContinuousLinearMap.adjoint_inner_right]
      simp [hA]
    show inner ℝ ξ (A (A ξ)) = ‖A ξ‖ ^ 2
    rw [← hadj ξ (A ξ), real_inner_self_eq_norm_sq]
  -- `tr(S ∘ₗ P) = tr(P ∘ₗ S) = ‖A ξ‖^2` by cyclicity and `htr`.
  have hSP : LinearMap.trace ℝ _ (S ∘ₗ P) = ‖A ξ‖ ^ 2 := by
    rw [← LinearMap.trace_comp_comm' S P]
    exact htr
  -- The goal's left-hand side is right-nested `R ∘ₗ (P ∘ₗ R)`; `change` to the
  -- left-nested form (definitionally equal, `comp_assoc` is `rfl`) and close.
  change LinearMap.trace ℝ _
      ((R ∘ₗ P) ∘ₗ R) = LinearMap.trace ℝ _ P + (a ^ 2 - 1) * ‖A ξ‖ ^ 2
  rw [hcyc3, hSP]

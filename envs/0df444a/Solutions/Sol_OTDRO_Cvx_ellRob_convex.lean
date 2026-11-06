-- Prove2me | solution 1 for OTDRO.Cvx.ellRob_convex
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:21:03.211693+00:00
-- url     : https://prove2.me/submissions/3d8e7f35-c113-43ec-a336-03e07003f50b

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting
import Theorems.Thm_OTDRO_Cvx_sup_transport_eq_ellRob

open Matrix

theorem solution {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (hPD : ∀ x, (A x).PosDef)
    (hlsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      OTDRO.Dual.mahalCost A p.1 p.2))
    (ℓ : ℝ → ℝ) (hℓ : ConvexOn ℝ Set.univ ℓ) (δ : ℝ) (hδ : 0 < δ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B) :
    ∀ x : EuclideanSpace ℝ (Fin d),
      ∀ β₁ ∈ B, ∀ β₂ ∈ B, ∀ lam₁ lam₂ : ℝ, 0 ≤ lam₁ → 0 ≤ lam₂ →
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
        OTDRO.Dual.ellRob ℓ A δ (α • β₁ + (1 - α) • β₂) (α * lam₁ + (1 - α) * lam₂) x ≤
          (α : EReal) * OTDRO.Dual.ellRob ℓ A δ β₁ lam₁ x +
            ((1 - α : ℝ) : EReal) * OTDRO.Dual.ellRob ℓ A δ β₂ lam₂ x := by
  intro x β₁ _ β₂ _ lam₁ lam₂ h1 h2 α hα0 hα1
  have hα1' : 0 ≤ 1 - α := by linarith
  have hlam : 0 ≤ α * lam₁ + (1 - α) * lam₂ := by positivity
  rw [← OTDRO.Cvx.sup_transport_eq_ellRob A x (hPD x) ℓ δ hδ _ _ hlam,
    ← OTDRO.Cvx.sup_transport_eq_ellRob A x (hPD x) ℓ δ hδ _ _ h1,
    ← OTDRO.Cvx.sup_transport_eq_ellRob A x (hPD x) ℓ δ hδ _ _ h2]
  apply iSup_le
  intro Δ
  set Q := dotProduct Δ.ofLp (A x *ᵥ Δ.ofLp)
  set u₁ := inner ℝ β₁ (x + Δ)
  set u₂ := inner ℝ β₂ (x + Δ)
  have hu : inner ℝ (α • β₁ + (1 - α) • β₂) (x + Δ) = α • u₁ + (1 - α) • u₂ := by
    simp [u₁, u₂, inner_add_left, real_inner_smul_left]
  have hconv := hℓ.2 (Set.mem_univ u₁) (Set.mem_univ u₂) hα0 hα1' (by ring)
  have key : ℓ (inner ℝ (α • β₁ + (1 - α) • β₂) (x + Δ)) -
      (α * lam₁ + (1 - α) * lam₂) / Real.sqrt δ * (Q - δ) ≤
      α * (ℓ u₁ - lam₁ / Real.sqrt δ * (Q - δ)) +
        (1 - α) * (ℓ u₂ - lam₂ / Real.sqrt δ * (Q - δ)) := by
    rw [hu]
    simp only [smul_eq_mul] at hconv ⊢
    have e : (α * lam₁ + (1 - α) * lam₂) / Real.sqrt δ * (Q - δ) =
        α * (lam₁ / Real.sqrt δ * (Q - δ)) + (1 - α) * (lam₂ / Real.sqrt δ * (Q - δ)) := by
      ring
    rw [e]; linarith
  calc ((ℓ (inner ℝ (α • β₁ + (1 - α) • β₂) (x + Δ)) -
        (α * lam₁ + (1 - α) * lam₂) / Real.sqrt δ * (Q - δ) : ℝ) : EReal)
      ≤ ((α * (ℓ u₁ - lam₁ / Real.sqrt δ * (Q - δ)) +
        (1 - α) * (ℓ u₂ - lam₂ / Real.sqrt δ * (Q - δ)) : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.2 key
    _ = (α : EReal) * ((ℓ u₁ - lam₁ / Real.sqrt δ * (Q - δ) : ℝ) : EReal) +
        ((1 - α : ℝ) : EReal) * ((ℓ u₂ - lam₂ / Real.sqrt δ * (Q - δ) : ℝ) : EReal) := by
        rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    _ ≤ _ := by
        gcongr
        · exact le_iSup (fun Δ : EuclideanSpace ℝ (Fin d) => ((ℓ (inner ℝ β₁ (x + Δ)) -
            lam₁ / Real.sqrt δ * (dotProduct Δ.ofLp (A x *ᵥ Δ.ofLp) - δ) : ℝ) : EReal)) Δ
        · exact le_iSup (fun Δ : EuclideanSpace ℝ (Fin d) => ((ℓ (inner ℝ β₂ (x + Δ)) -
            lam₂ / Real.sqrt δ * (dotProduct Δ.ofLp (A x *ᵥ Δ.ofLp) - δ) : ℝ) : EReal)) Δ

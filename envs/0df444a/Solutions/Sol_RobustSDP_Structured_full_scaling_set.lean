-- Prove2me | solution 1 for RobustSDP.Structured.full_scaling_set
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:08:40.867709+00:00
-- url     : https://prove2.me/submissions/e6cbf781-e4a1-4806-a47f-f30a9c9712a9

import Mathlib
import Definitions.Def_RobustSDP_Structured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Structured

theorem aux_fss_forward {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin p) (Fin q) ℝ)
    (h : (S, T, G) ∈ scalingSet (⊤ : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ))) :
    ∃ τ : ℝ, S = τ • (1 : Matrix (Fin p) (Fin p) ℝ) ∧ T = τ • (1 : Matrix (Fin q) (Fin q) ℝ) ∧
      G = 0 := by
  have h1 : ∀ (i : Fin p) (j : Fin q),
      S * single i j (1 : ℝ) = single i j (1 : ℝ) * T := fun i j =>
    (h (single i j 1) Submodule.mem_top).1
  have h2 : ∀ (i : Fin p) (j : Fin q),
      G * (single i j (1 : ℝ))ᵀ = -(single i j (1 : ℝ) * Gᵀ) := fun i j =>
    (h (single i j 1) Submodule.mem_top).2
  set i0 : Fin p := ⟨0, hp⟩
  set j0 : Fin q := ⟨0, hq⟩
  -- diagonal of S equals diagonal of T
  have hST : ∀ (i : Fin p) (j : Fin q), S i i = T j j := by
    intro i j
    have := congrFun (congrFun (h1 i j) i) j
    simpa using this
  refine ⟨S i0 i0, ?_, ?_, ?_⟩
  · ext a b
    by_cases hab : a = b
    · subst hab
      simp [hST a j0, hST i0 j0]
    · have := congrFun (congrFun (h1 b j0) a) j0
      simp [single_mul_apply_of_ne _ _ _ _ _ hab] at this
      simp [hab, this]
  · ext a b
    by_cases hab : a = b
    · subst hab
      simp [hST i0 a]
    · have := congrFun (congrFun (h1 i0 a) i0) b
      rw [mul_single_apply_of_ne _ _ _ _ _ (Ne.symm hab)] at this
      simp at this
      simp [hab, ← this]
  · ext a b
    have := congrFun (congrFun (h2 a b) a) a
    rw [transpose_single] at this
    simp at this
    simp
    linarith

end RobustSDP.Structured

open RobustSDP.Structured

theorem solution {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin p) (Fin q) ℝ) :
    ((S, T, G) ∈ scalingSet (⊤ : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) ↔
        ∃ τ : ℝ, S = τ • (1 : Matrix (Fin p) (Fin p) ℝ) ∧ T = τ • (1 : Matrix (Fin q) (Fin q) ℝ) ∧
          G = 0) ∧
      (S.PosSemidef → (S, T, G) ∈ scalingSet (⊤ : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) →
        ∃ τ : ℝ, 0 ≤ τ ∧ S = τ • (1 : Matrix (Fin p) (Fin p) ℝ) ∧
          T = τ • (1 : Matrix (Fin q) (Fin q) ℝ) ∧ G = 0) := by
  refine ⟨⟨aux_fss_forward hp hq S T G, ?_⟩, ?_⟩
  · rintro ⟨τ, rfl, rfl, rfl⟩
    intro Δ _
    simp
  · intro hS hmem
    obtain ⟨τ, hSe, hTe, hGe⟩ := aux_fss_forward hp hq S T G hmem
    refine ⟨τ, ?_, hSe, hTe, hGe⟩
    have := hS.diag_nonneg (i := (⟨0, hp⟩ : Fin p))
    rw [hSe] at this
    simpa using this

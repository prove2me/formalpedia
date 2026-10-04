-- Prove2me | solution 1 for ShorNonsmooth.Subdiff.max_function_subgradient
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:55:21.897507+00:00
-- url     : https://prove2.me/submissions/12353a86-89d3-44be-a27e-a29fb1563442

import Mathlib
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential

open ShorNonsmooth.Subdiff in
theorem solution {n m : ℕ} (hm : 0 < m)
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ i, ConvexOn ℝ Set.univ (f i)) :
    ConvexOn ℝ Set.univ
        (fun x => Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i => f i x)) ∧
      ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (i : Fin m),
        Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun j => f j x₀) = f i x₀ →
          subdifferential Set.univ (f i) x₀ ⊆
            subdifferential Set.univ
              (fun x => Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun j => f j x)) x₀ := by
  refine ⟨⟨convex_univ, ?_⟩, ?_⟩
  · intro x _ y _ a b ha hb hab
    refine Finset.sup'_le _ _ (fun i _ => ?_)
    have h1 := (hf i).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    have hx : f i x ≤ Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun j => f j x) :=
      Finset.le_sup' (fun j => f j x) (Finset.mem_univ i)
    have hy : f i y ≤ Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun j => f j y) :=
      Finset.le_sup' (fun j => f j y) (Finset.mem_univ i)
    simp only [smul_eq_mul] at h1 ⊢
    nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]
  · intro x₀ i hact g hg x hx
    have hgx := hg x hx
    have hle : f i x ≤ Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun j => f j x) :=
      Finset.le_sup' (fun j => f j x) (Finset.mem_univ i)
    show Finset.univ.sup' _ (fun j => f j x) - Finset.univ.sup' _ (fun j => f j x₀) ≥ _
    rw [hact]
    exact le_trans hgx (by linarith)

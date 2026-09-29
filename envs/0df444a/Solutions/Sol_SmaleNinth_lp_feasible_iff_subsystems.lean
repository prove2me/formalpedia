-- Prove2me | solution 1 for SmaleNinth.lp_feasible_iff_subsystems
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T01:36:53.245958+00:00
-- url     : https://prove2.me/submissions/3b8683c9-60df-4fd6-a306-134500dbed62

import Definitions.Def_Polyhedron
import Mathlib.Analysis.Convex.Radon
import Mathlib.Tactic

/-!
# Combinatorial dimension of LP feasibility

Helly's theorem for the half-spaces of a linear system: feasibility of
`Ax ≥ b` in `n` variables is equivalent to feasibility of every subsystem of
at most `n+1` inequalities.
-/

open Matrix LinearOptimization Finset


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (polyhedron A b).Nonempty ↔
      ∀ S : Finset (Fin m), S.card ≤ n + 1 →
        ∃ x : Fin n → ℝ, ∀ i ∈ S, b i ≤ (A.mulVec x) i := by
  constructor
  · rintro ⟨x, hx⟩ S _
    exact ⟨x, fun i _ => hx i⟩
  · intro h
    set F : Fin m → Set (Fin n → ℝ) := fun i => {x | b i ≤ (A.mulVec x) i} with hF
    have hlin : ∀ (i : Fin m) (s t : ℝ) (x y : Fin n → ℝ),
        (A.mulVec (s • x + t • y)) i = s * (A.mulVec x) i + t * (A.mulVec y) i := by
      intro i s t x y
      simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hconv : ∀ i, Convex ℝ (F i) := by
      intro i x hx y hy s t hs ht hst
      have hx' : b i ≤ (A.mulVec x) i := hx
      have hy' : b i ≤ (A.mulVec y) i := hy
      show b i ≤ (A.mulVec (s • x + t • y)) i
      rw [hlin]
      have hsum : s * b i + t * b i = b i := by
        calc s * b i + t * b i = (s + t) * b i := by ring
          _ = b i := by rw [hst]; ring
      linarith [mul_le_mul_of_nonneg_left hx' hs, mul_le_mul_of_nonneg_left hy' ht, hsum]
    have hrank : Module.finrank ℝ (Fin n → ℝ) = n := Module.finrank_fin_fun ℝ
    have hall : (⋂ i ∈ (Finset.univ : Finset (Fin m)), F i).Nonempty := by
      by_cases hm : n + 1 ≤ m
      · refine Convex.helly_theorem (𝕜 := ℝ) (F := F) (s := Finset.univ) ?_
          (fun i _ => hconv i) ?_
        · simp only [Finset.card_univ, Fintype.card_fin, hrank]
          exact hm
        · intro I _ hI
          obtain ⟨x, hx⟩ := h I (by rw [hI, hrank])
          exact ⟨x, Set.mem_iInter₂.mpr (fun i hi => hx i hi)⟩
      · obtain ⟨x, hx⟩ := h Finset.univ (by simp; omega)
        exact ⟨x, Set.mem_iInter₂.mpr (fun i _ => hx i (Finset.mem_univ i))⟩
    obtain ⟨x, hx⟩ := hall
    exact ⟨x, fun i => Set.mem_iInter₂.mp hx i (Finset.mem_univ i)⟩

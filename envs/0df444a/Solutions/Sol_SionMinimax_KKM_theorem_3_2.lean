-- Prove2me | solution 1 for SionMinimax.KKM.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:55:14.67297+00:00
-- url     : https://prove2.me/submissions/5eb3ade6-8fd5-4fd9-b885-7bd98a104428

import Mathlib



namespace SionMinimax.KKM

theorem t32_core {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (n : ℕ) (hdim : Module.finrank ℝ V < n)
    (a : Fin (n + 1) → V) (ha : Function.Injective a) :
    (⋂ i : Fin (n + 1), convexHull ℝ (Set.range a \ {a i})).Nonempty := by
  have hna : ¬ AffineIndependent ℝ a := by
    intro h
    have := h.card_le_finrank_succ
    simp at this
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range a))
    omega
  obtain ⟨I, p, hpI, hpJ⟩ := Convex.radon_partition hna
  refine ⟨p, Set.mem_iInter.2 fun i => ?_⟩
  by_cases hi : i ∈ I
  · refine convexHull_mono ?_ hpJ
    rintro _ ⟨j, hj, rfl⟩
    refine ⟨⟨j, rfl⟩, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro h
    exact hj (by rw [ha h]; exact hi)
  · refine convexHull_mono ?_ hpI
    rintro _ ⟨j, hj, rfl⟩
    refine ⟨⟨j, rfl⟩, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro h
    exact hi (by rw [← ha h]; exact hj)

end SionMinimax.KKM

open SionMinimax.KKM


theorem solution {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (n : ℕ) (hdim : Module.finrank ℝ V < n)
    (a : Fin (n + 1) → V) (ha : Function.Injective a) :
    (⋂ i : Fin (n + 1), convexHull ℝ (Set.range a \ {a i})).Nonempty := by
  exact t32_core n hdim a ha

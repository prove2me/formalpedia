-- Prove2me | solution 1 for ProjSchedTW.ActiveSchedules.lb_unique_minimal_point
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:09:40.951023+00:00
-- url     : https://prove2.me/submissions/0a340240-226d-4ec9-8931-5de5948ffca5

import Mathlib
import Definitions.Def_ProjSchedTW_ActiveSchedules_Project

open ProjSchedTW.ActiveSchedules in
theorem f3dd3e5a_lb_le {n : ℕ} {K : Type} (P : Project n K)
    (O : Set (Fin (n + 2) × Fin (n + 2))) (S : Fin (n + 2) → ℝ)
    (hS : S ∈ orderPolyhedron P O) (i : Fin (n + 2)) :
    lowerBound (orderPolyhedron P O) i ≤ S i := by
  unfold lowerBound
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨T, hT, rfl⟩
    exact hT.1.2.1 i
  · exact ⟨S, hS, rfl⟩

open ProjSchedTW.ActiveSchedules in
theorem f3dd3e5a_le_lb {n : ℕ} {K : Type} (P : Project n K)
    (O : Set (Fin (n + 2) × Fin (n + 2)))
    (hne : (orderPolyhedron P O).Nonempty) (i : Fin (n + 2)) (c : ℝ)
    (h : ∀ T ∈ orderPolyhedron P O, c ≤ T i) :
    c ≤ lowerBound (orderPolyhedron P O) i := by
  unfold lowerBound
  apply le_csInf
  · obtain ⟨S, hS⟩ := hne
    exact ⟨S i, S, hS, rfl⟩
  · rintro _ ⟨T, hT, rfl⟩
    exact h T hT

open ProjSchedTW.ActiveSchedules in
theorem f3dd3e5a_mem {n : ℕ} {K : Type} (P : Project n K)
    (O : Set (Fin (n + 2) × Fin (n + 2)))
    (hne : (orderPolyhedron P O).Nonempty) :
    lowerBound (orderPolyhedron P O) ∈ orderPolyhedron P O := by
  obtain ⟨S₀, hS₀⟩ := hne
  have hne' : (orderPolyhedron P O).Nonempty := ⟨S₀, hS₀⟩
  -- key: for c, i, j with T j ≥ T i + c on M, lb j ≥ lb i + c
  have key : ∀ (i j : Fin (n + 2)) (c : ℝ),
      (∀ T ∈ orderPolyhedron P O, T i + c ≤ T j) →
      lowerBound (orderPolyhedron P O) i + c ≤ lowerBound (orderPolyhedron P O) j := by
    intro i j c h
    apply f3dd3e5a_le_lb P O hne' j
    intro T hT
    have := f3dd3e5a_lb_le P O T hT i
    have := h T hT
    linarith
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · apply le_antisymm
    · have := f3dd3e5a_lb_le P O S₀ hS₀ 0
      rw [hS₀.1.1] at this
      exact this
    · apply f3dd3e5a_le_lb P O hne' 0
      intro T hT
      rw [hT.1.1]
  · intro i
    apply f3dd3e5a_le_lb P O hne' i
    intro T hT
    exact hT.1.2.1 i
  · intro e he
    have := key e.1 e.2 (P.δ e.1 e.2 : ℝ) (fun T hT => by
      have := hT.1.2.2 e he
      linarith)
    linarith
  · intro e he
    exact key e.1 e.2 (P.p e.1 : ℝ) (fun T hT => hT.2 e he)

open ProjSchedTW.ActiveSchedules in
theorem solution {n : ℕ} {K : Type} (P : Project n K)
    (O : Set (Fin (n + 2) × Fin (n + 2))) (hO : IsStrictOrderRel O)
    (hne : (orderPolyhedron P O).Nonempty) :
    Minimal (· ∈ orderPolyhedron P O) (lowerBound (orderPolyhedron P O)) ∧
      ∀ S : Fin (n + 2) → ℝ, Minimal (· ∈ orderPolyhedron P O) S →
        S = lowerBound (orderPolyhedron P O) := by
  have hmem := f3dd3e5a_mem P O hne
  have hle : ∀ S ∈ orderPolyhedron P O, lowerBound (orderPolyhedron P O) ≤ S :=
    fun S hS i => f3dd3e5a_lb_le P O S hS i
  refine ⟨⟨hmem, by intro y hy _; exact hle y hy⟩, ?_⟩
  intro S hS
  exact le_antisymm (hS.2 hmem (hle S hS.1)) (hle S hS.1)

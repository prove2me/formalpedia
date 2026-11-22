-- Prove2me | solution 1 for SubspaceEvasion312.Explicit.constant_alphabet_design
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T22:55:22.282161+00:00
-- url     : https://prove2.me/submissions/2cb5a5c4-883c-48e1-9304-d14a737ebc8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SubspaceEvasion312_Explicit_codeAlgorithms_of_entries
import Theorems.Thm_SubspaceEvasion312_Explicit_constant_alphabet_design_entries

open SubspaceEvasion312.Explicit

private theorem runFrom_mono {F : Type} [Field F]
    {P : Program F} {ns : List ℕ} {xs : List F}
    {t : ℕ} {z z' : MachineState F} {B B' : ℕ} (hBB : B ≤ B')
    (h : runFrom P ns xs B t z = some z') : runFrom P ns xs B' t z = some z' := by
  induction t generalizing z with
  | zero => simp [runFrom] at h
  | succ t ih =>
    simp only [runFrom] at h ⊢
    by_cases hzB : ∀ i, z.natReg i ≤ B
    · have hzB' : ∀ i, z.natReg i ≤ B' := fun i => (hzB i).trans hBB
      rw [if_pos hzB] at h
      rw [if_pos hzB']
      split at h
      · exact h
      · cases hs : step P ns xs z with
        | none => simp [hs] at h
        | some z₁ =>
          simp only [hs, Option.bind_some] at h ⊢
          exact ih h
    · rw [if_neg hzB] at h
      contradiction

private theorem runsWithin_mono {F : Type} [Field F]
    {P : Program F} {ns : List ℕ} {xs ys : List F} {outN : List ℕ}
    {T B T' B' : ℕ} (hT : T ≤ T') (hB : B ≤ B')
    (h : RunsWithin P ns xs T B ys outN) : RunsWithin P ns xs T' B' ys outN := by
  obtain ⟨t, z, ht, hrun, hout, houtN⟩ := h
  exact ⟨t, z, by omega, runFrom_mono hB hrun, hout, houtN⟩

/-- Theorem 17 from a uniform generator-matrix presentation. -/
theorem solution :
    ∃ A a h : ℕ, 0 < A ∧
    ∀ (F : Type) [Field F] [Fintype F] (r : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∃ K : ℕ, 0 < K ∧
    ∀ R : ℝ, 0 < R → R + ε ≤ 1 →
    ∃ (s m₀ : ℕ) (C : ∀ m, Code F s m) (k : ℕ → ℕ)
      (E : ∀ m, Vec F (k m) →ₗ[F] Blocks F s m)
      (τ : ℕ → ℕ → ℝ) (gen enc : Program F),
      0 < s ∧ 0 < m₀ ∧ (s : ℝ) ≤ A * (1 + r + 1 / ε)^a * (Fintype.card F : ℝ)^(r^2) ∧
      CodeAlgorithms k E gen enc (fun m => K * (m+1)^h) (fun m => K * (m+1)^h) m₀ ∧
      ∀ m ≥ m₀, IsEncoder (C m) (E m) ∧ R ≤ codeRate (C m) ∧
        SubspaceDesign (C m) (τ m) ∧ τ m r ≤ R + ε := by
  obtain ⟨c, compiler⟩ := codeAlgorithms_of_entries
  obtain ⟨A, a, h₀, hA, entries⟩ := constant_alphabet_design_entries
  refine ⟨A, a, h₀ + c, hA, ?_⟩
  intro F _ _ r ε hε hε1
  obtain ⟨K₀, hK₀, entries'⟩ := entries F r ε hε hε1
  let S : ℕ := ⌈(A : ℝ) * (1 + r + 1 / ε)^a * (Fintype.card F : ℝ)^(r^2)⌉₊
  refine ⟨K₀ * (S+2)^c, Nat.mul_pos hK₀ (pow_pos (by omega) _), ?_⟩
  intro R hR hRε
  obtain ⟨s, m₀, C, k, E, τ, dim, entry, hs, hm₀, hsbound, hk, horacle, hprop⟩ :=
    entries' R hR hRε
  obtain ⟨gen, enc, m₁, hm₀₁, hcomp⟩ :=
    compiler F s h₀ K₀ m₀ k E dim entry hK₀ hk horacle
  have hsS' : (s : ℝ) ≤ (S : ℝ) := by
    dsimp [S]
    exact hsbound.trans (Nat.le_ceil _)
  have hsS : s ≤ S := by exact_mod_cast hsS'
  have hspow : (s+2)^c ≤ (S+2)^c := Nat.pow_le_pow_left (by omega) c
  refine ⟨s, m₁, C, k, E, τ, gen, enc, hs, lt_of_lt_of_le hm₀ hm₀₁, hsbound, ?_, ?_⟩
  · intro m hm
    have htime : K₀ * (s+2)^c * (m+1)^(h₀+c) ≤
        K₀ * (S+2)^c * (m+1)^(h₀+c) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hspow)
    have hcompm := hcomp m hm
    exact ⟨runsWithin_mono htime htime hcompm.1,
      fun x => runsWithin_mono htime htime (hcompm.2 x)⟩
  · intro m hm
    exact hprop m (hm₀₁.trans hm)

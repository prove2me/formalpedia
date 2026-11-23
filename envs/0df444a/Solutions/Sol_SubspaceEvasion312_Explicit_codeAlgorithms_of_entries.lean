-- Prove2me | solution 1 for SubspaceEvasion312.Explicit.codeAlgorithms_of_entries
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:25:51.305091+00:00
-- url     : https://prove2.me/submissions/cfbc3b27-36df-44de-bff2-1e014a8e65fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SubspaceEvasion312_Explicit_generatorAlgorithm_of_entries
import Theorems.Thm_SubspaceEvasion312_Explicit_encoderAlgorithm_of_entries

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

private theorem budget_mono {K₀ s h₀ m c d : ℕ} (h : c ≤ d) :
    K₀ * (s+2)^c * (m+1)^(h₀+c) ≤ K₀ * (s+2)^d * (m+1)^(h₀+d) := by
  have hp₁ : (s+2)^c ≤ (s+2)^d := Nat.pow_le_pow_right (by omega) h
  have hp₂ : (m+1)^(h₀+c) ≤ (m+1)^(h₀+d) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp₁) hp₂

/-- A uniform generator-matrix presentation compiles to basis generation and encoding. -/
theorem solution :
    ∃ c : ℕ, ∀ (F : Type) [Field F] (s h₀ K₀ m₀ : ℕ)
      (k : ℕ → ℕ) (E : ∀ m, SubspaceEvasion312.Explicit.Vec F (k m) →ₗ[F] SubspaceEvasion312.Explicit.Blocks F s m)
      (dim entry : SubspaceEvasion312.Explicit.Program F), 0 < K₀ →
      (∀ m ≥ m₀, k m ≤ s * m) →
      (∀ m ≥ m₀,
        SubspaceEvasion312.Explicit.RunsWithin dim [m] [] (K₀ * (m+1)^h₀) (K₀ * (m+1)^h₀) [] [k m] ∧
        ∀ (j : Fin (k m)) (i : Fin m) (u : Fin s),
          SubspaceEvasion312.Explicit.RunsWithin entry [m, j.val, i.val, u.val] []
            (K₀ * (m+1)^h₀) (K₀ * (m+1)^h₀)
            [E m (Pi.single j 1) i u]) →
      ∃ (gen enc : SubspaceEvasion312.Explicit.Program F) (m₁ : ℕ), m₀ ≤ m₁ ∧
        SubspaceEvasion312.Explicit.CodeAlgorithms k E gen enc
          (fun m => K₀ * (s+2)^c * (m+1)^(h₀+c))
          (fun m => K₀ * (s+2)^c * (m+1)^(h₀+c)) m₁ := by
  obtain ⟨cg, gen_compiler⟩ := SubspaceEvasion312.Explicit.generatorAlgorithm_of_entries
  obtain ⟨ce, enc_compiler⟩ := SubspaceEvasion312.Explicit.encoderAlgorithm_of_entries
  refine ⟨max cg ce, ?_⟩
  intro F _ s h₀ K₀ m₀ k E dim entry hK₀ hk horacle
  obtain ⟨gen, mg, hmg, hgen⟩ := gen_compiler F s h₀ K₀ m₀ k E dim entry hK₀ hk horacle
  obtain ⟨enc, me, hme, henc⟩ := enc_compiler F s h₀ K₀ m₀ k E dim entry hK₀ hk horacle
  refine ⟨gen, enc, max mg me, le_trans hmg (Nat.le_max_left _ _), ?_⟩
  intro m hm
  have hmg' : mg ≤ m := (Nat.le_max_left mg me).trans hm
  have hme' : me ≤ m := (Nat.le_max_right mg me).trans hm
  have hbg := budget_mono (K₀ := K₀) (s := s) (h₀ := h₀) (m := m) (Nat.le_max_left cg ce)
  have hbe := budget_mono (K₀ := K₀) (s := s) (h₀ := h₀) (m := m) (Nat.le_max_right cg ce)
  exact ⟨runsWithin_mono hbg hbg (hgen m hmg'),
    fun x => runsWithin_mono hbe hbe (henc m hme' x)⟩

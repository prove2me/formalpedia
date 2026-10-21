-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P14.diagonal_replacement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:18:18.421804+00:00
-- url     : https://prove2.me/submissions/75862a1f-428b-4a34-b045-fb1fc7741c5f

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14
noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Claimed50.P14

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

theorem g57d_dephase_psd {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    Matrix.PosSemidef (Matrix.of fun a b => if f a = f b then M a b else 0 : Matrix ι ι ℂ) := by
  have key : (Matrix.of fun a b => if f a = f b then M a b else 0 : Matrix ι ι ℂ) =
      ∑ k : κ, (Matrix.diagonal (fun a => if f a = k then (1:ℂ) else 0))ᴴ * M *
        Matrix.diagonal (fun a => if f a = k then (1:ℂ) else 0) := by
    ext a b
    simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    by_cases h : f a = f b
    · rw [if_pos h, Finset.sum_eq_single (f a)]
      · simp [h]
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    · rw [if_neg h]
      refine (Finset.sum_eq_zero (fun k _ => ?_)).symm
      by_cases h1 : f a = k
      · have : f b ≠ k := fun h2 => h (h1.trans h2.symm)
        simp [this]
      · simp [h1]
  rw [key]
  exact Matrix.posSemidef_sum _ (fun k _ => hM.conjTranspose_mul_mul_same _)

theorem g57d_labels_eq {d n : ℕ} (j l : Labels d (n+1)) :
    j = l ↔ j 0 = l 0 ∧ Fin.tail j = Fin.tail l := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← Fin.cons_self_tail j, ← Fin.cons_self_tail l, h1, h2]

def g57d_dA {d n : ℕ} (A : Matrix (Labels d n × Labels d n) (Labels d n × Labels d n) ℂ) :
    Matrix (Labels d n × Labels d n) (Labels d n × Labels d n) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then A p q else 0

theorem g57d_causal (d k : ℕ) : ∀ (n : ℕ) (A : Matrix (Labels d n × Labels d n) (Labels d n × Labels d n) ℂ),
    CausalTraining d k n A → CausalTraining d k n (g57d_dA A) := by
  intro n
  induction n with
  | zero =>
    intro A hA
    simp only [CausalTraining] at hA ⊢
    subst hA
    ext p q
    simp only [g57d_dA, Matrix.of_apply, Matrix.one_apply]
    split_ifs with h1 h2 h2 <;> try rfl
    · exact absurd (h2 ▸ rfl : p.1 = q.1) h1
  | succ n ih =>
    intro A hA
    simp only [CausalTraining] at hA ⊢
    refine ⟨by unfold g57d_dA; convert g57d_dephase_psd (fun p => p.1) A hA.1, ?_⟩
    have h2 := hA.2
    split_ifs at h2 ⊢ with hk
    · obtain ⟨rho, hr, hr1, hA'⟩ := h2
      refine ⟨rho, hr, hr1, fun j a l b => ?_⟩
      simp only [g57d_dA, Matrix.of_apply, hA']
      split_ifs <;> simp_all
    · obtain ⟨B, C, hB, hC, hAB, hBC⟩ := h2
      refine ⟨Matrix.of fun p q => if p.2.1 = q.2.1 then B p q else 0, g57d_dA C,
        by convert g57d_dephase_psd (fun p => p.2.1) B hB, ih C hC, fun j a l b => ?_, fun j a l b => ?_⟩
      · simp only [g57d_dA, Matrix.of_apply, hAB]
        by_cases e : j = l
        · subst e; simp
        · rw [if_neg e]
          have := (g57d_labels_eq j l).not.mp e
          by_cases h0 : j 0 = l 0
          · rw [if_pos h0, if_neg (fun h => this ⟨h0, h⟩)]
          · rw [if_neg h0]
      · simp only [g57d_dA, Matrix.of_apply, ← hBC]
        split_ifs <;> simp

theorem solution {d N : ℕ} (hd : 2 ≤ d) (hN : 1 ≤ N)
    (k : ℕ) (S : Branches d N) (hS : LearningInstrument k S) :
    LearningInstrument k (outcomeDephasing S) ∧ IsDiagonal (outcomeDephasing S) ∧
    (∀ i j, (outcomeBlocks S i j).PosSemidef) ∧
    (∀ i a b, outcomeDephasing S i a b =
      if a.2.1 = b.2.1 then outcomeBlocks S i a.2.1 (a.1,a.2.2) (b.1,b.2.2) else 0) ∧
    ∀ U : SU d, replicatedPOVM (outcomeDephasing S) (U : (Matrix (Fin d) (Fin d) ℂ)) =
      replicatedPOVM S (U : (Matrix (Fin d) (Fin d) ℂ)) := by
  obtain ⟨hpsd, A, hA, hsum⟩ := hS
  refine ⟨⟨fun i => g57d_dephase_psd (fun a : TrainingWires d N => a.2.1) (S i) (hpsd i),
    g57d_dA A, g57d_causal d k N A hA, fun t j a s l b => ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [outcomeDephasing, g57d_dA, Matrix.of_apply]
    by_cases e : j = l
    · simp only [e, if_true]; rw [← hsum]
    · simp [e]
  · unfold IsDiagonal outcomeDephasing
    funext i a b
    split_ifs <;> rfl
  · intro i j
    exact (hpsd i).submatrix (fun a : Fin d × Labels d N => (a.1, (j, a.2)))
  · intro i a b
    simp only [outcomeDephasing, outcomeBlocks]
    split_ifs with h
    · obtain ⟨a1, a2, a3⟩ := a
      obtain ⟨b1, b2, b3⟩ := b
      simp only at h; subst h; rfl
    · rfl
  · intro U
    funext i t s
    simp [replicatedPOVM, outcomeDephasing]

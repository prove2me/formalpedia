-- Prove2me | solution 1 for PI.SqPair.LocCartanPairW.cmp_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:55.098402+00:00
-- url     : https://prove2.me/submissions/4fbd6b15-2880-4fed-bbe6-4b235f724198

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)
private lemma mapMul_lemma_2 {α β γ : Type*} [Fintype β] (X : Matrix α β R) (Y : Matrix β γ R) :
    (X * Y).map σ = X.map σ * Y.map σ := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]
end PI.SqPair.LocCartanPairW
namespace PI.SqPair.LCP
open PI.SqPair.LocCartanPairW
end PI.SqPair.LCP
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)
namespace PI.SqPair.LocCartanPairW
theorem _root_.solution [IsDomain R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A A' h : Matrix ι ι R) (s : R) (hh : (h.map σ)ᵀ * A * h = s • A')
    (c₁ c₂ : R) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (x y v₁ w₁ : ι → R)
    (hv : h *ᵥ v₁ = c₁ • x) (hw : h *ᵥ w₁ = c₂ • y)
    (u u' : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ A₁' : Matrix κ κ R)
    (huv : u * v = 1) (hvu : v * u = 1)
    (hu0 : ∀ i, u i (.inl 0) = x i) (hu1 : ∀ i, u i (.inl 1) = y i)
    (hu0' : ∀ i, u' i (.inl 0) = v₁ i) (hu1' : ∀ i, u' i (.inl 1) = w₁ i)
    (hG : (u.map σ)ᵀ * A * u = fromBlocks !![0, 1; 1, 0] 0 0 A₁)
    (hG' : (u'.map σ)ᵀ * A' * u' = fromBlocks !![0, 1; 1, 0] 0 0 A₁') :
    ∃ h₂ : Matrix κ κ R, v * h * u' = fromBlocks (diagonal ![c₁, c₂]) 0 0 h₂ ∧
      (h₂.map σ)ᵀ * A₁ * h₂ = s • A₁' := by
  obtain ⟨M, hMdef⟩ : ∃ M, M = v * h * u' := ⟨_, rfl⟩
  have hcol : ∀ b : Fin 2, ∀ i, (h * u') i (.inl b) = ![c₁, c₂] b * u i (.inl b) := by
    rw [Fin.forall_fin_two]
    constructor
    · intro i
      have e := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
      simp [Matrix.mul_apply, hu0', hu0, e]
    · intro i
      have e := congrFun hw i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
      simp [Matrix.mul_apply, hu1', hu1, e]
  have hM1 : ∀ a (b : Fin 2), M a (.inl b) =
      ![c₁, c₂] b * (1 : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) a (.inl b) := by
    intro a b
    rw [hMdef, Matrix.mul_assoc, Matrix.mul_apply, ← hvu, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcol b i]
    ring
  have hUM : u * M = h * u' := by
    rw [hMdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, huv, Matrix.one_mul]
  have hGram : (M.map σ)ᵀ * fromBlocks !![0, 1; 1, 0] 0 0 A₁ * M =
      s • fromBlocks !![0, 1; 1, 0] 0 0 A₁' := by
    rw [← hG, ← hG']
    calc (M.map σ)ᵀ * ((u.map σ)ᵀ * A * u) * M = ((u * M).map σ)ᵀ * A * (u * M) := by
          rw [mapMul_lemma_2 σ, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = ((h * u').map σ)ᵀ * A * (h * u') := by rw [hUM]
      _ = (u'.map σ)ᵀ * ((h.map σ)ᵀ * A * h) * u' := by
          rw [mapMul_lemma_2 σ, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = s • ((u'.map σ)ᵀ * A' * u') := by
          rw [hh, Matrix.mul_smul, Matrix.smul_mul]
  have hMb : M = fromBlocks (diagonal ![c₁, c₂]) M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · rw [hM1 (.inl a) b]
      by_cases hab : a = b
      · subst hab
        simp [Matrix.one_apply, Matrix.diagonal_apply]
      · simp [Matrix.one_apply, Matrix.diagonal_apply, hab]
    · simp [Matrix.toBlocks₁₂]
    · rw [hM1 (.inr a) b]
      simp [Matrix.one_apply]
    · simp [Matrix.toBlocks₂₂]
  rw [hMb] at hGram
  simp only [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul, Matrix.map_zero, map_zero, Matrix.transpose_zero, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, smul_zero] at hGram
  obtain ⟨-, hQ, -, hS⟩ := Matrix.fromBlocks_inj.mp hGram
  have hc₁' : σ c₁ ≠ 0 := by simpa using hc₁
  have hc₂' : σ c₂ ≠ 0 := by simpa using hc₂
  have hB : M.toBlocks₁₂ = 0 := by
    ext a l
    have e0 := congrFun (congrFun hQ 0) l
    have e1 := congrFun (congrFun hQ 1) l
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hc₁', hc₂'] at e0 e1
    fin_cases a
    · simpa using e1
    · simpa using e0
  refine ⟨M.toBlocks₂₂, ?_, ?_⟩
  · rw [← hMdef]
    nth_rewrite 1 [hMb]
    rw [hB]
  · rw [hB] at hS
    simpa using hS
end PI.SqPair.LocCartanPairW

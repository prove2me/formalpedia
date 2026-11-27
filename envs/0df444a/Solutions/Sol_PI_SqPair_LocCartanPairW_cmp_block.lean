-- Prove2me | solution 1 for PI.SqPair.LocCartanPairW.cmp_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:16:36.983278+00:00
-- url     : https://prove2.me/submissions/bbb13b3a-2a2f-42c7-9d53-b7f623ad0cbd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
import Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_conjT_mul
import Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_block_of_gram
import Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_det_diag_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)
namespace PI.SqPair.LocCartanPairW
theorem _root_.solution [IsDomain R] {ι μ κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ]
    [DecidableEq μ] [Fintype κ] [DecidableEq κ]
    (A A' h : Matrix ι ι R) (s : R) (hh : (h.map σ)ᵀ * A * h = s • A')
    (J : Matrix μ μ R) (hJ : J.det ≠ 0) (A₁ A₁' : Matrix κ κ R)
    (u u' : Matrix ι (μ ⊕ κ) R) (v : Matrix (μ ⊕ κ) ι R) (hvu : v * u = 1) (huv : u * v = 1)
    (hG : (u.map σ)ᵀ * A * u = fromBlocks J 0 0 A₁)
    (hG' : (u'.map σ)ᵀ * A' * u' = fromBlocks J 0 0 A₁')
    (c : μ → R) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ r i, (h * u') r (Sum.inl i) = c i * u r (Sum.inl i)) :
    ∃ h₂ : Matrix κ κ R, v * h * u' = fromBlocks (diagonal c) 0 0 h₂ ∧
      (h₂.map σ)ᵀ * A₁ * h₂ = s • A₁' := by
  have hcolM : ∀ r i, (v * h * u') r (Sum.inl i) = (v * u) r (Sum.inl i) * c i := by
    intro r i
    rw [Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcol]
    ring
  rw [hvu] at hcolM
  have h11 : (v * h * u').toBlocks₁₁ = diagonal c := by
    ext a b
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, hcolM, Matrix.one_apply, Sum.inl.injEq,
      diagonal_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab]
  have h21 : (v * h * u').toBlocks₂₁ = 0 := by
    ext a b
    simp [Matrix.toBlocks₂₁, hcolM]
  have hu : u * (v * h * u') = h * u' := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, huv, Matrix.one_mul]
  have hgram : ((v * h * u').map σ)ᵀ * fromBlocks J 0 0 A₁ * (v * h * u') =
      s • fromBlocks J 0 0 A₁' := by
    rw [← hG, ← hG']
    calc ((v * h * u').map σ)ᵀ * ((u.map σ)ᵀ * A * u) * (v * h * u')
        = ((u * (v * h * u')).map σ)ᵀ * A * (u * (v * h * u')) := by
          rw [cmp_conjT_mul σ u (v * h * u')]
          simp only [Matrix.mul_assoc]
      _ = ((h * u').map σ)ᵀ * A * (h * u') := by rw [hu]
      _ = (u'.map σ)ᵀ * ((h.map σ)ᵀ * A * h) * u' := by
          rw [cmp_conjT_mul σ h u']
          simp only [Matrix.mul_assoc]
      _ = s • ((u'.map σ)ᵀ * A' * u') := by
          rw [hh, Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨h12, h22⟩ := cmp_block_of_gram σ (v * h * u') J A₁ A₁' s hgram h21
    (by rw [h11]; exact cmp_det_diag_ne σ J hJ c hc)
  refine ⟨(v * h * u').toBlocks₂₂, ?_, h22⟩
  rw [← h11, ← h12, ← h21]
  exact (Matrix.fromBlocks_toBlocks _).symm
end PI.SqPair.LocCartanPairW

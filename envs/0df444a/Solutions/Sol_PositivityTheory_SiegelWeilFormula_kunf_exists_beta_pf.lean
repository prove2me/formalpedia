-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.kunf.exists_beta_pf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:48.810296+00:00
-- url     : https://prove2.me/submissions/586aab13-0355-48c6-a0d5-9436fb4e5ede

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_UnfoldingCompactness_ExistsBetaPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.kunf
namespace PositivityTheory.SiegelWeilFormula.kunf
theorem _root_.solution {K : Type} [Field K] (s : K →+* K) (hs : ∀ x, s (s x) = x) {n : ℕ} (e : K) (he : e * e = 1)
    (hse : s e = e) (a c d' : Matrix (Fin n) (Fin n) K) (hc : c.det = 0) (hda : e • (c.map s)ᵀ * a + d' * c = 0)
    (T : Matrix (Fin n) (Fin n) K) (hT : Tᵀ = -(e • T.map s)) (hTd : T.det ≠ 0) :
    ∃ β₁ : Matrix (Fin n) (Fin n) K, β₁ᵀ = -(e • β₁.map s) ∧ c * β₁ * (e • (c.map s)ᵀ) = 0 ∧
      (∃ v w : Fin n → K, a * β₁ * (e • (c.map s)ᵀ) = Matrix.vecMulVec v w ∧ w ⬝ᵥ v = 0) ∧ (T * β₁).trace = 2 := by
  classical
  obtain ⟨u, hu0, hcu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hc
  have hTu : T *ᵥ u ≠ 0 := fun h0 => hTd (Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, hu0, h0⟩)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hTu
  have hi' : (T *ᵥ u) i ≠ 0 := hi
  obtain ⟨y, hy⟩ : ∃ y : Fin n → K, y ⬝ᵥ (T *ᵥ u) = 1 :=
    ⟨Pi.single i ((T *ᵥ u) i)⁻¹, by rw [single_dotProduct, inv_mul_cancel₀ hi']⟩
  obtain ⟨su, hsu⟩ : ∃ w : Fin n → K, w = s ∘ u := ⟨_, rfl⟩
  obtain ⟨sy, hsy⟩ : ∃ w : Fin n → K, w = s ∘ y := ⟨_, rfl⟩
  have hcsu : c.map s *ᵥ su = 0 := by
    rw [hsu]
    ext j
    rw [← RingHom.map_mulVec, hcu]
    simp
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  have hM : (e • (c.map s)ᵀ * a) *ᵥ u = 0 := by
    rw [eq_neg_of_add_eq_zero_left hda, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hcu,
      Matrix.mulVec_zero, neg_zero]
  have hM' : ((c.map s)ᵀ * a) *ᵥ u = 0 := by
    rw [Matrix.smul_mul, Matrix.smul_mulVec] at hM
    exact (smul_eq_zero.mp hM).resolve_left he0
  have key : (c.map s *ᵥ y) ⬝ᵥ (a *ᵥ u) = y ⬝ᵥ (((c.map s)ᵀ * a) *ᵥ u) := by
    simp only [Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]
  refine ⟨vecMulVec u y - e • vecMulVec sy su, ?_, ?_, ?_, ?_⟩
  · subst hsu hsy
    ext j k
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply,
      Matrix.sub_apply, Matrix.vecMulVec_apply, Function.comp_apply, smul_eq_mul, map_sub, map_mul, hs, hse]
    linear_combination (-(y j * u k)) * he
  · simp [Matrix.mul_sub, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hcu, hcsu]
  · refine ⟨a *ᵥ u, e • (c.map s *ᵥ y), ?_, ?_⟩
    · simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
        hcsu]
    · rw [smul_dotProduct, key, hM', dotProduct_zero, smul_zero]
  · have h1 : (T *ᵥ u) ⬝ᵥ y = 1 := by rw [dotProduct_comm, hy]
    have hsy1 : sy ⬝ᵥ (T.map s *ᵥ su) = 1 := by
      have hmv : T.map s *ᵥ su = s ∘ (T *ᵥ u) := by
        rw [hsu]
        ext j
        exact (RingHom.map_mulVec s T u j).symm
      rw [hmv, hsy, ← RingHom.map_dotProduct, hy, map_one]
    have h2 : (T *ᵥ sy) ⬝ᵥ su = -e := by
      calc (T *ᵥ sy) ⬝ᵥ su = sy ⬝ᵥ (Tᵀ *ᵥ su) := by
            rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
        _ = sy ⬝ᵥ ((-(e • T.map s)) *ᵥ su) := by rw [hT]
        _ = -e * (sy ⬝ᵥ (T.map s *ᵥ su)) := by
            rw [Matrix.neg_mulVec, Matrix.smul_mulVec, dotProduct_neg, dotProduct_smul,
              smul_eq_mul]
            ring
        _ = -e := by rw [hsy1, mul_one]
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_vecMulVec, Matrix.trace_vecMulVec, h1, h2, smul_eq_mul]
    linear_combination he
end PositivityTheory.SiegelWeilFormula.kunf

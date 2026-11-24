-- Prove2me | solution 1 for QCQPTightness.Exact.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T01:37:56.661333+00:00
-- url     : https://prove2.me/submissions/2a7a179c-8b55-4229-8f3d-06f291778a95

import Mathlib
import Definitions.Def_QCQPTightness_Exact_QCQP
import Definitions.Def_QCQPTightness_Exact_Faces

open Matrix QCQPTightness.Exact

namespace QCQPLemma2Aux

/-- If two positive semidefinite matrices have a common null vector of their average, the vector is
in both kernels. -/
lemma ker_of_half {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) {v : Fin N → ℝ} (h : ((1 / 2 : ℝ) • (A + B)) *ᵥ v = 0) :
    A *ᵥ v = 0 ∧ B *ᵥ v = 0 := by
  rw [smul_mulVec, add_mulVec, smul_eq_zero] at h
  have h2 : A *ᵥ v + B *ᵥ v = 0 := by
    rcases h with h | h
    · norm_num at h
    · exact h
  have ha := hA.dotProduct_mulVec_nonneg v
  have hb := hB.dotProduct_mulVec_nonneg v
  have hsum : star v ⬝ᵥ (A *ᵥ v) + star v ⬝ᵥ (B *ᵥ v) = 0 := by
    rw [← dotProduct_add, h2, dotProduct_zero]
  have hA0 : star v ⬝ᵥ (A *ᵥ v) = 0 := by linarith
  have hB0 : star v ⬝ᵥ (B *ᵥ v) = 0 := by linarith
  exact ⟨(hA.dotProduct_mulVec_zero_iff v).1 hA0, (hB.dotProduct_mulVec_zero_iff v).1 hB0⟩

lemma Aγ_mid {N m : ℕ} (P : QCQP N m) (γ γ' : Fin m → ℝ) :
    P.Aγ ((1 / 2 : ℝ) • γ + (1 / 2 : ℝ) • γ') = (1 / 2 : ℝ) • (P.Aγ γ + P.Aγ γ') := by
  simp only [QCQP.Aγ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul,
    Finset.sum_add_distrib, ← smul_smul, ← Finset.smul_sum, smul_add]
  module

end QCQPLemma2Aux

theorem solution {N m : ℕ} (P : QCQP N m) (F : Set (Fin m → ℝ))
    (hF : P.IsSemidefiniteFace F) :
    ∃ v ∈ P.V F, v ⬝ᵥ v = 1 := by
  classical
  obtain ⟨⟨hne, hconv, hext⟩, hnot⟩ := hF
  have hpsd : ∀ γ ∈ F, (P.Aγ γ).PosSemidef := fun γ hγ => (hext.subset hγ).1
  set K : (Fin m → ℝ) → Submodule ℝ (Fin N → ℝ) :=
    fun γ => LinearMap.ker (P.Aγ γ).mulVecLin with hK
  have hex : ∃ n, ∃ γ ∈ F, Module.finrank ℝ (K γ) = n := ⟨_, hne.some, hne.some_mem, rfl⟩
  obtain ⟨γ0, hγ0, hγ0n⟩ := Nat.find_spec hex
  have hmin : ∀ γ ∈ F, Module.finrank ℝ (K γ0) ≤ Module.finrank ℝ (K γ) := by
    intro γ hγ
    rw [hγ0n]
    exact Nat.find_min' hex ⟨γ, hγ, rfl⟩
  -- the kernel at γ0 is contained in every kernel
  have hsub : ∀ γ ∈ F, K γ0 ≤ K γ := by
    intro γ hγ
    set μ := (1 / 2 : ℝ) • γ0 + (1 / 2 : ℝ) • γ with hμ
    have hμF : μ ∈ F := hconv hγ0 hγ (by norm_num) (by norm_num) (by norm_num)
    have hboth : ∀ v ∈ K μ, v ∈ K γ0 ∧ v ∈ K γ := by
      intro v hv
      simp only [hK, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
      rw [hμ, QCQPLemma2Aux.Aγ_mid] at hv
      exact QCQPLemma2Aux.ker_of_half (hpsd γ0 hγ0) (hpsd γ hγ) hv
    have hle : K μ ≤ K γ0 := fun v hv => (hboth v hv).1
    have heq : K μ = K γ0 := Submodule.eq_of_le_of_finrank_le hle (hmin μ hμF)
    rw [← heq]
    exact fun v hv => (hboth v hv).2
  -- a nonzero null vector at γ0
  have hdet : (P.Aγ γ0).det = 0 := by
    by_contra hd
    exact hnot ⟨γ0, hγ0, ((hpsd γ0 hγ0).posDef_iff_det_ne_zero).2 hd⟩
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hvV : v ∈ P.V F := by
    simp only [QCQP.V, Submodule.mem_iInf]
    intro γ hγ
    have : v ∈ K γ0 := by simp only [hK, LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hv
    exact hsub γ hγ this
  have hc0 : v ⬝ᵥ v ≠ 0 := fun h => hv0 (dotProduct_self_eq_zero.1 h)
  have hcnn : 0 ≤ v ⬝ᵥ v := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have hc : 0 < v ⬝ᵥ v := lt_of_le_of_ne hcnn (Ne.symm hc0)
  refine ⟨(Real.sqrt (v ⬝ᵥ v))⁻¹ • v, (P.V F).smul_mem _ hvV, ?_⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, inv_pow,
    Real.sq_sqrt hcnn]
  exact inv_mul_cancel₀ hc0

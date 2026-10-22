-- Prove2me | solution 1 for QCQPTightness.MultHull.psd_iff_kron
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:31:32.696393+00:00
-- url     : https://prove2.me/submissions/cdac2eb6-bd45-4f7d-840b-1d874895df0f

import Mathlib
import Definitions.Def_QCQPTightness_MultHull_Kron
set_option autoImplicit false
open QCQPTightness.MultHull Matrix

theorem solution {N m k n : ℕ} (P : QCQP N m) (h : k * n = N) (hk : 0 < k)
    (𝔸₀ : Matrix (Fin n) (Fin n) ℝ) (𝔸 : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hrep : P.IsKronRep h 𝔸₀ 𝔸) (γ : Fin m → ℝ) :
    (P.Aγ γ).PosSemidef ↔ (kronAγ 𝔸₀ 𝔸 γ).PosSemidef := by
  obtain ⟨_, _, hA0, hAi⟩ := hrep
  have hAγ : P.Aγ γ = (kronId k (kronAγ 𝔸₀ 𝔸 γ)).submatrix (blockEquiv h).symm (blockEquiv h).symm := by
    ext a b
    simp only [QCQP.Aγ, hA0, hAi, kronAγ, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply, kronId, Matrix.kroneckerMap_apply, smul_eq_mul]
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hAγ, posSemidef_submatrix_equiv (blockEquiv h).symm]
  set M := kronAγ 𝔸₀ 𝔸 γ
  have hone : (1 : Matrix (Fin k) (Fin k) ℝ).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self (1 : Matrix (Fin k) (Fin k) ℝ)
  constructor
  · intro hK
    have := hK.submatrix (fun b : Fin n => ((⟨0, hk⟩ : Fin k), b))
    convert this using 1
    ext a b
    simp [kronId, Matrix.kroneckerMap_apply]
  · intro hM
    exact Matrix.PosSemidef.kronecker hone hM

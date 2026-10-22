-- Prove2me | solution 1 for QMCProduct.HalfApprox.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T22:51:53.278768+00:00
-- url     : https://prove2.me/submissions/5ae2f2a0-2337-4181-8666-6d46d7c528b7

import Mathlib
import Definitions.Def_QMCProduct_HalfApprox_Basic

open QMCProduct.HalfApprox QAlgorithms
open scoped ComplexOrder Matrix

namespace QMC9Aux

lemma pauli1_herm (a : Fin 4) : (pauli1 a).IsHermitian := by
  unfold pauli1
  split_ifs
  · exact Matrix.isHermitian_one
  all_goals
    ext x y
    cases x <;> cases y <;> simp [pauliX, pauliY, pauliZ, Matrix.conjTranspose_apply]

lemma kron_herm {n : ℕ} (M : Fin n → Matrix Bool Bool ℂ) (hM : ∀ q, (M q).IsHermitian) :
    (kronAll M).IsHermitian := by
  ext y z
  simp only [kronAll, Matrix.conjTranspose_apply, Matrix.of_apply, star_prod]
  exact Finset.prod_congr rfl fun q _ => (hM q).apply (y q) (z q)

lemma poly_herm {n k : ℕ} (P : Op n) (hP : IsPauliPoly k P) : P.IsHermitian := by
  obtain ⟨c, -, rfl⟩ := hP
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  congr 1
  exact (kron_herm _ (fun q => pauli1_herm (s q))).eq

end QMC9Aux

open QMC9Aux

theorem solution {n : ℕ} (k : ℕ) (H : Op n) (hH : H.IsHermitian)
    (ρt : Op n) (hopt : IsOptimalLk k H ρt) :
    ∀ σ : Op n, QAlgorithms.IsDensityMatrix σ →
      (H * σ).trace.re ≤ (H * ρt).trace.re := by
  intro σ hσ
  refine hopt.2 σ ⟨hσ.1.isHermitian, hσ.2, fun P hP => ?_⟩
  have hPh := poly_herm P hP
  have h1 : (σ * P * P).trace = (P * σ * Pᴴ).trace := by
    rw [hPh.eq, Matrix.trace_mul_cycle]
  rw [h1]
  have h2 := (hσ.1.mul_mul_conjTranspose_same P).trace_nonneg
  exact (Complex.nonneg_iff.1 h2).1

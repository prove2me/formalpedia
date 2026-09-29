-- Prove2me | solution 1 for SparseApprox.Greedy.nnz_initial_eq_opt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:36:12.073868+00:00
-- url     : https://prove2.me/submissions/2e314087-1d07-4666-9fab-fb8c576484cf

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem aux_nieo_toEuc {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin A x = ∑ j, x j • colE A j := by
  ext i
  simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, colE, mul_comm]

theorem aux_nieo_scale (y : ℝ) {m : ℕ} (c : EuclideanSpace ℝ (Fin m)) :
    (y * ‖c‖) • normalizeVec c = y • c := by
  unfold normalizeVec
  by_cases hc : c = 0
  · subst hc; simp
  · rw [smul_smul, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc), mul_one]

theorem aux_nieo_scale' (y : ℝ) {m : ℕ} (c : EuclideanSpace ℝ (Fin m)) :
    (y * ‖c‖⁻¹) • c = y • normalizeVec c := by
  unfold normalizeVec
  rw [smul_smul]

end SparseApprox.Greedy

open SparseApprox.Greedy
open scoped InnerProductSpace

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (initState A b).col b (ε / 2) u) :
    nnz u = optSparsity A b (ε / 2) := by
  obtain ⟨hfeas, hmin⟩ := hu
  simp only [initState] at hfeas hmin
  -- x from u
  set x : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun j => u j * ‖colE A j‖⁻¹) with hx
  have hxmem : nnz x ∈ {N : ℕ | ∃ x : EuclideanSpace ℝ (Fin n),
      nnz x = N ∧ ‖Matrix.toEuclideanLin A x - b‖ ≤ ε / 2} := by
    refine ⟨x, rfl, ?_⟩
    rw [aux_nieo_toEuc]
    convert hfeas using 3
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hx]
    exact aux_nieo_scale' _ _
  have hxle : nnz x ≤ nnz u := by
    unfold nnz
    apply Finset.card_le_card
    intro j hj
    simp only [nzSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    intro h0
    apply hj
    rw [hx]
    simp [h0]
  unfold optSparsity
  apply le_antisymm
  · have hne : Set.Nonempty {N : ℕ | ∃ x : EuclideanSpace ℝ (Fin n),
        nnz x = N ∧ ‖Matrix.toEuclideanLin A x - b‖ ≤ ε / 2} := ⟨_, hxmem⟩
    obtain ⟨x', hx'1, hx'2⟩ := Nat.sInf_mem hne
    rw [← hx'1]
    set v : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun j => x' j * ‖colE A j‖) with hv
    have hvfeas : ‖(∑ i, v i • normalizeVec (colE A i)) - b‖ ≤ ε / 2 := by
      rw [aux_nieo_toEuc] at hx'2
      convert hx'2 using 3
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hv]
      exact aux_nieo_scale _ _
    refine le_trans (hmin v hvfeas) ?_
    unfold nnz
    apply Finset.card_le_card
    intro j hj
    simp only [nzSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    intro h0
    apply hj
    rw [hv]
    simp [h0]
  · exact le_trans (Nat.sInf_le hxmem) hxle

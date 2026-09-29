-- Prove2me | solution 1 for TaylorWiles.isEigenIdempotent_smul_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0f8df012-5e0c-5ae4-b44d-2a17d5bdef84

import Mathlib
import Definitions.Def_Deformations_LocalSplitting
import Theorems.Thm_Matrix_sub_smul_one_mul_sub_smul_one_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TaylorWiles_isEigenIdempotent_smul_sub

set_option autoImplicit false

universe u v

open Matrix

namespace Ws14Port
open TaylorWiles

variable {A : Type u} [CommRing A]

theorem idem_mul_compl {e : Matrix (Fin 2) (Fin 2) A} (he : e * e = e) : e * ((1 : Matrix (Fin 2) (Fin 2) A) - e) = 0 := by
  rw [mul_sub, mul_one, he, sub_self]

theorem trace_one_fin_two : (1 : Matrix (Fin 2) (Fin 2) A).trace = 2 := by
  rw [Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat]

theorem trace_compl {e : Matrix (Fin 2) (Fin 2) A} (htr : e.trace = 1) : ((1 : Matrix (Fin 2) (Fin 2) A) - e).trace = 1 := by
  rw [Matrix.trace_sub, trace_one_fin_two, htr]
  ring

theorem eq_smul_add_smul {M e : Matrix (Fin 2) (Fin 2) A} {a b : A} (h : IsEigenIdempotent M a b e) :
    M = a • e + b • ((1 : Matrix (Fin 2) (Fin 2) A) - e) := by
  have hM : M = M * e + M * ((1 : Matrix (Fin 2) (Fin 2) A) - e) := by
    rw [← mul_add]
    rw [show e + ((1 : Matrix (Fin 2) (Fin 2) A) - e) = 1 by abel, mul_one]
  rw [hM, h.mul_left, h.mul_right]

theorem mul_self_eq (M : Matrix (Fin 2) (Fin 2) A) : M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) A) := by
  rw [← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne, ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true,
    Fin.one_eq_zero_iff, mul_zero, mul_one]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

end Ws14Port

open TaylorWiles in
theorem solution {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A} {a b v : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) (hv : v * (a - b) = 1) :
    TaylorWiles.IsEigenIdempotent M a b (v • (M - b • (1 : Matrix (Fin 2) (Fin 2) A))) := by
  have hfact := Matrix.sub_smul_one_mul_sub_smul_one_eq_zero htr hdet
  have hfact' : (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) * (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) = 0 :=
    Matrix.sub_smul_one_mul_sub_smul_one_eq_zero (by rw [htr]; ring) (by rw [hdet]; ring)
  have hexp : M - a • (1 : Matrix (Fin 2) (Fin 2) A) + (a - b) • (1 : Matrix (Fin 2) (Fin 2) A) = M - b • (1 : Matrix (Fin 2) (Fin 2) A) := by
    rw [sub_smul]; abel
  have hsq : (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) * (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) =
      (a - b) • (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) := by
    nth_rewrite 2 [← hexp]
    rw [mul_add, hfact', mul_smul_comm, mul_one, zero_add]
  have hMe : M * (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) = a • (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) := by
    have hexp2 : M - a • (1 : Matrix (Fin 2) (Fin 2) A) + a • (1 : Matrix (Fin 2) (Fin 2) A) = M := by abel
    nth_rewrite 1 [← hexp2]
    rw [add_mul, hfact, smul_mul_assoc, one_mul, zero_add]
  have hMe' : M * (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) = b • (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) := by
    have hexp2 : M - b • (1 : Matrix (Fin 2) (Fin 2) A) + b • (1 : Matrix (Fin 2) (Fin 2) A) = M := by abel
    nth_rewrite 1 [← hexp2]
    rw [add_mul, hfact', smul_mul_assoc, one_mul, zero_add]
  have hsub : (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) - (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) = (a - b) • (1 : Matrix (Fin 2) (Fin 2) A) := by
    rw [sub_smul]; abel
  have hsum : v • (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) + (-v) • (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) = 1 := by
    rw [neg_smul, ← sub_eq_add_neg, ← smul_sub, hsub, smul_smul, hv, one_smul]
  have hcompl : (1 : Matrix (Fin 2) (Fin 2) A) - v • (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) = (-v) • (M - a • (1 : Matrix (Fin 2) (Fin 2) A)) := by
    nth_rewrite 1 [← hsum]
    abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [smul_mul_assoc, mul_smul_comm, hsq, smul_smul, smul_smul, mul_assoc, hv, mul_one]
  · rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, htr, Ws14Port.trace_one_fin_two,
      smul_eq_mul, smul_eq_mul, show a + b - b * 2 = a - b by ring, hv]
  · rw [mul_smul_comm, hMe, smul_smul, smul_smul, mul_comm v a]
  · rw [hcompl, mul_smul_comm, hMe', smul_smul, smul_smul, mul_comm b (-v)]

end S_TaylorWiles_isEigenIdempotent_smul_sub
end P2MW
export P2MW.S_TaylorWiles_isEigenIdempotent_smul_sub (solution)

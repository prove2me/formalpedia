-- Prove2me | solution 1 for WeierstrassEllipticZeta.idempotent_matrix_support_rank
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T14:39:00.222234+00:00
-- url     : https://prove2.me/submissions/4c2dc177-bd3e-4f98-a48a-5b0c5c8083f0

import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Rank

open scoped Classical



theorem solution
    (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (V : Type*) [Fintype V]
    (E : Matrix (Fin n) (Fin n) K) (w : V → ℕ) (f : V → K)
    (hE : IsIdempotentElem E)
    (htrace : E.trace = ∑ v : V, (w v : K) * (if f v = 0 then 0 else 1)) :
    E.rank = ∑ v ∈ Finset.univ.filter (fun v : V => f v ≠ 0), w v ∧
      Module.finrank K (LinearMap.ker E.mulVecLin) =
        n - ∑ v ∈ Finset.univ.filter (fun v : V => f v ≠ 0), w v := by
  classical
  have hL : IsIdempotentElem E.toLin' := by
    change E.toLin' * E.toLin' = E.toLin'
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE.eq]
  have htr : E.trace = (E.rank : K) := by
    rw [← Matrix.trace_toLin'_eq E]
    exact (LinearMap.IsIdempotentElem.isProj_range E.toLin' hL).trace
  have hcast : (E.rank : K) =
      ((∑ v ∈ Finset.univ.filter (fun v : V => f v ≠ 0), w v : ℕ) : K) := by
    rw [← htr, htrace, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : f v = 0 <;> simp [h]
  have hr : E.rank = ∑ v ∈ Finset.univ.filter (fun v : V => f v ≠ 0), w v :=
    Nat.cast_injective hcast
  refine ⟨hr, ?_⟩
  have hdim := LinearMap.finrank_range_add_finrank_ker E.mulVecLin
  change E.rank + Module.finrank K (LinearMap.ker E.mulVecLin) = _ at hdim
  simp only [Module.finrank_pi, Fintype.card_fin] at hdim
  omega


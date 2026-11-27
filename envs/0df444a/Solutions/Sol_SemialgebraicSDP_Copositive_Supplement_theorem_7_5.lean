-- Prove2me | solution 1 for SemialgebraicSDP.Copositive.Supplement.theorem_7_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:31:32.565995+00:00
-- url     : https://prove2.me/submissions/f6e4f334-dda6-46ee-bb9d-14dae1418964

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems
import Definitions.Def_SemialgebraicSDP_Copositive_Supplement_QuadraticSet

open SemialgebraicSDP
open SemialgebraicSDP.Copositive
open SemialgebraicSDP.Copositive.Supplement

open MurtyKabadi.Reduction

/-- Theorem 7.5 (Parrilo 2003, p. 316). Let `A₁, …, Aₘ` be real symmetric `n × n` matrices.
Assume there exist real symmetric positive semidefinite `Qᵢ` and real `rᵢⱼ ≥ 0` (`i < j`) such
that `∑ᵢ Qᵢ(x)Aᵢ(x) + ∑_{i<j} rᵢⱼ Aᵢ(x)Aⱼ(x) < 0` for every nonzero `x ∈ ℝⁿ` (7.5). Then the
set `𝒜` of (7.3) is empty. -/
theorem solution {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).IsSymm)
    (Qm : Fin m → Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i, (Qm i).PosSemidef)
    (r : Fin m → Fin m → ℝ) (hr : ∀ i j, i < j → 0 ≤ r i j)
    (h75 : ∀ x : Fin n → ℝ, x ≠ 0 → quarticLHS A Qm r x < 0) :
    setA A = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx, hnorm⟩
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hnorm
      have hlt := h75 x hx0
      have hQx : ∀ i, 0 ≤ Q (Qm i) x := by
        intro i
        have h := (hQ i).dotProduct_mulVec_nonneg x
        simpa [Q] using h
      have h1 : 0 ≤ quarticLHS A Qm r x := by
        unfold quarticLHS
        refine add_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hQx i) (hx i))
          (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j hj => ?_)
        have hij : i < j := (Finset.mem_filter.mp hj).2
        exact mul_nonneg (mul_nonneg (hr i j hij) (hx i)) (hx j)
      exact absurd hlt (not_lt.mpr h1)

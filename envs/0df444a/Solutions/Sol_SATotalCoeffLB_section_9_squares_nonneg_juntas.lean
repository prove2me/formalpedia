-- Prove2me | solution 1 for SATotalCoeffLB.section_9_squares_nonneg_juntas
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T07:45:38.444969+00:00
-- url     : https://prove2.me/submissions/98c79b6b-019f-4a5c-97c3-d6b3bb9e74fb

import Mathlib
import Definitions.Def_SATotalCoeffLB_DependsOnAtMost

open SATotalCoeffLB

namespace P2MHole01_cb3d1256
universe u_1
theorem solution {V : Type u_1} [inst : Fintype V] (k : ℕ) (f : CubeFn V) (g : ℝ → ℝ)
  (hf : DependsOnAtMost k f) : DependsOnAtMost k fun (x : V → ZMod (2 : ℕ)) => g (f x) := by
  obtain ⟨S, hcard, hdep⟩ := hf
  refine ⟨S, hcard, ?_⟩
  intro x y hxy
  exact congr_arg g (hdep x y hxy)
end P2MHole01_cb3d1256

/-! `f` depends on at most `k` variables and `g : ℝ → ℝ` ⇒ `g ∘ f` does too. -/
-- riskiest
lemma dep_pointwise {V : Type*} [Fintype V] (k : ℕ) (f : CubeFn V) (g : ℝ → ℝ)
    (hf : DependsOnAtMost k f) : DependsOnAtMost k (fun x => g (f x)) := by
  (first | exact P2MHole01_cb3d1256.solution k f g hf | (apply P2MHole01_cb3d1256.solution <;> assumption))

/-- A square is pointwise nonnegative. -/
lemma sq_nonneg_fn {V : Type*} [Fintype V] (h : CubeFn V) : ∀ x, 0 ≤ h x ^ 2 := by
  exact fun x => sq_nonneg (h x)

/-- Pointwise: `f ≥ 0` ⇒ `(sqrt (f x)) ^ 2 = f x`. -/
lemma sqrt_sq_eq {V : Type*} [Fintype V] (f : CubeFn V) (h : ∀ x, 0 ≤ f x) :
    ∀ x, (Real.sqrt (f x)) ^ 2 = f x := by
  exact fun x => Real.sq_sqrt (h x)

/-- **Section 9, squares of `k`-juntas are the nonnegative `k`-juntas**, p.50 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).

In the Boolean quotient ring, an element is the square of a polynomial depending on at most `k`
variables if and only if it depends on at most `k` variables and is nonnegative at every point of
the cube. (This rewrites the identity of Theorem 3, item 2, as Eq. (25).)

**Formalization Note** Stated for an arbitrary finite set of variables `V`. -/
theorem solution {V : Type*} [Fintype V] (k : ℕ) (f : CubeFn V) :
    (∃ h : CubeFn V, DependsOnAtMost k h ∧ f = h ^ 2) ↔
      (DependsOnAtMost k f ∧ ∀ x, 0 ≤ f x) := by
  constructor
  · rintro ⟨h, hdep, rfl⟩
    constructor
    · have hd : DependsOnAtMost k (fun x => (h x) ^ 2) := dep_pointwise k h (fun t => t ^ 2) hdep
      have hsq : (fun x : V → ZMod 2 => (h x) ^ 2) = h ^ 2 := by
        ext x
        simp [pow_two]
      exact hsq ▸ hd
    · exact sq_nonneg_fn h
  · rintro ⟨fdep, fnonneg⟩
    refine ⟨fun x => Real.sqrt (f x), dep_pointwise k f Real.sqrt fdep, ?eq⟩
    · ext x
      simpa [pow_two] using (sqrt_sq_eq f fnonneg x).symm

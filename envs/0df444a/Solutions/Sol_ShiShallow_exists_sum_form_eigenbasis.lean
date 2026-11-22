-- Prove2me | solution 1 for ShiShallow.exists_sum_form_eigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T01:26:23.380768+00:00
-- url     : https://prove2.me/submissions/c1cd4c2b-7963-438a-affe-f1e12f3e6d10

/-
Construction of an orthonormal, Parseval, eigenvalue-adapted basis for a Hermitian
matrix indexed by bit strings, delivered in explicit-sum language.

Built against Mathlib at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow

/-- The `EuclideanSpace` inner product, written as an explicit sum with the complex
conjugate on the FIRST argument.  This is the shape in which the main statement is
phrased. -/
private lemma shiEx1_inner_as_sum {w : ℕ} (x y : EuclideanSpace ℂ (Bits w)) :
    inner ℂ x y
      = ∑ t : Bits w, (starRingEnd ℂ) (WithLp.ofLp x t) * WithLp.ofLp y t := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro t _
  first
    | (rw [RCLike.inner_apply]; exact mul_comm _ _; done)
    | (rw [RCLike.inner_apply']; done)
    | (simp only [RCLike.inner_apply]; exact mul_comm _ _; done)

theorem solution {w : ℕ}
    (M : Matrix (Bits w) (Bits w) ℂ) (hM : M.IsHermitian) :
    ∃ u : Bits w → (Bits w → ℂ),
      (∀ i j, (∑ y : Bits w, (starRingEnd ℂ) (u i y) * u j y) = if i = j then 1 else 0)
      ∧ (∀ z : Bits w → ℂ,
          (∑ i : Bits w, ‖∑ y : Bits w, (starRingEnd ℂ) (z y) * u i y‖ ^ 2)
            = ∑ y : Bits w, ‖z y‖ ^ 2)
      ∧ (∀ i, Matrix.mulVec M (u i)
          = fun y => ((hM.eigenvalues i : ℝ) : ℂ) * u i y) := by
  refine ⟨fun i => WithLp.ofLp (hM.eigenvectorBasis i), ?_, ?_, ?_⟩
  · -- orthonormality
    intro i j
    have hOrth : inner ℂ (hM.eigenvectorBasis i) (hM.eigenvectorBasis j)
        = if i = j then (1 : ℂ) else 0 :=
      orthonormal_iff_ite.mp (hM.eigenvectorBasis).orthonormal i j
    rw [shiEx1_inner_as_sum] at hOrth
    first
      | (exact hOrth; done)
      | (simpa using hOrth; done)
      | (convert hOrth using 2; done)
  · -- Parseval
    intro z
    have hPar := (hM.eigenvectorBasis).sum_sq_norm_inner_left (WithLp.toLp 2 z)
    rw [EuclideanSpace.norm_sq_eq] at hPar
    simp only [shiEx1_inner_as_sum, WithLp.ofLp_toLp, PiLp.toLp_apply] at hPar
    first
      | (exact hPar; done)
      | (simpa using hPar; done)
  · -- the eigenvalue relation
    intro i
    funext t
    have hEig := congrFun (hM.mulVec_eigenvectorBasis i) t
    first
      | (rw [Pi.smul_apply, Complex.real_smul] at hEig)
      | (simp only [Pi.smul_apply, Complex.real_smul] at hEig)
      | (simp only [Complex.real_smul] at hEig)
      | skip
    first
      | (exact hEig; done)
      | (simpa using hEig; done)

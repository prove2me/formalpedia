-- Prove2me | solution 1 for ZhangCFL.psi_eq_trAbsPow
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:51:47.671386+00:00
-- url     : https://prove2.me/submissions/c0d8755f-c868-42a3-88f7-8b286423201e

import Mathlib
import Definitions.Def_OgawaNagaoka_matPow
import Definitions.Def_ZhangCFL_Psi
import Definitions.Def_ZhangCFL_trAbsPow
open scoped ComplexOrder

open ZhangCFL OgawaNagaoka in
theorem solution {n : Type} [Fintype n] [DecidableEq n]
    (p q s : ℝ) (K A B : Matrix n n ℂ) (hA : A.PosDef) (hB : B.PosDef) :
    Psi p q s K A B = trAbsPow (2 * s) (matPow A (p / 2) * K * matPow B (q / 2)) := by
  have spos : ∀ (M : Matrix n n ℂ), M.PosDef → ∀ x ∈ spectrum ℝ M, 0 < x := by
    intro M hM x hx
    rw [hM.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hM.eigenvalues_pos i
  have hcont : ∀ (M : Matrix n n ℂ), M.PosDef → ∀ r : ℝ,
      ContinuousOn (fun x : ℝ => x ^ r) (spectrum ℝ M) := fun M hM r x hx =>
    (Real.continuousAt_rpow_const x r (Or.inl (spos M hM x hx).ne')).continuousWithinAt
  have hsq : ∀ (M : Matrix n n ℂ), M.PosDef → ∀ r : ℝ,
      matPow M (r / 2) * matPow M (r / 2) = matPow M r := by
    intro M hM r
    unfold matPow
    rw [← cfc_mul _ _ M (hcont M hM _) (hcont M hM _)]
    apply cfc_congr
    intro x hx
    show x ^ (r / 2) * x ^ (r / 2) = x ^ r
    rw [← Real.rpow_add (spos M hM x hx)]
    congr 1
    ring
  have hsa : ∀ (M : Matrix n n ℂ) (r : ℝ), (matPow M r).conjTranspose = matPow M r := by
    intro M r
    exact (IsSelfAdjoint.cfc (f := fun x : ℝ => x ^ r) (a := M))
  unfold Psi trAbsPow
  have e : (matPow A (p / 2) * K * matPow B (q / 2)).conjTranspose * (matPow A (p / 2) * K * matPow B (q / 2)) =
      matPow B (q / 2) * K.conjTranspose * matPow A p * K * matPow B (q / 2) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hsa A, hsa B, ← hsq A hA p]
    simp only [mul_assoc]
  rw [e, show 2 * s / 2 = s by ring]

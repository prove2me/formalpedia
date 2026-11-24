-- Prove2me | solution 1 for WeilConjectures.exists_qladic_lower_half_cohomology_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:48:24.014204+00:00
-- url     : https://prove2.me/submissions/00c61011-7007-4b97-898e-0934ee41c9cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_exists_qladic_lower_half_dual_frobenius_of_ge_two

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

section LowerHalfDualToBilinear

private lemma eq_zero_of_forall_dual_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] {x : V} (hx : ∀ φ : Module.Dual K V, φ x = 0) : x = 0 := by
  let b := Module.finBasis K V
  apply b.repr.injective
  rw [map_zero]
  ext j
  simpa [Module.Basis.coord_apply] using hx (b.coord j)

/-- Reconstruct a twisted-equivariant nondegenerate bilinear form from a dual-Frobenius
equivalence `eMid : V ≃ₗ Dual V` with `eMid (F x) (F y) = q * eMid x y`. -/
private lemma exists_bilin_of_dual_frobenius {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (F : V ≃ₗ[K] V) (q : K)
    (eMid : V ≃ₗ[K] Module.Dual K V)
    (heq : ∀ x y : V, eMid (F x) (F y) = q * eMid x y) :
    ∃ Bmid : V →ₗ[K] V →ₗ[K] K,
      (∀ x y : V, Bmid (F x) (F y) = q * Bmid x y) ∧
      ((∀ x : V, (∀ y : V, Bmid x y = 0) → x = 0) ∧
       (∀ y : V, (∀ x : V, Bmid x y = 0) → y = 0)) := by
  refine ⟨eMid.toLinearMap, heq, ?_, ?_⟩
  · intro x hx
    apply eMid.injective
    apply LinearMap.ext
    intro y
    simpa using hx y
  · intro y hy
    apply eq_zero_of_forall_dual_eq_zero (K := K)
    intro φ
    have hx := hy (eMid.symm φ)
    simpa [LinearEquiv.apply_symm_apply] using hx

end LowerHalfDualToBilinear

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    ∃ (V : ℕ → Type) (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module (Padic ℓ) (V i))
      (_ : ∀ i, Module.Finite (Padic ℓ) (V i))
      (F : ∀ i, V i ≃ₗ[Padic ℓ] V i)
      (Bmid : V n →ₗ[Padic ℓ] V n →ₗ[Padic ℓ] Padic ℓ),
      (∀ m : ℕ, 0 < m →
        (pointCount p f m : Padic ℓ) =
          1 + ((Nat.card k : Padic ℓ) ^ n) ^ m +
            (-1 : Padic ℓ) ^ n *
              LinearMap.trace (Padic ℓ) (V n) ((F n : V n →ₗ[Padic ℓ] V n) ^ m) +
            ∑ i ∈ Finset.Ico 1 n,
              (-1 : Padic ℓ) ^ i *
                (LinearMap.trace (Padic ℓ) (V i) ((F i : V i →ₗ[Padic ℓ] V i) ^ m) +
                 ((Nat.card k : Padic ℓ) ^ n) ^ m *
                   LinearMap.trace (Padic ℓ) (V i) (((F i).symm : V i →ₗ[Padic ℓ] V i) ^ m))) ∧
      (∀ x y : V n, Bmid (F n x) (F n y) = (Nat.card k : Padic ℓ) ^ n * Bmid x y) ∧
      ((∀ x : V n, (∀ y : V n, Bmid x y = 0) → x = 0) ∧
       (∀ y : V n, (∀ x : V n, Bmid x y = 0) → y = 0)) ∧
      (∀ i, 1 ≤ i → i < n → ∃ W : ℤ[X], W.Monic ∧ aeval (F i : V i →ₗ[Padic ℓ] V i) W = 0 ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ = (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) ∧
      (∃ W : ℤ[X], W.Monic ∧ aeval (F n : V n →ₗ[Padic ℓ] V n) W = 0 ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((n : ℝ) / 2)) := by
  obtain ⟨V, hVAdd, hVMod, hVFin, F, eMid, htr, heq, hWlow, hWmid⟩ :=
    WeilConjectures.exists_qladic_lower_half_dual_frobenius_of_ge_two p k n hn X f hproj ℓ hℓp
  let _ : ∀ i, AddCommGroup (V i) := hVAdd
  let _ : ∀ i, Module (Padic ℓ) (V i) := hVMod
  let _ : ∀ i, Module.Finite (Padic ℓ) (V i) := hVFin
  obtain ⟨Bmid, hBmid_eq, hBmid_nondeg⟩ :=
    exists_bilin_of_dual_frobenius (F n) ((Nat.card k : Padic ℓ) ^ n) eMid heq
  exact ⟨V, hVAdd, hVMod, hVFin, F, Bmid, htr, hBmid_eq, hBmid_nondeg, hWlow, hWmid⟩

-- Prove2me | solution 1 for WeilConjectures.exists_integral_pid_cohomology_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T20:55:27.88581+00:00
-- url     : https://prove2.me/submissions/ce5e455a-c93b-4a72-a646-890a7eb95c91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_exists_deligne_integral_pid_cohomology_of_ge_two

open AlgebraicGeometry CategoryTheory
open WeilConjectures

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsPrincipalIdealRing R) (_ : CharZero R)
      (M : ℕ → Type) (_ : ∀ i, AddCommGroup (M i)) (_ : ∀ i, Module R (M i))
      (_ : ∀ i, Module.Finite R (M i)) (_ : ∀ i, Module.IsTorsionFree R (M i))
      (F : ∀ i, M i →ₗ[R] M i)
      (cup : ∀ i, i ≤ n → M i →ₗ[R] M (2 * n - i) →ₗ[R] M (2 * n))
      (tr : M (2 * n) →ₗ[R] R),
      (∀ m : ℕ, 0 < m →
        (pointCount p f m : R) =
          ∑ i ∈ Finset.range (2 * n + 1), (-1 : R) ^ i * LinearMap.trace R (M i) (F i ^ m)) ∧
      (∀ z : M (2 * n), tr (F (2 * n) z) = (Nat.card k : R) ^ n * tr z) ∧
      (∀ i (hi : i ≤ n) (x : M i) (y : M (2 * n - i)),
        cup i hi (F i x) (F (2 * n - i) y) = F (2 * n) (cup i hi x y)) ∧
      (∀ i (hi : i ≤ n),
        (∀ x : M i, (∀ y : M (2 * n - i), tr (cup i hi x y) = 0) → x = 0) ∧
        (∀ y : M (2 * n - i), (∀ x : M i, tr (cup i hi x y) = 0) → y = 0)) := by
  obtain ⟨R, hRComm, hRDom, hRPID, hRChar0, M, hMAdd, hMMod, hMFin, hMFree, F, cup, tr,
      htr, htopF, hcupF, hnondeg, _, _, _⟩ :=
    WeilConjectures.exists_deligne_integral_pid_cohomology_of_ge_two p k n hn X f hproj
  let _ : CommRing R := hRComm
  let _ : IsDomain R := hRDom
  let _ : ∀ i, AddCommGroup (M i) := hMAdd
  let _ : ∀ i, Module R (M i) := hMMod
  let _ : ∀ i, Module.Free R (M i) := hMFree
  exact ⟨R, hRComm, hRDom, hRPID, hRChar0, M, hMAdd, hMMod, hMFin, fun _ => inferInstance,
    F, cup, tr, htr, htopF, hcupF, hnondeg⟩

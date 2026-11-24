-- Prove2me | solution 1 for WeilConjectures.exists_qladic_lower_half_vconj_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T00:21:05.329254+00:00
-- url     : https://prove2.me/submissions/e55ade88-85eb-4183-a8b7-168c44df161e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_exists_qladic_lower_half_vconj_of_dim_two
import Theorems.Thm_WeilConjectures_exists_qladic_lower_half_vconj_of_dim_ge_three

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    ∃ (V : ℕ → Type) (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module (Padic ℓ) (V i))
      (_ : ∀ i, Module.Finite (Padic ℓ) (V i))
      (F : ∀ i, V i ≃ₗ[Padic ℓ] V i)
      (gMid : V n ≃ₗ[Padic ℓ] V n),
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
      (gMid.conj (F n : V n →ₗ[Padic ℓ] V n) =
        (((Nat.card k : Padic ℓ) ^ n) • ((F n).symm : V n →ₗ[Padic ℓ] V n))) ∧
      (∀ i, 1 ≤ i → i ≤ n → ∃ W : ℤ[X], W.Monic ∧ aeval (F i : V i →ₗ[Padic ℓ] V i) W = 0 ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ = (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) := by
  rcases eq_or_lt_of_le hn with rfl | hlt
  · obtain ⟨V, hVAdd, hVMod, hVFin, F, gMid, htr, hg, hW⟩ :=
      WeilConjectures.exists_qladic_lower_half_vconj_of_dim_two p k X f hproj ℓ hℓp
    exact ⟨V, hVAdd, hVMod, hVFin, F, gMid, htr, hg, hW⟩
  · have hn3 : 3 ≤ n := Nat.succ_le_of_lt hlt
    obtain ⟨V, hVAdd, hVMod, hVFin, F, gMid, htr, hg, hW⟩ :=
      WeilConjectures.exists_qladic_lower_half_vconj_of_dim_ge_three p k n hn3 X f hproj ℓ hℓp
    exact ⟨V, hVAdd, hVMod, hVFin, F, gMid, htr, hg, hW⟩

-- Prove2me | solution 1 for WeilConjectures.exists_poincare_duality_cohomology_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:39:12.05929+00:00
-- url     : https://prove2.me/submissions/7c4c58ec-79c3-4b99-9a72-46a911a4d32d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_exists_weil_cohomology_cup_trace_of_ge_two

open AlgebraicGeometry CategoryTheory
open WeilConjectures

section PoincareDualityFromCupTrace

private lemma exists_dualEquiv_of_nondeg {K U W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [Module.Finite K U]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (FU : U →ₗ[K] U) (FW : W →ₗ[K] W) (a : K)
    (B : U →ₗ[K] W →ₗ[K] K)
    (hL : ∀ x : U, (∀ y : W, B x y = 0) → x = 0)
    (hR : ∀ y : W, (∀ x : U, B x y = 0) → y = 0)
    (hF : ∀ (x : U) (y : W), B (FU x) (FW y) = a * B x y) :
    ∃ e : U ≃ₗ[K] Module.Dual K W, ∀ (x : U) (y : W), e (FU x) (FW y) = a * e x y := by
  have hinjL : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    apply hL x
    intro y
    have hxy := congrArg (fun φ : Module.Dual K W => φ y) (LinearMap.mem_ker.mp hx)
    exact hxy
  have hinjR : Function.Injective B.flip := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    apply hR y
    intro x
    have hxy := congrArg (fun φ : Module.Dual K U => φ x) (LinearMap.mem_ker.mp hy)
    exact hxy
  have hle1 : Module.finrank K U ≤ Module.finrank K W := by
    have h1 := LinearMap.finrank_le_finrank_of_injective hinjL
    rwa [Subspace.dual_finrank_eq] at h1
  have hle2 : Module.finrank K W ≤ Module.finrank K U := by
    have h2 := LinearMap.finrank_le_finrank_of_injective hinjR
    rwa [Subspace.dual_finrank_eq] at h2
  have hfin : Module.finrank K U = Module.finrank K (Module.Dual K W) := by
    rw [Subspace.dual_finrank_eq]
    exact le_antisymm hle1 hle2
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinjL
  exact ⟨LinearEquiv.ofBijective B ⟨hinjL, hsurj⟩, hF⟩

end PoincareDualityFromCupTrace

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (V : ℕ → Type) (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module K (V i))
      (_ : ∀ i, Module.Finite K (V i))
      (F : ∀ i, V i →ₗ[K] V i),
      (∀ m : ℕ, 0 < m →
        (pointCount p f m : K) =
          ∑ i ∈ Finset.range (2 * n + 1), (-1 : K) ^ i * LinearMap.trace K (V i) (F i ^ m)) ∧
      (∀ i ≤ 2 * n, ∃ e : V i ≃ₗ[K] Module.Dual K (V (2 * n - i)),
        ∀ (x : V i) (y : V (2 * n - i)),
          e (F i x) (F (2 * n - i) y) = (Nat.card k : K) ^ n * e x y) := by
  obtain ⟨K, hKField, hKChar0, V, hVAdd, hVMod, hVFin, F, cup, tr, htr, htopF, hcupF, hnondeg⟩ :=
    WeilConjectures.exists_weil_cohomology_cup_trace_of_ge_two p k n hn X f hproj
  let _ : Field K := hKField
  let _ : CharZero K := hKChar0
  let _ : ∀ i, AddCommGroup (V i) := hVAdd
  let _ : ∀ i, Module K (V i) := hVMod
  let _ : ∀ i, Module.Finite K (V i) := hVFin
  refine ⟨K, hKField, hKChar0, V, hVAdd, hVMod, hVFin, F, htr, ?_⟩
  intro i hi2n
  let pair : ∀ j (hj : j ≤ n), V j →ₗ[K] V (2 * n - j) →ₗ[K] K :=
    fun j hj => (cup j hj).compr₂ tr
  have hpair_eq : ∀ j (hj : j ≤ n) (x : V j) (y : V (2 * n - j)),
      pair j hj x y = tr (cup j hj x y) := fun _ _ _ _ => rfl
  have hpair_F : ∀ j (hj : j ≤ n) (x : V j) (y : V (2 * n - j)),
      pair j hj (F j x) (F (2 * n - j) y) = (Nat.card k : K) ^ n * pair j hj x y := by
    intro j hj x y
    rw [hpair_eq, hpair_eq, hcupF j hj x y, htopF]
  by_cases hi : i ≤ n
  · exact exists_dualEquiv_of_nondeg (F i) (F (2 * n - i)) ((Nat.card k : K) ^ n)
      (pair i hi) (hnondeg i hi).1 (hnondeg i hi).2 (hpair_F i hi)
  · generalize hj_def : 2 * n - i = j
    have hj : j ≤ n := by omega
    have hi_eq : i = 2 * n - j := by omega
    clear hj_def
    subst hi_eq
    exact exists_dualEquiv_of_nondeg (F (2 * n - j)) (F j) ((Nat.card k : K) ^ n)
      (pair j hj).flip (hnondeg j hj).2 (hnondeg j hj).1 (fun x y => hpair_F j hj y x)

-- Prove2me | solution 1 for WeilConjectures.exists_qladic_lower_half_dual_frobenius_of_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:59:43.941875+00:00
-- url     : https://prove2.me/submissions/f3022a6a-9b76-4bfe-950b-edc2cf53de3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_WeilConjectures_exists_qladic_lower_half_conj_dual_of_ge_two

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

section ConjDualEvaluationBridge

/-- Evaluation form of dual-Frobenius equivariance from the `LinearEquiv.conj` intertwiner. -/
private lemma eval_equiv_of_conj_dual {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (F : V ≃ₗ[K] V) (q : K)
    (eMid : V ≃ₗ[K] Module.Dual K V)
    (hconj : eMid.conj (F : V →ₗ[K] V) = (q • (F.symm : V →ₗ[K] V)).dualMap) :
    ∀ x y : V, eMid (F x) (F y) = q * eMid x y := by
  intro x y
  have hx : eMid (F x) = (q • (F.symm : V →ₗ[K] V)).dualMap (eMid x) := by
    have := congrArg (fun h : Module.End K (Module.Dual K V) => h (eMid x)) hconj
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] at this
    exact this
  calc
    eMid (F x) (F y)
        = ((q • (F.symm : V →ₗ[K] V)).dualMap (eMid x)) (F y) := by rw [hx]
    _ = (eMid x) ((q • (F.symm : V →ₗ[K] V)) (F y)) := by
          simp only [LinearMap.dualMap_apply]
    _ = (eMid x) (q • (F.symm (F y))) := by
          simp only [LinearMap.smul_apply, LinearEquiv.coe_coe]
    _ = (eMid x) (q • y) := by rw [LinearEquiv.symm_apply_apply]
    _ = q * eMid x y := by simp only [map_smul, smul_eq_mul]

end ConjDualEvaluationBridge

theorem solution (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) (hn : 2 ≤ n)
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    ∃ (V : ℕ → Type) (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module (Padic ℓ) (V i))
      (_ : ∀ i, Module.Finite (Padic ℓ) (V i))
      (F : ∀ i, V i ≃ₗ[Padic ℓ] V i)
      (eMid : V n ≃ₗ[Padic ℓ] Module.Dual (Padic ℓ) (V n)),
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
      (∀ (x y : V n),
        eMid (F n x) (F n y) = (Nat.card k : Padic ℓ) ^ n * eMid x y) ∧
      (∀ i, 1 ≤ i → i < n → ∃ W : ℤ[X], W.Monic ∧ aeval (F i : V i →ₗ[Padic ℓ] V i) W = 0 ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ = (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) ∧
      (∃ W : ℤ[X], W.Monic ∧ aeval (F n : V n →ₗ[Padic ℓ] V n) W = 0 ∧
        ∀ z : ℂ, aeval z W = 0 → ‖z‖ ≤ (Nat.card k : ℝ) ^ ((n : ℝ) / 2)) := by
  obtain ⟨V, hVAdd, hVMod, hVFin, F, eMid, htr, hconj, hWpure⟩ :=
    WeilConjectures.exists_qladic_lower_half_conj_dual_of_ge_two p k n hn X f hproj ℓ hℓp
  let _ : ∀ i, AddCommGroup (V i) := hVAdd
  let _ : ∀ i, Module (Padic ℓ) (V i) := hVMod
  let _ : ∀ i, Module.Finite (Padic ℓ) (V i) := hVFin
  refine ⟨V, hVAdd, hVMod, hVFin, F, eMid, htr, ?_, ?_, ?_⟩
  · exact eval_equiv_of_conj_dual (F n) ((Nat.card k : Padic ℓ) ^ n) eMid hconj
  · intro i h1 hlt
    obtain ⟨W, hWmon, hWF, hWnorm⟩ := hWpure i h1 (le_of_lt hlt)
    exact ⟨W, hWmon, hWF, hWnorm⟩
  · obtain ⟨W, hWmon, hWF, hWnorm⟩ := hWpure n (by omega) le_rfl
    exact ⟨W, hWmon, hWF, fun z hz => le_of_eq (hWnorm z hz)⟩

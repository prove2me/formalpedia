-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_contact_coordinate_jet_rank
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T03:08:56.645639+00:00
-- url     : https://prove2.me/submissions/030ee4aa-e390-4166-8004-bb4f222b8f25

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Isomorphisms

noncomputable section
open scoped Classical
open WeierstrassEllipticZeta

private lemma finite_power_matrix_rank {A ι : Type*} [CommRing A] [Algebra ℂ A]
    [Fintype ι] (e : A →ₗ[ℂ] (ι → ℂ)) (he : Function.Injective e) (x : A)
    (d : ℕ) (hd : Module.finrank ℂ A ≤ d) :
    Matrix.rank (Matrix.of fun i k => e (x ^ (k : ℕ)) i : Matrix ι (Fin d) ℂ) =
      Module.finrank ℂ (Algebra.adjoin ℂ ({x} : Set A)) := by
  let : FiniteDimensional ℂ A := FiniteDimensional.of_injective e he
  have hx : IsIntegral ℂ x := IsIntegral.of_finite ℂ x
  have hm : (minpoly ℂ x).natDegree ≤ d := (minpoly.natDegree_le x).trans hd
  have hs : Submodule.span ℂ (Set.range fun k : Fin d => x ^ (k : ℕ)) =
      (Algebra.adjoin ℂ ({x} : Set A)).toSubmodule := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℂ x) _
    · rw [← Submodule.span_range_natDegree_eq_adjoin (minpoly.monic hx)
        (minpoly.aeval ℂ x)]
      apply Submodule.span_mono
      intro y hy
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨⟨k, (Finset.mem_range.mp hk).trans_le hm⟩, rfl⟩
  rw [Matrix.rank_eq_finrank_span_cols]
  have hmap : Submodule.span ℂ
      (Set.range (Matrix.col (Matrix.of fun i k => e (x ^ (k : ℕ)) i :
        Matrix ι (Fin d) ℂ))) =
      (Algebra.adjoin ℂ ({x} : Set A)).toSubmodule.map e := by
    rw [← hs, Submodule.map_span]
    congr 1
    change Set.range (fun k : Fin d => e (x ^ (k : ℕ))) = _
    exact Set.range_comp e (fun k : Fin d => x ^ (k : ℕ))
  rw [hmap]
  exact (Submodule.equivMapOfInjective e he
    (Algebra.adjoin ℂ ({x} : Set A)).toSubmodule).finrank_eq.symm

theorem solution (G : Frontier.Geometry)
    (c : Fin 2) (Z : Finset ℂ) (N : ℕ) (p : MvPolynomial (Fin 4) ℂ) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ c
        (extensionChartCoordinates G.S c z.val) N
    let x := Ideal.Quotient.mk I p
    let J : Matrix (Z × Fin N) (Fin (N * Z.card)) ℂ := Matrix.of fun r k =>
      MvPolynomial.eval (extensionChartCoordinates G.S c r.1.val)
        ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[r.2.val] (p ^ k.val))
    J.rank = Module.finrank ℂ (Algebra.adjoin ℂ ({x} : Set _)) := by
  classical
  dsimp only
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ c
      (extensionChartCoordinates G.S c z.val) N
  let E : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] (Z × Fin N → ℂ) :=
    LinearMap.pi fun r =>
      (MvPolynomial.aeval (extensionChartCoordinates G.S c r.1.val)).toLinearMap.comp
        ((extensionChartDerivation G.L.g₂ G.L.g₃ c).toLinearMap ^ r.2.val)
  have hker : LinearMap.ker E = I.restrictScalars ℂ := by
    ext q
    change E q = 0 ↔ q ∈ (⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ c
      (extensionChartCoordinates G.S c z.val) N)
    simp only [Submodule.mem_iInf]
    constructor
    · intro h z
      apply (G.hcontact.1 c _ N q).mpr
      intro k hk
      have hq := congrFun h (z, ⟨k, hk⟩)
      simpa only [E, LinearMap.pi_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, Module.End.pow_apply, Pi.zero_apply] using! hq
    · intro h
      funext r
      have hq := (G.hcontact.1 c _ N q).mp (h r.1) r.2.val r.2.isLt
      simpa only [E, LinearMap.pi_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, Module.End.pow_apply, Pi.zero_apply] using! hq
  let e₀ : (MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₗ[ℂ] LinearMap.range E :=
    (Submodule.quotEquivOfEq (I.restrictScalars ℂ) (LinearMap.ker E) hker.symm).trans
      E.quotKerEquivRange
  let e : (MvPolynomial (Fin 4) ℂ ⧸ I) →ₗ[ℂ] (Z × Fin N → ℂ) :=
    (LinearMap.range E).subtype.comp e₀.toLinearMap
  have he : Function.Injective e := Subtype.val_injective.comp e₀.injective
  have hemk (q : MvPolynomial (Fin 4) ℂ) : e (Ideal.Quotient.mk I q) = E q := by
    rfl
  have hd : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) ≤ N * Z.card := by
    have h := LinearMap.finrank_le_finrank_of_injective he
    simpa [Module.finrank_pi_fintype, Nat.mul_comm] using h
  have hr := finite_power_matrix_rank e he (Ideal.Quotient.mk I p) (N * Z.card) hd
  have hcolumns : (Matrix.of fun i k => e ((Ideal.Quotient.mk I p) ^ (k : ℕ)) i :
      Matrix (Z × Fin N) (Fin (N * Z.card)) ℂ) =
      Matrix.of fun r k => MvPolynomial.eval (extensionChartCoordinates G.S c r.1.val)
        ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[r.2.val] (p ^ k.val)) := by
    ext r k
    simp only [Matrix.of_apply]
    rw [← map_pow, hemk]
    simp only [E, LinearMap.pi_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, Module.End.pow_apply]
    rfl
  rw [hcolumns] at hr
  exact hr

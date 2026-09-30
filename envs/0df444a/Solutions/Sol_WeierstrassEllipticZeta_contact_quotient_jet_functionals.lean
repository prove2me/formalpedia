-- Prove2me | solution 1 for WeierstrassEllipticZeta.contact_quotient_jet_functionals
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T17:11:14.152875+00:00
-- url     : https://prove2.me/submissions/3465dcdd-dc43-4a1b-a812-9975ae4eb87f

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Pi

noncomputable section
open scoped Classical
open WeierstrassEllipticZeta

private lemma finite_coordinate_functionals
    (K A L ι : Type*) [Field K] [AddCommGroup A] [Module K A]
    [AddCommGroup L] [Module K L] [Fintype ι]
    (e : A →ₗ[K] (ι → K)) (he : Function.Injective e) :
    (∀ T : A →ₗ[K] L, ∃ w : ι → L, ∀ a, T a = ∑ i, e a i • w i) ∧
      (∀ w : ι → L, ∃! T : A →ₗ[K] L, ∀ a, T a = ∑ i, e a i • w i) := by
  classical
  let D := LinearEquiv.piRing K L ι K
  constructor
  · intro T
    let f : (ι → K) →ₗ[K] L := T.comp e.leftInverse
    refine ⟨D f, ?_⟩
    intro a
    have h : f (e a) = T a := by
      dsimp only [f, LinearMap.comp_apply]
      rw [LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr he)]
    have hf := congrArg (fun q : (ι → K) →ₗ[K] L => q (e a)) (D.symm_apply_apply f)
    simpa only [D, LinearEquiv.piRing_symm_apply, h] using hf.symm
  · intro w
    let T : A →ₗ[K] L := (D.symm w).comp e
    have hT (a : A) : T a = ∑ i, e a i • w i := by
      simp only [T, D, LinearMap.comp_apply, LinearEquiv.piRing_symm_apply]
    refine ⟨T, hT, ?_⟩
    intro T' hT'
    ext a
    exact (hT' a).trans (hT a).symm

theorem solution
    (G : Frontier.Geometry) (c : Fin 2) (Z : Finset ℂ) (N : ℕ)
    (L : Type*) [AddCommGroup L] [Module ℂ L] :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ c
        (extensionChartCoordinates G.S c z.val) N
    (∀ T : (MvPolynomial (Fin 4) ℂ ⧸ I) →ₗ[ℂ] L,
      ∃ w : Z × Fin N → L, ∀ p : MvPolynomial (Fin 4) ℂ,
        T (Ideal.Quotient.mk I p) = ∑ r : Z × Fin N,
          MvPolynomial.eval (extensionChartCoordinates G.S c r.1.val)
            ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[r.2.val] p) • w r) ∧
    (∀ w : Z × Fin N → L,
      ∃! T : (MvPolynomial (Fin 4) ℂ ⧸ I) →ₗ[ℂ] L,
        ∀ p : MvPolynomial (Fin 4) ℂ,
          T (Ideal.Quotient.mk I p) = ∑ r : Z × Fin N,
            MvPolynomial.eval (extensionChartCoordinates G.S c r.1.val)
              ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[r.2.val] p) • w r) := by
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
    ext p
    change E p = 0 ↔ p ∈ (⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ c
      (extensionChartCoordinates G.S c z.val) N)
    simp only [Submodule.mem_iInf]
    constructor
    · intro h z
      apply (G.hcontact.1 c _ N p).mpr
      intro k hk
      have hp := congrFun h (z, ⟨k, hk⟩)
      simpa only [E, LinearMap.pi_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, Module.End.pow_apply, Pi.zero_apply] using! hp
    · intro h
      funext r
      have hp := (G.hcontact.1 c _ N p).mp (h r.1) r.2.val r.2.isLt
      simpa only [E, LinearMap.pi_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, Module.End.pow_apply, Pi.zero_apply] using! hp
  let e₀ : (MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₗ[ℂ] LinearMap.range E :=
    (Submodule.quotEquivOfEq (I.restrictScalars ℂ) (LinearMap.ker E) hker.symm).trans
      E.quotKerEquivRange
  let e : (MvPolynomial (Fin 4) ℂ ⧸ I) →ₗ[ℂ] (Z × Fin N → ℂ) :=
    (LinearMap.range E).subtype.comp e₀.toLinearMap
  have he : Function.Injective e := Subtype.val_injective.comp e₀.injective
  have hemk (p : MvPolynomial (Fin 4) ℂ) : e (Ideal.Quotient.mk I p) = E p := rfl
  obtain ⟨hrep, hdesc⟩ := finite_coordinate_functionals
    ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) L (Z × Fin N) e he
  constructor
  · intro T
    obtain ⟨w, hw⟩ := hrep T
    refine ⟨w, ?_⟩
    intro p
    simpa only [hemk, E, LinearMap.pi_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, Module.End.pow_apply] using! hw (Ideal.Quotient.mk I p)
  · intro w
    obtain ⟨T, hT, huniq⟩ := hdesc w
    refine ⟨T, ?_, ?_⟩
    · intro p
      simpa only [hemk, E, LinearMap.pi_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, Module.End.pow_apply] using! hT (Ideal.Quotient.mk I p)
    · intro T' hT'
      apply huniq T'
      intro a
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      simpa only [hemk, E, LinearMap.pi_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, Module.End.pow_apply] using! hT' p

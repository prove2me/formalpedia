-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.etale_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:02.506253+00:00
-- url     : https://prove2.me/submissions/32130214-24a1-45e9-bee6-d0aab632681a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open MvPolynomial
variable {R : Type} [CommRing R] {n : ℕ} {S : Type} [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial (Fin n) R) S] [IsScalarTower R (MvPolynomial (Fin n) R) S]
variable [Algebra.FormallyEtale (MvPolynomial (Fin n) R) S] (ε : S →ₐ[R] R)
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R)
    (hJ : IsNilpotent (RingHom.ker aug)) (φ₁ φ₂ : S →ₐ[R] A) (h1 : aug.comp φ₁ = ε) (h2 : aug.comp φ₂ = ε)
    (hs : ∀ j : Fin n, φ₁ (sX (S := S) R j) = φ₂ (sX (S := S) R j)) : φ₁ = φ₂ := by
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A := φ₁.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) S)
  have hρ2 : φ₂.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) S) = ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    exact (hs j).symm
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) A := IsScalarTower.of_algebraMap_eq (fun r => (ρ.commutes r).symm)
  let ψ₁ : S →ₐ[MvPolynomial (Fin n) R] A :=
    { φ₁.toRingHom with commutes' := fun p => rfl }
  let ψ₂ : S →ₐ[MvPolynomial (Fin n) R] A :=
    { φ₂.toRingHom with commutes' := fun p => AlgHom.congr_fun hρ2 p }
  have : ψ₁ = ψ₂ := by
    apply Algebra.FormallyUnramified.lift_unique (RingHom.ker aug) hJ
    ext x
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (AlgHom.congr_fun h1 x).trans (AlgHom.congr_fun h2 x).symm
  ext x
  exact AlgHom.congr_fun this x
end ReciprocityTheory.ChartRestriction.G.Chart

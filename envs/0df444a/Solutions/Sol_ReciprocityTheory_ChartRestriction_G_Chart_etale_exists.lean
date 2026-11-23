-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.etale_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:02.177678+00:00
-- url     : https://prove2.me/submissions/46c89aa9-b5f5-4aa1-90a7-b646c8c0751d

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
    (hJ : IsNilpotent (RingHom.ker aug)) (b : Fin n → A) (hb : ∀ j, aug (b j) = ε (sX R j)) :
    ∃ φ : S →ₐ[R] A, aug.comp φ = ε ∧ ∀ j, φ (sX R j) = b j := by
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A := MvPolynomial.aeval b
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) A := IsScalarTower.of_algebraMap_eq (fun r => (ρ.commutes r).symm)
  let J := RingHom.ker aug
  let mk : A →ₐ[MvPolynomial (Fin n) R] A ⧸ J := Ideal.Quotient.mkₐ _ J
  have hmkR : ∀ a : A, mk a = Ideal.Quotient.mk J (algebraMap R A (aug a)) := by
    intro a
    show Ideal.Quotient.mk J a = Ideal.Quotient.mk J (algebraMap R A (aug a))
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  let f₀r : S →+* A ⧸ J := (Ideal.Quotient.mk J).comp ((algebraMap R A).comp ε.toRingHom)
  have hf₀ : ∀ p : MvPolynomial (Fin n) R, f₀r (algebraMap _ S p) = algebraMap _ (A ⧸ J) p := by
    have : f₀r.comp (algebraMap (MvPolynomial (Fin n) R) S) = algebraMap (MvPolynomial (Fin n) R) (A ⧸ J) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        show Ideal.Quotient.mk J (algebraMap R A (ε (algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.C r)))) =
          Ideal.Quotient.mk J (ρ (MvPolynomial.C r))
        rw [MvPolynomial.aeval_C, show algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.C r) = algebraMap R S r from
          (IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R) S r).symm, AlgHom.commutes,
          Algebra.algebraMap_self, RingHom.id_apply]
      · intro j
        show Ideal.Quotient.mk J (algebraMap R A (ε (sX R j))) = Ideal.Quotient.mk J (ρ (MvPolynomial.X j))
        rw [MvPolynomial.aeval_X, Ideal.Quotient.eq, RingHom.mem_ker, map_sub, AlgHom.commutes,
          Algebra.algebraMap_self, RingHom.id_apply, hb, sub_self]
    exact fun p => RingHom.congr_fun this p
  let f₀ : S →ₐ[MvPolynomial (Fin n) R] A ⧸ J := { f₀r with commutes' := hf₀ }
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hker : IsNilpotent (RingHom.ker (mk : A →+* A ⧸ J)) := by
    have : RingHom.ker (mk : A →+* A ⧸ J) = J := Ideal.mk_ker
    rw [this]
    exact hJ
  let φ' := Algebra.FormallySmooth.liftOfSurjective f₀ mk hmk hker
  have hφ' : mk.comp φ' = f₀ := Algebra.FormallySmooth.comp_liftOfSurjective f₀ mk hmk hker
  refine ⟨φ'.restrictScalars R, ?_, ?_⟩
  · ext x
    have e1 := AlgHom.congr_fun hφ' x
    simp only [AlgHom.comp_apply] at e1
    rw [hmkR] at e1
    have e2 : (Ideal.Quotient.mk J) (algebraMap R A (aug (φ' x))) = (Ideal.Quotient.mk J) (algebraMap R A (ε x)) := e1
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.id_apply, sub_eq_zero] at e2
    exact e2
  · intro j
    show φ' (algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X j)) = b j
    rw [AlgHom.commutes]
    show ρ (MvPolynomial.X j) = b j
    exact MvPolynomial.aeval_X b j
end ReciprocityTheory.ChartRestriction.G.Chart

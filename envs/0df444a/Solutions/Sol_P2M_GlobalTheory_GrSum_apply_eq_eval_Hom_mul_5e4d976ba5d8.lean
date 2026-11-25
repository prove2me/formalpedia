-- Prove2me | solution 1 for P2M_GlobalTheory_GrSum_apply_eq_eval_Hom_mul_5e4d976ba5d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:11:59.800552+00:00
-- url     : https://prove2.me/submissions/0c18ab5d-7c31-4fcf-b27d-e9a5b1bb38a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulOfTwCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory
namespace GlobalTheory
namespace GrSum
theorem _root_.solution {ι R B : Type*} [CommRing R] [CommRing B]
    {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x) (c : R →+* B) (b : ι → B)
    (φ : ∀ n, A n → B) (hadd : ∀ n a a', φ n (a + a') = φ n a + φ n a')
    (hsmul : ∀ n (r : R) a, φ n (r • a) = c r * φ n a)
    (hop : ∀ i n a, φ (n + 1) (x i n a) = b i * φ n a)
    (F : MvPolynomial ι R) {t t' : ℤ} {a : A t} {a' : A t'}
    (h : F • GrSum.of hx t a = GrSum.of hx t' a') :
    φ t' a' = MvPolynomial.eval₂Hom c b F * φ t a := by
  letI : Algebra R B := c.toAlgebra
  letI : Algebra (MvPolynomial ι R) B := (MvPolynomial.eval₂Hom c b).toAlgebra
  haveI : IsScalarTower R (MvPolynomial ι R) B :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C c b r).symm
  let ψ : ∀ n, A n →ₗ[R] B := fun n => ⟨⟨φ n, hadd n⟩, hsmul n⟩
  have hψ : ∀ i n a, ψ (n + 1) (x i n a) = (MvPolynomial.X i : MvPolynomial ι R) • ψ n a :=
    fun i n a => (hop i n a).trans
      (congrArg (· * φ n a) (MvPolynomial.eval₂Hom_X' c b i).symm)
  have e := congrArg (GrSum.lift hx ψ hψ) h
  rw [map_smul, GrSum.lift_of, GrSum.lift_of] at e
  exact e.symm
end GrSum
end GlobalTheory

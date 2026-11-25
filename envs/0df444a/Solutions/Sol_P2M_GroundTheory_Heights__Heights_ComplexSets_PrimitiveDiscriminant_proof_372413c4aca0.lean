-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveDiscriminant_proof_372413c4aca0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:06:07.41013+00:00
-- url     : https://prove2.me/submissions/e25bac9e-4126-4801-b323-6c4db1dca388

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFunctionFieldDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitive
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_aeval_mk_projAlgebra_aa6d341dca34

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
variable {n d : ℕ}
set_option synthInstance.maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace PrimitiveDiscriminant
theorem _root_.solution (hG : GenericPrimitive.Statement) (hD : DiscrAdjoin.Statement)
    (hF : FunctionFieldDegree.Statement) : PrimitiveDiscriminant.Statement := by
  intro n d J A hJ _ hA
  have := hJ
  let := projAlgebra J A
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite

  let iRL : Algebra (MvPolynomial (Fin d) ℂ) (funField J) :=
    ((algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (funField J)).comp
      (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J))).toAlgebra
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ)
      (funField J)) :=
    (IsFractionRing.injective (MvPolynomial (Fin n) ℂ ⧸ J) _).comp (by exact hA.injective)
  let iKL : Algebra (FractionRing (MvPolynomial (Fin d) ℂ)) (funField J) :=
    (IsFractionRing.lift hinj).toAlgebra
  have t1 : IsScalarTower (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
      (funField J) :=
    IsScalarTower.of_algebraMap_eq fun r => (IsFractionRing.lift_algebraMap hinj r).symm
  have t2 : IsScalarTower (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)
      (funField J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let iCL : Algebra ℂ (funField J) :=
    ((algebraMap (FractionRing (MvPolynomial (Fin d) ℂ)) (funField J)).comp
      (algebraMap ℂ (FractionRing (MvPolynomial (Fin d) ℂ)))).toAlgebra
  have t3 : IsScalarTower ℂ (FractionRing (MvPolynomial (Fin d) ℂ))
      (funField J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hfin, hdeg, hgen⟩ := hF n d J A hJ hA (FractionRing (MvPolynomial (Fin d) ℂ))
    (funField J)
  have := hfin
  have : CharZero (FractionRing (MvPolynomial (Fin d) ℂ)) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (FractionRing (MvPolynomial (Fin d) ℂ))).injective
  have : Algebra.IsSeparable (FractionRing (MvPolynomial (Fin d) ℂ))
      (funField J) := inferInstance

  have hC : ∀ a : ℂ, algebraMap ℂ (funField J) a =
      algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) _ (Ideal.Quotient.mk J (C a)) := by
    intro a
    change algebraMap (FractionRing (MvPolynomial (Fin d) ℂ)) _ (algebraMap ℂ _ a) = _
    rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ)),
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) ℂ)
        (MvPolynomial (Fin n) ℂ ⧸ J)]
    congr 1
    change Ideal.Quotient.mk J (pullback A (algebraMap ℂ _ a)) = _
    rw [AlgHom.commutes]
    rfl
  obtain ⟨D, hD0, hDc⟩ := hG ℂ (FractionRing (MvPolynomial (Fin d) ℂ))
    (funField J) n _ hgen
  refine ⟨D, hD0, fun c hc => ?_⟩
  have hprim := hDc c hc
  have hsum : ∑ j, c j • algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (funField J)
      (Ideal.Quotient.mk J (X j)) = algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) _
        (Ideal.Quotient.mk J (sum₂ c)) := by
    simp only [Algebra.smul_def, hC, ← map_mul, ← map_sum, sum₂]
  rw [hsum] at hprim
  have hℓ : IsIntegral (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J (sum₂ c)) :=
    Algebra.IsIntegral.isIntegral _
  obtain ⟨hdeg', hdisc, hmem⟩ := hD (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
    (funField J) _ hℓ.algebraMap hprim
  have hmin : minpoly (MvPolynomial (Fin d) ℂ) (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J)
      (funField J) (Ideal.Quotient.mk J (sum₂ c))) =
        formMinpoly J A c :=
    minpoly.algHom_eq (IsScalarTower.toAlgHom (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) _)
      (IsFractionRing.injective _ _) _
  rw [hmin] at hdeg' hdisc hmem
  refine ⟨minpoly.monic hℓ, hdeg'.trans hdeg, ?_, hdisc, fun j => ?_⟩
  · have h0 := minpoly.aeval (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J (sum₂ c))
    rw [aeval_mk_projAlgebra] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  · have hxj : IsIntegral (MvPolynomial (Fin d) ℂ) (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J)
        (funField J) (Ideal.Quotient.mk J (X j))) :=
      (Algebra.IsIntegral.isIntegral _).algebraMap
    have hm := hmem _ hxj
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨G, hGe⟩ := hm
    refine ⟨G, Ideal.Quotient.eq.1 (IsFractionRing.injective (MvPolynomial (Fin n) ℂ ⧸ J)
      (funField J) ?_)⟩
    rw [← aeval_mk_projAlgebra, ← Polynomial.aeval_algebraMap_apply]
    refine Eq.trans ?_ hGe.symm
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (funField J),
      ← map_mul]
    congr 1
end PrimitiveDiscriminant
end GroundTheory.Heights₂.Heights.ComplexSets

-- Prove2me | solution 1 for P2M_RH_GlobalTheory_UnitLemma_Desc_isIntegral_sigma_9c63cf01f25c1776
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:59:30.935802+00:00
-- url     : https://prove2.me/submissions/a7a30f29-5c82-4e91-9985-917b4b4910b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteIntegralClosureOfSeparableInvolutionAlgebrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RhoPowLowerBoundSwappedPairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution (K : UQ) (B : InvAlg K) (y : B.A) (hy : IsIntegral K.O y) : IsIntegral K.O (B.σ y) := by
  obtain ⟨p, hpm, hp⟩ := hy
  choose cO hcO using K.c_int
  have hinj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E
  let ψ : K.O →+* K.O :=
    { toFun := cO
      map_one' := hinj (by rw [← hcO, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [← hcO, map_mul, map_mul, map_mul, hcO, hcO])
      map_zero' := hinj (by rw [← hcO, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [← hcO, map_add, map_add, map_add, hcO, hcO]) }
  have hcomp : (algebraMap K.O B.A).comp ψ = (B.σ : B.A →+* B.A).comp (algebraMap K.O B.A) := by
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg]
    show _ = algebraMap K.E B.A (K.c (algebraMap K.O K.E x))
    rw [hcO]; rfl
  refine ⟨p.map ψ, hpm.map ψ, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  have := Polynomial.hom_eval₂ p (algebraMap K.O B.A) (B.σ : B.A →+* B.A) y
  exact this.symm.trans (by rw [hp, map_zero])
end GlobalTheory.UnitLemma.Desc

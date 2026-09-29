-- Prove2me | solution 1 for PDivisibleGroup.eq_of_forall_toAlgHom_comp_eq_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8b70c6cc-0b97-5d62-a6e0-defb93acffc2

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Theorems.Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
import Theorems.Thm_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_eq_of_forall_toAlgHom_comp_eq_of_ringOfIntegers

set_option autoImplicit false

open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

universe u

namespace Ws47
namespace C2B

theorem eq_zero_of_forall_algHom_apply_eq_zero
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)] [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (v : ℕ) (b : B v)
    (hb : ∀ f : B v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p, f b = 0) : b = 0 := by
  classical

  obtain ⟨-, hdvr, -⟩ := PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete p K
  haveI : IsDiscreteValuationRing ↥(PadicAlgCl.ringOfIntegers p K) := hdvr
  haveI : CharZero ↥(PadicAlgCl.ringOfIntegers p K) := by
    refine charZero_of_injective_algebraMap (R := ℤ_[p]) (A := ↥(PadicAlgCl.ringOfIntegers p K)) ?_
    have hcomp : Function.Injective ((algebraMap ↥(PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)).comp
        (algebraMap ℤ_[p] ↥(PadicAlgCl.ringOfIntegers p K))) := by
      rw [← IsScalarTower.algebraMap_eq ℤ_[p] ↥(PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)]
      exact PadicAlgCl.ringOfIntegers.algebraMap_injective_padicInt p
    rw [RingHom.coe_comp] at hcomp
    exact Function.Injective.of_comp hcomp

  letI : Algebra ↥(PadicAlgCl.ringOfIntegers p K) (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) := inferInstance
  haveI : IsFractionRing ↥(PadicAlgCl.ringOfIntegers p K) (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) := inferInstance
  haveI : CharZero (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective ↥(PadicAlgCl.ringOfIntegers p K) (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)))
  have hinj : Function.Injective (algebraMap ↥(PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) := Subtype.val_injective
  letI : Algebra (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) (PadicAlgCl p) := (IsFractionRing.lift hinj).toAlgebra
  haveI : IsScalarTower ↥(PadicAlgCl.ringOfIntegers p K) (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) (PadicAlgCl p) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra]
      exact (IsFractionRing.lift_algebraMap hinj x).symm

  haveI : NoZeroSMulDivisors ↥(PadicAlgCl.ringOfIntegers p K) (B v) := ⟨fun {c x} hcx => by
    rcases eq_or_ne c 0 with hc | hc
    · exact Or.inl hc
    · right
      let bB := Module.Free.chooseBasis ↥(PadicAlgCl.ringOfIntegers p K) (B v)
      have h1 := congrArg bB.repr hcx
      rw [map_smul, map_zero] at h1
      exact bB.repr.injective (by rw [map_zero]; exact (smul_eq_zero.1 h1).resolve_left hc)⟩
  haveI : Algebra.FiniteType (FractionRing ↥(PadicAlgCl.ringOfIntegers p K))
      ((FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) ⊗[↥(PadicAlgCl.ringOfIntegers p K)] B v) := Module.Finite.finiteType _
  haveI : IsReduced ((FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) ⊗[↥(PadicAlgCl.ringOfIntegers p K)] B v) :=
    HopfAlgebra.isReduced_of_finiteType_of_charZero (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) _
  exact Algebra.eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
    (FractionRing ↥(PadicAlgCl.ringOfIntegers p K)) (PadicAlgCl p) b hb

end Ws47.C2B

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h h' : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (H : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h')
    (φ φ' : ∀ v : ℕ, H.level v →ₐc[PadicAlgCl.ringOfIntegers p K] G.level v)
    (hφ : ∀ (v : ℕ) (x : G.Point (PadicAlgCl p) v),
      (PDivisibleGroup.Point.toAlgHom x).comp (φ v : H.level v →ₐ[PadicAlgCl.ringOfIntegers p K] G.level v) =
        (PDivisibleGroup.Point.toAlgHom x).comp (φ' v : H.level v →ₐ[PadicAlgCl.ringOfIntegers p K] G.level v)) :
    φ = φ' := by
  funext v
  refine BialgHom.coe_algHom_injective ?_
  refine AlgHom.ext fun d => ?_
  rw [← sub_eq_zero]
  refine Ws47.C2B.eq_zero_of_forall_algHom_apply_eq_zero p K G.level v _ fun f => ?_
  have := DFunLike.congr_fun (hφ v (PDivisibleGroup.Point.ofAlgHom f)) d
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at this
  rw [map_sub, sub_eq_zero]
  exact this

end S_PDivisibleGroup_eq_of_forall_toAlgHom_comp_eq_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_eq_of_forall_toAlgHom_comp_eq_of_ringOfIntegers (solution)

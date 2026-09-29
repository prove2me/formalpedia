-- Prove2me | solution 1 for PDivisibleGroup.forall_bijective_of_bijective_linearMap_tateModule_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e3703f38-04de-577c-840d-a1b1e8460e22

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Theorems.Thm_PDivisibleGroup_eq_of_hasDimension_of_linearEquiv_tateModule_of_ringOfIntegers
import Theorems.Thm_Subalgebra_eq_top_of_associated_discr_of_basis
import Theorems.Thm_PDivisibleGroup_exists_hasDimension
import Theorems.Thm_PDivisibleGroup_exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq
import Theorems.Thm_PDivisibleGroup_finite_point_and_natCard_point_eq_pow
import Theorems.Thm_PDivisibleGroup_associated_discr_level_of_hasDimension_of_ringOfIntegers
import Theorems.Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
import Theorems.Thm_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_forall_bijective_of_bijective_linearMap_tateModule_of_ringOfIntegers
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions PDivisibleGroup.CPoints.instDistribMulAction PrimaryTorsion.instSMul PrimaryTorsion.instModule HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "PDivisibleGroup.CartierDuality.mk.injEq PDivisibleGroup.CartierDuality.toDualEquiv_apply PDivisibleGroup.CartierDuality.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul PDivisibleGroup.cotangentBaseChange_tmul PDivisibleGroup.baseChange_transition_tmul PDivisibleGroup.cotangentToBaseChange_toCotangent PDivisibleGroup.baseChange_level HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff PDivisibleGroup.cotangentClass_algebraMap PDivisibleGroup.cotangentClass_one"
p2m_attr_erase "simp" "PDivisibleGroup.cpointsProj_cpointsMap PDivisibleGroup.pointsMap_reduceModPow_cpointsProj_succ PDivisibleGroup.cpointsProj_toCPoints PDivisibleGroup.mapModPow_mk PDivisibleGroup.reduceModPow_mk PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

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

namespace Ws47
namespace ISO

p2m_open "PDivisibleGroup~baseChange"

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]

theorem bijective_baseChange_of_injective_of_finrank_eq
    {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra R F] [IsFractionRing R F]
    {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) (hrk : Module.finrank R M = Module.finrank R N) :
    Function.Bijective (f.baseChange F) := by
  haveI : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  have hinj : Function.Injective (f.baseChange F) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := F) f hf
  have hdim : Module.finrank F (F ⊗[R] M) = Module.finrank F (F ⊗[R] N) := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange, hrk]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩

theorem exists_rep {R : Type} [CommRing R] {h : ℕ} (G : PDivisibleGroup R p h) {L : Type} [Field L] [Algebra R L]
    (x : TateModule p (G.Points L)) (v : ℕ) :
    ∃ g : G.Point L v, G.pointsMkAdd L v (Additive.ofMul g) = (x : ℕ → G.Points L) v := by
  have hz := TateModule.torsion x v
  obtain ⟨w, y, hy⟩ := Points.exists_mkAdd G ((x : ℕ → G.Points L) v)
  rcases le_total w v with hwv | hvw
  · exact ⟨G.pointInclLE L hwv y, by rw [G.pointsMkAdd_pointInclLE]; exact hy⟩
  · have hx : y ^ (p ^ v) = 1 := by
      refine (G.pointsMkAdd_eq_pointsMkAdd_iff (L := L) _ _).1 ?_
      rw [ofMul_pow, map_nsmul, ofMul_one, map_zero, ← natCast_zsmul, hy]
      exact hz
    obtain ⟨g, hg⟩ := G.exists_pointInclLE_eq_of_pow_eq_one hvw y hx
    exact ⟨g, by rw [← G.pointsMkAdd_pointInclLE hvw g, hg]; exact hy⟩

theorem trace_eq_trace_of_injective_of_finrank_eq
    {R : Type} [CommRing R] [IsDomain R] {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B]
    (f : A →ₐ[R] B) (hf : Function.Injective f) (hrk : Module.finrank R A = Module.finrank R B) (a : A) :
    Algebra.trace R A a = Algebra.trace R B (f a) := by
  let F := FractionRing R
  apply IsFractionRing.injective R F
  have hbij := bijective_baseChange_of_injective_of_finrank_eq F f.toLinearMap hf hrk
  let e : F ⊗[R] A ≃ₐ[F] F ⊗[R] B :=
    AlgEquiv.ofBijective (Algebra.TensorProduct.map (AlgHom.id F F) f) hbij
  have h1 : algebraMap R F (Algebra.trace R A a) = Algebra.trace F (F ⊗[R] A) ((1 : F) ⊗ₜ a) := by
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
    congr 1
    refine TensorProduct.AlgebraTensorModule.ext fun k x => ?_
    simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  have h2 : algebraMap R F (Algebra.trace R B (f a)) = Algebra.trace F (F ⊗[R] B) ((1 : F) ⊗ₜ f a) := by
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
    congr 1
    refine TensorProduct.AlgebraTensorModule.ext fun k x => ?_
    simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  rw [h1, h2, ← Algebra.trace_eq_of_algEquiv e ((1 : F) ⊗ₜ a)]
  rfl

end Ws47.ISO

namespace Ws47
namespace ISO

p2m_open "PDivisibleGroup~baseChange"

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]
variable {h : ℕ} {G Γ : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h}
variable {u : ∀ v : ℕ, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] Γ.level v}
variable {Tu : TateModule p (Γ.Points (PadicAlgCl p)) →ₗ[ℤ_[p]] TateModule p (G.Points (PadicAlgCl p))}

def LevelFormula (G Γ : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) (u : ∀ v : ℕ, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] Γ.level v)
    (Tu : TateModule p (Γ.Points (PadicAlgCl p)) →ₗ[ℤ_[p]] TateModule p (G.Points (PadicAlgCl p))) : Prop :=
  ∀ (x : TateModule p (Γ.Points (PadicAlgCl p))) (n w : ℕ) (g : Γ.Point (PadicAlgCl p) w),
    Γ.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) = (x : ℕ → Γ.Points (PadicAlgCl p)) n →
    ((Tu x : TateModule p (G.Points (PadicAlgCl p))) : ℕ → G.Points (PadicAlgCl p)) n =
      G.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul (Point.ofAlgHom ((Point.toAlgHom g).comp (u w : G.level w →ₐ[PadicAlgCl.ringOfIntegers p K] Γ.level w))))

theorem exists_point_comp_eq (hTu : LevelFormula G Γ u Tu) (hbij : Function.Bijective Tu)
    (v : ℕ) (x : G.Point (PadicAlgCl p) v) :
    ∃ γ : Γ.Point (PadicAlgCl p) v, Point.ofAlgHom ((Point.toAlgHom γ).comp (u v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] Γ.level v)) = x := by
  have hcard := fun w => PDivisibleGroup.finite_point_and_natCard_point_eq_pow p G (PadicAlgCl p) w
  obtain ⟨X, hX⟩ := (PDivisibleGroup.exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq
    p G (PadicAlgCl p) hcard).1 v x
  obtain ⟨ξ, rfl⟩ := hbij.2 X
  obtain ⟨γ, hγ⟩ := exists_rep Γ ξ v
  refine ⟨γ, ?_⟩
  refine (G.pointsMkAdd_eq_pointsMkAdd_iff (L := PadicAlgCl p) _ _).1 ?_
  rw [← hTu ξ v v γ hγ, hX]

theorem injective_u (hTu : LevelFormula G Γ u Tu) (hbij : Function.Bijective Tu) (v : ℕ) :
    Function.Injective (u v) := by
  intro a b hab
  rw [← sub_eq_zero] at hab ⊢
  rw [← map_sub] at hab
  refine Ws47.C2B.eq_zero_of_forall_algHom_apply_eq_zero p K G.level v _ fun f => ?_
  obtain ⟨γ, hγ⟩ := exists_point_comp_eq hTu hbij v (Point.ofAlgHom f)
  have : f = (Point.toAlgHom γ).comp (u v : G.level v →ₐ[_] Γ.level v) := by
    rw [← Point.toAlgHom_ofAlgHom (G := G) f, ← hγ, Point.toAlgHom_ofAlgHom]
  rw [this, AlgHom.comp_apply]
  show Point.toAlgHom γ (u v (a - b)) = 0
  rw [hab, map_zero]

theorem equivariant (hTu : LevelFormula G Γ u Tu) (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) (x : TateModule p (Γ.Points (PadicAlgCl p))) :
    Tu (Γ.tateModuleRep (PadicAlgCl p) τ x) = G.tateModuleRep (PadicAlgCl p) τ (Tu x) := by
  apply Subtype.ext
  funext n
  obtain ⟨γ, hγ⟩ := exists_rep Γ x n
  have h1 : Γ.pointsMkAdd (PadicAlgCl p) n (Additive.ofMul (Γ.pointMap (τ : PadicAlgCl p →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) n γ))
      = ((Γ.tateModuleRep (PadicAlgCl p) τ x : TateModule p (Γ.Points (PadicAlgCl p))) : ℕ → Γ.Points (PadicAlgCl p)) n := by
    rw [tateModuleRep_apply, ← hγ, Points.smul_pointsMkAdd]
  rw [hTu _ n n _ h1, tateModuleRep_apply, hTu x n n γ hγ, Points.smul_pointsMkAdd]
  congr 2

end Ws47.ISO

namespace Ws47
namespace ISO
p2m_open "PDivisibleGroup~baseChange"
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]

theorem discr_comp_eq {R : Type} [CommRing R] [IsDomain R] {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B]
    (f : A →ₐ[R] B) (hf : Function.Injective f) (hrk : Module.finrank R A = Module.finrank R B)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → A) :
    Algebra.discr R (fun i => f (b i)) = Algebra.discr R b := by
  rw [Algebra.discr_def, Algebra.discr_def]
  congr 1
  ext i j
  rw [Algebra.traceMatrix_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.traceForm_apply,
    ← map_mul, ← trace_eq_trace_of_injective_of_finrank_eq f hf hrk]

noncomputable def levelBasis {R : Type} [CommRing R] [Nontrivial R] {h : ℕ} (G : PDivisibleGroup R p h) (v : ℕ) :
    Module.Basis (Fin (p ^ (v * h))) R (G.level v) :=
  (Module.Free.chooseBasis R (G.level v)).reindex (Fintype.equivFinOfCardEq (by
    rw [← Module.finrank_eq_card_chooseBasisIndex, G.finrank_level]))

end Ws47.ISO

p2m_open "PDivisibleGroup~baseChange" in open Ws47.ISO  in

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G Γ : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (u : ∀ v : ℕ, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] Γ.level v)
    (hu : ∀ v : ℕ, (u v).comp (G.transition v) = (Γ.transition v).comp (u (v + 1)))
    (Tu : TateModule p (Γ.Points (PadicAlgCl p)) →ₗ[ℤ_[p]] TateModule p (G.Points (PadicAlgCl p)))
    (hTu : ∀ (x : TateModule p (Γ.Points (PadicAlgCl p))) (n w : ℕ) (g : Γ.Point (PadicAlgCl p) w),
        Γ.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) = (x : ℕ → Γ.Points (PadicAlgCl p)) n →
        ((Tu x : TateModule p (G.Points (PadicAlgCl p))) : ℕ → G.Points (PadicAlgCl p)) n =
          G.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (u w : G.level w →ₐ[PadicAlgCl.ringOfIntegers p K] Γ.level w)))))
    (hbij : Function.Bijective Tu) :
    ∀ v : ℕ, Function.Bijective (u v) := by
  classical
  obtain ⟨-, hdvr, hcomp⟩ := PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete p K
  haveI : IsDiscreteValuationRing (PadicAlgCl.ringOfIntegers p K) := hdvr
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K)) (PadicAlgCl.ringOfIntegers p K) := hcomp
  have hpm : ((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ∈ IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K) :=
    (IsLocalRing.mem_maximalIdeal _).2 (PadicAlgCl.ringOfIntegers.not_isUnit_natCast p K)
  obtain ⟨n, hn⟩ := PDivisibleGroup.exists_hasDimension hpm G
  obtain ⟨n', hn'⟩ := PDivisibleGroup.exists_hasDimension hpm Γ
  have hTu' : LevelFormula G Γ u Tu := hTu
  have hnn : n = n' :=
    PDivisibleGroup.eq_of_hasDimension_of_linearEquiv_tateModule_of_ringOfIntegers p K G Γ hn hn'
      (LinearEquiv.ofBijective Tu hbij) (fun τ x => equivariant hTu' τ x)
  subst hnn
  intro v
  have hinj : Function.Injective (u v) := injective_u hTu' hbij v
  refine ⟨hinj, ?_⟩

  let bG := levelBasis G v
  let bΓ := levelBasis Γ v
  have hdG := PDivisibleGroup.associated_discr_level_of_hasDimension_of_ringOfIntegers p K G hn v bG
  have hdΓ := PDivisibleGroup.associated_discr_level_of_hasDimension_of_ringOfIntegers p K Γ hn' v bΓ
  have hp0 : ((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ≠ 0 := by
    intro h0
    have := congrArg (algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) h0
    rw [map_natCast, map_zero] at this
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this
  have hne : Algebra.discr (PadicAlgCl.ringOfIntegers p K) bΓ ≠ 0 := hdΓ.ne_zero_iff.2 (pow_ne_zero _ hp0)
  let uA : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] Γ.level v := (u v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] Γ.level v)
  have hinjA : Function.Injective uA := hinj
  let eB := AlgEquiv.ofInjective uA hinjA
  let b : Module.Basis (Fin (p ^ (v * h))) (PadicAlgCl.ringOfIntegers p K) ↥uA.range := bG.map eB.toLinearEquiv
  have hb : (fun i => ((b i : ↥uA.range) : Γ.level v)) = fun i => uA (bG i) := by
    funext i
    rfl
  have hrk : Module.finrank (PadicAlgCl.ringOfIntegers p K) (G.level v) = Module.finrank (PadicAlgCl.ringOfIntegers p K) (Γ.level v) := by
    rw [G.finrank_level, Γ.finrank_level]
  have hdiscr : Associated (Algebra.discr (PadicAlgCl.ringOfIntegers p K) (fun i => ((b i : ↥uA.range) : Γ.level v))) (Algebra.discr (PadicAlgCl.ringOfIntegers p K) bΓ) := by
    rw [hb, discr_comp_eq uA hinjA hrk]
    exact hdG.trans hdΓ.symm
  have htop := Subalgebra.eq_top_of_associated_discr_of_basis bΓ uA.range b hdiscr hne
  exact (AlgHom.range_eq_top uA).1 htop

end S_PDivisibleGroup_forall_bijective_of_bijective_linearMap_tateModule_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_forall_bijective_of_bijective_linearMap_tateModule_of_ringOfIntegers (solution)

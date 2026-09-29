-- Prove2me | solution 1 for PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/defd7fc5-4265-5df2-bc5b-6e4e22c9cf5b

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_padicPlace_liesOverPrime
import Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
import Theorems.Thm_PDivisibleGroup_exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange
import Theorems.Thm_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_field
import Theorems.Thm_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_ringOfIntegers
import Theorems.Thm_BialgHom_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq
import Theorems.Thm_HopfAlgebra_bialgHom_eq_of_forall_algHom_comp_eq_of_charZero
import Theorems.Thm_PDivisibleGroup_exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed
import Theorems.Thm_ValuationSubring_exists_intermediateField_finiteDimensional_forall_apply_mem_of_isDiscreteValuationRing_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime
p2m_attr_erase "instance" "CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl PadicComplex.smulCommClass_gal_padic PadicComplex.smulCommClass_padic_gal PadicComplex.uniformContinuousConstSMul_gal PadicComplex.mulSemiringAction CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra PDivisibleGroup.CPoints.instDistribMulAction PrimaryTorsion.instSMul PrimaryTorsion.instModule"
p2m_attr_erase "simp" "HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul PDivisibleGroup.Tower.levelCast_rfl"
p2m_attr_erase "simp" "PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul PadicComplex.galAlgHom_apply PadicComplex.smul_algebraMap PadicComplex.norm_smul_eq PadicComplex.nnnorm_smul_eq PadicComplex.smul_coe PDivisibleGroup.CartierDuality.mk.injEq PDivisibleGroup.CartierDuality.toDualEquiv_apply PDivisibleGroup.CartierDuality.mk.sizeOf_spec CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply PDivisibleGroup.cotangentClass_algebraMap PDivisibleGroup.cotangentClass_one PDivisibleGroup.cpointsProj_cpointsMap PDivisibleGroup.pointsMap_reduceModPow_cpointsProj_succ"
p2m_attr_erase "simp" "PDivisibleGroup.cpointsProj_toCPoints PDivisibleGroup.mapModPow_mk PDivisibleGroup.reduceModPow_mk PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map"

set_option autoImplicit false

open scoped TensorProduct Pointwise

namespace Bialgebra p2m_export "Bialgebra" "ofAlgHom counitAlgHom TensorProduct.map algebraMap_injective comulAlgHom_apply TensorProduct.lid counitAlgHom_apply comulAlgHom toAlgebra TensorProduct.map_tmul" namespace TensorProduct p2m_export "Bialgebra.TensorProduct" "map map_tmul" end Bialgebra.TensorProduct
p2m_open_scoped "Bialgebra Bialgebra.TensorProduct" in
set_option maxHeartbeats 1600000 in

theorem Bialgebra.TensorProduct.exists_bialgEquiv_cancelBaseChange
    (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (B : Type) [CommRing B] [Bialgebra R B] :
    ∃ e : T ⊗[S] (S ⊗[R] B) ≃ₐc[T] T ⊗[R] B, ∀ (t : T) (s : S) (b : B), e (t ⊗ₜ[S] (s ⊗ₜ[R] b)) = (s • t) ⊗ₜ[R] b := by
  classical
  let f : T ⊗[S] (S ⊗[R] B) ≃ₐ[T] T ⊗[R] B := Algebra.TensorProduct.cancelBaseChange R S T T B
  have hf : ∀ (t : T) (s : S) (b : B), f (t ⊗ₜ[S] (s ⊗ₜ[R] b)) = (s • t) ⊗ₜ[R] b := fun t s b =>
    Algebra.TensorProduct.cancelBaseChange_tmul R S T T B t s b
  have hcounit : (Bialgebra.counitAlgHom T (T ⊗[R] B)).comp (f : T ⊗[S] (S ⊗[R] B) →ₐ[T] T ⊗[R] B) =
      Bialgebra.counitAlgHom T (T ⊗[S] (S ⊗[R] B)) := by
    apply Algebra.TensorProduct.ext'
    intro t x
    simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul s b =>
      change CoalgebraStruct.counit (R := T) (f (t ⊗ₜ[S] (s ⊗ₜ[R] b))) =
        CoalgebraStruct.counit (R := T) (t ⊗ₜ[S] (s ⊗ₜ[R] b))
      rw [hf, TensorProduct.counit_tmul, TensorProduct.counit_tmul, TensorProduct.counit_tmul,
        CommSemiring.counit_apply, CommSemiring.counit_apply, smul_assoc]
      simp [CommSemiring.counit_apply]
  have hcomul : (Algebra.TensorProduct.map (f : T ⊗[S] (S ⊗[R] B) →ₐ[T] T ⊗[R] B) (f : _ →ₐ[T] _)).comp
      (Bialgebra.comulAlgHom T (T ⊗[S] (S ⊗[R] B))) = (Bialgebra.comulAlgHom T (T ⊗[R] B)).comp (f : _ →ₐ[T] _) := by
    apply Algebra.TensorProduct.ext'
    intro t x
    simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul s b =>
      change Algebra.TensorProduct.map (f : _ →ₐ[T] _) (f : _ →ₐ[T] _) (CoalgebraStruct.comul (R := T) (t ⊗ₜ[S] (s ⊗ₜ[R] b))) =
        CoalgebraStruct.comul (R := T) (f (t ⊗ₜ[S] (s ⊗ₜ[R] b)))
      rw [hf, TensorProduct.comul_tmul, TensorProduct.comul_tmul, TensorProduct.comul_tmul,
        CommSemiring.comul_apply, CommSemiring.comul_apply, CommSemiring.comul_apply]
      generalize (CoalgebraStruct.comul (R := R) b : B ⊗[R] B) = c
      induction c using TensorProduct.induction_on with
      | zero =>
        rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, TensorProduct.tmul_zero, LinearEquiv.map_zero,
          map_zero, TensorProduct.tmul_zero, LinearEquiv.map_zero]
      | add x y hx hy =>
        rw [TensorProduct.tmul_add, LinearEquiv.map_add, TensorProduct.tmul_add, LinearEquiv.map_add,
          map_add, hx, hy, TensorProduct.tmul_add, LinearEquiv.map_add]
      | tmul b₁ b₂ =>
        rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
          TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
          TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
          Algebra.TensorProduct.map_tmul]
        change f _ ⊗ₜ[T] f _ = _
        rw [hf, hf, one_smul]
  exact ⟨BialgEquiv.ofAlgEquiv f hcounit hcomul, fun t s b => by
    rw [BialgEquiv.ofAlgEquiv_apply]; exact hf t s b⟩

set_option maxHeartbeats 1600000 in

theorem T4_agree_core
    {O : Type} [CommRing O] (K : Type) [Field K] [Algebra O K]
    (Oh : Type) [CommRing Oh] [Nontrivial Oh] [Algebra O Oh]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra O Ω] [Algebra K Ω] [Algebra Oh Ω]
    [IsScalarTower O K Ω] [IsScalarTower O Oh Ω]
    {p h h' : ℕ} [Fact p.Prime] (G : PDivisibleGroup O p h) (H : PDivisibleGroup O p h') (v : ℕ)
    (gK : (H.baseChange K).level v →ₐc[K] (G.baseChange K).level v)
    (gOh : (H.baseChange Oh).level v →ₐc[Oh] (G.baseChange Oh).level v)
    (hpts : ∀ (y : G.level v →ₐ[O] Ω) (b : H.level v),
      Algebra.TensorProduct.lift (Algebra.ofId K Ω) y (fun _ _ => Commute.all _ _) (gK ((1 : K) ⊗ₜ[O] b)) =
        Algebra.TensorProduct.lift (Algebra.ofId Oh Ω) y (fun _ _ => Commute.all _ _) (gOh ((1 : Oh) ⊗ₜ[O] b))) :
    ∀ b : H.level v,
      ((IsScalarTower.toAlgHom O K Ω).toLinearMap.rTensor (G.level v)) (gK ((1 : K) ⊗ₜ[O] b)) =
        ((IsScalarTower.toAlgHom O Oh Ω).toLinearMap.rTensor (G.level v)) (gOh ((1 : Oh) ⊗ₜ[O] b)) := by
  classical
  intro b
  obtain ⟨eK, heK⟩ := Bialgebra.TensorProduct.exists_bialgEquiv_cancelBaseChange O K Ω (H.level v)
  obtain ⟨eK', heK'⟩ := Bialgebra.TensorProduct.exists_bialgEquiv_cancelBaseChange O K Ω (G.level v)
  obtain ⟨eO, heO⟩ := Bialgebra.TensorProduct.exists_bialgEquiv_cancelBaseChange O Oh Ω (H.level v)
  obtain ⟨eO', heO'⟩ := Bialgebra.TensorProduct.exists_bialgEquiv_cancelBaseChange O Oh Ω (G.level v)
  haveI : IsAlgClosure Ω Ω := ⟨inferInstance, inferInstance⟩

  have hrT : ∀ (S' : Type) [CommRing S'] [Algebra O S'] [Algebra S' Ω] [IsScalarTower O S' Ω]
      (e' : Ω ⊗[S'] (S' ⊗[O] G.level v) ≃ₐc[Ω] Ω ⊗[O] G.level v),
      (∀ (ω : Ω) (s : S') (a : G.level v), e' (ω ⊗ₜ[S'] (s ⊗ₜ[O] a)) = (s • ω) ⊗ₜ[O] a) →
      ∀ z : S' ⊗[O] G.level v, e' ((1 : Ω) ⊗ₜ[S'] z) = ((IsScalarTower.toAlgHom O S' Ω).toLinearMap.rTensor (G.level v)) z := by
    intro S' _ _ _ _ e' he' z
    induction z using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
    | tmul s a =>
      rw [he', LinearMap.rTensor_tmul]
      congr 1
      rw [Algebra.smul_def, mul_one]
      rfl
  let ΨK : (H.baseChange Ω).level v →ₐc[Ω] (G.baseChange Ω).level v :=
    eK'.toBialgHom.comp ((Bialgebra.TensorProduct.map (BialgHom.id Ω Ω) gK).comp eK.symm.toBialgHom)
  let Ψh : (H.baseChange Ω).level v →ₐc[Ω] (G.baseChange Ω).level v :=
    eO'.toBialgHom.comp ((Bialgebra.TensorProduct.map (BialgHom.id Ω Ω) gOh).comp eO.symm.toBialgHom)
  have hΨK1 : ∀ b : H.level v, ΨK ((1 : Ω) ⊗ₜ[O] b) =
      ((IsScalarTower.toAlgHom O K Ω).toLinearMap.rTensor (G.level v)) (gK ((1 : K) ⊗ₜ[O] b)) := by
    intro b
    have hs : eK ((1 : Ω) ⊗ₜ[K] ((1 : K) ⊗ₜ[O] b)) = (1 : Ω) ⊗ₜ[O] b := by rw [heK, one_smul]
    show eK' (Bialgebra.TensorProduct.map (BialgHom.id Ω Ω) gK (eK.symm ((1 : Ω) ⊗ₜ[O] b))) = _
    rw [← hs, BialgEquiv.symm_apply_apply]
    change eK' ((1 : Ω) ⊗ₜ[K] gK ((1 : K) ⊗ₜ[O] b)) = _
    exact hrT K eK' heK' _
  have hΨh1 : ∀ b : H.level v, Ψh ((1 : Ω) ⊗ₜ[O] b) =
      ((IsScalarTower.toAlgHom O Oh Ω).toLinearMap.rTensor (G.level v)) (gOh ((1 : Oh) ⊗ₜ[O] b)) := by
    intro b
    have hs : eO ((1 : Ω) ⊗ₜ[Oh] ((1 : Oh) ⊗ₜ[O] b)) = (1 : Ω) ⊗ₜ[O] b := by rw [heO, one_smul]
    show eO' (Bialgebra.TensorProduct.map (BialgHom.id Ω Ω) gOh (eO.symm ((1 : Ω) ⊗ₜ[O] b))) = _
    rw [← hs, BialgEquiv.symm_apply_apply]
    change eO' ((1 : Ω) ⊗ₜ[Oh] gOh ((1 : Oh) ⊗ₜ[O] b)) = _
    exact hrT Oh eO' heO' _

  have hlift : ∀ (S' : Type) [CommRing S'] [Algebra O S'] [Algebra S' Ω] [IsScalarTower O S' Ω]
      (f : Ω ⊗[O] G.level v →ₐ[Ω] Ω) (z : S' ⊗[O] G.level v),
      f (((IsScalarTower.toAlgHom O S' Ω).toLinearMap.rTensor (G.level v)) z) =
        Algebra.TensorProduct.lift (Algebra.ofId S' Ω)
          ((f.restrictScalars O).comp (Algebra.TensorProduct.includeRight : G.level v →ₐ[O] Ω ⊗[O] G.level v))
          (fun _ _ => Commute.all _ _) z := by
    intro S' _ _ _ _ f z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul s a =>
      rw [LinearMap.rTensor_tmul, Algebra.TensorProduct.lift_tmul]
      change f ((IsScalarTower.toAlgHom O S' Ω s) ⊗ₜ[O] a) = algebraMap S' Ω s * f ((1 : Ω) ⊗ₜ[O] a)
      rw [show (IsScalarTower.toAlgHom O S' Ω s) ⊗ₜ[O] a = algebraMap S' Ω s • ((1 : Ω) ⊗ₜ[O] a) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl, map_smul, smul_eq_mul]
  have hΨ : ΨK = Ψh :=
    HopfAlgebra.bialgHom_eq_of_forall_algHom_comp_eq_of_charZero Ω Ω ((G.baseChange Ω).level v) ((H.baseChange Ω).level v)
      ΨK Ψh (by
        intro f
        apply Algebra.TensorProduct.ext
        · exact Subsingleton.elim _ _
        · apply AlgHom.ext
          intro b'
          change f (ΨK ((1 : Ω) ⊗ₜ[O] b')) = f (Ψh ((1 : Ω) ⊗ₜ[O] b'))
          rw [hΨK1, hΨh1]
          exact (hlift K f _).trans ((hpts _ b').trans (hlift Oh f _).symm))
  rw [← hΨK1, ← hΨh1, hΨ]

theorem T4_fin
    {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (L : Type) [Field L] [Algebra O L] [Algebra K L] [IsScalarTower O K L]
    {p h h' : ℕ} (G : PDivisibleGroup O p h) (H : PDivisibleGroup O p h')
    (F : G.Points L →+ H.Points L)
    (eG : ∀ v : ℕ, G.Point L v ≃* (G.baseChange K).Point L v)
    (eH : ∀ v : ℕ, H.Point L v ≃* (H.baseChange K).Point L v)
    (EH : H.Points L ≃+ (H.baseChange K).Points L)
    (heGa : ∀ (v : ℕ) (x : G.Point L v) (s : K) (a : G.level v),
        PDivisibleGroup.Point.toAlgHom (eG v x) (s ⊗ₜ[O] a) = s • PDivisibleGroup.Point.toAlgHom x a)
    (heHa : ∀ (v : ℕ) (x : H.Point L v) (s : K) (a : H.level v),
        PDivisibleGroup.Point.toAlgHom (eH v x) (s ⊗ₜ[O] a) = s • PDivisibleGroup.Point.toAlgHom x a)
    (hEHb : ∀ (v : ℕ) (x : H.Point L v),
        EH (H.pointsMkAdd L v (Additive.ofMul x)) = (H.baseChange K).pointsMkAdd L v (Additive.ofMul (eH v x)))
    (ψK : ∀ v : ℕ, (H.baseChange K).level v →ₐc[K] (G.baseChange K).level v)
    (hψKt : ∀ v : ℕ, ((G.baseChange K).transition v).comp (ψK (v + 1)) = (ψK v).comp ((H.baseChange K).transition v))
    (hψKpts : ∀ (v : ℕ) (x : G.Point L v), EH (F (G.pointsMkAdd L v (Additive.ofMul x))) =
        (H.baseChange K).pointsMkAdd L v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom (eG v x)).comp (ψK v : (H.baseChange K).level v →ₐ[K] (G.baseChange K).level v)))))
    (hψKuniq : ∀ φ' : ∀ v : ℕ, (H.baseChange K).level v →ₐc[K] (G.baseChange K).level v,
        (∀ (v : ℕ) (x : G.Point L v), EH (F (G.pointsMkAdd L v (Additive.ofMul x))) =
          (H.baseChange K).pointsMkAdd L v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom (eG v x)).comp (φ' v : (H.baseChange K).level v →ₐ[K] (G.baseChange K).level v))))) →
        φ' = ψK)
    (φ : ∀ v : ℕ, H.level v →ₐc[O] G.level v)
    (hφ : ∀ v : ℕ, Bialgebra.TensorProduct.map (BialgHom.id K K) (φ v) = ψK v) :
    (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (H.transition v)) ∧
      (∀ (v : ℕ) (x : G.Point L v),
        F (G.pointsMkAdd L v (Additive.ofMul x)) =
          H.pointsMkAdd L v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : H.level v →ₐ[O] G.level v))))) ∧
      (∀ φ' : ∀ v : ℕ, H.level v →ₐc[O] G.level v,
        (∀ (v : ℕ) (x : G.Point L v),
          F (G.pointsMkAdd L v (Additive.ofMul x)) =
            H.pointsMkAdd L v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
              ((PDivisibleGroup.Point.toAlgHom x).comp (φ' v : H.level v →ₐ[O] G.level v))))) →
        φ' = φ) := by
  classical

  have free_inj : ∀ (M : Type) [AddCommGroup M] [Module O M] [Module.Flat O M],
      Function.Injective (fun a : M => (1 : K) ⊗ₜ[O] a) := by
    intro M _ _ _
    have h1 : Function.Injective ((Algebra.linearMap O K).rTensor M) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective O K)
    have h2 : (fun a : M => (1 : K) ⊗ₜ[O] a) = ((Algebra.linearMap O K).rTensor M) ∘ (TensorProduct.lid O M).symm := by
      funext a
      simp [LinearMap.rTensor_tmul]
    rw [h2]
    exact h1.comp (TensorProduct.lid O M).symm.injective
  have e1 : ∀ (w : ℕ) (b : H.level w), (1 : K) ⊗ₜ[O] φ w b = ψK w ((1 : K) ⊗ₜ[O] b) := fun w b => by
    have t := DFunLike.congr_fun (hφ w) ((1 : K) ⊗ₜ[O] b)
    rw [Bialgebra.TensorProduct.map_tmul] at t
    exact t
  have e1k : ∀ (w : ℕ) (k : K) (b : H.level w), ψK w (k ⊗ₜ[O] b) = k ⊗ₜ[O] φ w b := fun w k b => by
    have t := DFunLike.congr_fun (hφ w) (k ⊗ₜ[O] b)
    rw [Bialgebra.TensorProduct.map_tmul] at t
    exact t.symm
  have inj_bc : ∀ (w : ℕ) (f₁ f₂ : H.level w →ₐc[O] G.level w),
      Bialgebra.TensorProduct.map (BialgHom.id K K) f₁ = Bialgebra.TensorProduct.map (BialgHom.id K K) f₂ → f₁ = f₂ := by
    intro w f₁ f₂ h12
    apply BialgHom.ext
    intro b
    have h' := DFunLike.congr_fun h12 ((1 : K) ⊗ₜ[O] b)
    rw [Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul] at h'
    exact free_inj (G.level w) h'
  have key : ∀ (v : ℕ) (f : H.level v →ₐc[O] G.level v)
      (ψ : (H.baseChange K).level v →ₐc[K] (G.baseChange K).level v),
      (∀ (k : K) (b : H.level v), ψ (k ⊗ₜ[O] b) = k ⊗ₜ[O] f b) →
      ∀ x : G.Point L v,
      eH v (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (f : H.level v →ₐ[O] G.level v))) =
        PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom (eG v x)).comp
          (ψ : (H.baseChange K).level v →ₐ[K] (G.baseChange K).level v)) := by
    intro v f ψ hψf x
    apply (PDivisibleGroup.Point.ofAlgHom_toAlgHom (eH v _)).symm.trans
    apply congrArg PDivisibleGroup.Point.ofAlgHom
    apply Algebra.TensorProduct.ext'
    intro k b
    change PDivisibleGroup.Point.toAlgHom (eH v (PDivisibleGroup.Point.ofAlgHom
        ((PDivisibleGroup.Point.toAlgHom x).comp (f : H.level v →ₐ[O] G.level v)))) (k ⊗ₜ[O] b) =
      PDivisibleGroup.Point.toAlgHom (eG v x) (ψ (k ⊗ₜ[O] b))
    rw [heHa, hψf, heGa]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro v
    apply BialgHom.ext
    intro b
    apply free_inj (G.level v)
    show ((1 : K) ⊗ₜ[O] (G.transition v (φ (v + 1) b)) : (G.baseChange K).level v) =
      ((1 : K) ⊗ₜ[O] (φ v (H.transition v b)) : (G.baseChange K).level v)
    have s1 : ((G.baseChange K).transition v ((1 : K) ⊗ₜ[O] φ (v + 1) b) : (G.baseChange K).level v) =
        (1 : K) ⊗ₜ[O] (G.transition v (φ (v + 1) b)) := PDivisibleGroup.baseChange_transition_tmul G K v 1 _
    have s2 : ((H.baseChange K).transition v ((1 : K) ⊗ₜ[O] b) : (H.baseChange K).level v) =
        (1 : K) ⊗ₜ[O] (H.transition v b) := PDivisibleGroup.baseChange_transition_tmul H K v 1 _
    have s3 := DFunLike.congr_fun (hψKt v) ((1 : K) ⊗ₜ[O] b)
    change (G.baseChange K).transition v (ψK (v + 1) ((1 : K) ⊗ₜ[O] b)) =
      ψK v ((H.baseChange K).transition v ((1 : K) ⊗ₜ[O] b)) at s3
    rw [← e1, s1, s2, ← e1] at s3
    exact s3
  · intro v x
    apply EH.injective
    rw [hψKpts v x, hEHb, key v (φ v) (ψK v) (e1k v) x]
  · intro φ' hφ'
    funext v
    apply inj_bc v
    rw [hφ v]
    have huniq := hψKuniq (fun w => Bialgebra.TensorProduct.map (BialgHom.id K K) (φ' w)) (by
      intro w x
      rw [hφ' w x, hEHb, key w (φ' w) (Bialgebra.TensorProduct.map (BialgHom.id K K) (φ' w))
        (fun k b => Bialgebra.TensorProduct.map_tmul (BialgHom.id K K) (φ' w) k b)])
    exact congrFun huniq v

theorem T4_emb (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p) :
    ∃ ι : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl p,
      (∀ t : AlgebraicClosure ℚ, t ∈ Pl ↔ ‖ι t‖ ≤ 1) ∧
      (∀ t : AlgebraicClosure ℚ, Pl.valuation t < 1 ↔ ‖ι t‖ < 1) ∧
      (∀ τl : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ t, ι (τ t) = τl (ι t)) := by
  classical
  obtain ⟨g, hg⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime (Fact.out : p.Prime)
    (padicPlace p) Pl (padicPlace_liesOverPrime p) hPl
  let ι : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl p :=
    (padicEmbedding p).comp (g.symm : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)
  have hι : ∀ t, ι t = padicEmbedding p (g.symm t) := fun t => rfl
  have hginv : ∀ t, g⁻¹ t = g.symm t := fun t => rfl
  have hmem : ∀ t : AlgebraicClosure ℚ, t ∈ Pl ↔ ‖ι t‖ ≤ 1 := by
    intro t
    rw [← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, mem_padicPlace_iff,
      hginv, hι, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  refine ⟨ι, hmem, ?_, ?_⟩
  · intro t
    by_cases ht : t = 0
    · subst ht
      simp
    have hvpos : 0 < Pl.valuation t := (Valuation.pos_iff _).2 ht
    have hnpos : 0 < ‖ι t‖ := norm_pos_iff.2 ((map_ne_zero ι).2 ht)
    have h1 : Pl.valuation t < 1 ↔ ¬ t⁻¹ ∈ Pl := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, inv_le_one₀ hvpos, not_le]
    have h2 : ‖ι t‖ < 1 ↔ ¬ t⁻¹ ∈ Pl := by
      rw [hmem, map_inv₀, norm_inv, inv_le_one₀ hnpos, not_le]
    rw [h1, h2]
  · intro τl
    refine ⟨g * localGaloisToGlobal p τl * g⁻¹, fun t => ?_⟩
    rw [hι, hι, ← padicEmbedding_localGaloisToGlobal p τl, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hginv,
      AlgEquiv.symm_apply_apply]

set_option maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime]

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh] [IsDiscreteValuationRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ IsLocalRing.maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    {h h' : ℕ} (G : PDivisibleGroup Rh p h) (H : PDivisibleGroup Rh p h')
    (F : G.Points (AlgebraicClosure ℚ) →+ H.Points (AlgebraicClosure ℚ))

    (hFlev : ∀ (v : ℕ) (x : G.Point (AlgebraicClosure ℚ) v), ∃ y : H.Point (AlgebraicClosure ℚ) v,
      F (G.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y))

    (hFgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ) (z : G.Points (AlgebraicClosure ℚ)), F (τ • z) = τ • F z) :
    ∃ φ : ∀ v : ℕ, H.level v →ₐc[Rh] G.level v,
      (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (H.transition v)) ∧
      (∀ (v : ℕ) (x : G.Point (AlgebraicClosure ℚ) v),
        F (G.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) =
          H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : H.level v →ₐ[Rh] G.level v))))) ∧

      (∀ φ' : ∀ v : ℕ, H.level v →ₐc[Rh] G.level v,
        (∀ (v : ℕ) (x : G.Point (AlgebraicClosure ℚ) v),
          F (G.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) =
            H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
              ((PDivisibleGroup.Point.toAlgHom x).comp (φ' v : H.level v →ₐ[Rh] G.level v))))) →
        φ' = φ) := by
  classical

  obtain ⟨ιA, hmem, hval, hgalres⟩ := T4_emb p Pl hPl
  let ι : AlgebraicClosure ℚ →+* PadicAlgCl p := ιA.toRingHom
  replace hmem : ∀ t : AlgebraicClosure ℚ, t ∈ Pl ↔ ‖ι t‖ ≤ 1 := hmem
  replace hval : ∀ t : AlgebraicClosure ℚ, Pl.valuation t < 1 ↔ ‖ι t‖ < 1 := hval
  replace hgalres : ∀ τl : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ t, ι (τ t) = τl (ι t) := hgalres

  obtain ⟨K', hK'fd, hRK'⟩ := ValuationSubring.exists_intermediateField_finiteDimensional_forall_apply_mem_of_isDiscreteValuationRing_of_liesOverPrime p Pl hPl Rh hRA hRloc hres ι hmem
  haveI := hK'fd

  have hιO : ∀ x : Rh, ι (algebraMap Rh (AlgebraicClosure ℚ) x) ∈ PadicAlgCl.ringOfIntegers p K' := fun x =>
    ⟨(PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p _).2 ((hmem _).1 (hRA x)), hRK' x⟩
  let φR : Rh →+* PadicAlgCl.ringOfIntegers p K' :=
    { toFun := fun x => ⟨ι (algebraMap Rh (AlgebraicClosure ℚ) x), hιO x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  let Oh : Type := PadicAlgCl.ringOfIntegers p K'
  letI : Algebra Rh Oh := φR.toAlgebra
  letI : Algebra Rh (PadicAlgCl p) := (ι.comp (algebraMap Rh (AlgebraicClosure ℚ))).toAlgebra
  haveI : IsScalarTower Rh Oh (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hinjOh : Function.Injective (algebraMap Oh (PadicAlgCl p)) := Subtype.val_injective

  let ιRh : AlgebraicClosure ℚ →ₐ[Rh] PadicAlgCl p := { ι with commutes' := fun _ => rfl }

  let K := FractionRing Rh
  have hinj : Function.Injective (algebraMap Rh (AlgebraicClosure ℚ)) := FaithfulSMul.algebraMap_injective Rh _
  letI : Algebra K (AlgebraicClosure ℚ) := (IsFractionRing.lift hinj : K →+* AlgebraicClosure ℚ).toAlgebra
  haveI : IsScalarTower Rh K (AlgebraicClosure ℚ) := IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (K := K) hinj x).symm
  haveI : CharZero K := (algebraMap K (AlgebraicClosure ℚ)).charZero
  haveI : Algebra.IsAlgebraic K (AlgebraicClosure ℚ) := by

    haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    haveI : IsScalarTower ℚ K (AlgebraicClosure ℚ) := IsScalarTower.of_algebraMap_eq fun q => by simp
    exact Algebra.IsAlgebraic.tower_top (K := ℚ) (L := K)
  haveI : IsAlgClosure K (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  have hinj' : Function.Injective (algebraMap Rh (PadicAlgCl p)) := ι.injective.comp hinj
  letI : Algebra K (PadicAlgCl p) := (IsFractionRing.lift hinj' : K →+* PadicAlgCl p).toAlgebra
  haveI : IsScalarTower Rh K (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (K := K) hinj' x).symm

  obtain ⟨eG, EG, heGa, hEGb, -, hEGd⟩ :=
    PDivisibleGroup.exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange G K (AlgebraicClosure ℚ)
  obtain ⟨eH, EH, heHa, hEHb, -, hEHd⟩ :=
    PDivisibleGroup.exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange H K (AlgebraicClosure ℚ)

  let F' : (G.baseChange K).Points (AlgebraicClosure ℚ) →+ (H.baseChange K).Points (AlgebraicClosure ℚ) :=
    (EH : H.Points (AlgebraicClosure ℚ) →+ (H.baseChange K).Points (AlgebraicClosure ℚ)).comp
      (F.comp (EG.symm : (G.baseChange K).Points (AlgebraicClosure ℚ) →+ G.Points (AlgebraicClosure ℚ)))
  have hF'lev : ∀ (v : ℕ) (x : (G.baseChange K).Point (AlgebraicClosure ℚ) v), ∃ y : (H.baseChange K).Point (AlgebraicClosure ℚ) v,
      F' ((G.baseChange K).pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) =
        (H.baseChange K).pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y) := by
    intro v x'
    obtain ⟨x, rfl⟩ := (eG v).surjective x'
    obtain ⟨y, hy⟩ := hFlev v x
    refine ⟨eH v y, ?_⟩
    show EH (F (EG.symm ((G.baseChange K).pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (eG v x))))) = _
    rw [← hEGb, AddEquiv.symm_apply_apply, hy, hEHb]
  have hF'gal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[K] AlgebraicClosure ℚ) (z : (G.baseChange K).Points (AlgebraicClosure ℚ)),
      F' (τ • z) = τ • F' z := by
    intro τ z'
    obtain ⟨z, rfl⟩ := EG.surjective z'
    show EH (F (EG.symm (τ • EG z))) = τ • EH (F (EG.symm (EG z)))
    rw [← hEGd, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hFgal, hEHd]

  obtain ⟨ψK, hψKt, hψKpts, hψKuniq⟩ :=
    PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_field
      p (AlgebraicClosure ℚ) (G.baseChange K) (H.baseChange K) F' hF'lev hF'gal

  have hF'mk : ∀ (w : ℕ) (x : G.Point (AlgebraicClosure ℚ) w),
      F' ((G.baseChange K).pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (eG w x))) =
        EH (F (G.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul x))) := fun w x => by
    show EH (F (EG.symm ((G.baseChange K).pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (eG w x))))) = _
    rw [← hEGb, AddEquiv.symm_apply_apply]

  obtain ⟨exG, -, hexG, -, -, -⟩ :=
    PDivisibleGroup.exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed G (AlgebraicClosure ℚ) (PadicAlgCl p) ιRh
  obtain ⟨exH, -, hexH, -, -, -⟩ :=
    PDivisibleGroup.exists_mulEquiv_point_addEquiv_points_eq_pointMap_of_isAlgClosed H (AlgebraicClosure ℚ) (PadicAlgCl p) ιRh
  have hbijG : ∀ v, Function.Bijective (G.pointMap ιRh v) := fun v => by
    have hb := (exG v).bijective
    rwa [show (⇑(exG v) : G.Point (AlgebraicClosure ℚ) v → G.Point (PadicAlgCl p) v) = ⇑(G.pointMap ιRh v) from
      funext (hexG v)] at hb
  have hbijH : ∀ v, Function.Bijective (H.pointMap ιRh v) := fun v => by
    have hb := (exH v).bijective
    rwa [show (⇑(exH v) : H.Point (AlgebraicClosure ℚ) v → H.Point (PadicAlgCl p) v) = ⇑(H.pointMap ιRh v) from
      funext (hexH v)] at hb
  have hEGx : Function.Bijective (G.pointsMap ιRh) := by
    refine ⟨G.pointsMap_injective_of_injective ιRh ι.injective, fun z => ?_⟩
    obtain ⟨v, x, rfl⟩ := PDivisibleGroup.Points.exists_mkAdd (G := G) z
    obtain ⟨y, rfl⟩ := (hbijG v).2 x
    exact ⟨G.pointsMkAdd _ v (Additive.ofMul y), G.pointsMap_pointsMkAdd ιRh v y⟩
  have hEHx : Function.Bijective (H.pointsMap ιRh) := by
    refine ⟨H.pointsMap_injective_of_injective ιRh ι.injective, fun z => ?_⟩
    obtain ⟨v, x, rfl⟩ := PDivisibleGroup.Points.exists_mkAdd (G := H) z
    obtain ⟨y, rfl⟩ := (hbijH v).2 x
    exact ⟨H.pointsMkAdd _ v (Additive.ofMul y), H.pointsMap_pointsMkAdd ιRh v y⟩
  let EGx : G.Points (AlgebraicClosure ℚ) ≃+ G.Points (PadicAlgCl p) := AddEquiv.ofBijective (G.pointsMap ιRh) hEGx
  let EHx : H.Points (AlgebraicClosure ℚ) ≃+ H.Points (PadicAlgCl p) := AddEquiv.ofBijective (H.pointsMap ιRh) hEHx
  obtain ⟨eGh, EGh, heGha, hEGhb, -, hEGhd⟩ :=
    PDivisibleGroup.exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange G Oh (PadicAlgCl p)
  obtain ⟨eHh, EHh, heHha, hEHhb, -, hEHhd⟩ :=
    PDivisibleGroup.exists_mulEquiv_point_baseChange_and_addEquiv_points_baseChange H Oh (PadicAlgCl p)
  let Fh : (G.baseChange Oh).Points (PadicAlgCl p) →+ (H.baseChange Oh).Points (PadicAlgCl p) :=
    (EHh : H.Points (PadicAlgCl p) →+ _).comp ((EHx : H.Points (AlgebraicClosure ℚ) →+ _).comp
      (F.comp ((EGx.symm : G.Points (PadicAlgCl p) →+ _).comp (EGh.symm : (G.baseChange Oh).Points (PadicAlgCl p) →+ _))))
  have hFhlev : ∀ (v : ℕ) (x : (G.baseChange Oh).Point (PadicAlgCl p) v), ∃ y : (H.baseChange Oh).Point (PadicAlgCl p) v,
      Fh ((G.baseChange Oh).pointsMkAdd (PadicAlgCl p) v (Additive.ofMul x)) =
        (H.baseChange Oh).pointsMkAdd (PadicAlgCl p) v (Additive.ofMul y) := by
    intro v x'
    obtain ⟨x1, rfl⟩ := (eGh v).surjective x'
    obtain ⟨x, rfl⟩ := (hbijG v).2 x1
    obtain ⟨y, hy⟩ := hFlev v x
    refine ⟨eHh v (H.pointMap ιRh v y), ?_⟩
    show EHh (EHx (F (EGx.symm (EGh.symm ((G.baseChange Oh).pointsMkAdd (PadicAlgCl p) v
      (Additive.ofMul (eGh v (G.pointMap ιRh v x)))))))) = _
    rw [← hEGhb, AddEquiv.symm_apply_apply,
      show EGx.symm (G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (G.pointMap ιRh v x))) =
          G.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x) from
        (AddEquiv.symm_apply_eq EGx).2 (G.pointsMap_pointsMkAdd ιRh v x).symm,
      hy]
    show EHh (H.pointsMap ιRh (H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y))) = _
    rw [H.pointsMap_pointsMkAdd, hEHhb]
  have hFhgal : ∀ (τl : PadicAlgCl p ≃ₐ[Oh] PadicAlgCl p) (z : (G.baseChange Oh).Points (PadicAlgCl p)),
      Fh (τl • z) = τl • Fh z := by

    intro τl z
    obtain ⟨τ, hτ⟩ := hgalres (PadicAlgCl.ringOfIntegers.restrictScalarsRat p K' τl)
    have hτR : ∀ x : Rh, τ (algebraMap Rh (AlgebraicClosure ℚ) x) = algebraMap Rh (AlgebraicClosure ℚ) x := by
      intro x
      apply ι.injective
      rw [hτ, PadicAlgCl.ringOfIntegers.restrictScalarsRat_apply]
      exact τl.commutes (φR x)
    let τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) hτR
    let τlR : PadicAlgCl p →ₐ[Rh] PadicAlgCl p :=
      ((τl.restrictScalars Rh : PadicAlgCl p ≃ₐ[Rh] PadicAlgCl p) : PadicAlgCl p →ₐ[Rh] PadicAlgCl p)
    have hcomp : τlR.comp ιRh = ιRh.comp (τ' : AlgebraicClosure ℚ →ₐ[Rh] AlgebraicClosure ℚ) :=
      AlgHom.ext fun t => (hτ t).symm
    have hGx : ∀ z₁ : G.Points (AlgebraicClosure ℚ), (τl.restrictScalars Rh) • EGx z₁ = EGx (τ' • z₁) := by
      intro z₁
      show G.pointsMap τlR (G.pointsMap ιRh z₁) = G.pointsMap ιRh (G.pointsMap (τ' : AlgebraicClosure ℚ →ₐ[Rh] AlgebraicClosure ℚ) z₁)
      rw [← AddMonoidHom.comp_apply, ← G.pointsMap_comp, hcomp, G.pointsMap_comp, AddMonoidHom.comp_apply]
    have hHx : ∀ w : H.Points (AlgebraicClosure ℚ), (τl.restrictScalars Rh) • EHx w = EHx (τ' • w) := by
      intro w
      show H.pointsMap τlR (H.pointsMap ιRh w) = H.pointsMap ιRh (H.pointsMap (τ' : AlgebraicClosure ℚ →ₐ[Rh] AlgebraicClosure ℚ) w)
      rw [← AddMonoidHom.comp_apply, ← H.pointsMap_comp, hcomp, H.pointsMap_comp, AddMonoidHom.comp_apply]
    obtain ⟨z₀, rfl⟩ := EGh.surjective z
    obtain ⟨z₁, rfl⟩ := EGx.surjective z₀
    show EHh (EHx (F (EGx.symm (EGh.symm (τl • EGh (EGx z₁)))))) = τl • EHh (EHx (F (EGx.symm (EGh.symm (EGh (EGx z₁))))))
    rw [← hEGhd, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hGx, AddEquiv.symm_apply_apply,
      AddEquiv.symm_apply_apply, hFgal, ← hHx, hEHhd]
  obtain ⟨φh, hφht, hφhpts, hφhuniq⟩ :=
    PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_ringOfIntegers
      p K' (G.baseChange Oh) (H.baseChange Oh) Fh hFhlev hFhgal

  have hpts : ∀ (v : ℕ) (y : G.level v →ₐ[Rh] PadicAlgCl p) (b : H.level v),
      Algebra.TensorProduct.lift (Algebra.ofId K (PadicAlgCl p)) y (fun _ _ => Commute.all _ _) (ψK v ((1 : K) ⊗ₜ[Rh] b)) =
        Algebra.TensorProduct.lift (Algebra.ofId Oh (PadicAlgCl p)) y (fun _ _ => Commute.all _ _) (φh v ((1 : Oh) ⊗ₜ[Rh] b)) := by
    intro v y b
    obtain ⟨x₀, hx₀⟩ := (hbijG v).2 (PDivisibleGroup.Point.ofAlgHom y)
    obtain ⟨x₁, hx₁⟩ := hFlev v x₀
    have hy : ∀ a : G.level v, y a = ι (PDivisibleGroup.Point.toAlgHom x₀ a) := fun a => by
      rw [show y = PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom y) from rfl, ← hx₀]; rfl

    have hιK : ι.comp (algebraMap K (AlgebraicClosure ℚ)) = algebraMap K (PadicAlgCl p) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors Rh)
      ext r
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply Rh K (AlgebraicClosure ℚ), ← IsScalarTower.algebraMap_apply Rh K (PadicAlgCl p)]
      rfl

    let ιK : AlgebraicClosure ℚ →ₐ[K] PadicAlgCl p := { ι with commutes' := fun k => DFunLike.congr_fun hιK k }
    have hL : Algebra.TensorProduct.lift (Algebra.ofId K (PadicAlgCl p)) y (fun _ _ => Commute.all _ _) =
        ιK.comp (PDivisibleGroup.Point.toAlgHom (eG v x₀)) := by
      apply Algebra.TensorProduct.ext'
      intro k a
      rw [Algebra.TensorProduct.lift_tmul]
      change Algebra.ofId K (PadicAlgCl p) k * y a = ιK (PDivisibleGroup.Point.toAlgHom (eG v x₀) (k ⊗ₜ[Rh] a))
      rw [heGa, hy, Algebra.smul_def, map_mul]
      congr 1
      exact (ιK.commutes k).symm
    have hL2 : PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom (eG v x₀)).comp
        (ψK v : (H.baseChange K).level v →ₐ[K] (G.baseChange K).level v)) = eH v x₁ := by
      have h1 := hψKpts v (eG v x₀)
      rw [hF'mk, hx₁, hEHb] at h1
      exact Additive.ofMul.injective ((H.baseChange K).pointsMkAdd_injective v h1.symm)

    have hR : Algebra.TensorProduct.lift (Algebra.ofId Oh (PadicAlgCl p)) y (fun _ _ => Commute.all _ _) =
        PDivisibleGroup.Point.toAlgHom (eGh v (G.pointMap ιRh v x₀)) := by
      apply Algebra.TensorProduct.ext'
      intro s a
      rw [Algebra.TensorProduct.lift_tmul]
      change Algebra.ofId Oh (PadicAlgCl p) s * y a = PDivisibleGroup.Point.toAlgHom (eGh v (G.pointMap ιRh v x₀)) (s ⊗ₜ[Rh] a)
      rw [heGha, Algebra.smul_def, hy]
      rfl
    have hR2 : PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom (eGh v (G.pointMap ιRh v x₀))).comp
        (φh v : (H.baseChange Oh).level v →ₐ[Oh] (G.baseChange Oh).level v)) = eHh v (H.pointMap ιRh v x₁) := by
      have h2 := hφhpts v (eGh v (G.pointMap ιRh v x₀))
      have h3 : Fh ((G.baseChange Oh).pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (eGh v (G.pointMap ιRh v x₀)))) =
          (H.baseChange Oh).pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (eHh v (H.pointMap ιRh v x₁))) := by
        show EHh (EHx (F (EGx.symm (EGh.symm ((G.baseChange Oh).pointsMkAdd (PadicAlgCl p) v
          (Additive.ofMul (eGh v (G.pointMap ιRh v x₀)))))))) = _
        rw [← hEGhb, AddEquiv.symm_apply_apply,
          show EGx.symm (G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (G.pointMap ιRh v x₀))) =
              G.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x₀) from
            (AddEquiv.symm_apply_eq EGx).2 (G.pointsMap_pointsMkAdd ιRh v x₀).symm,
          hx₁]
        show EHh (H.pointsMap ιRh (H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x₁))) = _
        rw [H.pointsMap_pointsMkAdd, hEHhb]
      rw [h3] at h2
      exact Additive.ofMul.injective ((H.baseChange Oh).pointsMkAdd_injective v h2.symm)

    have e2 := congrArg (fun pt => PDivisibleGroup.Point.toAlgHom pt ((1 : K) ⊗ₜ[Rh] b)) hL2
    change PDivisibleGroup.Point.toAlgHom (eG v x₀) (ψK v ((1 : K) ⊗ₜ[Rh] b)) =
      PDivisibleGroup.Point.toAlgHom (eH v x₁) ((1 : K) ⊗ₜ[Rh] b) at e2
    rw [heHa, one_smul] at e2
    have e3 := congrArg (fun pt => PDivisibleGroup.Point.toAlgHom pt ((1 : Oh) ⊗ₜ[Rh] b)) hR2
    change PDivisibleGroup.Point.toAlgHom (eGh v (G.pointMap ιRh v x₀)) (φh v ((1 : Oh) ⊗ₜ[Rh] b)) =
      PDivisibleGroup.Point.toAlgHom (eHh v (H.pointMap ιRh v x₁)) ((1 : Oh) ⊗ₜ[Rh] b) at e3
    rw [heHha, one_smul] at e3
    rw [hL, hR]
    change ιK (PDivisibleGroup.Point.toAlgHom (eG v x₀) (ψK v ((1 : K) ⊗ₜ[Rh] b))) =
      PDivisibleGroup.Point.toAlgHom (eGh v (G.pointMap ιRh v x₀)) (φh v ((1 : Oh) ⊗ₜ[Rh] b))
    rw [e2, e3]
    rfl
  have hagree : ∀ (v : ℕ) (b : H.level v),
      ((IsScalarTower.toAlgHom Rh K (PadicAlgCl p)).toLinearMap.rTensor (G.level v)) (ψK v ((1 : K) ⊗ₜ b)) =
        ((IsScalarTower.toAlgHom Rh Oh (PadicAlgCl p)).toLinearMap.rTensor (G.level v)) (φh v ((1 : Oh) ⊗ₜ b)) :=
    fun v => T4_agree_core K Oh (PadicAlgCl p) G H v (ψK v) (φh v) (hpts v)

  have hcap : ∀ (x : K) (y : Oh), algebraMap K (PadicAlgCl p) x = algebraMap Oh (PadicAlgCl p) y →
      ∃ z : Rh, algebraMap Rh K z = x := by

    intro x y hxy
    rcases ValuationRing.isInteger_or_isInteger Rh x with ⟨z, hz⟩ | ⟨z, hz⟩
    · exact ⟨z, hz⟩
    · by_cases hx0 : x = 0
      · exact ⟨0, by rw [map_zero, hx0]⟩
      by_cases hzu : IsUnit z
      · obtain ⟨u, rfl⟩ := hzu
        refine ⟨((u⁻¹ : Rhˣ) : Rh), ?_⟩
        have hu : algebraMap Rh K ((u⁻¹ : Rhˣ) : Rh) * algebraMap Rh K (u : Rh) = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        rw [hz] at hu
        calc algebraMap Rh K ((u⁻¹ : Rhˣ) : Rh)
            = algebraMap Rh K ((u⁻¹ : Rhˣ) : Rh) * x⁻¹ * x := by rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one]
          _ = x := by rw [hu, one_mul]
      · exfalso
        have hzm : z ∈ IsLocalRing.maximalIdeal Rh := (IsLocalRing.mem_maximalIdeal _).2 hzu
        have h1 : ‖ι (algebraMap Rh (AlgebraicClosure ℚ) z)‖ < 1 := (hval _).1 ((hRloc z).1 hzm)
        have h2 : ‖algebraMap Oh (PadicAlgCl p) y‖ ≤ 1 :=
          (PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p _).1 y.2.1
        have h3 : ι (algebraMap Rh (AlgebraicClosure ℚ) z) = (algebraMap K (PadicAlgCl p) x)⁻¹ := by
          rw [← map_inv₀, ← hz, ← IsScalarTower.algebraMap_apply Rh K (PadicAlgCl p) z]
          rfl
        have hy0 : algebraMap Oh (PadicAlgCl p) y ≠ 0 := by
          rw [← hxy]; exact (map_ne_zero _).2 hx0
        rw [h3, hxy, norm_inv, inv_lt_one₀ (norm_pos_iff.2 hy0)] at h1
        exact absurd h2 (not_le.2 h1)
  have hL3 : ∀ v : ℕ, ∃! φv : H.level v →ₐc[Rh] G.level v,
      Bialgebra.TensorProduct.map (BialgHom.id K K) φv = ψK v ∧
        Bialgebra.TensorProduct.map (BialgHom.id Oh Oh) φv = φh v := fun v =>
    BialgHom.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq
      Rh K Oh (PadicAlgCl p) hinjOh hcap (G.level v) (H.level v) (ψK v) (φh v) (hagree v)
  choose φ hφ hφuniq using hL3

  exact ⟨φ, T4_fin K (AlgebraicClosure ℚ) G H F eG eH EH heGa heHa hEHb ψK hψKt
    (fun v x => (hF'mk v x).symm.trans (hψKpts v (eG v x)))
    (fun φ' hφ' => hψKuniq φ' (fun w x' => by
      obtain ⟨x, rfl⟩ := (eG w).surjective x'
      rw [hF'mk, hφ' w x]))
    φ (fun v => (hφ v).1)⟩

end S_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime
end P2MW
export P2MW.S_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_isDiscreteValuationRing_of_liesOverPrime (solution)

-- Prove2me | solution 1 for PDivisibleGroup.exists_bialgHom_comp_transition_eq_nsmulBialgHom_and_injective_and_map_ker_counit_eq_torsionIdeal_and_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/89e0cd80-35ae-5e71-94d8-d12678ec08df

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Tower
import Theorems.Thm_PDivisibleGroup_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_bialgHom_comp_transition_eq_nsmulBialgHom_and_injective_and_map_ker_counit_eq_torsionIdeal_and_faithfullyFlat
p2m_attr_erase "instance" "PDivisibleGroup.Points.instAddCommGroup PDivisibleGroup.Points.instInhabited PDivisibleGroup.Point.instCommGroup PDivisibleGroup.pointsDirectedSystem PDivisibleGroup.Points.instDistribMulAction PDivisibleGroup.Point.instCommMonoid TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "PDivisibleGroup.Points.smul_pointsMkAdd PDivisibleGroup.pointsMkAdd_pointInclLE PDivisibleGroup.Point.toAlgHom_ofAlgHom PDivisibleGroup.pointsMkAdd_pointIncl PDivisibleGroup.pointsMk_pointInclLE PDivisibleGroup.pointIncl_apply PDivisibleGroup.pointInclLE_self PDivisibleGroup.toAlgHom_pointMap PDivisibleGroup.Point.toConv_ofConv PDivisibleGroup.Hopf.antipodeAlgHom_apply PDivisibleGroup.Hopf.convCompMonoidHom_apply PDivisibleGroup.pointsMap_pointsMkAdd PDivisibleGroup.Point.ofAlgHom_toAlgHom PDivisibleGroup.pointsMk_pointIncl PDivisibleGroup.Point.ofConv_toConv TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq HopfAlgebra.canAlgHom_tmul"
p2m_attr_erase "simp" "HopfAlgebra.canMap_tmul"

set_option autoImplicit false

open Coalgebra Bialgebra

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "Hopf.nsmulAlgHom Hopf.counit_nsmulAlgHom Hopf.augIdeal Hopf.torsionIdeal transitionAlgHom counit_transition nsmulAlgHom_transition transition_surjective transition level Hopf.map_comp_comulAlgHom_nsmulAlgHom Hopf.map_augIdeal_of_surjective exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk"
namespace PDivEpi
p2m_open "PDivisibleGroup"

universe u v w'

theorem faithfullyFlat_of_flat_of_linearMap_apply_eq_one
    {S : Type u} [CommRing S] {M : Type v} [AddCommGroup M] [Module S M] [Module.Flat S M]
    (r : M →ₗ[S] S) (x : M) (hx : r x = 1) : Module.FaithfullyFlat S M := by
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨inferInstance, fun I hI htop => hI ?_⟩
  rw [Ideal.eq_top_iff_one]
  have h1 : x ∈ I • (⊤ : Submodule S M) := by
    rw [htop]
    exact Submodule.mem_top
  have h2 : r x ∈ I • Submodule.map r ⊤ := by
    rw [← Submodule.map_smul'']
    exact Submodule.mem_map_of_mem h1
  rw [hx] at h2
  have h3 : I • Submodule.map r (⊤ : Submodule S M) ≤ I :=
    calc I • Submodule.map r (⊤ : Submodule S M) ≤ I • (⊤ : Submodule S S) :=
          Submodule.smul_mono le_rfl le_top
      _ = I := by rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact h3 h2

theorem faithfullyFlat_of_ringEquiv_subalgebra
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] {B : Type w'} [CommRing B] [Algebra R B]
    (C : Subalgebra R B) [Module.Flat C B] (r : B →ₗ[C] C) (hr : r 1 = 1)
    (f : S →+* B) (e : S ≃+* C) (hef : ∀ s, ((e s : C) : B) = f s) :
    letI := f.toAlgebra
    Module.FaithfullyFlat S B := by
  letI := f.toAlgebra
  letI : Algebra S C := e.toRingHom.toAlgebra
  haveI : IsScalarTower S C B := IsScalarTower.of_algebraMap_eq fun s => (hef s).symm
  haveI : Module.FaithfullyFlat C B := faithfullyFlat_of_flat_of_linearMap_apply_eq_one r 1 hr
  let eL : C ≃ₗ[S] S :=
    { toFun := e.symm
      invFun := e
      map_add' := fun x y => map_add e.symm x y
      map_smul' := fun s c => by
        change e.symm (s • c) = s • e.symm c
        rw [Algebra.smul_def, map_mul, smul_eq_mul]
        congr 1
        exact e.symm_apply_apply s
      left_inv := fun c => e.apply_symm_apply c
      right_inv := fun s => e.symm_apply_apply s }
  haveI : Module.FaithfullyFlat S C := Module.FaithfullyFlat.of_linearEquiv S S eL
  exact Module.FaithfullyFlat.trans S C B

end PDivisibleGroup.PDivEpi

open _root_.PDivisibleGroup _root_.P2MW.S_PDivisibleGroup_exists_bialgHom_comp_transition_eq_nsmulBialgHom_and_injective_and_map_ker_counit_eq_torsionIdeal_and_faithfullyFlat.PDivisibleGroup in
theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime] {h : ℕ} (G : PDivisibleGroup R p h) (w : ℕ) :
    ∃ m : G.level w →ₐc[R] G.level (w + 1),
      (m : G.level w →ₐ[R] G.level (w + 1)).comp (G.transitionAlgHom w) =
        PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (w + 1)) p ∧
      (G.transitionAlgHom w).comp (m : G.level w →ₐ[R] G.level (w + 1)) =
        PDivisibleGroup.Hopf.nsmulAlgHom R (G.level w) p ∧
      Function.Injective m ∧
      Ideal.map (m : G.level w →ₐ[R] G.level (w + 1)) (PDivisibleGroup.Hopf.augIdeal R (G.level w)) =
        PDivisibleGroup.Hopf.torsionIdeal R (G.level (w + 1)) p ∧

      (letI := (m : G.level w →ₐ[R] G.level (w + 1)).toRingHom.toAlgebra
       Module.FaithfullyFlat (G.level w) (G.level (w + 1))) := by
  obtain ⟨⟨e, he⟩, -, hproj, ⟨r, hr⟩, -⟩ :=
    PDivisibleGroup.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk G w

  have ht : Function.Surjective (G.transitionAlgHom w) := G.transition_surjective w
  let m₀ : G.level w →ₐ[R] G.level (w + 1) :=
    (Hopf.nsmulAlgHom R (G.level (w + 1)) p).range.val.comp (e : G.level w →ₐ[R] _)
  have hm₀t : m₀.comp (G.transitionAlgHom w) = Hopf.nsmulAlgHom R (G.level (w + 1)) p :=
    AlgHom.ext fun a => he a

  have hcounit : (counitAlgHom R (G.level (w + 1))).comp m₀ = counitAlgHom R (G.level w) := by
    refine (AlgHom.cancel_right ht).1 ?_
    rw [AlgHom.comp_assoc, hm₀t]
    refine AlgHom.ext fun a => ?_
    change counit (R := R) (Hopf.nsmulAlgHom R (G.level (w + 1)) p a) = counit (R := R) (G.transition w a)
    rw [Hopf.counit_nsmulAlgHom, G.counit_transition]

  have hcomul : (Algebra.TensorProduct.map m₀ m₀).comp (comulAlgHom R (G.level w)) =
      (comulAlgHom R (G.level (w + 1))).comp m₀ := by
    refine (AlgHom.cancel_right ht).1 ?_
    calc ((Algebra.TensorProduct.map m₀ m₀).comp (comulAlgHom R (G.level w))).comp (G.transitionAlgHom w)
        = (Algebra.TensorProduct.map m₀ m₀).comp
            ((Algebra.TensorProduct.map (G.transitionAlgHom w) (G.transitionAlgHom w)).comp
              (comulAlgHom R (G.level (w + 1)))) := by
          rw [AlgHom.comp_assoc]
          exact congrArg _ (BialgHom.map_comp_comulAlgHom (G.transition w)).symm
      _ = (Algebra.TensorProduct.map (Hopf.nsmulAlgHom R (G.level (w + 1)) p)
            (Hopf.nsmulAlgHom R (G.level (w + 1)) p)).comp (comulAlgHom R (G.level (w + 1))) := by
          rw [← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, hm₀t]
      _ = (comulAlgHom R (G.level (w + 1))).comp (Hopf.nsmulAlgHom R (G.level (w + 1)) p) :=
          Hopf.map_comp_comulAlgHom_nsmulAlgHom R (G.level (w + 1)) p
      _ = ((comulAlgHom R (G.level (w + 1))).comp m₀).comp (G.transitionAlgHom w) := by
          rw [AlgHom.comp_assoc, hm₀t]
  let mB : G.level w →ₐc[R] G.level (w + 1) := BialgHom.ofAlgHom m₀ hcounit hcomul
  have hcoe : (mB : G.level w →ₐ[R] G.level (w + 1)) = m₀ := AlgHom.ext fun _ => rfl

  have hii : (G.transitionAlgHom w).comp m₀ = Hopf.nsmulAlgHom R (G.level w) p := by
    refine (AlgHom.cancel_right ht).1 ?_
    rw [AlgHom.comp_assoc, hm₀t]
    refine AlgHom.ext fun a => ?_
    exact (G.nsmulAlgHom_transition w p a).symm

  have hinj : Function.Injective m₀ := fun x y hxy => e.injective (Subtype.val_injective hxy)

  have hiv : Ideal.map m₀ (Hopf.augIdeal R (G.level w)) = Hopf.torsionIdeal R (G.level (w + 1)) p := by
    rw [← Hopf.map_augIdeal_of_surjective (G.transition w) (G.transition_surjective w)]
    have h1 := Ideal.map_map (I := Hopf.augIdeal R (G.level (w + 1)))
      ((G.transitionAlgHom w : G.level (w + 1) →+* G.level w)) (m₀ : G.level w →+* G.level (w + 1))
    have h2 : (m₀ : G.level w →+* G.level (w + 1)).comp (G.transitionAlgHom w : G.level (w + 1) →+* G.level w) =
        (Hopf.nsmulAlgHom R (G.level (w + 1)) p : G.level (w + 1) →+* G.level (w + 1)) :=
      RingHom.ext fun a => he a
    rw [h2] at h1
    exact h1

  haveI : Module.Flat ↥(Hopf.nsmulAlgHom R (G.level (w + 1)) p).range (G.level (w + 1)) :=
    Module.Flat.of_projective
  have hr1 : r 1 = 1 := hr 1
  refine ⟨mB, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcoe]; exact hm₀t
  · rw [hcoe]; exact hii
  · exact fun x y hxy => hinj hxy
  · rw [hcoe]; exact hiv
  · exact PDivEpi.faithfullyFlat_of_ringEquiv_subalgebra (Hopf.nsmulAlgHom R (G.level (w + 1)) p).range r hr1
      ((mB : G.level w →ₐ[R] G.level (w + 1)).toRingHom) (e : G.level w ≃+* _) (fun _ => rfl)

end S_PDivisibleGroup_exists_bialgHom_comp_transition_eq_nsmulBialgHom_and_injective_and_map_ker_counit_eq_torsionIdeal_and_faithfullyFlat
end P2MW
export P2MW.S_PDivisibleGroup_exists_bialgHom_comp_transition_eq_nsmulBialgHom_and_injective_and_map_ker_counit_eq_torsionIdeal_and_faithfullyFlat (solution)

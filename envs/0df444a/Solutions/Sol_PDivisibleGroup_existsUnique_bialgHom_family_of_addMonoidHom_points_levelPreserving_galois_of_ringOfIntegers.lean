-- Prove2me | solution 1 for PDivisibleGroup.existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c5f4cacb-6e27-56f6-a7da-b3323af08152

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Theorems.Thm_PDivisibleGroup_exists_prod_bialgHom_bijective_points
import Theorems.Thm_PDivisibleGroup_exists_linearEquiv_tateModule_prod_of_bialgHom_comp_transition_of_bijective_points
import Theorems.Thm_PDivisibleGroup_exists_linearMap_tateModule_apply_eq_of_addMonoidHom_points
import Theorems.Thm_PDivisibleGroup_exists_hopf_quotient_system_points_iff_mem_of_forall_smul_mem_of_ringOfIntegers
import Theorems.Thm_PDivisibleGroup_exists_pDivisibleGroup_bialgHom_linearMap_tateModule_injective_range_eq_of_hopf_quotient_system_of_ringOfIntegers
import Theorems.Thm_PDivisibleGroup_forall_bijective_of_bijective_linearMap_tateModule_of_ringOfIntegers
import Theorems.Thm_PDivisibleGroup_eq_of_forall_toAlgHom_comp_eq_of_ringOfIntegers
import Theorems.Thm_PDivisibleGroup_nonempty_basis_tateModule_points
import Theorems.Thm_PDivisibleGroup_exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq
import Theorems.Thm_PDivisibleGroup_finite_point_and_natCard_point_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_ringOfIntegers
p2m_attr_erase "instance" "CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl PadicComplex.smulCommClass_gal_padic PadicComplex.smulCommClass_padic_gal PadicComplex.uniformContinuousConstSMul_gal PadicComplex.mulSemiringAction CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra PDivisibleGroup.CPoints.instDistribMulAction PrimaryTorsion.instSMul PrimaryTorsion.instModule"
p2m_attr_erase "simp" "HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul PDivisibleGroup.Tower.levelCast_rfl"
p2m_attr_erase "simp" "PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul PadicComplex.galAlgHom_apply PadicComplex.smul_algebraMap PadicComplex.norm_smul_eq PadicComplex.nnnorm_smul_eq PadicComplex.smul_coe PDivisibleGroup.CartierDuality.mk.injEq PDivisibleGroup.CartierDuality.toDualEquiv_apply PDivisibleGroup.CartierDuality.mk.sizeOf_spec CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply PDivisibleGroup.cotangentBaseChange_tmul PDivisibleGroup.baseChange_transition_tmul PDivisibleGroup.cotangentToBaseChange_toCotangent PDivisibleGroup.baseChange_level"
p2m_attr_erase "simp" "PDivisibleGroup.cotangentClass_algebraMap PDivisibleGroup.cotangentClass_one PDivisibleGroup.cpointsProj_cpointsMap PDivisibleGroup.pointsMap_reduceModPow_cpointsProj_succ PDivisibleGroup.cpointsProj_toCPoints PDivisibleGroup.mapModPow_mk PDivisibleGroup.reduceModPow_mk PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map"

set_option autoImplicit false

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

namespace Ws47
namespace T2asm
open PDivisibleGroup
theorem exists_rep {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h) {L : Type} [Field L] [Algebra R L]
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
end Ws47.T2asm

open Ws47.T2asm PDivisibleGroup in

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h h' : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (H : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h')
    (F : G.Points (PadicAlgCl p) →+ H.Points (PadicAlgCl p))

    (hFlev : ∀ (v : ℕ) (x : G.Point (PadicAlgCl p) v), ∃ y : H.Point (PadicAlgCl p) v,
      F (G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul x)) = H.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul y))

    (hFgal : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) (z : G.Points (PadicAlgCl p)), F (τ • z) = τ • F z) :
    ∃ φ : ∀ v : ℕ, H.level v →ₐc[PadicAlgCl.ringOfIntegers p K] G.level v,
      (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (H.transition v)) ∧
      (∀ (v : ℕ) (x : G.Point (PadicAlgCl p) v),
        F (G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul x)) =
          H.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : H.level v →ₐ[PadicAlgCl.ringOfIntegers p K] G.level v))))) ∧

      (∀ φ' : ∀ v : ℕ, H.level v →ₐc[PadicAlgCl.ringOfIntegers p K] G.level v,
        (∀ (v : ℕ) (x : G.Point (PadicAlgCl p) v),
          F (G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul x)) =
            H.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
              ((PDivisibleGroup.Point.toAlgHom x).comp (φ' v : H.level v →ₐ[PadicAlgCl.ringOfIntegers p K] G.level v))))) →
        φ' = φ) := by
  classical

  obtain ⟨P, iG, iH, hiG, hiH, hPpts⟩ := PDivisibleGroup.exists_prod_bialgHom_bijective_points G H
  obtain ⟨TP, hTP⟩ := PDivisibleGroup.exists_linearEquiv_tateModule_prod_of_bialgHom_comp_transition_of_bijective_points
    G H P iG iH hiG hiH hPpts (PadicAlgCl p)

  obtain ⟨TF, hTF⟩ := PDivisibleGroup.exists_linearMap_tateModule_apply_eq_of_addMonoidHom_points p G H F
  let D : TateModule p (P.Points (PadicAlgCl p)) →ₗ[ℤ_[p]] TateModule p (H.Points (PadicAlgCl p)) :=
    (LinearMap.snd ℤ_[p] _ _ ∘ₗ TP.toLinearMap) - TF ∘ₗ (LinearMap.fst ℤ_[p] _ _ ∘ₗ TP.toLinearMap)
  let M : Submodule ℤ_[p] (TateModule p (P.Points (PadicAlgCl p))) := LinearMap.ker D
  have hMmem : ∀ z, z ∈ M ↔ (TP z).2 = TF (TP z).1 := fun z => by
    show D z = 0 ↔ _
    simp only [D, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.snd_apply, LinearMap.fst_apply,
      LinearEquiv.coe_toLinearMap, sub_eq_zero]
  have hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) (z : TateModule p (P.Points (PadicAlgCl p))),
      z ∈ M → P.tateModuleRep (PadicAlgCl p) τ z ∈ M := by
    intro τ z hz
    have E : ∀ y : TateModule p (P.Points (PadicAlgCl p)),
        (TP (P.tateModuleRep (PadicAlgCl p) τ y)).1 = G.tateModuleRep (PadicAlgCl p) τ (TP y).1 ∧
        (TP (P.tateModuleRep (PadicAlgCl p) τ y)).2 = H.tateModuleRep (PadicAlgCl p) τ (TP y).2 := by
      intro y
      constructor
      all_goals
        apply Subtype.ext
        funext n
        obtain ⟨g, hg⟩ := exists_rep P y n
        have h1 : P.pointsMkAdd (PadicAlgCl p) n (Additive.ofMul (P.pointMap (τ : PadicAlgCl p →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) n g))
            = ((P.tateModuleRep (PadicAlgCl p) τ y : TateModule p (P.Points (PadicAlgCl p))) : ℕ → P.Points (PadicAlgCl p)) n := by
          rw [tateModuleRep_apply, ← hg, Points.smul_pointsMkAdd]
      · rw [(hTP _ n n _ h1).1, tateModuleRep_apply, (hTP y n n g hg).1, Points.smul_pointsMkAdd]
        congr 2
      · rw [(hTP _ n n _ h1).2, tateModuleRep_apply, (hTP y n n g hg).2, Points.smul_pointsMkAdd]
        congr 2
    have ETF : ∀ X : TateModule p (G.Points (PadicAlgCl p)),
        TF (G.tateModuleRep (PadicAlgCl p) τ X) = H.tateModuleRep (PadicAlgCl p) τ (TF X) := by
      intro X
      apply Subtype.ext
      funext n
      rw [hTF, tateModuleRep_apply, tateModuleRep_apply, hTF, hFgal]
    rw [hMmem] at hz ⊢
    rw [(E z).1, (E z).2, hz, ETF]
  have hMsat : ∀ (r : ℤ_[p]) (z : TateModule p (P.Points (PadicAlgCl p))), r ≠ 0 → r • z ∈ M → z ∈ M := by
    intro r z hr hz
    obtain ⟨bH⟩ := PDivisibleGroup.nonempty_basis_tateModule_points H (PadicAlgCl p)
    rw [hMmem] at hz ⊢
    rw [map_smul, Prod.smul_snd, Prod.smul_fst, map_smul, ← sub_eq_zero, ← smul_sub] at hz
    rw [← sub_eq_zero]
    set w := (TP z).2 - TF (TP z).1 with hw
    refine bH.ext_elem fun i => ?_
    have hi := congrArg (fun y => bH.repr y i) hz
    simp only [map_smul, map_zero, Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul,
      mul_eq_zero] at hi
    rcases hi with hi | hi
    · exact absurd hi hr
    · simpa using hi

  obtain ⟨B, _i1, _i2, _i3, _i4, _i5, π, t, hπ, ht, hπt, hpts⟩ :=
    PDivisibleGroup.exists_hopf_quotient_system_points_iff_mem_of_forall_smul_mem_of_ringOfIntegers p K P M hMstab hMsat
  obtain ⟨h'', Γ, φP, TφP, hφP, hTφP, hTφPσ, hTφPinj, hTφPrange⟩ :=
    PDivisibleGroup.exists_pDivisibleGroup_bialgHom_linearMap_tateModule_injective_range_eq_of_hopf_quotient_system_of_ringOfIntegers
      p K P M hMstab hMsat B π t hπ ht hπt hpts

  let u : ∀ v : ℕ, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] Γ.level v := fun v => (φP v).comp (iG v)
  have hu : ∀ v : ℕ, (u v).comp (G.transition v) = (Γ.transition v).comp (u (v + 1)) := by
    intro v
    show ((φP v).comp (iG v)).comp (G.transition v) = (Γ.transition v).comp ((φP (v + 1)).comp (iG (v + 1)))
    rw [BialgHom.comp_assoc, hiG, ← BialgHom.comp_assoc, hφP, BialgHom.comp_assoc]
  let Tu : TateModule p (Γ.Points (PadicAlgCl p)) →ₗ[ℤ_[p]] TateModule p (G.Points (PadicAlgCl p)) :=
    (LinearMap.fst ℤ_[p] _ _ ∘ₗ TP.toLinearMap) ∘ₗ TφP
  have hTu : ∀ (x : TateModule p (Γ.Points (PadicAlgCl p))) (n w : ℕ) (g : Γ.Point (PadicAlgCl p) w),
      Γ.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) = (x : ℕ → Γ.Points (PadicAlgCl p)) n →
      ((Tu x : TateModule p (G.Points (PadicAlgCl p))) : ℕ → G.Points (PadicAlgCl p)) n =
        G.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom g).comp (u w : G.level w →ₐ[PadicAlgCl.ringOfIntegers p K] Γ.level w)))) := by
    intro x n w g hg
    have h1 := hTφP x n w g hg
    have h2 := (hTP (TφP x) n w _ h1.symm).1
    exact h2
  have hbij : Function.Bijective Tu := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have hm : TφP x ∈ M := by rw [← hTφPrange]; exact LinearMap.mem_range_self _ _
      rw [hMmem] at hm
      have h1 : (TP (TφP x)).1 = 0 := hx
      rw [h1, map_zero] at hm
      have h2 : TP (TφP x) = 0 := Prod.ext h1 hm
      rw [← map_zero TP] at h2
      exact hTφPinj (by rw [TP.injective h2, map_zero])
    · intro y
      have hz : TP.symm (y, TF y) ∈ M := by rw [hMmem]; simp
      rw [← hTφPrange] at hz
      obtain ⟨x, hx⟩ := hz
      refine ⟨x, ?_⟩
      show (TP (TφP x)).1 = y
      rw [hx]
      simp

  have hh : h'' = h := by
    obtain ⟨bΓ⟩ := PDivisibleGroup.nonempty_basis_tateModule_points Γ (PadicAlgCl p)
    obtain ⟨bG⟩ := PDivisibleGroup.nonempty_basis_tateModule_points G (PadicAlgCl p)
    have e := (LinearEquiv.ofBijective Tu hbij).finrank_eq
    rw [Module.finrank_eq_card_basis bΓ, Module.finrank_eq_card_basis bG, Fintype.card_fin, Fintype.card_fin] at e
    exact e
  subst hh
  have hiso : ∀ v : ℕ, Function.Bijective (u v) :=
    PDivisibleGroup.forall_bijective_of_bijective_linearMap_tateModule_of_ringOfIntegers p K G Γ u hu Tu hTu hbij

  let e : ∀ v : ℕ, G.level v ≃ₐc[PadicAlgCl.ringOfIntegers p K] Γ.level v := fun v => BialgEquiv.ofBijective (u v) (hiso v)
  let φ : ∀ v : ℕ, H.level v →ₐc[PadicAlgCl.ringOfIntegers p K] G.level v := fun v =>
    ((e v).symm : Γ.level v →ₐc[PadicAlgCl.ringOfIntegers p K] G.level v).comp ((φP v).comp (iH v))
  have hUe : ∀ (v : ℕ) (y : Γ.level v), u v ((e v).symm y) = y := fun v y => (e v).apply_symm_apply y
  have hφu : ∀ (v : ℕ) (d : H.level v), u v (φ v d) = φP v (iH v d) := fun v d => hUe v _

  have hind : ∀ (v : ℕ) (x : G.Point (PadicAlgCl p) v), F (G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul x)) =
      H.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (Point.ofAlgHom ((Point.toAlgHom x).comp (φ v : H.level v →ₐ[PadicAlgCl.ringOfIntegers p K] G.level v)))) := by
    intro v x
    have hcardG := fun w => PDivisibleGroup.finite_point_and_natCard_point_eq_pow p G (PadicAlgCl p) w
    obtain ⟨X, hX⟩ := (PDivisibleGroup.exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq
      p G (PadicAlgCl p) hcardG).1 v x
    have hz : TP.symm (X, TF X) ∈ M := by rw [hMmem]; simp
    rw [← hTφPrange] at hz
    obtain ⟨ξ, hξ⟩ := hz
    obtain ⟨γ, hγ⟩ := exists_rep Γ ξ v
    have ha := hTφP ξ v v γ hγ
    have hb := hTP (TφP ξ) v v _ ha.symm
    rw [hξ, LinearEquiv.apply_symm_apply] at hb
    obtain ⟨hb1, hb2⟩ := hb
    change ((TF X : TateModule p (H.Points (PadicAlgCl p))) : ℕ → H.Points (PadicAlgCl p)) v = _ at hb2
    rw [hTF, hX] at hb2
    rw [hb2]
    change ((X : TateModule p (G.Points (PadicAlgCl p))) : ℕ → G.Points (PadicAlgCl p)) v = _ at hb1
    have hx' : Point.toAlgHom x = ((Point.toAlgHom γ).comp (φP v : P.level v →ₐ[PadicAlgCl.ringOfIntegers p K] Γ.level v)).comp (iG v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] P.level v) := by
      have := (G.pointsMkAdd_eq_pointsMkAdd_iff (L := PadicAlgCl p) _ _).1 (hX.symm.trans hb1).symm
      rw [← this]
      rfl
    congr 2
    apply congrArg Point.ofAlgHom
    refine AlgHom.ext fun d => ?_
    rw [hx']
    show Point.toAlgHom γ (φP v (iH v d)) = Point.toAlgHom γ (φP v (iG v (φ v d)))
    congr 1
    exact (hφu v d).symm
  refine ⟨φ, ?_, hind, ?_⟩
  ·
    intro v
    apply BialgHom.coe_algHom_injective
    refine AlgHom.ext fun d => ?_
    apply (hiso v).1
    show u v (G.transition v (φ (v + 1) d)) = u v (φ v (H.transition v d))
    have e1 := DFunLike.congr_fun (hu v) (φ (v + 1) d)
    have e2 := DFunLike.congr_fun (hiH v) d
    have e3 := DFunLike.congr_fun (hφP v) (iH (v + 1) d)
    simp only [BialgHom.coe_comp, Function.comp_apply] at e1 e2 e3
    rw [e1, hφu, hφu, e2, e3]
  ·
    intro φ' hφ'
    refine (PDivisibleGroup.eq_of_forall_toAlgHom_comp_eq_of_ringOfIntegers p K G H φ φ' fun v x => ?_).symm
    have h1 := (hind v x).symm.trans (hφ' v x)
    have h2 := (H.pointsMkAdd_eq_pointsMkAdd_iff (L := PadicAlgCl p) _ _).1 h1
    exact congrArg Point.toAlgHom h2

end S_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_existsUnique_bialgHom_family_of_addMonoidHom_points_levelPreserving_galois_of_ringOfIntegers (solution)

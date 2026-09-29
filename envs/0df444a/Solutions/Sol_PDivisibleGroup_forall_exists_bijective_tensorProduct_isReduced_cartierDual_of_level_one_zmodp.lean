-- Prove2me | solution 1 for PDivisibleGroup.forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_level_one_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8a76a85f-911e-5810-9845-2ba944ec1420

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_PDivisibleGroup_exists_tower_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp
import Theorems.Thm_HopfAlgebra_isReduced_cartierDual_of_bijective_tensorProduct_isReduced_cartierDual_of_bijective_tensorProduct_comul_zmodp
import Theorems.Thm_PDivisibleGroup_Tower_forall_isReduced_cartierDual_of_isReduced_cartierDual_one_zmodp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_level_one_zmodp
p2m_attr_erase "instance" "HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra Deformation.TruncWitt.instSubsingleton Deformation.DieudonneModule.instInhabited Deformation.wittHomShiftLE_directedSystem Deformation.DieudonneModule.instAddCommGroup PDivisibleGroup.Points.instAddCommGroup PDivisibleGroup.Points.instInhabited PDivisibleGroup.Point.instCommGroup PDivisibleGroup.pointsDirectedSystem PDivisibleGroup.Points.instDistribMulAction PDivisibleGroup.Point.instCommMonoid TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec Deformation.wittHomDieudonneDatum_F_apply Deformation.TruncWitt.shift_truncate Deformation.coe_wittHomShift Deformation.coe_wittHomFrobenius Deformation.wittHomDieudonneDatum_V_apply Deformation.TruncWitt.coeff_map Deformation.coe_wittHomVerschiebung Deformation.coe_wittHomRestrict Deformation.coe_wittHomMap Deformation.TruncWitt.map_truncate Deformation.TruncWitt.coeff_frobeniusFun"
p2m_attr_erase "simp" "Deformation.TruncWitt.verschiebung_truncate Deformation.TruncWitt.map_id Deformation.TruncWitt.shiftLE_refl Deformation.DieudonneModule.dieudonneDatum_F_apply Deformation.coe_wittHomShiftLE Deformation.DieudonneModule.frobenius_of Deformation.DieudonneModule.lift_of Deformation.TruncWitt.verschiebungIter_apply Deformation.DieudonneModule.map_of Deformation.DieudonneModule.dieudonneDatum_V_apply Deformation.DieudonneModule.of_shift Deformation.TruncWitt.shiftLE_truncate Deformation.DieudonneModule.verschiebung_of Deformation.DieudonneModule.of_shiftLE Deformation.wittHomShiftLE_refl PDivisibleGroup.Points.smul_pointsMkAdd PDivisibleGroup.pointsMkAdd_pointInclLE PDivisibleGroup.Point.toAlgHom_ofAlgHom PDivisibleGroup.pointsMkAdd_pointIncl PDivisibleGroup.pointsMk_pointInclLE PDivisibleGroup.pointIncl_apply PDivisibleGroup.pointInclLE_self PDivisibleGroup.toAlgHom_pointMap PDivisibleGroup.Point.toConv_ofConv PDivisibleGroup.Hopf.antipodeAlgHom_apply PDivisibleGroup.Hopf.convCompMonoidHom_apply PDivisibleGroup.pointsMap_pointsMkAdd PDivisibleGroup.Point.ofAlgHom_toAlgHom PDivisibleGroup.pointsMk_pointIncl PDivisibleGroup.Point.ofConv_toConv TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply"
p2m_attr_erase "simp" "GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe v

theorem solution
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * h))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
    (hord₁ : ∃ (M : Type v) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
        (_ : Module.Free (ZMod p) M) (E : Type v) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
        (Θ : G 1 →ₐc[ZMod p] M ⊗[ZMod p] E),
        Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M)) :
    ∀ v : ℕ, ∃ (M : Type v) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
        (_ : Module.Free (ZMod p) M) (E : Type v) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
        (Θ : G v →ₐc[ZMod p] M ⊗[ZMod p] E),
        Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M) := by
  classical

  obtain ⟨hc, he, Gc, _, _, _, _, Ge, _, _, _, _, sc, se, qc, πe, σ, Θ, hsum, hloc, hred, hunr, hsc, hrankc, hkerc,
    hse, hranke, hkere, hqc, hπe, hkerπe, hσ, hkerqc, hΘbij, hΘ, hqcs, hπes, hsσ, hΘs⟩ :=
    PDivisibleGroup.exists_tower_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp p h G s hs hrankG hkerG

  have h₁ : IsReduced (CartierDual (ZMod p) (Gc 1)) :=
    HopfAlgebra.isReduced_cartierDual_of_bijective_tensorProduct_isReduced_cartierDual_of_bijective_tensorProduct_comul_zmodp
      p (qc 1) (πe 1) (σ 1) (Θ 1) (hqc 1) (hπe 1) (hkerπe 1) (hσ 1) (hunr 1) (hkerqc 1) (hΘ 1) (hloc 1) hord₁

  have hall := PDivisibleGroup.Tower.forall_isReduced_cartierDual_of_isReduced_cartierDual_one_zmodp p hc Gc sc hsc
    hrankc hkerc h₁
  intro v
  exact ⟨Gc v, inferInstance, inferInstance, inferInstance, inferInstance, Ge v, inferInstance, inferInstance, Θ v,
    hΘbij v, hred v, hall v⟩

end S_PDivisibleGroup_forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_level_one_zmodp
end P2MW
export P2MW.S_PDivisibleGroup_forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_level_one_zmodp (solution)

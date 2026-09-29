-- Prove2me | solution 1 for PDivisibleGroup.forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_comp_eq_idempotent_of_reduction_pow_eq_frobenius_conv_verschiebung
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8f86913a-08b0-5bf6-9f0f-c8b61003a8b7

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_comp_eq_id_comp_eq_of_comp_eq_self_of_isLocalRing
import Theorems.Thm_PDivisibleGroup_Tower_surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp
import Theorems.Thm_HopfAlgebra_exists_cartierDualMap_id_eq_frobenius_conv_verschiebung_of_comp_eq_idempotent_of_cartierDualMap_pow_eq
import Theorems.Thm_HopfAlgebra_exists_split_idempotent_bijective_tensorProduct_isReduced_cartierDual_of_cartierDualMap_eq_frobenius_conv_verschiebung
import Theorems.Thm_PDivisibleGroup_forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_level_one_zmodp
import Theorems.Thm_PDivisibleGroup_surjective_and_finrank_and_ker_tensorProduct_map_transition
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_comp_eq_idempotent_of_reduction_pow_eq_frobenius_conv_verschiebung
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient Deformation.TruncWitt.instSubsingleton Deformation.DieudonneModule.instInhabited Deformation.wittHomShiftLE_directedSystem Deformation.DieudonneModule.instAddCommGroup PDivisibleGroup.Points.instAddCommGroup PDivisibleGroup.Points.instInhabited PDivisibleGroup.Point.instCommGroup PDivisibleGroup.pointsDirectedSystem PDivisibleGroup.Points.instDistribMulAction PDivisibleGroup.Point.instCommMonoid TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec Deformation.wittHomDieudonneDatum_F_apply Deformation.TruncWitt.shift_truncate Deformation.coe_wittHomShift Deformation.coe_wittHomFrobenius Deformation.wittHomDieudonneDatum_V_apply Deformation.TruncWitt.coeff_map Deformation.coe_wittHomVerschiebung Deformation.coe_wittHomRestrict Deformation.coe_wittHomMap Deformation.TruncWitt.map_truncate Deformation.TruncWitt.coeff_frobeniusFun Deformation.TruncWitt.verschiebung_truncate Deformation.TruncWitt.map_id"
p2m_attr_erase "simp" "Deformation.TruncWitt.shiftLE_refl Deformation.DieudonneModule.dieudonneDatum_F_apply Deformation.coe_wittHomShiftLE Deformation.DieudonneModule.frobenius_of Deformation.DieudonneModule.lift_of Deformation.TruncWitt.verschiebungIter_apply Deformation.DieudonneModule.map_of Deformation.DieudonneModule.dieudonneDatum_V_apply Deformation.DieudonneModule.of_shift Deformation.TruncWitt.shiftLE_truncate Deformation.DieudonneModule.verschiebung_of Deformation.DieudonneModule.of_shiftLE Deformation.wittHomShiftLE_refl PDivisibleGroup.Points.smul_pointsMkAdd PDivisibleGroup.pointsMkAdd_pointInclLE PDivisibleGroup.Point.toAlgHom_ofAlgHom PDivisibleGroup.pointsMkAdd_pointIncl PDivisibleGroup.pointsMk_pointInclLE PDivisibleGroup.pointIncl_apply PDivisibleGroup.pointInclLE_self PDivisibleGroup.toAlgHom_pointMap PDivisibleGroup.Point.toConv_ofConv PDivisibleGroup.Hopf.antipodeAlgHom_apply PDivisibleGroup.Hopf.convCompMonoidHom_apply PDivisibleGroup.pointsMap_pointsMkAdd PDivisibleGroup.Point.ofAlgHom_toAlgHom PDivisibleGroup.pointsMk_pointIncl PDivisibleGroup.Point.ofConv_toConv TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg"
p2m_attr_erase "simp" "WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

namespace OrdSp

theorem bc_comp {O : Type} [CommRing O] (k : Type) [CommRing k] [Algebra O k]
    {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [HopfAlgebra O A] [HopfAlgebra O B] [HopfAlgebra O C]
    (f : B →ₐc[O] C) (g : A →ₐc[O] B) :
    (Bialgebra.TensorProduct.map (BialgHom.id k k) f).comp (Bialgebra.TensorProduct.map (BialgHom.id k k) g) =
      Bialgebra.TensorProduct.map (BialgHom.id k k) (f.comp g) := by
  apply BialgHom.coe_algHom_injective
  show (Bialgebra.TensorProduct.map (BialgHom.id k k) f : k ⊗[O] B →ₐ[k] k ⊗[O] C).comp
      (Bialgebra.TensorProduct.map (BialgHom.id k k) g : k ⊗[O] A →ₐ[k] k ⊗[O] B) = _
  rw [Bialgebra.TensorProduct.map_toAlgHom, Bialgebra.TensorProduct.map_toAlgHom, Bialgebra.TensorProduct.map_toAlgHom,
    ← Algebra.TensorProduct.map_comp]
  rfl

theorem bc_id {O : Type} [CommRing O] (k : Type) [CommRing k] [Algebra O k]
    {A : Type} [CommRing A] [HopfAlgebra O A] :
    Bialgebra.TensorProduct.map (BialgHom.id k k) (BialgHom.id O A) = BialgHom.id k (k ⊗[O] A) := by
  apply BialgHom.coe_algHom_injective
  rw [Bialgebra.TensorProduct.map_toAlgHom]
  apply AlgHom.ext; intro z
  induction z with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, hx, hy]; rfl

end OrdSp

open OrdSp in
theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (ZMod p)]
    {h : ℕ} (H : PDivisibleGroup O p h)

    (u ε w : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (hu : ∀ v : ℕ, (H.transition v).comp (u (v + 1)) = (u v).comp (H.transition v))
    (hεε : ∀ v : ℕ, (ε v).comp (ε v) = ε v)
    (hεtr : ∀ v : ℕ, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))
    (hεu : ∀ v : ℕ, (ε v).comp (u v) = (u v).comp (ε v))
    (hwtr : ∀ v : ℕ, (H.transition v).comp (w (v + 1)) = (w v).comp (H.transition v))
    (hεw : ∀ v : ℕ, (ε v).comp (w v) = w v) (hwε : ∀ v : ℕ, (w v).comp (ε v) = w v)
    (hwuε : ∀ v : ℕ, (w v).comp ((u v).comp (ε v)) = ε v)
    (huεw : ∀ v : ℕ, ((u v).comp (ε v)).comp (w v) = ε v)

    (hFV : ∀ Fk : ZMod p ⊗[O] H.level 1 →ₐc[ZMod p] ZMod p ⊗[O] H.level 1, (∀ x, Fk x = x ^ p) →
      ∀ FD : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₐ[ZMod p]
          CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1), (∀ ψ, FD ψ = ψ ^ p) →
      ∃ (n : ℕ) (a b : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₐc[ZMod p]
          CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)),
        (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u 1)) :
            CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
              CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)) ^ n =
          (WithConv.toConv ((FD : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)) ∘ₗ
              (a : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1))) *
            WithConv.toConv ((b : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)) ∘ₗ
              (CartierDual.map Fk : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)))).ofConv)
    :
    ∀ (v : ℕ) (Cv : Type) [CommRing Cv] [HopfAlgebra (ZMod p) Cv] [Coalgebra.IsCocomm (ZMod p) Cv]
      [Module.Finite (ZMod p) Cv] [Module.Free (ZMod p) Cv]
      (q : ZMod p ⊗[O] H.level v →ₐc[ZMod p] Cv) (i : Cv →ₐc[ZMod p] ZMod p ⊗[O] H.level v),
      Function.Surjective q → q.comp i = BialgHom.id (ZMod p) Cv →
      i.comp q = Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v) →
      ∃ (M : Type) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
        (_ : Module.Free (ZMod p) M) (E : Type) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
        (Θ : Cv →ₐc[ZMod p] M ⊗[ZMod p] E),
        Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M) := by
  intro v Cv _ _ _ _ _ q i hq hqi hiq
  classical

  obtain ⟨hs, hrank, hker⟩ := PDivisibleGroup.surjective_and_finrank_and_ker_tensorProduct_map_transition p H (ZMod p)

  have heb : ∀ n : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε n)).comp
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε n)) =
      Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε n) := fun n => by rw [bc_comp, hεε]
  have het : ∀ n : ℕ, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (H.transition n)).comp
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε (n + 1))) =
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε n)).comp
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (H.transition n)) := fun n => by
    rw [bc_comp, bc_comp, hεtr]

  have hOF1 := fun n : ℕ => HopfAlgebra.exists_bialgHom_surjective_comp_eq_id_comp_eq_of_comp_eq_self_of_isLocalRing (ZMod p) (ZMod p ⊗[O] H.level n)
    (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε n)) (heb n)
  choose C iC iH iCo iFin iFree qn inn hqn hqin hinq using hOF1
  letI : ∀ n, CommRing (C n) := iC
  letI : ∀ n, HopfAlgebra (ZMod p) (C n) := iH
  haveI : ∀ n, Coalgebra.IsCocomm (ZMod p) (C n) := iCo
  haveI : ∀ n, Module.Finite (ZMod p) (C n) := iFin
  haveI : ∀ n, Module.Free (ZMod p) (C n) := iFree

  obtain ⟨hT1, ⟨h₁, hh₁, hrankC⟩, hT3⟩ := PDivisibleGroup.Tower.surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp
    p h (fun n => ZMod p ⊗[O] H.level n) (fun n => Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (H.transition n))
    hs hrank hker (fun n => Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε n)) heb het C qn inn hqn hqin hinq

  have hrel := fun (a b : H.level 1 →ₐc[O] H.level 1) => bc_comp (ZMod p) a b
  have hidFV := HopfAlgebra.exists_cartierDualMap_id_eq_frobenius_conv_verschiebung_of_comp_eq_idempotent_of_cartierDualMap_pow_eq
    p (ZMod p ⊗[O] H.level 1)
    (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u 1))
    (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε 1))
    (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (w 1))
    (heb 1) (by rw [hrel, hrel, hεu]) (by rw [hrel, hεw]) (by rw [hrel, hwε]) (by rw [hrel, hrel, hwuε])
    (by rw [hrel, hrel, huεw]) hFV (C 1) (qn 1) (inn 1) (hqn 1) (hqin 1) (hinq 1)
  obtain ⟨C', _, _, _, _, _, q', i', hq', hq'i', hi'q', M₁, _, _, _, _, E₁, _, _, Θ₁, hΘ₁, hE₁, hM₁⟩ :=
    HopfAlgebra.exists_split_idempotent_bijective_tensorProduct_isReduced_cartierDual_of_cartierDualMap_eq_frobenius_conv_verschiebung p (C 1) (BialgHom.id (ZMod p) (C 1)) (by rfl) hidFV
  have hq'bij : Function.Bijective q' := by
    refine Function.bijective_iff_has_inverse.mpr ⟨i', fun x => ?_, fun y => ?_⟩
    · exact DFunLike.congr_fun hi'q' x
    · exact DFunLike.congr_fun hq'i' y
  have hord₁ : ∃ (M : Type) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
      (_ : Module.Free (ZMod p) M) (E : Type) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
      (Θ : C 1 →ₐc[ZMod p] M ⊗[ZMod p] E),
      Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M) :=
    ⟨M₁, inferInstance, inferInstance, inferInstance, inferInstance, E₁, inferInstance, inferInstance, Θ₁.comp q',
      hΘ₁.comp hq'bij, hE₁, hM₁⟩

  obtain ⟨M, _, _, _, _, E, _, _, Θv, hΘv, hE, hM⟩ := PDivisibleGroup.forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_level_one_zmodp
    p h₁ C (fun n => (qn n).comp ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (H.transition n)).comp (inn (n + 1))))
    hT1 hrankC hT3 hord₁ v

  have hbij : Function.Bijective ((qn v).comp i) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨q.comp (inn v), fun x => ?_, fun y => ?_⟩
    · show q (inn v (qn v (i x))) = x
      have h1 : inn v (qn v (i x)) = (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) (i x) :=
        DFunLike.congr_fun (hinq v) (i x)
      rw [h1, ← hiq]
      show q (i (q (i x))) = x
      have h2 := DFunLike.congr_fun hqi
      simp only [BialgHom.comp_apply, BialgHom.id_apply] at h2
      rw [h2, h2]
    · show qn v (i (q (inn v y))) = y
      have h1 : i (q (inn v y)) = (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) (inn v y) := by
        rw [← hiq]; rfl
      rw [h1, ← hinq v]
      show qn v (inn v (qn v (inn v y))) = y
      have h2 := DFunLike.congr_fun (hqin v)
      simp only [BialgHom.comp_apply, BialgHom.id_apply] at h2
      rw [h2, h2]
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, E, inferInstance, inferInstance, Θv.comp ((qn v).comp i),
    hΘv.comp hbij, hE, hM⟩

end S_PDivisibleGroup_forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_comp_eq_idempotent_of_reduction_pow_eq_frobenius_conv_verschiebung
end P2MW
export P2MW.S_PDivisibleGroup_forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_comp_eq_idempotent_of_reduction_pow_eq_frobenius_conv_verschiebung (solution)

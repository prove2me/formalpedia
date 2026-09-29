-- Prove2me | solution 1 for PDivisibleGroup.exists_rep_pow_sub_smul_eq_cyclotomicCharacter_smul_of_reduction_pow_eq_frobenius_conv_verschiebung
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/05b871de-0062-5071-bdd6-0f1132b8abc7

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_PDivisibleGroup_CartierDuality
import Theorems.Thm_PDivisibleGroup_surjective_and_finrank_and_ker_tensorProduct_map_transition
import Theorems.Thm_PDivisibleGroup_exists_linearMap_tateModule_injective_of_surjective_comp_transition
import Theorems.Thm_PDivisibleGroup_finite_point_and_natCard_point_eq_pow
import Theorems.Thm_PDivisibleGroup_exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq
import Theorems.Thm_PDivisibleGroup_tateModule_induced_mem_and_comm_and_add_and_comp
import Theorems.Thm_PDivisibleGroup_eq_of_forall_point_toAlgHom_apply_eq
import Theorems.Thm_exists_idempotent_mul_eq_and_pow_mul_sub_mem_of_moduleFinite_padicInt
import Theorems.Thm_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self
import Theorems.Thm_HopfAlgebra_exists_split_idempotent_bijective_tensorProduct_isReduced_cartierDual_of_cartierDualMap_eq_frobenius_conv_verschiebung
import Theorems.Thm_PDivisibleGroup_forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_level_one_zmodp
import Theorems.Thm_PDivisibleGroup_CartierDuality_pair_eq_one_of_forall_valuation_sub_counit_lt_one_of_bijective_tensorProduct_isReduced
import Theorems.Thm_PDivisibleGroup_CartierDuality_tateModuleRep_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_of_forall_pair_eq_one
import Theorems.Thm_PDivisibleGroup_forall_mem_adjoin_tateModule_apply_mem_and_comp_tateModuleRep_eq
import Theorems.Thm_PDivisibleGroup_exists_submodule_tateModule_reduction_and_rep_sub_mem_of_mem_inertiaSubgroupIn
import Theorems.Thm_PDivisibleGroup_exists_isCartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_rep_pow_sub_smul_eq_cyclotomicCharacter_smul_of_reduction_pow_eq_frobenius_conv_verschiebung
p2m_attr_erase "instance" "HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra Deformation.TruncWitt.instSubsingleton Deformation.DieudonneModule.instInhabited Deformation.wittHomShiftLE_directedSystem Deformation.DieudonneModule.instAddCommGroup HopfAlgebra.IsHopfTower.refl CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec Deformation.wittHomDieudonneDatum_F_apply Deformation.TruncWitt.shift_truncate Deformation.coe_wittHomShift Deformation.coe_wittHomFrobenius Deformation.wittHomDieudonneDatum_V_apply Deformation.TruncWitt.coeff_map Deformation.coe_wittHomVerschiebung Deformation.coe_wittHomRestrict Deformation.coe_wittHomMap Deformation.TruncWitt.map_truncate Deformation.TruncWitt.coeff_frobeniusFun Deformation.TruncWitt.verschiebung_truncate Deformation.TruncWitt.map_id Deformation.TruncWitt.shiftLE_refl Deformation.DieudonneModule.dieudonneDatum_F_apply Deformation.coe_wittHomShiftLE Deformation.DieudonneModule.frobenius_of"
p2m_attr_erase "simp" "Deformation.DieudonneModule.lift_of Deformation.TruncWitt.verschiebungIter_apply Deformation.DieudonneModule.map_of Deformation.DieudonneModule.dieudonneDatum_V_apply Deformation.DieudonneModule.of_shift Deformation.TruncWitt.shiftLE_truncate Deformation.DieudonneModule.verschiebung_of Deformation.DieudonneModule.of_shiftLE Deformation.wittHomShiftLE_refl HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u v w

theorem S42SLP.level_eq_of_induced_eq
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)]
    (hinj : Function.Injective (algebraMap O (AlgebraicClosure ℚ)))
    {h : ℕ} (H : PDivisibleGroup O p h)

    (hlift : ∀ (v : ℕ) (x : H.Point (AlgebraicClosure ℚ) v), ∃ y : TateModule p (H.Points (AlgebraicClosure ℚ)),
      (y : ℕ → H.Points (AlgebraicClosure ℚ)) v = H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))
    (V : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))
    (ε ε' : ∀ w : ℕ, H.level w →ₐ[O] H.level w)
    (hε : (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((V x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (ε w))))))
    (hε' : (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((V x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (ε' w)))))) :
    ∀ w, ε w = ε' w := by
  intro w
  refine AlgHom.ext fun c => ?_
  refine PDivisibleGroup.eq_of_forall_point_toAlgHom_apply_eq p hinj H w _ _ fun x => ?_
  obtain ⟨y, hy⟩ := hlift w x
  have h1 := hε y w w x hy.symm
  have h2 := hε' y w w x hy.symm
  have h3 := H.pointsMkAdd_injective (L := AlgebraicClosure ℚ) w (h1.symm.trans h2)
  have h4 : PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ε w)) =
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ε' w)) := Additive.ofMul.injective h3
  have h5 := congrArg PDivisibleGroup.Point.toAlgHom h4
  rw [PDivisibleGroup.Point.toAlgHom_ofAlgHom, PDivisibleGroup.Point.toAlgHom_ofAlgHom] at h5
  exact AlgHom.congr_fun h5 c

theorem S42SLP.exists_bialgHom_family_of_mem_adjoin
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    {h : ℕ} (H : PDivisibleGroup O p h)
    (S : Submodule ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))
    (hS : ∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), y ∈ S ↔
        ∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (y : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1)
    (u : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (hu : ∀ v : ℕ, (H.transition v).comp (u (v + 1)) = (u v).comp (H.transition v))
    (U : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))
    (hU : (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u w : H.level w →ₐ[O] H.level w))))))
    (V : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))
    (hV : V ∈ Algebra.adjoin ℤ_[p] ({U} : Set (Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))))) :
    ∃ ε : ∀ w : ℕ, H.level w →ₐc[O] H.level w,
      (∀ v, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v)) ∧
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((V x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (ε w : H.level w →ₐ[O] H.level w))))) := by
  classical
  obtain ⟨-, -, h3, h4, h5, -, h7⟩ := PDivisibleGroup.tateModule_induced_mem_and_comm_and_add_and_comp p P H S hS

  have co_mul : ∀ (w : ℕ) (f g : H.level w →ₐc[O] H.level w),
      ((WithConv.toConv f * WithConv.toConv g).ofConv : H.level w →ₐ[O] H.level w) =
        (WithConv.toConv (f : H.level w →ₐ[O] H.level w) * WithConv.toConv (g : H.level w →ₐ[O] H.level w)).ofConv :=
    fun w f g => congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul (WithConv.toConv f) (WithConv.toConv g))
  have co_pow : ∀ (w n : ℕ),
      (((WithConv.toConv (BialgHom.id O (H.level w))) ^ n).ofConv : H.level w →ₐ[O] H.level w) =
        ((WithConv.toConv (AlgHom.id O (H.level w))) ^ n).ofConv := by
    intro w n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero]
      exact congrArg WithConv.ofConv (BialgHom.toAlgHom_convOne (R := O) (A := H.level w) (C := H.level w))
    | succ n ih =>
      rw [pow_succ, pow_succ]
      have := congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul ((WithConv.toConv (BialgHom.id O (H.level w))) ^ n)
        (WithConv.toConv (BialgHom.id O (H.level w))))
      rw [WithConv.ofConv_toConv] at this
      rw [this, WithConv.toConv_ofConv]
      show (WithConv.toConv (((WithConv.toConv (BialgHom.id O (H.level w))) ^ n).ofConv : H.level w →ₐ[O] H.level w) *
        WithConv.toConv (AlgHom.id O (H.level w))).ofConv = _
      rw [ih, WithConv.toConv_ofConv]

  have id_pow_card : ∀ w : ℕ, (WithConv.toConv (AlgHom.id O (H.level w))) ^ (p ^ w) = 1 := fun w =>
    PDivisibleGroup.Point.pow_card_eq_one (G := H) (L := H.level w)
      (PDivisibleGroup.Point.ofAlgHom (AlgHom.id O (H.level w)))

  have nsmul_appr : ∀ (r : ℤ_[p]) (w : ℕ),
      PDivisibleGroup.Hopf.nsmulAlgHom O (H.level w) (PadicInt.appr r (w + 1)) =
        PDivisibleGroup.Hopf.nsmulAlgHom O (H.level w) (PadicInt.appr r w) := by
    intro r w
    obtain ⟨m, hm⟩ := PadicInt.dvd_appr_sub_appr r w (w + 1) (Nat.le_succ w)
    have hle : PadicInt.appr r w ≤ PadicInt.appr r (w + 1) := PadicInt.appr_mono r (Nat.le_succ w)
    have heq : PadicInt.appr r (w + 1) = PadicInt.appr r w + p ^ w * m := by omega
    rw [heq, PDivisibleGroup.Hopf.nsmulAlgHom_add, PDivisibleGroup.Hopf.nsmulAlgHom_mul,
      PDivisibleGroup.Hopf.toConv_nsmulAlgHom O (H.level w) (p ^ w), id_pow_card, one_pow, WithConv.toConv_ofConv,
      mul_one, WithConv.ofConv_toConv]
  induction hV using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨u, hu, hU⟩
  | algebraMap r =>
    refine ⟨fun w => ((WithConv.toConv (BialgHom.id O (H.level w))) ^ PadicInt.appr r w).ofConv, fun v => ?_, ?_⟩
    ·
      refine BialgHom.ext fun a => ?_
      have key : ((H.transition v : H.level (v + 1) →ₐ[O] H.level v).comp
          (PDivisibleGroup.Hopf.nsmulAlgHom O (H.level (v + 1)) (PadicInt.appr r (v + 1)))) =
          (PDivisibleGroup.Hopf.nsmulAlgHom O (H.level v) (PadicInt.appr r v)).comp
            (H.transition v : H.level (v + 1) →ₐ[O] H.level v) := by
        rw [← PDivisibleGroup.Hopf.nsmulAlgHom_comp_bialgHom, nsmul_appr]
      have e1 : ∀ (w : ℕ) (b : H.level w),
          (((WithConv.toConv (BialgHom.id O (H.level w))) ^ PadicInt.appr r w).ofConv) b =
            PDivisibleGroup.Hopf.nsmulAlgHom O (H.level w) (PadicInt.appr r w) b := by
        intro w b
        have := AlgHom.congr_fun (co_pow w (PadicInt.appr r w)) b
        exact this
      show H.transition v ((((WithConv.toConv (BialgHom.id O (H.level (v + 1)))) ^ PadicInt.appr r (v + 1)).ofConv) a) =
        (((WithConv.toConv (BialgHom.id O (H.level v))) ^ PadicInt.appr r v).ofConv) (H.transition v a)
      rw [e1, e1]
      exact AlgHom.congr_fun key a
    · rw [Algebra.algebraMap_eq_smul_one]
      intro x n w f hf
      rw [co_pow]
      exact h7 _ _ h5 r x n w f hf
  | add x y _ _ ihx ihy =>
    obtain ⟨ε₁, t₁, i₁⟩ := ihx
    obtain ⟨ε₂, t₂, i₂⟩ := ihy
    refine ⟨fun w => (WithConv.toConv (ε₁ w) * WithConv.toConv (ε₂ w)).ofConv, fun v => ?_, ?_⟩
    · refine BialgHom.ext fun a => ?_
      have key : ((H.transition v : H.level (v + 1) →ₐ[O] H.level v).comp
          ((WithConv.toConv (ε₁ (v + 1) : H.level (v + 1) →ₐ[O] H.level (v + 1)) *
            WithConv.toConv (ε₂ (v + 1) : H.level (v + 1) →ₐ[O] H.level (v + 1))).ofConv)) =
          ((WithConv.toConv (ε₁ v : H.level v →ₐ[O] H.level v) * WithConv.toConv (ε₂ v : H.level v →ₐ[O] H.level v)).ofConv).comp
            (H.transition v : H.level (v + 1) →ₐ[O] H.level v) := by
        rw [AlgHom.comp_convMul_distrib, AlgHom.convMul_comp_bialgHom_distrib]
        have c1 : (H.transition v : H.level (v + 1) →ₐ[O] H.level v).comp (ε₁ (v + 1) : H.level (v + 1) →ₐ[O] H.level (v + 1)) =
            (ε₁ v : H.level v →ₐ[O] H.level v).comp (H.transition v : H.level (v + 1) →ₐ[O] H.level v) :=
          AlgHom.ext fun b => DFunLike.congr_fun (t₁ v) b
        have c2 : (H.transition v : H.level (v + 1) →ₐ[O] H.level v).comp (ε₂ (v + 1) : H.level (v + 1) →ₐ[O] H.level (v + 1)) =
            (ε₂ v : H.level v →ₐ[O] H.level v).comp (H.transition v : H.level (v + 1) →ₐ[O] H.level v) :=
          AlgHom.ext fun b => DFunLike.congr_fun (t₂ v) b
        rw [WithConv.ofConv_toConv, WithConv.ofConv_toConv, WithConv.ofConv_toConv, WithConv.ofConv_toConv, c1, c2]
      have := AlgHom.congr_fun key a
      rw [← co_mul, ← co_mul] at this
      exact this
    · intro x' n w f hf
      rw [co_mul]
      exact h3 _ _ x y i₁ i₂ x' n w f hf
  | mul x y _ _ ihx ihy =>
    obtain ⟨ε₁, t₁, i₁⟩ := ihx
    obtain ⟨ε₂, t₂, i₂⟩ := ihy
    refine ⟨fun w => (ε₂ w).comp (ε₁ w), fun v => ?_, ?_⟩
    · rw [← BialgHom.comp_assoc, t₂ v, BialgHom.comp_assoc, t₁ v, BialgHom.comp_assoc]
    · rw [Module.End.mul_eq_comp]
      intro x' n w f hf
      exact h4 _ _ x y i₁ i₂ x' n w f hf

theorem S42SLP.natCard_fixed_eq_pow
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    {h : ℕ} (H : PDivisibleGroup O p h) (v : ℕ)
    (hfin : Finite (H.Point (AlgebraicClosure ℚ) v))
    (hlift : ∀ (v : ℕ) (x : H.Point (AlgebraicClosure ℚ) v), ∃ y : TateModule p (H.Points (AlgebraicClosure ℚ)),
      (y : ℕ → H.Points (AlgebraicClosure ℚ)) v = H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))
    (hzero : ∀ (v : ℕ) (y : TateModule p (H.Points (AlgebraicClosure ℚ))),
      (y : ℕ → H.Points (AlgebraicClosure ℚ)) v = 0 ↔
        ∃ z : TateModule p (H.Points (AlgebraicClosure ℚ)), y = ((p : ℤ_[p]) ^ v) • z)
    [Module.Free ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))]
    [Module.Finite ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))]
    (eT : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) (he : IsIdempotentElem eT)
    (ε : ∀ w : ℕ, H.level w →ₐ[O] H.level w)
    (hεind : (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((eT x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (ε w)))))) :
    Nat.card {x : H.Point (AlgebraicClosure ℚ) v //
        (PDivisibleGroup.Point.toAlgHom x).comp (ε v) = PDivisibleGroup.Point.toAlgHom x} =
      p ^ (v * Module.finrank ℤ_[p] (LinearMap.range eT)) := by
  classical
  haveI := hfin

  have hrep0 : ∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), ∃ x : H.Point (AlgebraicClosure ℚ) v,
      H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x) = (y : ℕ → H.Points (AlgebraicClosure ℚ)) v := by
    intro y
    obtain ⟨w, x, hx⟩ := PDivisibleGroup.Points.exists_mkAdd H ((y : ℕ → H.Points (AlgebraicClosure ℚ)) v)
    rcases le_total v w with hvw | hwv
    · have hpow : x ^ (p ^ v) = 1 := by
        have ht := TateModule.torsion y v
        rw [← hx, natCast_zsmul, ← map_nsmul, ← ofMul_pow] at ht
        exact Additive.ofMul.injective (H.pointsMkAdd_injective w (ht.trans (map_zero _).symm))
      obtain ⟨x', rfl⟩ := H.exists_pointInclLE_eq_of_pow_eq_one hvw x hpow
      exact ⟨x', by rw [← hx, H.pointsMkAdd_pointInclLE]⟩
    · exact ⟨H.pointInclLE (AlgebraicClosure ℚ) hwv x, by rw [H.pointsMkAdd_pointInclLE]; exact hx⟩
  choose rep hrep using hrep0
  have hrep_eq : ∀ (y : TateModule p (H.Points (AlgebraicClosure ℚ))) (x : H.Point (AlgebraicClosure ℚ) v),
      H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x) = (y : ℕ → H.Points (AlgebraicClosure ℚ)) v → rep y = x := fun y x hx =>
    Additive.ofMul.injective (H.pointsMkAdd_injective v ((hrep y).trans hx.symm))

  let π : TateModule p (H.Points (AlgebraicClosure ℚ)) →+ Additive (H.Point (AlgebraicClosure ℚ) v) :=
    { toFun := fun y => Additive.ofMul (rep y)
      map_zero' := by
        rw [ofMul_eq_zero]
        exact hrep_eq 0 1 (by rw [ofMul_one, map_zero, TateModule.coe_zero, Pi.zero_apply])
      map_add' := fun y z => by
        rw [← ofMul_mul]
        exact congrArg Additive.ofMul (hrep_eq (y + z) _ (by
          rw [ofMul_mul, map_add, hrep, hrep, TateModule.coe_add, Pi.add_apply])) }
  have hπ : ∀ y, π y = Additive.ofMul (rep y) := fun y => rfl

  have heT : ∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), rep (eT y) = PDivisibleGroup.Point.ofAlgHom
      ((PDivisibleGroup.Point.toAlgHom (rep y)).comp (ε v)) := fun y =>
    hrep_eq _ _ (hεind y v v (rep y) (hrep y)).symm

  set A : Submodule ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))) := LinearMap.range eT with hA
  have hAfix : ∀ a : A, eT (a : TateModule p (H.Points (AlgebraicClosure ℚ))) = a := fun a => by
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 a.2
    rw [← hy, ← Module.End.mul_apply, he.eq]
  haveI : IsNoetherianRing ℤ_[p] := inferInstance
  haveI : IsNoetherian ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))) := isNoetherian_of_isNoetherianRing_of_finite ℤ_[p] _
  haveI : Module.Finite ℤ_[p] A := Module.IsNoetherian.finite ℤ_[p] A
  haveI : Module.Free ℤ_[p] A := Module.free_of_finite_type_torsion_free'
  set r := Module.finrank ℤ_[p] A with hr
  let bA := Module.finBasis ℤ_[p] A

  let Λ : A →+ Additive (H.Point (AlgebraicClosure ℚ) v) := π.comp A.toAddSubgroup.subtype
  let Γ : A →+ (Fin r → ZMod (p ^ v)) :=
    { toFun := fun a i => PadicInt.toZModPow v (bA.repr a i)
      map_zero' := by funext i; rw [map_zero, Finsupp.zero_apply, map_zero]; rfl
      map_add' := fun a b => by funext i; rw [map_add, Finsupp.add_apply, map_add]; rfl }

  have hrange : ∀ x : H.Point (AlgebraicClosure ℚ) v,
      (PDivisibleGroup.Point.toAlgHom x).comp (ε v) = PDivisibleGroup.Point.toAlgHom x ↔
        Additive.ofMul x ∈ Λ.range := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hlift v x
      have hrepy : rep y = x := hrep_eq y x hy.symm
      refine ⟨⟨eT y, LinearMap.mem_range_self eT y⟩, ?_⟩
      change π (eT y) = Additive.ofMul x
      rw [hπ, heT, hrepy, hx, PDivisibleGroup.Point.ofAlgHom_toAlgHom]
    · rintro ⟨a, ha⟩
      change π (a : TateModule p (H.Points (AlgebraicClosure ℚ))) = Additive.ofMul x at ha
      rw [hπ] at ha
      have hxa : rep (a : TateModule p (H.Points (AlgebraicClosure ℚ))) = x := Additive.ofMul.injective ha
      have h1 := heT (a : TateModule p (H.Points (AlgebraicClosure ℚ)))
      rw [hAfix a, hxa] at h1
      have h2 := congrArg PDivisibleGroup.Point.toAlgHom h1
      rw [PDivisibleGroup.Point.toAlgHom_ofAlgHom] at h2
      exact h2.symm
  have e1 : {x : H.Point (AlgebraicClosure ℚ) v //
      (PDivisibleGroup.Point.toAlgHom x).comp (ε v) = PDivisibleGroup.Point.toAlgHom x} ≃ Λ.range :=
    { toFun := fun x => ⟨Additive.ofMul x.1, (hrange x.1).1 x.2⟩
      invFun := fun q => ⟨Additive.toMul q.1, (hrange _).2 (by simpa only [ofMul_toMul] using q.2)⟩
      left_inv := fun x => by simp
      right_inv := fun q => by simp }

  have hkerΛ : ∀ a : A, Λ a = 0 ↔ ∃ a' : A, a = ((p : ℤ_[p]) ^ v) • a' := by
    intro a
    change π (a : TateModule p (H.Points (AlgebraicClosure ℚ))) = 0 ↔ _
    rw [hπ, ofMul_eq_zero]
    constructor
    · intro h1
      have hv0 : ((a : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) v = 0 := by
        rw [← hrep (a : TateModule p (H.Points (AlgebraicClosure ℚ))), h1, ofMul_one, map_zero]
      obtain ⟨z, hz⟩ := (hzero v (a : TateModule p (H.Points (AlgebraicClosure ℚ)))).1 hv0
      refine ⟨⟨eT z, LinearMap.mem_range_self eT z⟩, Subtype.ext ?_⟩
      change (a : TateModule p (H.Points (AlgebraicClosure ℚ))) = ((p : ℤ_[p]) ^ v) • eT z
      rw [← map_smul, ← hz, hAfix a]
    · rintro ⟨a', rfl⟩
      apply hrep_eq
      rw [ofMul_one, map_zero, Submodule.coe_smul, (hzero v _).2 ⟨(a' : TateModule p (H.Points (AlgebraicClosure ℚ))), rfl⟩]
  have hkerΓ : ∀ a : A, Γ a = 0 ↔ ∃ a' : A, a = ((p : ℤ_[p]) ^ v) • a' := by
    intro a
    constructor
    · intro h0
      have hi : ∀ i, bA.repr a i ∈ Ideal.span {(p : ℤ_[p]) ^ v} := fun i => by
        rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
        exact congrFun h0 i
      choose c hc using fun i => Ideal.mem_span_singleton'.1 (hi i)
      refine ⟨bA.equivFun.symm c, bA.repr.injective (Finsupp.ext fun i => ?_)⟩
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← hc i, mul_comm, bA.equivFun_symm_apply, bA.repr_sum_self]
    · rintro ⟨a', rfl⟩
      funext i
      change PadicInt.toZModPow v (bA.repr (((p : ℤ_[p]) ^ v) • a') i) = 0
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self,
        zero_mul]

  have hΓsurj : Function.Surjective Γ := by
    intro c
    choose d hd using fun i => ZMod.ringHom_surjective (PadicInt.toZModPow v) (c i)
    refine ⟨bA.equivFun.symm d, funext fun i => ?_⟩
    change PadicInt.toZModPow v (bA.repr (bA.equivFun.symm d) i) = c i
    rw [bA.equivFun_symm_apply, bA.repr_sum_self, hd]

  have hker : Λ.ker = Γ.ker := by
    ext a
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hkerΛ, hkerΓ]
  have e2 : Λ.range ≃ Γ.range :=
    ((QuotientAddGroup.quotientKerEquivRange Λ).symm.trans
      ((QuotientAddGroup.quotientAddEquivOfEq hker).trans (QuotientAddGroup.quotientKerEquivRange Γ))).toEquiv
  have e3 : Γ.range ≃ (Fin r → ZMod (p ^ v)) :=
    Equiv.ofBijective (fun q => (q : Fin r → ZMod (p ^ v)))
      ⟨fun a b hab => Subtype.ext hab, fun c => by
        obtain ⟨a, ha⟩ := hΓsurj c
        exact ⟨⟨c, a, ha⟩, rfl⟩⟩
  haveI : NeZero (p ^ v) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [Nat.card_congr e1, Nat.card_congr e2, Nat.card_congr e3, Nat.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Nat.card_zmod, ← pow_mul]

theorem S42SLP.exists_bijective_of_two_splittings
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [Algebra O (ZMod p)]
    {A A₁ : Type} [CommRing A] [HopfAlgebra O A] [CommRing A₁] [HopfAlgebra O A₁]
    (ε : A →ₐc[O] A) (π : A →ₐc[O] A₁) (σ : A₁ →ₐ[O] A)
    (hπσ : (π : A →ₐ[O] A₁).comp σ = AlgHom.id O A₁) (hσπ : σ.comp (π : A →ₐ[O] A₁) = (ε : A →ₐ[O] A))
    {C : Type} [CommRing C] [HopfAlgebra (ZMod p) C]
    (q : ZMod p ⊗[O] A →ₐc[ZMod p] C) (i : C →ₐc[ZMod p] ZMod p ⊗[O] A)
    (hqi : q.comp i = BialgHom.id (ZMod p) C)
    (hiq : i.comp q = Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ε)
    {M E : Type} [CommRing M] [HopfAlgebra (ZMod p) M] [CommRing E] [HopfAlgebra (ZMod p) E]
    (ΘC : C →ₐc[ZMod p] M ⊗[ZMod p] E) (hΘC : Function.Bijective ΘC) :
    ∃ Θ : ZMod p ⊗[O] A₁ →ₐc[ZMod p] M ⊗[ZMod p] E, Function.Bijective Θ := by
  classical

  have hσπ' : ∀ a : A, σ (π a) = ε a := fun a => by
    have := AlgHom.congr_fun hσπ a; simpa using this
  have hπσ' : ∀ a₁ : A₁, π (σ a₁) = a₁ := fun a₁ => by
    have := AlgHom.congr_fun hπσ a₁; simpa using this
  have hqi' : ∀ c : C, q (i c) = c := fun c => by
    have := DFunLike.congr_fun hqi c; simpa using this
  have hiq' : ∀ w : ZMod p ⊗[O] A, i (q w) = Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ε w :=
    fun w => by have := DFunLike.congr_fun hiq w; simpa using this

  let lam : C →ₐc[ZMod p] ZMod p ⊗[O] A₁ := (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π).comp i
  let mu : ZMod p ⊗[O] A₁ → C := fun z => q (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) σ z)
  have I1 : ∀ w : ZMod p ⊗[O] A,
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) σ
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π w) =
      Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ε w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c a =>
      rw [Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, hσπ']
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have I2 : ∀ z : ZMod p ⊗[O] A₁,
      Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ε
          (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) σ z)) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c a₁ =>
      rw [Algebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul,
        AlgHom.id_apply, ← hσπ', hπσ', hπσ']
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hleft : Function.LeftInverse mu lam := fun c => by
    change q (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) σ
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π (i c))) = c
    rw [I1, ← hiq', hqi', hqi']
  have hright : Function.RightInverse mu lam := fun z => by
    change Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π
      (i (q (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) σ z))) = z
    rw [hiq', I2]
  have hlam : Function.Bijective lam := ⟨hleft.injective, hright.surjective⟩
  let lamE : C ≃ₐc[ZMod p] ZMod p ⊗[O] A₁ := BialgEquiv.ofBijective lam hlam
  refine ⟨ΘC.comp (lamE.symm : ZMod p ⊗[O] A₁ →ₐc[ZMod p] C), hΘC.comp lamE.symm.bijective⟩

def S42SLP.biter {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A] (u : A →ₐc[R] A) : ℕ → (A →ₐc[R] A)
  | 0 => BialgHom.id R A
  | k + 1 => u.comp (S42SLP.biter u k)

theorem S42SLP.biter_zero {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A] (u : A →ₐc[R] A) :
    S42SLP.biter u 0 = BialgHom.id R A := rfl

theorem S42SLP.biter_succ {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A] (u : A →ₐc[R] A) (k : ℕ) :
    S42SLP.biter u (k + 1) = u.comp (S42SLP.biter u k) := rfl

theorem S42SLP.toAlgHom_biter {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A] (u : A →ₐc[R] A) (k : ℕ) :
    (S42SLP.biter u k : A →ₐ[R] A) = (u : A →ₐ[R] A) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [S42SLP.biter_succ, pow_succ']
    show (u : A →ₐ[R] A).comp (S42SLP.biter u k : A →ₐ[R] A) = _
    rw [ih]
    rfl

theorem S42SLP.baseChange_map_comp (p : ℕ) {O : Type} [CommRing O] [Algebra O (ZMod p)]
    {A : Type} [CommRing A] [HopfAlgebra O A] (f g : A →ₐc[O] A) :
    Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (f.comp g) =
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) f).comp
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) g) := by
  refine BialgHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c x =>
    rw [BialgHom.comp_apply, Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul,
      Bialgebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem S42SLP.baseChange_map_id (p : ℕ) {O : Type} [CommRing O] [Algebra O (ZMod p)]
    {A : Type} [CommRing A] [HopfAlgebra O A] :
    Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (BialgHom.id O A) =
      BialgHom.id (ZMod p) (ZMod p ⊗[O] A) := by
  refine BialgHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c x => rw [Bialgebra.TensorProduct.map_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

section CartierDualCoe

variable {R B : Type*} [CommRing R] [CommRing B] [Bialgebra R B] [Module.Finite R B] [Module.Free R B]

theorem S42SLP.cd_toLinearMap_comp (g f : CartierDual R B →ₐc[R] CartierDual R B) :
    ((g.comp f : CartierDual R B →ₐc[R] CartierDual R B) : CartierDual R B →ₗ[R] CartierDual R B) = (g : CartierDual R B →ₗ[R] CartierDual R B) ∘ₗ (f : CartierDual R B →ₗ[R] CartierDual R B) :=
  LinearMap.ext fun _ => rfl

theorem S42SLP.cd_convMul_ofConv_comp (f g : CartierDual R B →ₗ[R] CartierDual R B) (w : CartierDual R B →ₐc[R] CartierDual R B) :
    (WithConv.toConv f * WithConv.toConv g).ofConv ∘ₗ (w : CartierDual R B →ₗ[R] CartierDual R B) =
      (WithConv.toConv (f ∘ₗ (w : CartierDual R B →ₗ[R] CartierDual R B)) * WithConv.toConv (g ∘ₗ (w : CartierDual R B →ₗ[R] CartierDual R B))).ofConv :=
  LinearMap.convMul_comp_coalgHom_distrib (WithConv.toConv f) (WithConv.toConv g) w.toCoalgHom

theorem S42SLP.cd_algHom_comp_comp (F : CartierDual R B →ₐ[R] CartierDual R B) (a w : CartierDual R B →ₐc[R] CartierDual R B) :
    ((F : CartierDual R B →ₗ[R] CartierDual R B) ∘ₗ (a : CartierDual R B →ₗ[R] CartierDual R B)) ∘ₗ (w : CartierDual R B →ₗ[R] CartierDual R B) =
      (F : CartierDual R B →ₗ[R] CartierDual R B) ∘ₗ ((a.comp w : CartierDual R B →ₐc[R] CartierDual R B) : CartierDual R B →ₗ[R] CartierDual R B) :=
  LinearMap.ext fun _ => rfl

theorem S42SLP.cd_comp_comp_eq_of_comm (b V w : CartierDual R B →ₐc[R] CartierDual R B)
    (h : (V : CartierDual R B →ₗ[R] CartierDual R B) ∘ₗ (w : CartierDual R B →ₗ[R] CartierDual R B) = (w : CartierDual R B →ₗ[R] CartierDual R B) ∘ₗ (V : CartierDual R B →ₗ[R] CartierDual R B)) :
    ((b : CartierDual R B →ₗ[R] CartierDual R B) ∘ₗ (V : CartierDual R B →ₗ[R] CartierDual R B)) ∘ₗ (w : CartierDual R B →ₗ[R] CartierDual R B) =
      ((b.comp w : CartierDual R B →ₐc[R] CartierDual R B) : CartierDual R B →ₗ[R] CartierDual R B) ∘ₗ (V : CartierDual R B →ₗ[R] CartierDual R B) := by
  rw [LinearMap.comp_assoc, h, ← LinearMap.comp_assoc, S42SLP.cd_toLinearMap_comp]

theorem S42SLP.cd_map_comm (V w : B →ₐc[R] B) (h : w.comp V = V.comp w) :
    (CartierDual.map V : CartierDual R B →ₗ[R] CartierDual R B) ∘ₗ (CartierDual.map w : CartierDual R B →ₗ[R] CartierDual R B) =
      (CartierDual.map w : CartierDual R B →ₗ[R] CartierDual R B) ∘ₗ (CartierDual.map V : CartierDual R B →ₗ[R] CartierDual R B) := by
  rw [← S42SLP.cd_toLinearMap_comp, ← S42SLP.cd_toLinearMap_comp, ← CartierDual.map_comp, ← CartierDual.map_comp, h]

end CartierDualCoe

theorem S42SLP.cartierDual_map_baseChange_biter (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [Algebra O (ZMod p)]
    {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A] (u₁ : A →ₐc[O] A) (k : ℕ) :
    (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (S42SLP.biter u₁ k)) :
      CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p] CartierDual (ZMod p) (ZMod p ⊗[O] A)) =
      (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) u₁) :
        CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p] CartierDual (ZMod p) (ZMod p ⊗[O] A)) ^ k := by
  induction k with
  | zero =>
    rw [S42SLP.biter_zero, S42SLP.baseChange_map_id, CartierDual.map_id, pow_zero]
    rfl
  | succ k ih =>
    rw [S42SLP.biter_succ, S42SLP.baseChange_map_comp, CartierDual.map_comp, pow_succ, Module.End.mul_eq_comp, ← ih]
    rfl

theorem S42SLP.bialgHom_toLinearMap_comp {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] (g : B →ₐc[R] C) (f : A →ₐc[R] B) :
    ((g.comp f : A →ₐc[R] C) : A →ₗ[R] C) = (g : B →ₗ[R] C) ∘ₗ (f : A →ₗ[R] B) :=
  LinearMap.ext fun _ => rfl

theorem S42SLP.bialgHom_toCoalgHom_toLinearMap {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Bialgebra R A] [Bialgebra R B] (f : A →ₐc[R] B) :
    f.toCoalgHom.toLinearMap = (f : A →ₗ[R] B) :=
  LinearMap.ext fun _ => rfl

theorem S42SLP.cartierDual_map_baseChange_comp_biter (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [Algebra O (ZMod p)]
    {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A] (u₁ β : A →ₐc[O] A) (n : ℕ) :
    (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (β.comp (S42SLP.biter u₁ n))) :
      CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p] CartierDual (ZMod p) (ZMod p ⊗[O] A)) =
      ((CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) u₁) :
        CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p] CartierDual (ZMod p) (ZMod p ⊗[O] A)) ^ n) ∘ₗ
      (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) β) : CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p] CartierDual (ZMod p) (ZMod p ⊗[O] A)) := by
  rw [S42SLP.baseChange_map_comp, CartierDual.map_comp, S42SLP.cd_toLinearMap_comp, S42SLP.cartierDual_map_baseChange_biter]

theorem S42SLP.cartierDual_map_eq_convMul_of_factor
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [Algebra O (ZMod p)]
    {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
    (u₁ ε₁ : A →ₐc[O] A)
    (hFV : ∀ Fk : ZMod p ⊗[O] A →ₐc[ZMod p] ZMod p ⊗[O] A, (∀ x, Fk x = x ^ p) →
      ∀ FD : CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₐ[ZMod p]
          CartierDual (ZMod p) (ZMod p ⊗[O] A), (∀ ψ, FD ψ = ψ ^ p) →
      ∃ (n : ℕ) (a b : CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₐc[ZMod p]
          CartierDual (ZMod p) (ZMod p ⊗[O] A)),
        (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) u₁) :
            CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p]
              CartierDual (ZMod p) (ZMod p ⊗[O] A)) ^ n =
          (WithConv.toConv ((FD : CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] A)) ∘ₗ
              (a : CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] A))) *
            WithConv.toConv ((b : CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] A)) ∘ₗ
              (CartierDual.map Fk : CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] A)))).ofConv)
    (hβ : ∀ n : ℕ, ∃ β : A →ₐc[O] A, (ε₁ : A →ₐ[O] A) = (β : A →ₐ[O] A).comp ((u₁ : A →ₐ[O] A) ^ n)) :
    ∀ Fk : ZMod p ⊗[O] A →ₐc[ZMod p] ZMod p ⊗[O] A, (∀ x, Fk x = x ^ p) →
      ∀ FD : CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₐ[ZMod p]
          CartierDual (ZMod p) (ZMod p ⊗[O] A), (∀ ψ, FD ψ = ψ ^ p) →
      ∃ (a b : CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₐc[ZMod p]
          CartierDual (ZMod p) (ZMod p ⊗[O] A)),
        (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ε₁) :
            CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p]
              CartierDual (ZMod p) (ZMod p ⊗[O] A)) =
          (WithConv.toConv ((FD : CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] A)) ∘ₗ
              (a : CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] A))) *
            WithConv.toConv ((b : CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] A)) ∘ₗ
              (CartierDual.map Fk : CartierDual (ZMod p) (ZMod p ⊗[O] A) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] A)))).ofConv := by
  intro Fk hFk FD hFD
  obtain ⟨n, a, b, hn⟩ := hFV Fk hFk FD hFD
  obtain ⟨β, hβn⟩ := hβ n

  have hε : ε₁ = β.comp (S42SLP.biter u₁ n) := BialgHom.ext fun x => by
    have h1 := AlgHom.congr_fun hβn x
    rw [← S42SLP.toAlgHom_biter] at h1
    exact h1

  have hcomm : (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) β).comp Fk =
      Fk.comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) β) :=
    BialgHom.ext fun x => by rw [BialgHom.comp_apply, BialgHom.comp_apply, hFk, hFk, map_pow]
  refine ⟨a.comp (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) β)),
    b.comp (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) β)), ?_⟩
  rw [hε, S42SLP.cartierDual_map_baseChange_comp_biter, hn, S42SLP.cd_convMul_ofConv_comp, S42SLP.cd_algHom_comp_comp,
    S42SLP.cd_comp_comp_eq_of_comm b (CartierDual.map Fk) _ (S42SLP.cd_map_comm Fk _ hcomm)]

theorem S42SLP.algebraMap_injective_of_res
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra O (AlgebraicClosure ℚ)] [Algebra O (ZMod p)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (hres : ∀ x : O, algebraMap O (ZMod p) x = 0 ↔
      P.valuation (algebraMap O (AlgebraicClosure ℚ) x) < 1) :
    Function.Injective (algebraMap O (AlgebraicClosure ℚ)) := by
  classical
  haveI : Nontrivial O := inferInstance
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0

  have hker : RingHom.ker (algebraMap O (AlgebraicClosure ℚ)) ≠ ⊥ := fun hbot => hx0 (by
    have : x ∈ RingHom.ker (algebraMap O (AlgebraicClosure ℚ)) := hx
    rwa [hbot, Ideal.mem_bot] at this)
  haveI : (RingHom.ker (algebraMap O (AlgebraicClosure ℚ))).IsPrime := RingHom.ker_isPrime _
  have hmax : (RingHom.ker (algebraMap O (AlgebraicClosure ℚ))).IsMaximal := IsPrime.to_maximal_ideal hker
  have heq : RingHom.ker (algebraMap O (AlgebraicClosure ℚ)) = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
  have hpunit : ¬ IsUnit ((p : ℕ) : O) := fun hu => by
    have h1 := hu.map (algebraMap O (ZMod p))
    rw [map_natCast, ZMod.natCast_self] at h1
    exact not_isUnit_zero h1
  have hpmem : ((p : ℕ) : O) ∈ RingHom.ker (algebraMap O (AlgebraicClosure ℚ)) := by
    rw [heq]
    exact (IsLocalRing.mem_maximalIdeal _).2 hpunit
  rw [RingHom.mem_ker, map_natCast] at hpmem
  exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hpmem)

theorem S42SLP.moduleFinite_tateModule
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    {h : ℕ} (H : PDivisibleGroup O p h)
    (hcardH : ∀ v : ℕ, Finite (H.Point (AlgebraicClosure ℚ) v) ∧ Nat.card (H.Point (AlgebraicClosure ℚ) v) = p ^ (v * h))
    [Module.Free ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))]
    (hrank : Module.finrank ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))) = h) :
    Module.Finite ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))) := by
  classical
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  ·
    have hone : ∀ (v : ℕ) (x : H.Point (AlgebraicClosure ℚ) v), x = 1 := fun v x => by
      haveI := (hcardH v).1
      have hc : Nat.card (H.Point (AlgebraicClosure ℚ) v) = 1 := by rw [(hcardH v).2, h0, mul_zero, pow_zero]
      haveI : Subsingleton (H.Point (AlgebraicClosure ℚ) v) := (Nat.card_eq_one_iff_unique.1 hc).1
      exact Subsingleton.elim _ _
    haveI : Subsingleton (TateModule p (H.Points (AlgebraicClosure ℚ))) := ⟨fun y z => Subtype.ext (funext fun n => by
      obtain ⟨v, x, hx⟩ := PDivisibleGroup.Points.exists_mkAdd H ((y : ℕ → H.Points (AlgebraicClosure ℚ)) n)
      obtain ⟨v', x', hx'⟩ := PDivisibleGroup.Points.exists_mkAdd H ((z : ℕ → H.Points (AlgebraicClosure ℚ)) n)
      rw [← hx, ← hx', hone v x, hone v' x', ofMul_one, ofMul_one, map_zero, map_zero])⟩
    haveI : Finite (TateModule p (H.Points (AlgebraicClosure ℚ))) := Finite.of_subsingleton
    exact Module.Finite.of_finite
  · exact Module.finite_of_finrank_pos (by rw [hrank]; exact hpos)

theorem S42SLP.moduleFinite_adjoin_singleton
    (p : ℕ) [Fact p.Prime] {M : Type} [AddCommGroup M] [Module ℤ_[p] M] [Module.Finite ℤ_[p] M] [Module.Free ℤ_[p] M]
    (U : Module.End ℤ_[p] M) :
    Module.Finite ℤ_[p] ↥(Algebra.adjoin ℤ_[p] ({U} : Set (Module.End ℤ_[p] M))) := by
  classical
  haveI : IsNoetherianRing ℤ_[p] := inferInstance
  haveI : IsNoetherian ℤ_[p] (Module.End ℤ_[p] M) := isNoetherian_of_isNoetherianRing_of_finite ℤ_[p] _
  exact Module.Finite.of_injective (Algebra.adjoin ℤ_[p] ({U} : Set (Module.End ℤ_[p] M))).val.toLinearMap
    Subtype.val_injective

theorem S42SLP.finrank_range_add_finrank_range_one_sub
    (p : ℕ) [Fact p.Prime] {M : Type} [AddCommGroup M] [Module ℤ_[p] M] [Module.Finite ℤ_[p] M] [Module.Free ℤ_[p] M]
    (e : Module.End ℤ_[p] M) (he : IsIdempotentElem e) :
    Module.finrank ℤ_[p] (LinearMap.range e) + Module.finrank ℤ_[p] (LinearMap.range (1 - e)) =
      Module.finrank ℤ_[p] M := by
  classical
  haveI : IsNoetherianRing ℤ_[p] := inferInstance
  haveI : IsNoetherian ℤ_[p] M := isNoetherian_of_isNoetherianRing_of_finite ℤ_[p] _
  have hc : IsCompl (LinearMap.range e) (LinearMap.range (1 - e)) := by
    rw [← LinearMap.IsIdempotentElem.ker_eq_range_one_sub he]
    exact LinearMap.IsIdempotentElem.isCompl he
  haveI : Module.Finite ℤ_[p] (LinearMap.range e) := Module.IsNoetherian.finite ℤ_[p] _
  haveI : Module.Finite ℤ_[p] (LinearMap.range (1 - e)) := Module.IsNoetherian.finite ℤ_[p] _
  haveI : Module.Free ℤ_[p] (LinearMap.range e) := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free ℤ_[p] (LinearMap.range (1 - e)) := Module.free_of_finite_type_torsion_free'
  rw [← Module.finrank_prod, (Submodule.prodEquivOfIsCompl _ _ hc).finrank_eq]

set_option maxHeartbeats 4000000 in
theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra O (AlgebraicClosure ℚ)] [Algebra O (ZMod p)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (hres : ∀ x : O, algebraMap O (ZMod p) x = 0 ↔
      P.valuation (algebraMap O (AlgebraicClosure ℚ) x) < 1)
    {h : ℕ} (H : PDivisibleGroup O p h)
    (u : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (hu : ∀ v : ℕ, (H.transition v).comp (u (v + 1)) = (u v).comp (H.transition v))
    (U : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))
    (hU : ∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ)
      (f : H.Point (AlgebraicClosure ℚ) w),
      H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
        (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
      ((U x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom f).comp (u w : H.level w →ₐ[O] H.level w)))))
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
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)))).ofConv) :
    ∃ N : ℕ, ∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)),

      (∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
          (y : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
        ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      ∃ z : TateModule p (H.Points (AlgebraicClosure ℚ)),

        (∀ n : ℕ, ∃ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (z : ℕ → H.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : H.level w, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) ∧

        ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ),
          (∀ x : AlgebraicClosure ℚ, τ' x = τ x) → τ ∈ P.inertiaSubgroupIn ℚ →
          H.tateModuleRep (AlgebraicClosure ℚ) τ' ((U ^ N) y - (p : ℤ_[p]) • z) =
            ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) •
              ((U ^ N) y - (p : ℤ_[p]) • z) := by
  classical

  have hinj : Function.Injective (algebraMap O (AlgebraicClosure ℚ)) :=
    S42SLP.algebraMap_injective_of_res p P hOP hres

  have hcardH : ∀ v : ℕ, Finite (H.Point (AlgebraicClosure ℚ) v) ∧ Nat.card (H.Point (AlgebraicClosure ℚ) v) = p ^ (v * h) :=
    fun v => PDivisibleGroup.finite_point_and_natCard_point_eq_pow p H (AlgebraicClosure ℚ) v
  obtain ⟨hlift, hzero, hfree, hrankT⟩ :=
    PDivisibleGroup.exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq p H
      (AlgebraicClosure ℚ) hcardH

  obtain ⟨⟨S, hS, hsat⟩, -⟩ :=
    PDivisibleGroup.exists_submodule_tateModule_reduction_and_rep_sub_mem_of_mem_inertiaSubgroupIn p P hOP H
  obtain ⟨hI1, hI2, hI3, hI4, hI5, hI6, hI7⟩ :=
    PDivisibleGroup.tateModule_induced_mem_and_comm_and_add_and_comp p P H S hS

  haveI : Module.Free ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))) := hfree
  haveI : Module.Finite ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))) :=
    S42SLP.moduleFinite_tateModule p H hcardH hrankT
  let Aadj : Subalgebra ℤ_[p] (Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) :=
    Algebra.adjoin ℤ_[p] ({U} : Set (Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))))
  letI : CommRing ↥Aadj := Algebra.adjoinCommRingOfComm ℤ_[p] (by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb])
  haveI : Module.Finite ℤ_[p] ↥Aadj := S42SLP.moduleFinite_adjoin_singleton p U
  obtain ⟨e, he, -, ⟨b, hb, hUb⟩, N, hN⟩ :=
    exists_idempotent_mul_eq_and_pow_mul_sub_mem_of_moduleFinite_padicInt p ↥Aadj
      ⟨U, Algebra.self_mem_adjoin_singleton ℤ_[p] U⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hN

  have heT : IsIdempotentElem (e : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) := by
    have := congrArg (fun z : ↥Aadj => (z : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))) he.eq
    simp at this
    exact this

  obtain ⟨ε, hεt, hεind⟩ := S42SLP.exists_bialgHom_family_of_mem_adjoin p P H S hS u hu U hU
    (e : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) e.2
  obtain ⟨ε', hε't, hε'ind⟩ := S42SLP.exists_bialgHom_family_of_mem_adjoin p P H S hS u hu U hU
    (1 - (e : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))))
    (Subalgebra.sub_mem _ (Subalgebra.one_mem _) e.2)

  have hlift' : ∀ (v : ℕ) (x : H.Point (AlgebraicClosure ℚ) v), ∃ y : TateModule p (H.Points (AlgebraicClosure ℚ)),
      (y : ℕ → H.Points (AlgebraicClosure ℚ)) v = H.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x) := hlift
  set eT : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))) :=
    (e : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) with heTdef
  have he2 : eT * eT = eT := heT.eq

  have hε : ∀ v, (ε v).comp (ε v) = ε v := by
    have hind := hI4 (fun w => (ε w : H.level w →ₐ[O] H.level w)) (fun w => (ε w : H.level w →ₐ[O] H.level w)) eT eT hεind hεind
    rw [← Module.End.mul_eq_comp, he2] at hind
    have hL := S42SLP.level_eq_of_induced_eq p hinj H hlift' eT _ _ hind hεind
    intro v
    exact BialgHom.ext fun a => AlgHom.congr_fun (hL v) a
  have hε' : ∀ v, (ε' v).comp (ε' v) = ε' v := by
    have h1e : (1 - eT) * (1 - eT) = 1 - eT := (heT.one_sub).eq
    have hind := hI4 (fun w => (ε' w : H.level w →ₐ[O] H.level w)) (fun w => (ε' w : H.level w →ₐ[O] H.level w)) _ _ hε'ind hε'ind
    rw [← Module.End.mul_eq_comp, h1e] at hind
    have hL := S42SLP.level_eq_of_induced_eq p hinj H hlift' (1 - eT) _ _ hind hε'ind
    intro v
    exact BialgHom.ext fun a => AlgHom.congr_fun (hL v) a
  have hεε' : ∀ v, (ε v : H.level v →ₐ[O] H.level v).comp (ε' v : H.level v →ₐ[O] H.level v) =
      (Algebra.ofId O (H.level v)).comp (Bialgebra.counitAlgHom O (H.level v)) := by

    have hind := hI4 (fun w => (ε' w : H.level w →ₐ[O] H.level w)) (fun w => (ε w : H.level w →ₐ[O] H.level w)) _ _ hε'ind hεind
    have h0 : (1 - eT) ∘ₗ eT = 0 := by
      rw [← Module.End.mul_eq_comp, sub_mul, one_mul, he2, sub_self]
    rw [h0] at hind
    exact S42SLP.level_eq_of_induced_eq p hinj H hlift' 0 _ _ hind hI6
  have hε'ε : ∀ v, (ε' v : H.level v →ₐ[O] H.level v).comp (ε v : H.level v →ₐ[O] H.level v) =
      (Algebra.ofId O (H.level v)).comp (Bialgebra.counitAlgHom O (H.level v)) := by
    have hind := hI4 (fun w => (ε w : H.level w →ₐ[O] H.level w)) (fun w => (ε' w : H.level w →ₐ[O] H.level w)) _ _ hεind hε'ind
    have h0 : eT ∘ₗ (1 - eT) = 0 := by
      rw [← Module.End.mul_eq_comp, mul_sub, mul_one, he2, sub_self]
    rw [h0] at hind
    exact S42SLP.level_eq_of_induced_eq p hinj H hlift' 0 _ _ hind hI6
  have hsum : ∀ v, WithConv.toConv (ε v : H.level v →ₐ[O] H.level v) *
      WithConv.toConv (ε' v : H.level v →ₐ[O] H.level v) = WithConv.toConv (AlgHom.id O (H.level v)) := by
    have hind := hI3 (fun w => (ε w : H.level w →ₐ[O] H.level w)) (fun w => (ε' w : H.level w →ₐ[O] H.level w)) _ _ hεind hε'ind
    rw [add_sub_cancel] at hind
    have hL := S42SLP.level_eq_of_induced_eq p hinj H hlift' 1 _ _ hind hI5
    intro v
    have := congrArg WithConv.toConv (hL v)
    simpa only [WithConv.toConv_ofConv] using this

  let h₁ : ℕ := Module.finrank ℤ_[p] (LinearMap.range eT)
  let h₂ : ℕ := Module.finrank ℤ_[p] (LinearMap.range (1 - eT))
  have hh : h₁ + h₂ = h := by
    rw [← hrankT]; exact S42SLP.finrank_range_add_finrank_range_one_sub p eT heT
  have hcard₁ : ∀ v, Nat.card {x : H.Point (AlgebraicClosure ℚ) v //
      (PDivisibleGroup.Point.toAlgHom x).comp (ε v : H.level v →ₐ[O] H.level v) = PDivisibleGroup.Point.toAlgHom x} =
        p ^ (v * h₁) :=
    fun v => S42SLP.natCard_fixed_eq_pow p H v (hcardH v).1 hlift' hzero eT heT
      (fun w => (ε w : H.level w →ₐ[O] H.level w)) hεind
  have hcard₂ : ∀ v, Nat.card {x : H.Point (AlgebraicClosure ℚ) v //
      (PDivisibleGroup.Point.toAlgHom x).comp (ε' v : H.level v →ₐ[O] H.level v) = PDivisibleGroup.Point.toAlgHom x} =
        p ^ (v * h₂) :=
    fun v => S42SLP.natCard_fixed_eq_pow p H v (hcardH v).1 hlift' hzero (1 - eT) heT.one_sub
      (fun w => (ε' w : H.level w →ₐ[O] H.level w)) hε'ind

  obtain ⟨H₁, H₂, π₁, π₂, σ₁, σ₂, Θ, hπ₁s, hπ₂s, hπ₁t, hπ₂t, hπσ₁, hσπ₁, hπσ₂, hσπ₂, hΘb, hΘ⟩ :=
    PDivisibleGroup.exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self p H ε ε' hε hε'
      hεε' hε'ε hsum hεt hε't h₁ h₂ hh hcard₁ hcard₂

  let ε₁bar : ZMod p ⊗[O] H.level 1 →ₐc[ZMod p] ZMod p ⊗[O] H.level 1 :=
    Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε 1)
  have hε₁bar_idem : ε₁bar.comp ε₁bar = ε₁bar := by
    apply BialgHom.ext
    intro x
    show ε₁bar (ε₁bar x) = ε₁bar x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b =>
      show Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (ε 1 : H.level 1 →ₐ[O] H.level 1)
          (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (ε 1 : H.level 1 →ₐ[O] H.level 1) (a ⊗ₜ[O] b)) =
        Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (ε 1 : H.level 1 →ₐ[O] H.level 1) (a ⊗ₜ[O] b)
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      congr 1
      exact DFunLike.congr_fun (hε 1) b
    | add x y hx hy => rw [map_add, map_add, hx, hy]

  have hUpow : ∀ n : ℕ, (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (m w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) m →
          (((U ^ n) x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) m =
            H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
              ((PDivisibleGroup.Point.toAlgHom f).comp ((u w : H.level w →ₐ[O] H.level w) ^ n))))) := by
    intro n
    induction n with
    | zero =>
      intro x m w f hf
      rw [pow_zero]
      have h__af := hI5 x m w f hf
      simp only [pow_zero] at h__af
      exact h__af
    | succ n ih =>
      have := hI4 (fun w => (u w : H.level w →ₐ[O] H.level w)) (fun w => (u w : H.level w →ₐ[O] H.level w) ^ n) U (U ^ n) hU ih
      intro x m w f hf
      rw [pow_succ', Module.End.mul_eq_comp, this x m w f hf]
      rfl
  have hβ : ∀ n : ℕ, ∃ β : H.level 1 →ₐc[O] H.level 1,
      (ε 1 : H.level 1 →ₐ[O] H.level 1) = (β : H.level 1 →ₐ[O] H.level 1).comp ((u 1 : H.level 1 →ₐ[O] H.level 1) ^ n) := by
    intro n

    have hfac : eT = (U ^ n) ∘ₗ ((b ^ n * e : ↥Aadj) : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) := by
      have h1 : (⟨U, Algebra.self_mem_adjoin_singleton ℤ_[p] U⟩ * b) ^ n * e = e := by
        rw [hUb, ← pow_succ, he.pow_succ_eq]
      have h2 : e = ⟨U, Algebra.self_mem_adjoin_singleton ℤ_[p] U⟩ ^ n * (b ^ n * e) := by
        rw [← mul_assoc, ← mul_pow, h1]
      have h3 := congrArg (fun z : ↥Aadj => (z : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ))))) h2
      simp only [Subalgebra.coe_mul, Subalgebra.coe_pow] at h3
      rw [← Module.End.mul_eq_comp]
      exact h3
    obtain ⟨β, -, hβind⟩ := S42SLP.exists_bialgHom_family_of_mem_adjoin p P H S hS u hu U hU _ (b ^ n * e).2
    have hind := hI4 (fun w => (u w : H.level w →ₐ[O] H.level w) ^ n) (fun w => (β w : H.level w →ₐ[O] H.level w))
      (U ^ n) _ (hUpow n) hβind
    rw [← hfac] at hind
    have hL := S42SLP.level_eq_of_induced_eq p hinj H hlift' eT (fun w => (ε w : H.level w →ₐ[O] H.level w)) _ hεind hind
    exact ⟨β 1, hL 1⟩
  have hFVε : ∀ Fk : ZMod p ⊗[O] H.level 1 →ₐc[ZMod p] ZMod p ⊗[O] H.level 1, (∀ x, Fk x = x ^ p) →
      ∀ FD : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₐ[ZMod p] CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1),
        (∀ ψ, FD ψ = ψ ^ p) →
      ∃ (a b : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₐc[ZMod p] CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)),
        (CartierDual.map ε₁bar : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
            CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)) =
          (WithConv.toConv ((FD : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)) ∘ₗ
              (a : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p] CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1))) *
            WithConv.toConv ((b : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)) ∘ₗ
              (CartierDual.map Fk : CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1) →ₗ[ZMod p]
                CartierDual (ZMod p) (ZMod p ⊗[O] H.level 1)))).ofConv :=
    S42SLP.cartierDual_map_eq_convMul_of_factor p (u 1) (ε 1) hFV hβ
  obtain ⟨C, _, _, _, _, _, q, i, hqs, hqi, hiq, M, _, _, _, _, E, _, _, ΘC, hΘC, hEred, hMred⟩ :=
    HopfAlgebra.exists_split_idempotent_bijective_tensorProduct_isReduced_cartierDual_of_cartierDualMap_eq_frobenius_conv_verschiebung
      p (ZMod p ⊗[O] H.level 1) ε₁bar hε₁bar_idem hFVε
  have hord₁ : ∃ (M : Type) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
      (_ : Module.Free (ZMod p) M) (E : Type) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
      (Θ : ZMod p ⊗[O] H₁.level 1 →ₐc[ZMod p] M ⊗[ZMod p] E),
      Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M) := by
    obtain ⟨Θ₁, hΘ₁⟩ := S42SLP.exists_bijective_of_two_splittings p (ε 1) (π₁ 1) (σ₁ 1) (hπσ₁ 1) (hσπ₁ 1)
      q i hqi hiq ΘC hΘC
    exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, E, inferInstance, inferInstance, Θ₁, hΘ₁, hEred, hMred⟩
  obtain ⟨hs₁, hrank₁, hker₁⟩ :=
    PDivisibleGroup.surjective_and_finrank_and_ker_tensorProduct_map_transition p H₁ (ZMod p)
  have hord : ∀ v : ℕ, ∃ (M : Type) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
      (_ : Module.Free (ZMod p) M) (E : Type) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
      (Θ : ZMod p ⊗[O] H₁.level v →ₐc[ZMod p] M ⊗[ZMod p] E),
      Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M) :=
    PDivisibleGroup.forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_level_one_zmodp p h₁
      (fun v => ZMod p ⊗[O] H₁.level v)
      (fun v => Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (H₁.transition v)) hs₁ hrank₁ hker₁ hord₁

  obtain ⟨H₁', ⟨D₁⟩⟩ := PDivisibleGroup.exists_isCartierDual H₁
  have horth : ∀ (v : ℕ) (f : H₁.Point (AlgebraicClosure ℚ) v) (ψ : H₁'.Point (AlgebraicClosure ℚ) v),
      (∀ a : H₁.level v, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : H₁'.level v, P.valuation (PDivisibleGroup.Point.toAlgHom ψ a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      D₁.pair (AlgebraicClosure ℚ) v f ψ = 1 :=
    fun v f ψ hf hψ =>
      PDivisibleGroup.CartierDuality.pair_eq_one_of_forall_valuation_sub_counit_lt_one_of_bijective_tensorProduct_isReduced
        p P hOP hres H₁ H₁' D₁ v (hord v) f ψ hf hψ
  have hchi := fun τ τ' hττ' hτ x hx =>
    PDivisibleGroup.CartierDuality.tateModuleRep_eq_cyclotomicCharacter_smul_of_mem_inertiaSubgroupIn_of_forall_pair_eq_one
      p P hOP D₁ horth τ τ' hττ' hτ x hx

  obtain ⟨j, hjinj, hjrep, hjrange, hjgal, hjred⟩ :=
    PDivisibleGroup.exists_linearMap_tateModule_injective_of_surjective_comp_transition p P H H₁ π₁ hπ₁s hπ₁t

  obtain ⟨hcS, -⟩ := PDivisibleGroup.forall_mem_adjoin_tateModule_apply_mem_and_comp_tateModuleRep_eq p P H u U hU S hS
    (c : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) c.2
  obtain ⟨heS, -⟩ := PDivisibleGroup.forall_mem_adjoin_tateModule_apply_mem_and_comp_tateModuleRep_eq p P H u U hU S hS
    eT e.2
  obtain ⟨hUS, -⟩ := PDivisibleGroup.forall_mem_adjoin_tateModule_apply_mem_and_comp_tateModuleRep_eq p P H u U hU S hS
    (U ^ N) (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ_[p] U) N)
  refine ⟨N, fun y hy => ?_⟩
  have hyS : y ∈ S := (hS y).2 hy
  refine ⟨(c : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) y, (hS _).1 (hcS y hyS), ?_⟩
  intro τ τ' hττ' hτ

  have hkey : (U ^ N) y - (p : ℤ_[p]) • (c : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) y =
      eT ((U ^ N) y) := by
    have hcomm : eT * (U ^ N) = (U ^ N) * eT := by
      have := congrArg (fun z : ↥Aadj => (z : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))))
        (mul_comm e (⟨U, Algebra.self_mem_adjoin_singleton ℤ_[p] U⟩ ^ N))
      simp only [Subalgebra.coe_mul, Subalgebra.coe_pow] at this
      exact this
    have h2 := congrArg (fun z : ↥Aadj => (z : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) y) hc
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, AddSubgroupClass.coe_sub,
      Subalgebra.coe_one, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub] at h2
    have hcast : ((p : ↥Aadj) : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) =
        (p : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) := map_natCast Aadj.val p
    simp only [hcast, Module.End.natCast_apply, map_nsmul] at h2

    have h3 : (U ^ N) (eT y) = eT ((U ^ N) y) := by
      rw [← Module.End.mul_apply, ← hcomm, Module.End.mul_apply]
    rw [h3] at h2
    have h4 : (p : ℤ_[p]) • (c : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) y =
        (U ^ N) y - eT ((U ^ N) y) := by
      rw [← h2, Nat.cast_smul_eq_nsmul]
    rw [h4, sub_sub_cancel]

  have hmS : eT ((U ^ N) y) ∈ S := heS _ (hUS _ hyS)
  have hm_range : eT ((U ^ N) y) ∈ LinearMap.range j := by
    rw [hjrange]
    intro n
    obtain ⟨w, f, hf⟩ := PDivisibleGroup.Points.exists_mkAdd H
      ((((U ^ N) y : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n)
    refine ⟨w, PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom f).comp (ε w : H.level w →ₐ[O] H.level w)),
      (hεind _ n w f hf).symm, ?_⟩
    intro a ha
    rw [PDivisibleGroup.Point.toAlgHom_ofAlgHom, AlgHom.comp_apply]
    have : (ε w : H.level w →ₐ[O] H.level w) a = σ₁ w (π₁ w a) := by
      rw [← hσπ₁ w]; rfl
    rw [this, show (π₁ w) a = ((π₁ w : H.level w →ₐ[O] H₁.level w)) a from rfl]
    rw [show ((π₁ w : H.level w →ₐ[O] H₁.level w)) a = π₁ w a from rfl, ha, map_zero, map_zero]
  obtain ⟨x₁, hx₁⟩ := hm_range
  have hx₁red := (hjred x₁).1 (by rw [hx₁]; exact (hS _).1 hmS)
  have hχ := hchi τ τ' hττ' hτ x₁ hx₁red
  rw [hkey, ← hx₁, ← LinearMap.comp_apply, ← hjgal τ', LinearMap.comp_apply, hχ, map_smul]

end S_PDivisibleGroup_exists_rep_pow_sub_smul_eq_cyclotomicCharacter_smul_of_reduction_pow_eq_frobenius_conv_verschiebung
end P2MW
export P2MW.S_PDivisibleGroup_exists_rep_pow_sub_smul_eq_cyclotomicCharacter_smul_of_reduction_pow_eq_frobenius_conv_verschiebung (solution)

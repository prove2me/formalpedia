-- Prove2me | solution 1 for PDivisibleGroup.exists_point_toAlgHom_eq_comp_of_etale_cartierDual_of_forall_comp_eq_of_reduction_pow_eq_frobenius_conv_verschiebung
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/dff218c6-d250-51b0-b616-1dc3aa312b18

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CharacterClosure
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_comp_eq_id_comp_eq_of_comp_eq_self_of_isLocalRing
import Theorems.Thm_PDivisibleGroup_forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_comp_eq_idempotent_of_reduction_pow_eq_frobenius_conv_verschiebung
import Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_isLocalRing_tensorProduct_forall_point_comp_eq_of_henselianLocalRing
import Theorems.Thm_HopfAlgebra_isReduced_cartierDual_of_surjective_of_isLocalRing_of_bijective_tensorProduct_isReduced
import Theorems.Thm_Algebra_Etale_of_formallyUnramified_residueField_baseChange
import Theorems.Thm_CartierDual_dualBaseChangeLin_bijective_integral
import Theorems.Thm_Algebra_Etale_of_isReduced_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_point_toAlgHom_eq_comp_of_etale_cartierDual_of_forall_comp_eq_of_reduction_pow_eq_frobenius_conv_verschiebung
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient Deformation.TruncWitt.instSubsingleton Deformation.DieudonneModule.instInhabited Deformation.wittHomShiftLE_directedSystem Deformation.DieudonneModule.instAddCommGroup HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec Deformation.wittHomDieudonneDatum_F_apply Deformation.TruncWitt.shift_truncate Deformation.coe_wittHomShift Deformation.coe_wittHomFrobenius Deformation.wittHomDieudonneDatum_V_apply Deformation.TruncWitt.coeff_map Deformation.coe_wittHomVerschiebung Deformation.coe_wittHomRestrict Deformation.coe_wittHomMap Deformation.TruncWitt.map_truncate Deformation.TruncWitt.coeff_frobeniusFun Deformation.TruncWitt.verschiebung_truncate Deformation.TruncWitt.map_id"
p2m_attr_erase "simp" "Deformation.TruncWitt.shiftLE_refl Deformation.DieudonneModule.dieudonneDatum_F_apply Deformation.coe_wittHomShiftLE Deformation.DieudonneModule.frobenius_of Deformation.DieudonneModule.lift_of Deformation.TruncWitt.verschiebungIter_apply Deformation.DieudonneModule.map_of Deformation.DieudonneModule.dieudonneDatum_V_apply Deformation.DieudonneModule.of_shift Deformation.TruncWitt.shiftLE_truncate Deformation.DieudonneModule.verschiebung_of Deformation.DieudonneModule.of_shiftLE Deformation.wittHomShiftLE_refl HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

namespace OrdFinAux

theorem ker_algebraMap_zmod_eq_maximalIdeal (p : ℕ) [Fact p.Prime]
    (O : Type) [CommRing O] [IsLocalRing O] [Algebra O (ZMod p)] :
    RingHom.ker (algebraMap O (ZMod p)) = IsLocalRing.maximalIdeal O := by
  have hs : Function.Surjective (algebraMap O (ZMod p)) := ZMod.ringHom_surjective _
  have hm : (RingHom.ker (algebraMap O (ZMod p))).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ hs
  exact IsLocalRing.eq_maximalIdeal hm

noncomputable def residueEquiv (p : ℕ) [Fact p.Prime]
    (O : Type) [CommRing O] [IsLocalRing O] [Algebra O (ZMod p)] :
    IsLocalRing.ResidueField O ≃ₐ[O] ZMod p :=
  (Ideal.quotientEquivAlgOfEq O (ker_algebraMap_zmod_eq_maximalIdeal p O).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId O (ZMod p)) (ZMod.ringHom_surjective _))

theorem formallyUnramified_residueField_tensor (p : ℕ) [Fact p.Prime]
    (O : Type) [CommRing O] [IsLocalRing O] [Algebra O (ZMod p)]
    (D : Type) [CommRing D] [Algebra O D]
    (h : Algebra.FormallyUnramified (ZMod p) (ZMod p ⊗[O] D)) :
    Algebra.FormallyUnramified (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] D) := by

  haveI : Algebra.FormallyUnramified O (ZMod p) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId O (ZMod p)) (ZMod.ringHom_surjective (algebraMap O (ZMod p)))
  haveI : Algebra.FormallyUnramified O (ZMod p ⊗[O] D) := Algebra.FormallyUnramified.comp O (ZMod p) _

  let e : IsLocalRing.ResidueField O ⊗[O] D ≃ₐ[O] ZMod p ⊗[O] D :=
    Algebra.TensorProduct.congr (residueEquiv p O) AlgEquiv.refl
  haveI : Algebra.FormallyUnramified O (IsLocalRing.ResidueField O ⊗[O] D) :=
    Algebra.FormallyUnramified.of_equiv e.symm
  exact Algebra.FormallyUnramified.of_restrictScalars O _ _

end OrdFinAux

theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsDomain O] [HenselianLocalRing O]
    [Algebra O (AlgebraicClosure ℚ)] [Algebra O (ZMod p)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (hres : ∀ x : O, algebraMap O (ZMod p) x = 0 ↔
      P.valuation (algebraMap O (AlgebraicClosure ℚ) x) < 1)
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
    (v : ℕ)

    (Mt : Type) [CommRing Mt] [HopfAlgebra O Mt] [Coalgebra.IsCocomm O Mt] [Module.Free O Mt] [Module.Finite O Mt]
    [Algebra.Etale O (CartierDual O Mt)]
    (π : H.level v →ₐc[O] Mt) (hπ : Function.Surjective π)
    (huniv : ∀ (M' : Type) [CommRing M'] [HopfAlgebra O M'] [Coalgebra.IsCocomm O M']
        [Module.Free O M'] [Module.Finite O M'] [Algebra.Etale O (CartierDual O M')]
        (f : H.level v →ₐc[O] M'), ∃! g : Mt →ₐc[O] M', g.comp π = f) :
    ∀ f : H.Point (AlgebraicClosure ℚ) v,
      (∀ a : H.level v, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
          algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (PDivisibleGroup.Point.toAlgHom f).comp (ε v : H.level v →ₐ[O] H.level v) =
        PDivisibleGroup.Point.toAlgHom f →
      ∃ g : Mt →ₐ[O] AlgebraicClosure ℚ,
        PDivisibleGroup.Point.toAlgHom f = g.comp (π : H.level v →ₐ[O] Mt) := by
  classical
  intro f hf hfε
  haveI : IsLocalRing O := inferInstance

  obtain ⟨C, _, _, _, _, _, q, i, hq, hqi, hiq⟩ :=
    HopfAlgebra.exists_bialgHom_surjective_comp_eq_id_comp_eq_of_comp_eq_self_of_isLocalRing
      O (H.level v) (ε v) (hεε v)

  set f₁ : C →ₐ[O] AlgebraicClosure ℚ := (PDivisibleGroup.Point.toAlgHom f).comp (i : C →ₐ[O] H.level v)
    with hf₁
  have hff₁ : PDivisibleGroup.Point.toAlgHom f = f₁.comp (q : H.level v →ₐ[O] C) := by
    rw [hf₁, AlgHom.comp_assoc]
    have : (i : C →ₐ[O] H.level v).comp (q : H.level v →ₐ[O] C) = (ε v : H.level v →ₐ[O] H.level v) := by
      apply AlgHom.ext
      intro x
      exact DFunLike.congr_fun hiq x
    rw [this, hfε]

  have hf₁formal : ∀ c : C, P.valuation (f₁ c - algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit c)) < 1 := by
    intro c
    have hc : Coalgebra.counit (R := O) (i c) = Coalgebra.counit (R := O) c :=
      LinearMap.congr_fun i.counit_comp c
    have := hf (i c)
    rw [hc] at this
    simpa [hf₁] using this

  have hker := OrdFinAux.ker_algebraMap_zmod_eq_maximalIdeal p O
  have hres' : ∀ x : O, algebraMap O (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal O := by
    intro x; rw [← hker, RingHom.mem_ker]
  have hloc : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O →
      P.valuation (algebraMap O (AlgebraicClosure ℚ) x) < 1 := by
    intro x hx; exact (hres x).1 ((hres' x).2 hx)

  obtain ⟨C₀, _, _, _, _, _, q₀, hq₀, hC₀loc, hfac, -, -⟩ :=
    HopfAlgebra.exists_bialgHom_surjective_isLocalRing_tensorProduct_forall_point_comp_eq_of_henselianLocalRing
      p O P hOP hloc hres' C
  obtain ⟨g₁, hg₁⟩ := hfac f₁ hf₁formal

  let qb := Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) q
  let ib := Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) i
  have hqb : Function.Surjective qb := by
    show Function.Surjective (TensorProduct.map LinearMap.id (q : H.level v →ₐ[O] C).toLinearMap)
    exact TensorProduct.map_surjective Function.surjective_id hq
  have hqbib : qb.comp ib = BialgHom.id (ZMod p) (ZMod p ⊗[O] C) := by
    refine BialgHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
        show qb (ib (c ⊗ₜ[O] a)) = c ⊗ₜ[O] a
        rw [Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply,
          BialgHom.id_apply]
        exact congrArg (fun y => c ⊗ₜ[O] y) (DFunLike.congr_fun hqi a)
    | add x y hx hy =>
        show qb (ib (x + y)) = x + y
        rw [map_add, map_add]
        exact congrArg₂ (· + ·) hx hy
  have hibqb : ib.comp qb = Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v) := by
    refine BialgHom.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
        show ib (qb (c ⊗ₜ[O] a)) = Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v) (c ⊗ₜ[O] a)
        rw [Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul,
          BialgHom.id_apply, BialgHom.id_apply]
        exact congrArg (fun y => c ⊗ₜ[O] y) (DFunLike.congr_fun hiq a)
    | add x y hx hy =>
        show ib (qb (x + y)) = Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v) (x + y)
        rw [map_add, map_add, map_add]
        exact congrArg₂ (· + ·) hx hy
  obtain ⟨M, _, _, _, _, E, _, _, Θ, hΘ, hE, hM⟩ :=
    PDivisibleGroup.forall_exists_bijective_tensorProduct_isReduced_cartierDual_of_comp_eq_idempotent_of_reduction_pow_eq_frobenius_conv_verschiebung
      p H u ε w hu hεε hεtr hεu hwtr hεw hwε hwuε huεw hFV v (ZMod p ⊗[O] C) qb ib hqb hqbib hibqb

  have hred : IsReduced (CartierDual (ZMod p) (ZMod p ⊗[O] C₀)) :=
    HopfAlgebra.isReduced_cartierDual_of_surjective_of_isLocalRing_of_bijective_tensorProduct_isReduced
      p (ZMod p ⊗[O] C) M E Θ hΘ hE hM (ZMod p ⊗[O] C₀)
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) q₀)
      (by
        show Function.Surjective (TensorProduct.map LinearMap.id (q₀ : C →ₐ[O] C₀).toLinearMap)
        exact TensorProduct.map_surjective Function.surjective_id hq₀)
      hC₀loc

  have hEt : Algebra.Etale O (CartierDual O C₀) := by

    haveI : IsReduced (CartierDual (ZMod p) (ZMod p ⊗[O] C₀)) := hred
    haveI : Algebra.Etale (ZMod p) (CartierDual (ZMod p) (ZMod p ⊗[O] C₀)) :=
      Algebra.Etale.of_isReduced_of_perfectField (ZMod p) _
    obtain ⟨hbij, h1, hmul, -, -⟩ := CartierDual.dualBaseChangeLin_bijective_integral O (ZMod p) C₀
    let β : ZMod p ⊗[O] CartierDual O C₀ →ₐ[ZMod p] CartierDual (ZMod p) (ZMod p ⊗[O] C₀) :=
      AlgHom.ofLinearMap (CartierDual.dualBaseChangeLin O (ZMod p) C₀) h1 hmul
    let βe := AlgEquiv.ofBijective β hbij
    haveI : Algebra.FormallyUnramified (ZMod p) (ZMod p ⊗[O] CartierDual O C₀) :=
      Algebra.FormallyUnramified.of_equiv βe.symm
    exact Algebra.Etale.of_formallyUnramified_residueField_baseChange O (CartierDual O C₀)
      (OrdFinAux.formallyUnramified_residueField_tensor p O (CartierDual O C₀) inferInstance)

  haveI := hEt
  obtain ⟨g₀, hg₀, -⟩ := huniv C₀ (q₀.comp q)
  refine ⟨g₁.comp (g₀ : Mt →ₐ[O] C₀), ?_⟩
  rw [hff₁, hg₁, AlgHom.comp_assoc, AlgHom.comp_assoc]
  congr 1
  apply AlgHom.ext
  intro x
  exact (DFunLike.congr_fun hg₀ x).symm

end S_PDivisibleGroup_exists_point_toAlgHom_eq_comp_of_etale_cartierDual_of_forall_comp_eq_of_reduction_pow_eq_frobenius_conv_verschiebung
end P2MW
export P2MW.S_PDivisibleGroup_exists_point_toAlgHom_eq_comp_of_etale_cartierDual_of_forall_comp_eq_of_reduction_pow_eq_frobenius_conv_verschiebung (solution)

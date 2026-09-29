-- Prove2me | solution 1 for PDivisibleGroup.Tower.forall_isReduced_cartierDual_of_isReduced_cartierDual_one_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9a434752-e726-568a-b1cd-e908a851ed18

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal
import Theorems.Thm_PDivisibleGroup_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal
import Theorems.Thm_HopfAlgebra_isReduced_cartierDual_of_injective_of_surjective_of_ker_eq_map_zmodp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_Tower_forall_isReduced_cartierDual_of_isReduced_cartierDual_one_zmodp
p2m_attr_erase "instance" "PDivisibleGroup.Points.instAddCommGroup PDivisibleGroup.Points.instInhabited PDivisibleGroup.Point.instCommGroup PDivisibleGroup.pointsDirectedSystem PDivisibleGroup.Points.instDistribMulAction PDivisibleGroup.Point.instCommMonoid TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite HopfAlgebra.IsHopfTower.refl HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply PDivisibleGroup.Points.smul_pointsMkAdd PDivisibleGroup.pointsMkAdd_pointInclLE PDivisibleGroup.Point.toAlgHom_ofAlgHom PDivisibleGroup.pointsMkAdd_pointIncl PDivisibleGroup.pointsMk_pointInclLE PDivisibleGroup.pointIncl_apply PDivisibleGroup.pointInclLE_self PDivisibleGroup.toAlgHom_pointMap PDivisibleGroup.Point.toConv_ofConv PDivisibleGroup.Hopf.antipodeAlgHom_apply PDivisibleGroup.Hopf.convCompMonoidHom_apply PDivisibleGroup.pointsMap_pointsMkAdd PDivisibleGroup.Point.ofAlgHom_toAlgHom PDivisibleGroup.pointsMk_pointIncl PDivisibleGroup.Point.ofConv_toConv TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq"
p2m_attr_erase "simp" "ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u v w

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "Hopf.nsmulAlgHom Hopf.augIdeal Hopf.mem_augIdeal_iff Hopf.torsionIdeal level Hopf.exists_forall_comp_transition_surjective_ker_eq_torsionIdeal exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal"
namespace Hopf
p2m_export "PDivisibleGroup.Hopf" "nsmulAlgHom nsmulAlgHom_one nsmulAlgHom_succ augIdeal mem_augIdeal_iff torsionIdeal exists_forall_comp_transition_surjective_ker_eq_torsionIdeal"
namespace MultTower
p2m_open "PDivisibleGroup.Hopf PDivisibleGroup"

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Bialgebra R A] [Coalgebra.IsCocomm R A]

theorem exists_bialgHom_coe_eq_nsmulAlgHom (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : A →ₐc[R] A, (f : A →ₐ[R] A) = nsmulAlgHom R A n := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨BialgHom.id R A, by rw [nsmulAlgHom_one]; rfl⟩
  | succ n hn ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨(Bialgebra.mulBialgHom R A).comp
      ((Bialgebra.TensorProduct.map f (BialgHom.id R A)).comp (Bialgebra.comulBialgHom R A)), ?_⟩
    refine AlgHom.ext fun a => ?_
    rw [nsmulAlgHom_succ, ← hf]
    change Bialgebra.mulBialgHom R A (Bialgebra.TensorProduct.map f (BialgHom.id R A)
      (Coalgebra.comul (R := R) a)) = (WithConv.toConv (f : A →ₐ[R] A) * WithConv.toConv (AlgHom.id R A)) a
    rw [AlgHom.convMul_apply]
    induction Coalgebra.comul (R := R) a using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      rw [Bialgebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

end PDivisibleGroup.Hopf.MultTower

theorem solution
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra (ZMod p) (L v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (L v)] [∀ v, Module.Finite (ZMod p) (L v)]
    (t : ∀ v, L (v + 1) →ₐc[ZMod p] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank (ZMod p) (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (L (v + 1)) (p ^ v))
    (hred₁ : IsReduced (CartierDual (ZMod p) (L 1))) :
    ∀ v : ℕ, IsReduced (CartierDual (ZMod p) (L v)) := by
  classical
  haveI : ∀ v, Module.Free (ZMod p) (L v) := fun v => inferInstance
  have hp : p.Prime := Fact.out

  obtain ⟨T, -, -, hTsurj, hTker, -, -⟩ :=
    PDivisibleGroup.Hopf.exists_forall_comp_transition_surjective_ker_eq_torsionIdeal p h L t ht hrankL hkerL
  have hTQ : ∀ v, ∃ π : L (v + 1) →ₐc[ZMod p] L 1, Function.Surjective π ∧
      RingHom.ker π = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (L (v + 1)) (p ^ 1) := by
    intro v
    have aux : ∀ n m : ℕ, n = m →
        (∃ π : L n →ₐc[ZMod p] L 1, Function.Surjective π ∧
          RingHom.ker π = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (L n) (p ^ 1)) →
        (∃ π : L m →ₐc[ZMod p] L 1, Function.Surjective π ∧
          RingHom.ker π = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (L m) (p ^ 1)) := by
      rintro n m rfl hh; exact hh
    exact aux (1 + v) (v + 1) (Nat.add_comm 1 v) ⟨T 1 v, hTsurj 1 v, hTker 1 v⟩

  have h0 : IsReduced (CartierDual (ZMod p) (L 0)) := by
    have hr : Module.finrank (ZMod p) (CartierDual (ZMod p) (L 0)) = 1 := by
      rw [LinearEquiv.finrank_eq (CartierDual.toDual (ZMod p) (L 0)), Subspace.dual_finrank_eq, hrankL 0, zero_mul,
        pow_zero]
    haveI : Module.Finite (ZMod p) (CartierDual (ZMod p) (L 0)) := Module.finite_of_finrank_eq_succ hr
    have hnt : Nontrivial (CartierDual (ZMod p) (L 0)) := Module.nontrivial_of_finrank_eq_succ hr
    have h1 : (1 : CartierDual (ZMod p) (L 0)) ≠ 0 := one_ne_zero
    refine ⟨fun x hx => ?_⟩
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : CartierDual (ZMod p) (L 0)) h1).1 hr x
    obtain ⟨n, hn⟩ := hx
    rw [← hc] at hn ⊢
    rw [smul_pow, one_pow, smul_eq_zero] at hn
    rcases hn with hcn | h10
    · rw [pow_eq_zero_iff'] at hcn
      rw [hcn.1, zero_smul]
    · exact absurd h10 h1

  intro v
  induction v with
  | zero => exact h0
  | succ v ih =>

    obtain ⟨⟨e, he⟩, -⟩ := PDivisibleGroup.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal
      (ZMod p) p h L t ht hrankL hkerL v
    obtain ⟨np, hnp⟩ := PDivisibleGroup.Hopf.MultTower.exists_bialgHom_coe_eq_nsmulAlgHom (ZMod p) (L (v + 1)) p hp.one_lt.le
    let jalg : L v →ₐ[ZMod p] L (v + 1) :=
      (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (L (v + 1)) p).range.val.comp (e : L v →ₐ[ZMod p] _)
    have hjt : ∀ b : L (v + 1), jalg (t v b) = np b := fun b => by
      change ((e (t v b) : ↥(PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (L (v + 1)) p).range) : L (v + 1)) = np b
      rw [he b, ← hnp]
      rfl
    have hjinj : Function.Injective jalg := Subtype.val_injective.comp e.injective
    have hnpb : ∀ b : L (v + 1), np b = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (L (v + 1)) p b := fun b =>
      AlgHom.congr_fun hnp b

    have hcounit : (Bialgebra.counitAlgHom (ZMod p) (L (v + 1))).comp jalg = Bialgebra.counitAlgHom (ZMod p) (L v) := by
      refine AlgHom.ext fun a => ?_
      obtain ⟨b, rfl⟩ := ht v a
      rw [AlgHom.comp_apply, hjt, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
        CoalgHomClass.counit_comp_apply np b, CoalgHomClass.counit_comp_apply (t v) b]
    have hcomul : (Algebra.TensorProduct.map jalg jalg).comp (Bialgebra.comulAlgHom (ZMod p) (L v)) =
        (Bialgebra.comulAlgHom (ZMod p) (L (v + 1))).comp jalg := by
      refine AlgHom.ext fun a => ?_
      obtain ⟨b, rfl⟩ := ht v a
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply, hjt,
        ← CoalgHomClass.map_comp_comul_apply np b, ← CoalgHomClass.map_comp_comul_apply (t v) b]
      induction Coalgebra.comul (R := ZMod p) b using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul x y =>
        rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
        change Algebra.TensorProduct.map jalg jalg (t v x ⊗ₜ[ZMod p] t v y) = np x ⊗ₜ[ZMod p] np y
        rw [Algebra.TensorProduct.map_tmul, hjt, hjt]
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    let j : L v →ₐc[ZMod p] L (v + 1) := BialgHom.ofAlgHom jalg hcounit hcomul
    have hjcoe : (j : L v →ₐ[ZMod p] L (v + 1)) = jalg := rfl

    obtain ⟨π, hπ, hkerπ⟩ := hTQ v
    have hex : RingHom.ker (π : L (v + 1) →ₐ[ZMod p] L 1) =
        Ideal.map (j : L v →ₐ[ZMod p] L (v + 1)) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (L v))) := by
      rw [hjcoe]
      change RingHom.ker π = _
      rw [hkerπ, pow_one, PDivisibleGroup.Hopf.torsionIdeal]
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro b hb
        rw [Ideal.mem_comap]
        have htb : t v b ∈ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (L v)) := by
          rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply, CoalgHomClass.counit_comp_apply (t v) b]
          exact (PDivisibleGroup.Hopf.mem_augIdeal_iff _ _ b).1 hb
        have : jalg (t v b) ∈ Ideal.map jalg (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (L v))) :=
          Ideal.mem_map_of_mem _ htb
        rw [hjt, hnpb] at this
        exact this
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap]
        obtain ⟨b, rfl⟩ := ht v a
        have hb' : b - algebraMap (ZMod p) (L (v + 1)) (Coalgebra.counit (R := ZMod p) b) ∈
            PDivisibleGroup.Hopf.augIdeal (ZMod p) (L (v + 1)) := by
          rw [PDivisibleGroup.Hopf.mem_augIdeal_iff, map_sub, Bialgebra.counit_algebraMap, sub_self]
        have htb : t v b = t v (b - algebraMap (ZMod p) (L (v + 1)) (Coalgebra.counit (R := ZMod p) b)) := by
          rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply, CoalgHomClass.counit_comp_apply (t v) b] at ha
          rw [ha, map_zero, sub_zero]
        rw [htb, hjt, hnpb]
        exact Ideal.mem_map_of_mem _ hb'
    have hrank : Module.finrank (ZMod p) (L (v + 1)) = Module.finrank (ZMod p) (L v) * Module.finrank (ZMod p) (L 1) := by
      rw [hrankL, hrankL, hrankL, one_mul, ← pow_add, Nat.succ_mul]
    exact HopfAlgebra.isReduced_cartierDual_of_injective_of_surjective_of_ker_eq_map_zmodp p j hjinj π hπ hex hrank ih
      hred₁

end S_PDivisibleGroup_Tower_forall_isReduced_cartierDual_of_isReduced_cartierDual_one_zmodp
end P2MW
export P2MW.S_PDivisibleGroup_Tower_forall_isReduced_cartierDual_of_isReduced_cartierDual_one_zmodp (solution)

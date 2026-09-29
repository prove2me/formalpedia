-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.pair_eq_one_of_forall_valuation_sub_counit_lt_one_of_bijective_tensorProduct_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d1f98fed-1d48-5e1c-8b2b-c6d745156ff3

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_PDivisibleGroup_CartierDuality
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_henselianLocalRing
import Theorems.Thm_HopfAlgebra_exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring
import Theorems.Thm_HopfAlgebra_apply_ofDual_eq_one_of_eq_comp_of_forall_sub_apply_one_mem_maximalIdeal_of_henselianLocalRing
import Theorems.Thm_CartierDual_exists_bialgEquiv_baseChange_forall_pairing_symm_tmul
import Theorems.Thm_HopfAlgebra_exists_bijective_tensorProduct_isReduced_cartierDual_residueField_of_zmodp_valuationSubring_of_isCocomm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_pair_eq_one_of_forall_valuation_sub_counit_lt_one_of_bijective_tensorProduct_isReduced
p2m_attr_erase "instance" "HopfAlgebra.IsHopfTower.refl HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0"
p2m_attr_erase "simp" "TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u v w

noncomputable section

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "Point Point.toAlgHom height finrank_level level CartierDuality CartierDuality.toDualEquiv_symm_apply CartierDuality.pair_def"
namespace S6aMain
p2m_open "PDivisibleGroup"

section Frame

variable {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
  (P : ValuationSubring (AlgebraicClosure ℚ)) (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)

def toP : O →+* P := (algebraMap O (AlgebraicClosure ℚ)).codRestrict P.toSubring hOP

theorem coe_toP (x : O) : ((toP P hOP x : P) : AlgebraicClosure ℚ) = algebraMap O (AlgebraicClosure ℚ) x := rfl

abbrev algebraOP : Algebra O P := (toP P hOP).toAlgebra

theorem isScalarTower : letI := algebraOP P hOP; IsScalarTower O P (AlgebraicClosure ℚ) :=
  letI := algebraOP P hOP
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable {P}

theorem mem_maximalIdeal_iff (x : P) :
    x ∈ IsLocalRing.maximalIdeal P ↔ P.valuation (x : AlgebraicClosure ℚ) < 1 :=
  ValuationSubring.valuation_lt_one_iff P x

include hOP in

theorem mem_of_isIntegral {x : AlgebraicClosure ℚ} (hx : IsIntegral O x) : x ∈ P := by
  letI := algebraOP P hOP
  haveI := isScalarTower P hOP
  have hx' : IsIntegral P x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := P) (K := AlgebraicClosure ℚ)).mp hx'
  rw [← hy]
  exact y.2

variable {A : Type*} [CommRing A]

section Alg

variable [Algebra O A] [Module.Finite O A]

include hOP in

theorem apply_mem (f : A →ₐ[O] AlgebraicClosure ℚ) (a : A) : f a ∈ P :=
  mem_of_isIntegral hOP ((Algebra.IsIntegral.isIntegral (R := O) a).map f)

def ptP (f : A →ₐ[O] AlgebraicClosure ℚ) : letI := algebraOP P hOP; A →ₐ[O] P :=
  letI := algebraOP P hOP
  { toFun := fun a => ⟨f a, apply_mem hOP f a⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' := fun a b => Subtype.ext (map_mul f a b)
    map_zero' := Subtype.ext (map_zero f)
    map_add' := fun a b => Subtype.ext (map_add f a b)
    commutes' := fun r => Subtype.ext (f.commutes r) }

theorem coe_ptP_apply (f : A →ₐ[O] AlgebraicClosure ℚ) (a : A) :
    letI := algebraOP P hOP; ((ptP hOP f a : P) : AlgebraicClosure ℚ) = f a := by
  rfl

def bcPt (f : A →ₐ[O] AlgebraicClosure ℚ) : letI := algebraOP P hOP; P ⊗[O] A →ₐ[P] P :=
  letI := algebraOP P hOP
  Algebra.TensorProduct.lift (AlgHom.id P P) (ptP hOP f) (fun _ _ => Commute.all _ _)

omit [Module.Finite O A] in
theorem bcPt_tmul [Module.Finite O A] (f : A →ₐ[O] AlgebraicClosure ℚ) (s : P) (a : A) :
    letI := algebraOP P hOP; bcPt hOP f (s ⊗ₜ[O] a) = s * ptP hOP f a := by
  letI := algebraOP P hOP
  show Algebra.TensorProduct.lift (AlgHom.id P P) (ptP hOP f) (fun _ _ => Commute.all _ _) (s ⊗ₜ[O] a) = _
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply]

end Alg

section Bialg

variable [Bialgebra O A] [Module.Finite O A]

theorem bcPt_sub_counit_mem (f : A →ₐ[O] AlgebraicClosure ℚ)
    (hf : ∀ a : A, P.valuation (f a - algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit (R := O) a)) < 1) :
    letI := algebraOP P hOP
    ∀ x : P ⊗[O] A, bcPt hOP f x - Coalgebra.counit (R := P) x ∈ IsLocalRing.maximalIdeal P := by
  letI := algebraOP P hOP
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, sub_zero]; exact Ideal.zero_mem _
  | tmul s a =>
    rw [bcPt_tmul, TensorProduct.counit_tmul]
    have h1 : Coalgebra.counit (R := P) s = s := rfl
    rw [h1, Algebra.smul_def, mul_comm (algebraMap O P _) s, ← mul_sub]
    refine Ideal.mul_mem_left _ s ((mem_maximalIdeal_iff _).mpr ?_)
    exact hf a
  | add x y hx hy =>
    rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hx hy

end Bialg

end Frame

section DualPoint

variable {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
  {P : ValuationSubring (AlgebraicClosure ℚ)} (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
  {p h : ℕ} {H H' : PDivisibleGroup O p h} (D : H.CartierDuality H') (v : ℕ)

def idEquiv : letI := algebraOP P hOP; P ⊗[O] CartierDual O (H.level v) ≃ₐ[P] P ⊗[O] H'.level v :=
  letI := algebraOP P hOP
  Algebra.TensorProduct.congr (AlgEquiv.refl : P ≃ₐ[P] P) ((D.equiv v).toAlgEquiv.symm)

theorem idEquiv_tmul (s : P) (φ : CartierDual O (H.level v)) :
    letI := algebraOP P hOP; idEquiv hOP D v (s ⊗ₜ[O] φ) = s ⊗ₜ[O] (D.equiv v).symm φ := by
  letI := algebraOP P hOP
  show Algebra.TensorProduct.congr (AlgEquiv.refl : P ≃ₐ[P] P) ((D.equiv v).toAlgEquiv.symm) (s ⊗ₜ[O] φ) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  rfl

theorem counit_idEquiv (z : letI := algebraOP P hOP; P ⊗[O] CartierDual O (H.level v)) :
    letI := algebraOP P hOP
    Coalgebra.counit (R := P) (idEquiv hOP D v z) = Coalgebra.counit (R := P) z := by
  letI := algebraOP P hOP
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul s φ =>
    rw [idEquiv_tmul, TensorProduct.counit_tmul, TensorProduct.counit_tmul]
    congr 1
    exact CoalgHomClass.counit_comp_apply (D.equiv v).symm φ
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

def psiP (ψ : H'.level v →ₐ[O] AlgebraicClosure ℚ)
    (e : letI := algebraOP P hOP; CartierDual P (P ⊗[O] H.level v) ≃ₐc[P] P ⊗[O] CartierDual O (H.level v)) :
    letI := algebraOP P hOP; CartierDual P (P ⊗[O] H.level v) →ₐ[P] P :=
  letI := algebraOP P hOP
  ((bcPt hOP ψ).comp (idEquiv hOP D v).toAlgHom).comp (e.toAlgEquiv : CartierDual P (P ⊗[O] H.level v) →ₐ[P] _)

theorem psiP_apply (ψ : H'.level v →ₐ[O] AlgebraicClosure ℚ)
    (e : letI := algebraOP P hOP; CartierDual P (P ⊗[O] H.level v) ≃ₐc[P] P ⊗[O] CartierDual O (H.level v))
    (lam : letI := algebraOP P hOP; CartierDual P (P ⊗[O] H.level v)) :
    letI := algebraOP P hOP; psiP hOP D v ψ e lam = bcPt hOP ψ (idEquiv hOP D v (e lam)) := rfl

theorem psiP_sub_apply_one_mem (ψ : H'.level v →ₐ[O] AlgebraicClosure ℚ)
    (hψ : ∀ a : H'.level v, P.valuation (ψ a - algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit (R := O) a)) < 1)
    (e : letI := algebraOP P hOP; CartierDual P (P ⊗[O] H.level v) ≃ₐc[P] P ⊗[O] CartierDual O (H.level v)) :
    letI := algebraOP P hOP
    ∀ lam : CartierDual P (P ⊗[O] H.level v), psiP hOP D v ψ e lam - lam 1 ∈ IsLocalRing.maximalIdeal P := by
  letI := algebraOP P hOP
  intro lam
  have hce : Coalgebra.counit (R := P) (e lam) = Coalgebra.counit (R := P) lam := CoalgHomClass.counit_comp_apply e lam
  have h1 : lam 1 = Coalgebra.counit (R := P) (idEquiv hOP D v (e lam)) := by
    rw [counit_idEquiv, hce, CartierDual.counit_apply]
  rw [psiP_apply, h1]
  exact bcPt_sub_counit_mem hOP ψ hψ _

theorem e_ofDual_bcPt (f : H.level v →ₐ[O] AlgebraicClosure ℚ)
    (e : letI := algebraOP P hOP; CartierDual P (P ⊗[O] H.level v) ≃ₐc[P] P ⊗[O] CartierDual O (H.level v))
    (he : letI := algebraOP P hOP; ∀ (s t : P) (φ : CartierDual O (H.level v)) (a : H.level v),
        CartierDual.pairing P (P ⊗[O] H.level v) (e.symm (s ⊗ₜ[O] φ)) (t ⊗ₜ[O] a) =
          s * t * algebraMap O P (CartierDual.pairing O (H.level v) φ a)) :
    letI := algebraOP P hOP
    e ((CartierDual.ofDual P (P ⊗[O] H.level v)) (bcPt hOP f).toLinearMap) =
      ∑ i, ptP hOP f (Module.Free.chooseBasis O (H.level v) i) ⊗ₜ[O]
        CartierDual.ofDual O (H.level v) ((Module.Free.chooseBasis O (H.level v)).coord i) := by
  letI := algebraOP P hOP
  apply EquivLike.injective e.symm
  rw [e.symm_apply_apply]
  refine CartierDual.ext fun x => ?_

  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul t a =>
    rw [CartierDual.ofDual_apply, AlgHom.toLinearMap_apply, bcPt_tmul, map_sum, ← CartierDual.toDual_apply (R := P),
      map_sum, LinearMap.sum_apply]
    have hterm : ∀ i, CartierDual.toDual P (P ⊗[O] H.level v)
        (e.symm (ptP hOP f (Module.Free.chooseBasis O (H.level v) i) ⊗ₜ[O]
          CartierDual.ofDual O (H.level v) ((Module.Free.chooseBasis O (H.level v)).coord i))) (t ⊗ₜ[O] a) =
        ptP hOP f (Module.Free.chooseBasis O (H.level v) i) * t *
          algebraMap O P ((Module.Free.chooseBasis O (H.level v)).repr a i) := fun i =>
      he (ptP hOP f (Module.Free.chooseBasis O (H.level v) i)) t _ a
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    refine Eq.symm ?_
    calc ∑ i, ptP hOP f (Module.Free.chooseBasis O (H.level v) i) * t *
          algebraMap O P ((Module.Free.chooseBasis O (H.level v)).repr a i)
        = t * ∑ i, (Module.Free.chooseBasis O (H.level v)).repr a i •
            ptP hOP f (Module.Free.chooseBasis O (H.level v) i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Algebra.smul_def]
          ring
      _ = t * ptP hOP f (∑ i, (Module.Free.chooseBasis O (H.level v)).repr a i • Module.Free.chooseBasis O (H.level v) i) := by
          rw [map_sum]
          refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
          rw [map_smul]
      _ = t * ptP hOP f a := by rw [Module.Basis.sum_repr]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem coe_psiP_ofDual_bcPt (f : H.Point (AlgebraicClosure ℚ) v) (ψ : H'.Point (AlgebraicClosure ℚ) v)
    (e : letI := algebraOP P hOP; CartierDual P (P ⊗[O] H.level v) ≃ₐc[P] P ⊗[O] CartierDual O (H.level v))
    (he : letI := algebraOP P hOP; ∀ (s t : P) (φ : CartierDual O (H.level v)) (a : H.level v),
        CartierDual.pairing P (P ⊗[O] H.level v) (e.symm (s ⊗ₜ[O] φ)) (t ⊗ₜ[O] a) =
          s * t * algebraMap O P (CartierDual.pairing O (H.level v) φ a)) :
    letI := algebraOP P hOP
    ((psiP hOP D v (PDivisibleGroup.Point.toAlgHom ψ) e
        ((CartierDual.ofDual P (P ⊗[O] H.level v)) (bcPt hOP (PDivisibleGroup.Point.toAlgHom f)).toLinearMap) : P) :
      AlgebraicClosure ℚ) = D.pair (AlgebraicClosure ℚ) v f ψ := by
  letI := algebraOP P hOP
  rw [psiP_apply, e_ofDual_bcPt hOP v (PDivisibleGroup.Point.toAlgHom f) e he, map_sum, map_sum,
    PDivisibleGroup.CartierDuality.pair_def]
  show P.subtype (∑ i, bcPt hOP (PDivisibleGroup.Point.toAlgHom ψ)
    (idEquiv hOP D v (ptP hOP (PDivisibleGroup.Point.toAlgHom f) (Module.Free.chooseBasis O (H.level v) i) ⊗ₜ[O]
      CartierDual.ofDual O (H.level v) ((Module.Free.chooseBasis O (H.level v)).coord i)))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [idEquiv_tmul, bcPt_tmul, map_mul, PDivisibleGroup.CartierDuality.toDualEquiv_symm_apply]
  rfl

end DualPoint

end PDivisibleGroup.S6aMain

end

open PDivisibleGroup.S6aMain in

theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra O (AlgebraicClosure ℚ)] [Algebra O (ZMod p)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (hres : ∀ x : O, algebraMap O (ZMod p) x = 0 ↔
      P.valuation (algebraMap O (AlgebraicClosure ℚ) x) < 1)
    {h : ℕ} (H H' : PDivisibleGroup O p h) (D : H.CartierDuality H')
    (v : ℕ)

    (hord : ∃ (M : Type) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
        (_ : Module.Free (ZMod p) M) (E : Type) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
        (Θ : ZMod p ⊗[O] H.level v →ₐc[ZMod p] M ⊗[ZMod p] E),
        Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M))
    (f : H.Point (AlgebraicClosure ℚ) v) (ψ : H'.Point (AlgebraicClosure ℚ) v)
    (hf : ∀ a : H.level v, P.valuation (PDivisibleGroup.Point.toAlgHom f a -
      algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1)
    (hψ : ∀ a : H'.level v, P.valuation (PDivisibleGroup.Point.toAlgHom ψ a -
      algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) :
    D.pair (AlgebraicClosure ℚ) v f ψ = 1 := by
  classical
  letI := algebraOP P hOP
  haveI := isScalarTower P hOP
  haveI : HenselianLocalRing P := ValuationSubring.henselianLocalRing_of_isAlgClosed P

  have hp : ((p : ℕ) : P) ∈ IsLocalRing.maximalIdeal P := by
    rw [mem_maximalIdeal_iff]
    have h := (hres (p : O)).mp (by rw [map_natCast, ZMod.natCast_self])
    rwa [map_natCast] at h

  haveI : Coalgebra.IsCocomm P (P ⊗[O] H.level v) := inferInstance
  have hA : ∃ n : ℕ, Module.finrank P (P ⊗[O] H.level v) = p ^ n :=
    ⟨v * h, by rw [Module.finrank_baseChange, H.finrank_level]⟩
  obtain ⟨M, _iM1, _iM2, _iM3, _iM4, _iM5, π, hπ, hMet, huniv, hEnd, hμbc⟩ :=
    HopfAlgebra.exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_henselianLocalRing
      P (P ⊗[O] H.level v)
  have hordk : ∃ (M₀ : Type) (_ : CommRing M₀) (_ : HopfAlgebra (IsLocalRing.ResidueField P) M₀)
        (_ : Module.Finite (IsLocalRing.ResidueField P) M₀) (_ : Module.Free (IsLocalRing.ResidueField P) M₀)
        (E₀ : Type) (_ : CommRing E₀) (_ : HopfAlgebra (IsLocalRing.ResidueField P) E₀)
        (Θ : IsLocalRing.ResidueField P ⊗[P] (P ⊗[O] H.level v) →ₐc[IsLocalRing.ResidueField P]
          M₀ ⊗[IsLocalRing.ResidueField P] E₀),
        Function.Bijective Θ ∧ IsReduced E₀ ∧ IsReduced (CartierDual (IsLocalRing.ResidueField P) M₀) :=
    HopfAlgebra.exists_bijective_tensorProduct_isReduced_cartierDual_residueField_of_zmodp_valuationSubring_of_isCocomm p P hOP hres
      (H.level v) hord
  obtain ⟨g, hg⟩ :=
    HopfAlgebra.exists_eq_comp_of_forall_sub_counit_mem_maximalIdeal_of_bijective_tensorProduct_isReduced_valuationSubring
      p P hp (P ⊗[O] H.level v) hA M π hπ hMet hμbc hordk (bcPt hOP (PDivisibleGroup.Point.toAlgHom f))
      (bcPt_sub_counit_mem hOP (PDivisibleGroup.Point.toAlgHom f) hf)

  obtain ⟨e, he⟩ := CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul O P (H.level v)
  obtain ⟨ψP, hψP, hpair⟩ : ∃ ψP : CartierDual P (P ⊗[O] H.level v) →ₐ[P] P,
      (∀ lam : CartierDual P (P ⊗[O] H.level v), ψP lam - lam 1 ∈ IsLocalRing.maximalIdeal P) ∧
      ((ψP ((CartierDual.ofDual P (P ⊗[O] H.level v)) (bcPt hOP (PDivisibleGroup.Point.toAlgHom f)).toLinearMap) : P) :
        AlgebraicClosure ℚ) = D.pair (AlgebraicClosure ℚ) v f ψ :=
    ⟨psiP hOP D v (PDivisibleGroup.Point.toAlgHom ψ) e,
      psiP_sub_apply_one_mem hOP D v (PDivisibleGroup.Point.toAlgHom ψ) hψ e,
      coe_psiP_ofDual_bcPt hOP D v f ψ e he⟩
  have h3 := HopfAlgebra.apply_ofDual_eq_one_of_eq_comp_of_forall_sub_apply_one_mem_maximalIdeal_of_henselianLocalRing
    P (P ⊗[O] H.level v) M π hMet (bcPt hOP (PDivisibleGroup.Point.toAlgHom f)) g hg ψP hψP
  rw [← hpair, h3]
  rfl

end S_PDivisibleGroup_CartierDuality_pair_eq_one_of_forall_valuation_sub_counit_lt_one_of_bijective_tensorProduct_isReduced
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_pair_eq_one_of_forall_valuation_sub_counit_lt_one_of_bijective_tensorProduct_isReduced (solution)

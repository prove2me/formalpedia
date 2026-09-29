-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.pair_eq_one_of_eq_comp_of_etale_cartierDual_of_forall_valuation_sub_counit_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5d4702e3-672f-58be-b75b-c08a51e90798

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_PDivisibleGroup_CartierDuality
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_HopfAlgebra_apply_ofDual_eq_one_of_eq_comp_of_forall_sub_apply_one_mem_maximalIdeal_of_henselianLocalRing
import Theorems.Thm_CartierDual_exists_bialgEquiv_baseChange_forall_pairing_symm_tmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_pair_eq_one_of_eq_comp_of_etale_cartierDual_of_forall_valuation_sub_counit_lt_one
p2m_attr_erase "instance" "CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open scoped TensorProduct

universe u v w

noncomputable section

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "Point Point.toAlgHom height level CartierDuality CartierDuality.toDualEquiv_symm_apply CartierDuality.pair_def"
namespace ConnOrthMult
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

end PDivisibleGroup.ConnOrthMult

end

open PDivisibleGroup.ConnOrthMult in

theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    {h : ℕ} (H H' : PDivisibleGroup O p h) (D : H.CartierDuality H')
    (v : ℕ)

    (Mt : Type) [CommRing Mt] [HopfAlgebra O Mt] [Coalgebra.IsCocomm O Mt] [Module.Free O Mt] [Module.Finite O Mt]
    [Algebra.Etale O (CartierDual O Mt)]
    (π : H.level v →ₐc[O] Mt)
    (f : H.Point (AlgebraicClosure ℚ) v) (g : Mt →ₐ[O] AlgebraicClosure ℚ)
    (hfg : PDivisibleGroup.Point.toAlgHom f = g.comp (π : H.level v →ₐ[O] Mt))

    (ψ : H'.Point (AlgebraicClosure ℚ) v)
    (hψ : ∀ a : H'.level v, P.valuation (PDivisibleGroup.Point.toAlgHom ψ a -
      algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) :
    D.pair (AlgebraicClosure ℚ) v f ψ = 1 := by
  classical
  letI := PDivisibleGroup.ConnOrthMult.algebraOP P hOP
  haveI := PDivisibleGroup.ConnOrthMult.isScalarTower P hOP
  haveI : HenselianLocalRing P := ValuationSubring.henselianLocalRing_of_isAlgClosed P
  haveI : Coalgebra.IsCocomm P (P ⊗[O] H.level v) := inferInstance

  obtain ⟨e, he⟩ := CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul O P (H.level v)
  obtain ⟨ψP, hψP, hpair⟩ : ∃ ψP : CartierDual P (P ⊗[O] H.level v) →ₐ[P] P,
      (∀ lam : CartierDual P (P ⊗[O] H.level v), ψP lam - lam 1 ∈ IsLocalRing.maximalIdeal P) ∧
      ((ψP ((CartierDual.ofDual P (P ⊗[O] H.level v)) (PDivisibleGroup.ConnOrthMult.bcPt hOP (PDivisibleGroup.Point.toAlgHom f)).toLinearMap) : P) :
        AlgebraicClosure ℚ) = D.pair (AlgebraicClosure ℚ) v f ψ :=
    ⟨PDivisibleGroup.ConnOrthMult.psiP hOP D v (PDivisibleGroup.Point.toAlgHom ψ) e,
      PDivisibleGroup.ConnOrthMult.psiP_sub_apply_one_mem hOP D v (PDivisibleGroup.Point.toAlgHom ψ) hψ e,
      PDivisibleGroup.ConnOrthMult.coe_psiP_ofDual_bcPt hOP D v f ψ e he⟩

  let πP : P ⊗[O] H.level v →ₐc[P] P ⊗[O] Mt := Bialgebra.TensorProduct.map (BialgHom.id P P) π
  haveI hMet : Algebra.Etale P (CartierDual P (P ⊗[O] Mt)) := by
    obtain ⟨e', -⟩ := CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul O P Mt
    exact Algebra.Etale.of_equiv e'.toAlgEquiv.symm
  have hfac : PDivisibleGroup.ConnOrthMult.bcPt hOP (PDivisibleGroup.Point.toAlgHom f) =
      (PDivisibleGroup.ConnOrthMult.bcPt hOP g).comp (πP : P ⊗[O] H.level v →ₐ[P] P ⊗[O] Mt) := by
    apply Algebra.TensorProduct.ext'
    intro s a
    rw [PDivisibleGroup.ConnOrthMult.bcPt_tmul, AlgHom.comp_apply]
    show _ = PDivisibleGroup.ConnOrthMult.bcPt hOP g (πP (s ⊗ₜ[O] a))
    have hπP : πP (s ⊗ₜ[O] a) = s ⊗ₜ[O] π a := rfl
    rw [hπP, PDivisibleGroup.ConnOrthMult.bcPt_tmul]
    congr 1
    apply Subtype.ext
    show (PDivisibleGroup.Point.toAlgHom f) a = g (π a)
    rw [hfg]
    rfl
  have h3 := HopfAlgebra.apply_ofDual_eq_one_of_eq_comp_of_forall_sub_apply_one_mem_maximalIdeal_of_henselianLocalRing
    P (P ⊗[O] H.level v) (P ⊗[O] Mt) πP hMet (PDivisibleGroup.ConnOrthMult.bcPt hOP (PDivisibleGroup.Point.toAlgHom f))
    (PDivisibleGroup.ConnOrthMult.bcPt hOP g) hfac ψP hψP
  rw [← hpair, h3]
  rfl

end S_PDivisibleGroup_CartierDuality_pair_eq_one_of_eq_comp_of_etale_cartierDual_of_forall_valuation_sub_counit_lt_one
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_pair_eq_one_of_eq_comp_of_etale_cartierDual_of_forall_valuation_sub_counit_lt_one (solution)

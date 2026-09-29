-- Prove2me | solution 1 for PDivisibleGroup.tateModule_induced_mem_and_comm_and_add_and_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2c0b0b8c-e706-52c0-a26f-72914e4a88fb

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_tateModule_induced_mem_and_comm_and_add_and_comp

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

theorem solution
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
            algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) :

    (∀ (u : ∀ w : ℕ, H.level w →ₐ[O] H.level w) (U : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))),
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u w))))) →
      (∀ (w : ℕ) (a : H.level w), Coalgebra.counit (R := O) (u w a) = Coalgebra.counit (R := O) a) →
      ∀ y : TateModule p (H.Points (AlgebraicClosure ℚ)), y ∈ S → U y ∈ S) ∧

    (∀ (u : ∀ w : ℕ, H.level w →ₐ[O] H.level w) (U : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))),
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u w))))) →
      ∀ τ' : AlgebraicClosure ℚ ≃ₐ[O] AlgebraicClosure ℚ,
        H.tateModuleRep (AlgebraicClosure ℚ) τ' ∘ₗ U = U ∘ₗ H.tateModuleRep (AlgebraicClosure ℚ) τ') ∧

    (∀ (u u' : ∀ w : ℕ, H.level w →ₐ[O] H.level w)
      (U U' : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))),
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u w))))) → (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U' x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u' w))))) →
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        (((U + U') x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp ((fun w => (WithConv.toConv (u w) * WithConv.toConv (u' w)).ofConv) w)))))) ∧

    (∀ (u u' : ∀ w : ℕ, H.level w →ₐ[O] H.level w)
      (U U' : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))),
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u w))))) → (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U' x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u' w))))) →
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        (((U ∘ₗ U') x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp ((fun w => (u' w).comp (u w)) w)))))) ∧

    (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        (((1 : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp ((fun w => AlgHom.id O (H.level w)) w))))) ∧
    (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        (((0 : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))) x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp ((fun w => (Algebra.ofId O (H.level w)).comp (Bialgebra.counitAlgHom O (H.level w))) w))))) ∧

    (∀ (u : ∀ w : ℕ, H.level w →ₐ[O] H.level w) (U : Module.End ℤ_[p] (TateModule p (H.Points (AlgebraicClosure ℚ)))),
      (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        ((U x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp (u w))))) →
      ∀ c : ℤ_[p], (∀ (x : TateModule p (H.Points (AlgebraicClosure ℚ))) (n w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
        H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) = (x : ℕ → H.Points (AlgebraicClosure ℚ)) n →
        (((c • U) x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n =
          H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom f).comp ((fun w => (WithConv.toConv (u w) ^ PadicInt.appr c w).ofConv) w)))))) := by
  classical

  have hmul : ∀ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w) (u u' : H.level w →ₐ[O] H.level w),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom f).comp
          (WithConv.toConv u * WithConv.toConv u').ofConv) =
        (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom f).comp u) *
          PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom f).comp u') :
            H.Point (AlgebraicClosure ℚ) w) := by
    intro w f u u'
    rw [AlgHom.comp_convMul_distrib]
    rfl
  have hone : ∀ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom f).comp
        ((Algebra.ofId O (H.level w)).comp (Bialgebra.counitAlgHom O (H.level w)))) =
        (1 : H.Point (AlgebraicClosure ℚ) w) := by
    intro w f
    refine PDivisibleGroup.Point.ext fun a => ?_
    rw [PDivisibleGroup.Point.toAlgHom_ofAlgHom, PDivisibleGroup.Point.one_apply, AlgHom.comp_apply,
      AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply, AlgHom.commutes]
  have hpow : ∀ (w : ℕ) (f : H.Point (AlgebraicClosure ℚ) w) (u : H.level w →ₐ[O] H.level w) (m : ℕ),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom f).comp (WithConv.toConv u ^ m).ofConv) =
        (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom f).comp u) : H.Point (AlgebraicClosure ℚ) w) ^ m := by
    intro w f u m
    induction m with
    | zero =>
      rw [pow_zero, pow_zero]
      refine PDivisibleGroup.Point.ext fun a => ?_
      rw [PDivisibleGroup.Point.toAlgHom_ofAlgHom, PDivisibleGroup.Point.one_apply, AlgHom.comp_apply]
      change (PDivisibleGroup.Point.toAlgHom f) ((1 : WithConv (H.level w →ₐ[O] H.level w)) a) = _
      rw [AlgHom.convOne_apply, AlgHom.commutes]
    | succ m ih =>
      rw [pow_succ, pow_succ, AlgHom.comp_convMul_distrib, ← ih]
      rfl
  have happr : ∀ (c : ℤ_[p]) (k m : ℕ), k ≤ m →
      ((c.appr m : ℕ) : ZMod (p ^ k)) = ((c.appr k : ℕ) : ZMod (p ^ k)) := by
    intro c k m hkm
    rw [← TateModule.toZModPow_eq_appr k, ← PadicInt.zmod_cast_comp_toZModPow k m hkm, RingHom.comp_apply,
      TateModule.toZModPow_eq_appr, ZMod.castHom_apply, ZMod.cast_natCast (pow_dvd_pow p hkm)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro u U hpin hcounit y hy
    rw [hS] at hy ⊢
    intro n
    obtain ⟨w, f, hf, hred⟩ := hy n
    refine ⟨w, PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom f).comp (u w)),
      (hpin y n w f hf).symm, fun a => ?_⟩
    rw [PDivisibleGroup.Point.toAlgHom_ofAlgHom, AlgHom.comp_apply, ← hcounit w a]
    exact hred (u w a)
  ·
    intro u U hpin τ'
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    obtain ⟨w, f, hf⟩ := PDivisibleGroup.Points.exists_mkAdd H ((x : ℕ → H.Points (AlgebraicClosure ℚ)) n)
    have hτx : H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul (H.pointMap (τ' : AlgebraicClosure ℚ →ₐ[O] AlgebraicClosure ℚ) w f)) =
        ((H.tateModuleRep (AlgebraicClosure ℚ) τ' x : TateModule p (H.Points (AlgebraicClosure ℚ))) : ℕ → H.Points (AlgebraicClosure ℚ)) n := by
      rw [PDivisibleGroup.tateModuleRep_apply, ← hf, PDivisibleGroup.Points.smul_pointsMkAdd]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, PDivisibleGroup.tateModuleRep_apply, hpin x n w f hf,
      PDivisibleGroup.Points.smul_pointsMkAdd, hpin _ n w _ hτx]
    rfl
  ·
    intro u u' U U' hpin hpin' x n w f hf
    rw [LinearMap.add_apply, TateModule.coe_add, Pi.add_apply, hpin x n w f hf, hpin' x n w f hf, ← map_add,
      ← ofMul_mul]
    congr 2
    exact (hmul w f (u w) (u' w)).symm
  ·
    intro u u' U U' hpin hpin' x n w f hf
    rw [LinearMap.comp_apply, hpin (U' x) n w _ (hpin' x n w f hf).symm]
    rfl
  ·
    intro x n w f hf
    rw [Module.End.one_apply, ← hf]
    rfl
  ·
    intro x n w f hf
    rw [LinearMap.zero_apply, TateModule.coe_zero, Pi.zero_apply, hone, ofMul_one, map_zero]
  ·
    intro u U hpin c x n w f hf
    have hUn := hpin x n w f hf
    rw [LinearMap.smul_apply, TateModule.smul_apply, hUn, hpow, ofMul_pow, map_nsmul, ← natCast_zsmul]
    have htor_n : ((p ^ n : ℕ) : ℤ) • H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul
        (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom f).comp (u w)) : H.Point (AlgebraicClosure ℚ) w)) = 0 := by
      rw [← hUn]
      exact TateModule.torsion (U x) n
    have htor_w : ((p ^ w : ℕ) : ℤ) • H.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul
        (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom f).comp (u w)) : H.Point (AlgebraicClosure ℚ) w)) = 0 := by
      rw [natCast_zsmul]
      exact H.nsmul_pointsMkAdd_eq_zero w _
    rcases le_total n w with hnw | hwn
    · exact TateModule.natCast_smul_eq_of_zmod_eq htor_n (happr c n w hnw).symm
    · exact TateModule.natCast_smul_eq_of_zmod_eq htor_w (happr c w n hwn)

end S_PDivisibleGroup_tateModule_induced_mem_and_comm_and_add_and_comp
end P2MW
export P2MW.S_PDivisibleGroup_tateModule_induced_mem_and_comm_and_add_and_comp (solution)

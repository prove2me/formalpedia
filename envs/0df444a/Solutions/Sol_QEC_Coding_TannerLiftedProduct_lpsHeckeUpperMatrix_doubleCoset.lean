-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeUpperMatrix_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:40:59.22925+00:00
-- url     : https://prove2.me/submissions/6cfd11d6-6daf-46e1-ab46-fce8fc2519d8

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (i : Option (Fin p)) :
    ∃ (δ γ : SL(2,ℤ)), δ∈CongruenceSubgroup.Gamma0 N ∧ γ∈CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperMatrix p i=(δ:Matrix (Fin 2) (Fin 2) ℤ)*
        lpsHeckeUpperMatrix p none*(γ:Matrix (Fin 2) (Fin 2) ℤ) := by
  cases i with
  | none => exact ⟨1,1,(CongruenceSubgroup.Gamma0 N).one_mem,
      (CongruenceSubgroup.Gamma0 N).one_mem,by simp⟩
  | some j =>
    have hNu : IsUnit (N:ZMod p) := (ZMod.isUnit_iff_coprime N p).mpr hNp.symm
    have hN : (N:ZMod p)≠0 := hNu.ne_zero
    let k : ℤ := ((j.val:ZMod p)-(N:ZMod p)⁻¹).val
    have hk : (k:ZMod p)=(j.val:ZMod p)-(N:ZMod p)⁻¹ := by
      dsimp [k]
      exact_mod_cast ZMod.natCast_zmod_val ((j.val:ZMod p)-(N:ZMod p)⁻¹)
    let γ : SL(2,ℤ) := ⟨!![1,k;(N:ℤ),1+(N:ℤ)*k],by simp [Matrix.det_fin_two];ring⟩
    have hγ : γ∈CongruenceSubgroup.Gamma0 N := by
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [γ]
    let A := lpsHeckeUpperMatrix p none*(γ:Matrix (Fin 2) (Fin 2) ℤ)
    have hAe : A= !![(p:ℤ),(p:ℤ)*k;(N:ℤ),1+(N:ℤ)*k] := by
      ext r c
      fin_cases r <;> fin_cases c <;>
        simp [A,γ,lpsHeckeUpperMatrix]
    have h0 : (p:ℤ)∣A 0 1-A 0 0*(j.val:ℤ) := by
      rw [hAe]
      change (p:ℤ)∣(p:ℤ)*k-(p:ℤ)*(j.val:ℤ)
      exact dvd_sub (dvd_mul_right _ _) (dvd_mul_right _ _)
    have h1 : (p:ℤ)∣A 1 1-A 1 0*(j.val:ℤ) := by
      rw [hAe]
      change (p:ℤ)∣1+(N:ℤ)*k-(N:ℤ)*(j.val:ℤ)
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      push_cast
      rw [hk]
      field_simp
      ring
    let D : Matrix (Fin 2) (Fin 2) ℤ := !![A 0 0,(A 0 1-A 0 0*(j.val:ℤ))/(p:ℤ);
      A 1 0,(A 1 1-A 1 0*(j.val:ℤ))/(p:ℤ)]
    have he := lpsHeckeFactorFinite p A j h0 h1
    have hDA : D.det=1 := by
      have hd := congrArg Matrix.det he
      have hA : A.det=(p:ℤ) := by
        simp [A,Matrix.det_mul,lpsHeckeUpperMatrix_det,Matrix.SpecialLinearGroup.det_coe]
      rw [hA,Matrix.det_mul,lpsHeckeUpperMatrix_det] at hd
      have hpZ : (p:ℤ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      apply mul_right_cancel₀ hpZ
      simpa only [one_mul] using hd.symm
    let δ : SL(2,ℤ) := ⟨D,hDA⟩
    have hδ : δ∈CongruenceSubgroup.Gamma0 N := by
      rw [CongruenceSubgroup.Gamma0_mem]
      have hD : D 1 0=(N:ℤ) := by
        simp [D,hAe]
      simp [δ,hD]
    refine ⟨δ⁻¹,γ,(CongruenceSubgroup.Gamma0 N).inv_mem hδ,hγ,?_⟩
    have hi : ((δ⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)*(δ:Matrix (Fin 2) (Fin 2) ℤ)=1 := by
      rw [←Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one]
    calc
      lpsHeckeUpperMatrix p (some j)=((δ⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)*
          ((δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p (some j)) := by
            rw [←Matrix.mul_assoc,hi,Matrix.one_mul]
      _=((δ⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)*A :=
        congrArg (fun M => ((δ⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)*M) he.symm
      _=_ := (Matrix.mul_assoc _ _ _).symm
end QEC.Coding.TannerLiftedProduct

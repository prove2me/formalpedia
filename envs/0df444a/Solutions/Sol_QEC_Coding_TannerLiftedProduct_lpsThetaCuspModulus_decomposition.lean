-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspModulus_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:41:47.231608+00:00
-- url     : https://prove2.me/submissions/2b3762c8-bb05-4a3e-b568-be2bfc97f139

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q N : ℕ) [Fact q.Prime] (hN : 0<N) :
    ∃ t v L : ℕ,0<L ∧ L.Coprime (2*q) ∧ N=2^t*q^v*L := by
  obtain ⟨t,n,hn2,heN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' 2 (by decide)
  have hn : n≠0 := by intro h;rw [h,mul_zero] at heN;exact hN.ne' heN
  obtain ⟨v,L,hLq,hen⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q (Fact.out : q.Prime).ne_one
  have hL : 0<L := by
    apply Nat.pos_of_ne_zero
    intro h
    rw [h,mul_zero] at hen
    exact hn hen
  have hL2 : ¬2∣L := by
    intro h
    apply hn2
    rw [hen]
    exact dvd_mul_of_dvd_right h _
  have hc2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hL2).symm
  have hcq := ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hLq).symm
  refine ⟨t,v,L,hL,hc2.mul_right hcq,?_⟩
  rw [heN,hen]
  ring
end QEC.Coding.TannerLiftedProduct

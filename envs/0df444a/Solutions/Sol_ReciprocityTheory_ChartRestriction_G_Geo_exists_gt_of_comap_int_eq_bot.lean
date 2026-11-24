-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.exists_gt_of_comap_int_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:35.034795+00:00
-- url     : https://prove2.me/submissions/ecfdd4e1-ba7c-45d1-8c85-89c7cf34b304

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_int_isJacobsonRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open Ideal
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {σ A : Type*} [Finite σ] [CommRing A]
    (g : MvPolynomial σ ℤ →+* A) (hg : Function.Surjective g) (p : Ideal A) (hp : p.IsPrime)
    (hb : p.comap (g.comp MvPolynomial.C) = ⊥) : ∃ q : Ideal A, q.IsPrime ∧ p < q := by
  haveI := int_isJacobsonRing
  have hnm : ¬ p.IsMaximal := by
    intro hm
    haveI := hm
    letI : Field (A ⧸ p) := Ideal.Quotient.field p
    let f : MvPolynomial σ ℤ →+* A ⧸ p := (Ideal.Quotient.mk p).comp g
    have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hg
    have hint : (f.comp MvPolynomial.C).IsIntegral := by
      first
      | exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing f hf
      | exact Ideal.MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing f hf
      | exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobson f hf
    have hinj : Function.Injective (f.comp MvPolynomial.C) := by
      rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
      intro x hx
      rw [RingHom.mem_ker] at hx
      have hx' : x ∈ p.comap (g.comp MvPolynomial.C) := by
        rw [Ideal.mem_comap]
        exact Ideal.Quotient.eq_zero_iff_mem.mp hx
      rw [hb] at hx'
      exact hx'
    letI := (f.comp MvPolynomial.C).toAlgebra
    haveI : Algebra.IsIntegral ℤ (A ⧸ p) := ⟨hint⟩
    have hZ : IsField ℤ := isField_of_isIntegral_of_isField hinj (Field.toIsField (A ⧸ p))
    obtain ⟨y, hy⟩ := hZ.mul_inv_cancel (two_ne_zero : (2 : ℤ) ≠ 0)
    omega
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  refine ⟨m, hm.isPrime, lt_of_le_of_ne hpm ?_⟩
  rintro rfl
  exact hnm hm
end ReciprocityTheory.ChartRestriction.G.Geo

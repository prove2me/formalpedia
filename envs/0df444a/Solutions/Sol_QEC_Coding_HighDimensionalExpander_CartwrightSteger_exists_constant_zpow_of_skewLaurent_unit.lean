-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_constant_zpow_of_skewLaurent_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:33:09.261577+00:00
-- url     : https://prove2.me/submissions/1123e98d-6777-480e-bb71-12683622b075

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_skewLaurent_support_max
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_skewLaurent_support_min
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurent_support_max_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurent_support_min_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val


attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Multiplicative SkewMonoidAlgebra
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerSkewLaurentRing P r)ˣ) :
    ∃ c : (ConstantExtension P r)ˣ, ∃ n : ℤ,
      (u : CartwrightStegerSkewLaurentRing P r) =
        SkewMonoidAlgebra.single (Multiplicative.ofAdd n)
          (c : ConstantExtension P r) := by
  let f : CartwrightStegerSkewLaurentRing P r := u
  let g : CartwrightStegerSkewLaurentRing P r := ↑u⁻¹
  have hf : f ≠ 0 := Units.ne_zero u
  have hg : g ≠ 0 := Units.ne_zero u⁻¹
  obtain ⟨a, ha, hmaxa⟩ := exists_skewLaurent_support_max P r hf
  obtain ⟨b, hb, hmaxb⟩ := exists_skewLaurent_support_max P r hg
  obtain ⟨c, hc, hminc⟩ := exists_skewLaurent_support_min P r hf
  obtain ⟨d, hd, hmind⟩ := exists_skewLaurent_support_min P r hg
  have hprod : f * g = 1 := by
    change (u : CartwrightStegerSkewLaurentRing P r) *
      (↑u⁻¹ : CartwrightStegerSkewLaurentRing P r) = 1
    change ↑(u * u⁻¹) = (1 : CartwrightStegerSkewLaurentRing P r)
    rw [mul_inv_cancel]
    rfl
  have hmaxProd := (skewLaurent_support_max_mul P r
    ha hmaxa hb hmaxb).1
  have hminProd := (skewLaurent_support_min_mul P r
    hc hminc hd hmind).1
  rw [hprod, SkewMonoidAlgebra.support_one] at hmaxProd hminProd
  have hab : a + b = 0 := by
    have heq : Multiplicative.ofAdd (a + b) = 1 :=
      Finset.mem_singleton.mp hmaxProd
    exact congrArg Multiplicative.toAdd heq
  have hcd : c + d = 0 := by
    have heq : Multiplicative.ofAdd (c + d) = 1 :=
      Finset.mem_singleton.mp hminProd
    exact congrArg Multiplicative.toAdd heq
  have hca : c ≤ a := hminc a ha
  have hdb : d ≤ b := hmind b hb
  have hac : a = c := by omega
  subst c
  have hsupp : f.support = {Multiplicative.ofAdd a} := by
    apply Finset.Subset.antisymm
    · intro x hx
      have hxrepr : x = Multiplicative.ofAdd x.toAdd := rfl
      have hle := hmaxa x.toAdd (hxrepr ▸ hx)
      have hge := hminc x.toAdd (hxrepr ▸ hx)
      have hxa : x.toAdd = a := by omega
      apply Finset.mem_singleton.mpr
      apply Multiplicative.toAdd.injective
      exact hxa
    · exact Finset.singleton_subset_iff.mpr ha
  have hcoeff : f.coeff (Multiplicative.ofAdd a) ≠ 0 :=
    SkewMonoidAlgebra.mem_support_iff.mp ha
  let coeffUnit : (ConstantExtension P r)ˣ :=
    Units.mk0 (f.coeff (Multiplicative.ofAdd a)) hcoeff
  refine ⟨coeffUnit, a, ?_⟩
  apply SkewMonoidAlgebra.ext
  intro x
  by_cases hx : x = Multiplicative.ofAdd a
  · subst x
    rw [SkewMonoidAlgebra.coeff_single_apply, if_pos rfl]
    rfl
  · have hxnot : x ∉ f.support := by
      rw [hsupp]
      intro hmem
      exact hx (Finset.mem_singleton.mp hmem)
    rw [SkewMonoidAlgebra.notMem_support_iff.mp hxnot]
    rw [SkewMonoidAlgebra.coeff_single_apply, if_neg (Ne.symm hx)]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger

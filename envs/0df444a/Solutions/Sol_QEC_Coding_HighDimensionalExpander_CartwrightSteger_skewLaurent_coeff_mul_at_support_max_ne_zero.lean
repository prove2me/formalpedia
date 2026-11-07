-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurent_coeff_mul_at_support_max_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:30:05.940692+00:00
-- url     : https://prove2.me/submissions/90de8c0c-cffa-4f3a-a596-95884f68c018

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
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
    {f g : CartwrightStegerSkewLaurentRing P r}
    {a b : ℤ}
    (ha : Multiplicative.ofAdd a ∈ f.support)
    (hmaxa : ∀ x, Multiplicative.ofAdd x ∈ f.support → x ≤ a)
    (hb : Multiplicative.ofAdd b ∈ g.support)
    (hmaxb : ∀ x, Multiplicative.ofAdd x ∈ g.support → x ≤ b) :
    (f * g).coeff (Multiplicative.ofAdd (a + b)) ≠ 0 := by
  rw [SkewMonoidAlgebra.coeff_mul_left,
    SkewMonoidAlgebra.sum_def']
  rw [Finset.sum_eq_single (Multiplicative.ofAdd a)]
  · have hfa : f.coeff (Multiplicative.ofAdd a) ≠ 0 :=
      SkewMonoidAlgebra.mem_support_iff.mp ha
    have hgb : g.coeff (Multiplicative.ofAdd b) ≠ 0 :=
      SkewMonoidAlgebra.mem_support_iff.mp hb
    have hact : Multiplicative.ofAdd a •
        g.coeff (Multiplicative.ofAdd b) ≠ 0 := by
      change constantFrobeniusZRingAction P r (Multiplicative.ofAdd a)
        (g.coeff (Multiplicative.ofAdd b)) ≠ 0
      exact (map_ne_zero (constantFrobeniusZRingAction P r
        (Multiplicative.ofAdd a))).mpr hgb
    simpa using mul_ne_zero hfa hact
  · intro x hx hxa
    let xInt := Multiplicative.toAdd x
    have hxrepr : Multiplicative.ofAdd xInt = x := rfl
    have hxmem : Multiplicative.ofAdd xInt ∈ f.support := hxrepr ▸ hx
    have hxlt : xInt < a := lt_of_le_of_ne (hmaxa xInt hxmem) (by
      intro h
      apply hxa
      rw [← hxrepr]
      exact congrArg Multiplicative.ofAdd h)
    have hnot : Multiplicative.ofAdd (-xInt + (a + b)) ∉ g.support := by
      intro hmem
      have hle := hmaxb (-xInt + (a + b)) hmem
      omega
    have heq : x⁻¹ * Multiplicative.ofAdd (a + b) =
        Multiplicative.ofAdd (-xInt + (a + b)) := by
      apply Multiplicative.toAdd.injective
      simp [xInt]
    rw [heq, SkewMonoidAlgebra.notMem_support_iff.mp hnot]
    simp
  · exact fun hnot => (hnot ha).elim
end QEC.Coding.HighDimensionalExpander.CartwrightSteger

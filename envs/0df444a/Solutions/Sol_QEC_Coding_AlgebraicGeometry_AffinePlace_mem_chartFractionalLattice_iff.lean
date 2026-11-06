-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.mem_chartFractionalLattice_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:14:17.003491+00:00
-- url     : https://prove2.me/submissions/7328a98a-f594-404a-ba1c-d9613367fbf5

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_count_chartFractionalLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_chartFractionalLattice_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_count_spanSingleton_eq_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_order_lowerBound_iff_valuation_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_le_of_all_count_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero nonZeroDivisors
open QEC.Coding.AlgebraicGeometry.AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.AffinePlace._p2m_local_instance_45ffe40864_30
namespace QEC.Coding.AlgebraicGeometry.AffinePlace
theorem _root_.solution (D : Divisor (carrier k F)) (f : F) :
    f ∈ chartFractionalLattice k F D ↔
      ∀ P : carrier k F, valuation k F P f ≤ WithZero.exp (D P) := by
  constructor
  · intro hfmem P
    by_cases hf : f = 0
    · simpa only [hf, map_zero] using
        (zero_le' : (0 : ℤᵐ⁰) ≤ WithZero.exp (D P))
    · have hspan_ne_zero :
        FractionalIdeal.spanSingleton (affineRing k F)⁰ f ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf
      have hspan_le : FractionalIdeal.spanSingleton (affineRing k F)⁰ f ≤
          chartFractionalLattice k F D :=
        FractionalIdeal.spanSingleton_le_iff_mem.mpr hfmem
      have hcounts := FractionalIdeal.count_mono F P hspan_ne_zero hspan_le
      have horder : -D P ≤ GlobalPlace.order (globalPlace k F P) f := by
        rw [count_chartFractionalLattice, count_spanSingleton_eq_order k F P hf] at hcounts
        exact hcounts
      exact (order_lowerBound_iff_valuation_le k F P hf (D P)).mp horder
  · intro h
    by_cases hf : f = 0
    · simpa only [hf] using (chartFractionalLattice k F D).zero_mem
    · have hspan_ne_zero :
        FractionalIdeal.spanSingleton (affineRing k F)⁰ f ≠ 0 :=
        FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf
      have hcounts : ∀ P : carrier k F,
          FractionalIdeal.count F P (chartFractionalLattice k F D) ≤
            FractionalIdeal.count F P
              (FractionalIdeal.spanSingleton (affineRing k F)⁰ f) := by
        intro P
        rw [count_chartFractionalLattice, count_spanSingleton_eq_order k F P hf]
        exact (order_lowerBound_iff_valuation_le k F P hf (D P)).mpr (h P)
      exact FractionalIdeal.spanSingleton_le_iff_mem.mp
        (le_of_all_count_le k F hspan_ne_zero
          (chartFractionalLattice_ne_zero k F D) hcounts)
end QEC.Coding.AlgebraicGeometry.AffinePlace

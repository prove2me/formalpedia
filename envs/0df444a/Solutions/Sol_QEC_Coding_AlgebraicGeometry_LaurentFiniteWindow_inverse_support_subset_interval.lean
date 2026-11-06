-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.inverse_support_subset_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:29:31.713923+00:00
-- url     : https://prove2.me/submissions/2aa8fd7b-13b6-49bf-bfa3-d8e0266b8816

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_directCoordinate_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_inverseCoordinate_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_direct_support_subset_interval

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
theorem _root_.solution (q : k[X]) :
    (inverseCoordinate k q).coeff.support ⊆ Finset.Icc (-(q.natDegree : ℤ)) 0 := by
  intro n hn
  have hneg : -n ∈ (directCoordinate k q).coeff.support := by
    rw [Finsupp.mem_support_iff] at hn ⊢
    simpa [directCoordinate_apply, inverseCoordinate_apply] using hn
  have hbounds := direct_support_subset_interval k q hneg
  rw [Finset.mem_Icc] at hbounds ⊢
  omega
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.hc_mul_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:53.950202+00:00
-- url     : https://prove2.me/submissions/2a0106b4-9037-4175-8e66-a36a763d8e9c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_XZeroPowDvdOfIsHomogeneousAeval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution {σ : Type*} {p : MvPolynomial σ ℤ} {a : ℕ} (hp : p.IsHomogeneous a)
    (q : MvPolynomial σ ℤ) (b : ℕ) :
    MvPolynomial.homogeneousComponent (a + b) (p * q) =
      p * MvPolynomial.homogeneousComponent b q := by
  classical
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent q]
  rw [Finset.mul_sum, map_sum, Finset.sum_eq_single b]
  · rw [MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (hp.mul (MvPolynomial.homogeneousComponent_isHomogeneous b q))), if_pos rfl]
  · intro k _ hk
    rw [MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (hp.mul (MvPolynomial.homogeneousComponent_isHomogeneous k q))), if_neg (by omega)]
  · intro hb
    rw [MvPolynomial.homogeneousComponent_eq_zero b q (by simp at hb; omega), mul_zero, map_zero]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree.so_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:19.064275+00:00
-- url     : https://prove2.me/submissions/6fbefd65-4e5c-4a59-bf94-0a303a15a06b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
variable {k : Type} [CommRing k]
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
theorem _root_.solution (c : σ → σ → k) (r : k) (P : MvPolynomial σ k) :
    secondOrder k c (r • P) = r • secondOrder k c P := by
  first
  | (simp only [so_def, MvPolynomial.smul_eq_C_mul, Finset.mul_sum, Derivation.leibniz, smul_eq_mul,
      pderiv_C, mul_zero, add_zero]
     refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
     ring)
  | simp [so_def, Finset.smul_sum, mul_smul_comm]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree

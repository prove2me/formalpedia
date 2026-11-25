-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.Canon.zero_of_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:14.176014+00:00
-- url     : https://prove2.me/submissions/1d639d6f-7f05-4d95-9bc2-ccd57d72ea8a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.LocalProperties.Reduced
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_formalSeriesValueAtThreePoints_genericPoints
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_dir_same
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_dir_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_pderiv_eval_three
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_zero_of_pd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_update_three_two_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
variable [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.Canon
theorem _root_.solution (f : PS k 3 d) (add : ∀ {n} (x y v v' : Q k d n), E3 f x y (v + v') = E3 f x y v + E3 f x y v')
    (h : ∀ {n} b (x y : Q k d n), E3 (pderiv k (2, b) f) x y 0 = 0) : f = 0 := by
  have h0 : ∀ {n : ℕ} (x y : Q k d n), E3 f x y 0 = 0 := by
    intro n x y
    have e := add x y 0 0
    rw [add_zero] at e
    linear_combination -e
  have hd : ∀ b, pderiv k (2, b) f = 0 := by
    intro b
    have e := congrArg (pderiv k ((3 : Fin 4), b)) (add (gen 0) (gen 1) (gen 2) (gen 3))
    have d0 : Dir (3 : Fin 4) (gen 0 : Q k d 4) 0 := dir_ne (by decide)
    have d1 : Dir (3 : Fin 4) (gen 1 : Q k d 4) 0 := dir_ne (by decide)
    have d2 : Dir (3 : Fin 4) (gen 2 : Q k d 4) 0 := dir_ne (by decide)
    have d3 : Dir (3 : Fin 4) (gen 3 : Q k d 4) 1 := dir_same 3
    rw [map_add, pderiv_eval_three d0 d1 (d2.add d3), pderiv_eval_three d0 d1 d2, pderiv_eval_three d0 d1 d3] at e
    simp only [mul_zero, zero_add, add_zero, mul_one] at e
    have e' := congrArg (sb (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3)) e
    have s0 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 0) = gen 0 := sq_gen _ 0
    have s1 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 1) = gen 1 := sq_gen _ 1
    have s2 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 2) = gen 2 := sq_gen _ 2
    have s3 : sq (![gen 0, gen 1, gen 2, 0] : Fin 4 → Q k d 3) (gen 3) = 0 := sq_gen _ 3
    rw [formalPointSubstitutionSeries_valueAtThreePoints, formalPointSubstitutionSeries_valueAtThreePoints, map_add, s0, s1, s2, s3, add_zero, h b (gen 0) (gen 1), formalSeriesValueAtThreePoints_genericPoints] at e'
    exact e'
  have hz : sb (Function.update gen 2 0) f = 0 := by
    rw [update_three_two_zero]
    exact h0 (gen 0) (gen 1)
  exact zero_of_pd 2 hd hz
end ReciprocityTheory.ChartRestriction.G.TB.Canon

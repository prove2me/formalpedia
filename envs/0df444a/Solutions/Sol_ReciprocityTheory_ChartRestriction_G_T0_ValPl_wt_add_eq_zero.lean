-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValPl.wt_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:41.095203+00:00
-- url     : https://prove2.me/submissions/2230e233-5b2c-4d81-b34c-72a8f44a7f4a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValPl
open IsDedekindDomain WithZero IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.T0.ValPl
theorem _root_.solution {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 := by
  induction a using WithTop.recTopCoe with
  | top => simp at h
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp at h
    | coe b =>
      have ha' : (0 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (0 : ℤ) ≤ b := by exact_mod_cast hb
      have h' : a + b = 0 := by exact_mod_cast h
      have ha0 : a = 0 := by omega
      rw [ha0]
      first | rfl | exact WithTop.coe_zero | simp
end ReciprocityTheory.ChartRestriction.G.T0.ValPl

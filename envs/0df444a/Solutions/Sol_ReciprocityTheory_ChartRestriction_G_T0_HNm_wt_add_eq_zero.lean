-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HNm.wt_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:34:47.724704+00:00
-- url     : https://prove2.me/submissions/62f0cf6f-7807-42e1-81fd-049158e7ecff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HNm
namespace ReciprocityTheory.ChartRestriction.G.T0.HNm
theorem _root_.solution {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 := by
  cases a with
  | top => simp at h
  | coe x =>
    cases b with
    | top => simp at h
    | coe y =>
      have h' : x + y = 0 := by exact_mod_cast h
      have hx : 0 ≤ x := by exact_mod_cast ha
      have hy : 0 ≤ y := by exact_mod_cast hb
      exact_mod_cast (show x = 0 by omega)
end ReciprocityTheory.ChartRestriction.G.T0.HNm

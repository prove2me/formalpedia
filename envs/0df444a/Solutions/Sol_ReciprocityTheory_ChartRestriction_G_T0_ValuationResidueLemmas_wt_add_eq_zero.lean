-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.wt_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:15:17.306704+00:00
-- url     : https://prove2.me/submissions/1068153d-521a-4c8f-b013-52e6294dd9c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
namespace ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
theorem _root_.solution {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 := by
  induction a using WithTop.recTopCoe with
  | top => simp at h
  | coe x =>
    induction b using WithTop.recTopCoe with
    | top => simp at h
    | coe y =>
      have hx : (0 : ℤ) ≤ x := by exact_mod_cast ha
      have hy : (0 : ℤ) ≤ y := by exact_mod_cast hb
      have hxy : x + y = 0 := by exact_mod_cast h
      have hx0 : x = 0 := by omega
      rw [hx0]
      rfl
end ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.wt_nonneg_of_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:43.564301+00:00
-- url     : https://prove2.me/submissions/1fa4f957-850b-4156-8a93-9e5a0e38e23c

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
theorem _root_.solution {a b c : WithTop ℤ} (hb : b ≠ ⊤) (h : a + b = c) (hc : b ≤ c) : 0 ≤ a := by
  induction b using WithTop.recTopCoe with
  | top => exact absurd rfl hb
  | coe y =>
    induction a using WithTop.recTopCoe with
    | top => exact le_top
    | coe x =>
      rw [← h] at hc
      have hyx : y ≤ x + y := by exact_mod_cast hc
      have hx : (0 : ℤ) ≤ x := by omega
      exact_mod_cast hx
end ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas

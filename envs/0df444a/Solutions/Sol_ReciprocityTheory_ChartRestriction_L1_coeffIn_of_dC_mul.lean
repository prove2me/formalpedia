-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.coeffIn_of_dC_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:41:08.718312+00:00
-- url     : https://prove2.me/submissions/b03eb5f4-0a1c-4b1e-89f5-0ccd5294f53b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_exists_dC_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (R : Subring ℂ) (H : PowerSeries ℂ) (h : CoeffIn R (dC * H)) : CoeffIn R H := by
  obtain ⟨v, -, hv⟩ := exists_dC_inv
  intro n
  rw [← PowerSeries.coeff_succ_X_mul, hv H, PowerSeries.coeff_mul]
  refine sum_mem fun x _ => mul_mem ?_ (h x.2)
  rw [PowerSeries.coeff_map, eq_intCast]
  exact intCast_mem _ _
end ReciprocityTheory.ChartRestriction.L1

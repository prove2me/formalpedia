-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.ev_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:50.735649+00:00
-- url     : https://prove2.me/submissions/e18ef6bb-26df-4c3d-9955-e7b7242b9846

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_summable_norm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_mul_term

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
theorem _root_.solution {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) {x : ℂ} (hx : ‖x‖ < 1) :
    ev (f * g) x = ev f x * ev g x := by
  unfold ev
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (hf.summable_norm hx)
    (hg.summable_norm hx)]
  exact tsum_congr fun n => coeff_mul_term f g x n
end ReciprocityTheory.ChartRestriction.L1

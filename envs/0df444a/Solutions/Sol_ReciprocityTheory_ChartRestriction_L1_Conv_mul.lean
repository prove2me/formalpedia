-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Conv.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:49.163321+00:00
-- url     : https://prove2.me/submissions/3e9fe240-f730-48b9-8735-3ca3a5f75f6f

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
namespace Conv
theorem _root_.solution {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) : Conv (f * g) := by
  intro x hx
  refine (summable_norm_sum_mul_antidiagonal_of_summable_norm (hf.summable_norm hx)
    (hg.summable_norm hx)).congr fun n => ?_
  beta_reduce
  rw [← coeff_mul_term, norm_mul, norm_pow]
end Conv
end ReciprocityTheory.ChartRestriction.L1

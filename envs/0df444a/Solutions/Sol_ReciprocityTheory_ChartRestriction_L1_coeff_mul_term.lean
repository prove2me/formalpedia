-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.coeff_mul_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:29.890313+00:00
-- url     : https://prove2.me/submissions/42c7fe8f-b0da-4462-b02d-ac00976906c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer

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
theorem _root_.solution (f g : PowerSeries ℂ) (x : ℂ) (n : ℕ) :
    PowerSeries.coeff n (f * g) * x ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * x ^ kl.1) * (PowerSeries.coeff kl.2 g * x ^ kl.2) := by
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl]
  ring
end ReciprocityTheory.ChartRestriction.L1

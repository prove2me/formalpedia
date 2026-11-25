-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.psiM_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:38:59.29465+00:00
-- url     : https://prove2.me/submissions/144e16f2-b7ff-4c62-af36-27579979cc68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (f : MonoidAlgebra ℤ (muM l)) : psiM l f ∈ Rmu l := by
  rw [psiM, MonoidAlgebra.lift_apply]
  exact Subring.sum_mem _ fun a _ => Subring.zsmul_mem _ (Subring.subset_closure (a ^ l).2) _
end ReciprocityTheory.ChartRestriction.L1

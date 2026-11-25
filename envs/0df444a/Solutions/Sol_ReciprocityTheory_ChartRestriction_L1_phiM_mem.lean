-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.phiM_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:39:10.451043+00:00
-- url     : https://prove2.me/submissions/b4152338-c5df-4a07-9e56-360cc66647b0

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
theorem _root_.solution (f : MonoidAlgebra ℤ (muM l)) : phiM l f ∈ Rmu l := by
  rw [phiM, MonoidAlgebra.lift_apply]
  exact Subring.sum_mem _ fun a _ => Subring.zsmul_mem _ (Subring.subset_closure a.2) _
end ReciprocityTheory.ChartRestriction.L1

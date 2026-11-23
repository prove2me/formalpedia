-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.CoeffIn.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:49.43609+00:00
-- url     : https://prove2.me/submissions/1c42b413-e25a-479a-af0e-bb1d43bd206a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul


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
namespace CoeffIn
theorem _root_.solution {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) (n : ℕ) : CoeffIn R (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.one R
  | succ n ih =>
    rw [pow_succ]
    exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.mul ih hf
end CoeffIn
end ReciprocityTheory.ChartRestriction.L1

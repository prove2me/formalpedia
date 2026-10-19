-- Prove2me | solution 1 for SpherePacking.exists_maximal_sphericalCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/399de871-d907-4ac8-bdf7-526b17b5b80e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_exists_maximal_sphericalCode
import Theorems.Thm_SpherePacking_sphericalCodeNumber_eq_codes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open SpherePacking
namespace SpherePacking
theorem _root_.solution {n : ℕ} {s : ℝ} (hs : s < 1) :
    ∃ C : SphericalCode n s,
      (C.points.card : ℕ∞) = sphericalCodeNumber n s := by
  obtain ⟨C, hC⟩ := MetricCodes.exists_maximal_sphericalCode hs
  refine ⟨SphericalCode.ofCodes C, ?_⟩
  simpa [sphericalCodeNumber_eq_codes] using hC
end SpherePacking

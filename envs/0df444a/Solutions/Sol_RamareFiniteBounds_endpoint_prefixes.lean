-- Prove2me | solution 1 for RamareFiniteBounds.endpoint_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T20:15:26.6173+00:00
-- url     : https://prove2.me/submissions/babcdc93-6bb6-4d0d-821c-7cc9c4025264

import Theorems.Thm_RamareFiniteBounds_endpoint_prefixes_le_80257
import Theorems.Thm_RamareFiniteBounds_endpoint_prefixes_gt_80257

set_option autoImplicit false

/-- Reassemble the two explicit endpoint ranges at their common cutoff. -/
theorem solution :
    ∀ e ∈ RamareFiniteBounds.logEndpoints,
      RamareFiniteBounds.roundedPrefix 10000000000 e.hi = e.upper := by
  have hcut :
      RamareFiniteBounds.roundedPrefix 10000000000 80257 = 126251687858 := by
    have hmem :
        (⟨69862, 80257, 16, 126251687858⟩ : RamareFiniteBounds.LogEndpoint) ∈
          RamareFiniteBounds.logEndpoints := by
      decide +kernel
    exact RamareFiniteBounds.endpoint_prefixes_le_80257
      ⟨69862, 80257, 16, 126251687858⟩ hmem (by decide)
  intro e he
  by_cases hle : e.hi ≤ 80257
  · exact RamareFiniteBounds.endpoint_prefixes_le_80257 e he hle
  · exact RamareFiniteBounds.endpoint_prefixes_gt_80257 hcut e he (lt_of_not_ge hle)

#print axioms solution

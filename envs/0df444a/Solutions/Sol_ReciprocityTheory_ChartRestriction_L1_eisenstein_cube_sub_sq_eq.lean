-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.eisenstein_cube_sub_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:15.94068+00:00
-- url     : https://prove2.me/submissions/8c473d61-463f-47c9-b1f5-139923776986

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_eisensteinFourInt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_eisensteinSixInt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_tZ_mul

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
theorem _root_.solution : e4Z ^ 3 - e6Z ^ 2 = PowerSeries.C (1728 : ℤ) *
    (tZ + PowerSeries.C (100 : ℤ) * s3Z ^ 2 + PowerSeries.C (8000 : ℤ) * s3Z ^ 3
      - PowerSeries.C (147 : ℤ) * s5Z ^ 2) := by
  have h := tZ_mul
  rw [eisensteinFourInt_eq, eisensteinSixInt_eq]
  simp only [map_ofNat] at h ⊢
  linear_combination (-144 : PowerSeries ℤ) * h
end ReciprocityTheory.ChartRestriction.L1

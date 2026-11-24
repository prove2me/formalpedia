-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_xc_ne_zero_d6f9f1c37a1d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:17.788857+00:00
-- url     : https://prove2.me/submissions/74295602-6f6a-4dbe-9265-6796600e64e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjArithVar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectiveArithmeticVariety
variable (K : Type) [Field K] [NumberField K] (n : ℕ)
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights.ProjectiveArithmeticVariety
theorem _root_.solution (j : Fin (n + 1)) : xc K n j ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_ne_zero j)
end GroundTheory.Heights₂.Heights.ProjectiveArithmeticVariety

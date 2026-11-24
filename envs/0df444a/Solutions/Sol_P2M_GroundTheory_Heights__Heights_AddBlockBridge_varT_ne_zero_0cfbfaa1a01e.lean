-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockBridge_varT_ne_zero_0cfbfaa1a01e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:11.698331+00:00
-- url     : https://prove2.me/submissions/bccfa122-80b6-47b8-83a9-c1c809c994cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockBridge
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.AddBlockBridge
theorem _root_.solution (k : ι) : varT (Ω := Ω) k ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial ι Ω) (ConeField ι Ω))).mpr (X_ne_zero k)
end GroundTheory.Heights₂.Heights.AddBlockBridge

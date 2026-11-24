-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockBridge_coneHom_X_aa17785c5646
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:16.086615+00:00
-- url     : https://prove2.me/submissions/5e89a619-7eb9-43ea-bbac-77079ae0000a

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
theorem _root_.solution (y : Coord n → Ω) (v : Coord n) : coneHom y (X v) = constMap ι (y v) * varT v.1 := by
  rw [coneHom_apply]
  simp [Geo.mConeMap, constMap, varT]
end GroundTheory.Heights₂.Heights.AddBlockBridge

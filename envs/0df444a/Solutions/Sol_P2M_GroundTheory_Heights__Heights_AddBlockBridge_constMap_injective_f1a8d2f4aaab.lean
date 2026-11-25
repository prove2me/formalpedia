-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockBridge_constMap_injective_f1a8d2f4aaab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:07.723197+00:00
-- url     : https://prove2.me/submissions/f5a7afda-e61f-4124-aa83-4ba92dc5459d

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
theorem _root_.solution : Function.Injective (constMap (Ω := Ω) ι) :=
  (IsFractionRing.injective (MvPolynomial ι Ω) (ConeField ι Ω)).comp (C_injective _ _)
end GroundTheory.Heights₂.Heights.AddBlockBridge

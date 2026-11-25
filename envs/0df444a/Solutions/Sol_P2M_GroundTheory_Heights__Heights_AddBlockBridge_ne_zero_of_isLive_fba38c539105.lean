-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockBridge_ne_zero_of_isLive_fba38c539105
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:15.737822+00:00
-- url     : https://prove2.me/submissions/6180def3-c7a9-4a00-9401-3d9622ef5d67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_coneHom_X_aa17785c5646

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
variable (P : ArithVariety n) (y : Coord n → Ω) (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)
include hP
namespace GroundTheory.Heights₂.Heights.AddBlockBridge
theorem _root_.solution {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (k : ι) : y ⟨k, c k⟩ ≠ 0 := by
  intro hy
  apply hc k
  rw [hP, mem_mCoordIdeal_iff, coneHom_X, hy, map_zero, zero_mul]
end GroundTheory.Heights₂.Heights.AddBlockBridge

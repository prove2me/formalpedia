-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_nrm_sub_le_of_le__5fdbf955fbfb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:33.247211+00:00
-- url     : https://prove2.me/submissions/71795523-4ea8-4ebc-af9e-67ded85eeb24

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
variable {K}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {x y z : Ω} {r : ℝ} (h₁ : nrm K (x - y) ≤ r) (h₂ : nrm K (y - z) ≤ r) :
    nrm K (x - z) ≤ r := by
  have : x - z = (x - y) + (y - z) := by ring
  rw [this]
  exact nrm_add_le_of_le h₁ h₂
end GroundTheory.PAdicHodge

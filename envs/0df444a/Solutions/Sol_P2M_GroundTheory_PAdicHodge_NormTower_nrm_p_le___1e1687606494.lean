-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_NormTower_nrm_p_le___1e1687606494
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:07:52.348874+00:00
-- url     : https://prove2.me/submissions/ac307ed8-9d04-49bc-aaf7-227c46e99b64

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower

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
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] (p : ℕ)
open GroundTheory.PAdicHodge.NormTower
variable {K Ω p} (t : NormTower K Ω p)
namespace GroundTheory.PAdicHodge.NormTower
theorem _root_.solution : nrm K (p : Ω) ≤ t.ρ := le_max_right _ _
end GroundTheory.PAdicHodge.NormTower

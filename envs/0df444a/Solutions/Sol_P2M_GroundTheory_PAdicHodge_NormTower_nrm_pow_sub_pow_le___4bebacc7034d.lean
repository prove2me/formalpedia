-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_NormTower_nrm_pow_sub_pow_le___4bebacc7034d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:18.221459+00:00
-- url     : https://prove2.me/submissions/f7c8c4d4-b2f0-4d48-a4a2-f12d742c2c3d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_pow_sub_pow_le

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
theorem _root_.solution {a b : Ω} (ha : nrm K a ≤ 1) (hb : nrm K b ≤ 1)
    (hab : nrm K (a - b) ≤ t.ρ) (m : ℕ) : nrm K (a ^ m - b ^ m) ≤ t.ρ :=
  (nrm_pow_sub_pow_le ha hb m).trans hab
end GroundTheory.PAdicHodge.NormTower

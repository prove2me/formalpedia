-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:33.261437+00:00
-- url     : https://prove2.me/submissions/a3a10d18-de16-4d11-a078-e682eb228fb6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDensLevi

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights.Targets.ProjPotDens
open ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotDens
theorem _root_.solution (k : K) (z : (Σ k, ι k) → ℂ) (i : ι k) :
    blockCLM k z i = z ⟨k, i⟩ := rfl
end GroundTheory.Heights₂.Heights.Targets.ProjPotDens

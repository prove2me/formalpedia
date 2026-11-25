-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_TeichLift_algebraMap___mem_Econ_e50aaa839a7f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:00.363802+00:00
-- url     : https://prove2.me/submissions/2eff9169-db63-422f-a119-761f282737cc

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_zcoeff___pow_1768146d2888
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_mem_Econ

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
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ : ℝ}
variable {b c : T.B}
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution (ρ : Set.Ioo (0 : ℝ) 1) : algebraMap Γ T.B T.π ∈ T.Econ ρ := by
  rw [mem_Econ, coeffB_algebraMap, ← pow_one T.π, zcoeff_π_pow]; exact convergesAt_pi_single _ _ _
end GroundTheory.PAdicHodge.TeichLift

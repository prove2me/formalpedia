-- Prove2me | solution 1 for P2M_GroundTheory_PAdicHodge_TeichLift_sub_teich_eq___mul_tail_219974f30227
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:43.791774+00:00
-- url     : https://prove2.me/submissions/aaab4abd-a4ab-4304-9707-3e666e8c560b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich

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
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution (x : Γ) : x - T.teich (T.red x) = T.π * T.tail x :=
  (T.red_eq_zero_iff.1 (T.red_sub_teich_red x)).choose_spec
end GroundTheory.PAdicHodge.TeichLift

-- Prove2me | solution 1 for TunnellMap.RecordDA.heldGenerated_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:35:39.749323+00:00
-- url     : https://prove2.me/submissions/eab22868-0eeb-4eca-81be-509b0bf812af

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
import Theorems.Thm_TunnellMap_RecordDA_heldGenerated_step

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n) (frames : FrameFamily n) :
    ∀ {E : DARun n}, Sim hnpos frames E → HeldGenerated frames E →
      HeldGenerated frames (run frames E) := by
  intro E
  induction E using run.induct (frames := frames) with
  | case1 E hstep =>
      intro _ hHG
      rw [run, hstep]
      exact hHG
  | case2 E E' hstep ih =>
      intro hSim hHG
      rw [run, hstep]
      exact ih (step_some_sim hn hnpos frames hSim hstep).1
        (heldGenerated_step hnpos frames hSim hHG hstep)
end TunnellMap.RecordDA

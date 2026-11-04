-- Prove2me | solution 1 for ThreeSum.LightCyclic.program_procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:34:38.139702+00:00
-- url     : https://prove2.me/submissions/611fc8d8-b245-467d-8ea0-9071805969ac

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCyclic

set_option autoImplicit false
open ThreeSum ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCyclic
theorem _root_.solution : LightKaratsuba.Procs program 1 2 3 4 := ⟨rfl, rfl, rfl, rfl⟩
end ThreeSum.LightCyclic

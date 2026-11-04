-- Prove2me | solution 1 for ThreeSum.LightResidues.residue_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:31:37.959461+00:00
-- url     : https://prove2.me/submissions/ed503d4d-5c5a-47c4-8857-0421b685c75c

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightResidues
import Theorems.Thm_ThreeSum_LightResidues_residue_cast

set_option autoImplicit false
open ThreeSum ThreeSum.LightResidues
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightResidues
theorem _root_.solution {p : ℕ} (hp : 0 < p) (c x : ℤ) : residue p c x < p := by
  have h := Int.emod_lt_of_pos (c * x) (by exact_mod_cast hp : (0 : ℤ) < p)
  rw [← residue_cast hp] at h
  exact_mod_cast h
end ThreeSum.LightResidues

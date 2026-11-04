-- Prove2me | solution 1 for ThreeSum.LightIrreducibleFinder.chosen_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:29.783981+00:00
-- url     : https://prove2.me/submissions/5ac02b11-60f9-4934-89ba-4faddf651d21

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Definitions.Def_Submission_ThreeSum_LightArgumentTable
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_degreeFlag_irreducible
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_pick_good
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_pick_le
import Theorems.Thm_ThreeSum_LightTernaryRowSelector_pick_pos_iff
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_exists_irreducible_code


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightIrreducibleFinder
open Light ThreeSum.LightExtensionFactorPredicate
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {lim : Limits}
open TernaryExtensionEncoding
namespace ThreeSum.LightIrreducibleFinder
theorem _root_.solution (C : Layout) [Fact C.p.Prime] (hd : 0<C.dim) :
    0<chosen C (C.p^C.dim) (C.p^C.dim) ∧
    chosen C (C.p^C.dim) (C.p^C.dim)≤C.p^C.dim ∧
    Irreducible (monicOfCode (p := C.p) C.dim (chosen C (C.p^C.dim) (C.p^C.dim)-1)) := by
  have equiv (c : ℕ) (hc : c<C.p^C.dim) :
      accepted C (C.p^C.dim) c ↔ Irreducible (monicOfCode (p := C.p) C.dim c) := by
    exact degreeFlag_irreducible C hd hc
  obtain ⟨c,hc,hi⟩ := exists_irreducible_code (p := C.p) C.dim hd
  have hpos : 0<chosen C (C.p^C.dim) (C.p^C.dim) :=
    (LightTernaryRowSelector.pick_pos_iff _ _).mpr ⟨c,hc,(equiv c hc).mpr hi⟩
  have hle : chosen C (C.p^C.dim) (C.p^C.dim)≤C.p^C.dim := LightTernaryRowSelector.pick_le _ _
  exact ⟨hpos,hle,(equiv _ (by omega)).mp (LightTernaryRowSelector.pick_good _ _ hpos)⟩
end ThreeSum.LightIrreducibleFinder

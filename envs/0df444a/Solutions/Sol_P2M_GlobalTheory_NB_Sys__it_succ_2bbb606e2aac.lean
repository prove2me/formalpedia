-- Prove2me | solution 1 for P2M_GlobalTheory_NB_Sys__it_succ_2bbb606e2aac
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:00:03.932472+00:00
-- url     : https://prove2.me/submissions/2948e57e-d780-4337-94b6-a01b8b669d9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB
attribute [instance] Fr.eeRing Fr.eeAlgA Fr.eeAlgO Fr.eeTow
open GlobalTheory.NB.Sys
variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r : ℕ} (S : Sys R n r)
theorem _root_.solution (c : ZMod n) (j : ℕ) :
    S.φit c (j + 1) = (S.φl (c + (j : ZMod n) + 1)).comp (S.φit c j) := by
  rfl




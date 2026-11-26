-- Prove2me | solution 1 for P2M_GlobalTheory_NB_Sys__0it_succ_d08c2df5bfc9
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:00:02.861004+00:00
-- url     : https://prove2.me/submissions/0aad3b72-bd72-4214-ba1d-604fa309afd0

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
variable [IsDomain O]
theorem _root_.solution (c : ZMod n) (j : ℕ) :
    S.φ0it c (j + 1) = S.φ0 (c + (j : ZMod n) + 1) * S.φ0it c j := by
  rfl




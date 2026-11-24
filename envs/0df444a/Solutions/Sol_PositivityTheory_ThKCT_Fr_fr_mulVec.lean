-- Prove2me | solution 1 for PositivityTheory.ThKCT.Fr.fr_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:02:33.572458+00:00
-- url     : https://prove2.me/submissions/aa2e67bd-1c70-403b-a06f-84b7bd26c933

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_ColsOfMul
import Theorems.Thm_PositivityTheory_ThKCT_Fr_IsFr_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Fr
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {ε : R} {A' : Matrix (e ⊕ Fin 2) d R} {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}
omit [DecidableEq d] [DecidableEq e]
namespace PositivityTheory.ThKCT.Fr
theorem _root_.solution (u : e → R) (s t : R) : fr ι x y *ᵥ Sum.elim u ![s, t] = ι *ᵥ u + s • x + t • y := by
  ext i
  simp [fr, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring
end PositivityTheory.ThKCT.Fr

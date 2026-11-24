-- Prove2me | solution 1 for PositivityTheory.ThKCT.Fr.IsFr.ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:49:08.412233+00:00
-- url     : https://prove2.me/submissions/6312c2bb-bd1c-4113-b0d8-67ab81c6ddf6

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_ColsOfMul

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
namespace PositivityTheory.ThKCT.Fr
namespace IsFr
theorem _root_.solution (h : IsFr c ε J J₁ ι x y A') {m m' : Matrix d d R} (h1 : m *ᵥ x = m' *ᵥ x) (h2 : m *ᵥ y = m' *ᵥ y)
    (h3 : m * ι = m' * ι) : m = m' := by
  have hf : m * fr ι x y = m' * fr ι x y := by
    ext i j
    rcases j with j | j
    · have := congrFun (congrFun h3 i) j
      simpa [fr, Matrix.mul_apply] using this
    · fin_cases j
      · have := congrFun h1 i
        simpa [fr, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
      · have := congrFun h2 i
        simpa [fr, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  calc m = m * (fr ι x y * A') := by rw [h.inv1, Matrix.mul_one]
    _ = m' * (fr ι x y * A') := by rw [← Matrix.mul_assoc, hf, Matrix.mul_assoc]
    _ = m' := by rw [h.inv1, Matrix.mul_one]
end IsFr
end PositivityTheory.ThKCT.Fr

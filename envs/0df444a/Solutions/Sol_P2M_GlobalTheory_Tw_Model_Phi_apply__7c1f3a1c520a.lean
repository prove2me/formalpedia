-- Prove2me | solution 1 for P2M_GlobalTheory_Tw_Model_Phi_apply__7c1f3a1c520a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:16.46759+00:00
-- url     : https://prove2.me/submissions/2d66e708-294f-47d1-97ca-4bb4cbd062c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.Model
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
omit [StarRing R]
namespace GlobalTheory.Tw.Model
theorem _root_.solution (i j : Fin n) : Phi n R i j = if j = i.rev then (-1) ^ (i : ℕ) else 0 := by
  simp only [Phi, Matrix.of_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff, Fin.val_rev]
  have := i.2
  have := j.2
  omega
end GlobalTheory.Tw.Model

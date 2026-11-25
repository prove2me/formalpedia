-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeffMatrix_one_gramPolyMinor_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:40:58.625364+00:00
-- url     : https://prove2.me/submissions/625bbbe9-317f-4192-bf9e-38c444578561

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_one_gramPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ)
    (a b : Fin m) : cf 1 (Gm N hd m hm v) a b =
      (hd (Fin.castLE hm a) : ℂ) * zMat N v (Fin.castLE hm a) (Fin.castLE hm b) +
        star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) * (hd (Fin.castLE hm b) : ℂ) := by
  show cf 1 (gP N hd v) _ _ = _
  rw [coeffMatrix_one_gramPoly]
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, conjTranspose_apply]
end ReciprocityTheory.AnForm.P

-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.coeffMatrix_zero_gramPolyMinor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:33:58.156896+00:00
-- url     : https://prove2.me/submissions/722d0377-1ec6-4c02-8fe0-796e66d78961

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Theorems.Thm_ReciprocityTheory_AnForm_P_coeffMatrix_zero_gramPoly

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
theorem _root_.solution (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    cf 0 (Gm N hd m hm v) = diagonal fun a => (hd (Fin.castLE hm a) : ℂ) := by
  show (cf 0 (gP N hd v)).submatrix _ _ = _
  rw [coeffMatrix_zero_gramPoly, submatrix_diagonal _ _ (Fin.castLE_injective hm)]
  rfl
end ReciprocityTheory.AnForm.P

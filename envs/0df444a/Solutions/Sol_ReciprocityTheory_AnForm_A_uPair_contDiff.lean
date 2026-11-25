-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.uPair_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:08.369866+00:00
-- url     : https://prove2.me/submissions/d2664a8b-d7a2-4b20-af80-fc47904fb212

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Theorems.Thm_ReciprocityTheory_AnForm_A_contDiff_insertNth_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Laplacian Pointwise
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (j : Fin (D + 1)) {u : (Fin (D + 1) → ℂ) → ℝ}
    (hu : ContDiff ℝ 2 u) : ContDiff ℝ 2 (uPair j u) := by
  exact hu.comp (contDiff_insertNth_pair j)
end ReciprocityTheory.AnForm.A

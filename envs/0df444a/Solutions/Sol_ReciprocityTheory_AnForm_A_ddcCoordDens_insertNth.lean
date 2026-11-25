-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.ddcCoordDens_insertNth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:20.063264+00:00
-- url     : https://prove2.me/submissions/5d4d187c-96f7-47f5-9e80-6424425ce6cb

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
import Theorems.Thm_ReciprocityTheory_AnForm_A_levi_insertNth

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
    (hu : ContDiff ℝ 2 u) (w : Fin D → ℂ) (ζ : ℂ) :
    ddcCoordDens j u (Fin.insertNth j ζ w) =
      (1 / (2 * Real.pi)) * Δ (fun ζ' => uPair j u (ζ', w)) ζ := by
  rw [ddcCoordDens, levi_insertNth j u hu w ζ]
  simp only [uPair]
  ring
end ReciprocityTheory.AnForm.A

-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.uPair_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:10.947564+00:00
-- url     : https://prove2.me/submissions/6c3f5e7e-b2a0-4827-af17-89ebbf8e1ed8

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
    (hs : HasCompactSupport u) : HasCompactSupport (uPair j u) := by
  let h : ℂ × (Fin D → ℂ) ≃ₜ (Fin (D + 1) → ℂ) :=
    { toEquiv := Fin.insertNthEquiv (fun _ : Fin (D + 1) => ℂ) j
      continuous_toFun := (contDiff_insertNth_pair j).continuous
      continuous_invFun := by
        change Continuous fun z : Fin (D + 1) → ℂ => (z j, fun i => z (j.succAbove i))
        exact (continuous_apply j).prodMk (continuous_pi fun i => continuous_apply _) }
  exact hs.comp_homeomorph h
end ReciprocityTheory.AnForm.A

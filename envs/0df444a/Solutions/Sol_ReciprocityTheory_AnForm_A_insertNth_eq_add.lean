-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.insertNth_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:29.646006+00:00
-- url     : https://prove2.me/submissions/f3df1ca8-1546-49bc-8e13-b38a19ed794a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord

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
theorem _root_.solution {D : ℕ} (j : Fin (D + 1)) (w : Fin D → ℂ) (ζ : ℂ) :
    Fin.insertNth j ζ w = Fin.insertNth j (0 : ℂ) w + (Pi.single j ζ : Fin (D + 1) → ℂ) := by
  ext k
  by_cases hk : k = j
  · subst hk
    simp
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hk
    simp [Pi.single_apply]
end ReciprocityTheory.AnForm.A

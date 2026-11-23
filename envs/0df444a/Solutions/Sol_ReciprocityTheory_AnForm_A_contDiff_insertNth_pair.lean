-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.contDiff_insertNth_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:51.206189+00:00
-- url     : https://prove2.me/submissions/0a024696-5439-41e9-9df3-4ca8a2b54007

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
theorem _root_.solution {D : ℕ} (j : Fin (D + 1)) :
    ContDiff ℝ 2 (fun q : ℂ × (Fin D → ℂ) => (Fin.insertNth j q.1 q.2 : Fin (D + 1) → ℂ)) := by
  refine contDiff_pi.2 fun k => ?_
  by_cases hk : k = j
  · subst hk
    have e : (fun q : ℂ × (Fin D → ℂ) => (Fin.insertNth k q.1 q.2 : Fin (D + 1) → ℂ) k) =
        fun q => q.1 := funext fun q => Fin.insertNth_apply_same _ _ _
    rw [e]
    exact contDiff_fst
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hk
    have e : (fun q : ℂ × (Fin D → ℂ) => (Fin.insertNth j q.1 q.2 : Fin (D + 1) → ℂ) (j.succAbove i)) =
        fun q => q.2 i := funext fun q => Fin.insertNth_apply_succAbove _ _ _ _
    rw [e]
    exact (contDiff_apply ℝ ℂ i).comp contDiff_snd
end ReciprocityTheory.AnForm.A

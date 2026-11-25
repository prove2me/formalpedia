-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.det_finsetSum_eq_sum_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:50.104745+00:00
-- url     : https://prove2.me/submissions/6bf4156f-6156-47cc-aa69-beb540232a2f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (S : Finset (Fin D)) :
    (∑ k ∈ S, A k).det = ∑ r : Fin D → Fin D,
      if (∀ i, r i ∈ S) then (Matrix.of fun i => A (r i) i).det else 0 := by
  classical
  have h1 : (∑ k ∈ S, A k) = fun i => ∑ k ∈ S, A k i := by
    ext i j; simp [Matrix.sum_apply]
  have h2 := (Matrix.detRowAlternating : (Fin D → ℂ) [⋀^Fin D]→ₗ[ℂ] ℂ).toMultilinearMap.map_sum_finset
    (fun i k => A k i) (fun _ => S)
  rw [h1]
  refine h2.trans ?_
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext r; simp [Fintype.mem_piFinset]
  · intro r _; rfl
end ReciprocityTheory.AnForm.A

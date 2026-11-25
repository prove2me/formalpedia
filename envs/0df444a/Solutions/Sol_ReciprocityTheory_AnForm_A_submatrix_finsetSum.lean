-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.submatrix_finsetSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:50.031914+00:00
-- url     : https://prove2.me/submissions/b2d232cd-df73-48ce-90e2-0bdf06a75e93

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
theorem _root_.solution {ι : Type*} {n m : ℕ} (f : Fin m → Fin n)
    (B : ι → Matrix (Fin n) (Fin n) ℂ) (S : Finset ι) :
    (∑ k ∈ S, B k).submatrix f f = ∑ k ∈ S, (B k).submatrix f f := by
  ext a b; simp [Matrix.sum_apply]
end ReciprocityTheory.AnForm.A

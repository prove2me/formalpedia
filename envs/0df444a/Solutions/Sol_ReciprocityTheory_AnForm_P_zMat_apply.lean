-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.zMat_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:15.612307+00:00
-- url     : https://prove2.me/submissions/735c7fa3-83d4-494d-81a8-9a28849d2948

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB

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
theorem _root_.solution (N : ℕ) (z : Pairs N → ℂ) (i j : Fin N) :
    zMat N z i j = if h : j < i then z ⟨(j, i), h⟩ else 0 := by
  simp only [zMat, Matrix.sum_apply, Matrix.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(j, i), h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hb (Subtype.ext (Prod.ext h2 h1))
    · simp
  · refine Finset.sum_eq_zero fun p _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (by rw [← h1, ← h2]; exact p.2)
end ReciprocityTheory.AnForm.P

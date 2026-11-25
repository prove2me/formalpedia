-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.det_diff_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:33:49.745358+00:00
-- url     : https://prove2.me/submissions/3e13a729-57bc-4d94-8f02-1ca7182bc404

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution {k : ℕ} (B B' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (h : ∀ a b, ¬ (a = Fin.last k ∧ b = Fin.last k) → B a b = B' a b) :
    B.det - B'.det = (B (Fin.last k) (Fin.last k) - B' (Fin.last k) (Fin.last k)) *
      (B.submatrix Fin.castSucc Fin.castSucc).det := by
  have hrows : ∀ j : Fin (k + 1), B.submatrix (Fin.last k).succAbove j.succAbove =
      B'.submatrix (Fin.last k).succAbove j.succAbove := by
    intro j
    ext a b
    refine h _ _ fun hab => ?_
    have := hab.1
    rw [Fin.succAbove_last] at this
    exact Fin.castSucc_ne_last a this
  rw [Matrix.det_succ_row B (Fin.last k), Matrix.det_succ_row B' (Fin.last k),
    ← Finset.sum_sub_distrib, Finset.sum_eq_single (Fin.last k)]
  · rw [hrows (Fin.last k)]
    have hs : (-1 : ℂ) ^ ((Fin.last k : ℕ) + (Fin.last k : ℕ)) = 1 := by
      rw [Fin.val_last, ← two_mul, pow_mul]; simp
    have hc : B.submatrix Fin.castSucc Fin.castSucc = B'.submatrix Fin.castSucc Fin.castSucc := by
      simpa [Fin.succAbove_last] using hrows (Fin.last k)
    rw [hs, Fin.succAbove_last, hc]
    ring
  · intro j _ hj
    have hrow : B (Fin.last k) j = B' (Fin.last k) j := h _ _ fun hab => hj hab.2
    rw [hrow, hrows j]
    ring
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI

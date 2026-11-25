-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.toMatrix_luD_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:53.944798+00:00
-- url     : https://prove2.me/submissions/5139ef1b-c1c3-4242-8f17-78a5946986f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_luD_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (w : Ix ι r → ℂ) (i : Ix ι r) :
    LinearMap.toMatrix' (luD w) i i = if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1 := by
  obtain ⟨τ, a, b⟩ := i
  rw [LinearMap.toMatrix'_apply, luD_apply]
  have hs1 : ∀ k : Fin r, sl (Pi.single (τ, a, b) (1 : ℂ)) τ a k * up w τ k b =
      if k = b then (if b < a then w (τ, b, b) else 0) else 0 := by
    intro k
    by_cases hkb : k = b
    · subst hkb
      by_cases hka : k < a <;> simp [Pi.single_apply, sl, up, hka]
    · simp [Pi.single_apply, sl, hkb]
  have hs2 : ∀ k : Fin r, (1 + sl w τ) a k * up (Pi.single (τ, a, b) (1 : ℂ)) τ k b =
      if k = a then (if b < a then 0 else 1) else 0 := by
    intro k
    by_cases hka : k = a
    · subst hka
      by_cases hbk : b < k <;> simp [Pi.single_apply, sl, up, hbk]
    · simp [Pi.single_apply, up, hka]
  rw [Finset.sum_congr rfl (fun k _ => hs1 k), Finset.sum_congr rfl (fun k _ => hs2 k)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI

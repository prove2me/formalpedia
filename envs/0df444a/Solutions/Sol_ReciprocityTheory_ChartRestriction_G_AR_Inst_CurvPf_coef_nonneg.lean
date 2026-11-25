-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.coef_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:19.324778+00:00
-- url     : https://prove2.me/submissions/36c6ce2a-7216-4d5e-97c5-de4b274e61bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_TelePoint
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoefNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution (la : Wt X.Ψ r) (hdom : X.IsDominant la) (τ : X.Ψ) (a j : Fin r) (h : (a : ℕ) < j) :
    0 ≤ coef X la τ a j := by
  obtain ⟨h1, h2', h3⟩ := hdom τ
  have haj : a < j := Fin.lt_def.2 h
  unfold coef Dsg sgn
  by_cases hj : (j : ℕ) < X.p0
  · have ha : (a : ℕ) < X.p0 := by omega
    have hz := h1 a j haj.le hj
    have hr : (la τ j : ℝ) ≤ la τ a := by exact_mod_cast hz
    rw [if_pos hj, if_pos ha]
    norm_num
    linarith
  · by_cases ha : (a : ℕ) < X.p0
    · have hz := h3 a j ha (by omega)
      have hr : (la τ a : ℝ) ≤ la τ j := by exact_mod_cast hz
      rw [if_neg hj, if_pos ha]
      norm_num
      linarith
    · have hz := h2' a j (by omega) haj.le
      have hr : (la τ j : ℝ) ≤ la τ a := by exact_mod_cast hz
      rw [if_neg hj, if_neg ha]
      norm_num
      linarith
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

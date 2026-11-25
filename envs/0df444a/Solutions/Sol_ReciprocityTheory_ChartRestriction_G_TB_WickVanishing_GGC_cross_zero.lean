-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.cross_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:38:40.018278+00:00
-- url     : https://prove2.me/submissions/ec9cb7fb-4405-4428-bb78-b706d43abe2a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_sv_star
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_Gy_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_sv_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {r : ℕ} (p0 : ℕ)
variable {p0}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
theorem _root_.solution {y : Matrix (Fin r) (Fin r) ℂ} (h : Ok p0 y) {a b : Fin r}
    (hab : ¬((a : ℕ) < p0 ↔ (b : ℕ) < p0)) : Gy p0 y a b = 0 := by
  have hH := h.isHermitian
  have hG : star (Gy p0 y b a) = Gy p0 y a b := by
    rw [Gy_apply, Gy_apply, star_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [star_mul', sv_star, Complex.star_def, Complex.conj_conj]
    ring
  have h1 := (hH.apply a b).symm
  simp only [Matrix.diagonal_mul] at h1
  rw [star_mul', sv_star, hG] at h1
  have h2 : (sv p0 a - sv p0 b) * Gy p0 y a b = 0 := by rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3).symm (sv_ne hab)
  · exact h3
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC

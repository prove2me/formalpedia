-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Ms_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:42:19.08124+00:00
-- url     : https://prove2.me/submissions/e7e8e369-8fc1-491d-b2c5-1edca10456c8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_sf_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_sf_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB
open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB
theorem _root_.solution (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) (c : ℝ) (v : Fin r → ℂ) :
    Ms p0 hp N ((c : ℂ) • v) = c ^ 2 * Ms p0 hp N v := by
  have h1 : (∑ a : Fin p0, ∑ b : Fin p0, sf p0 ((c : ℂ) • v) (cl N (Fin.castLE hp a)) *
      (Ag p0 hp N)⁻¹ a b * conj (sf p0 ((c : ℂ) • v) (cl N (Fin.castLE hp b)))) =
      ((c ^ 2 : ℝ) : ℂ) * ∑ a : Fin p0, ∑ b : Fin p0, sf p0 v (cl N (Fin.castLE hp a)) *
        (Ag p0 hp N)⁻¹ a b * conj (sf p0 v (cl N (Fin.castLE hp b))) := by
    simp only [sf_smul_left, map_mul, Complex.conj_ofReal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  have h2 : sf p0 ((c : ℂ) • v) ((c : ℂ) • v) = ((c ^ 2 : ℝ) : ℂ) * sf p0 v v := by
    rw [sf_smul_left, sf_smul_right]
    push_cast
    ring
  simp only [Ms]
  rw [h1, h2, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift.maj_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:47.537978+00:00
-- url     : https://prove2.me/submissions/998fa965-9acb-4030-840a-2e4209480cea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} {X : Data E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift
theorem _root_.solution {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (k : ℝ) (v : Fin r → ℂ) :
    X.maj z τ ((k : ℂ) • v) = k ^ 2 * X.maj z τ v := by
  have hS : (∑ a : Fin X.p0, ∑ b : Fin X.p0,
      hermC τ.1 X.Gm ((k : ℂ) • v) (col (mat z τ) (Fin.castLE X.p0_le a)) * (X.gramPos z τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm ((k : ℂ) • v) (col (mat z τ) (Fin.castLE X.p0_le b)))) =
      ((k ^ 2 : ℝ) : ℂ) * ∑ a : Fin X.p0, ∑ b : Fin X.p0,
        hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le a)) * (X.gramPos z τ)⁻¹ a b *
          conj (hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le b))) := by
    simp only [hermC_smul_left, map_mul, Complex.conj_ofReal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  have hh : hermC τ.1 X.Gm ((k : ℂ) • v) ((k : ℂ) • v) = ((k ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hermC_smul_left, hermC_smul_right, Complex.conj_ofReal]
    push_cast
    ring
  simp only [Data.maj, Data.posPart]
  rw [hS, hh, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift

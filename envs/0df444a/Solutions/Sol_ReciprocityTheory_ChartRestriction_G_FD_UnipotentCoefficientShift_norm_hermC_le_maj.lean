-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift.norm_hermC_le_maj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:52:07.611625+00:00
-- url     : https://prove2.me/submissions/b8f808b0-e6ff-4ddb-809a-79ca61d7275b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_ppos_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_ppos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_sub
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sub_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_zero_left
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


section
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace UnipotentCoefficientShift
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} {X : Data E r}
private lemma maj_nonneg_of_mem_dom {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj z τ v := by
  rcases eq_or_ne v 0 with h | h
  · subst h
    simp [Data.maj, Data.posPart, hermC]
  · exact (X.maj_pos hz τ h).le
end UnipotentCoefficientShift
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} {X : Data E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift
theorem _root_.solution {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    ‖hermC τ.1 X.Gm v v‖ ≤ X.maj z τ v := by
  have hv : v = X.ppos z τ v + (v - X.ppos z τ v) := by abel
  have hPq : X.ppos z τ (v - X.ppos z τ v) = 0 := by
    rw [Data.ppos_sub, X.ppos_ppos hz, sub_self]
  have hpq : hermC τ.1 X.Gm (X.ppos z τ v) (v - X.ppos z τ v) = 0 := by
    rw [hermC_sub_right, X.hermC_ppos_left hz τ v v, sub_self]
  have hqp : hermC τ.1 X.Gm (v - X.ppos z τ v) (X.ppos z τ v) = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm (X.ppos z τ v) (v - X.ppos z τ v), hpq, map_zero]
  have hA : X.Hf z τ (X.ppos z τ v) (X.ppos z τ v) = hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) := by
    rw [Data.Hf, X.ppos_ppos hz, two_smul, add_sub_cancel_right]
  have hB : X.Hf z τ (v - X.ppos z τ v) (v - X.ppos z τ v) =
      -hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) := by
    rw [Data.Hf, hPq, smul_zero, hermC_sub_left, hermC_zero_left, zero_sub]
  have hV : X.Hf z τ v v = 2 * hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) - hermC τ.1 X.Gm v v := by
    rw [Data.Hf, hermC_sub_left, hermC_smul_left, X.hermC_ppos_left hz τ v v]
  have hvv : hermC τ.1 X.Gm v v = hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) +
      hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) := by
    conv_lhs => rw [hv]
    rw [hermC_add_left, hermC_add_right, hermC_add_right, hpq, hqp]
    ring
  have eA : hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) = (X.maj z τ (X.ppos z τ v) : ℂ) := by
    rw [← hA]; exact X.Hf_self hz τ _
  have eB : hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) = -(X.maj z τ (v - X.ppos z τ v) : ℂ) := by
    rw [← X.Hf_self hz τ, hB, neg_neg]
  have eC : ((X.maj z τ v : ℝ) : ℂ) = ((X.maj z τ (X.ppos z τ v) + X.maj z τ (v - X.ppos z τ v) : ℝ) : ℂ) := by
    rw [← X.Hf_self hz τ, hV, hvv, eA, eB]
    push_cast
    ring
  have eC' : X.maj z τ v = X.maj z τ (X.ppos z τ v) + X.maj z τ (v - X.ppos z τ v) := by
    exact_mod_cast eC
  have ha := maj_nonneg_of_mem_dom hz τ (X.ppos z τ v)
  have hb := maj_nonneg_of_mem_dom hz τ (v - X.ppos z τ v)
  have e : hermC τ.1 X.Gm v v = ((X.maj z τ (X.ppos z τ v) - X.maj z τ (v - X.ppos z τ v) : ℝ) : ℂ) := by
    rw [hvv, eA, eB]
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, eC']
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
end ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift

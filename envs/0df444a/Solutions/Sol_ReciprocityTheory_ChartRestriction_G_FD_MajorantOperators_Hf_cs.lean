-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.Hf_cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:53.661441+00:00
-- url     : https://prove2.me/submissions/93e237a6-f4c9-40a6-8cb2-8b0ff1855596

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalLatticeDecomposition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_Hf_zero_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_maj_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_maj_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_maj_decomp
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
open ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
theorem _root_.solution {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    ‖X.Hf z τ u w‖ ^ 2 ≤ X.maj z τ u * X.maj z τ w := by
  by_cases hw : w = 0
  · rw [hw, Hf_zero_right, maj_zero hz]
    simp
  have hmw := X.maj_pos hz τ hw
  have hww : X.Hf z τ w w = (X.maj z τ w : ℂ) := X.Hf_self hz τ w
  have hne : X.Hf z τ w w ≠ 0 := by
    rw [hww]
    exact_mod_cast hmw.ne'
  have hd := UnipotentCoefficientShift.maj_decomp hz τ u w hne
  rw [hww, norm_div, Complex.norm_real, Real.norm_of_nonneg hmw.le] at hd
  have h0 := maj_nonneg hz τ (u - (X.Hf z τ u w / (X.maj z τ w : ℂ)) • w)
  have e : (‖X.Hf z τ u w‖ / X.maj z τ w) ^ 2 * X.maj z τ w = ‖X.Hf z τ u w‖ ^ 2 / X.maj z τ w := by
    have := hmw.ne'
    field_simp
  have h1 : ‖X.Hf z τ u w‖ ^ 2 / X.maj z τ w ≤ X.maj z τ u := by
    rw [hd, ← e]
    linarith
  exact (div_le_iff₀ hmw).mp h1
end ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators

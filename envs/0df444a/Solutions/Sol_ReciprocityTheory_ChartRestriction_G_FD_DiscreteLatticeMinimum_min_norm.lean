-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum.min_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:18:07.546258+00:00
-- url     : https://prove2.me/submissions/8e564380-c53d-49ff-a548-7d3654c5dfb9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscriminantTraceBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscreteLatticeMinimum
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_mem__p_iff_0da98c18e74b
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_maj_le_norm_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_mem_Lat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_phi_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_ucomp_line
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_ucomp_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_maj_smul
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
open ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum
open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Y : DataX E r}
  (z : Frame Y.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ Y.dom)]
variable {ξ} (hξ : Y.IsIso ξ)
variable (ep0 : ℝ) (hns : ∀ x ∈ Y.L', herm Y.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : Y.Ψ, ep0 ≤ Y.maj z τ (Y.ucomp z ξ (Y.embV x) τ))
include hns
namespace ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum
theorem _root_.solution (a : VT (X := Y.toData) z ξ) (ha : a ∈ Lat z ξ hξ) (ha0 : a ≠ 0) :
    Real.sqrt ep0 / Y.NA ≤ ‖a‖ := by
  obtain ⟨μ, rfl⟩ := (mem_Lat z ξ hξ).mp ha
  have hμ := LatticeSpanMembership.mem_Λp_iff.mp μ.2
  have hNA : (Y.NA : E) ≠ 0 := by exact_mod_cast Y.NA_pos.ne'
  have hNAr : (0 : ℝ) < Y.NA := by exact_mod_cast Y.NA_pos
  obtain ⟨τ, hτ⟩ := hns ((Y.NA : E) • (μ : Fin r → E)) (Y.NA_sub _ hμ.1)
    (by rw [HermitianTraceFormVanishing.herm_smul_left, hμ.2, mul_zero])
    (by
      intro e he
      apply ha0
      have hμe : (μ : Fin r → E) = ((Y.NA : E)⁻¹ * e) • ξ := by
        rw [mul_smul, ← he, smul_smul, inv_mul_cancel₀ hNA, one_smul]
      exact VT.ext (by rw [phi_val, hμe, ucomp_line z ξ hξ]; rfl))
  have hemb : Y.embV ((Y.NA : E) • (μ : Fin r → E)) = (Y.NA : ℝ) • Y.embV μ := by
    funext τ' b
    simp [Data.embV, Data.emb]
  rw [hemb, ucomp_smul, Pi.smul_apply, ← Complex.coe_smul, UnipotentCoefficientShift.maj_smul hz.out] at hτ
  have h2 := maj_le_norm_sq z ξ (phi z ξ hξ μ) τ
  rw [phi_val] at h2
  have h3 : ep0 ≤ (Y.NA * ‖phi z ξ hξ μ‖) ^ 2 := by
    rw [mul_pow]
    exact le_trans hτ (mul_le_mul_of_nonneg_left h2 (by positivity))
  have h4 := Real.sqrt_le_sqrt h3
  rw [Real.sqrt_sq (by positivity)] at h4
  rw [div_le_iff₀ hNAr]
  linarith
end ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs.e_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:03:07.815893+00:00
-- url     : https://prove2.me/submissions/3e7d8e4e-72dd-4974-b44f-6800811817f4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowIsotropicPairs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowIsotropicPairs_xp_facts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMajorantFlags_Hf_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMajorantFlags_maj_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hermC_smul_right
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_c_pos
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
theorem _root_.solution (X : Data E r) {ξ x : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0) (hξ0 : ξ ≠ 0)
    (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.dom)
    (e : X.Ψ → Fin r → ℂ) (hxp0 : ∀ τ, X.ucomp z0 ξ (X.embV x) τ ≠ 0)
    (he : ∀ τ, e τ = ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) •
      X.ucomp z0 ξ (X.embV x) τ) :
    X.IsIsoV e ∧ (∀ τ, hermC τ.1 X.Gm (e τ) (Data.emb τ.1 ξ) = 0) ∧
      (∀ τ, X.Hf z0 τ (e τ) (Data.emb τ.1 ξ) = 0) ∧ (∀ τ, X.c τ * X.maj z0 τ (e τ) = 1) := by
  have key : ∀ τ, ∃ k : ℝ, 0 < k ∧ e τ = (k : ℂ) • X.ucomp z0 ξ (X.embV x) τ ∧
      k ^ 2 * (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) = 1 := by
    intro τ
    have hm : 0 < X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) :=
      mul_pos (MajorantFamilyNorms.c_pos X τ) (X.maj_pos hz0 τ (hxp0 τ))
    refine ⟨(Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹,
      inv_pos.mpr (Real.sqrt_pos.mpr hm), ?_, ?_⟩
    · simp only [he τ, Complex.ofReal_inv]
    · rw [inv_pow, Real.sq_sqrt hm.le, inv_mul_cancel₀ hm.ne']
  refine ⟨fun τ => ?_, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩
  · obtain ⟨k, hk, hek, -⟩ := key τ
    have hf := xp_facts X hξξ hξ0 hxξ hxx hz0 τ
    refine ⟨?_, ?_⟩
    · rw [hek, hermC_smul_left, hermC_smul_right, hf.2.1, mul_zero, mul_zero]
    · rw [hek]
      exact smul_ne_zero (Complex.ofReal_ne_zero.mpr hk.ne') (hxp0 τ)
  · obtain ⟨k, -, hek, -⟩ := key τ
    rw [hek, hermC_smul_left, (xp_facts X hξξ hξ0 hxξ hxx hz0 τ).1, mul_zero]
  · obtain ⟨k, -, hek, -⟩ := key τ
    rw [hek, Hf_smul_left, (xp_facts X hξξ hξ0 hxξ hxx hz0 τ).2.2, mul_zero]
  · obtain ⟨k, -, hek, hk2⟩ := key τ
    rw [hek, maj_smul X hz0, ← hk2]
    ring
end ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs

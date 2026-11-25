-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum.covering
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:12:57.945724+00:00
-- url     : https://prove2.me/submissions/afd1df9c-792a-436b-b629-e7cc33e88836

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscriminantTraceBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscreteLatticeMinimum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DiscreteLatticeMinimum_short_basis
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_mem_Lat
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
theorem _root_.solution (hD3 : IntegerApproximationCount (E := E)) (hep : 0 < ep0) (d : VT (X := Y.toData) z ξ) :
    ∃ μ : Y.Λp ξ, ‖d - phi z ξ hξ μ‖ ≤ (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 3 * Y.NA /
      (2 * Y.k0 * Real.sqrt ep0) := by
  classical
  rcases Nat.eq_zero_or_pos (finrank ℝ (VT (X := Y.toData) z ξ)) with h0 | hpos
  · have hsub : Subsingleton (VT (X := Y.toData) z ξ) := Module.finrank_zero_iff.mp h0
    refine ⟨0, ?_⟩
    rw [Subsingleton.elim (d - phi z ξ hξ 0) 0, norm_zero, h0]
    simp
  have : Nonempty (Fin (finrank ℝ (VT (X := Y.toData) z ξ))) := ⟨⟨0, hpos⟩⟩
  obtain ⟨y, hli, hyL, hyn⟩ := short_basis z hξ ep0 hns hD3 hep
  let yb := Basis.mk hli (hli.span_eq_top_of_card_eq_finrank (by simp)).ge
  have hyb : ∀ i, yb i = y i := fun i => Basis.mk_apply _ _ _
  set c := yb.repr d with hc
  set p : VT (X := Y.toData) z ξ := ∑ i, (round (c i) : ℤ) • y i with hp
  have hpL : p ∈ Lat z ξ hξ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hyL i)
  obtain ⟨μ, hμ⟩ := (mem_Lat z ξ hξ).mp hpL
  refine ⟨μ, ?_⟩
  rw [hμ]
  have hd : d = ∑ i, c i • y i := by
    conv_lhs => rw [← yb.sum_repr d]
    simp only [hyb, hc]
  have hdiff : d - p = ∑ i, (c i - round (c i)) • y i := by
    rw [hd, hp, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_smul, ← Int.cast_smul_eq_zsmul ℝ]
  rw [hdiff]
  have hlam0 : 0 < Y.k0 * Real.sqrt ep0 / Y.NA := by
    have h1 := Y.minWeight_pos
    have h2 : (0 : ℝ) < Y.NA := by exact_mod_cast Y.NA_pos
    have h3 := Real.sqrt_pos.mpr hep
    positivity
  calc ‖∑ i, (c i - round (c i)) • y i‖ ≤ ∑ i, ‖(c i - round (c i)) • y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (finrank ℝ (VT (X := Y.toData) z ξ)), (1 / 2) *
        ((finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 2 / (Y.k0 * Real.sqrt ep0 / Y.NA)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (abs_sub_round _) (hyn i) (norm_nonneg _) (by norm_num)
    _ = (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 3 * Y.NA / (2 * Y.k0 * Real.sqrt ep0) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 := Y.minWeight_pos.ne'
        have h2 : (Y.NA : ℝ) ≠ 0 := by exact_mod_cast Y.NA_pos.ne'
        have h3 := (Real.sqrt_pos.mpr hep).ne'
        field_simp
end ReciprocityTheory.ChartRestriction.G.FD.DiscreteLatticeMinimum

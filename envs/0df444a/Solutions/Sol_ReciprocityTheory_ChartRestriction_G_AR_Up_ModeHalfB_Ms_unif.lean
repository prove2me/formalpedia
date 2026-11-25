-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Ms_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:56:02.372819+00:00
-- url     : https://prove2.me/submissions/85e73977-8076-4fa3-a211-3daeb2892a79

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_Ms_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_Ms_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_Ms_contAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_Ms_zero
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
theorem _root_.solution (X : Data E r) (τ : X.Ψ) {κ : ℝ} (hκ : 1 < κ) :
    ∀ᶠ N in 𝓝 (Nid r), ∀ v : Fin r → ℂ, κ⁻¹ * ∑ k, ‖v k‖ ^ 2 ≤ Ms X.p0 X.p0_le N v ∧
      Ms X.p0 X.p0_le N v ≤ κ * ∑ k, ‖v k‖ ^ 2 := by
  set S : Set (Fin r → ℂ) := {v | ∑ k, ‖v k‖ ^ 2 = 1} with hS
  have hScont : Continuous fun v : Fin r → ℂ => ∑ k, ‖v k‖ ^ 2 :=
    continuous_finset_sum _ fun k _ => ((continuous_apply k).norm).pow 2
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded (isClosed_eq hScont continuous_const)
    refine (Metric.isBounded_closedBall (x := (0 : Fin r → ℂ)) (r := 1)).subset ?_
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    have h1 : ‖v k‖ ^ 2 ≤ 1 := by
      have hv' : ∑ k, ‖v k‖ ^ 2 = 1 := hv
      rw [← hv']
      exact Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ k)
    nlinarith [norm_nonneg (v k)]
  have hev : ∀ᶠ N in 𝓝 (Nid r), ∀ v ∈ S,
      κ⁻¹ < Ms X.p0 X.p0_le N v ∧ Ms X.p0 X.p0_le N v < κ := by
    apply hSc.eventually_forall_of_forall_eventually
    intro v0 hv0
    have hc := Ms_contAt X.p0 X.p0_le v0
    have hval : Ms X.p0 X.p0_le (Nid r) v0 = 1 := by
      rw [Ms_id X τ]
      exact hv0
    have hmem : Set.Ioo κ⁻¹ κ ∈ 𝓝 (Ms X.p0 X.p0_le (Nid r) v0) := by
      rw [hval]
      exact Ioo_mem_nhds (inv_lt_one_of_one_lt₀ hκ) hκ
    filter_upwards [hc.preimage_mem_nhds hmem] with p hp
    exact hp
  filter_upwards [hev] with N hN
  intro v
  by_cases hv : ∑ k, ‖v k‖ ^ 2 = 0
  · have hv0 : v = 0 := by
      funext k
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖v i‖)).mp hv k
        (Finset.mem_univ k)
      simpa using h
    subst hv0
    simp [Ms_zero]
  · have hpos : 0 < ∑ k, ‖v k‖ ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hv)
    set s := Real.sqrt (∑ k, ‖v k‖ ^ 2) with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
    have hss : s ^ 2 = ∑ k, ‖v k‖ ^ 2 := Real.sq_sqrt hpos.le
    set u : Fin r → ℂ := ((s⁻¹ : ℝ) : ℂ) • v with hu
    have huS : u ∈ S := by
      show ∑ k, ‖u k‖ ^ 2 = 1
      have hk : ∀ k, ‖u k‖ ^ 2 = s⁻¹ ^ 2 * ‖v k‖ ^ 2 := by
        intro k
        simp only [hu, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hs0), mul_pow]
      simp only [hk, ← Finset.mul_sum, ← hss]
      field_simp
    have hvu : v = ((s : ℝ) : ℂ) • u := by
      rw [hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0.ne', Complex.ofReal_one, one_smul]
    have hMs : Ms X.p0 X.p0_le N v = s ^ 2 * Ms X.p0 X.p0_le N u := by
      rw [hvu, Ms_smul]
    obtain ⟨h1, h2⟩ := hN u huS
    rw [hMs, ← hss]
    have hs2 : 0 < s ^ 2 := pow_pos hs0 2
    constructor
    · nlinarith [mul_lt_mul_of_pos_left h1 hs2]
    · nlinarith [mul_lt_mul_of_pos_left h2 hs2]
end ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB

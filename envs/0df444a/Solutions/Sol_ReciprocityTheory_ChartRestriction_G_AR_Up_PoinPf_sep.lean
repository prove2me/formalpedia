-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:11:09.782112+00:00
-- url     : https://prove2.me/submissions/040b1059-cb2f-4aab-a1fa-921c41c022aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_gM_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_orth_mem_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_idF_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_rmul_idF
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (hPD : PropDisc X) :
    ∃ c > 0, ∀ δ ∈ X.Γ, δ ≠ 1 → ∃ τ a b,
      c ≤ ‖gM X x0 (lact δ x0) τ a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ := by
  classical
  have hd := orth_mem_dom X hx0
  obtain ⟨U, hU, U', hU', hfin⟩ := hPD x0 hd x0 hd
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU'
  have hne : ∀ δ ∈ X.Γ, δ ≠ 1 → 0 < dist (lact δ x0) x0 := by
    intro δ hδ h1
    refine dist_pos.2 fun h => h1 (X.Γ_free δ hδ x0 hd (idF X) (idF_mem X) ?_)
    rw [rmul_idF]; exact h
  set T := hfin.toFinset.filter (· ≠ 1) with hTdef
  obtain ⟨ε1, hε1, hT⟩ : ∃ ε1 > 0, ∀ δ ∈ T, ε1 ≤ dist (lact δ x0) x0 := by
    rcases T.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨δ0, hδ0, hmin⟩ := T.exists_min_image (fun δ => dist (lact δ x0) x0) h
      have h0 := Finset.mem_filter.1 hδ0
      exact ⟨_, hne δ0 (hfin.mem_toFinset.1 h0.1).1 h0.2, hmin⟩
  set ε' := min ε ε1 with hε'
  have hε'0 : 0 < ε' := lt_min hε hε1
  have hall : ∀ δ ∈ X.Γ, δ ≠ 1 → ε' ≤ dist (lact δ x0) x0 := by
    intro δ hδ h1
    by_cases hS : δ ∈ T
    · exact (min_le_right _ _).trans (hT δ hS)
    · refine (min_le_left _ _).trans (not_lt.1 fun hlt => hS ?_)
      refine Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨hδ, x0, mem_of_mem_nhds hU, lact δ x0,
        hball (Metric.mem_ball.2 hlt), idF X, idF_mem X, (rmul_idF X _).symm⟩, h1⟩
  set K0 : ℝ := ∑ τ, ∑ a, ∑ k, ‖x0 τ a k‖ + 1 with hK0def
  have hK0 : ∀ τ a k, ‖x0 τ a k‖ ≤ K0 := by
    intro τ a k
    have h1 : ‖x0 τ a k‖ ≤ ∑ k', ‖x0 τ a k'‖ :=
      Finset.single_le_sum (f := fun k' => ‖x0 τ a k'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    have h2 : ∑ k', ‖x0 τ a k'‖ ≤ ∑ a', ∑ k', ‖x0 τ a' k'‖ :=
      Finset.single_le_sum (f := fun a' => ∑ k', ‖x0 τ a' k'‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    have h3 : ∑ a', ∑ k', ‖x0 τ a' k'‖ ≤ ∑ τ', ∑ a', ∑ k', ‖x0 τ' a' k'‖ :=
      Finset.single_le_sum (f := fun τ' => ∑ a', ∑ k', ‖x0 τ' a' k'‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ τ)
    linarith
  have hK0pos : 0 < K0 := by
    have : 0 ≤ ∑ τ, ∑ a, ∑ k, ‖x0 τ a k‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  refine ⟨ε' / ((r : ℝ) * K0 + 1), by positivity, fun δ hδ h1 => ?_⟩
  have hdist := hall δ hδ h1
  by_contra hcon
  push Not at hcon
  have hlt : dist (lact δ x0) x0 < ε' := by
    refine (dist_pi_lt_iff hε'0).2 fun τ => (dist_pi_lt_iff hε'0).2 fun a =>
      (dist_pi_lt_iff hε'0).2 fun b => ?_
    rw [dist_eq_norm]
    have hm := congrFun (congrFun (gM_mul X hx0 (lact δ x0) τ) a) b
    have he : lact δ x0 τ a b - x0 τ a b = ∑ k, x0 τ a k *
        (gM X x0 (lact δ x0) τ k b - (1 : Matrix (Fin r) (Fin r) ℂ) k b) := by
      rw [show lact δ x0 τ a b = mat (lact δ x0) τ a b from rfl, ← hm, Matrix.mul_apply]
      simp only [mul_sub, Finset.sum_sub_distrib, Matrix.one_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
    rw [he]
    calc ‖∑ k, x0 τ a k * (gM X x0 (lact δ x0) τ k b - (1 : Matrix (Fin r) (Fin r) ℂ) k b)‖
        ≤ ∑ k, ‖x0 τ a k * (gM X x0 (lact δ x0) τ k b - (1 : Matrix (Fin r) (Fin r) ℂ) k b)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k : Fin r, K0 * (ε' / ((r : ℝ) * K0 + 1)) := Finset.sum_le_sum fun k _ => by
          rw [norm_mul]
          exact mul_le_mul (hK0 τ a k) (hcon τ k b).le (norm_nonneg _) hK0pos.le
      _ = ε' * ((r : ℝ) * K0 / ((r : ℝ) * K0 + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ < ε' := mul_lt_of_lt_one_right hε'0 ((div_lt_one (by positivity)).2 (lt_add_one _))
  linarith
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

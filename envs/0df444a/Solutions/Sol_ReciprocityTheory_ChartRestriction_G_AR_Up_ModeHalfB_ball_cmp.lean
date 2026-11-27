-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.ball_cmp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:25:57.257802+00:00
-- url     : https://prove2.me/submissions/f2cfc49a-bdf7-4128-9eb4-3c1b6f6b2eb9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_of_Nid
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_Ms_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_Ms_unif
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_nmat_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfB_nmat_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfA_maj_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB
open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB
theorem _root_.solution (X : Data E r) {κ : ℝ} (hκ : 1 < κ) : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
    ∀ u, IsOrth X u → ∀ z : V (nd X), ‖z‖ < ρ → ∀ τ (v : Fin r → ℂ),
      κ⁻¹ * X.maj u τ v ≤ X.maj (cpt X u z) τ v ∧ X.maj (cpt X u z) τ v ≤ κ * X.maj u τ v := by
  have hall : ∀ᶠ z in 𝓝 (0 : V (nd X)), ∀ τ : X.Ψ, ∀ v : Fin r → ℂ,
      κ⁻¹ * ∑ k, ‖v k‖ ^ 2 ≤ Ms X.p0 X.p0_le (nmat X z τ) v ∧
        Ms X.p0 X.p0_le (nmat X z τ) v ≤ κ * ∑ k, ‖v k‖ ^ 2 := by
    rw [Filter.eventually_all]
    intro τ
    have hc : Tendsto (fun z => nmat X z τ) (𝓝 0) (𝓝 (Nid r)) := by
      have := (nmat_cont X τ).tendsto 0
      rwa [nmat_zero X τ] at this
    exact hc.eventually (Ms_unif X τ hκ)
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  refine ⟨min ρ0 1, lt_min hρ0 one_pos, min_le_right _ _, ?_⟩
  intro u hu z hz τ v
  have hz' : z ∈ Metric.ball (0 : V (nd X)) ρ0 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_lt_of_le hz (min_le_left _ _)
  obtain ⟨h1, h2⟩ := hball z hz' τ ((mat u τ)⁻¹ *ᵥ v)
  have hY := hu τ
  have e1 : X.maj (cpt X u z) τ v = Ms X.p0 X.p0_le (nmat X z τ) ((mat u τ)⁻¹ *ᵥ v) :=
    maj_chart X hY (nmat X z τ) rfl v
  have e2 : X.maj u τ v = ∑ k, ‖((mat u τ)⁻¹ *ᵥ v) k‖ ^ 2 := by
    rw [maj_chart X hY (Nid r) (by rw [of_Nid, Matrix.mul_one]) v, Ms_id X τ]
  rw [e1, e2]
  exact ⟨h1, h2⟩
end ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:43:55.362062+00:00
-- url     : https://prove2.me/submissions/be5e40e6-de1a-4eb3-a0d9-986939f7f955

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
open scoped ComplexConjugate ContDiff ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable (x0 : Frame X.Ψ r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
theorem _root_.solution (la : Wt X.Ψ r) : ContinuousOn (fun z => X.nfac la (cpt X x0 z)) (OmF X x0) := by
  have hn : Continuous fun z : V (nd X) => nmat X z := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    unfold nmat
    by_cases h : b < a
    · simp only [h, dif_pos]
      fun_prop
    · simp only [h, dif_neg, not_false_eq_true]
      exact continuous_const
  have hc : Continuous fun z : V (nd X) => cpt X x0 z := by
    refine continuous_pi fun τ => ?_
    show Continuous fun z : V (nd X) => mat x0 τ * mat (nmat X z) τ
    exact continuous_const.matrix_mul ((continuous_apply τ).comp hn)
  have hd : ∀ τ i, Continuous fun z : V (nd X) => dmin X.Gm (cpt X x0 z) τ i := by
    intro τ i
    have h1 : Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
      unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram ReciprocityTheory.ChartRestriction.G.FD.hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
      fun_prop
    exact h1.comp hc
  have hne : ∀ z ∈ OmF X x0, ∀ τ i, dmin X.Gm (cpt X x0 z) τ i ≠ 0 := by
    intro z hz τ i h
    have hz' : ∀ τ : X.Ψ, (mat (cpt X x0 z) τ).det ≠ 0 ∧
        ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re := hz
    have h2 := (hz' τ).2 i
    rw [h, Complex.zero_re, mul_zero] at h2
    exact lt_irrefl _ h2
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  apply continuousOn_finset_prod
  intro τ _
  apply continuousOn_finset_prod
  intro i _
  intro z hz
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.rpow_const
  · exact ((hd τ _).continuousAt.div (hd τ _).continuousAt (hne z hz τ _)).norm
  · left
    exact norm_ne_zero_iff.mpr (div_ne_zero (hne z hz τ _) (hne z hz τ _))
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE

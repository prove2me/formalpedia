-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:10.87051+00:00
-- url     : https://prove2.me/submissions/67f371ba-6b50-444f-a232-d86966085141

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
theorem _root_.solution {la : Wt X.Ψ r} {z : V (nd X)} (hz : z ∈ OmF X x0) : 0 < X.nfac la (cpt X x0 z) := by
  have hz' : ∀ τ : X.Ψ, (mat (cpt X x0 z) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re := hz
  have hd : ∀ τ i, dmin X.Gm (cpt X x0 z) τ i ≠ 0 := by
    intro τ i h
    have h2 := (hz' τ).2 i
    rw [h, Complex.zero_re, mul_zero] at h2
    exact lt_irrefl _ h2
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  apply Finset.prod_pos
  intro τ _
  apply Finset.prod_pos
  intro i _
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:21.803537+00:00
-- url     : https://prove2.me/submissions/111cb51d-20eb-40d1-8d44-1a1c8565dc3e

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
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
theorem _root_.solution (la : Wt X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : bchar la b ≠ 0 := by
  have hb' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 := hb
  unfold bchar
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  rw [Finset.prod_ne_zero_iff]
  intro i _
  have hd := (hb' τ).1
  have hbt : (mat b τ).BlockTriangular id := fun a c hca => (hb' τ).2 a c hca
  rw [Matrix.det_of_upperTriangular hbt, Finset.prod_ne_zero_iff] at hd
  have hi := hd i (Finset.mem_univ _)
  exact zpow_ne_zero _ hi
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE

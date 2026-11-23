-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.cpt_mem_dom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:37.302796+00:00
-- url     : https://prove2.me/submissions/e1bc8dc9-b57d-40c5-addc-4fa7686181ed

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_dmin_cpt_orth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hxo : IsOrth X x) {w : V (nd X)}
    (h1 : ∀ τ, (mat (nmat X w) τ).det ≠ 0)
    (h2 : ∀ τ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (lminor (Gw X w τ) i).re) :
    cpt X x w ∈ X.dom := fun τ =>
  ⟨by
    show (mat x τ * mat (nmat X w) τ).det ≠ 0
    rw [Matrix.det_mul]; exact mul_ne_zero (hx τ).1 (h1 τ),
   fun i => by rw [dmin_cpt_orth X hxo]; exact h2 τ i⟩
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

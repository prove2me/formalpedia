-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.chart_elem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:39:36.647372+00:00
-- url     : https://prove2.me/submissions/22143829-b4d1-4c42-9c81-47278005296f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_XZeroPowDvdOfIsHomogeneousAeval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (l : Fin (D + 1)) (a : fnField (x ∘ e))
    (ha : a ∈ chartRing x e l) :
    ∃ g : MvPolynomial {k // k ≠ l} ℤ, (a : Ω) = MvPolynomial.aeval (fun k => x (e k.1) / x (e l)) g := by
  rw [chartRing, Algebra.adjoin_range_eq_range_aeval] at ha
  obtain ⟨g, rfl⟩ := ha
  refine ⟨g, ?_⟩
  induction g using MvPolynomial.induction_on <;> simp_all [chartGen]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds

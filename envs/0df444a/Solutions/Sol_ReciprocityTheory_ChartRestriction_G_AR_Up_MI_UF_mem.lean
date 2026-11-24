-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.UF_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:30.840546+00:00
-- url     : https://prove2.me/submissions/23d78def-a393-4d12-90bc-f3cea338ec3b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution {y : UpI X.Ψ r → ℂ} (hy : ∀ τ b, y (dI τ b) ≠ 0) : UF X y ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq]
  intro τ
  have hU : (Umat y τ).BlockTriangular id := by
    intro a b h
    have h' : b < a := h
    simp only [Umat, Matrix.of_apply]
    rw [dif_neg (not_not.2 h')]
  refine ⟨?_, fun a c h => hU h⟩
  show (Umat y τ).det ≠ 0
  rw [Matrix.det_of_upperTriangular hU]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  have e : Umat y τ a a = y (dI τ a) := by
    unfold Umat dI
    rw [Matrix.of_apply, dif_pos (lt_irrefl a)]
  rw [e]
  exact hy τ a
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI

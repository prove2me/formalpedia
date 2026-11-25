-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.CmatSet_diag_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:39.680812+00:00
-- url     : https://prove2.me/submissions/9099c76e-b0ac-4747-ac13-ddce0f9219a6

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
theorem _root_.solution {β : Frame X.Ψ r} (hβ : β ∈ CmatSet X) {D : X.Ψ → Fin r → ℂ}
    (hD : ∀ τ a, ‖D τ a‖ = 1) : (fun τ => (diagonal (D τ) * mat β τ : Matrix (Fin r) (Fin r) ℂ)) ∈ CmatSet X := by
  simp only [CmatSet, Set.mem_setOf_eq] at hβ ⊢
  intro τ a b
  obtain ⟨h1, h2, h3⟩ := hβ τ a b
  simp only [Matrix.diagonal_mul, mat, Matrix.of_apply, norm_mul, hD, one_mul]
  exact ⟨fun h => by rw [h1 h, mul_zero], h2, h3⟩
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.cont_Zb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:37.941446+00:00
-- url     : https://prove2.me/submissions/bd20a0ab-a919-4ba2-af42-7a0078cc949e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_Lemmata_GeneralBFactBisForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E)
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
theorem _root_.solution {n : ℕ} {B : (Fin n → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ}
    (hB : Continuous B) (y : Frame X.Ψ r) : Continuous fun t => X.Zb u (B t) y := by
  have hB' : ∀ τ i k, Continuous fun t => B t τ i k := fun τ i k => by fun_prop
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
  simp only [Data.Zb, Data.zmat, Matrix.mul_apply, Matrix.of_apply, mat]
  fun_prop
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain

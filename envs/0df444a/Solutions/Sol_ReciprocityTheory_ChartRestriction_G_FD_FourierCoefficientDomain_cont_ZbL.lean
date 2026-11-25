-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.cont_ZbL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:04:49.66109+00:00
-- url     : https://prove2.me/submissions/6bd8ac38-75c6-4ca1-acdd-fdfd36bc5d0d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Definitions.Def_Lemmata_GeneralBFactBisForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientDomain_cont_Zb

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
    (hB : Continuous B) : Continuous fun t => ZbL X u (B t) :=
  continuous_clm_apply.2 fun y => cont_Zb X u hB y
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain

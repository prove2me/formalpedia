-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.mulVec_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:36.302217+00:00
-- url     : https://prove2.me/submissions/671fb189-4658-45a2-bc09-43bf5756012e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowFixesComplementOfIsotropic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
variable (ξ : Fin r → E) (τ : X.Ψ)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (M : Matrix (Fin r) (Fin r) ℂ) {n : ℕ} (β : Fin n → ℂ) (v : Fin n → Fin r → ℂ) :
    Matrix.mulVec M (∑ a, β a • v a) = ∑ a, β a • Matrix.mulVec M (v a) := by
  simp [Matrix.mulVec_sum, Matrix.mulVec_smul]
end ReciprocityTheory.ChartRestriction.G.FD.Data

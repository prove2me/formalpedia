-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.ppos_mat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:13.62286+00:00
-- url     : https://prove2.me/submissions/8fd0a216-fedd-4ae8-bc34-e2546478fb59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantBoundOrthogonalPart

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
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution {x x' : Frame X.Ψ r} {τ : X.Ψ} (h : mat x τ = mat x' τ) (v : Fin r → ℂ) :
    X.ppos x τ v = X.ppos x' τ v := by
  simp only [Data.ppos, Data.gramPos, h]
end ReciprocityTheory.ChartRestriction.G.FD.Data

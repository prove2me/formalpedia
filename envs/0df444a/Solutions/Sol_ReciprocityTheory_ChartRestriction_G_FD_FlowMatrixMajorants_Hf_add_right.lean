-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants.Hf_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:19.883476+00:00
-- url     : https://prove2.me/submissions/53ecf912-b4e0-4617-a6d0-9c6679c3c70d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants

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
open ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants
open MajorantConjugateTransfer
variable {r : ℕ} (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ)
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants
theorem _root_.solution (x : Frame X.Ψ r) (u w w' : Fin r → ℂ) :
    X.Hf x τ u (w + w') = X.Hf x τ u w + X.Hf x τ u w' := by
  unfold Data.Hf hermC
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
end ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants

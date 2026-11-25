-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants.flowMat_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:08.783743+00:00
-- url     : https://prove2.me/submissions/47aa79bd-d108-42fc-94f6-d1bf94d6e1c9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_flowMat_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_flowMat_zero

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
theorem _root_.solution (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (a : ℂ)
    (w : Fin r → ℂ) : Matrix.mulVec (X.flowMat ξ τ a) (Matrix.mulVec (X.flowMat ξ τ (-a)) w) = w := by
  rw [Matrix.mulVec_mulVec, ← flowMat_add X ξ τ hiso, add_neg_cancel, flowMat_zero,
    Matrix.one_mulVec]
end ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants

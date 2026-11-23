-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants.flow_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:49.568815+00:00
-- url     : https://prove2.me/submissions/29460a12-3028-416c-8634-b6208ec27549

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_flowMat_add

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
theorem _root_.solution (hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0)
    (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flow ξ s x = X.flow ξ (fun τ => I * ((s τ).im : ℂ)) (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) := by
  funext τ
  have hs : I * ((s τ).im : ℂ) + ((s τ).re : ℂ) = s τ := by
    rw [add_comm, mul_comm, Complex.re_add_im]
  show X.flowMat ξ τ (s τ) * mat x τ =
    X.flowMat ξ τ (I * ((s τ).im : ℂ)) * (X.flowMat ξ τ ((s τ).re : ℂ) * mat x τ)
  conv_lhs => rw [← hs]
  rw [flowMat_add X ξ τ (hiso τ), mul_assoc]
end ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants

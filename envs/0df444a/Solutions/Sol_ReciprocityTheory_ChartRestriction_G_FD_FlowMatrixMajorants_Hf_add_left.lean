-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants.Hf_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:13.329088+00:00
-- url     : https://prove2.me/submissions/0b25c093-3131-41a0-b9df-f9b2218e7a95

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_add


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
theorem _root_.solution (x : Frame X.Ψ r) (u u' w : Fin r → ℂ) :
    X.Hf x τ (u + u') w = X.Hf x τ u w + X.Hf x τ u' w := by
  unfold Data.Hf hermC
  rw [X.ppos_add x τ]
  simp only [smul_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
end ReciprocityTheory.ChartRestriction.G.FD.FlowMatrixMajorants

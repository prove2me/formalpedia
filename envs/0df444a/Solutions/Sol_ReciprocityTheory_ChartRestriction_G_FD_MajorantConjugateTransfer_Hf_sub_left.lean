-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.Hf_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:36.891058+00:00
-- url     : https://prove2.me/submissions/c49b97f9-5af5-4243-a412-e952c04da711

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_eq_two_ppos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sub_left


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
open ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) (u u' w : Fin r → ℂ) :
    X.Hf x τ (u - u') w = X.Hf x τ u w - X.Hf x τ u' w := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.ppos_sub, hermC_sub_left,
    hermC_sub_left]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.Hf_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:31.354973+00:00
-- url     : https://prove2.me/submissions/502d44ef-3ca1-4587-9d43-bf28fa43e8d2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_eq_two_ppos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_smul_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left


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
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (k • u) w = k * X.Hf x τ u w := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.ppos_smul_eq, hermC_smul_left, hermC_smul_left]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer

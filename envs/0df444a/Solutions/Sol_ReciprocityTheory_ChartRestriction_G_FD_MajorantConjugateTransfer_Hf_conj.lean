-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.Hf_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:27.150719+00:00
-- url     : https://prove2.me/submissions/8cc58244-c5c4-43a4-b36f-282a071c5999

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_eq_two_ppos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_selfadj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj


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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    conj (X.Hf x τ u w) = X.Hf x τ w u := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, map_sub, map_mul, map_ofNat, hermC_conj _ X.Gm_herm,
    hermC_conj _ X.Gm_herm, X.ppos_selfadj hx τ w u]
end ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer

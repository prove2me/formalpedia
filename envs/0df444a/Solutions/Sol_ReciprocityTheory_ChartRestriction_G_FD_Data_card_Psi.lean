-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.card_Psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:13.64881+00:00
-- url     : https://prove2.me/submissions/bebab63c-35f0-471c-8675-f1811d43790b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_sum_emb_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution : 2 * Fintype.card X.Ψ = finrank ℚ E := by
  have h := X.sum_emb_split (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [← NumberField.Embeddings.card E ℂ]
  have h' : ((Fintype.card (E →+* ℂ) : ℕ) : ℂ) = ((2 * Fintype.card X.Ψ : ℕ) : ℂ) := by
    push_cast
    linear_combination h
  exact (Nat.cast_injective h').symm
end ReciprocityTheory.ChartRestriction.G.FD.Data

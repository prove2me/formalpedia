-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices.Mmat_f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:46.851191+00:00
-- url     : https://prove2.me/submissions/0de08ffd-d4e1-4b96-ba1a-d4a2835a381b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatUnitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_eps_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_Mmat_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EigenframeMatrices_hf_eps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p : ℕ) (f g : Fin n → Fin r → ℂ)
variable (hG : ∀ a b, cc (G a b) = G b a)
  (hf : ∀ k l, hermC τ G (f k) (f l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
include hG hf
namespace ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
theorem _root_.solution (l : Fin n) : Mmat τ G p f g *ᵥ f l = g l := by
  rw [Mmat_mulVec]
  simp only [hf_eps τ G p f hG hf, mul_ite, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, eps_sq, one_smul]
  abel
end ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices

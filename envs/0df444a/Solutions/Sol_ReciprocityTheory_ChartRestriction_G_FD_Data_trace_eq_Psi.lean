-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.trace_eq_Psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:25.244675+00:00
-- url     : https://prove2.me/submissions/8e404820-d37b-4b6e-9243-8e8bbd54941f

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
theorem _root_.solution (y : E) :
    ((Algebra.trace ℚ E y : ℚ) : ℂ) = ∑ τ : X.Ψ, (τ.1 y + conj (τ.1 y)) := by
  have h1 : ((Algebra.trace ℚ E y : ℚ) : ℂ) = ∑ φ : E →+* ℂ, φ y := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := y)
    rw [eq_ratCast] at h
    rw [h]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ fun σ => rfl
  rw [h1, X.sum_emb_split (fun φ => φ y)]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD.Data

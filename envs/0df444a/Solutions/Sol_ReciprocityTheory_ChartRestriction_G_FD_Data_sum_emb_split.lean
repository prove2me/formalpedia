-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.sum_emb_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:31.457933+00:00
-- url     : https://prove2.me/submissions/68c74d31-00ff-4d3b-8ff6-5bd761d50863

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_conjugate_conjugate__4a5ffdebff34
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_conj_mem_iff

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
theorem _root_.solution (f : (E →+* ℂ) → ℂ) :
    ∑ φ : E →+* ℂ, f φ = ∑ τ : X.Ψ, (f τ.1 + f (ComplexEmbedding.conjugate τ.1)) := by
  classical
  have h2 : ∑ φ ∈ X.Ψ, f (ComplexEmbedding.conjugate φ) = ∑ φ ∈ X.Ψᶜ, f φ :=
    Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate
      (fun a ha => Finset.mem_compl.2 fun hc => (X.conj_mem_iff a).1 hc ha)
      (fun a ha => (X.conj_mem_iff a).2 (Finset.mem_compl.1 ha))
      (fun a _ => conjugate_conjugate' a) (fun a _ => conjugate_conjugate' a) (fun a _ => rfl)
  have h2' : ∑ x : X.Ψ, f (ComplexEmbedding.conjugate x.1) = ∑ φ ∈ X.Ψᶜ, f φ := by
    rw [← h2]
    exact Finset.sum_coe_sort X.Ψ (fun φ => f (ComplexEmbedding.conjugate φ))
  rw [Finset.sum_add_distrib, h2', Finset.sum_coe_sort X.Ψ f, Finset.sum_add_sum_compl]
end ReciprocityTheory.ChartRestriction.G.FD.Data

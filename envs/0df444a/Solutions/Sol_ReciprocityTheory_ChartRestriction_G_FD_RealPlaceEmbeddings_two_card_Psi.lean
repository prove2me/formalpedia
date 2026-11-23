-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.two_card_Psi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:12.865933+00:00
-- url     : https://prove2.me/submissions/523209e4-1b0b-488d-83d7-a62b07af851f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_conj_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
open NumberField Module Submodule
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
theorem _root_.solution : 2 * Fintype.card X.Ψ = finrank ℚ E := by
  classical
  rw [← NumberField.Embeddings.card E ℂ]
  have h1 : (X.Ψᶜ).card = X.Ψ.card := by
    refine Finset.card_bij (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_
    · intro τ hτ
      rw [Finset.mem_compl] at hτ
      exact (X.cmType _).mpr (by rw [TraceIntegralBasis.conj_conj]; exact hτ)
    · intro a _ b _ h
      have := congrArg ComplexEmbedding.conjugate h
      rwa [TraceIntegralBasis.conj_conj, TraceIntegralBasis.conj_conj] at this
    · intro τ hτ
      refine ⟨ComplexEmbedding.conjugate τ, ?_, TraceIntegralBasis.conj_conj τ⟩
      rw [Finset.mem_compl]
      intro h
      exact ((X.cmType _).mp h) (by rw [TraceIntegralBasis.conj_conj]; exact hτ)
  have h2 := Finset.card_add_card_compl X.Ψ
  rw [Fintype.card_coe]
  omega
end ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings

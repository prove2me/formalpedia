-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.span_real_embeddings_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:23:38.44043+00:00
-- url     : https://prove2.me/submissions/86d3975e-fc74-4a22-87ab-24dd363df4f1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_Tm_iota
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_Tm_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_finrank_Psi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_bas_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_finrank_VS


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
theorem _root_.solution : span ℝ (Set.range fun x : E => fun τ : X.Ψ => τ.1 x) = ⊤ := by
  have hs : span ℝ (Set.range (TraceIntegralBasis.iota E)) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← (TraceIntegralBasis.bas E).span_eq]
    exact span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨_, (TraceIntegralBasis.bas_apply i).symm⟩)
  have hdim : finrank ℝ (TraceIntegralBasis.VS E) = finrank ℝ (X.Ψ → ℂ) := by
    rw [TraceIntegralBasis.finrank_VS, finrank_Psi]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (Tm_injective X)
  rw [eq_top_iff]
  intro z _
  obtain ⟨y, rfl⟩ := hsurj z
  have hy : y ∈ span ℝ (Set.range (TraceIntegralBasis.iota E)) := by rw [hs]; trivial
  have h1 := Submodule.mem_map_of_mem (f := Tm X) hy
  rw [Submodule.map_span] at h1
  refine span_mono ?_ h1
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨x, funext fun τ => (Tm_iota X x τ).symm⟩
end ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings

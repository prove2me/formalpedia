-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.nLa_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:41:43.985511+00:00
-- url     : https://prove2.me/submissions/c76abd71-3745-414b-b6c7-000933740356

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_Wres_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_admissible_over_prime


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (c : ι) (f : A c) (a : Ω c) (ha : a ≠ 0)
    (hOs : ∀ v, d.admitted c v → ((O c v (a • f) : ℤ) : WithTop ℤ) = v a + (O c v f : WithTop ℤ)) :
    Function.support (fun la => d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a)) ⊆
      {la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O c (d.Wres c w) f ≠ 0} ∪
      {la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O c (d.Wres c w) (a • f) ≠ 0} := by
  intro la hla
  obtain ⟨w, hw, hw0⟩ := exists_ne_zero_of_finsum_mem_ne_zero hla
  have hv := (d.admissible_over_prime hd h la c w hw).1
  have hs := d.shift hv ha (hOs _ hv)
  by_cases h0 : O c (d.Wres c w) f = 0
  · right
    refine ⟨w, hw, ?_⟩
    rw [hs, h0, add_zero]
    intro h1; apply hw0; rw [← d.Wres_apply, h1, mul_zero]
  · exact Or.inl ⟨w, hw, h0⟩
end ReciprocityTheory.ChartRestriction.G.T0.Data

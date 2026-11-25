-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.la_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:22:41.518031+00:00
-- url     : https://prove2.me/submissions/3d7a8805-85fd-4323-bdcd-50f374a61315

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_isOver_inj
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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (O : AddValuation (Ω c) (WithTop ℤ) → ℤ)
    (hO : {v | d.admitted c v ∧ O v ≠ 0}.Finite) :
    {la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O (d.Wres c w) ≠ 0}.Finite := by
  classical
  set s := {la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O (d.Wres c w) ≠ 0}
  have hF : ∀ la (hla : la ∈ s), d.admitted c (d.Wres c hla.choose) ∧
      IsOver (K := K) (d.Wres c hla.choose) la ∧ O (d.Wres c hla.choose) ≠ 0 := by
    intro la hla
    have hs := (d.admissible_over_prime hd h la c _ hla.choose_spec.1)
    exact ⟨hs.1, hs.2.1, hla.choose_spec.2⟩
  have : Finite s := by
    have := hO.to_subtype
    refine Finite.of_injective (fun la : s => (⟨d.Wres c la.2.choose, (hF la la.2).1, (hF la la.2).2.2⟩ :
      {v | d.admitted c v ∧ O v ≠ 0})) ?_
    intro la la' heq
    have heq' : d.Wres c la.2.choose = d.Wres c la'.2.choose := congrArg Subtype.val heq
    exact Subtype.ext (isOver_inj (K := K) (hF la la.2).2.1 (heq' ▸ (hF la' la'.2).2.1))
  exact Set.toFinite s
end ReciprocityTheory.ChartRestriction.G.T0.Data

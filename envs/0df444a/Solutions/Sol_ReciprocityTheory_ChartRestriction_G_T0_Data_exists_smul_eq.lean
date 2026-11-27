-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.exists_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:44:53.133782+00:00
-- url     : https://prove2.me/submissions/c32fe400-fa56-4b59-ba86-9bd0a9108828

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IntNsg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightGeneratorLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IntegralLeOfAeLeAffine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogNormNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDE

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
theorem _root_.solution (hd : d.AxH 𝒜) {c : ι} {G : WT} {f g : A c} (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0)
    (hg : g ∈ 𝒜 c G) (hg0 : g ≠ 0) : ∃ a : Ω c, a ≠ 0 ∧ a • f = g := by
  have h1 := hd.finrank_one c G
  have hne : (⟨f, hf⟩ : 𝒜 c G) ≠ 0 := by
    rwa [Ne, Submodule.mk_eq_zero]
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 h1 ⟨g, hg⟩
  have ha' : a • f = g := congrArg Subtype.val ha
  refine ⟨a, ?_, ha'⟩
  rintro rfl
  exact hg0 (by rw [← ha', zero_smul])
end ReciprocityTheory.ChartRestriction.G.T0.Data

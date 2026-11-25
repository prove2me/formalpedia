-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.eq_ratio_smul_on_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:25:26.430209+00:00
-- url     : https://prove2.me/submissions/a032543b-8a3f-4f96-be3b-e2eeaa15d904

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ratio_eq_of_eq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution {hd : d.AxH 𝒜} {c : ι} {G : WT} {f g : A c} (hf : f ∈ 𝒜 c G) (hg : g ∈ 𝒜 c G)
    (hg0 : g ≠ 0) : f = ratio (Ω := Ω c) f g • g := by
  have h1 := hd.finrank_one c G
  have hg' : (⟨g, hg⟩ : 𝒜 c G) ≠ 0 := fun h => hg0 (by simpa using congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hg').1 h1 ⟨f, hf⟩
  have hfa : f = a • g := by
    have := congrArg Subtype.val ha
    simpa using this.symm
  rw [ratio_eq_of_eq_smul hg0 hfa]
  exact hfa
end ReciprocityTheory.ChartRestriction.G.T0.Data

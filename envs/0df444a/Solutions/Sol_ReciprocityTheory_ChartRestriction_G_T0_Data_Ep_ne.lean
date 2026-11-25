-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.Ep_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:22:14.762184+00:00
-- url     : https://prove2.me/submissions/f57eaf9d-bc5e-4e6c-af05-65037f60a7cb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumEqSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_nP_split
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_primes_properties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (f : A c) (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    {p | p ∈ d.HtOne ∧ d.Ep h c p ≠ 0}.Finite := by
  refine ((d.good_primes_properties hd h c).2.2.1 d.wL f hf hf0).union ((d.good_primes_properties hd h c).2.2.2 f hf hf0)
    |>.subset ?_
  rintro p ⟨hp, hE⟩
  by_contra hno
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and, not_not] at hno
  have := d.nP_split hd h c hp f
  rw [hno.1 hp, hno.2 hp] at this
  omega
end ReciprocityTheory.ChartRestriction.G.T0.Data

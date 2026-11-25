-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.GeneratorMultiHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:04:48.571118+00:00
-- url     : https://prove2.me/submissions/32df8c4c-f869-4a29-9861-6642be82356b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessTheorem_HtGaussUniq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericTheorem_HtGaussGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AdmissibleValuationPrimeUnique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_AdmissibleValuationPrimeUnique
import Theorems.Thm_HtGaussGen
import Theorems.Thm_HtGaussUniq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_PlaceTrivialOrPositive


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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∀ p ∈ d.HtOne, (∃ w, w ∈ d.GoodP c p) →
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen p))
        (d.gen p) :=
  HtGaussGen 𝒜 d (Data.PlaceTrivialOrPositive (𝒜 := 𝒜) d) (Data.AdmissibleValuationPrimeUnique (𝒜 := 𝒜) d) hd h c
end ReciprocityTheory.ChartRestriction.G.T0.Data

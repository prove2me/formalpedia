-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.hint_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:20:08.954832+00:00
-- url     : https://prove2.me/submissions/f70b8d37-03da-426f-af81-2137a538cfd1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintLogFinprod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintISBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_hint_bsp_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (sg : K →+* ℂ) {G : WT} {f : A c} (hf : f ∈ 𝒜 c G)
    (hf0 : f ≠ 0) :
    AEStronglyMeasurable (d.hintSm c sg fun P => Real.log (d.nrm c G f P))
      (blockSphereProb d.D (d.N + 1)) := by
  rw [d.hint_bsp_smul]
  exact ((hd.a13 c sg hf hf0).smul_measure _).aestronglyMeasurable
end ReciprocityTheory.ChartRestriction.G.T0.Data

-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.hint_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:01:17.581248+00:00
-- url     : https://prove2.me/submissions/2c20110a-9b34-4b63-af39-42c9611ee18d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintLogFinprod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintISBounds

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
theorem _root_.solution (hd : d.AxH 𝒜) {c : ι} {G : WT} {f : A c} (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0)
    {sg : K →+* ℂ} {B : ℝ} (hB : ∀ P ∈ PT (Ω := Ω c) sg, d.nrm c G f P ≤ B) :
    ∀ P ∈ PT (Ω := Ω c) sg, Real.log (d.nrm c G f P) ≤ Real.log B := fun P hP => Real.log_le_log (hd.nrm_pos c P hf hf0) (hB P hP)
end ReciprocityTheory.ChartRestriction.G.T0.Data

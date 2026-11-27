-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.hintIS_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:07:34.496604+00:00
-- url     : https://prove2.me/submissions/58da3b0b-7b27-4ebc-8d08-1a2d229b52e9

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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ}
    {φ ψ : (Ω c →+* ℂ) → ℝ} (hφ : d.HintIS c sg φ) (heq : ∀ P ∈ PT (Ω := Ω c) sg, φ P = ψ P) :
    d.HintIS c sg ψ := by
  unfold HintIS at *
  refine hφ.congr (Filter.Eventually.of_forall fun z => ?_)
  exact finsum_mem_congr rfl fun P hP => heq P hP.1
end ReciprocityTheory.ChartRestriction.G.T0.Data

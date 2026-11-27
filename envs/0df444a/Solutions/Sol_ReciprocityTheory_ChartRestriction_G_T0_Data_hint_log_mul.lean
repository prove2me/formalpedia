-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.hint_log_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:53:14.142295+00:00
-- url     : https://prove2.me/submissions/3d8b526e-cccb-470c-b048-39df7fac86b7

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
theorem _root_.solution (hd : d.AxH 𝒜) {c : ι} {G G' : WT} {f g : A c} (hf : f ∈ 𝒜 c G)
    (hg : g ∈ 𝒜 c G') (hf0 : f ≠ 0) (hg0 : g ≠ 0) (P : Ω c →+* ℂ) :
    Real.log (d.nrm c (G + G') (f * g) P) =
      Real.log (d.nrm c G f P) + Real.log (d.nrm c G' g P) := by
  rw [hd.nrm_mul c P hf hg hf0 hg0,
    Real.log_mul (hd.nrm_pos c P hf hf0).ne' (hd.nrm_pos c P hg hg0).ne']
end ReciprocityTheory.ChartRestriction.G.T0.Data

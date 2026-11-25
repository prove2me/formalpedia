-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.lineRatio_val_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:11:04.70709+00:00
-- url     : https://prove2.me/submissions/30a68d98-5a3c-4f76-b230-0a2a5104b5ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight

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
theorem _root_.solution (c : ι) (p : Ideal (KTp K d.D d.N))
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.OverP c p)
    (htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) : 0 ≤ w (d.rationalBaseRow c) := by
  unfold rationalBaseRow
  refine AddValuation.map_le_sum w fun j _ => ?_
  rw [AddValuation.map_mul]
  have h1 : 0 ≤ w (d.sH c (MvPolynomial.X (0, j))) := (hw.2 _).1
  have h2 : 0 ≤ w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) := by
    by_cases ha : ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = 0
    · rw [ha, map_zero, AddValuation.map_zero]
      exact le_top
    · have h3 := htriv _ ha
      unfold Wres at h3
      exact le_of_eq h3.symm
  exact add_nonneg h1 h2
end ReciprocityTheory.ChartRestriction.G.T0.Data

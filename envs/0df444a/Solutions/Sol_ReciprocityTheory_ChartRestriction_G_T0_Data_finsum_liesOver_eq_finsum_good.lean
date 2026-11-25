-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.finsum_liesOver_eq_finsum_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:52:04.053604+00:00
-- url     : https://prove2.me/submissions/37da40ab-e866-4c3e-ad59-5c5539574af2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Theorems.Thm_BlockPoly_translEquiv_apply
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
theorem _root_.solution (c : ι) (p : Ideal (KTp K d.D d.N)) (g : Ω c) (hg : g ≠ 0)
    (F : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → WithTop ℤ → ℤ)
    (hF : ∀ w, F w 0 = 0) :
    (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
      F w (w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g))) =
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
      F w (d.Wres c w g) := by
  classical
  refine finsum_congr fun w => ?_
  by_cases hG : w ∈ d.GoodP c p
  · have hO : w ∈ d.OverP c p := hG.1
    simp only [finsum_eq_if, if_pos hO, if_pos hG]
    rfl
  · simp only [finsum_eq_if, if_neg hG]
    split_ifs with hO
    · have h0 : d.Wres c w g = 0 := by
        by_contra hne
        exact hG ⟨hO, g, hg, hne⟩
      have h1 : w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) = 0 := h0
      rw [h1, hF]
    · rfl
end ReciprocityTheory.ChartRestriction.G.T0.Data

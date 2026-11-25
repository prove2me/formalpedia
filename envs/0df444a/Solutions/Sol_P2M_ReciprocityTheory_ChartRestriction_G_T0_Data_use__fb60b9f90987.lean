-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_use__fb60b9f90987
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:35:46.945913+00:00
-- url     : https://prove2.me/submissions/69e6e365-5b6f-4dbf-85c5-18046ee0ff2f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_by_places
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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (r : Ω c) (hr : r ≠ 0) :
    {p | p ∈ d.HtOne ∧ (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
      (_ : w ∈ d.GoodP c p), (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w r)) ≠ 0}.Finite := by
  obtain ⟨-, hy⟩ := d.norm_by_places hd h c
  have hne : algebraMap (Ω c) (OmS (Ω c) d.D d.N) r ≠ 0 := by
    intro h0
    exact hr ((map_eq_zero_iff _ (algebraMap (Ω c) (OmS (Ω c) d.D d.N)).injective).mp h0)
  refine (hy _ hne).1.subset ?_
  rintro p ⟨hp, hsum⟩
  refine ⟨hp, ?_⟩
  by_contra hcon
  push_neg at hcon
  apply hsum
  refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
  classical
  by_cases hw : w ∈ d.GoodP c p
  · have h0 : d.Wres c w r = 0 := hcon w hw.1
    simp [finsum_eq_if, hw, h0]
  · simp [finsum_eq_if, hw]
end ReciprocityTheory.ChartRestriction.G.T0.Data

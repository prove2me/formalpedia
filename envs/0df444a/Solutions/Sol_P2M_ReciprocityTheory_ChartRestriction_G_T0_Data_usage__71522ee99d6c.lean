-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_usage__71522ee99d6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:13:09.207551+00:00
-- url     : https://prove2.me/submissions/f981e5b8-4dd8-43ff-9c95-fb14f4748a97

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_admissible_of_good_valuation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_shift
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_goodP_finite__50a0ff3ed058

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (c : ι) (f : A c) (a : Ω c) (ha : a ≠ 0)
    (hOs : ∀ v, d.admitted c v → ((O c v (a • f) : ℤ) : WithTop ℤ) = v a + (O c v f : WithTop ℤ))
    {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    d.anP h O c (a • f) p = d.anP h O c f p + d.nPa h c p a := by
  unfold anP nPa
  rw [← finsum_mem_add_distrib (d.goodP_finite' hd h c hp)]
  refine finsum_mem_congr rfl fun w hw => ?_
  have hv := d.admissible_of_good_valuation hd h c hp hw
  rw [d.shift hv ha (hOs _ hv)]
  ring
end ReciprocityTheory.ChartRestriction.G.T0.Data

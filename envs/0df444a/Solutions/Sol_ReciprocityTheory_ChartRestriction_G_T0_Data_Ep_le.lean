-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.Ep_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:47:42.856975+00:00
-- url     : https://prove2.me/submissions/e10402dd-b5ba-4a33-93bb-d088bf55a68b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumEqSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_hh_good_adm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_finite

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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (hF1d : d.TrivialPlaceHyp) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) :
    (d.Ep h c p : ℝ) ≤ d.cc / (2 * d.i) * d.nP h c (d.n1 • d.wde) (d.et c) p := by
  have hs := d.good_finite hd h c hp
  unfold Ep nP
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  have ha := d.hh_good_adm hd h hp hw
  have := hF1d c _ ha.1 ha.2
  have hf : (0 : ℝ) ≤ d.fze h c w := Nat.cast_nonneg _
  calc (d.fze h c w : ℝ) * (d.Emin c (d.Wres c w) : ℝ)
      ≤ (d.fze h c w : ℝ) * (d.cc / (2 * d.i) * d.ord c (d.Wres c w) (d.n1 • d.wde) (d.et c)) :=
        mul_le_mul_of_nonneg_left this hf
    _ = _ := by ring
end ReciprocityTheory.ChartRestriction.G.T0.Data

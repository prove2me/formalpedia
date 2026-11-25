-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.Nla_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:48:19.716456+00:00
-- url     : https://prove2.me/submissions/efafc8f7-ba1a-4aed-94e8-57865f34298b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogNormNonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_NlaG_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_admissible_over_prime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_places_over_la


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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (hH1 : d.FinitePlaceHyp) (f : ∀ c, A c)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    d.NlaG h d.wL f la ≤ d.NlaMM h f la + d.del * d.nu la +
      d.cc / d.i * d.NlaG h (d.n1 • d.wde) d.et la := by
  have hnn := d.NlaG_nonneg hd h la
  have hi : (0 : ℝ) ≤ d.cc / d.i := div_nonneg hd.cc_nonneg (Nat.cast_nonneg _)
  suffices key : d.NlaG h d.wL f la ≤ d.NlaMM h f la + d.del * d.nu la +
      d.cc / (2 * d.i) * d.NlaG h (d.n1 • d.wde) d.et la by
    have : d.cc / (2 * d.i) * d.NlaG h (d.n1 • d.wde) d.et la ≤ d.cc / d.i * d.NlaG h (d.n1 • d.wde) d.et la := by
      have : d.cc / (2 * d.i) = (d.cc / d.i) / 2 := by ring
      rw [this]; nlinarith
    linarith
  unfold NlaG NlaMM del
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  have hfin := (d.places_over_la hd h la c).1
  have hsum := (d.places_over_la hd h la c).2
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum ⊢
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsumR : (d.delc c : ℝ) = ∑ w ∈ hfin.toFinset, (d.fze h c w : ℝ) * (ramIdx (K := K) (d.Wres c w) la : ℝ) := by
    have e := congrArg (fun z : ℤ => (z : ℝ)) hsum
    push_cast at e
    linarith
  rw [hsumR, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  have hs := d.admissible_over_prime hd h la c w hw
  have h3 := hH1.2.2.2 c (d.Wres c w) la hs.1 hs.2.1
  have hf : (0 : ℝ) ≤ d.fze h c w := Nat.cast_nonneg _
  unfold ordMM
  push_cast
  have e : ((⨅ j : {j // d.w j c ≠ 0}, d.ord c (d.Wres c w) d.wL (d.w j c) : ℤ) : ℝ) =
    (d.Emin c (d.Wres c w) : ℝ) := rfl
  rw [e] at h3 ⊢
  nlinarith [mul_le_mul_of_nonneg_left h3 hf]
end ReciprocityTheory.ChartRestriction.G.T0.Data

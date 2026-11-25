-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.aNla_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:11.07861+00:00
-- url     : https://prove2.me/submissions/daf48141-2c21-44d7-966f-305e1ac82f05

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_Wres_apply
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
    (ta : ∀ c, A c) (a : ∀ c, Ω c) (ha : ∀ c, a c ≠ 0)
    (hOs : ∀ c v, d.admitted c v → ((O c v (a c • ta c) : ℤ) : WithTop ℤ) = v (a c) + (O c v (ta c) : WithTop ℤ))
    (la : HeightOneSpectrum (𝓞 K)) :
    d.aNla h O (fun c => a c • ta c) la =
      d.aNla h O ta la + ∑ c, (d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a c)) : ℝ) := by
  unfold aNla
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  have hfin := (d.places_over_la hd h la c).1
  unfold nLa
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Set.Finite.mem_toFinset] at hw
  have hv := (d.admissible_over_prime hd h la c w hw).1
  rw [d.shift hv (ha c) (hOs c _ hv)]
  push_cast
  rw [d.Wres_apply]
  ring
end ReciprocityTheory.ChartRestriction.G.T0.Data

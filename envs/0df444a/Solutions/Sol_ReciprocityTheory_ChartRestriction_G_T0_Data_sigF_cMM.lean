-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.sigF_cMM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:12:21.20533+00:00
-- url     : https://prove2.me/submissions/81b0f2f3-386b-45b0-b9eb-3e7a053d9778

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_prod_zpow_eq_zpow_sum_height
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sigF_algebraMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_algebraMap_K_KTf
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_primes_properties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scale_multiHomogeneous
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
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (b : Fin (d.D + 1)) (u : Kˣ) :
    sigF b u (d.cMM h c) =
      algebraMap K (KTf K d.D d.N) ((u : K) ^ (if b = 0 then (0 : ℤ) else d.aMM h c)) * d.cMM h c := by
  classical
  have x2 := d.good_primes_properties hd h c
  have hfin := x2.2.2.2 _ (hd.w_mem (d.jc c) c) (hd.w_base c)
  set S := hfin.toFinset
  have hS : ∀ p ∈ S, p ∈ d.HtOne := fun p hp => ((Set.Finite.mem_toFinset _).1 hp).1
  have hsub : ∀ p, p ∈ d.HtOne → d.nPMM h c (d.w (d.jc c) c) p ≠ 0 → p ∈ S := fun p hp h1 =>
    (Set.Finite.mem_toFinset _).2 ⟨hp, h1⟩
  have eC : d.cMM h c = ∏ p ∈ S,
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p := by
    unfold cMM
    refine finprod_mem_eq_prod_of_subset _ ?_ (fun p hp => hS p hp)
    rintro p ⟨hp, hne⟩
    by_contra hpS
    have : d.nPMM h c (d.w (d.jc c) c) p = 0 := by
      by_contra h1; exact hpS (hsub p hp h1)
    exact hne (by simp [this])
  have eA : d.aMM h c = ∑ p ∈ S, d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ) := by
    unfold aMM
    refine finsum_mem_eq_sum_of_subset _ ?_ (fun p hp => hS p hp)
    rintro p ⟨hp, hne⟩
    by_contra hpS
    have : d.nPMM h c (d.w (d.jc c) c) p = 0 := by
      by_contra h1; exact hpS (hsub p hp h1)
    exact hne (by simp [this])
  have hfac : ∀ p ∈ S, sigF b u (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
        d.nPMM h c (d.w (d.jc c) c) p) =
      algebraMap K (KTf K d.D d.N) ((u : K) ^ (if b = 0 then (0 : ℤ) else
        d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ))) *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p := by
    intro p hp
    have hpH := hS p hp
    have hne : d.nPMM h c (d.w (d.jc c) c) p ≠ 0 := ((Set.Finite.mem_toFinset _).1 hp).2
    have hg : ∃ w, w ∈ d.GoodP c p := by
      by_contra hno
      push_neg at hno
      have hG : d.GoodP c p = ∅ := Set.eq_empty_iff_forall_notMem.mpr hno
      apply hne
      unfold nPMM
      rw [hG]
      simp
    have hm := x2.2.1 p hpH hg
    rw [map_zpow₀, d.sigF_algebraMap, sigP, scale_multiHomogeneous b u _ _ hm, map_mul, mul_zpow,
      ← d.algebraMap_K_KTf]
    congr 1
    by_cases hb : b = 0
    · simp [hb]
    · simp only [hb, if_false]
      rw [← map_zpow₀, ← zpow_natCast, ← zpow_mul, mul_comm]
  rw [eC, map_prod, Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, ← map_prod,
    prod_zpow_eq_zpow_sum_height _ _ _ (Units.ne_zero u)]
  congr 2
  by_cases hb : b = 0
  · simp [hb]
  · simp [hb, eA]
end ReciprocityTheory.ChartRestriction.G.T0.Data

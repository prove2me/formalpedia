-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.pi_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:57:18.380011+00:00
-- url     : https://prove2.me/submissions/872b87c8-e060-440c-87dc-d9ddd97b90ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DecompBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstRowZeroFixOfDegreeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_substRowZero_fix_of_degree_zero
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_GeneratorMultiHomogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_generator_ne_zero_of_height
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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (f : A c) :
    ∃ Pp Pm : KTp K d.D d.N, Pm ≠ 0 ∧ (∀ x, d.sub0 x Pp = Pp) ∧ (∀ x, d.sub0 x Pm = Pm) ∧
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pp =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pm *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c f p := by
  classical
  have hfix : ∀ p ∈ d.HtOne, d.nPMM h c f p ≠ 0 → ∀ x, d.sub0 x (d.gen p) = d.gen p := by
    intro p hp hn x
    have hw : ∃ w, w ∈ d.GoodP c p := by
      by_contra hno
      push_neg at hno
      exact hn (by simp [Data.nPMM, hno])
    have hm := d.GeneratorMultiHomogeneous hd h c p hp hw
    refine d.substRowZero_fix_of_degree_zero x (d.gen p) fun s hs => ?_
    simpa using hm s hs 0
  rw [finprod_mem_def, finprod_def]
  split_ifs with hfin
  · set T := hfin.toFinset with hT
    have hTmem : ∀ p ∈ T, p ∈ d.HtOne ∧ d.nPMM h c f p ≠ 0 := by
      intro p hpT
      have hpT' : p ∈ Function.mulSupport (d.HtOne.mulIndicator fun p =>
          (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)) (d.gen p) ^ d.nPMM h c f p) :=
        (Set.Finite.mem_toFinset (hs := hfin)).mp hpT
      rw [Function.mem_mulSupport] at hpT'
      by_cases hp : p ∈ d.HtOne
      · refine ⟨hp, fun h0 => hpT' ?_⟩
        simp [Set.mulIndicator_of_mem hp, h0]
      · simp [hp] at hpT'
    refine ⟨∏ p ∈ T, d.gen p ^ (d.nPMM h c f p).toNat,
      ∏ p ∈ T, d.gen p ^ (-d.nPMM h c f p).toNat, ?_, ?_, ?_, ?_⟩
    · exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (d.generator_ne_zero_of_height p (hTmem p hp).1)
    · intro x
      rw [map_prod]
      exact Finset.prod_congr rfl fun p hp => by
        rw [map_pow, hfix p (hTmem p hp).1 (hTmem p hp).2 x]
    · intro x
      rw [map_prod]
      exact Finset.prod_congr rfl fun p hp => by
        rw [map_pow, hfix p (hTmem p hp).1 (hTmem p hp).2 x]
    · rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Set.mulIndicator_of_mem (hTmem p hp).1]
      have ha : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)),
          (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)).eq_iff]
        exact d.generator_ne_zero_of_height p (hTmem p hp).1
      rw [map_pow, map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ha]
      congr 1
      omega
  · exact ⟨1, 1, one_ne_zero, fun x => map_one _, fun x => map_one _, by simp⟩
end ReciprocityTheory.ChartRestriction.G.T0.Data

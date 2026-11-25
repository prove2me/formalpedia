-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.norm_ratio_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:12:46.543904+00:00
-- url     : https://prove2.me/submissions/30b3bf07-208b-4ed2-a7e2-965f9c09b87d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_X4v4RatioSpec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_x4v4_ratio_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_x4v4_wx_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_x4v4_gen_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_x4v4_split
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_primes_properties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_factorization_clause
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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (x : Fin (d.N + 1) → K)
    (hx : d.wx x c ≠ 0) :
    ∃ κ : K, κ ≠ 0 ∧
      (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
        Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
            (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c))) *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p) := by
  classical
  have hmem := d.x4v4_wx_mem hd x c
  have hg0 := d.x4v4_ratio_ne hd c hmem hx
  obtain ⟨κ, hκ, hN⟩ := d.norm_factorization_clause hd h c _ hg0
  refine ⟨κ, hκ, ?_⟩
  rw [hN, mul_assoc]
  congr 1
  set na : Ideal (KTp K d.D d.N) → ℤ := fun p =>
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0
        (d.Wres c w (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c))) with hna
  set G : Ideal (KTp K d.D d.N) → KTf K d.D d.N := fun p =>
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) with hG
  have hsplit : ∀ p ∈ d.HtOne, d.nPMM h c (d.wx x c) p = na p + d.nPMM h c (d.w (d.jc c) c) p :=
    fun p hp => d.x4v4_split hd h c hp hmem hx
  have hSx := (d.good_primes_properties hd h c).2.2.2 _ hmem hx
  have hSj := (d.good_primes_properties hd h c).2.2.2 _ (hd.w_mem _ c) (hd.w_base c)
  have hfa : (d.HtOne ∩ Function.mulSupport fun p => G p ^ na p).Finite := by
    refine (hSx.union hSj).subset fun p hp => ?_
    have hn : na p ≠ 0 := by
      intro h0; apply hp.2; simp only [h0, zpow_zero]
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hc
    apply hn
    have e := hsplit p hp.1
    rw [hc.1 hp.1, hc.2 hp.1] at e
    omega
  have hfj : (d.HtOne ∩ Function.mulSupport fun p => G p ^ d.nPMM h c (d.w (d.jc c) c) p).Finite := by
    refine hSj.subset fun p hp => ⟨hp.1, ?_⟩
    intro h0; apply hp.2; simp only [h0, zpow_zero]
  show (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ na p) *
      (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ d.nPMM h c (d.w (d.jc c) c) p) =
    ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ d.nPMM h c (d.wx x c) p
  rw [← finprod_mem_mul_distrib' hfa hfj]
  refine finprod_mem_congr rfl fun p hp => ?_
  rw [hsplit p hp, zpow_add₀ (d.x4v4_gen_ne hp)]
end ReciprocityTheory.ChartRestriction.G.T0.Data

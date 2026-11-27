-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.substituted_factorization_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T06:19:03.622806+00:00
-- url     : https://prove2.me/submissions/b8a3e4ca-4c72-4b52-94c4-f5a334b9b191

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ComponentFormProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IntNsg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrdEqValuationRatioBaseAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SpecialFibreFactorization
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationGenericRatioEqRestriction
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_exists_ne_zero_of_finsum_mem_ne_zero__a210564d8b11
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_multiplicity_split_finsum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_algebraMap_gen_ne_zero
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_SpecialFibreFactorization
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_primes_properties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_linearCombination_mem_section
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_by_places
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_factorization
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_ratio_base_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero



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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ∃ κ : K, κ ≠ 0 ∧ d.heightSubstitutionCondition h x c F κ := by
  set a := ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) with ha_def
  have hmem := d.linearCombination_mem_section hd x c
  have ha : a ≠ 0 := d.ratio_base_ne_zero hd c hmem (hx c)
  obtain ⟨κ1, hκ1, e1⟩ := d.SpecialFibreFactorization hd h c F hF x (hx c)
  obtain ⟨κ3, hκ3, e3⟩ := (d.norm_factorization hd h).1 c a ha
  set na : Ideal (KTp K d.D d.N) → ℤ := fun p =>
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w a) with hna
  have hsplit : ∀ p ∈ d.HtOne, d.nPMM h c (d.wx x c) p = na p + d.nPMM h c (d.w (d.jc c) c) p :=
    fun p hp => d.multiplicity_split_finsum hd h c hp hmem (hx c)
  have hyne : algebraMap (Ω c) (OmS (Ω c) d.D d.N) a ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (Ω c) (OmS (Ω c) d.D d.N)).injective).mpr ha
  have hSa := ((d.norm_by_places hd h c).2 _ hyne).1
  have hSj := (d.good_primes_properties hd h c).2.2.2 _ (hd.w_mem _ c) (hd.w_base c)
  set g : Ideal (KTp K d.D d.N) → KTf K d.D d.N := fun p =>
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) with hg
  have hfa : (d.HtOne ∩ Function.mulSupport fun p => g p ^ na p).Finite := by
    refine hSa.subset fun p hp => ⟨hp.1, ?_⟩
    have hn : na p ≠ 0 := by
      intro h0; apply hp.2; simp only [h0, zpow_zero]
    obtain ⟨w, hw, hne⟩ := exists_ne_zero_of_finsum_mem_ne_zero' hn
    refine ⟨w, hw.1, fun h0 => hne ?_⟩
    show (d.fze h c w : ℤ) * WithTop.untopD 0 (w _) = 0
    rw [h0]; simp
  have hfj : (d.HtOne ∩ Function.mulSupport fun p => g p ^ d.nPMM h c (d.w (d.jc c) c) p).Finite := by
    refine hSj.subset fun p hp => ⟨hp.1, ?_⟩
    intro h0; apply hp.2; simp only [h0, zpow_zero]
  have hprod : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), g p ^ d.nPMM h c (d.wx x c) p) =
      (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), g p ^ na p) *
        ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), g p ^ d.nPMM h c (d.w (d.jc c) c) p := by
    rw [← finprod_mem_mul_distrib' hfa hfj]
    refine finprod_mem_congr rfl fun p hp => ?_
    rw [hsplit p hp, zpow_add₀ (d.algebraMap_gen_ne_zero hp)]
  refine ⟨κ1 / κ3, div_ne_zero hκ1 hκ3, ?_⟩
  unfold heightSubstitutionCondition translatedForm
  rw [hF, e1, e3, hprod]
  unfold fZ
  have h3 : algebraMap K (KTf K d.D d.N) κ3 ≠ 0 := (map_ne_zero _).mpr hκ3
  rw [map_div₀]
  simp only [hg, hna]
  field_simp
end ReciprocityTheory.ChartRestriction.G.T0.Data

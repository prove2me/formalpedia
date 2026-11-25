-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.arithDegree_additive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:00:43.986323+00:00
-- url     : https://prove2.me/submissions/76af275c-79a1-4cb1-943f-18b0df02e1c2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_key_degree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_nP_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_nP_smul
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_use__fb60b9f90987
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_primes_properties
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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) :
    (∀ (G : WT) (ta ta' : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c G ∧ ta' c ≠ 0) → d.aG h G ta = d.aG h G ta') ∧
    (∀ (G G' : WT) (ta ta' : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c G' ∧ ta' c ≠ 0) → d.aG h (G + G') (ta * ta') = d.aG h G ta + d.aG h G' ta') := by
  have hfin1 : ∀ c (G : WT) (f : A c), f ∈ 𝒜 c G → f ≠ 0 →
      (d.HtOne ∩ Function.support fun p => d.nP h c G f p * (d.dg (d.gen p) : ℤ)).Finite := by
    intro c G f hf hf0
    refine ((d.good_primes_properties hd h c).2.2.1 G f hf hf0).subset ?_
    rintro p ⟨hp, hs⟩
    refine ⟨hp, fun h0 => hs ?_⟩
    simp [h0]
  refine ⟨?_, ?_⟩
  · intro G ta ta' hta hta'
    unfold aG
    refine Finset.sum_congr rfl fun c _ => ?_
    have hv : (⟨ta c, (hta c).1⟩ : 𝒜 c G) ≠ 0 := by
      intro h0
      apply (hta c).2
      simpa using congrArg Subtype.val h0
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hv).mp (hd.finrank_one c G)
      ⟨ta' c, (hta' c).1⟩
    have ha' : a • ta c = ta' c := congrArg Subtype.val ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply (hta' c).2
      rw [← ha', zero_smul]
    have hS : (d.HtOne ∩ Function.support fun p =>
        (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
          (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w a)) * (d.dg (d.gen p) : ℤ)).Finite := by
      refine (d.use₈ hd h c a ha0).subset ?_
      rintro p ⟨hp, hs⟩
      refine ⟨hp, fun h0 => hs ?_⟩
      simp [h0]
    have e : ∀ p ∈ d.HtOne, d.nP h c G (a • ta c) p * (d.dg (d.gen p) : ℤ) =
        d.nP h c G (ta c) p * (d.dg (d.gen p) : ℤ) +
          (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
            (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w a)) * (d.dg (d.gen p) : ℤ) := by
      intro p hp
      rw [d.nP_smul hd h c (hta c).1 (hta c).2 ha0 hp, add_mul]
    rw [← ha', finsum_mem_congr rfl e,
      finsum_mem_add_distrib' (hfin1 c G _ (hta c).1 (hta c).2) hS,
      d.key_degree hd h c a ha0, add_zero]
  · intro G G' ta ta' hta hta'
    unfold aG
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e : ∀ p ∈ d.HtOne, d.nP h c (G + G') ((ta * ta') c) p * (d.dg (d.gen p) : ℤ) =
        d.nP h c G (ta c) p * (d.dg (d.gen p) : ℤ) + d.nP h c G' (ta' c) p * (d.dg (d.gen p) : ℤ) := by
      intro p hp
      rw [Pi.mul_apply, d.nP_mul hd h c (hta c).1 (hta' c).1 (hta c).2 (hta' c).2 hp, add_mul]
    rw [finsum_mem_congr rfl e, finsum_mem_add_distrib' (hfin1 c G _ (hta c).1 (hta c).2)
      (hfin1 c G' _ (hta' c).1 (hta' c).2)]
end ReciprocityTheory.ChartRestriction.G.T0.Data

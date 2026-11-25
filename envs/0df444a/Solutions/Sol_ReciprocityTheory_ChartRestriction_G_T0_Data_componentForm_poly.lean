-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.componentForm_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:51:02.464932+00:00
-- url     : https://prove2.me/submissions/d0d3a615-f3c1-44d0-b176-ba96e1c205f4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_untopD_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_lineRatio_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_lineRatio_val_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_valuation_balance
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_generator_ne_zero_of_height
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_by_places


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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ F : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c ∧ F ≠ 0 := by
  classical
  have hy : d.rationalBaseRow c ≠ 0 := d.lineRatio_ne_zero hd c
  obtain ⟨hfin, hnb⟩ := d.norm_by_places hd h c
  obtain ⟨hT, κ, hκ, hN⟩ := hnb (d.rationalBaseRow c) hy
  obtain ⟨e1, he1⟩ : ∃ e1 : Ideal (KTp K d.D d.N) → ℤ, ∀ p, e1 p = ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) := ⟨_, fun _ => rfl⟩
  simp only [← he1] at hN
  have hg0 : ∀ p ∈ d.HtOne, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := fun p hp =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (d.generator_ne_zero_of_height p hp)
  have hzero : ∀ p ∈ d.HtOne, p ∉ {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w (d.rationalBaseRow c) ≠ 0} → e1 p = 0 ∧ d.nPMM h c (d.w (d.jc c) c) p = 0 := by
    intro p hp hpT
    have hw0 : ∀ w ∈ d.OverP c p, w (d.rationalBaseRow c) = 0 := fun w hw => by
      by_contra hne
      exact hpT ⟨hp, w, hw, hne⟩
    constructor
    · rw [he1, finsum_mem_congr rfl (fun w hw => (show (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) = 0 by
        rw [hw0 w hw]; simp)), finsum_mem_zero _]
    · unfold nPMM
      refine (finsum_mem_congr rfl (fun w hw => ?_)).trans (finsum_mem_zero _)
      have h1 := d.good_valuation_balance hd h c p hp w hw
      rw [hw0 w hw.1] at h1
      simp at h1
      show (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c) = 0
      rw [h1, mul_zero]
  have hnn : ∀ p ∈ d.HtOne, 0 ≤ e1 p + d.nPMM h c (d.w (d.jc c) c) p := by
    intro p hp
    have hOf := (hfin p hp)
    have hGsub : d.GoodP c p ⊆ d.OverP c p := fun w hw => hw.1
    have hGf : (d.GoodP c p).Finite := hOf.subset hGsub
    have hRf : (d.OverP c p \ d.GoodP c p).Finite := hOf.diff
    rw [he1, ← Set.union_diff_cancel hGsub, finsum_mem_union Set.disjoint_sdiff_right hGf hRf]
    unfold nPMM
    rw [add_right_comm, ← finsum_mem_add_distrib hGf]
    have hG0 : ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        ((d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) +
          (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c)) = 0 := by
      rw [finsum_mem_congr rfl (fun w hw => by rw [← mul_add, d.good_valuation_balance hd h c p hp w hw, mul_zero]),
        finsum_mem_zero _]
    rw [hG0, zero_add, finsum_mem_eq_finite_toFinset_sum _ hRf]
    refine Finset.sum_nonneg fun w hw => ?_
    rw [Set.Finite.mem_toFinset] at hw
    have htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0 := by
      intro a ha
      by_contra hne
      exact hw.2 ⟨hw.1, a, ha, hne⟩
    exact mul_nonneg (Nat.cast_nonneg _) (untopD_nonneg (d.lineRatio_val_nonneg c p w hw.1 htriv))
  have hms1 : (d.HtOne ∩ Function.mulSupport fun p => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ e1 p).Finite := by
    refine hT.subset fun p ⟨hp, hne⟩ => ?_
    by_contra hpT
    exact hne (by simp only [(hzero p hp hpT).1, zpow_zero])
  have hms2 : (d.HtOne ∩ Function.mulSupport fun p =>
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p).Finite := by
    refine hT.subset fun p ⟨hp, hne⟩ => ?_
    by_contra hpT
    exact hne (by simp only [(hzero p hp hpT).2, zpow_zero])
  have hms3 : (d.HtOne ∩ Function.mulSupport fun p => d.gen p ^ (e1 p + d.nPMM h c (d.w (d.jc c) c) p).toNat).Finite := by
    refine hT.subset fun p ⟨hp, hne⟩ => ?_
    by_contra hpT
    obtain ⟨h1, h2⟩ := hzero p hp hpT
    exact hne (by simp only [h1, h2, add_zero, Int.toNat_zero, pow_zero])
  refine ⟨MvPolynomial.C κ * ∏ᶠ (p) (_ : p ∈ d.HtOne), d.gen p ^ (e1 p + d.nPMM h c (d.w (d.jc c) c) p).toNat, ?_, ?_⟩
  · have hmap : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (∏ᶠ (p) (_ : p ∈ d.HtOne), d.gen p ^ (e1 p + d.nPMM h c (d.w (d.jc c) c) p).toNat) =
        ∏ᶠ (p) (_ : p ∈ d.HtOne), algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p ^ (e1 p + d.nPMM h c (d.w (d.jc c) c) p).toNat) :=
      MonoidHom.map_finprod_mem' (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)).toMonoidHom hms3
    rw [map_mul, hmap]
    unfold fZ
    rw [hN, mul_assoc, ← finprod_mem_mul_distrib' hms1 hms2,
      show algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C κ) = algebraMap K (KTf K d.D d.N) κ from
        (IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N) κ).symm]
    congr 1
    refine finprod_mem_congr rfl fun p hp => ?_
    rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (hnn p hp), zpow_add₀ (hg0 p hp)]
  · refine mul_ne_zero (by simpa using hκ) ?_
    exact finprod_mem_induction (fun x => x ≠ 0) one_ne_zero (fun x y hx hy => mul_ne_zero hx hy)
      fun p hp => pow_ne_zero _ (d.generator_ne_zero_of_height p hp)
end ReciprocityTheory.ChartRestriction.G.T0.Data

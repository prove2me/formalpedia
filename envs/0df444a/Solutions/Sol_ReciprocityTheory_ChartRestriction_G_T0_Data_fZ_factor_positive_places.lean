-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.fZ_factor_positive_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:35:11.671012+00:00
-- url     : https://prove2.me/submissions/6bb7e277-25ae-4dd1-ada8-cd996ce40c66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockSphereProbIsProbabilityMeasure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_generator_ne_zero_of_height
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_valuation_balance
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_lineRatio_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_lineRatio_val_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_by_places
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_untopD_nonneg


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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ∃ (κ : K) (T : Finset (Ideal (KTp K d.D d.N))) (e : Ideal (KTp K d.D d.N) → ℕ),
      κ ≠ 0 ∧ (↑T : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne ∧
      F = MvPolynomial.C κ * ∏ p ∈ T, d.gen p ^ e p ∧
      ∀ p ∈ T, 0 < e p → ∃ w ∈ d.OverP c p, (∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) ∧
        0 < w (d.rationalBaseRow c) := by
  classical
  have hy : d.rationalBaseRow c ≠ 0 := d.lineRatio_ne_zero hd c
  obtain ⟨hOfin, hrest⟩ := d.norm_by_places hd h c
  obtain ⟨hP0fin, κ, hκ, hnorm⟩ := hrest (d.rationalBaseRow c) hy
  obtain ⟨E, hE⟩ : ∃ E : Ideal (KTp K d.D d.N) → ℤ, ∀ p, E p =
      ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) := ⟨_, fun _ => rfl⟩
  obtain ⟨Nn, hNn⟩ : ∃ Nn : Ideal (KTp K d.D d.N) → ℤ, ∀ p, Nn p =
      ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p \ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) := ⟨_, fun _ => rfl⟩
  simp only [← hE] at hnorm

  have htriv : ∀ p w, w ∈ d.OverP c p \ d.GoodP c p → ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0 := by
    rintro p w ⟨hO, hG⟩ a ha
    by_contra hne
    exact hG ⟨hO, a, ha, hne⟩
  have hwy : ∀ p w, w ∈ d.OverP c p \ d.GoodP c p → 0 ≤ w (d.rationalBaseRow c) :=
    fun p w hw => d.lineRatio_val_nonneg c p w hw.1 (htriv p w hw)
  have hNn0 : ∀ p, 0 ≤ Nn p := by
    intro p
    rw [hNn]
    exact finsum_nonneg fun w => finsum_nonneg fun hw =>
      mul_nonneg (Nat.cast_nonneg _) (untopD_nonneg (hwy p w hw))

  have hsplit : ∀ p ∈ d.HtOne, E p + d.nPMM h c (d.w (d.jc c) c) p = Nn p := by
    intro p hp
    have hGsub : d.GoodP c p ⊆ d.OverP c p := fun w hw => hw.1
    have hGfin : (d.GoodP c p).Finite := (hOfin p hp).subset hGsub
    have hgood : d.nPMM h c (d.w (d.jc c) c) p =
        ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
          -((d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c))) := by
      unfold Data.nPMM
      refine finsum_mem_congr rfl fun w hw => ?_
      have h1 := d.good_valuation_balance hd h c p hp w hw
      rw [show d.ordMM c (d.Wres c w) (d.w (d.jc c) c) = -WithTop.untopD 0 (w (d.rationalBaseRow c)) by linarith]
      ring
    have hsum : (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c))) +
        ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
          -((d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c))) = 0 := by
      rw [← finsum_mem_add_distrib' (hGfin.inter_of_left _) (hGfin.inter_of_left _)]
      simp
    have hO := finsum_mem_union
      (f := fun w => (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)))
      (Set.disjoint_sdiff_right : Disjoint (d.GoodP c p) (d.OverP c p \ d.GoodP c p)) hGfin
      ((hOfin p hp).subset Set.diff_subset)
    rw [Set.union_diff_cancel hGsub] at hO
    beta_reduce at hO
    rw [hE, hNn, hgood, hO]
    linarith

  have hout : ∀ p ∈ d.HtOne, p ∉ {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w (d.rationalBaseRow c) ≠ 0} →
      E p = 0 ∧ Nn p = 0 := by
    intro p hp hpP
    have hz : ∀ w ∈ d.OverP c p, w (d.rationalBaseRow c) = 0 := by
      intro w hw
      by_contra hne
      exact hpP ⟨hp, w, hw, hne⟩
    constructor
    · rw [hE]
      refine (finsum_mem_congr rfl fun w hw => ?_).trans (finsum_mem_zero _)
      rw [hz w hw]
      simp
    · rw [hNn]
      refine (finsum_mem_congr rfl fun w hw => ?_).trans (finsum_mem_zero _)
      rw [hz w hw.1]
      simp
  have hTS : (↑hP0fin.toFinset : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne := by
    intro p hp
    rw [Set.Finite.coe_toFinset] at hp
    exact hp.1
  have hnotT : ∀ p ∈ d.HtOne, p ∉ hP0fin.toFinset →
      p ∉ {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w (d.rationalBaseRow c) ≠ 0} := by
    intro p _ hpT hpP
    exact hpT ((Set.Finite.mem_toFinset hP0fin).mpr hpP)
  have hgen0 : ∀ p ∈ d.HtOne, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := fun p hp =>
    (map_ne_zero_iff _ (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N))).mpr
      (d.generator_ne_zero_of_height p hp)
  have hprodE : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p) =
      ∏ p ∈ hP0fin.toFinset, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p := by
    refine finprod_mem_eq_prod_of_subset _ ?_ hTS
    rintro p ⟨hpS, hpm⟩
    by_contra hpT
    apply hpm
    show algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p = 1
    rw [(hout p hpS (hnotT p hpS hpT)).1, zpow_zero]
  have hprodM : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p) =
      ∏ p ∈ hP0fin.toFinset,
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p := by
    refine finprod_mem_eq_prod_of_subset _ ?_ hTS
    rintro p ⟨hpS, hpm⟩
    by_contra hpT
    apply hpm
    show algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p = 1
    have h1 := hout p hpS (hnotT p hpS hpT)
    have h2 := hsplit p hpS
    rw [show d.nPMM h c (d.w (d.jc c) c) p = 0 by linarith [h1.1, h1.2], zpow_zero]
  have hF' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
        (MvPolynomial.C κ * ∏ p ∈ hP0fin.toFinset, d.gen p ^ (Nn p).toNat) := by
    rw [hF]
    simp only [Data.fZ]
    rw [hnorm, hprodE, hprodM, mul_assoc, ← Finset.prod_mul_distrib, map_mul, map_prod]
    rw [IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N) κ, MvPolynomial.algebraMap_eq]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpS := hTS (Finset.mem_coe.mpr hp)
    rw [← zpow_add₀ (hgen0 p hpS), hsplit p hpS, map_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (hNn0 p)]
  refine ⟨κ, hP0fin.toFinset, fun p => (Nn p).toNat, hκ, hTS,
    IsFractionRing.injective _ _ hF', ?_⟩
  intro p hpT hpos
  by_contra hne
  push_neg at hne
  have hz : Nn p = 0 := by
    rw [hNn]
    refine (finsum_mem_congr rfl fun w hw => ?_).trans (finsum_mem_zero _)
    have h0 : w (d.rationalBaseRow c) = 0 := le_antisymm (hne w hw.1 (htriv p w hw)) (hwy p w hw)
    rw [h0]
    simp
  simp [hz] at hpos
end ReciprocityTheory.ChartRestriction.G.T0.Data

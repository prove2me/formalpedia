-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.fZ_factor_height_one_primes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:37:21.962743+00:00
-- url     : https://prove2.me/submissions/2f3a9fce-6d2b-481c-a3ab-82250d6df89e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZMultiHomogeneousDegreeSum
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_algebraMap_K_KTf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_generator_ne_zero_of_height
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_valuation_balance
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_lineRatio_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_lineRatio_val_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_by_places
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_untopD_nonneg
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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ∃ κ : K, κ ≠ 0 ∧ ∃ T : Finset (Ideal (KTp K d.D d.N)), ∃ e : Ideal (KTp K d.D d.N) → ℕ,
      (∀ p ∈ T, p ∈ d.HtOne) ∧ F = C κ * ∏ p ∈ T, d.gen p ^ e p ∧
      ∀ p ∈ T, e p ≠ 0 → ∃ w ∈ d.OverP c p, (∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) ∧
        0 < w (d.rationalBaseRow c) := by
  classical
  have hy : d.rationalBaseRow c ≠ 0 := d.lineRatio_ne_zero hd c
  obtain ⟨hfin, hall⟩ := d.norm_by_places hd h c
  obtain ⟨hSy, κ, hκ, hN⟩ := hall _ hy
  set T := hSy.toFinset with hT
  set Gm : Ideal (KTp K d.D d.N) → KTf K d.D d.N :=
    fun p => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) with hGm
  set a : Ideal (KTp K d.D d.N) → ℤ := fun p =>
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) with ha
  set b : Ideal (KTp K d.D d.N) → ℤ := fun p => d.nPMM h c (d.w (d.jc c) c) p with hb
  have hmemT : ∀ p, p ∈ T ↔ p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w (d.rationalBaseRow c) ≠ 0 := fun p =>
    Set.Finite.mem_toFinset hSy
  have hGne : ∀ p ∈ d.HtOne, Gm p ≠ 0 := fun p hp => by
    simp only [hGm]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N))).mpr
      (d.generator_ne_zero_of_height p hp)

  have hoff : ∀ p ∈ d.HtOne, p ∉ T → ∀ w ∈ d.OverP c p, w (d.rationalBaseRow c) = 0 := by
    intro p hp hpT w hw
    by_contra hne
    exact hpT ((hmemT p).mpr ⟨hp, w, hw, hne⟩)
  have ha0 : ∀ p ∈ d.HtOne, p ∉ T → a p = 0 := by
    intro p hp hpT
    simp only [ha]
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin p hp)]
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [hoff p hp hpT w ((Set.Finite.mem_toFinset _).mp hw)]
    simp
  have hb0 : ∀ p ∈ d.HtOne, p ∉ T → b p = 0 := by
    intro p hp hpT
    simp only [hb, Data.nPMM]
    have hGf : (d.GoodP c p).Finite := (hfin p hp).subset fun w hw => hw.1
    rw [finsum_mem_eq_finite_toFinset_sum _ hGf]
    refine Finset.sum_eq_zero fun w hw => ?_
    have hw' := (Set.Finite.mem_toFinset _).mp hw
    have := d.good_valuation_balance hd h c p hp w hw'
    rw [hoff p hp hpT w hw'.1] at this
    simp at this
    rw [this, mul_zero]
  have hab : ∀ p ∈ d.HtOne, 0 ≤ a p + b p := by
    intro p hp
    have hGf : (d.GoodP c p).Finite := (hfin p hp).subset fun w hw => hw.1
    have e1 : a p = ∑ w ∈ (hfin p hp).toFinset,
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) :=
      finsum_mem_eq_finite_toFinset_sum _ (hfin p hp)
    have e2 : b p = ∑ w ∈ (hfin p hp).toFinset,
        if w ∈ d.GoodP c p then (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c) else 0 := by
      rw [← Finset.sum_filter]
      simp only [hb, Data.nPMM]
      rw [finsum_mem_eq_finite_toFinset_sum _ hGf]
      congr 1
      ext w
      simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
      exact ⟨fun hw => ⟨hw.1, hw⟩, fun hw => hw.2⟩
    rw [e1, e2, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun w hw => ?_
    have hwO := (Set.Finite.mem_toFinset _).mp hw
    by_cases hg : w ∈ d.GoodP c p
    · rw [if_pos hg, ← mul_add, d.good_valuation_balance hd h c p hp w hg, mul_zero]
    · rw [if_neg hg, add_zero]
      refine mul_nonneg (by positivity) (untopD_nonneg ?_)
      refine d.lineRatio_val_nonneg c p w hwO fun a0 ha0' => ?_
      by_contra hne
      exact hg ⟨hwO, a0, ha0', hne⟩
  have hTsub : (T : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne := fun p hp => ((hmemT p).mp hp).1
  have e1 : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), Gm p ^ a p) = ∏ p ∈ T, Gm p ^ a p := by
    refine finprod_mem_eq_prod_of_subset _ ?_ hTsub
    rintro p ⟨hp, hne⟩
    by_contra hpT
    exact hne (by simp only [ha0 p hp hpT, zpow_zero])
  have e2 : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), Gm p ^ b p) = ∏ p ∈ T, Gm p ^ b p := by
    refine finprod_mem_eq_prod_of_subset _ ?_ hTsub
    rintro p ⟨hp, hne⟩
    by_contra hpT
    exact hne (by simp only [hb0 p hp hpT, zpow_zero])
  have hfZ : d.fZ h c = algebraMap K (KTf K d.D d.N) κ * ∏ p ∈ T, Gm p ^ (a p + b p) := by
    have hN' := hN
    unfold Data.fZ
    rw [hN', e1, e2, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p hp => (zpow_add₀ (hGne p (hTsub hp)) _ _).symm
  refine ⟨κ, hκ, T, fun p => (a p + b p).toNat, fun p hp => hTsub hp, ?_, ?_⟩
  · apply IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
    rw [hF, hfZ, map_mul, map_prod, ← d.algebraMap_K_KTf]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (hab p (hTsub hp))]
  · intro p hpT he
    have hp := hTsub hpT
    have hne : a p + b p ≠ 0 := fun h0 => he (by simp only [h0, Int.toNat_zero])
    have hGf : (d.GoodP c p).Finite := (hfin p hp).subset fun w hw => hw.1
    have e1 : a p = ∑ w ∈ (hfin p hp).toFinset,
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) :=
      finsum_mem_eq_finite_toFinset_sum _ (hfin p hp)
    have e2 : b p = ∑ w ∈ (hfin p hp).toFinset,
        if w ∈ d.GoodP c p then (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c) else 0 := by
      rw [← Finset.sum_filter]
      simp only [hb, Data.nPMM]
      rw [finsum_mem_eq_finite_toFinset_sum _ hGf]
      congr 1
      ext w
      simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
      exact ⟨fun hw => ⟨hw.1, hw⟩, fun hw => hw.2⟩
    rw [e1, e2, ← Finset.sum_add_distrib] at hne
    obtain ⟨w, hwF, hw0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hwO := (Set.Finite.mem_toFinset _).mp hwF
    by_cases hg : w ∈ d.GoodP c p
    · rw [if_pos hg, ← mul_add, d.good_valuation_balance hd h c p hp w hg, mul_zero] at hw0
      exact absurd rfl hw0
    · rw [if_neg hg, add_zero] at hw0
      have htriv : ∀ a0 : Ω c, a0 ≠ 0 → d.Wres c w a0 = 0 := fun a0 ha0 => by
        by_contra hne'
        exact hg ⟨hwO, a0, ha0, hne'⟩
      have hnn := d.lineRatio_val_nonneg c p w hwO htriv
      have hu : WithTop.untopD 0 (w (d.rationalBaseRow c)) ≠ 0 := right_ne_zero_of_mul hw0
      exact ⟨w, hwO, htriv, lt_of_le_of_ne hnn fun h0 => hu (by rw [← h0]; rfl)⟩
end ReciprocityTheory.ChartRestriction.G.T0.Data

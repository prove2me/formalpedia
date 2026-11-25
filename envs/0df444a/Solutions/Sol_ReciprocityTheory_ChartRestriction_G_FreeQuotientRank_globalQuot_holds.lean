-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.globalQuot_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:07:09.215845+00:00
-- url     : https://prove2.me/submissions/ace12612-bf36-4ad9-aaf6-0e4e74608a9d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_finite_ordAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_finsum_ordAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_log_det_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution : GlobalQuotStatement := by
  intro K _ _ ρ m hdet s β a b B Bfin hs hβ harch hdeg hfin
  classical
  set n : ℝ := (Module.finrank ℚ K : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Module.finrank_pos
  have hsum : ∑ σ : InfinitePlace K, (σ.mult : ℝ) = n := by
    rw [hn]; exact_mod_cast InfinitePlace.sum_mult_eq
  have hord := finite_ordAt (K := K) hdet
  have hsU : (⋃ i, Function.support (s i)).Finite := Set.finite_iUnion hs
  set T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
    (hord.union (hsU.union hβ)).toFinset with hT
  have memT : ∀ w, w ∈ (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => (ordAt v m.det : ℝ) * logN v) ∪
      ((⋃ i, Function.support (s i)) ∪ Function.support β) → w ∈ T := by
    intro w hw; rw [hT, Set.Finite.mem_toFinset]; exact hw
  have e1 : ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (ordAt w m.det : ℝ) * logN w = ∑ w ∈ T, (ordAt w m.det : ℝ) * logN w := by
    apply finsum_eq_sum_of_support_subset
    intro w hw; exact memT w (Or.inl hw)
  have e2 : ∀ i, ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), s i w * logN w = ∑ w ∈ T, s i w * logN w := by
    intro i; apply finsum_eq_sum_of_support_subset
    intro w hw
    simp only [Function.mem_support, ne_eq] at hw
    refine memT w (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨i, fun h => hw ?_⟩)))
    rw [h, zero_mul]
  have e3 : ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), β w * logN w = ∑ w ∈ T, β w * logN w := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    simp only [Function.mem_support, ne_eq] at hw
    refine memT w (Or.inr (Or.inr fun h => hw ?_))
    rw [h, zero_mul]
  have e0 : ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w =
      ∑ w ∈ T, ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    simp only [Function.mem_support, ne_eq] at hw
    by_contra hnot
    apply hw
    have h1 : (ordAt w m.det : ℝ) * logN w = 0 := by
      by_contra h; exact hnot (memT w (Or.inl h))
    have h2 : ∀ i, s i w = 0 := fun i => by
      by_contra h; exact hnot (memT w (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨i, h⟩))))
    have h3 : β w = 0 := by
      by_contra h; exact hnot (memT w (Or.inr (Or.inr h)))
    rw [add_mul, add_mul, h1]
    simp [h2, h3]

  have hPF : ∑ w ∈ T, (ordAt w m.det : ℝ) * logN w =
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (σ m.det) := by
    rw [← e1]; exact finsum_ordAt hdet
  have hHad : ∀ σ : InfinitePlace K, Real.log (σ m.det) ≤
      ∑ j, b j σ - ∑ i, a i σ + (ρ : ℝ) / 2 * Real.log ρ := fun σ =>
    log_det_le m hdet σ (fun i => a i σ) (fun j => b j σ) fun i j h => harch σ i j h
  have hsumσ : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (σ m.det) ≤
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * (∑ j, b j σ - ∑ i, a i σ + (ρ : ℝ) / 2 * Real.log ρ) :=
    Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hHad σ) (Nat.cast_nonneg _)
  have hexp : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * (∑ j, b j σ - ∑ i, a i σ + (ρ : ℝ) / 2 * Real.log ρ) =
      ∑ j, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * b j σ -
        ∑ i, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * a i σ + n * ((ρ : ℝ) / 2 * Real.log ρ) := by
    have c1 : ∑ σ : InfinitePlace K, ∑ j, (σ.mult : ℝ) * b j σ =
        ∑ j, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * b j σ := Finset.sum_comm
    have c2 : ∑ σ : InfinitePlace K, ∑ i, (σ.mult : ℝ) * a i σ =
        ∑ i, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * a i σ := Finset.sum_comm
    have c3 : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * ((ρ : ℝ) / 2 * Real.log ρ) =
        n * ((ρ : ℝ) / 2 * Real.log ρ) := by rw [← Finset.sum_mul, hsum]
    rw [← c1, ← c2, ← c3, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_add, mul_sub, Finset.mul_sum, Finset.mul_sum]

  have hdeg' : ∀ i, ∑ w ∈ T, s i w * logN w - ∑ σ : InfinitePlace K, (σ.mult : ℝ) * a i σ ≤ B i * n := by
    intro i
    have := hdeg i
    rw [e2 i, div_le_iff₀ hnpos] at this
    exact this
  have hdegS : ∑ i, ∑ w ∈ T, s i w * logN w - ∑ i, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * a i σ ≤
      (∑ i, B i) * n := by
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hdeg' i
  have hfin' : ∑ w ∈ T, β w * logN w ≤ Bfin * n := by
    have := hfin
    rw [e3, div_le_iff₀ hnpos] at this
    exact this
  have hfinρ : (ρ : ℝ) * ∑ w ∈ T, β w * logN w ≤ ρ * (Bfin * n) :=
    mul_le_mul_of_nonneg_left hfin' (Nat.cast_nonneg _)

  have hL : ∑ w ∈ T, ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w =
      ∑ w ∈ T, (ordAt w m.det : ℝ) * logN w + ∑ i, ∑ w ∈ T, s i w * logN w +
        ρ * ∑ w ∈ T, β w * logN w := by
    have hw : ∀ w, ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w =
        (ordAt w m.det : ℝ) * logN w + ∑ i, s i w * logN w + ρ * (β w * logN w) := fun w => by
      rw [add_mul, add_mul, Finset.sum_mul]; ring
    rw [Finset.sum_congr rfl fun w _ => hw w, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_comm]
  have hR : (∑ j, (∑ σ : InfinitePlace K, (σ.mult : ℝ) * b j σ) / n) * n =
      ∑ j, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * b j σ := by
    rw [← Finset.sum_div, div_mul_cancel₀ _ hnpos.ne']
  rw [e0, hL, div_le_iff₀ hnpos, add_mul, add_mul, add_mul, hR]
  linarith [hPF, hsumσ, hexp, hdegS, hfinρ]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

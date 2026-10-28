-- Prove2me | solution 1 for PersonalizedRM.RevenueGap.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:31:02.566436+00:00
-- url     : https://prove2.me/submissions/60480236-4704-40ac-ba49-503687059da2

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model

open MeasureTheory ProbabilityTheory

open Filter Topology in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Set (EuclideanSpace ℝ ι))
    (f : EuclideanSpace ℝ ι → ℝ) (hf : Differentiable ℝ f) (η : ℝ) (hη : 0 < η)
    (hsc : StrongConvexOn K η f) (θstar θhat : EuclideanSpace ℝ ι) (hstar : θstar ∈ K)
    (hhat : θhat ∈ K) (hmin : IsMinOn f K θhat) (g : ℝ)
    (hg : ∀ k, |fderiv ℝ f θstar (EuclideanSpace.single k 1)| ≤ g) :
    ‖θhat - θstar‖ ≤ Real.sqrt (Fintype.card ι) * g / η := by
  set d := θhat - θstar with hd
  set D := ‖d‖ with hD
  set L := fderiv ℝ f θstar with hLdef
  have hD0 : 0 ≤ D := norm_nonneg _
  have hp : ∀ t : ℝ, (1 - t) • θstar + t • θhat = θstar + t • d := by
    intro t
    rw [hd, smul_sub, sub_smul, one_smul]
    abel
  have hmem : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → θstar + t • d ∈ K := by
    intro t h0 h1
    rw [← hp t]
    exact hsc.1 hstar hhat (sub_nonneg.2 h1) h0 (by ring)
  have hA : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f (θstar + t • d) ≤ (1 - t) * f θstar + t * f θhat - (1 - t) * t * (η / 2 * D ^ 2) := by
    intro t h0 h1
    have h := hsc.2 hstar hhat (sub_nonneg.2 h1) h0 (by ring)
    rw [hp t, smul_eq_mul, smul_eq_mul, norm_sub_rev] at h
    exact h
  have hminK : ∀ x ∈ K, f θhat ≤ f x := fun x hx => isMinOn_iff.mp hmin x hx
  -- step 1: f θhat - f θstar ≤ -η/2 * D^2
  have hB : f θhat - f θstar ≤ -η / 2 * 1 * D ^ 2 := by
    have hcont : Continuous (fun t : ℝ => -η / 2 * t * D ^ 2) := by fun_prop
    have lim : Tendsto (fun t : ℝ => -η / 2 * t * D ^ 2) (𝓝[<] 1) (𝓝 (-η / 2 * 1 * D ^ 2)) :=
      (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto lim (eventually_nhdsWithin_of_forall fun t (ht : t < 1) => ?_)
    by_cases h0 : t ≤ 0
    · have := hminK θstar hstar
      have : 0 ≤ -η / 2 * t * D ^ 2 := by
        have : 0 ≤ D ^ 2 := sq_nonneg D
        have : 0 ≤ -η / 2 * t := by nlinarith
        positivity
      linarith
    · push_neg at h0
      have h1 := hA t h0.le ht.le
      have h2 := hminK _ (hmem t h0.le ht.le)
      by_contra hc
      push_neg at hc
      have hpos : 0 < (1 - t) * ((f θhat - f θstar) - (-η / 2 * t * D ^ 2)) :=
        mul_pos (by linarith) (by linarith)
      nlinarith
  -- step 2: derivative bound
  have hγ : HasDerivAt (fun t : ℝ => θstar + t • d) d 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const d).const_add θstar
    simpa using this
  have hφ : HasDerivAt (f ∘ fun t : ℝ => θstar + t • d) (L d) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq 0 (hf θstar).hasFDerivAt hγ (by simp)
  have hC : L d ≤ -η * D ^ 2 := by
    have lim1 := hφ.tendsto_slope_zero_right
    have hcont : Continuous (fun t : ℝ => η / 2 * t * D ^ 2) := by fun_prop
    have lim2 : Tendsto (fun t : ℝ => η / 2 * t * D ^ 2) (𝓝[>] 0) (𝓝 (η / 2 * 0 * D ^ 2)) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have lim := lim1.sub lim2
    have key := le_of_tendsto lim (b := -η * D ^ 2) (by
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
      have ht0 := ht.1
      have ht1 := ht.2
      simp only [Function.comp_apply, zero_add, zero_smul, add_zero, smul_eq_mul]
      have h1 := hA t ht0.le ht1.le
      have hX : t⁻¹ * (f (θstar + t • d) - f θstar) ≤ -η * D ^ 2 + η / 2 * t * D ^ 2 := by
        rw [inv_mul_le_iff₀ ht0]
        nlinarith
      linarith)
    have : η / 2 * 0 * D ^ 2 = 0 := by ring
    linarith
  -- step 3: bound L d
  have hLd : L d = ∑ k, d k * L (EuclideanSpace.single k 1) := by
    have hdec : d = ∑ k, d k • EuclideanSpace.single k (1 : ℝ) := by
      have := (EuclideanSpace.basisFun ι ℝ).sum_repr d
      simpa using this.symm
    conv_lhs => rw [hdec]
    rw [map_sum]
    congr 1
    funext k
    rw [map_smul, smul_eq_mul]
  have hsum : ∑ k, |d k| ≤ Real.sqrt (Fintype.card ι) * D := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => |d k|)
    have hnorm : D = Real.sqrt (∑ k, d k ^ 2) := by
      rw [hD, EuclideanSpace.norm_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Real.norm_eq_abs, sq_abs]
    rw [hnorm, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    have : (∑ k, |d k|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ k, d k ^ 2 := by
      simpa [sq_abs, Finset.card_univ] using hcs
    exact (le_abs_self _).trans (Real.abs_le_sqrt this)
  have hgnn : 0 ≤ Real.sqrt (Fintype.card ι) * g := by
    by_cases hne : Nonempty ι
    · obtain ⟨k⟩ := hne
      have := (abs_nonneg _).trans (hg k)
      positivity
    · rw [not_nonempty_iff] at hne
      simp
  have hLabs : -L d ≤ Real.sqrt (Fintype.card ι) * g * D := by
    rw [hLd, ← Finset.sum_neg_distrib]
    calc ∑ k, -(d k * L (EuclideanSpace.single k 1)) ≤ ∑ k, |d k| * g := by
          apply Finset.sum_le_sum
          intro k _
          calc -(d k * L (EuclideanSpace.single k 1))
              ≤ |d k * L (EuclideanSpace.single k 1)| := neg_le_abs _
            _ = |d k| * |L (EuclideanSpace.single k 1)| := abs_mul _ _
            _ ≤ |d k| * g := mul_le_mul_of_nonneg_left (hg k) (abs_nonneg _)
      _ = (∑ k, |d k|) * g := by rw [Finset.sum_mul]
      _ ≤ Real.sqrt (Fintype.card ι) * D * g := by
          by_cases hg0 : 0 ≤ g
          · exact mul_le_mul_of_nonneg_right hsum hg0
          · push_neg at hg0
            have hne : IsEmpty ι := by
              by_contra hne
              rw [not_isEmpty_iff] at hne
              obtain ⟨k⟩ := hne
              have := (abs_nonneg _).trans (hg k)
              linarith
            simp [Finset.univ_eq_empty]
      _ = Real.sqrt (Fintype.card ι) * g * D := by ring
  have hfin : η * D ^ 2 ≤ Real.sqrt (Fintype.card ι) * g * D := by linarith
  rw [le_div_iff₀ hη]
  by_cases hDz : D = 0
  · rw [hDz, zero_mul]; exact hgnn
  · have hDpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hDz)
    nlinarith

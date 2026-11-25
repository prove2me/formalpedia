-- Prove2me | solution 1 for SNumbers.kolmogorovNumber_le_succ_mul_entropyNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:23:24.15898+00:00
-- url     : https://prove2.me/submissions/18896408-754c-43ba-b52f-fcce9d43b563

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_SNumbers_le_entropyNumber_of_separated
public import Theorems.Thm_SNumbers_exists_kolmogorov_flag
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_entropyNumber_nonneg
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.entropyNumber_zero_op
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL


section
@[expose] public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
private lemma le_succ_mul_of_sep {n : ℕ} {γ e : ℝ} (hn1 : (0 : ℝ) < (n : ℝ) + 1)
    (h : (2 * γ / ((n : ℝ) + 1)) / 2 ≤ e) : γ ≤ ((n : ℝ) + 1) * e := by
  have heq : (2 * γ / ((n : ℝ) + 1)) / 2 = γ / ((n : ℝ) + 1) := by ring
  rw [heq] at h
  calc γ = ((n : ℝ) + 1) * (γ / ((n : ℝ) + 1)) := by field_simp
    _ ≤ ((n : ℝ) + 1) * e := mul_le_mul_of_nonneg_left h hn1.le
private lemma norm_signedSum_le {n : ℕ} {x : Fin (n + 1) → X}
    (hx : ∀ j, ‖x j‖ ≤ 1) {a : Fin (n + 1) → 𝕜} (ha : ∀ k, ‖a k‖ ≤ 1) :
    ‖∑ k, a k • x k‖ ≤ (n : ℝ) + 1 := by
  calc ‖∑ k, a k • x k‖ ≤ ∑ k, ‖a k • x k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin (n + 1), (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_smul]
        nlinarith [ha k, hx k, norm_nonneg (a k), norm_nonneg (x k)]
    _ = (n : ℝ) + 1 := by simp
private lemma le_entropyNumber_of_sign_family {S : X →L[𝕜] Y} {n : ℕ} {δ : ℝ}
    {z : (Fin (n + 1) → Bool) → Y}
    (hmem : ∀ σ, z σ ∈ ⇑S '' Metric.closedBall 0 1)
    (hδ : 0 < δ) (hsep : ∀ σ τ, σ ≠ τ → δ ≤ dist (z σ) (z τ)) :
    δ / 2 ≤ entropyNumber S n := by
  classical
  have hz_inj : Function.Injective z := by
    intro σ τ hστ
    by_contra hne
    have h1 := hsep σ τ hne
    rw [hστ, dist_self] at h1
    linarith
  have hPcard : (Finset.image z Finset.univ).card = 2 ^ (n + 1) := by
    rw [Finset.card_image_of_injective _ hz_inj, Finset.card_univ, Fintype.card_fun]
    simp
  refine le_entropyNumber_of_separated (P := Finset.image z Finset.univ) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨σ, rfl⟩ := hy
    exact hmem σ
  · rw [hPcard]
    exact Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self n)
  · intro y hy y' hy' hyy
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy hy'
    obtain ⟨σ, rfl⟩ := hy
    obtain ⟨τ, rfl⟩ := hy'
    exact hsep σ τ fun h => hyy (by rw [h])
section Identity
open MeasureTheory
end Identity
section Hilbert
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
end Hilbert
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n ≤ ((n : ℝ) + 1) * entropyNumber S n := by
  classical
  by_contra hcon
  obtain ⟨γ, hγ1, hγ2⟩ := exists_between (not_le.mp hcon)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hγ0 : 0 < γ :=
    lt_of_le_of_lt (by positivity [entropyNumber_nonneg S n]) hγ1
  obtain ⟨x, V, hxnorm, hVmem, hVgt⟩ := exists_kolmogorov_flag S hγ2 (n + 1) le_rfl
  have hnorm_two : ‖(2 : 𝕜)‖ = 2 := by
    rw [show (2 : 𝕜) = ((2 : ℕ) : 𝕜) by push_cast; ring, RCLike.norm_natCast]
    norm_num
  -- The averaging scalar and the `2 ^ (n+1)` signed averages.
  set c : 𝕜 := ((((n : ℝ) + 1)⁻¹ : ℝ) : 𝕜) with hc
  have hcnorm : ‖c‖ = ((n : ℝ) + 1)⁻¹ := by
    rw [hc, RCLike.norm_ofReal, abs_of_pos (by positivity)]
  set sgn : Bool → 𝕜 := fun b => if b then 1 else -1 with hsgn
  have hsgn_norm : ∀ b, ‖sgn b‖ = 1 := by intro b; cases b <;> simp [hsgn]
  set z : (Fin (n + 1) → Bool) → Y := fun σ => S (c • ∑ k, sgn (σ k) • x k) with hz
  -- Each signed average lies in the image of the unit ball.
  have hz_mem : ∀ σ, z σ ∈ ⇑S '' Metric.closedBall 0 1 := by
    intro σ
    refine ⟨c • ∑ k, sgn (σ k) • x k, ?_, rfl⟩
    rw [mem_closedBall_zero_iff, norm_smul, hcnorm]
    have h1 : ‖∑ k, sgn (σ k) • x k‖ ≤ (n : ℝ) + 1 :=
      norm_signedSum_le hxnorm fun k => le_of_eq (hsgn_norm (σ k))
    calc ((n : ℝ) + 1)⁻¹ * ‖∑ k, sgn (σ k) • x k‖
        ≤ ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hn1)
  -- Distinct sign patterns give points more than `2γ/(n+1)` apart.
  have hsep : ∀ σ τ, σ ≠ τ → 2 * γ / ((n : ℝ) + 1) ≤ dist (z σ) (z τ) := by
    intro σ τ hne
    set D : Finset (Fin (n + 1)) := Finset.univ.filter (fun k => σ k ≠ τ k) with hD
    have hDne : D.Nonempty := by
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
      exact ⟨k, by simp [hD, hk]⟩
    set j := D.max' hDne with hj
    have hjne : σ j ≠ τ j := by
      have := D.max'_mem hDne
      simpa [hD, hj] using this
    set a : Fin (n + 1) → 𝕜 := fun k => sgn (σ k) - sgn (τ k) with ha
    have ha_zero : ∀ k, σ k = τ k → a k = 0 := by intro k h; simp [ha, h]
    have ha_norm : ∀ k, σ k ≠ τ k → ‖a k‖ = 2 := by
      intro k h
      have hcases : a k = 2 ∨ a k = -2 := by
        simp only [ha, hsgn]
        cases hb : σ k <;> cases hb' : τ k <;> simp [hb, hb'] at h ⊢ <;> norm_num
      rcases hcases with h2 | h2
      · rw [h2, hnorm_two]
      · rw [h2, norm_neg, hnorm_two]
    have haj_ne : a j ≠ 0 := by
      intro h0
      have h2 := ha_norm j hjne
      rw [h0, norm_zero] at h2
      norm_num at h2
    -- Split off the largest disagreeing index; the rest lies in `V j`.
    set u : Y := ∑ k ∈ Finset.univ.erase j, a k • S (x k) with hu
    have htail : u ∈ V j := by
      refine Submodule.sum_mem _ fun k hk => ?_
      by_cases hk_eq : σ k = τ k
      · rw [ha_zero k hk_eq, zero_smul]; exact Submodule.zero_mem _
      · have hkD : k ∈ D := by simp [hD, hk_eq]
        have hkj : k < j :=
          lt_of_le_of_ne (D.le_max' k hkD) (Finset.ne_of_mem_erase hk)
        exact Submodule.smul_mem _ _ (hVmem j k hkj)
    have hvec : z σ - z τ = c • (a j • (S (x j) + (a j)⁻¹ • u)) := by
      have h1 : (c • ∑ k, sgn (σ k) • x k) - (c • ∑ k, sgn (τ k) • x k)
          = c • ∑ k, a k • x k := by
        rw [← smul_sub, ← Finset.sum_sub_distrib]
        exact congrArg _ (Finset.sum_congr rfl fun k _ => (sub_smul _ _ _).symm)
      have h2 : S (c • ∑ k, a k • x k) = c • ∑ k, a k • S (x k) := by
        rw [map_smul, map_sum]
        exact congrArg _ (Finset.sum_congr rfl fun k _ => map_smul S _ _)
      have h3 : ∑ k, a k • S (x k) = a j • S (x j) + u :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
      have h4 : a j • (S (x j) + (a j)⁻¹ • u) = a j • S (x j) + u := by
        rw [smul_add, smul_inv_smul₀ haj_ne]
      rw [hz]
      simp only
      rw [← map_sub, h1, h2, h3, h4]
    have hinner : γ < ‖S (x j) + (a j)⁻¹ • u‖ :=
      hVgt j _ (Submodule.smul_mem _ _ htail)
    rw [dist_eq_norm, hvec, norm_smul, norm_smul, hcnorm, ha_norm j hjne]
    rw [div_eq_inv_mul, mul_comm 2 γ, ← mul_assoc]
    calc ((n : ℝ) + 1)⁻¹ * γ * 2
        ≤ ((n : ℝ) + 1)⁻¹ * (2 * ‖S (x j) + (a j)⁻¹ • u‖) := by
          rw [mul_comm 2 ‖S (x j) + (a j)⁻¹ • u‖, ← mul_assoc]
          have : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
          nlinarith [hinner.le]
      _ = ((n : ℝ) + 1)⁻¹ * (2 * ‖S (x j) + (a j)⁻¹ • u‖) := rfl
  -- Pigeonhole, then unwind the constants.
  exact absurd (le_succ_mul_of_sep hn1
    (le_entropyNumber_of_sign_family hz_mem (by positivity) hsep)) (not_le.mpr hγ1)
end SNumbers

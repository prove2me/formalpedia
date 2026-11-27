-- Prove2me | solution 1 for ShorNonsmooth.RAlgorithm.width_dilation_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:48:23.498802+00:00
-- url     : https://prove2.me/submissions/e6fe8896-52f5-4bb6-a6e6-1ee42d470c75

import Mathlib
import Definitions.Def_ShorNonsmooth_RAlgorithm_Widths

open scoped InnerProductSpace
open Filter Topology Metric Set
open scoped Pointwise

namespace ShorNonsmooth.RAlgorithm

variable {n : ℕ}

local notation "En" => EuclideanSpace ℝ (Fin n)

lemma dilation_apply' (β : ℝ) (ξ x : En) :
    dilation β ξ x = x + ((β - 1) * ⟪ξ, x⟫_ℝ) • ξ := by
  simp [dilation, mul_smul]

lemma inner_dilation_left (β : ℝ) (ξ x y : En) :
    ⟪dilation β ξ x, y⟫_ℝ = ⟪x, y⟫_ℝ + (β - 1) * ⟪ξ, x⟫_ℝ * ⟪ξ, y⟫_ℝ := by
  simp only [dilation_apply', inner_add_left, inner_smul_left, conj_trivial]

lemma dilation_symm (β : ℝ) (ξ x y : En) :
    ⟪dilation β ξ x, y⟫_ℝ = ⟪x, dilation β ξ y⟫_ℝ := by
  simp only [dilation_apply', inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    conj_trivial]
  have := real_inner_comm x ξ
  linear_combination (β - 1) * ⟪ξ, y⟫_ℝ * this

lemma adjoint_dilation (β : ℝ) (ξ : En) :
    ContinuousLinearMap.adjoint (dilation β ξ) = dilation β ξ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  exact dilation_symm β ξ x y

lemma inner_dilation_unit (β : ℝ) {ξ : En} (hξ : ‖ξ‖ = 1) (x : En) :
    ⟪dilation β ξ x, ξ⟫_ℝ = β * ⟪x, ξ⟫_ℝ := by
  rw [inner_dilation_left, real_inner_self_eq_norm_sq, hξ, real_inner_comm ξ x]
  ring

lemma norm_sq_dilation_unit (β : ℝ) {ξ : En} (hξ : ‖ξ‖ = 1) (x : En) :
    ‖dilation β ξ x‖ ^ 2 = ‖x‖ ^ 2 + (β ^ 2 - 1) * ⟪x, ξ⟫_ℝ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [dilation_apply', inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    conj_trivial]
  rw [real_inner_self_eq_norm_sq ξ, hξ, real_inner_comm ξ x]
  ring

/-! ### Support functions of compact sets -/

lemma bddAbove_inner_image {W : Set En} (hW : IsCompact W) (η : En) :
    BddAbove ((fun x => ⟪η, x⟫_ℝ) '' W) :=
  (hW.image (continuous_const.inner continuous_id)).bddAbove

lemma bddBelow_inner_image {W : Set En} (hW : IsCompact W) (η : En) :
    BddBelow ((fun x => ⟪η, x⟫_ℝ) '' W) :=
  (hW.image (continuous_const.inner continuous_id)).bddBelow

lemma inner_le_upperSupport {W : Set En} (hW : IsCompact W) (η : En) {x : En} (hx : x ∈ W) :
    ⟪η, x⟫_ℝ ≤ upperSupport η W :=
  le_csSup (bddAbove_inner_image hW η) ⟨x, hx, rfl⟩

lemma lowerSupport_le_inner {W : Set En} (hW : IsCompact W) (η : En) {x : En} (hx : x ∈ W) :
    lowerSupport η W ≤ ⟪η, x⟫_ℝ :=
  csInf_le (bddBelow_inner_image hW η) ⟨x, hx, rfl⟩

lemma dirWidth_nonneg {W : Set En} (hW : IsCompact W) (hne : W.Nonempty) (η : En) :
    0 ≤ dirWidth η W := by
  obtain ⟨x, hx⟩ := hne
  unfold dirWidth
  linarith [inner_le_upperSupport hW η hx, lowerSupport_le_inner hW η hx]

lemma inner_sub_le_dirWidth {W : Set En} (hW : IsCompact W) (η : En) {x y : En}
    (hx : x ∈ W) (hy : y ∈ W) : ⟪η, x - y⟫_ℝ ≤ dirWidth η W := by
  unfold dirWidth
  rw [inner_sub_right]
  linarith [inner_le_upperSupport hW η hx, lowerSupport_le_inner hW η hy]

lemma abs_inner_sub_le_dirWidth {W : Set En} (hW : IsCompact W) (η : En) {x y : En}
    (hx : x ∈ W) (hy : y ∈ W) : |⟪η, x - y⟫_ℝ| ≤ dirWidth η W := by
  rw [abs_le]
  refine ⟨?_, inner_sub_le_dirWidth hW η hx hy⟩
  have := inner_sub_le_dirWidth hW η hy hx
  rw [← neg_sub, inner_neg_right] at this
  linarith

lemma dirWidth_le_of_bounds {W : Set En} (hne : W.Nonempty) (η : En) {l u : ℝ}
    (h : ∀ x ∈ W, l ≤ ⟪η, x⟫_ℝ ∧ ⟪η, x⟫_ℝ ≤ u) : dirWidth η W ≤ u - l := by
  unfold dirWidth upperSupport lowerSupport
  have h1 : sSup ((fun x => ⟪η, x⟫_ℝ) '' W) ≤ u :=
    csSup_le (hne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact (h x hx).2)
  have h2 : l ≤ sInf ((fun x => ⟪η, x⟫_ℝ) '' W) :=
    le_csInf (hne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact (h x hx).1)
  linarith

lemma dirWidth_smul {W : Set En} (η : En) {c : ℝ} (hc : 0 ≤ c) :
    dirWidth (c • η) W = c * dirWidth η W := by
  have himg : (fun x => ⟪c • η, x⟫_ℝ) '' W = c • ((fun x => ⟪η, x⟫_ℝ) '' W) := by
    rw [← Set.image_smul, Set.image_image]
    congr 1
    ext x
    simp [inner_smul_left]
  unfold dirWidth upperSupport lowerSupport
  rw [himg, Real.sSup_smul_of_nonneg hc, Real.sInf_smul_of_nonneg hc, smul_eq_mul, smul_eq_mul]
  ring

lemma dirWidth_image (T : En →L[ℝ] En) (η : En) (W : Set En) :
    dirWidth η (T '' W) = dirWidth (ContinuousLinearMap.adjoint T η) W := by
  have himg : (fun x => ⟪η, x⟫_ℝ) '' (T '' W) =
      (fun x => ⟪ContinuousLinearMap.adjoint T η, x⟫_ℝ) '' W := by
    rw [Set.image_image]
    congr 1
    ext x
    simp [ContinuousLinearMap.adjoint_inner_left]
  unfold dirWidth upperSupport lowerSupport
  rw [himg]

lemma dirWidth_image_adjoint (T : En →L[ℝ] En) (η : En) (W : Set En) :
    dirWidth η (ContinuousLinearMap.adjoint T '' W) = dirWidth (T η) W := by
  rw [dirWidth_image, ContinuousLinearMap.adjoint_adjoint]

/-! ### Widths -/

lemma sphere_nonempty_of_pos (hn : 0 < n) : (sphere (0 : En) 1).Nonempty := by
  have : Nontrivial En := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  exact NormedSpace.sphere_nonempty.mpr zero_le_one

lemma width_le_dirWidth {W : Set En} (hW : IsCompact W) (hne : W.Nonempty) {η : En}
    (hη : ‖η‖ = 1) : width W ≤ dirWidth η W := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨ρ, _, rfl⟩
    exact dirWidth_nonneg hW hne ρ
  · exact ⟨η, by simpa using hη, rfl⟩

lemma le_width {W : Set En} (hn : 0 < n) {c : ℝ} (h : ∀ η : En, ‖η‖ = 1 → c ≤ dirWidth η W) :
    c ≤ width W := by
  apply le_csInf ((sphere_nonempty_of_pos hn).image _)
  rintro _ ⟨η, hη, rfl⟩
  exact h η (by simpa using hη)

lemma width_nonneg {W : Set En} (hn : 0 < n) (hW : IsCompact W) (hne : W.Nonempty) :
    0 ≤ width W :=
  le_width hn (fun η _ => dirWidth_nonneg hW hne η)

lemma mul_width_le_dirWidth {W : Set En} (hW : IsCompact W) (hne : W.Nonempty) (η : En) :
    ‖η‖ * width W ≤ dirWidth η W := by
  rcases eq_or_ne η 0 with rfl | hη
  · rw [norm_zero, zero_mul]; exact dirWidth_nonneg hW hne 0
  have hu : ‖‖η‖⁻¹ • η‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hη)]
  have h1 := width_le_dirWidth hW hne hu
  have h2 : η = ‖η‖ • (‖η‖⁻¹ • η) := by
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hη), one_smul]
  rw [h2, dirWidth_smul _ (norm_nonneg _), ← h2]
  exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

/-- Generalized Lemma 3.3: dilation along a chord which is long relative to the width. -/
theorem width_dilation_ge (hn : 0 < n) {W : Set En} (hW : IsCompact W) (hne : W.Nonempty)
    {z₁ z₂ : En} (hz₁ : z₁ ∈ W) (hz₂ : z₂ ∈ W) (hz : z₁ ≠ z₂)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) {θ : ℝ} (hθ : 0 < θ)
    (hw : width W ≤ θ * ‖z₁ - z₂‖) :
    width W / Real.sqrt (1 + (1 - β ^ 2) * θ ^ 2 / β ^ 2) ≤
      width (dilation β (‖z₁ - z₂‖⁻¹ • (z₁ - z₂)) '' W) := by
  set L := ‖z₁ - z₂‖ with hL
  have hLpos : 0 < L := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  set ξ : En := L⁻¹ • (z₁ - z₂) with hξdef
  have hξ : ‖ξ‖ = 1 := by
    rw [hξdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hLpos.ne']
  set d := width W with hd
  have hd0 : 0 ≤ d := width_nonneg hn hW hne
  set s := (1 - β ^ 2) * θ ^ 2 / β ^ 2 with hs
  have hs0 : 0 ≤ s := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg _ (by positivity)
    nlinarith
  have hsq : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.mpr (by linarith)
  apply le_width hn
  intro η hη
  set D := dirWidth η (dilation β ξ '' W) with hD
  have hDeq : D = dirWidth (dilation β ξ η) W := by
    rw [hD, dirWidth_image, adjoint_dilation]
  have hD0 : 0 ≤ D := by rw [hDeq]; exact dirWidth_nonneg hW hne _
  -- first bound
  have hA : ‖dilation β ξ η‖ * d ≤ D := by rw [hDeq]; exact mul_width_le_dirWidth hW hne _
  -- second bound
  have hB : β * L * |⟪η, ξ⟫_ℝ| ≤ D := by
    rw [hDeq]
    have := abs_inner_sub_le_dirWidth hW (dilation β ξ η) hz₁ hz₂
    have hz12 : z₁ - z₂ = L • ξ := by
      rw [hξdef, smul_smul, mul_inv_cancel₀ hLpos.ne', one_smul]
    rw [hz12, inner_smul_right, inner_dilation_unit β hξ, abs_mul, abs_mul,
      abs_of_pos hLpos, abs_of_pos hβ0] at this
    linarith
  set t := ⟪η, ξ⟫_ℝ ^ 2 with ht
  have hnorm : ‖dilation β ξ η‖ ^ 2 = 1 + (β ^ 2 - 1) * t := by
    rw [norm_sq_dilation_unit β hξ, hη]; ring
  have hA2 : (1 + (β ^ 2 - 1) * t) * d ^ 2 ≤ D ^ 2 := by
    rw [← hnorm, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hA 2
  have hB2 : β ^ 2 * L ^ 2 * t ≤ D ^ 2 := by
    have : (β * L * |⟪η, ξ⟫_ℝ|) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (by positivity) hB 2
    rw [mul_pow, mul_pow, sq_abs] at this
    linarith
  have hdL : d ^ 2 ≤ θ ^ 2 * L ^ 2 := by
    have : d ^ 2 ≤ (θ * L) ^ 2 := pow_le_pow_left₀ hd0 hw 2
    linarith [mul_pow θ L 2]
  -- combine
  have key : d ^ 2 ≤ D ^ 2 * (1 + s) := by
    have hβ2 : 0 < β ^ 2 := by positivity
    have ht0 : 0 ≤ t := sq_nonneg _
    have e1 : D ^ 2 * s * β ^ 2 = D ^ 2 * (1 - β ^ 2) * θ ^ 2 := by
      rw [hs]; field_simp
    have h1b : 0 ≤ 1 - β ^ 2 := by nlinarith
    -- D^2 s ≥ (1-β^2) t d^2
    have h3 : (1 - β ^ 2) * t * d ^ 2 ≤ D ^ 2 * s := by
      have : (1 - β ^ 2) * t * d ^ 2 * β ^ 2 ≤ D ^ 2 * s * β ^ 2 := by
        rw [e1]
        have := mul_le_mul_of_nonneg_left hdL (mul_nonneg h1b (mul_nonneg ht0 hβ2.le))
        nlinarith [mul_le_mul_of_nonneg_left hB2 (mul_nonneg h1b (sq_nonneg θ))]
      exact le_of_mul_le_mul_right this hβ2
    nlinarith
  rw [div_le_iff₀ hsq]
  have : Real.sqrt (d ^ 2) ≤ Real.sqrt (D ^ 2 * (1 + s)) := Real.sqrt_le_sqrt key
  rwa [Real.sqrt_sq hd0, Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD0] at this

end ShorNonsmooth.RAlgorithm

open ShorNonsmooth.RAlgorithm in
theorem solution {n : ℕ} (hn : 0 < n) (W : Set (EuclideanSpace ℝ (Fin n)))
    (hW_convex : Convex ℝ W) (hW_closed : IsClosed W) (hW_bdd : Bornology.IsBounded W)
    (hW_body : (interior W).Nonempty)
    (z₁ z₂ : EuclideanSpace ℝ (Fin n)) (hz₁ : z₁ ∈ W) (hz₂ : z₂ ∈ W)
    (β : ℝ) (hβ_pos : 0 < β) (hβ_le : β ≤ 1)
    (γ : ℝ) (hγ : γ = ‖z₁ - z₂‖ / width W) (hγ_ge : 1 ≤ γ) :
    width W / Real.sqrt (1 + (1 - β ^ 2) / (β ^ 2 * γ ^ 2)) ≤
      width (dilation β (‖z₁ - z₂‖⁻¹ • (z₁ - z₂)) '' W) := by
  have hWc : IsCompact W := Metric.isCompact_of_isClosed_isBounded hW_closed hW_bdd
  have hne : W.Nonempty := ⟨z₁, hz₁⟩
  have hd0 : 0 ≤ width W := width_nonneg hn hWc hne
  have hdpos : 0 < width W := by
    rcases hd0.lt_or_eq with h | h
    · exact h
    · rw [← h, div_zero] at hγ; linarith
  have hz : z₁ ≠ z₂ := by
    rintro rfl
    rw [sub_self, norm_zero, zero_div] at hγ; linarith
  have hγpos : 0 < γ := by linarith
  have hL : ‖z₁ - z₂‖ = γ * width W := by
    rw [hγ, div_mul_cancel₀ _ hdpos.ne']
  have key := width_dilation_ge hn hWc hne hz₁ hz₂ hz hβ_pos hβ_le (θ := 1 / γ) (by positivity)
    (by rw [hL]; field_simp; rfl)
  have heq : (1 - β ^ 2) * (1 / γ) ^ 2 / β ^ 2 = (1 - β ^ 2) / (β ^ 2 * γ ^ 2) := by
    field_simp
  rwa [heq] at key

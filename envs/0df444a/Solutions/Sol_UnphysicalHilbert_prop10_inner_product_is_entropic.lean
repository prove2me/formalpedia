-- Prove2me | solution 1 for UnphysicalHilbert.prop10_inner_product_is_entropic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:10:49.141951+00:00
-- url     : https://prove2.me/submissions/8d64c472-8eeb-40b6-8963-a36deab0713c

import Definitions.Def_UnphysicalHilbert_StateSpace

namespace UnphysicalHilbert

open scoped InnerProductSpace

namespace P10Aux

lemma g_eq (p : ℝ) :
    Real.negMulLog ((1 + p) / 2) + Real.negMulLog ((1 - p) / 2) = Real.binEntropy ((1 + p) / 2) := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  congr 2; ring

lemma injOn : Set.InjOn (fun p : ℝ => Real.negMulLog ((1 + p) / 2) + Real.negMulLog ((1 - p) / 2))
    (Set.Icc 0 1) := by
  intro x hx y hy hxy
  simp only [g_eq] at hxy
  have hx' : (1 + x) / 2 ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hy' : (1 + y) / 2 ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have := Real.binEntropy_strictAntiOn.injOn hx' hy' hxy
  linarith

lemma sum_eval {n : ℕ} (hn : n ≤ 2) (f : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h1 : ∑ i, f i = 1) (h2 : ∑ i, f i ^ 2 = (1 + c ^ 2) / 2) :
    ∑ i, Real.negMulLog (f i) =
      Real.negMulLog ((1 + c) / 2) + Real.negMulLog ((1 - c) / 2) := by
  interval_cases n
  · simp at h1
  · simp only [Fin.sum_univ_one] at h1 h2 ⊢
    rw [h1] at h2
    have hc1 : c = 1 := by nlinarith
    subst hc1
    rw [h1]; norm_num
  · simp only [Fin.sum_univ_two] at h1 h2 ⊢
    have hd : (f 0 - f 1) ^ 2 = c ^ 2 := by nlinarith
    have hd' : |f 0 - f 1| = c := by
      rw [← abs_of_nonneg hc]; exact sq_eq_sq_iff_abs_eq_abs _ _ |>.mp hd
    rcases abs_eq hc |>.mp hd' with h | h
    · have e0 : f 0 = (1 + c) / 2 := by linarith
      have e1 : f 1 = (1 - c) / 2 := by linarith
      rw [e0, e1]
    · have e0 : f 0 = (1 - c) / 2 := by linarith
      have e1 : f 1 = (1 + c) / 2 := by linarith
      rw [e0, e1, add_comm]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma finrank_le (ψ ϕ : H) : Module.finrank ℂ (pairSpan ψ ϕ) ≤ 2 := by
  classical
  have h := finrank_span_finset_le_card (R := ℂ) ({ψ, ϕ} : Finset H)
  have h2 : ({ψ, ϕ} : Finset H).card ≤ 2 := Finset.card_le_two
  unfold pairSpan
  simp only [Finset.coe_insert, Finset.coe_singleton] at h
  exact h.trans h2

lemma entropy_eq (ψ ϕ : H) (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) :
    equalMixtureEntropy ψ ϕ =
      Real.negMulLog ((1 + ‖⟪ψ, ϕ⟫_ℂ‖) / 2) + Real.negMulLog ((1 - ‖⟪ψ, ϕ⟫_ℂ‖) / 2) := by
  set W := pairSpan ψ ϕ
  set T : W →ₗ[ℂ] W := (equalMixture ψ ϕ).restrict (equalMixture_mapsTo ψ ϕ) with hTdef
  let ψ' : W := ⟨ψ, Submodule.subset_span (by simp)⟩
  let ϕ' : W := ⟨ϕ, Submodule.subset_span (by simp)⟩
  have hTw : ∀ w : W, T w = (1 / 2 : ℂ) • (⟪ψ', w⟫_ℂ • ψ' + ⟪ϕ', w⟫_ℂ • ϕ') := by
    intro w
    apply Subtype.ext
    simp [T, ψ', ϕ', equalMixture, ketBra, innerₛₗ_apply_apply, Submodule.coe_inner]
  have hT : T.IsSymmetric := by
    intro x y
    rw [hTw, hTw]
    simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
      inner_conj_symm]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hψ1 : ⟪ψ', ψ'⟫_ℂ = 1 := by
    rw [Submodule.coe_inner, inner_self_eq_norm_sq_to_K]; simp [ψ', hψ]
  have hϕ1 : ⟪ϕ', ϕ'⟫_ℂ = 1 := by
    rw [Submodule.coe_inner, inner_self_eq_norm_sq_to_K]; simp [ϕ', hϕ]
  have hψϕ : ⟪ψ', ϕ'⟫_ℂ = ⟪ψ, ϕ⟫_ℂ := rfl
  unfold equalMixtureEntropy vonNeumannEntropyFin
  rw [dif_pos hT]
  set d := Module.finrank ℂ W
  set b := hT.eigenvectorBasis (rfl : Module.finrank ℂ W = d)
  set ev := hT.eigenvalues (rfl : Module.finrank ℂ W = d)
  have hb : ∀ j, T (b j) = (ev j : ℂ) • b j := fun j => hT.apply_eigenvectorBasis _ j
  have hbn : ∀ j, ⟪b j, b j⟫_ℂ = 1 := fun j => by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 j]; simp
  have hev : ∀ j, (ev j : ℂ) = ⟪b j, T (b j)⟫_ℂ := fun j => by
    rw [hb, inner_smul_right, hbn, mul_one]
  have hev2 : ∀ j, ((ev j) ^ 2 : ℝ) = (⟪T (b j), T (b j)⟫_ℂ : ℂ) := fun j => by
    rw [hb, inner_smul_left, inner_smul_right, hbn]; simp [sq]
  have hs1 : ∑ j, ev j = 1 := by
    have : (∑ j, (ev j : ℂ)) = 1 := by
      simp_rw [hev, hTw, inner_smul_right, inner_add_right, inner_smul_right]
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      have e1 := b.sum_inner_mul_inner ψ' ψ'
      have e2 := b.sum_inner_mul_inner ϕ' ϕ'
      rw [hψ1] at e1; rw [hϕ1] at e2
      rw [e1, e2]; norm_num
    exact_mod_cast this
  have hs2 : ∑ j, ev j ^ 2 = (1 + ‖⟪ψ, ϕ⟫_ℂ‖ ^ 2) / 2 := by
    have : (∑ j, ((ev j ^ 2 : ℝ) : ℂ)) = ((1 + ‖⟪ψ, ϕ⟫_ℂ‖ ^ 2) / 2 : ℝ) := by
      simp_rw [hev2, hTw, inner_smul_right, inner_smul_left, inner_add_right, inner_add_left,
        inner_smul_right, inner_smul_left, inner_conj_symm]
      have e1 := b.sum_inner_mul_inner ψ' ψ'
      have e2 := b.sum_inner_mul_inner ϕ' ϕ'
      have e3 := b.sum_inner_mul_inner ψ' ϕ'
      have e4 := b.sum_inner_mul_inner ϕ' ψ'
      rw [Finset.sum_congr rfl (g := fun j => (1 / 4 : ℂ) * ((⟪ψ', b j⟫_ℂ * ⟪b j, ψ'⟫_ℂ) * ⟪ψ', ψ'⟫_ℂ +
            (⟪ϕ', b j⟫_ℂ * ⟪b j, ψ'⟫_ℂ) * ⟪ψ', ϕ'⟫_ℂ +
            (⟪ψ', b j⟫_ℂ * ⟪b j, ϕ'⟫_ℂ) * ⟪ϕ', ψ'⟫_ℂ + (⟪ϕ', b j⟫_ℂ * ⟪b j, ϕ'⟫_ℂ) * ⟪ϕ', ϕ'⟫_ℂ))
        (fun j _ => by simp only [map_div₀, map_one, map_ofNat]; ring)]
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
      have hϕψ : ⟪ϕ', ψ'⟫_ℂ = (starRingEnd ℂ) ⟪ψ, ϕ⟫_ℂ := (inner_conj_symm ϕ ψ).symm
      rw [e1, e2, e3, e4, hψ1, hϕ1, hψϕ, hϕψ]
      have hz := Complex.mul_conj' ⟪ψ, ϕ⟫_ℂ
      push_cast
      linear_combination (1 / 2 : ℂ) * hz
    exact_mod_cast this
  exact sum_eval (finrank_le ψ ϕ) ev _ (norm_nonneg _) hs1 hs2

end P10Aux


end UnphysicalHilbert

open scoped InnerProductSpace
open UnphysicalHilbert

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    (∀ ψ ϕ : H, ‖ψ‖ = 1 → ‖ϕ‖ = 1 →
      equalMixtureEntropy ψ ϕ =
        Real.negMulLog ((1 + ‖⟪ψ, ϕ⟫_ℂ‖) / 2) + Real.negMulLog ((1 - ‖⟪ψ, ϕ⟫_ℂ‖) / 2)) ∧
    Set.InjOn (fun p : ℝ => Real.negMulLog ((1 + p) / 2) + Real.negMulLog ((1 - p) / 2))
      (Set.Icc 0 1) :=
  ⟨fun ψ ϕ hψ hϕ => P10Aux.entropy_eq ψ ϕ hψ hϕ, P10Aux.injOn⟩


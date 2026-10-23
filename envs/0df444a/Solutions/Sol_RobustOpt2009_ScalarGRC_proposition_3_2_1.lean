-- Prove2me | solution 1 for RobustOpt2009.ScalarGRC.proposition_3_2_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:58:54.664353+00:00
-- url     : https://prove2.me/submissions/a969390d-5cd7-472a-b0c1-4233ba3dfe79

import Mathlib

open scoped BigOperators

lemma g78h_lin {n L : ℕ} (a0 : Fin n → ℝ) (a : Fin L → Fin n → ℝ) (x : Fin n → ℝ)
    (ζ : Fin L → ℝ) :
    (∑ j, (a0 j + ∑ l, ζ l * a l j) * x j) =
      (∑ j, a0 j * x j) + ζ ⬝ᵥ (fun l => ∑ j, a l j * x j) := by
  simp only [add_mul, Finset.sum_add_distrib, dotProduct, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma g78h_lin0 {n L : ℕ} (a : Fin L → Fin n → ℝ) (x : Fin n → ℝ)
    (ζ : Fin L → ℝ) :
    (∑ j, (∑ l, ζ l * a l j) * x j) = ζ ⬝ᵥ (fun l => ∑ j, a l j * x j) := by
  have := g78h_lin (fun _ => 0) a x ζ
  simpa using this

lemma g78h_sumb {L : ℕ} (b ζ : Fin L → ℝ) : (∑ l, ζ l * b l) = ζ ⬝ᵥ b := rfl

theorem solution {n L : ℕ}
    (a0 : Fin n → ℝ) (a : Fin L → Fin n → ℝ)
    (b0 : ℝ) (b : Fin L → ℝ)
    (Z K : Set (Fin L → ℝ)) (N : Seminorm ℝ (Fin L → ℝ))
    (hN : ∀ v, N v = 0 → v = 0)
    (hZne : Z.Nonempty) (hZclosed : IsClosed Z) (hZconvex : Convex ℝ Z)
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (hKzero : (0 : Fin L → ℝ) ∈ K)
    (hKscale : ∀ (t : ℝ), 0 ≤ t → ∀ v ∈ K, t • v ∈ K)
    (α : ℝ) (hα : 0 ≤ α) (x : Fin n → ℝ) :
    (∀ ζ : Fin L → ℝ,
      (∃ z ∈ Z, ∃ d ∈ K, ζ = z + d) →
      (∑ j, (a0 j + ∑ l, ζ l * a l j) * x j) ≤
        b0 + (∑ l, ζ l * b l) +
          α * sInf {r : ℝ | ∃ z ∈ Z, ζ - z ∈ K ∧ r = N (ζ - z)}) ↔
    ((∀ ζ ∈ Z,
      (∑ j, (a0 j + ∑ l, ζ l * a l j) * x j) ≤ b0 + ∑ l, ζ l * b l) ∧
     (∀ d ∈ K, N d ≤ 1 →
      (∑ j, (∑ l, d l * a l j) * x j) ≤ (∑ l, d l * b l) + α)) := by
  rw [show (∀ ζ : Fin L → ℝ, _ ) ↔ _ from Iff.rfl]
  simp only [g78h_lin a0 a x, g78h_lin0 a x]
  simp only [g78h_sumb]
  set w : Fin L → ℝ := fun l => a l ⬝ᵥ x with hw
  set A0 : ℝ := a0 ⬝ᵥ x with hA0
  have hbdd : ∀ ζ : Fin L → ℝ, BddBelow {r : ℝ | ∃ z ∈ Z, ζ - z ∈ K ∧ r = N (ζ - z)} := by
    intro ζ
    refine ⟨0, ?_⟩
    rintro r ⟨z, -, -, rfl⟩
    exact apply_nonneg N _
  constructor
  · intro h
    refine ⟨fun ζ hζ => ?_, fun d hd hNd => ?_⟩
    · have h1 := h ζ ⟨ζ, hζ, 0, hKzero, by simp⟩
      have h0 : sInf {r : ℝ | ∃ z ∈ Z, ζ - z ∈ K ∧ r = N (ζ - z)} ≤ 0 :=
        csInf_le (hbdd ζ) ⟨ζ, hζ, by simpa using hKzero, by simp⟩
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hα h0]
    · obtain ⟨z0, hz0⟩ := hZne
      set c : ℝ := A0 + z0 ⬝ᵥ w - b0 - z0 ⬝ᵥ b
      have key : ∀ t : ℝ, 0 ≤ t → c + t * (d ⬝ᵥ w - d ⬝ᵥ b) ≤ α * t := by
        intro t ht
        have h1 := h (z0 + t • d) ⟨z0, hz0, t • d, hKscale t ht d hd, rfl⟩
        have hle : sInf {r : ℝ | ∃ z ∈ Z, (z0 + t • d) - z ∈ K ∧ r = N ((z0 + t • d) - z)}
            ≤ t := by
          refine le_trans (csInf_le (hbdd _) ⟨z0, hz0, by simpa using hKscale t ht d hd, rfl⟩) ?_
          simp only [add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht]
          nlinarith [apply_nonneg N d]
        have h2 := mul_le_mul_of_nonneg_left hle hα
        simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at h1
        simp only [c]
        nlinarith
      by_contra hcon
      push_neg at hcon
      have hpos : 0 < d ⬝ᵥ w - d ⬝ᵥ b - α := by linarith
      have := key ((|c| + 1) / (d ⬝ᵥ w - d ⬝ᵥ b - α)) (by positivity)
      have e : (|c| + 1) / (d ⬝ᵥ w - d ⬝ᵥ b - α) * (d ⬝ᵥ w - d ⬝ᵥ b - α) = |c| + 1 :=
        div_mul_cancel₀ _ hpos.ne'
      nlinarith [neg_abs_le c]
  · rintro ⟨h1, h2⟩ ζ ⟨z, hz, d, hd, rfl⟩
    -- g(d') ≤ α N(d') for d' ∈ K
    have hg : ∀ d' ∈ K, d' ⬝ᵥ w - d' ⬝ᵥ b ≤ α * N d' := by
      intro d' hd'
      by_cases h0 : N d' = 0
      · have := hN d' h0
        subst this
        simp
      · have hpos : 0 < N d' := lt_of_le_of_ne (apply_nonneg N d') (Ne.symm h0)
        have hk := h2 ((N d')⁻¹ • d') (hKscale _ (by positivity) d' hd')
          (by
            rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
              inv_mul_cancel₀ h0])
        simp only [smul_dotProduct, smul_eq_mul] at hk
        have e : d' ⬝ᵥ w - d' ⬝ᵥ b = N d' * ((N d')⁻¹ * (d' ⬝ᵥ w) - (N d')⁻¹ * (d' ⬝ᵥ b)) := by
          field_simp
        rw [e, mul_comm α]
        exact mul_le_mul_of_nonneg_left (by linarith) hpos.le
    have hall : ∀ r ∈ {r : ℝ | ∃ z' ∈ Z, (z + d) - z' ∈ K ∧ r = N ((z + d) - z')},
        A0 + (z + d) ⬝ᵥ w - (b0 + (z + d) ⬝ᵥ b) ≤ α * r := by
      rintro r ⟨z', hz', hK', rfl⟩
      have e1 := h1 z' hz'
      have e2 := hg _ hK'
      have e3 : (z + d) ⬝ᵥ w = z' ⬝ᵥ w + ((z + d) - z') ⬝ᵥ w := by
        rw [sub_dotProduct]; ring
      have e4 : (z + d) ⬝ᵥ b = z' ⬝ᵥ b + ((z + d) - z') ⬝ᵥ b := by
        rw [sub_dotProduct]; ring
      linarith
    have hne : {r : ℝ | ∃ z' ∈ Z, (z + d) - z' ∈ K ∧ r = N ((z + d) - z')}.Nonempty :=
      ⟨_, z, hz, by simpa using hd, rfl⟩
    rcases eq_or_lt_of_le hα with h0 | hpos
    · subst h0
      obtain ⟨r, hr⟩ := hne
      have := hall r hr
      simp at this ⊢
      linarith
    · have : (A0 + (z + d) ⬝ᵥ w - (b0 + (z + d) ⬝ᵥ b)) / α ≤
          sInf {r : ℝ | ∃ z' ∈ Z, (z + d) - z' ∈ K ∧ r = N ((z + d) - z')} := by
        refine le_csInf hne (fun r hr => ?_)
        rw [div_le_iff₀ hpos]
        linarith [hall r hr]
      rw [div_le_iff₀ hpos] at this
      linarith

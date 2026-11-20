-- Prove2me | solution 1 for SharpJL.Dimension.corollary_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:38:35.074192+00:00
-- url     : https://prove2.me/submissions/825aa57b-1575-4298-a0b1-1c3b4ef7f3f6

import Mathlib
import Theorems.Thm_SharpJL_Dimension_theorem_1_2

section
namespace SharpJL.Dev

theorem psd_factor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (s : ℕ)
    (hs : A.rank ≤ s) : ∃ B : Matrix (Fin s) (Fin n) ℝ, A = B.transpose * B := by
  classical
  have hH := hA.isHermitian
  set ev := hH.eigenvalues with hev
  set U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  have hspec : A = U * Matrix.diagonal ev * U.transpose := by
    have := hH.spectral_theorem
    simpa [hU, hev, Matrix.star_eq_conjTranspose] using this
  have hcard : Fintype.card {i // ev i ≠ 0} ≤ s := by
    have := hH.rank_eq_card_non_zero_eigs
    rw [← this]; exact hs
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := {i // ev i ≠ 0}) (β := Fin s) (by simpa using hcard)
  have hnn : ∀ i, 0 ≤ ev i := hA.eigenvalues_nonneg
  refine ⟨Matrix.of fun j l => ∑ i : {i // ev i ≠ 0},
    if e i = j then Real.sqrt (ev i) * U l i else 0, ?_⟩
  ext l l'
  have hL : A l l' = ∑ i, ev i * U l i * U l' i := by
    rw [hspec]
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_mul, mul_comm, mul_left_comm]
  have h1 : ∀ j : Fin s, (∑ i : {i // ev i ≠ 0}, if e i = j then Real.sqrt (ev i) * U l i else 0)
      * (∑ i : {i // ev i ≠ 0}, if e i = j then Real.sqrt (ev i) * U l' i else 0)
      = ∑ i : {i // ev i ≠ 0}, if e i = j then ev i * U l i * U l' i else 0 := by
    intro j
    by_cases h : ∃ i0, e i0 = j
    · obtain ⟨i0, hi0⟩ := h
      have key : ∀ (f : {i // ev i ≠ 0} → ℝ), (∑ i, if e i = j then f i else 0) = f i0 := by
        intro f
        rw [Finset.sum_eq_single i0]
        · simp [hi0]
        · intro b _ hb
          have : e b ≠ j := fun h => hb (e.injective (h.trans hi0.symm))
          simp [this]
        · simp
      rw [key, key, key]
      have := hnn i0
      calc _ = (Real.sqrt (ev i0))^2 * U l i0 * U l' i0 := by ring
        _ = _ := by rw [Real.sq_sqrt this]
    · push Not at h
      simp [h]
  have hR : ((Matrix.of fun j l => ∑ i : {i // ev i ≠ 0},
      if e i = j then Real.sqrt (ev i) * U l i else 0 : Matrix (Fin s) (Fin n) ℝ).transpose *
      (Matrix.of fun j l => ∑ i : {i // ev i ≠ 0},
      if e i = j then Real.sqrt (ev i) * U l i else 0 : Matrix (Fin s) (Fin n) ℝ)) l l'
      = ∑ i : {i // ev i ≠ 0}, ev i * U l i * U l' i := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    simp only [h1]
    rw [Finset.sum_comm]
    simp
  rw [hL, hR]
  symm
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Subtype.val : {i // ev i ≠ 0} → Fin n)))]
  · rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
  · intro i _ hi
    have : ev i = 0 := by
      by_contra h; exact hi (Finset.mem_image.2 ⟨⟨i, h⟩, Finset.mem_univ _, rfl⟩)
    simp [this]

end SharpJL.Dev
end

section
namespace SharpJL.Dev.Cor21

open Matrix

theorem key {r N : ℕ} (B : Matrix (Fin r) (Fin N) ℝ) (v : EuclideanSpace ℝ (Fin N)) :
    ‖Matrix.toEuclideanLin B v‖ ^ 2 = ∑ i, ∑ j, v i * (B.transpose * B) i j * v j := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Real.norm_eq_abs,
    Matrix.mul_apply, Matrix.transpose_apply, sq, abs_mul_abs_self, Finset.sum_mul_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  have : ∀ i, ∑ j, ∑ k, v.ofLp i * (B k i * B k j) * v.ofLp j
      = ∑ k, ∑ j, v.ofLp i * (B k i * B k j) * v.ofLp j := fun i => Finset.sum_comm
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- log(2 + m/r²) ≤ 2 log(2 + n/r) when m ≤ n². -/
theorem log_le {n m r : ℕ} (hr : 1 ≤ r) (hm : m ≤ n * n) :
    Real.log (2 + (m : ℝ) / (r : ℝ) ^ 2) ≤ 2 * Real.log (2 + (n : ℝ) / (r : ℝ)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hm' : (m : ℝ) ≤ n * n := by exact_mod_cast hm
  have h1 : (m : ℝ) / (r : ℝ) ^ 2 ≤ ((n : ℝ) / r) ^ 2 := by
    rw [div_pow, sq (n : ℝ)]
    exact div_le_div_of_nonneg_right hm' (by positivity)
  have ht : (0 : ℝ) ≤ (n : ℝ) / r := by positivity
  have h2 : 2 + (m : ℝ) / (r : ℝ) ^ 2 ≤ (2 + (n : ℝ) / r) ^ 2 := by nlinarith
  calc Real.log (2 + (m : ℝ) / (r : ℝ) ^ 2) ≤ Real.log ((2 + (n : ℝ) / r) ^ 2) :=
        Real.log_le_log (by positivity) h2
    _ = 2 * Real.log (2 + (n : ℝ) / r) := by
        rw [Real.log_pow]; norm_num

theorem core (C : ℝ) (hC : 0 < C)
    (h12 : ∀ (r m : ℕ), 1 ≤ r → 1 ≤ m →
      ∀ (u : Fin m → EuclideanSpace ℝ (Fin (2 * r))),
        (∀ ℓ, ‖u ℓ‖ = 1) →
        ∃ M : Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ,
          M.PosSemidef ∧ M.rank ≤ r ∧
          ∀ ℓ : Fin m,
            |(∑ i : Fin (2 * r), ∑ j : Fin (2 * r), u ℓ i * M i j * u ℓ j) - 1| ≤
              C * Real.sqrt (Real.log (2 + (m : ℝ) / (r : ℝ) ^ 2) / (r : ℝ)))
    (n r : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ r)
    (X : Finset (EuclideanSpace ℝ (Fin (2 * r)))) (hX2 : 2 ≤ X.card) (hXn : X.card ≤ n) :
    ∃ L : EuclideanSpace ℝ (Fin (2 * r)) →ₗ[ℝ] EuclideanSpace ℝ (Fin r),
      ∀ x ∈ X, ∀ y ∈ X,
        (1 - C * Real.sqrt 2 * Real.sqrt (Real.log (2 + (n : ℝ) / (r : ℝ)) / (r : ℝ)))
            * ‖x - y‖ ^ 2 ≤ ‖L x - L y‖ ^ 2 ∧
        ‖L x - L y‖ ^ 2 ≤
          (1 + C * Real.sqrt 2 * Real.sqrt (Real.log (2 + (n : ℝ) / (r : ℝ)) / (r : ℝ)))
            * ‖x - y‖ ^ 2 := by
  classical
  set P : Finset (EuclideanSpace ℝ (Fin (2 * r)) × EuclideanSpace ℝ (Fin (2 * r))) :=
    (X ×ˢ X).filter (fun p => p.1 ≠ p.2) with hP
  have hmem : ∀ p, p ∈ P ↔ p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 ≠ p.2 := by
    intro p; simp [hP, and_assoc]
  have hm1 : 1 ≤ P.card := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hX2
    exact Finset.card_pos.mpr ⟨(a, b), (hmem _).mpr ⟨ha, hb, hab⟩⟩
  have hmn : P.card ≤ n * n := by
    calc P.card ≤ (X ×ˢ X).card := Finset.card_filter_le _ _
      _ = X.card * X.card := Finset.card_product _ _
      _ ≤ n * n := Nat.mul_le_mul hXn hXn
  let e := P.equivFin
  let d : Fin P.card → EuclideanSpace ℝ (Fin (2 * r)) := fun ℓ => (e.symm ℓ).1.1 - (e.symm ℓ).1.2
  have hd : ∀ ℓ, d ℓ ≠ 0 := by
    intro ℓ
    have := ((hmem _).mp (e.symm ℓ).2).2.2
    exact sub_ne_zero.mpr this
  have hdn : ∀ ℓ, 0 < ‖d ℓ‖ := fun ℓ => norm_pos_iff.mpr (hd ℓ)
  obtain ⟨M, hM, hrk, hbd⟩ := h12 r P.card hr hm1 (fun ℓ => (‖d ℓ‖⁻¹) • d ℓ) (by
    intro ℓ
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hdn ℓ).ne'])
  obtain ⟨B, hB⟩ := SharpJL.Dev.psd_factor M hM r hrk
  refine ⟨Matrix.toEuclideanLin B, ?_⟩
  have hδ : C * Real.sqrt (Real.log (2 + (P.card : ℝ) / (r : ℝ) ^ 2) / (r : ℝ))
      ≤ C * Real.sqrt 2 * Real.sqrt (Real.log (2 + (n : ℝ) / (r : ℝ)) / (r : ℝ)) := by
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have := log_le hr hmn
    have h3 : Real.sqrt (Real.log (2 + (P.card : ℝ) / (r : ℝ) ^ 2) / (r : ℝ))
        ≤ Real.sqrt 2 * Real.sqrt (Real.log (2 + (n : ℝ) / (r : ℝ)) / (r : ℝ)) := by
      rw [← Real.sqrt_mul (by norm_num)]
      apply Real.sqrt_le_sqrt
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right this hr'.le
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h3 hC.le
  intro x hx y hy
  by_cases hxy : x = y
  · subst hxy; simp
  have hp : (x, y) ∈ P := (hmem _).mpr ⟨hx, hy, hxy⟩
  set L := Matrix.toEuclideanLin B
  have hℓ : e.symm (e ⟨(x, y), hp⟩) = ⟨(x, y), hp⟩ := e.symm_apply_apply _
  have hb := hbd (e ⟨(x, y), hp⟩)
  have hdl : d (e ⟨(x, y), hp⟩) = x - y := by simp [d, hℓ]
  have hsum : (∑ i : Fin (2 * r), ∑ j : Fin (2 * r),
      ((‖d (e ⟨(x, y), hp⟩)‖⁻¹) • d (e ⟨(x, y), hp⟩)) i * M i j *
        ((‖d (e ⟨(x, y), hp⟩)‖⁻¹) • d (e ⟨(x, y), hp⟩)) j)
      = (‖x - y‖⁻¹) ^ 2 * ‖L x - L y‖ ^ 2 := by
    rw [hdl, hB]
    have := key B ((‖x - y‖⁻¹) • (x - y))
    simp only [PiLp.smul_apply, smul_eq_mul] at this ⊢
    rw [← this, ← map_sub, map_smul, norm_smul, norm_inv, norm_norm, mul_pow, map_sub]
  rw [hsum] at hb
  have hxn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hb2 := le_trans hb (hδ)
  set δ := C * Real.sqrt 2 * Real.sqrt (Real.log (2 + (n : ℝ) / (r : ℝ)) / (r : ℝ))
  have hq : ‖L x - L y‖ ^ 2 = ‖x - y‖ ^ 2 * ((‖x - y‖⁻¹) ^ 2 * ‖L x - L y‖ ^ 2) := by
    field_simp
  rw [abs_le] at hb2
  obtain ⟨h1, h2⟩ := hb2
  have hsq : 0 < ‖x - y‖ ^ 2 := by positivity
  constructor
  · rw [hq]; nlinarith
  · rw [hq]; nlinarith

end SharpJL.Dev.Cor21

namespace SharpJL.Dimension

theorem chk_corollary_2_1 :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (n r : ℕ), 2 ≤ n → 1 ≤ r →
      ∀ (X : Finset (EuclideanSpace ℝ (Fin (2 * r)))),
        2 ≤ X.card → X.card ≤ n →
        ∃ L : EuclideanSpace ℝ (Fin (2 * r)) →ₗ[ℝ] EuclideanSpace ℝ (Fin r),
          let δ := C₀ * Real.sqrt (Real.log (2 + (n : ℝ) / (r : ℝ)) / (r : ℝ))
          ∀ x ∈ X, ∀ y ∈ X,
            (1 - δ) * ‖x - y‖ ^ 2 ≤ ‖L x - L y‖ ^ 2 ∧
              ‖L x - L y‖ ^ 2 ≤ (1 + δ) * ‖x - y‖ ^ 2 := by
  obtain ⟨C, hC, h12⟩ := SharpJL.Dimension.theorem_1_2
  refine ⟨C * Real.sqrt 2, by positivity, ?_⟩
  intro n r hn hr X hX2 hXn
  obtain ⟨L, hL⟩ := SharpJL.Dev.Cor21.core C hC h12 n r hn hr X hX2 hXn
  exact ⟨L, hL⟩

end SharpJL.Dimension
end

theorem solution : type_of% @SharpJL.Dimension.chk_corollary_2_1 := @SharpJL.Dimension.chk_corollary_2_1

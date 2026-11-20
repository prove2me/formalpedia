-- Prove2me | solution 1 for SharpJL.Dimension.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:38:34.668238+00:00
-- url     : https://prove2.me/submissions/5ee580ac-3ee3-4ae1-ba09-d234661b1b9b

import Mathlib
import Definitions.Def_SpencerEight_IsSymmContraction
import Theorems.Thm_SharpJL_Dimension_proposition_3_1

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
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SharpJL.Dev.Rank12

theorem quad_abs_le {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : ‖Q‖ ≤ 1) (y : Fin k → ℝ) :
    |y ⬝ᵥ (Q *ᵥ y)| ≤ y ⬝ᵥ y := by
  let Y : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 y
  have h1 := Matrix.l2_opNorm_mulVec Q Y
  have h2 : ‖(EuclideanSpace.equiv (Fin k) ℝ).symm (Q.mulVec Y.ofLp)‖ ≤ ‖Y‖ :=
    h1.trans (by nlinarith [norm_nonneg Y])
  have h3 := abs_real_inner_le_norm Y ((EuclideanSpace.equiv (Fin k) ℝ).symm (Q.mulVec Y.ofLp))
  have h4 : ‖Y‖ * ‖Y‖ = y ⬝ᵥ y := by
    rw [← real_inner_self_eq_norm_mul_norm, EuclideanSpace.inner_eq_star_dotProduct]
    simp [Y]
  have h5 : inner ℝ Y ((EuclideanSpace.equiv (Fin k) ℝ).symm (Q.mulVec Y.ofLp)) = y ⬝ᵥ (Q *ᵥ y) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [Y, dotProduct_comm]
  rw [h5] at h3
  rw [← h4]
  calc _ ≤ ‖Y‖ * ‖(EuclideanSpace.equiv (Fin k) ℝ).symm (Q.mulVec Y.ofLp)‖ := h3
    _ ≤ _ := by nlinarith [norm_nonneg Y]

theorem psd_of_contraction {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℝ) (hs : Q.IsSymm) (hn : ‖Q‖ ≤ 1)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (1 + σ • Q).PosSemidef ∧
      ∀ y, y ⬝ᵥ ((1 + σ • Q) *ᵥ y) = y ⬝ᵥ y + σ * (y ⬝ᵥ (Q *ᵥ y)) := by
  have hform : ∀ y, y ⬝ᵥ ((1 + σ • Q) *ᵥ y) = y ⬝ᵥ y + σ * (y ⬝ᵥ (Q *ᵥ y)) := by
    intro y
    simp [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul]
  refine ⟨?_, hform⟩
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp [show Qᵀ = Q from hs]
  · intro y
    simp only [star_trivial, hform]
    have := quad_abs_le Q hn y
    rcases hσ with rfl | rfl <;> [skip; skip] <;> nlinarith [abs_le.1 this]


def P31 (C₁ : ℝ) : Prop :=
  ∀ (k m : ℕ), 1 ≤ k → 1 ≤ m →
      ∀ (w : Fin m → EuclideanSpace ℝ (Fin k)),
        (∀ ℓ, ‖w ℓ‖ = 1) →
        ∃ Q : Matrix (Fin k) (Fin k) ℝ,
          SpencerEight.IsSymmContraction Q ∧
          ⌈(k : ℝ) / 4⌉₊ ≤
            Module.finrank ℝ (LinearMap.ker (1 - Q).mulVecLin) +
            Module.finrank ℝ (LinearMap.ker (1 + Q).mulVecLin) ∧
          ∀ ℓ : Fin m,
            |∑ i : Fin k, ∑ j : Fin k, w ℓ i * Q i j * w ℓ j| ≤
              C₁ * Real.sqrt (Real.log (3 + (m : ℝ) / (k : ℝ) ^ 2) / (k : ℝ))

theorem norm_mul_self_eq {k : ℕ} (y : EuclideanSpace ℝ (Fin k)) :
    ‖y‖ * ‖y‖ = y.ofLp ⬝ᵥ y.ofLp := by
  rw [← real_inner_self_eq_norm_mul_norm, EuclideanSpace.inner_eq_star_dotProduct]
  simp

theorem dot_self_nonneg' {k : ℕ} (x : Fin k → ℝ) : 0 ≤ x ⬝ᵥ x := by
  simp only [dotProduct]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

theorem exists_unit {k : ℕ} (hk : 1 ≤ k) (x : Fin k → ℝ) :
    ∃ w : EuclideanSpace ℝ (Fin k), ‖w‖ = 1 ∧ ∀ i, x i = Real.sqrt (x ⬝ᵥ x) * w.ofLp i := by
  by_cases h : x ⬝ᵥ x = 0
  · have hx : x = 0 := dotProduct_self_eq_zero.1 h
    refine ⟨EuclideanSpace.single ⟨0, hk⟩ 1, by simp, ?_⟩
    intro i; simp [hx]
  · have hpos : 0 < x ⬝ᵥ x := lt_of_le_of_ne (dot_self_nonneg' x) (Ne.symm h)
    set c := Real.sqrt (x ⬝ᵥ x) with hc
    have hc0 : 0 < c := Real.sqrt_pos.2 hpos
    have hcc : c * c = x ⬝ᵥ x := Real.mul_self_sqrt hpos.le
    refine ⟨WithLp.toLp 2 (c⁻¹ • x), ?_, ?_⟩
    · have := norm_mul_self_eq (WithLp.toLp 2 (c⁻¹ • x))
      have h2 : (WithLp.toLp 2 (c⁻¹ • x) : EuclideanSpace ℝ (Fin k)).ofLp ⬝ᵥ
          (WithLp.toLp 2 (c⁻¹ • x) : EuclideanSpace ℝ (Fin k)).ofLp = 1 := by
        simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
        rw [← hcc]; field_simp
      rw [h2] at this
      have hn := norm_nonneg (WithLp.toLp 2 (c⁻¹ • x) : EuclideanSpace ℝ (Fin k))
      nlinarith
    · intro i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp

theorem step {C₁ : ℝ} (h : P31 C₁) {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (x : Fin m → Fin k → ℝ) (β : ℝ)
    (hβ : C₁ * Real.sqrt (Real.log (3 + (m : ℝ) / (k : ℝ) ^ 2) / (k : ℝ)) ≤ β) :
    ∃ (k' : ℕ) (S : Matrix (Fin k') (Fin k) ℝ), 8 * k' ≤ 7 * k ∧
      ∀ ℓ, |(S *ᵥ x ℓ) ⬝ᵥ (S *ᵥ x ℓ) - x ℓ ⬝ᵥ x ℓ| ≤ β * (x ℓ ⬝ᵥ x ℓ) := by
  choose w hw1 hw using fun ℓ => exists_unit hk (x ℓ)
  obtain ⟨Q, ⟨hs, hn⟩, hker, hq⟩ := h k m hk hm w hw1
  have hq' : ∀ ℓ, |(w ℓ).ofLp ⬝ᵥ Q *ᵥ (w ℓ).ofLp| ≤ β := by
    intro ℓ
    refine le_trans (le_of_eq ?_) ((hq ℓ).trans hβ)
    congr 1
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have key : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      k ≤ 8 * Module.finrank ℝ (LinearMap.ker (1 + σ • Q).mulVecLin) := by
    have hk4 : k ≤ 4 * (Module.finrank ℝ (LinearMap.ker (1 - Q).mulVecLin) +
        Module.finrank ℝ (LinearMap.ker (1 + Q).mulVecLin)) := by
      have h1 : (k : ℝ) / 4 ≤ (⌈(k : ℝ) / 4⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈(k : ℝ) / 4⌉₊ : ℝ) ≤ ((Module.finrank ℝ (LinearMap.ker (1 - Q).mulVecLin) +
        Module.finrank ℝ (LinearMap.ker (1 + Q).mulVecLin) : ℕ) : ℝ) := by exact_mod_cast hker
      have : (k : ℝ) ≤ 4 * ((Module.finrank ℝ (LinearMap.ker (1 - Q).mulVecLin) +
        Module.finrank ℝ (LinearMap.ker (1 + Q).mulVecLin) : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    by_cases hc : Module.finrank ℝ (LinearMap.ker (1 - Q).mulVecLin) ≤
        Module.finrank ℝ (LinearMap.ker (1 + Q).mulVecLin)
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [one_smul]; omega
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have : (1 : Matrix (Fin k) (Fin k) ℝ) + (-1 : ℝ) • Q = 1 - Q := by
        rw [neg_smul, one_smul, sub_eq_add_neg]
      rw [this]; omega
  obtain ⟨σ, hσ, hd⟩ := key
  obtain ⟨hpsd, hform⟩ := psd_of_contraction Q hs hn σ hσ
  set A : Matrix (Fin k) (Fin k) ℝ := 1 + σ • Q with hA
  set d := Module.finrank ℝ (LinearMap.ker A.mulVecLin) with hd'
  have hrk : A.rank + d = k := by
    have := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    simpa [Matrix.rank] using this
  obtain ⟨S, hS⟩ := SharpJL.Dev.psd_factor A hpsd (k - d) (by omega)
  refine ⟨k - d, S, by omega, ?_⟩
  intro ℓ
  have hSx : (S *ᵥ x ℓ) ⬝ᵥ (S *ᵥ x ℓ) = x ℓ ⬝ᵥ (A *ᵥ x ℓ) := by
    rw [hS, ← Matrix.mulVec_mulVec]
    have e : S *ᵥ x ℓ = x ℓ ᵥ* Sᵀ := (Matrix.vecMul_transpose S _).symm
    nth_rewrite 1 [e]
    rw [← Matrix.dotProduct_mulVec]
  have hxw : x ℓ = Real.sqrt (x ℓ ⬝ᵥ x ℓ) • (w ℓ).ofLp := funext (fun i => hw ℓ i)
  have hww : (w ℓ).ofLp ⬝ᵥ (w ℓ).ofLp = 1 := by
    rw [← norm_mul_self_eq, hw1 ℓ]; norm_num
  have hcc : Real.sqrt (x ℓ ⬝ᵥ x ℓ) * Real.sqrt (x ℓ ⬝ᵥ x ℓ) = x ℓ ⬝ᵥ x ℓ :=
    Real.mul_self_sqrt (dot_self_nonneg' _)
  set c := Real.sqrt (x ℓ ⬝ᵥ x ℓ)
  have hxAx : x ℓ ⬝ᵥ (A *ᵥ x ℓ) = (x ℓ ⬝ᵥ x ℓ) * (1 + σ * ((w ℓ).ofLp ⬝ᵥ Q *ᵥ (w ℓ).ofLp)) := by
    have e1 : x ℓ ⬝ᵥ (A *ᵥ x ℓ) = c * c * ((w ℓ).ofLp ⬝ᵥ (A *ᵥ (w ℓ).ofLp)) := by
      conv_lhs => rw [hxw]
      simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    rw [e1, hcc, hform, hww]
  rw [hSx, hxAx]
  have : (x ℓ ⬝ᵥ x ℓ) * (1 + σ * ((w ℓ).ofLp ⬝ᵥ Q *ᵥ (w ℓ).ofLp)) - x ℓ ⬝ᵥ x ℓ =
      (x ℓ ⬝ᵥ x ℓ) * (σ * ((w ℓ).ofLp ⬝ᵥ Q *ᵥ (w ℓ).ofLp)) := by ring
  rw [this, abs_mul, abs_of_nonneg (dot_self_nonneg' _), abs_mul]
  have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  rw [hσ1, one_mul, mul_comm β]
  exact mul_le_mul_of_nonneg_left (hq' ℓ) (dot_self_nonneg' _)


theorem gram_eq {a c : ℕ} (S : Matrix (Fin a) (Fin c) ℝ) (y : Fin c → ℝ) :
    (S *ᵥ y) ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ ((Sᵀ * S) *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec]
  have e : S *ᵥ y = y ᵥ* Sᵀ := (Matrix.vecMul_transpose S _).symm
  nth_rewrite 1 [e]
  rw [← Matrix.dotProduct_mulVec]

theorem sqrt_mono {C₁ : ℝ} (hC : 0 ≤ C₁) {r k m : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    C₁ * Real.sqrt (Real.log (3 + (m : ℝ) / (k : ℝ) ^ 2) / (k : ℝ)) ≤
      C₁ * Real.sqrt (Real.log (3 + (m : ℝ) / (r : ℝ) ^ 2) / (r : ℝ)) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrk' : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have hk0 : (0 : ℝ) < k := by linarith
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.sqrt_le_sqrt
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h1 : (m : ℝ) / (k : ℝ) ^ 2 ≤ (m : ℝ) / (r : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_left hm0 (by positivity)
    nlinarith
  have hlog : Real.log (3 + (m : ℝ) / (k : ℝ) ^ 2) ≤ Real.log (3 + (m : ℝ) / (r : ℝ) ^ 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (3 + (m : ℝ) / (r : ℝ) ^ 2) :=
    Real.log_nonneg (by have : (0:ℝ) ≤ (m : ℝ) / (r : ℝ) ^ 2 := by positivity
                        linarith)
  calc Real.log (3 + (m : ℝ) / (k : ℝ) ^ 2) / k ≤ Real.log (3 + (m : ℝ) / (r : ℝ) ^ 2) / k :=
        div_le_div_of_nonneg_right hlog hk0.le
    _ ≤ _ := div_le_div_of_nonneg_left hlog0 (by linarith) hrk'

theorem iter {C₁ : ℝ} (h : P31 C₁) (hC : 0 ≤ C₁) {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (u : Fin m → Fin (2 * r) → ℝ) (hu : ∀ ℓ, u ℓ ⬝ᵥ u ℓ = 1) (b : ℝ)
    (hb : C₁ * Real.sqrt (Real.log (3 + (m : ℝ) / (r : ℝ) ^ 2) / (r : ℝ)) ≤ b) (hb1 : b ≤ 1) :
    ∀ t : ℕ, ∃ s ≤ t, ∃ (k : ℕ) (B : Matrix (Fin k) (Fin (2 * r)) ℝ),
      (∀ ℓ, (1 - b) ^ s ≤ (B *ᵥ u ℓ) ⬝ᵥ (B *ᵥ u ℓ) ∧
            (B *ᵥ u ℓ) ⬝ᵥ (B *ᵥ u ℓ) ≤ (1 + b) ^ s) ∧
      (k ≤ r ∨ (s = t ∧ 8 ^ t * k ≤ 7 ^ t * (2 * r))) := by
  have hb0 : 0 ≤ b := by
    refine le_trans (mul_nonneg hC (Real.sqrt_nonneg _)) hb
  intro t
  induction t with
  | zero =>
    refine ⟨0, le_refl _, 2 * r, 1, ?_, Or.inr ⟨rfl, by simp⟩⟩
    intro ℓ
    simp [hu ℓ]
  | succ t ih =>
    obtain ⟨s, hst, k, B, hB, hk⟩ := ih
    by_cases hkr : k ≤ r
    · exact ⟨s, by omega, k, B, hB, Or.inl hkr⟩
    · have hkr' : r < k := by omega
      have hs : s = t ∧ 8 ^ t * k ≤ 7 ^ t * (2 * r) := by
        rcases hk with h' | h'
        · omega
        · exact h'
      obtain ⟨rfl, hsz⟩ := hs
      obtain ⟨k', S, hk', hS⟩ := step h (by omega) hm (fun ℓ => B *ᵥ u ℓ) b
        ((sqrt_mono hC hr hkr'.le).trans hb)
      refine ⟨s + 1, le_refl _, k', S * B, ?_, Or.inr ⟨rfl, ?_⟩⟩
      · intro ℓ
        rw [← Matrix.mulVec_mulVec]
        have h1 := abs_le.1 (hS ℓ)
        obtain ⟨hl, hu'⟩ := hB ℓ
        set q := (B *ᵥ u ℓ) ⬝ᵥ (B *ᵥ u ℓ)
        constructor
        · have : (1 - b) ^ s * (1 - b) ≤ q * (1 - b) :=
            mul_le_mul_of_nonneg_right hl (by linarith)
          rw [pow_succ]; nlinarith [h1.1]
        · have : q * (1 + b) ≤ (1 + b) ^ s * (1 + b) :=
            mul_le_mul_of_nonneg_right hu' (by linarith)
          rw [pow_succ]; nlinarith [h1.2]
      · calc 8 ^ (s + 1) * k' = 8 ^ s * (8 * k') := by ring
          _ ≤ 8 ^ s * (7 * k) := Nat.mul_le_mul_left _ hk'
          _ = 7 * (8 ^ s * k) := by ring
          _ ≤ 7 * (7 ^ s * (2 * r)) := Nat.mul_le_mul_left _ hsz
          _ = 7 ^ (s + 1) * (2 * r) := by ring

theorem log_cmp {x : ℝ} (hx : 0 ≤ x) : Real.log (3 + x) ≤ 2 * Real.log (2 + x) := by
  have := Real.log_pow (2 + x) 2
  push_cast at this
  rw [← this]
  exact Real.log_le_log (by linarith) (by nlinarith)

theorem b_le {C₁ : ℝ} (hC : 0 ≤ C₁) {r m : ℕ} (hr : 1 ≤ r) :
    C₁ * Real.sqrt (Real.log (3 + (m : ℝ) / (r : ℝ) ^ 2) / (r : ℝ)) ≤
      2 * (C₁ * Real.sqrt (Real.log (2 + (m : ℝ) / (r : ℝ) ^ 2) / (r : ℝ))) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hx : (0 : ℝ) ≤ (m : ℝ) / (r : ℝ) ^ 2 := by positivity
  have h1 := log_cmp hx
  have hL : 0 ≤ Real.log (2 + (m : ℝ) / (r : ℝ) ^ 2) := Real.log_nonneg (by linarith)
  have h2 : Real.sqrt (Real.log (3 + (m : ℝ) / (r : ℝ) ^ 2) / (r : ℝ)) ≤
      2 * Real.sqrt (Real.log (2 + (m : ℝ) / (r : ℝ) ^ 2) / (r : ℝ)) := by
    have e : 2 * Real.sqrt (Real.log (2 + (m : ℝ) / (r : ℝ) ^ 2) / (r : ℝ)) =
        Real.sqrt (4 * (Real.log (2 + (m : ℝ) / (r : ℝ) ^ 2) / (r : ℝ))) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [e]
    apply Real.sqrt_le_sqrt
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hr'.le
    linarith
  nlinarith


theorem quad_eq {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ) :
    (∑ i : Fin k, ∑ j : Fin k, v i * M i j * v j) = v ⬝ᵥ (M *ᵥ v) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

end SharpJL.Dev.Rank12

namespace SharpJL.Dimension

theorem chk_theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r m : ℕ), 1 ≤ r → 1 ≤ m →
      ∀ (u : Fin m → EuclideanSpace ℝ (Fin (2 * r))),
        (∀ ℓ, ‖u ℓ‖ = 1) →
        ∃ M : Matrix (Fin (2 * r)) (Fin (2 * r)) ℝ,
          M.PosSemidef ∧ M.rank ≤ r ∧
          ∀ ℓ : Fin m,
            |(∑ i : Fin (2 * r), ∑ j : Fin (2 * r), u ℓ i * M i j * u ℓ j) - 1| ≤
              C * Real.sqrt (Real.log (2 + (m : ℝ) / (r : ℝ) ^ 2) / (r : ℝ)) := by
  obtain ⟨C₁, hC₁, h⟩ := SharpJL.Dimension.proposition_3_1
  have h' : SharpJL.Dev.Rank12.P31 C₁ := h
  refine ⟨40 * C₁, by positivity, ?_⟩
  intro r m hr hm u hu
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set b := C₁ * Real.sqrt (Real.log (3 + (m : ℝ) / (r : ℝ) ^ 2) / (r : ℝ)) with hb
  have hbb := SharpJL.Dev.Rank12.b_le hC₁.le (r := r) (m := m) hr
  rw [← hb] at hbb
  set T := Real.sqrt (Real.log (2 + (m : ℝ) / (r : ℝ) ^ 2) / (r : ℝ)) with hT
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := mul_nonneg hC₁.le (Real.sqrt_nonneg _)
  by_cases hbig : 1 / 20 < b
  · refine ⟨0, Matrix.PosSemidef.zero, by simp, ?_⟩
    intro ℓ
    have : (∑ i : Fin (2 * r), ∑ j : Fin (2 * r), u ℓ i * (0 : Matrix _ _ ℝ) i j * u ℓ j) = 0 := by
      simp
    rw [this]
    have : C₁ * T ≥ 0 := by positivity
    rw [show (0 : ℝ) - 1 = -1 by norm_num, abs_neg, abs_one]
    nlinarith
  · push Not at hbig
    have hu' : ∀ ℓ, (u ℓ).ofLp ⬝ᵥ (u ℓ).ofLp = 1 := by
      intro ℓ
      rw [← SharpJL.Dev.Rank12.norm_mul_self_eq, hu ℓ]; norm_num
    obtain ⟨s, hs6, k, B, hB, hk⟩ := SharpJL.Dev.Rank12.iter h' hC₁.le hr hm
      (fun ℓ => (u ℓ).ofLp) hu' b le_rfl (by linarith) 6
    have hkr : k ≤ r := by
      rcases hk with h1 | ⟨_, h1⟩
      · exact h1
      · norm_num at h1; omega
    refine ⟨Bᵀ * B, ?_, ?_, ?_⟩
    · have := Matrix.posSemidef_conjTranspose_mul_self B
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    · calc (Bᵀ * B).rank ≤ Bᵀ.rank := Matrix.rank_mul_le_left _ _
        _ = B.rank := Matrix.rank_transpose B
        _ ≤ k := Matrix.rank_le_height B
        _ ≤ r := hkr
    · intro ℓ
      rw [SharpJL.Dev.Rank12.quad_eq, ← SharpJL.Dev.Rank12.gram_eq]
      obtain ⟨hl, hu2⟩ := hB ℓ
      set q := (B *ᵥ (u ℓ).ofLp) ⬝ᵥ (B *ᵥ (u ℓ).ofLp)
      have hlow : 1 - (s : ℝ) * b ≤ (1 - b) ^ s := by
        have := one_add_mul_le_pow (a := -b) (by linarith) s
        rw [← sub_eq_add_neg] at this
        linarith
      have hsb : (s : ℝ) * b ≤ 6 * b := by
        have : (s : ℝ) ≤ 6 := by exact_mod_cast hs6
        nlinarith
      have hup : (1 + b) ^ s ≤ (1 + b) ^ 6 :=
        pow_le_pow_right₀ (by linarith) hs6
      have h6 : (1 + b) ^ 6 - 1 ≤ 8 * b := by
        have e : (1 + b) ^ 6 - 1 = b * (6 + 15 * b + 20 * b ^ 2 + 15 * b ^ 3 + 6 * b ^ 4 + b ^ 5) := by
          ring
        rw [e]
        have h2 : b ^ 2 ≤ b / 20 := by nlinarith
        have h3 : b ^ 3 ≤ b / 400 := by nlinarith
        have h4 : b ^ 4 ≤ b / 8000 := by nlinarith
        have h5 : b ^ 5 ≤ b / 160000 := by nlinarith
        nlinarith
      rw [abs_le]
      have hTT : 0 ≤ C₁ * T := by positivity
      constructor <;> nlinarith

end SharpJL.Dimension
end

theorem solution : type_of% @SharpJL.Dimension.chk_theorem_1_2 := @SharpJL.Dimension.chk_theorem_1_2

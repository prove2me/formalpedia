-- Prove2me | solution 1 for WorstCaseVaR.KnownMoments.phi_closed_form_and_maximum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T16:15:24.164989+00:00
-- url     : https://prove2.me/submissions/95d9bfdd-000c-4d88-8825-ee214267a373

import Mathlib
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic

set_option autoImplicit false

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace P7398ea44

lemma quad_vmv {n : ℕ} (u z : Fin n → ℝ) :
    z ⬝ᵥ (vecMulVec u u *ᵥ z) = (z ⬝ᵥ u) ^ 2 := by
  simp only [dotProduct, mulVec, vecMulVec, of_apply, sq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma herm_sym {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.IsHermitian)
    (z w : Fin n → ℝ) : w ⬝ᵥ (Γ *ᵥ z) = z ⬝ᵥ (Γ *ᵥ w) := by
  have hT : Γᵀ = Γ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hΓ.eq
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hT]

lemma cs {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosSemidef) (z w : Fin n → ℝ)
    (hQ : 0 < w ⬝ᵥ (Γ *ᵥ w)) :
    (z ⬝ᵥ (Γ *ᵥ w)) ^ 2 ≤ (z ⬝ᵥ (Γ *ᵥ z)) * (w ⬝ᵥ (Γ *ᵥ w)) := by
  have hs := herm_sym Γ hΓ.1 z w
  set a := z ⬝ᵥ (Γ *ᵥ z)
  set b := z ⬝ᵥ (Γ *ᵥ w)
  set Q := w ⬝ᵥ (Γ *ᵥ w)
  have key : ∀ t : ℝ, 0 ≤ a - 2 * t * b + t ^ 2 * Q := by
    intro t
    have h := hΓ.dotProduct_mulVec_nonneg (z - t • w)
    simp only [star_trivial, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
    rw [hs] at h
    nlinarith [h]
  have h := key (b / Q)
  have e : a - 2 * (b / Q) * b + (b / Q) ^ 2 * Q = (a * Q - b ^ 2) / Q := by
    field_simp
    ring
  rw [e] at h
  have := (div_nonneg_iff.mp h)
  rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
  · linarith
  · linarith

lemma inner_eq {n : ℕ} (x w : EuclideanSpace ℝ (Fin n)) : ⟪x, w⟫_ℝ = ⇑w ⬝ᵥ ⇑x := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

lemma sqrt_ratio (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) :
    Real.sqrt ((1 - y) / y) = Real.sqrt (y * (1 - y)) / y := by
  have e : (1 - y) / y = (y * (1 - y)) / y ^ 2 := by
    field_simp
  rw [e, Real.sqrt_div (by nlinarith), Real.sqrt_sq hy0.le]

end P7398ea44

open MeasureTheory Matrix InnerProductSpace WorstCaseVaR.KnownMoments in
theorem solution {n : ℕ}
    (xhat w : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ y : ℝ, 0 < y → y < 1 →
      IsGreatest {r : ℝ | ∃ v : EuclideanSpace ℝ (Fin n),
          (Γ - (1 / (y * (1 - y))) • vecMulVec ⇑(v - y • xhat) ⇑(v - y • xhat)).PosSemidef ∧
          r = -⟪v, w⟫_ℝ / y}
        (Real.sqrt ((1 - y) / y) * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ)) ∧
    IsGreatest
      ((fun y : ℝ => Real.sqrt ((1 - y) / y) * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ) ''
        Set.Icc ε 1)
      (kappa ε * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ) := by
  have hPSD : Γ.PosSemidef := hΓ.posSemidef
  have hQ0 : 0 ≤ ⇑w ⬝ᵥ Γ *ᵥ ⇑w := by
    have := hPSD.dotProduct_mulVec_nonneg ⇑w
    simpa using this
  refine ⟨?_, ?_⟩
  · intro y hy0 hy1
    have hc : 0 < y * (1 - y) := by nlinarith
    set c := y * (1 - y) with hc_def
    set Q := ⇑w ⬝ᵥ Γ *ᵥ ⇑w with hQ_def
    rw [P7398ea44.sqrt_ratio y hy0 hy1]
    constructor
    · rcases hQ0.lt_or_eq with hQ | hQ
      · -- attainment with u = -(√c/√Q) Γ w
        set s := Real.sqrt c / Real.sqrt Q with hs_def
        have hsqQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
        have hs2 : s ^ 2 = c / Q := by
          rw [hs_def, div_pow, Real.sq_sqrt hc.le, Real.sq_sqrt hQ.le]
        refine ⟨y • xhat + (-s) • WithLp.toLp 2 (Γ *ᵥ ⇑w), ?_, ?_⟩
        · have hu : ⇑(y • xhat + (-s) • WithLp.toLp 2 (Γ *ᵥ ⇑w) - y • xhat)
              = (-s) • (Γ *ᵥ ⇑w) := by
            ext i
            simp
          rw [hu]
          refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
          · ext i j
            have hij := congrFun (congrFun hPSD.1.eq i) j
            simp [conjTranspose, vecMulVec] at hij ⊢
            rw [hij]
            ring
          · intro z
            simp only [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
              smul_eq_mul, P7398ea44.quad_vmv]
            have hcs := P7398ea44.cs Γ hPSD z ⇑w hQ
            have e : 1 / c * (-s * (z ⬝ᵥ (Γ *ᵥ ⇑w))) ^ 2 = (z ⬝ᵥ (Γ *ᵥ ⇑w)) ^ 2 / Q := by
              rw [mul_pow, neg_sq, hs2]
              field_simp
            rw [e, sub_nonneg, div_le_iff₀ hQ]
            exact hcs
        · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, P7398ea44.inner_eq xhat w,
            P7398ea44.inner_eq (WithLp.toLp 2 (Γ *ᵥ ⇑w)) w]
          simp only [← hQ_def]
          have hsq : Real.sqrt Q * Real.sqrt Q = Q := Real.mul_self_sqrt hQ.le
          have hsQ : s * Q = Real.sqrt c * Real.sqrt Q := by
            rw [hs_def, div_mul_eq_mul_div, div_eq_iff hsqQ.ne', mul_assoc, hsq]
          rw [div_mul_eq_mul_div, ← hsQ]
          field_simp
          ring
      · -- Q = 0
        refine ⟨y • xhat, ?_, ?_⟩
        · simp only [sub_self]
          simpa using hPSD
        · rw [← hQ, Real.sqrt_zero, real_inner_smul_left, P7398ea44.inner_eq xhat w]
          field_simp
          ring
    · rintro r ⟨v, hv, rfl⟩
      set u := ⇑(v - y • xhat) with hu_def
      have h := hv.dotProduct_mulVec_nonneg ⇑w
      simp only [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
        smul_eq_mul, P7398ea44.quad_vmv] at h
      have hb : (⇑w ⬝ᵥ u) ^ 2 ≤ c * Q := by
        have : 1 / c * (⇑w ⬝ᵥ u) ^ 2 ≤ Q := by linarith
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hc] at this
        linarith
      have hvw : ⟪v, w⟫_ℝ = ⇑w ⬝ᵥ u + y * ⟪xhat, w⟫_ℝ := by
        have : v = (v - y • xhat) + y • xhat := by abel
        conv_lhs => rw [this]
        rw [inner_add_left, real_inner_smul_left, P7398ea44.inner_eq (v - y • xhat) w]
      rw [hvw]
      have habs : |⇑w ⬝ᵥ u| ≤ Real.sqrt (c * Q) := Real.abs_le_sqrt hb
      rw [Real.sqrt_mul hc.le] at habs
      have hneg : -(⇑w ⬝ᵥ u) ≤ Real.sqrt c * Real.sqrt Q := le_trans (neg_le_abs _) habs
      have : -(⇑w ⬝ᵥ u + y * ⟪xhat, w⟫_ℝ) / y
          = -(⇑w ⬝ᵥ u) / y - ⟪xhat, w⟫_ℝ := by
        field_simp
        ring
      rw [this]
      have : Real.sqrt c / y * Real.sqrt Q = (Real.sqrt c * Real.sqrt Q) / y := by ring
      rw [this]
      have := div_le_div_of_nonneg_right hneg hy0.le
      linarith
  · constructor
    · refine ⟨ε, ⟨le_refl ε, hε1⟩, ?_⟩
      simp only [WorstCaseVaR.KnownMoments.kappa]
    · rintro r ⟨y, ⟨hy1, hy2⟩, rfl⟩
      simp only [WorstCaseVaR.KnownMoments.kappa]
      have hy0 : 0 < y := lt_of_lt_of_le hε0 hy1
      have hle : (1 - y) / y ≤ (1 - ε) / ε := by
        rw [div_le_div_iff₀ hy0 hε0]
        nlinarith
      have := Real.sqrt_le_sqrt hle
      have := mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg (⇑w ⬝ᵥ Γ *ᵥ ⇑w))
      linarith

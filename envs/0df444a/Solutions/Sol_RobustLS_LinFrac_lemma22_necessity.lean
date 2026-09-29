-- Prove2me | solution 1 for RobustLS.LinFrac.lemma22_necessity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:18:40.785972+00:00
-- url     : https://prove2.me/submissions/08e62800-5971-4757-af38-ba355d94cde0

import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

lemma aux_l22_dself_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

lemma aux_l22_dmv {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (v : Fin a → ℝ) (w : Fin b → ℝ) :
    v ⬝ᵥ (M *ᵥ w) = (Mᵀ *ᵥ v) ⬝ᵥ w := by
  rw [dotProduct_mulVec, mulVec_transpose]

lemma aux_l22_qexp {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (u w : ι → ℝ) (s t : ℝ) :
    (s • u + t • w) ⬝ᵥ (M *ᵥ (s • u + t • w)) =
      s ^ 2 * (u ⬝ᵥ (M *ᵥ u)) + s * t * (u ⬝ᵥ (M *ᵥ w) + w ⬝ᵥ (M *ᵥ u)) +
        t ^ 2 * (w ⬝ᵥ (M *ᵥ w)) := by
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

lemma aux_l22_pair (p q r α γ δ : ℝ) (hp : 0 < p) (hr : r < 0)
    (h : ∀ s t : ℝ, 0 ≤ s ^ 2 * p + s * t * q + t ^ 2 * r →
      0 ≤ s ^ 2 * α + s * t * γ + t ^ 2 * δ) : α * r ≤ δ * p := by
  have hpr : 0 < p * (-r) := mul_pos hp (neg_pos.mpr hr)
  have hD : 0 < q ^ 2 - 4 * p * r := by nlinarith [sq_nonneg q]
  set σ := Real.sqrt (q ^ 2 - 4 * p * r) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.mpr hD
  have hσ2 : σ ^ 2 = q ^ 2 - 4 * p * r := Real.sq_sqrt hD.le
  have h1 := h (-q - σ) (2 * p) (le_of_eq (by linear_combination (-p) * hσ2))
  have h2 := h (-q + σ) (2 * p) (le_of_eq (by linear_combination (-p) * hσ2))
  have hs2 : 0 < σ - q := by nlinarith
  have hs1 : 0 < σ + q := by nlinarith
  have key : 8 * σ * p * (δ * p - α * r) =
      (σ - q) * ((-q - σ) ^ 2 * α + (-q - σ) * (2 * p) * γ + (2 * p) ^ 2 * δ) +
      (σ + q) * ((-q + σ) ^ 2 * α + (-q + σ) * (2 * p) * γ + (2 * p) ^ 2 * δ) := by
    linear_combination (-2 * σ * α) * hσ2
  have hnn : 0 ≤ 8 * σ * p * (δ * p - α * r) := by
    rw [key]; exact add_nonneg (mul_nonneg hs2.le h1) (mul_nonneg hs1.le h2)
  have hpos : 0 < 8 * σ * p := by positivity
  have := (mul_nonneg_iff_of_pos_left hpos).mp hnn
  linarith

lemma aux_l22_slemma {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) (z₀ : ι → ℝ)
    (hz₀ : 0 < z₀ ⬝ᵥ (B *ᵥ z₀))
    (himp : ∀ z, 0 ≤ z ⬝ᵥ (B *ᵥ z) → 0 ≤ z ⬝ᵥ (A *ᵥ z)) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ∀ z, 0 ≤ z ⬝ᵥ ((A - τ • B) *ᵥ z) := by
  have hpair : ∀ u w : ι → ℝ, 0 < u ⬝ᵥ (B *ᵥ u) → w ⬝ᵥ (B *ᵥ w) < 0 →
      w ⬝ᵥ (A *ᵥ w) / w ⬝ᵥ (B *ᵥ w) ≤ u ⬝ᵥ (A *ᵥ u) / u ⬝ᵥ (B *ᵥ u) := by
    intro u w hu hw
    have := aux_l22_pair (u ⬝ᵥ (B *ᵥ u)) (u ⬝ᵥ (B *ᵥ w) + w ⬝ᵥ (B *ᵥ u)) (w ⬝ᵥ (B *ᵥ w))
      (u ⬝ᵥ (A *ᵥ u)) (u ⬝ᵥ (A *ᵥ w) + w ⬝ᵥ (A *ᵥ u)) (w ⬝ᵥ (A *ᵥ w)) hu hw
      (fun s t hst => by
        have e1 := aux_l22_qexp B u w s t
        have e2 := aux_l22_qexp A u w s t
        rw [← e2]
        apply himp
        rw [e1]
        exact hst)
    rw [div_le_iff_of_neg hw, div_mul_eq_mul_div, div_le_iff₀ hu]
    linarith
  set S : Set ℝ := {x | ∃ w : ι → ℝ, w ⬝ᵥ (B *ᵥ w) < 0 ∧ x = w ⬝ᵥ (A *ᵥ w) / w ⬝ᵥ (B *ᵥ w)}
    with hS
  have hbdd : BddAbove S := ⟨z₀ ⬝ᵥ (A *ᵥ z₀) / z₀ ⬝ᵥ (B *ᵥ z₀), by
    rintro x ⟨w, hw, rfl⟩; exact hpair z₀ w hz₀ hw⟩
  refine ⟨max 0 (sSup S), le_max_left _ _, fun z => ?_⟩
  have hexp : z ⬝ᵥ ((A - max 0 (sSup S) • B) *ᵥ z) =
      z ⬝ᵥ (A *ᵥ z) - max 0 (sSup S) * z ⬝ᵥ (B *ᵥ z) := by
    simp [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul]
  rw [hexp]
  rcases lt_trichotomy (z ⬝ᵥ (B *ᵥ z)) 0 with hneg | hzero | hpos
  · have hmem : z ⬝ᵥ (A *ᵥ z) / z ⬝ᵥ (B *ᵥ z) ∈ S := ⟨z, hneg, rfl⟩
    have h1 : z ⬝ᵥ (A *ᵥ z) / z ⬝ᵥ (B *ᵥ z) ≤ max 0 (sSup S) :=
      (le_csSup hbdd hmem).trans (le_max_right _ _)
    rw [div_le_iff_of_neg hneg] at h1
    linarith
  · rw [hzero]; simpa using himp z hzero.ge
  · have hA : 0 ≤ z ⬝ᵥ (A *ᵥ z) := himp z hpos.le
    have h1 : max 0 (sSup S) ≤ z ⬝ᵥ (A *ᵥ z) / z ⬝ᵥ (B *ᵥ z) := by
      apply max_le (div_nonneg hA hpos.le)
      apply Real.sSup_le _ (div_nonneg hA hpos.le)
      rintro x ⟨w, hw, rfl⟩
      exact hpair z w hpos hw
    rw [le_div_iff₀ hpos] at h1
    linarith

lemma aux_l22_specNorm_le_one {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    (h : ∀ w : Fin n → ℝ, (X *ᵥ w) ⬝ᵥ (X *ᵥ w) ≤ w ⬝ᵥ w) : specNorm X ≤ 1 := by
  unfold specNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => ?_)
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  have := h (WithLp.ofLp w)
  simpa [dotProduct, sq, toLpLin_apply] using this

lemma aux_l22_rank1 {k l : ℕ} (a : Fin k → ℝ) (b : Fin l → ℝ) (c : ℝ) (hc : 0 < c)
    (h : (a ⬝ᵥ a) * (b ⬝ᵥ b) ≤ c ^ 2) : specNorm (c⁻¹ • vecMulVec a b) ≤ 1 := by
  apply aux_l22_specNorm_le_one
  intro w
  have hcs : (b ⬝ᵥ w) ^ 2 ≤ (b ⬝ᵥ b) * (w ⬝ᵥ w) := by
    simpa [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ b w
  have haa := aux_l22_dself_nonneg a
  have hww := aux_l22_dself_nonneg w
  have e : ((c⁻¹ • vecMulVec a b) *ᵥ w) ⬝ᵥ ((c⁻¹ • vecMulVec a b) *ᵥ w) =
      ((b ⬝ᵥ w) ^ 2 * (a ⬝ᵥ a)) / c ^ 2 := by
    simp only [smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  have h3 := mul_le_mul_of_nonneg_right hcs haa
  have h4 := mul_le_mul_of_nonneg_right h hww
  nlinarith

lemma aux_l22_attain {k l : ℕ} (T : Matrix (Fin l) (Fin k) ℝ) (h : 1 ≤ specNorm T) :
    ∃ v : Fin k → ℝ, v ⬝ᵥ v ≤ 1 ∧ 1 ≤ (T *ᵥ v) ⬝ᵥ (T *ᵥ v) := by
  set f := LinearMap.toContinuousLinearMap (toEuclideanLin T) with hf
  obtain ⟨v₀, hv₀, hmax⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin k)) 1).exists_isMaxOn
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩ (continuous_norm.comp f.continuous).continuousOn
  have hle : ‖f‖ ≤ ‖f v₀‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun w => ?_)
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have hmem : ‖w‖⁻¹ • w ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hw'.ne']
      have := isMaxOn_iff.mp hmax _ hmem
      simp only [Function.comp, map_smul, norm_smul, norm_inv, norm_norm] at this
      rw [inv_mul_le_iff₀ hw'] at this
      linarith [mul_comm ‖w‖ ‖f v₀‖]
  have h' : 1 ≤ ‖f‖ := h
  have h1 : 1 ≤ ‖f v₀‖ := h'.trans hle
  have h2 : ‖v₀‖ ≤ 1 := by simpa using hv₀
  refine ⟨WithLp.ofLp v₀, ?_, ?_⟩
  · have e := EuclideanSpace.real_norm_sq_eq v₀
    have : ‖v₀‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v₀]
    rw [e] at this
    simpa [dotProduct, sq] using this
  · have e := EuclideanSpace.real_norm_sq_eq (f v₀)
    have : 1 ≤ ‖f v₀‖ ^ 2 := by nlinarith
    rw [e] at this
    simpa [dotProduct, sq, hf, toLpLin_apply] using this

lemma aux_l22_reduce {d k l : ℕ} (T₁ : Matrix (Fin d) (Fin d) ℝ)
    (T₂ : Matrix (Fin d) (Fin k) ℝ) (T₃ : Matrix (Fin l) (Fin d) ℝ)
    (T₄ : Matrix (Fin l) (Fin k) ℝ)
    (h9 : ∀ Δ : Matrix (Fin k) (Fin l) ℝ, specNorm Δ ≤ 1 →
      (1 - T₄ * Δ).det ≠ 0 ∧ (lftT T₁ T₂ T₃ T₄ Δ).PosSemidef)
    (hT1 : ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ (T₁ *ᵥ x))
    (x : Fin d → ℝ) (p : Fin l → ℝ)
    (hG : p ⬝ᵥ p ≤ (T₂ᵀ *ᵥ x + T₄ᵀ *ᵥ p) ⬝ᵥ (T₂ᵀ *ᵥ x + T₄ᵀ *ᵥ p)) :
    0 ≤ x ⬝ᵥ (T₁ *ᵥ x) + 2 * ((T₃ *ᵥ x) ⬝ᵥ p) := by
  set q := T₂ᵀ *ᵥ x + T₄ᵀ *ᵥ p with hq
  by_cases hq0 : q ⬝ᵥ q = 0
  · have hp0 : p = 0 := by
      have := aux_l22_dself_nonneg p
      exact dotProduct_self_eq_zero.mp (le_antisymm (hG.trans hq0.le) this)
    subst hp0
    simpa using hT1 x
  · have hc : 0 < q ⬝ᵥ q := lt_of_le_of_ne (aux_l22_dself_nonneg q) (Ne.symm hq0)
    set c := q ⬝ᵥ q with hcdef
    set Δ : Matrix (Fin k) (Fin l) ℝ := c⁻¹ • vecMulVec q p with hΔ
    have hΔn : specNorm Δ ≤ 1 :=
      aux_l22_rank1 q p c hc (by nlinarith [aux_l22_dself_nonneg p])
    obtain ⟨hdet, hpsd⟩ := h9 Δ hΔn
    have hΔq : Δᵀ *ᵥ q = p := by
      rw [hΔ, transpose_smul, transpose_vecMulVec, smul_mulVec, vecMulVec_mulVec,
        op_smul_eq_smul, smul_smul, ← hcdef, inv_mul_cancel₀ hc.ne', one_smul]
    set N := 1 - T₄ * Δ with hN
    have hNt : Nᵀ *ᵥ p = Δᵀ *ᵥ (T₂ᵀ *ᵥ x) := by
      have hpe : p = Δᵀ *ᵥ (T₂ᵀ *ᵥ x) + Δᵀ *ᵥ (T₄ᵀ *ᵥ p) := by
        rw [← mulVec_add]; exact hΔq.symm
      rw [hN, transpose_sub, transpose_one, transpose_mul, sub_mulVec, one_mulVec,
        ← mulVec_mulVec, sub_eq_iff_eq_add]
      exact hpe
    have hp : (N⁻¹)ᵀ *ᵥ (Δᵀ *ᵥ (T₂ᵀ *ᵥ x)) = p := by
      rw [← hNt, transpose_nonsing_inv, mulVec_mulVec,
        nonsing_inv_mul _ (by rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hdet),
        one_mulVec]
    have hval := hpsd.dotProduct_mulVec_nonneg x
    have e3 : (T₃ᵀ * (N⁻¹)ᵀ * Δᵀ * T₂ᵀ) *ᵥ x = T₃ᵀ *ᵥ p := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hp]
    have e2 : x ⬝ᵥ ((T₂ * Δ * N⁻¹ * T₃) *ᵥ x) = x ⬝ᵥ ((T₃ᵀ * (N⁻¹)ᵀ * Δᵀ * T₂ᵀ) *ᵥ x) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
      congr 2
      simp [transpose_mul, Matrix.mul_assoc]
    have hform : star x ⬝ᵥ (lftT T₁ T₂ T₃ T₄ Δ *ᵥ x) =
        x ⬝ᵥ (T₁ *ᵥ x) + 2 * ((T₃ *ᵥ x) ⬝ᵥ p) := by
      simp only [lftT, star_trivial, add_mulVec, dotProduct_add]
      rw [← hN, e2, e3, dotProduct_mulVec x T₃ᵀ p, vecMul_transpose]
      ring
    rw [hform] at hval
    exact hval

end RobustLS.LinFrac

open RobustLS.LinFrac
open Matrix

theorem solution {d k l : ℕ} (T₁ : Matrix (Fin d) (Fin d) ℝ) (hT₁ : T₁ = T₁ᵀ)
    (T₂ : Matrix (Fin d) (Fin k) ℝ) (T₃ : Matrix (Fin l) (Fin d) ℝ)
    (T₄ : Matrix (Fin l) (Fin k) ℝ) (hT : T₂ ≠ 0 ∨ T₃ = 0)
    (h9 : ∀ Δ : Matrix (Fin k) (Fin l) ℝ, specNorm Δ ≤ 1 →
      (1 - T₄ * Δ).det ≠ 0 ∧ (lftT T₁ T₂ T₃ T₄ Δ).PosSemidef) :
    specNorm T₄ < 1 ∧ ∃ τ : ℝ, 0 ≤ τ ∧ (lemma22Block T₁ T₂ T₃ T₄ τ).PosSemidef := by
  have h0n : specNorm (0 : Matrix (Fin k) (Fin l) ℝ) ≤ 1 :=
    aux_l22_specNorm_le_one 0 (fun w => by simp [aux_l22_dself_nonneg])
  have hT1psd : T₁.PosSemidef := by simpa [lftT] using (h9 0 h0n).2
  have hT1 : ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ (T₁ *ᵥ x) := by
    intro x; simpa using hT1psd.dotProduct_mulVec_nonneg x
  refine ⟨?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨v, hv1, hv2⟩ := aux_l22_attain T₄ hcon
    set u := T₄ *ᵥ v with hu
    have hu0 : 0 < u ⬝ᵥ u := by linarith
    set Δ : Matrix (Fin k) (Fin l) ℝ := (u ⬝ᵥ u)⁻¹ • vecMulVec v u with hΔ
    have hΔn : specNorm Δ ≤ 1 :=
      aux_l22_rank1 v u _ hu0 (by nlinarith [aux_l22_dself_nonneg v])
    apply (h9 Δ hΔn).1
    rw [← exists_mulVec_eq_zero_iff]
    refine ⟨u, ?_, ?_⟩
    · intro h; rw [h] at hu0; simp at hu0
    · rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hΔ, smul_mulVec, vecMulVec_mulVec,
        op_smul_eq_smul, smul_smul, inv_mul_cancel₀ hu0.ne', one_smul, ← hu, sub_self]
  · set A : Matrix (Fin d ⊕ Fin l) (Fin d ⊕ Fin l) ℝ :=
      fromBlocks T₁ T₃ᵀ T₃ (0 : Matrix (Fin l) (Fin l) ℝ) with hA
    set B : Matrix (Fin d ⊕ Fin l) (Fin d ⊕ Fin l) ℝ :=
      fromBlocks (T₂ * T₂ᵀ) (T₂ * T₄ᵀ) (T₄ * T₂ᵀ) (T₄ * T₄ᵀ - 1) with hB
    have hqA : ∀ (x : Fin d → ℝ) (p : Fin l → ℝ),
        Sum.elim x p ⬝ᵥ (A *ᵥ Sum.elim x p) = x ⬝ᵥ (T₁ *ᵥ x) + 2 * ((T₃ *ᵥ x) ⬝ᵥ p) := by
      intro x p
      rw [hA, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim,
        zero_mulVec, add_zero, dotProduct_add, dotProduct_mulVec x T₃ᵀ p, vecMul_transpose,
        dotProduct_comm p (T₃ *ᵥ x)]
      ring
    have hqB : ∀ (x : Fin d → ℝ) (p : Fin l → ℝ),
        Sum.elim x p ⬝ᵥ (B *ᵥ Sum.elim x p) =
          (T₂ᵀ *ᵥ x + T₄ᵀ *ᵥ p) ⬝ᵥ (T₂ᵀ *ᵥ x + T₄ᵀ *ᵥ p) - p ⬝ᵥ p := by
      intro x p
      rw [hB, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim]
      simp only [sub_mulVec, one_mulVec, ← mulVec_mulVec, dotProduct_add, add_dotProduct,
        dotProduct_sub, aux_l22_dmv T₂, aux_l22_dmv T₄]
      ring
    have hsplit : ∀ z : Fin d ⊕ Fin l → ℝ, z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) :=
      fun z => (Sum.elim_comp_inl_inr z).symm
    have hkey : ∃ τ : ℝ, 0 ≤ τ ∧ ∀ z, 0 ≤ z ⬝ᵥ ((A - τ • B) *ᵥ z) := by
      rcases hT with hT2 | hT3
      · obtain ⟨x₀, hx₀⟩ : ∃ x : Fin d → ℝ, T₂ᵀ *ᵥ x ≠ 0 := by
          by_contra hc
          push Not at hc
          apply hT2
          ext i j
          have := congr_fun (hc (Pi.single i 1)) j
          simpa [mulVec_single_one] using this
        refine aux_l22_slemma A B (Sum.elim x₀ 0) ?_ ?_
        · rw [hqB]
          simp only [mulVec_zero, add_zero, dotProduct_zero, sub_zero]
          exact lt_of_le_of_ne (aux_l22_dself_nonneg _)
            (Ne.symm (fun h => hx₀ (dotProduct_self_eq_zero.mp h)))
        · intro z hz
          rw [hsplit z, hqB] at hz
          rw [hsplit z, hqA]
          exact aux_l22_reduce T₁ T₂ T₃ T₄ h9 hT1 _ _ (by linarith)
      · refine ⟨0, le_refl _, fun z => ?_⟩
        rw [zero_smul, sub_zero, hsplit z, hqA, hT3]
        simpa using hT1 _
    obtain ⟨τ, hτ, hz⟩ := hkey
    refine ⟨τ, hτ, ?_⟩
    have hblk : lemma22Block T₁ T₂ T₃ T₄ τ = A - τ • B := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [lemma22Block, hA, hB] <;> ring
    rw [hblk]
    have hAt : Aᵀ = A := by
      rw [hA, fromBlocks_transpose, transpose_transpose, transpose_zero, ← hT₁]
    have hBt : Bᵀ = B := by
      rw [hB, fromBlocks_transpose]
      simp [transpose_mul, transpose_sub]
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun z => by simpa using hz z)
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul, hAt,
      hBt]

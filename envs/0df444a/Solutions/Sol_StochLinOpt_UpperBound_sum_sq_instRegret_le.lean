-- Prove2me | solution 1 for StochLinOpt.UpperBound.sum_sq_instRegret_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:40:48.515863+00:00
-- url     : https://prove2.me/submissions/d48d5e68-5536-4955-b058-d3975985f0f8

import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_confidenceBall2
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities

open Matrix

namespace StochLinOpt.UpperBound

lemma aux_ssq_posDef {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) : (designMatrix x t).PosDef := by
  unfold designMatrix
  refine Matrix.PosDef.one.add_posSemidef ?_
  refine Matrix.posSemidef_sum _ (fun τ _ => ?_)
  simpa using Matrix.posSemidef_vecMulVec_self_star (x τ)

lemma aux_ssq_succ {n : ℕ} (x : ℕ → Fin n → ℝ) {t : ℕ} (ht : 1 ≤ t) :
    designMatrix x (t+1) = designMatrix x t + vecMulVec (x t) (x t) := by
  unfold designMatrix
  rw [Finset.sum_Ico_succ_top ht, add_assoc]

lemma aux_ssq_det_succ {n : ℕ} (x : ℕ → Fin n → ℝ) {t : ℕ} (ht : 1 ≤ t) :
    (designMatrix x (t+1)).det =
      (designMatrix x t).det * (1 + x t ⬝ᵥ ((designMatrix x t)⁻¹ *ᵥ x t)) := by
  rw [aux_ssq_succ x ht, vecMulVec_eq Unit, det_add_replicateCol_mul_replicateRow]
  · congr 1
    rw [det_unique]
    simp [Matrix.mul_apply, replicateRow, replicateCol, mulVec, dotProduct, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  · exact (aux_ssq_posDef x t).det_pos.ne'.isUnit

lemma aux_ssq_quad_nonneg {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) :
    0 ≤ x t ⬝ᵥ ((designMatrix x t)⁻¹ *ᵥ x t) := by
  simpa using (aux_ssq_posDef x t).inv.posSemidef.dotProduct_mulVec_nonneg (x t)

lemma aux_ssq_width_sq {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) :
    width x t ^ 2 = x t ⬝ᵥ ((designMatrix x t)⁻¹ *ᵥ x t) := by
  unfold width
  exact Real.sq_sqrt (aux_ssq_quad_nonneg x t)

lemma aux_ssq_sum_log {n : ℕ} (x : ℕ → Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, Real.log (1 + width x t ^ 2) =
      Real.log (designMatrix x (T+1)).det := by
  induction T with
  | zero => simp [designMatrix]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, aux_ssq_det_succ x (by omega : 1 ≤ k+1),
      Real.log_mul, aux_ssq_width_sq]
    · exact (aux_ssq_posDef x _).det_pos.ne'
    · have := aux_ssq_quad_nonneg x (k+1)
      linarith

lemma aux_ssq_trace_le {n : ℕ} (x : ℕ → Fin n → ℝ) (T : ℕ)
    (hx : ∀ t ∈ Finset.Icc 1 T, ∀ i, |x t i| ≤ 1) :
    (designMatrix x (T+1)).trace ≤ n * ((T:ℝ) + 1) := by
  unfold designMatrix
  rw [trace_add, trace_one, trace_sum]
  simp only [trace_vecMulVec, Fintype.card_fin]
  have h1 : ∀ τ ∈ Finset.Ico 1 (T+1), x τ ⬝ᵥ x τ ≤ n := by
    intro τ hτ
    have hτ' : τ ∈ Finset.Icc 1 T := by
      simp only [Finset.mem_Ico, Finset.mem_Icc] at hτ ⊢; omega
    unfold dotProduct
    calc ∑ i, x τ i * x τ i ≤ ∑ _i : Fin n, (1:ℝ) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have := hx τ hτ' i
          rw [abs_le] at this
          nlinarith
      _ = n := by simp
  have h2 := Finset.sum_le_sum h1
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h2
  have : ((T + 1 - 1 : ℕ) : ℝ) = T := by simp
  rw [this] at h2
  nlinarith

lemma aux_ssq_logdet_le {n : ℕ} (x : ℕ → Fin n → ℝ) (T : ℕ)
    (hx : ∀ t ∈ Finset.Icc 1 T, ∀ i, |x t i| ≤ 1) :
    Real.log (designMatrix x (T+1)).det ≤ n * Real.log ((T:ℝ) + 1) := by
  have hA := aux_ssq_posDef x (T+1)
  have htr := aux_ssq_trace_le x T hx
  have htr' : (designMatrix x (T+1)).trace = ∑ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.trace_eq_sum_eigenvalues
  have hdet : (designMatrix x (T+1)).det = ∏ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.det_eq_prod_eigenvalues
  have hpos : ∀ i, 0 < hA.isHermitian.eigenvalues i := fun i => hA.eigenvalues_pos i
  rw [hdet, Real.log_prod (fun i _ => (hpos i).ne')]
  have hc : (0:ℝ) < (T:ℝ) + 1 := by positivity
  have hle : ∀ i, Real.log (hA.isHermitian.eigenvalues i) ≤
      Real.log ((T:ℝ) + 1) + hA.isHermitian.eigenvalues i / ((T:ℝ) + 1) - 1 := by
    intro i
    have h := Real.log_le_sub_one_of_pos (div_pos (hpos i) hc)
    rw [Real.log_div (hpos i).ne' hc.ne'] at h
    linarith
  calc ∑ i, Real.log (hA.isHermitian.eigenvalues i)
      ≤ ∑ i, (Real.log ((T:ℝ) + 1) + hA.isHermitian.eigenvalues i / ((T:ℝ) + 1) - 1) :=
        Finset.sum_le_sum (fun i _ => hle i)
    _ = n * Real.log ((T:ℝ) + 1) + (∑ i, hA.isHermitian.eigenvalues i) / ((T:ℝ) + 1) - n := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_div]
        simp
    _ ≤ n * Real.log ((T:ℝ) + 1) := by
        rw [← htr']
        have : (designMatrix x (T+1)).trace / ((T:ℝ) + 1) ≤ n := by
          rw [div_le_iff₀ hc]; exact htr
        linarith

lemma aux_ssq_cs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (v y : Fin n → ℝ) :
    (v ⬝ᵥ y) ^ 2 ≤ (v ⬝ᵥ (A *ᵥ v)) * (y ⬝ᵥ (A⁻¹ *ᵥ y)) := by
  have hT : Aᵀ = A := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hA.isHermitian.eq
  have hsym : ∀ a b : Fin n → ℝ, a ⬝ᵥ (A *ᵥ b) = b ⬝ᵥ (A *ᵥ a) := by
    intro a b
    rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]
  have hpsd : ∀ w, 0 ≤ w ⬝ᵥ (A *ᵥ w) := fun w => by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg w
  set u := A⁻¹ *ᵥ y with hu
  have hyu : y = A *ᵥ u := by
    rw [hu, mulVec_mulVec, mul_nonsing_inv _ hA.det_pos.ne'.isUnit, one_mulVec]
  have e1 : v ⬝ᵥ y = v ⬝ᵥ (A *ᵥ u) := by rw [← hyu]
  have e2 : y ⬝ᵥ u = u ⬝ᵥ (A *ᵥ u) := by
    rw [dotProduct_comm]; exact congrArg (fun z => u ⬝ᵥ z) hyu
  rw [e1, e2]
  have hq : ∀ s : ℝ, 0 ≤ (u ⬝ᵥ (A *ᵥ u)) * (s * s) + (-2 * (v ⬝ᵥ (A *ᵥ u))) * s +
      v ⬝ᵥ (A *ᵥ v) := by
    intro s
    have h := hpsd (v - s • u)
    simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul] at h
    rw [hsym u v] at h
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

lemma aux_ssq_par {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (a b : Fin n → ℝ) :
    (a - b) ⬝ᵥ (A *ᵥ (a - b)) ≤ 2 * (a ⬝ᵥ (A *ᵥ a)) + 2 * (b ⬝ᵥ (A *ᵥ b)) := by
  have h : 0 ≤ (a + b) ⬝ᵥ (A *ᵥ (a + b)) := by
    simpa using hA.dotProduct_mulVec_nonneg (a + b)
  simp only [mulVec_add, mulVec_sub, add_dotProduct, dotProduct_add, sub_dotProduct,
    dotProduct_sub] at h ⊢
  linarith

lemma aux_ssq_beta_mono {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {s t : ℕ} (hs : 1 ≤ s)
    (hst : s ≤ t) : beta n δ s ≤ beta n δ t := by
  unfold beta
  have hs' : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hst' : (s:ℝ) ≤ t := by exact_mod_cast hst
  have h1 : 0 ≤ Real.log s := Real.log_nonneg hs'
  have h2 : Real.log s ≤ Real.log t := Real.log_le_log (by linarith) hst'
  have h1' : 0 ≤ Real.log t := le_trans h1 h2
  have h3 : 0 < Real.log ((s:ℝ)^2/δ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hδ]; nlinarith
  have h4 : Real.log ((s:ℝ)^2/δ) ≤ Real.log ((t:ℝ)^2/δ) :=
    Real.log_le_log (by positivity) (by gcongr)
  have hn : (0:ℝ) ≤ 128 * (n:ℝ) := by positivity
  apply max_le_max
  · exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hn) h4 h3.le (mul_nonneg hn h1')
  · have : 0 ≤ 8 / 3 * Real.log ((s:ℝ)^2/δ) := by positivity
    exact pow_le_pow_left₀ this (by linarith) 2

lemma aux_ssq_min_log {u : ℝ} (hu : 0 ≤ u) : min u 1 ≤ 2 * Real.log (1 + u) := by
  rcases le_or_gt u 1 with h | h
  · rw [min_eq_left h]
    have h1 := Real.one_sub_inv_le_log_of_pos (by linarith : (0:ℝ) < 1 + u)
    have h2 : u / 2 ≤ 1 - (1 + u)⁻¹ := by
      rw [show 1 - (1 + u)⁻¹ = u / (1 + u) by field_simp; ring]
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    linarith
  · rw [min_eq_right h.le]
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log (1 + u) := Real.log_le_log (by norm_num) (by linarith)
    norm_num at h1
    linarith

end StochLinOpt.UpperBound

open StochLinOpt.UpperBound
open Matrix

theorem solution {n : ℕ} (D : Set (Fin n → ℝ)) (δ : ℝ)
    (μ xstar : Fin n → ℝ) (x : ℕ → Fin n → ℝ) (ℓ : ℕ → ℝ)
    (hD_cube : ∀ y ∈ D, ∀ i, |y i| ≤ 1)
    (hμD : ∀ y ∈ D, |μ ⬝ᵥ y| ≤ 1)
    (hxstar : xstar ∈ D ∧ ∀ y ∈ D, μ ⬝ᵥ xstar ≤ μ ⬝ᵥ y)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hβ₁ : 1 ≤ beta n δ 1)
    (hrun : IsConfidenceBall2Run D δ x ℓ) (T : ℕ)
    (hμ : ∀ t ∈ Finset.Icc 1 T, μ ∈ confBall δ x ℓ t) :
    ∑ t ∈ Finset.Icc 1 T, (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤
      8 * n * beta n δ T * Real.log (T + 1) := by
  have hround : ∀ t ∈ Finset.Icc 1 T, (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤
      8 * beta n δ T * Real.log (1 + width x t ^ 2) := by
    intro t ht
    obtain ⟨ht1, htT⟩ := Finset.mem_Icc.mp ht
    obtain ⟨hxD, μt, hμt, hmin⟩ := hrun t ht1
    have hApd := aux_ssq_posDef x t
    have hw2 := aux_ssq_width_sq x t
    have hw0 : 0 ≤ width x t ^ 2 := sq_nonneg _
    have hr0 : 0 ≤ μ ⬝ᵥ x t - μ ⬝ᵥ xstar := by linarith [hxstar.2 _ hxD]
    have hr2 : μ ⬝ᵥ x t - μ ⬝ᵥ xstar ≤ 2 := by
      have h1 := hμD _ hxD
      have h2 := hμD _ hxstar.1
      rw [abs_le] at h1 h2
      linarith
    have hle : μ ⬝ᵥ x t - μ ⬝ᵥ xstar ≤ (μ - μt) ⬝ᵥ x t := by
      have := hmin μ (hμ t ht) xstar hxstar.1
      rw [sub_dotProduct]; linarith
    have hball : (μ - μt) ⬝ᵥ (designMatrix x t *ᵥ (μ - μt)) ≤ 4 * beta n δ t := by
      have h := aux_ssq_par (designMatrix x t) hApd.posSemidef (μ - muHat x ℓ t)
        (μt - muHat x ℓ t)
      have e : (μ - muHat x ℓ t) - (μt - muHat x ℓ t) = μ - μt := by abel
      rw [e] at h
      have h1 : (μ - muHat x ℓ t) ⬝ᵥ (designMatrix x t *ᵥ (μ - muHat x ℓ t)) ≤ beta n δ t :=
        hμ t ht
      have h2 : (μt - muHat x ℓ t) ⬝ᵥ (designMatrix x t *ᵥ (μt - muHat x ℓ t)) ≤ beta n δ t :=
        hμt
      linarith
    have hcs := aux_ssq_cs (designMatrix x t) hApd (μ - μt) (x t)
    have hsq : (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤ 4 * beta n δ t * width x t ^ 2 := by
      calc (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤ ((μ - μt) ⬝ᵥ x t) ^ 2 := pow_le_pow_left₀ hr0 hle 2
        _ ≤ _ := hcs
        _ ≤ 4 * beta n δ t * width x t ^ 2 := by
          rw [hw2]
          exact mul_le_mul_of_nonneg_right hball (aux_ssq_quad_nonneg x t)
    have hβt1 : 1 ≤ beta n δ t := le_trans hβ₁ (aux_ssq_beta_mono hδ hδ1 le_rfl ht1)
    have hmin' : (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤ 4 * beta n δ t * min (width x t ^ 2) 1 := by
      rcases le_total (width x t ^ 2) 1 with h | h
      · rw [min_eq_left h]; exact hsq
      · rw [min_eq_right h]; nlinarith
    have hlog := aux_ssq_min_log hw0
    have hlog0 : 0 ≤ Real.log (1 + width x t ^ 2) := Real.log_nonneg (by linarith)
    have hβT : beta n δ t ≤ beta n δ T := aux_ssq_beta_mono hδ hδ1 ht1 htT
    calc (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2 ≤ 4 * beta n δ t * min (width x t ^ 2) 1 := hmin'
      _ ≤ 4 * beta n δ t * (2 * Real.log (1 + width x t ^ 2)) := by
          apply mul_le_mul_of_nonneg_left hlog; linarith
      _ = 8 * beta n δ t * Real.log (1 + width x t ^ 2) := by ring
      _ ≤ 8 * beta n δ T * Real.log (1 + width x t ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hlog0; linarith
  have hβT0 : 0 ≤ beta n δ T := by
    unfold beta; exact le_max_of_le_right (sq_nonneg _)
  have hx : ∀ t ∈ Finset.Icc 1 T, ∀ i, |x t i| ≤ 1 := by
    intro t ht i
    exact hD_cube _ (hrun t (Finset.mem_Icc.mp ht).1).1 i
  calc ∑ t ∈ Finset.Icc 1 T, (μ ⬝ᵥ x t - μ ⬝ᵥ xstar) ^ 2
      ≤ ∑ t ∈ Finset.Icc 1 T, 8 * beta n δ T * Real.log (1 + width x t ^ 2) :=
        Finset.sum_le_sum hround
    _ = 8 * beta n δ T * Real.log (designMatrix x (T+1)).det := by
        rw [← Finset.mul_sum, aux_ssq_sum_log]
    _ ≤ 8 * beta n δ T * (n * Real.log ((T:ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left (aux_ssq_logdet_le x T hx); linarith
    _ = 8 * n * beta n δ T * Real.log (T + 1) := by ring

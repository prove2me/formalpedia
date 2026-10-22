-- Prove2me | solution 1 for WrightPDIPM.Potential.eq_4_16
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:43:57.667699+00:00
-- url     : https://prove2.me/submissions/a2f62bd2-e833-473c-8234-70aeae0316df

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting
open Matrix
open WrightPDIPM.Potential

theorem g69b_log_quad (t a τ : ℝ) (ha : |t| ≤ τ) (hτ : τ < 1) :
    -Real.log (1 + t) ≤ -t + t ^ 2 / (2 * (1 - τ)) := by
  have hta : |t| < 1 := lt_of_le_of_lt ha hτ
  have h1 : |(-t)| < 1 := by rwa [abs_neg]
  have hS := Real.hasSum_pow_div_log_of_abs_lt_one h1
  rw [sub_neg_eq_add] at hS
  have hS' := (hasSum_nat_add_iff' (f := fun n : ℕ => (-t) ^ (n + 1) / (n + 1)) 1).mpr hS
  simp only [Finset.range_one, Finset.sum_singleton] at hS'
  set b := |t|
  have hb0 : 0 ≤ b := abs_nonneg t
  have hG : HasSum (fun n : ℕ => b ^ 2 / 2 * b ^ n) (b ^ 2 / 2 * (1 - b)⁻¹) :=
    (hasSum_geometric_of_lt_one hb0 hta).mul_left _
  have hle := hasSum_le (fun n => ?_) hS' hG
  · have hb2 : b ^ 2 = t ^ 2 := sq_abs t
    have h1b : 0 < 1 - b := by linarith
    have h1τ : 0 < 1 - τ := by linarith
    have : b ^ 2 / 2 * (1 - b)⁻¹ ≤ t ^ 2 / (2 * (1 - τ)) := by
      rw [hb2, ← div_eq_mul_inv, div_div]
      apply div_le_div_of_nonneg_left (sq_nonneg t) (by positivity)
      linarith
    norm_num at hle
    linarith
  · show _ ≤ _
    have e : b ^ 2 / 2 * b ^ n = b ^ (n + 1 + 1) / 2 := by ring
    rw [e]
    have hpow : (-t) ^ (n + 1 + 1) ≤ b ^ (n + 1 + 1) := by
      calc (-t) ^ (n + 1 + 1) ≤ |(-t) ^ (n + 1 + 1)| := le_abs_self _
        _ = b ^ (n + 1 + 1) := by rw [abs_pow, abs_neg]
    have hc : ((n + 1 : ℕ) : ℝ) + 1 ≥ 2 := by push_cast; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    calc (-t) ^ (n + 1 + 1) / (((n + 1 : ℕ) : ℝ) + 1) ≤ b ^ (n + 1 + 1) / (((n + 1 : ℕ) : ℝ) + 1) :=
          div_le_div_of_nonneg_right hpow (by linarith)
      _ ≤ b ^ (n + 1 + 1) / 2 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hc

theorem g69b_dxds0 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (h1 : Aᵀ *ᵥ dlam + ds = 0) (h2 : A *ᵥ dx = 0) : dx ⬝ᵥ ds = 0 := by
  have : ds = -(Aᵀ *ᵥ dlam) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h1
  rw [this, dotProduct_neg, dotProduct_mulVec, vecMul_transpose, h2]
  simp

theorem g69b_eq_4_16 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hF : (x, lam, s) ∈ Fo A b c)
    (ρ : ℝ) (hρ : (n : ℝ) < ρ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hdir : IsFeasibleDirection A dx dlam ds)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (α : ℝ) (hα0 : 0 < α)
    (hατ : α * max (normInf (fun i => dx i / x i)) (normInf (fun i => ds i / s i)) ≤ τ) :
    Phi ρ (x + α • dx) (s + α • ds) ≤ q ρ τ x s dx ds α := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [Phi, q, g1, g2, norm2]
  obtain ⟨_, _, hx, hs⟩ := hF
  simp only at hx hs
  obtain ⟨hAdx, hAds⟩ := hdir
  have hdxds := g69b_dxds0 A dx dlam ds hAds hAdx
  have hρ0 : 0 < ρ := lt_of_le_of_lt (Nat.cast_nonneg n) hρ
  set tx : Fin n → ℝ := fun i => α * (dx i / x i) with htxdef
  set ts : Fin n → ℝ := fun i => α * (ds i / s i) with htsdef
  have htx : ∀ i, |tx i| ≤ τ := by
    intro i
    have h1 : |dx i / x i| ≤ normInf (fun i => dx i / x i) :=
      le_ciSup (Finite.bddAbove_range (fun j => |dx j / x j|)) i
    have h2 := le_max_left (normInf (fun i => dx i / x i)) (normInf (fun i => ds i / s i))
    simp only [tx, abs_mul, abs_of_pos hα0]
    nlinarith
  have hts : ∀ i, |ts i| ≤ τ := by
    intro i
    have h1 : |ds i / s i| ≤ normInf (fun i => ds i / s i) :=
      le_ciSup (Finite.bddAbove_range (fun j => |ds j / s j|)) i
    have h2 := le_max_right (normInf (fun i => dx i / x i)) (normInf (fun i => ds i / s i))
    simp only [ts, abs_mul, abs_of_pos hα0]
    nlinarith
  have h1tx : ∀ i, 0 < 1 + tx i := fun i => by linarith [(abs_le.mp ((htx i).trans hτ1.le)).1, htx i, neg_abs_le (tx i)]
  have h1ts : ∀ i, 0 < 1 + ts i := fun i => by linarith [hts i, neg_abs_le (ts i)]
  have hx' : ∀ i, (x + α • dx) i = x i * (1 + tx i) := by
    intro i; simp only [tx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; field_simp [(hx i).ne']
  have hs' : ∀ i, (s + α • ds) i = s i * (1 + ts i) := by
    intro i; simp only [ts, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; field_simp [(hs i).ne']
  have hlog : ∀ i, Real.log ((x + α • dx) i * (s + α • ds) i) =
      Real.log (x i * s i) + Real.log (1 + tx i) + Real.log (1 + ts i) := by
    intro i
    rw [hx', hs', show x i * (1 + tx i) * (s i * (1 + ts i)) =
      (x i * s i) * (1 + tx i) * (1 + ts i) by ring]
    have := mul_pos (hx i) (hs i)
    rw [Real.log_mul (mul_pos this (h1tx i)).ne' (h1ts i).ne', Real.log_mul this.ne' (h1tx i).ne']
  have hxs : 0 < x ⬝ᵥ s := by
    exact Finset.sum_pos (fun i _ => mul_pos (hx i) (hs i)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set β := α * ((s ⬝ᵥ dx + x ⬝ᵥ ds) / (x ⬝ᵥ s)) with hβdef
  have hdot : (x + α • dx) ⬝ᵥ (s + α • ds) = (x ⬝ᵥ s) * (1 + β) := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hdxds, dotProduct_comm dx s, hβdef]
    field_simp
    try ring
  have hnewpos : 0 ≤ (x + α • dx) ⬝ᵥ (s + α • ds) := by
    apply Finset.sum_nonneg
    intro i _
    rw [hx', hs']
    have := h1tx i; have := h1ts i; have := hx i; have := hs i
    positivity
  have h1β : 0 < 1 + β := by
    have : 0 < (x + α • dx) ⬝ᵥ (s + α • ds) := by
      apply Finset.sum_pos _ ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      intro i _
      rw [hx', hs']
      have := h1tx i; have := h1ts i; have := hx i; have := hs i
      positivity
    rw [hdot] at this
    exact pos_of_mul_pos_right this hxs.le
  have hlogβ : Real.log (1 + β) ≤ β := by
    have := Real.log_le_sub_one_of_pos h1β; linarith
  have A2 : -∑ i, Real.log (1 + tx i) ≤ ∑ i, (-tx i + tx i ^ 2 / (2 * (1 - τ))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun i _ => g69b_log_quad (tx i) 0 τ (htx i) hτ1)
  have A3 : -∑ i, Real.log (1 + ts i) ≤ ∑ i, (-ts i + ts i ^ 2 / (2 * (1 - τ))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun i _ => g69b_log_quad (ts i) 0 τ (hts i) hτ1)
  have E2 : ∑ i, (-tx i + tx i ^ 2 / (2 * (1 - τ))) =
      -(α * ∑ i, dx i / x i) + (1 / 2) * α ^ 2 * ((1 / (1 - τ)) * norm2 (fun i => dx i / x i) ^ 2) := by
    unfold norm2
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    simp only [tx]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    have : (1 - τ) ≠ 0 := ne_of_gt (by linarith)
    field_simp
    try ring
  have E3 : ∑ i, (-ts i + ts i ^ 2 / (2 * (1 - τ))) =
      -(α * ∑ i, ds i / s i) + (1 / 2) * α ^ 2 * ((1 / (1 - τ)) * norm2 (fun i => ds i / s i) ^ 2) := by
    unfold norm2
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    simp only [ts]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    have : (1 - τ) ≠ 0 := ne_of_gt (by linarith)
    field_simp
    try ring
  have hρβ : ρ * Real.log (1 + β) ≤ ρ * β := mul_le_mul_of_nonneg_left hlogβ hρ0.le
  have hP : Phi ρ x s = ρ * Real.log (x ⬝ᵥ s) - ∑ i, Real.log (x i * s i) := rfl
  unfold q g1 g2
  rw [hP]
  unfold Phi
  rw [hdot, Real.log_mul hxs.ne' h1β.ne']
  simp_rw [hlog]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have K1 : ρ * (Real.log (x ⬝ᵥ s) + Real.log (1 + β)) =
      ρ * Real.log (x ⬝ᵥ s) + ρ * Real.log (1 + β) := by ring
  have K2 : α * (ρ * ((s ⬝ᵥ dx + x ⬝ᵥ ds) / x ⬝ᵥ s) - (∑ i, dx i / x i + ∑ i, ds i / s i)) =
      ρ * β - α * ∑ i, dx i / x i - α * ∑ i, ds i / s i := by rw [hβdef]; ring
  have K3 : 1 / 2 * α ^ 2 * (1 / (1 - τ) * ((norm2 fun i => dx i / x i) ^ 2 +
      (norm2 fun i => ds i / s i) ^ 2)) =
      1 / 2 * α ^ 2 * (1 / (1 - τ) * (norm2 fun i => dx i / x i) ^ 2) +
      1 / 2 * α ^ 2 * (1 / (1 - τ) * (norm2 fun i => ds i / s i) ^ 2) := by ring
  linarith [A2, A3, E2, E3, hρβ, K1, K2, K3]

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hF : (x, lam, s) ∈ Fo A b c)
    (ρ : ℝ) (hρ : (n : ℝ) < ρ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hdir : IsFeasibleDirection A dx dlam ds)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (α : ℝ) (hα0 : 0 < α)
    (hατ : α * max (normInf (fun i => dx i / x i)) (normInf (fun i => ds i / s i)) ≤ τ) :
    Phi ρ (x + α • dx) (s + α • ds) ≤ q ρ τ x s dx ds α :=
  g69b_eq_4_16 A b c x lam s hF ρ hρ dx dlam ds hdir τ hτ0 hτ1 α hα0 hατ

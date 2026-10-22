-- Prove2me | solution 1 for WrightPDIPM.Potential.corollary_4_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:15:23.079611+00:00
-- url     : https://prove2.me/submissions/65718be1-1f83-4b3c-af2d-8c06eaf8dcf7

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

theorem g69b_rvec_sq {n : ℕ} (ρ : ℝ) (x s : Fin n → ℝ) (i : Fin n) (hw : 0 < x i * s i) :
    rvec ρ x s i ^ 2 = (-(x i * s i) + (n : ℝ) / ρ * mu x s) ^ 2 / (x i * s i) := by
  unfold rvec vvec
  have hv := Real.sqrt_pos.mpr hw
  have hv2 := Real.sq_sqrt hw.le
  set v := Real.sqrt (x i * s i)
  rw [← hv2]
  field_simp
  try ring

theorem g70wr_e426 {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ)
    (hF : (x, lam, s) ∈ Fo A b c) (ρ : ℝ) (hρ : (n : ℝ) < ρ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hdir : IsPRDirection A ρ x s dx dlam ds)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    g2 τ x s dx ds ≤ 1 / (1 - τ) * (norm2 (rvec ρ x s) ^ 2 / vmin x s ^ 2) ∧
      g1 ρ x s dx ds = -(ρ / (n * mu x s)) * norm2 (rvec ρ x s) ^ 2 := by
  obtain ⟨_, _, hx, hs⟩ := hF
  simp only at hx hs
  obtain ⟨⟨hAdx, hAds⟩, h3⟩ := hdir
  have hdxds := g69b_dxds0 A dx dlam ds hAds hAdx
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ0 : 0 < ρ := lt_trans hn' hρ
  have hw : ∀ i, 0 < x i * s i := fun i => mul_pos (hx i) (hs i)
  have hxs : 0 < x ⬝ᵥ s :=
    Finset.sum_pos (fun i _ => hw i) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hmu : 0 < mu x s := div_pos hxs hn'
  have hxsmu : x ⬝ᵥ s = n * mu x s := by unfold mu; field_simp
  set σ := (n : ℝ) / ρ with hσ
  set μ := mu x s
  have hr2 : norm2 (rvec ρ x s) ^ 2 = ∑ i, (-(x i * s i) + σ * μ) ^ 2 / (x i * s i) := by
    unfold norm2
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    exact Finset.sum_congr rfl (fun i _ => g69b_rvec_sq ρ x s i (hw i))
  constructor
  · -- g2 bound
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := vvec x s)
    have hvmin_pos : 0 < vmin x s := by
      unfold vmin; rw [← hj]; exact Real.sqrt_pos.mpr (hw j)
    have hvmin_le : ∀ i, vmin x s ^ 2 ≤ x i * s i := by
      intro i
      have h1 : vmin x s ≤ vvec x s i := ciInf_le (Finite.bddBelow_range _) i
      have h2 : vvec x s i ^ 2 = x i * s i := Real.sq_sqrt (hw i).le
      rw [← h2]
      exact pow_le_pow_left₀ hvmin_pos.le h1 2
    set p : Fin n → ℝ := fun i => dx i ^ 2 * s i / x i + ds i ^ 2 * x i / s i
    have hp0 : ∀ i, 0 ≤ p i := by
      intro i; have := hx i; have := hs i; simp only [p]; positivity
    have hpi : ∀ i, (dx i / x i) ^ 2 + (ds i / s i) ^ 2 = p i / (x i * s i) := by
      intro i
      simp only [p]
      field_simp [(hx i).ne', (hs i).ne']
      try ring
    have hpsum : ∑ i, p i = ∑ i, (-(x i * s i) + σ * μ) ^ 2 / (x i * s i) := by
      have : ∀ i, (-(x i * s i) + σ * μ) ^ 2 / (x i * s i) = p i + 2 * (dx i * ds i) := by
        intro i
        rw [← h3 i]
        simp only [p]
        field_simp [(hx i).ne', (hs i).ne']
        ring
      have hsplit : ∑ i, (-(x i * s i) + σ * μ) ^ 2 / (x i * s i) =
          ∑ i, p i + 2 * (dx ⬝ᵥ ds) := by
        rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
      rw [hsplit, hdxds]; ring
    have hkey : norm2 (fun i => dx i / x i) ^ 2 + norm2 (fun i => ds i / s i) ^ 2 ≤
        norm2 (rvec ρ x s) ^ 2 / vmin x s ^ 2 := by
      unfold norm2
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
      rw [← norm2, hr2, ← hpsum, ← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_le_sum
      intro i _
      rw [hpi]
      exact div_le_div_of_nonneg_left (hp0 i) (by positivity) (hvmin_le i)
    unfold g2
    exact mul_le_mul_of_nonneg_left hkey (le_of_lt (one_div_pos.mpr (by linarith)))
  · -- g1 identity
    have hsum1 : s ⬝ᵥ dx + x ⬝ᵥ ds = -(n * μ) + n * (σ * μ) := by
      have : s ⬝ᵥ dx + x ⬝ᵥ ds = ∑ i, (-(x i * s i) + σ * μ) := by
        unfold dotProduct
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => h3 i)
      rw [this, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← hxsmu]; rfl
    have hsum2 : ∑ i, (dx i / x i + ds i / s i) = ∑ i, (-1 + σ * μ * (1 / (x i * s i))) := by
      apply Finset.sum_congr rfl
      intro i _
      have := h3 i
      field_simp [(hx i).ne', (hs i).ne']
      linear_combination this
    have hsum3 : ∑ i, (-(x i * s i) + σ * μ) ^ 2 / (x i * s i) =
        ∑ i, (x i * s i - 2 * σ * μ + (σ * μ) ^ 2 * (1 / (x i * s i))) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(hx i).ne', (hs i).ne']
      ring
    set S := ∑ i, 1 / (x i * s i)
    have T1 : ∑ i, (-1 + σ * μ * (1 / (x i * s i))) = -(n : ℝ) + σ * μ * S := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have T2 : ∑ i, (x i * s i - 2 * σ * μ + (σ * μ) ^ 2 * (1 / (x i * s i))) =
        n * μ - n * (2 * σ * μ) + (σ * μ) ^ 2 * S := by
      have e : ∑ i, x i * s i = n * μ := hxsmu
      simp only [S, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, e,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold g1
    rw [hr2, hsum1, hsum2, hsum3, hxsmu, T1, T2, hσ]
    field_simp
    ring
theorem g70wr_core45 {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i) (μ : ℝ)
    (hμ0 : 0 < μ) (hμ : ∑ i, v i ^ 2 = n * μ) (ρ : ℝ) (hρ : (n : ℝ) + Real.sqrt n ≤ ρ)
    (i0 : Fin n) :
    3 / 4 * ((n : ℝ) / ρ * μ) ^ 2 / (v i0) ^ 2 ≤ ∑ i, (-v i + (n : ℝ) / ρ * μ / v i) ^ 2 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hρ0 : 0 < ρ := by linarith
  set a := (n : ℝ) / ρ * μ with ha
  set p : Fin n → ℝ := fun i => 1 / v i - v i / μ with hp
  have hpt : ∀ i, (-v i + a / v i) ^ 2 =
      a ^ 2 * p i ^ 2 + 2 * a * (a / μ - 1) * (1 - v i ^ 2 / μ) + (a / μ - 1) ^ 2 * v i ^ 2 := by
    intro i
    have := (hv i).ne'
    simp only [hp]
    field_simp
    ring
  have hsum0 : ∑ i, (1 - v i ^ 2 / μ) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hμ]
    simp
    field_simp
    ring
  have htot : ∑ i, (-v i + a / v i) ^ 2 = a ^ 2 * ∑ i, p i ^ 2 + (a / μ - 1) ^ 2 * (n * μ) := by
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsum0, hμ]
    ring
  rw [htot]
  have hp0 : p i0 ^ 2 ≤ ∑ i, p i ^ 2 :=
    Finset.single_le_sum (f := fun i => p i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i0)
  have hρn : Real.sqrt n ≤ ρ - n := by linarith
  have hρn2 : (n : ℝ) ≤ (ρ - n) ^ 2 := by
    have := mul_le_mul hρn hρn hsq (by linarith)
    rw [Real.mul_self_sqrt hnr.le] at this
    nlinarith
  have hsecond : a ^ 2 / μ ≤ (a / μ - 1) ^ 2 * (n * μ) := by
    have e1 : a / μ - 1 = -(ρ - n) / ρ := by rw [ha]; field_simp; ring
    rw [e1, ha]
    rw [div_pow, div_le_iff₀ hμ0]
    have : ((n : ℝ) / ρ * μ) ^ 2 = n * (n * μ ^ 2 / ρ ^ 2) := by ring
    rw [this]
    have h2 : 0 ≤ n * μ ^ 2 / ρ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hρn2 h2
    calc (n : ℝ) * (n * μ ^ 2 / ρ ^ 2) ≤ (ρ - n) ^ 2 * (n * μ ^ 2 / ρ ^ 2) := this
      _ = (-(ρ - ↑n)) ^ 2 / ρ ^ 2 * (↑n * μ) * μ := by field_simp
  have hm := hv i0
  have hkey : 3 / 4 / v i0 ^ 2 ≤ p i0 ^ 2 + 1 / μ := by
    have : p i0 ^ 2 + 1 / μ - 3 / 4 / v i0 ^ 2 = (1 / (2 * v i0) - v i0 / μ) ^ 2 := by
      simp only [hp]; field_simp; ring
    nlinarith [sq_nonneg (1 / (2 * v i0) - v i0 / μ)]
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  calc 3 / 4 * a ^ 2 / v i0 ^ 2 = a ^ 2 * (3 / 4 / v i0 ^ 2) := by ring
    _ ≤ a ^ 2 * (p i0 ^ 2 + 1 / μ) := mul_le_mul_of_nonneg_left hkey ha2
    _ = a ^ 2 * p i0 ^ 2 + a ^ 2 / μ := by ring
    _ ≤ a ^ 2 * ∑ i, p i ^ 2 + (a / μ - 1) ^ 2 * (n * μ) := by
        have := mul_le_mul_of_nonneg_left hp0 ha2
        linarith


/-- **Lemma 4.5** (Wright, p. 75). For any `(x, λ, s) ∈ F°` and for `ρ > n + √n`,
`‖r‖ ≥ (√3/(2v_min)) · (nμ/ρ)` (4.28), with `v_min`, `r` from (4.20) and `μ = xᵀs/n`
(`n ≥ 1`). -/
theorem g70wr_l45 {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ)
    (hF : (x, lam, s) ∈ Fo A b c) (ρ : ℝ) (hρ : (n : ℝ) + Real.sqrt n ≤ ρ) :
    Real.sqrt 3 / (2 * vmin x s) * (n * mu x s / ρ) ≤ norm2 (rvec ρ x s) := by
  obtain ⟨hA, hd, hx, hs⟩ := hF
  have hv : ∀ i, 0 < vvec x s i := fun i => Real.sqrt_pos.mpr (mul_pos (hx i) (hs i))
  have hv2 : ∀ i, vvec x s i ^ 2 = x i * s i := fun i =>
    Real.sq_sqrt (mul_pos (hx i) (hs i)).le
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hμ : ∑ i, vvec x s i ^ 2 = n * mu x s := by
    simp only [hv2, mu]; field_simp; rfl
  have hμ0 : 0 < mu x s := by
    unfold mu
    apply div_pos _ hnr
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Finset.sum_pos (fun i _ => mul_pos (hx i) (hs i)) Finset.univ_nonempty
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i0, hi0⟩ := exists_eq_ciInf_of_finite (f := vvec x s)
  have hvm : vmin x s = vvec x s i0 := by rw [vmin, hi0]
  have core := g70wr_core45 hn (vvec x s) hv (mu x s) hμ0 hμ ρ hρ i0
  apply Real.le_sqrt_of_sq_le
  rw [hvm]
  have hm := hv i0
  have e : (Real.sqrt 3 / (2 * vvec x s i0) * (n * mu x s / ρ)) ^ 2 =
      3 / 4 * ((n : ℝ) / ρ * mu x s) ^ 2 / (vvec x s i0) ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    field_simp
    ring
  rw [e]
  refine core.trans (le_of_eq ?_)
  rfl


theorem g70wr_ii {n : ℕ} (hn : 0 < n) (x s : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i)
    (ρ : ℝ) (hρ : (n : ℝ) < ρ) : mu x s ≤ Real.exp (Phi ρ x s / (ρ - n)) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hxs : 0 < x ⬝ᵥ s := Finset.sum_pos (fun i _ => mul_pos (hx i) (hs i)) Finset.univ_nonempty
  have hμ : 0 < mu x s := div_pos hxs hnr
  have hsum : ∑ i, Real.log (x i * s i) ≤ n * Real.log (mu x s) := by
    have h1 : ∀ i, Real.log (x i * s i) - Real.log (mu x s) ≤ x i * s i / mu x s - 1 := fun i => by
      rw [← Real.log_div (mul_pos (hx i) (hs i)).ne' hμ.ne']
      exact Real.log_le_sub_one_of_pos (div_pos (mul_pos (hx i) (hs i)) hμ)
    have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h1 i)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div] at h2
    have h3 : (∑ i, x i * s i) / mu x s = n := by
      rw [mu, dotProduct]; field_simp; exact div_self (ne_of_gt (by simpa [dotProduct] using hxs))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h2
    rw [h3] at h2
    linarith
  have hlogxs : Real.log (mu x s) ≤ Real.log (x ⬝ᵥ s) := by
    apply Real.log_le_log hμ
    rw [mu, div_le_iff₀ hnr]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [← Real.log_le_iff_le_exp hμ, le_div_iff₀ (by linarith), Phi]
  have : 0 ≤ ρ := by linarith
  have := mul_le_mul_of_nonneg_left hlogxs this
  nlinarith


theorem g70wr_rlow {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i) (μ : ℝ)
    (hμ0 : 0 < μ) (hμ : ∑ i, v i ^ 2 = n * μ) (ρ : ℝ) (hρ0 : 0 < ρ) :
    n * μ * (1 - n / ρ) ^ 2 ≤ ∑ i, (-v i + (n : ℝ) / ρ * μ / v i) ^ 2 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set a := (n : ℝ) / ρ * μ with ha
  set p : Fin n → ℝ := fun i => 1 / v i - v i / μ with hp
  have hpt : ∀ i, (-v i + a / v i) ^ 2 =
      a ^ 2 * p i ^ 2 + 2 * a * (a / μ - 1) * (1 - v i ^ 2 / μ) + (a / μ - 1) ^ 2 * v i ^ 2 := by
    intro i
    have := (hv i).ne'
    simp only [hp]
    field_simp
    ring
  have hsum0 : ∑ i, (1 - v i ^ 2 / μ) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hμ]
    simp
    field_simp
    ring
  have htot : ∑ i, (-v i + a / v i) ^ 2 = a ^ 2 * ∑ i, p i ^ 2 + (a / μ - 1) ^ 2 * (n * μ) := by
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsum0, hμ]
    ring
  rw [htot]
  have e : a / μ - 1 = -(1 - n / ρ) := by rw [ha]; field_simp; ring
  rw [e]
  have : 0 ≤ a ^ 2 * ∑ i, p i ^ 2 :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  nlinarith

set_option maxHeartbeats 1000000 in
theorem g70wr_step {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (ρ : ℝ) (hρ : (n : ℝ) + Real.sqrt n ≤ ρ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hF : (x, lam, s) ∈ Fo A b c)
    (x' : Fin n → ℝ) (lam' : Fin m → ℝ) (s' : Fin n → ℝ)
    (hPR : IsPRStep A ρ x lam s x' lam' s') :
    (x', lam', s') ∈ Fo A b c ∧ Phi ρ x' s' ≤ Phi ρ x s - 15 / 100 := by
  obtain ⟨dx, dlam, ds, hdir, α, hαI, hmin, rfl, rfl, rfl⟩ := hPR
  have hF' := hF
  obtain ⟨hA, hd, hx, hs⟩ := hF
  simp only at hA hd hx hs
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnr
  have hρn : (n : ℝ) < ρ := by linarith
  have hρ0 : 0 < ρ := by linarith
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hw : ∀ i, 0 < x i * s i := fun i => mul_pos (hx i) (hs i)
  have hxs : 0 < x ⬝ᵥ s := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  have hμ : 0 < mu x s := div_pos hxs hnr
  obtain ⟨j0, hj0⟩ := exists_eq_ciInf_of_finite (f := vvec x s)
  have hvpos : ∀ i, 0 < vvec x s i := fun i => Real.sqrt_pos.mpr (hw i)
  have hvm : vmin x s = vvec x s j0 := by rw [vmin, hj0]
  have hvm0 : 0 < vmin x s := by rw [hvm]; exact hvpos j0
  set V := vmin x s with hV
  set R := norm2 (rvec ρ x s) with hR
  set μ := mu x s with hμdef
  have h45 := g70wr_l45 hn A b c x lam s hF' ρ hρ
  simp only [← hV, ← hR, ← hμdef] at h45
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) h45
  -- g2 / g1
  obtain ⟨hg2, hg1⟩ := g70wr_e426 hn A b c x lam s hF' ρ hρn dx dlam ds hdir (1 / 2)
    (by norm_num) (by norm_num)
  simp only [← hV, ← hR, ← hμdef] at hg2 hg1
  have hSb : norm2 (fun i => dx i / x i) ^ 2 + norm2 (fun i => ds i / s i) ^ 2 ≤ (R / V) ^ 2 := by
    unfold g2 at hg2
    rw [div_pow]
    have : (1 : ℝ) / (1 - 1 / 2) = 2 := by norm_num
    rw [this] at hg2
    linarith
  have hsq_term : ∀ (f : Fin n → ℝ) (i : Fin n), f i ^ 2 ≤ norm2 f ^ 2 := fun f i => by
    unfold norm2
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    exact Finset.single_le_sum (f := fun i => f i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
  have hRV : 0 ≤ R / V := (div_pos hRpos hvm0).le
  have habs : ∀ (t : ℝ), t ^ 2 ≤ (R / V) ^ 2 → |t| ≤ R / V := fun t ht => by
    have := Real.sqrt_le_sqrt ht
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hRV] at this
  have hdxb : ∀ i, |dx i / x i| ≤ R / V := fun i => habs _ (by
    have h1 := hsq_term (fun i => dx i / x i) i
    have h2 := sq_nonneg (norm2 (fun i => ds i / s i))
    linarith)
  have hdsb : ∀ i, |ds i / s i| ≤ R / V := fun i => habs _ (by
    have h1 := hsq_term (fun i => ds i / s i) i
    have h2 := sq_nonneg (norm2 (fun i => dx i / x i))
    linarith)
  have hinfx : normInf (fun i => dx i / x i) ≤ R / V := ciSup_le hdxb
  have hinfs : normInf (fun i => ds i / s i) ≤ R / V := ciSup_le hdsb
  -- R ≥ V/2
  have hv2 : ∀ i, vvec x s i ^ 2 = x i * s i := fun i => Real.sq_sqrt (hw i).le
  have hsumv : ∑ i, vvec x s i ^ 2 = n * μ := by
    simp only [hv2, hμdef, mu]; field_simp; rfl
  have hrl := g70wr_rlow hn (vvec x s) hvpos μ hμ hsumv ρ hρ0
  have hR2 : R ^ 2 = ∑ i, (-vvec x s i + (n : ℝ) / ρ * μ / vvec x s i) ^ 2 := by
    rw [hR, norm2, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]; rfl
  have hVle : ∀ i, V ≤ vvec x s i := fun i => by rw [hV, vmin]; exact ciInf_le (Finite.bddBelow_range _) i
  have hV2 : V ^ 2 ≤ μ := by
    have h1 : ∀ i, V ^ 2 ≤ x i * s i := fun i => by
      rw [← hv2]; exact pow_le_pow_left₀ hvm0.le (hVle i) 2
    have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h1 i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    have h3 : ∑ i, x i * s i = n * μ := by rw [← hsumv]; simp [hv2]
    rw [h3] at h2
    nlinarith
  have hquart : μ / 4 ≤ n * μ * (1 - n / ρ) ^ 2 := by
    set r := Real.sqrt n with hr
    have hr2 : r * r = n := Real.mul_self_sqrt hnr.le
    have hr1 : 1 ≤ r := by
      rw [hr, show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    set d := ρ - n with hd'
    have hdr : r ≤ d := by linarith
    have e : 1 - n / ρ = d / ρ := by rw [hd']; field_simp
    have k1 := mul_le_mul_of_nonneg_right hdr (show (0 : ℝ) ≤ 2 * r - 1 by linarith)
    have h3 : 0 ≤ r * (r - 1) := mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ 2 * r * d - r * r - d := by linarith
    have k3 : 0 ≤ 2 * r * d + r * r + d := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ r) (by linarith : (0:ℝ) ≤ d); linarith
    have k4 : (r * r + d) ^ 2 ≤ 4 * (r * r) * d ^ 2 := by
      have e2 : 4 * (r * r) * d ^ 2 - (r * r + d) ^ 2 =
          (2 * r * d - r * r - d) * (2 * r * d + r * r + d) := by ring
      have := mul_nonneg k2 k3
      linarith
    rw [hr2] at k4
    have hρd : ρ = n + d := by rw [hd']; ring
    rw [← hρd] at k4
    rw [e, div_pow, show (n : ℝ) * μ * (d ^ 2 / ρ ^ 2) = μ * (n * d ^ 2) / ρ ^ 2 by ring,
      le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left k4 hμ.le
    linarith
  have hRV2 : V / 2 ≤ R := by nlinarith
  -- step
  set ab := V / (2 * R) with hab
  set α0 := 9 / 10 * ab with hα0
  have hab0 : 0 < ab := div_pos hvm0 (by linarith)
  have hab1 : ab ≤ 1 := by rw [hab, div_le_one (by linarith)]; linarith
  have habR : ab * (R / V) = 1 / 2 := by rw [hab]; field_simp
  have hmem : ab ∈ {a : ℝ | 0 ≤ a ∧ a ≤ 1 ∧ ∀ i, 0 ≤ x i + a * dx i ∧ 0 ≤ s i + a * ds i} := by
    refine ⟨hab0.le, hab1, fun i => ⟨?_, ?_⟩⟩
    · have h1 := (abs_le.mp (hdxb i)).1
      have h2 : -(1 / 2) ≤ ab * (dx i / x i) := by
        have := mul_le_mul_of_nonneg_left h1 hab0.le; linarith
      have e : x i + ab * dx i = x i * (1 + ab * (dx i / x i)) := by
        have hxi := (hx i).ne'
        field_simp
      rw [e]; exact mul_nonneg (hx i).le (by linarith)
    · have h1 := (abs_le.mp (hdsb i)).1
      have h2 : -(1 / 2) ≤ ab * (ds i / s i) := by
        have := mul_le_mul_of_nonneg_left h1 hab0.le; linarith
      have e : s i + ab * ds i = s i * (1 + ab * (ds i / s i)) := by
        have hsi := (hs i).ne'
        field_simp
      rw [e]; exact mul_nonneg (hs i).le (by linarith)
  have hamax : ab ≤ alphaMax x s dx ds := le_csSup ⟨1, fun a ha => ha.2.1⟩ hmem
  have hα0I : α0 ∈ Set.Ioo 0 (alphaMax x s dx ds) := ⟨by positivity, by linarith⟩
  have hατ : α0 * max (normInf (fun i => dx i / x i)) (normInf (fun i => ds i / s i)) ≤ 1 / 2 := by
    have : max (normInf (fun i => dx i / x i)) (normInf (fun i => ds i / s i)) ≤ R / V :=
      max_le hinfx hinfs
    have h := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ α0)
    have : α0 * (R / V) = 9 / 20 := by rw [hα0, mul_assoc, habR]; norm_num
    linarith
  have h416 := g69b_eq_4_16 A b c x lam s hF' ρ hρn dx dlam ds hdir.1 (1 / 2) (by norm_num)
    (by norm_num) α0 (by positivity) hατ
  have hq : q ρ (1 / 2) x s dx ds α0 ≤ Phi ρ x s - 15 / 100 := by
    unfold q
    rw [hg1]
    have hg2' : g2 (1 / 2) x s dx ds ≤ 2 * (R / V) ^ 2 := by
      have : (1 : ℝ) / (1 - 1 / 2) = 2 := by norm_num
      rw [this, ← div_pow] at hg2; exact hg2
    have t2 : 1 / 2 * α0 ^ 2 * g2 (1 / 2) x s dx ds ≤ 81 / 400 := by
      have h := mul_le_mul_of_nonneg_left hg2' (by positivity : (0 : ℝ) ≤ 1 / 2 * α0 ^ 2)
      have : 1 / 2 * α0 ^ 2 * (2 * (R / V) ^ 2) = (α0 * (R / V)) ^ 2 := by ring
      have h2 : α0 * (R / V) = 9 / 20 := by rw [hα0, mul_assoc, habR]; norm_num
      rw [this, h2] at h; linarith
    have hW : Real.sqrt 3 / 2 ≤ V * R * ρ / (n * μ) := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left h45 (by positivity : (0 : ℝ) ≤ V * ρ)
      have e : V * ρ * (Real.sqrt 3 / (2 * V) * (n * μ / ρ)) = Real.sqrt 3 / 2 * (n * μ) := by
        field_simp
      linarith
    have t1 : α0 * (-(ρ / (n * μ)) * R ^ 2) = -(9 / 20) * (V * R * ρ / (n * μ)) := by
      have h1 := hRpos.ne'
      have h2 := hvm0.ne'
      have h3 : (n : ℝ) * μ ≠ 0 := by positivity
      rw [hα0, hab]; field_simp; ring
    have hs3 : (17 : ℝ) / 10 ≤ Real.sqrt 3 := by
      rw [show (17 : ℝ) / 10 = Real.sqrt ((17 / 10) ^ 2) by rw [Real.sqrt_sq]; norm_num]
      exact Real.sqrt_le_sqrt (by norm_num)
    rw [t1]
    have : (9 / 20 : ℝ) * (17 / 10 / 2) ≤ 9 / 20 * (V * R * ρ / (n * μ)) := by linarith
    linarith
  have hstep : Phi ρ (x + α • dx) (s + α • ds) ≤ Phi ρ (x + α0 • dx) (s + α0 • ds) :=
    (isMinOn_iff.mp hmin) α0 hα0I
  refine ⟨?_, by linarith⟩
  -- feasibility of the new point
  obtain ⟨hα0', hαm⟩ := hαI
  have hne : ({a : ℝ | 0 ≤ a ∧ a ≤ 1 ∧ ∀ i, 0 ≤ x i + a * dx i ∧ 0 ≤ s i + a * ds i}).Nonempty :=
    ⟨0, le_rfl, zero_le_one, fun i => by simp [(hx i).le, (hs i).le]⟩
  unfold alphaMax at hαm
  obtain ⟨β, hβ, hαβ⟩ := exists_lt_of_lt_csSup hne hαm
  obtain ⟨⟨hAdx, hAds⟩, -⟩ := hdir
  refine ⟨?_, ?_, fun i => ?_, fun i => ?_⟩
  · simp only; rw [mulVec_add, mulVec_smul, hA, hAdx, smul_zero, add_zero]
  · simp only
    rw [mulVec_add, mulVec_smul]
    calc Aᵀ *ᵥ lam + α • (Aᵀ *ᵥ dlam) + (s + α • ds) = (Aᵀ *ᵥ lam + s) + α • (Aᵀ *ᵥ dlam + ds) := by
          rw [smul_add]; abel
      _ = c := by rw [hd, hAds, smul_zero, add_zero]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := (hβ.2.2 i).1
    rcases le_or_gt 0 (dx i) with h | h
    · have := mul_nonneg hα0'.le h; linarith [hx i]
    · have : β * dx i < α * dx i := mul_lt_mul_of_neg_right hαβ h
      linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := (hβ.2.2 i).2
    rcases le_or_gt 0 (ds i) with h | h
    · have := mul_nonneg hα0'.le h; linarith [hs i]
    · have : β * ds i < α * ds i := mul_lt_mul_of_neg_right hαβ h
      linarith


/-- **Corollary 4.7** (Wright, pp. 77–78). Fix `ρ ≥ n + √n` (`n ≥ 1`) and `ε > 0`, and let
`(xᵏ, λᵏ, sᵏ)` be the iterates of Algorithm PR (p. 67) from an initial point
`(x⁰, λ⁰, s⁰) ∈ F°` with `Φ_ρ(x⁰, s⁰) ≤ κ(ρ − n)|log ε|` for some `κ > 0`. Then the index
`K = ⌈((κ + 1)/0.15)(ρ − n)|log ε|⌉` (4.32) has the property that `(xᵏ, λᵏ, sᵏ) ∈ F°` and
`μ_k ≤ ε` for all `k ≥ K`. Each iteration is `IsPRStep`: the direction of (1.13) with
`σ_k = n/ρ` and a step length `α_k` minimizing `Φ_ρ` along it over `(0, α_max)` (4.6). -/
theorem solution {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (ρ : ℝ) (hρ : (n : ℝ) + Real.sqrt n ≤ ρ) (ε : ℝ) (hε : 0 < ε)
    (κ : ℝ) (hκ : 0 < κ)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ)
    (h0 : (x 0, lam 0, s 0) ∈ Fo A b c)
    (hPR : ∀ k, IsPRStep A ρ (x k) (lam k) (s k) (x (k + 1)) (lam (k + 1)) (s (k + 1)))
    (hΦ0 : Phi ρ (x 0) (s 0) ≤ κ * (ρ - n) * |Real.log ε|) :
    ∀ k : ℕ, ⌈(κ + 1) / (15 / 100) * (ρ - n) * |Real.log ε|⌉ ≤ (k : ℤ) →
      (x k, lam k, s k) ∈ Fo A b c ∧ mu (x k) (s k) ≤ ε := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hρn : (n : ℝ) < ρ := by have := Real.sqrt_pos.mpr hnr; linarith
  have hall : ∀ k : ℕ, (x k, lam k, s k) ∈ Fo A b c ∧
      Phi ρ (x k) (s k) ≤ Phi ρ (x 0) (s 0) - 15 / 100 * k := by
    intro k
    induction k with
    | zero => exact ⟨h0, by simp⟩
    | succ k ih =>
      obtain ⟨h1, h2⟩ := g70wr_step hn A b c ρ hρ (x k) (lam k) (s k) ih.1 _ _ _ (hPR k)
      refine ⟨h1, ?_⟩
      push_cast
      linarith [ih.2]
  intro k hk
  obtain ⟨hFk, hΦk⟩ := hall k
  refine ⟨hFk, ?_⟩
  have hmu := g70wr_ii hn (x k) (s k) hFk.2.2.1 hFk.2.2.2 ρ hρn
  refine hmu.trans ?_
  have hk' : (κ + 1) / (15 / 100) * (ρ - n) * |Real.log ε| ≤ (k : ℝ) := by
    have := Int.ceil_le.mp hk
    exact_mod_cast this
  set L := |Real.log ε| with hL
  have hL0 : 0 ≤ L := abs_nonneg _
  have hpos : 0 < ρ - n := by linarith
  have h1 : (κ + 1) * (ρ - n) * L ≤ 15 / 100 * k := by
    have e : (κ + 1) / (15 / 100) * (ρ - n) * L = (κ + 1) * (ρ - n) * L / (15 / 100) := by ring
    rw [e, div_le_iff₀ (by norm_num)] at hk'
    linarith
  have h2 : Phi ρ (x k) (s k) ≤ -((ρ - n) * L) := by nlinarith
  have h3 : Phi ρ (x k) (s k) / (ρ - n) ≤ Real.log ε := by
    rw [div_le_iff₀ hpos]
    have : -L ≤ Real.log ε := by rw [hL]; exact neg_abs_le _
    nlinarith
  calc Real.exp (Phi ρ (x k) (s k) / (ρ - n)) ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr h3
    _ = ε := Real.exp_log hε



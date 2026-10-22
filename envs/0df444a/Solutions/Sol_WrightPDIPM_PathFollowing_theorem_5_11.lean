-- Prove2me | solution 1 for WrightPDIPM.PathFollowing.theorem_5_11
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:57:25.553338+00:00
-- url     : https://prove2.me/submissions/941b1662-0e23-4d76-a1ca-8ffae7cbdb0e

import Mathlib
import Definitions.Def_WrightPDIPM_PathFollowing_Setup
open WrightPDIPM.PathFollowing

open Matrix

theorem g69b_pf_dxds {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (h1 : Aᵀ *ᵥ dlam + ds = 0) (h2 : A *ᵥ dx = 0) : dx ⬝ᵥ ds = 0 := by
  have : ds = -(Aᵀ *ᵥ dlam) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h1
  rw [this, dotProduct_neg, dotProduct_mulVec, vecMul_transpose, h2]
  simp

theorem g69b_pf_sum {n : ℕ} (x s dx ds : Fin n → ℝ) (σ : ℝ)
    (h3 : ∀ i, s i * dx i + x i * ds i = -(x i * s i) + σ * mu x s) :
    s ⬝ᵥ dx + x ⬝ᵥ ds = -(x ⬝ᵥ s) + σ * (x ⬝ᵥ s) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [dotProduct]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have : s ⬝ᵥ dx + x ⬝ᵥ ds = ∑ i, (-(x i * s i) + σ * mu x s) := by
    unfold dotProduct
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => h3 i)
  rw [this, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold mu
  unfold dotProduct
  field_simp

theorem g69b_pf_mu_alpha {n : ℕ} (x s dx ds : Fin n → ℝ) (σ : ℝ)
    (h0 : dx ⬝ᵥ ds = 0)
    (h3 : ∀ i, s i * dx i + x i * ds i = -(x i * s i) + σ * mu x s) (α : ℝ) :
    mu (x + α • dx) (s + α • ds) = (1 - α * (1 - σ)) * mu x s := by
  have hs := g69b_pf_sum x s dx ds σ h3
  have : (x + α • dx) ⬝ᵥ (s + α • ds) = (1 - α * (1 - σ)) * (x ⬝ᵥ s) := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [h0, dotProduct_comm dx s]
    linear_combination α * hs
  unfold mu
  rw [this, mul_div_assoc]

theorem g69b_rpow_sq : ((2 : ℝ) ^ (-((3 : ℝ) / 2))) ^ 2 = 1 / 8 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem g69b_uv_sumsq {n : ℕ} (u v : Fin n → ℝ) (huv : 0 ≤ u ⬝ᵥ v) :
    ∑ i, (u i * v i) ^ 2 ≤ (∑ i, (u + v) i ^ 2) ^ 2 / 8 := by
  set p : Fin n → ℝ := fun i => max (u i * v i) 0
  set q : Fin n → ℝ := fun i => max (-(u i * v i)) 0
  have hp0 : ∀ i, 0 ≤ p i := fun i => le_max_right _ _
  have hq0 : ∀ i, 0 ≤ q i := fun i => le_max_right _ _
  have hsq : ∀ i, (u i * v i) ^ 2 = p i ^ 2 + q i ^ 2 := by
    intro i
    simp only [p, q]
    rcases le_total 0 (u i * v i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hpq : ∀ i, u i * v i = p i - q i := by
    intro i
    simp only [p, q]
    rcases le_total 0 (u i * v i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  set P := ∑ i, p i
  set Q := ∑ i, q i
  have hQP : Q ≤ P := by
    have : u ⬝ᵥ v = P - Q := by
      unfold dotProduct
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hpq i)
    linarith
  have hP2 : ∑ i, p i ^ 2 ≤ P * P := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have : p i ≤ P := Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
    nlinarith [hp0 i]
  have hQ2 : ∑ i, q i ^ 2 ≤ Q * Q := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have : q i ≤ Q := Finset.single_le_sum (fun j _ => hq0 j) (Finset.mem_univ i)
    nlinarith [hq0 i]
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun j _ => hq0 j)
  have hPS : P ≤ (∑ i, (u + v) i ^ 2) / 4 := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    simp only [p, Pi.add_apply]
    apply max_le
    · nlinarith [sq_nonneg (u i - v i)]
    · positivity
  have hsum : ∑ i, (u i * v i) ^ 2 = ∑ i, p i ^ 2 + ∑ i, q i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hsq i)
  rw [hsum]
  have hP0 : 0 ≤ P := Finset.sum_nonneg (fun j _ => hp0 j)
  have : Q * Q ≤ P * P := mul_le_mul hQP hQP hQ0 hP0
  have : P * P ≤ ((∑ i, (u + v) i ^ 2) / 4) * ((∑ i, (u + v) i ^ 2) / 4) :=
    mul_le_mul hPS hPS hP0 (le_trans hP0 hPS)
  nlinarith

theorem g69b_lemma_5_3 {n : ℕ} (u v : Fin n → ℝ) (huv : 0 ≤ u ⬝ᵥ v) :
    norm2 (fun i => u i * v i) ≤ (2 : ℝ) ^ (-((3 : ℝ) / 2)) * norm2 (u + v) ^ 2 := by
  unfold norm2
  have hS : 0 ≤ ∑ i, (u + v) i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [Real.sq_sqrt hS]
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · rw [mul_pow, g69b_rpow_sq]
    have := g69b_uv_sumsq u v huv
    linarith

theorem g69b_abs_le_norm2 {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : |v i| ≤ norm2 v := by
  unfold norm2
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem g69b_pf_scaled {n : ℕ} (x s dx ds r : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hs : ∀ i, 0 < s i) (h0 : dx ⬝ᵥ ds = 0) (h3 : ∀ i, s i * dx i + x i * ds i = r i) :
    norm2 (fun i => dx i * ds i) ≤
      (2 : ℝ) ^ (-((3 : ℝ) / 2)) * ∑ i, r i ^ 2 / (x i * s i) := by
  set u : Fin n → ℝ := fun i => dx i * Real.sqrt (s i) / Real.sqrt (x i)
  set v : Fin n → ℝ := fun i => ds i * Real.sqrt (x i) / Real.sqrt (s i)
  have hpx : ∀ i, 0 < Real.sqrt (x i) := fun i => Real.sqrt_pos.mpr (hx i)
  have hps : ∀ i, 0 < Real.sqrt (s i) := fun i => Real.sqrt_pos.mpr (hs i)
  have huv : ∀ i, u i * v i = dx i * ds i := by
    intro i
    simp only [u, v]
    field_simp [(hpx i).ne', (hps i).ne']
  have hdot : 0 ≤ u ⬝ᵥ v := by
    have : u ⬝ᵥ v = dx ⬝ᵥ ds := by
      unfold dotProduct; exact Finset.sum_congr rfl (fun i _ => huv i)
    rw [this, h0]
  have hsq : ∀ i, (u + v) i ^ 2 = r i ^ 2 / (x i * s i) := by
    intro i
    have e : (u + v) i = r i / (Real.sqrt (x i) * Real.sqrt (s i)) := by
      simp only [Pi.add_apply, u, v]
      rw [← h3 i]
      field_simp [(hpx i).ne', (hps i).ne']
      simp only [Real.sq_sqrt (hx i).le, Real.sq_sqrt (hs i).le]
      ring
    rw [e, div_pow, mul_pow, Real.sq_sqrt (hx i).le, Real.sq_sqrt (hs i).le]
  have h53 := g69b_lemma_5_3 u v hdot
  have e1 : (fun i => u i * v i) = (fun i => dx i * ds i) := funext huv
  rw [e1] at h53
  have e2 : norm2 (u + v) ^ 2 = ∑ i, r i ^ 2 / (x i * s i) := by
    unfold norm2
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    exact Finset.sum_congr rfl (fun i _ => hsq i)
  rwa [e2] at h53

theorem g69b_dot_pos {n : ℕ} (hn : 0 < n) (x s : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hs : ∀ i, 0 < s i) : 0 < mu x s := by
  unfold mu
  apply div_pos _ (by exact_mod_cast hn)
  unfold dotProduct
  exact Finset.sum_pos (fun i _ => mul_pos (hx i) (hs i)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem g69b_sum_w {n : ℕ} (hn : 0 < n) (x s : Fin n → ℝ) :
    ∑ i, x i * s i = n * mu x s := by
  unfold mu
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp
  rfl
theorem g69b_lemma_5_10 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ σ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hN : (x, lam, s) ∈ NegInf A b c γ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hstep : IsStep A x s σ dx dlam ds) :
    norm2 (fun i => dx i * ds i) ≤
      (2 : ℝ) ^ (-((3 : ℝ) / 2)) * (1 + 1 / γ) * (n : ℝ) * mu x s := by
  obtain ⟨⟨_, _, hx, hs⟩, hw⟩ := hN
  simp only at hx hs hw
  obtain ⟨h1, h2, h3⟩ := hstep
  have h0 := g69b_pf_dxds A dx dlam ds h1 h2
  have hsc := g69b_pf_scaled x s dx ds (fun i => -(x i * s i) + σ * mu x s) hx hs h0 h3
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [norm2]
  have hmu := g69b_dot_pos hn x s hx hs
  have hterm : ∀ i, (-(x i * s i) + σ * mu x s) ^ 2 / (x i * s i) ≤ x i * s i + mu x s / γ := by
    intro i
    have hwi : 0 < x i * s i := mul_pos (hx i) (hs i)
    rw [div_le_iff₀ hwi]
    have hg := hw i
    have e : mu x s / γ * (x i * s i) ≥ mu x s * mu x s := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hγ0]
      nlinarith
    have : σ ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hσ0 hmu.le) hwi.le, mul_nonneg (sq_nonneg (mu x s)) (by linarith : 0 ≤ 1 - σ ^ 2)]
  have hS : ∑ i, (-(x i * s i) + σ * mu x s) ^ 2 / (x i * s i) ≤ (1 + 1 / γ) * n * mu x s := by
    calc _ ≤ ∑ i, (x i * s i + mu x s / γ) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (1 + 1 / γ) * n * mu x s := by
        rw [Finset.sum_add_distrib, g69b_sum_w hn x s]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  calc _ ≤ _ := hsc
    _ ≤ (2 : ℝ) ^ (-((3 : ℝ) / 2)) * ((1 + 1 / γ) * n * mu x s) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by ring

theorem g69b_pos_of_path (a da b db : ℝ) (ha : 0 < a)
    (hf : ∀ α : ℝ, 0 ≤ α → α ≤ 1 → 0 < (a + α * da) * (b + α * db)) : 0 < a + da := by
  by_contra h
  push_neg at h
  have hda : da < 0 := by linarith
  set α0 := a / (-da)
  have h0 : 0 ≤ α0 := div_nonneg ha.le (by linarith)
  have h1 : α0 ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hne : da ≠ 0 := hda.ne
  have hz : a + α0 * da = 0 := by simp only [α0]; field_simp; ring
  have := hf α0 h0 h1
  rw [hz, zero_mul] at this
  exact lt_irrefl _ this

theorem g69b_sig_min (σmin σmax σ : ℝ) (h1 : σmin ≤ σ) (h2 : σ ≤ σmax) :
    min (σmin * (1 - σmin)) (σmax * (1 - σmax)) ≤ σ * (1 - σ) := by
  rcases le_total (σ + σmin) 1 with h | h
  · exact le_trans (min_le_left _ _) (by nlinarith)
  · exact le_trans (min_le_right _ _) (by nlinarith)

theorem solution (γ σmin σmax : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hσmin : 0 < σmin) (hσ : σmin < σmax) (hσmax : σmax < 1)
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ)
    (hLPF : IsLPFIterates A b c γ σmin σmax x lam s σ α dx dlam ds) :
    ∀ k : ℕ, mu (x (k + 1)) (s (k + 1)) ≤
      (1 - (2 : ℝ) ^ ((3 : ℝ) / 2) * γ * ((1 - γ) / (1 + γ)) *
          min (σmin * (1 - σmin)) (σmax * (1 - σmax)) / (n : ℝ)) * mu (x k) (s k) := by
  intro k
  have hNk : (x k, lam k, s k) ∈ NegInf A b c γ := by
    cases k with
    | zero => exact hLPF.start
    | succ k' =>
      have := (hLPF.alpha_greatest k').1.2
      rw [hLPF.update_x k', hLPF.update_lam k', hLPF.update_s k']
      exact this
  have hσk := hLPF.sigma_mem k
  set σk := σ k with hσkdef
  have hσk0 : 0 < σk := lt_of_lt_of_le hσmin hσk.1
  have hσk1 : σk < 1 := lt_of_le_of_lt hσk.2 hσmax
  have hstep := hLPF.step k
  have h510 := g69b_lemma_5_10 A b c γ σk hγ0 hγ1 hσk0.le hσk1.le (x k) (lam k) (s k) hNk
    (dx k) (dlam k) (ds k) hstep
  obtain ⟨⟨hAx, hAs, hx, hs⟩, hw⟩ := hNk
  simp only at hAx hAs hx hs hw
  obtain ⟨h1, h2, h3⟩ := hstep
  have h0 := g69b_pf_dxds A (dx k) (dlam k) (ds k) h1 h2
  have hmua := g69b_pf_mu_alpha (x k) (s k) (dx k) (ds k) σk h0 h3
  have hupd : mu (x (k + 1)) (s (k + 1)) = (1 - α k * (1 - σk)) * mu (x k) (s k) := by
    rw [hLPF.update_x k, hLPF.update_s k, hmua]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [mu]
  have hmu := g69b_dot_pos hn (x k) (s k) hx hs
  set μ := mu (x k) (s k) with hμdef
  set C : ℝ := (2 : ℝ) ^ ((3 : ℝ) / 2) with hCdef
  set cc : ℝ := (2 : ℝ) ^ (-((3 : ℝ) / 2)) with hccdef
  have hC0 : 0 < C := by positivity
  have hcC : cc = C⁻¹ := by rw [hccdef, hCdef, Real.rpow_neg (by norm_num)]
  have hC4 : C ≤ 4 := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (show (3 : ℝ) / 2 ≤ 2 by norm_num)
    rw [hCdef]; norm_num at this ⊢; linarith
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set B : ℝ := cc * (1 + 1 / γ) * n with hBdef
  set ab : ℝ := C * γ * ((1 - γ) / (1 + γ)) * σk / n with habdef
  have hab0 : 0 ≤ ab := by
    rw [habdef]; apply div_nonneg _ (by linarith)
    apply mul_nonneg _ hσk0.le
    apply mul_nonneg (mul_nonneg hC0.le hγ0.le)
    apply div_nonneg (by linarith) (by linarith)
  have hid : B * ab = σk * (1 - γ) := by
    rw [hBdef, habdef, hcC]
    field_simp
    ring
  have hab1 : ab ≤ 1 := by
    rw [habdef, div_le_one (by linarith)]
    have e1 : γ * ((1 - γ) / (1 + γ)) ≤ 1 / 4 := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg (γ - 1 / 2)]
    have e2 : 0 ≤ γ * ((1 - γ) / (1 + γ)) := mul_nonneg hγ0.le (div_nonneg (by linarith) (by linarith))
    calc C * γ * ((1 - γ) / (1 + γ)) * σk = C * (γ * ((1 - γ) / (1 + γ))) * σk := by ring
      _ ≤ 4 * (1 / 4) * 1 := by
          apply mul_le_mul _ hσk1.le hσk0.le (by positivity)
          exact mul_le_mul hC4 e1 e2 (by norm_num)
      _ ≤ n := by linarith
  have hN : norm2 (fun i => dx k i * ds k i) ≤ B * μ := by
    rw [hBdef]; linarith [h510]
  -- products along the step
  have hprod : ∀ a : ℝ, 0 ≤ a → a ≤ ab → ∀ i,
      γ * ((1 - a * (1 - σk)) * μ) ≤ (x k i + a * dx k i) * (s k i + a * ds k i) := by
    intro a ha0 ha1 i
    have ha1' : a ≤ 1 := le_trans ha1 hab1
    have e : (x k i + a * dx k i) * (s k i + a * ds k i) =
        (1 - a) * (x k i * s k i) + a * σk * μ + a ^ 2 * (dx k i * ds k i) := by
      have := h3 i; linear_combination a * this
    rw [e]
    have hd : -(B * μ) ≤ dx k i * ds k i := by
      have := g69b_abs_le_norm2 (fun i => dx k i * ds k i) i
      have := neg_abs_le (dx k i * ds k i)
      try simp only at *
      linarith
    have p1 : 0 ≤ (1 - a) * (x k i * s k i - γ * μ) :=
      mul_nonneg (by linarith) (by linarith [hw i])
    have p2 : 0 ≤ a ^ 2 * (dx k i * ds k i + B * μ) := mul_nonneg (sq_nonneg a) (by linarith)
    have hB0 : 0 ≤ B := by rw [hBdef]; positivity
    have p3 : 0 ≤ a * μ * (σk * (1 - γ) - a * B) := by
      apply mul_nonneg (mul_nonneg ha0 hmu.le)
      rw [← hid]; nlinarith
    nlinarith
  have hmem : ∀ a : ℝ, 0 ≤ a → a ≤ ab →
      (x k + a • dx k, lam k + a • dlam k, s k + a • ds k) ∈ NegInf A b c γ := by
    intro a ha0 ha1
    have hf : ∀ i, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        0 < (x k i + t * (a * dx k i)) * (s k i + t * (a * ds k i)) := by
      intro i t ht0 ht1
      have hta0 : 0 ≤ t * a := mul_nonneg ht0 ha0
      have hta1 : t * a ≤ ab := le_trans (mul_le_of_le_one_left ha0 ht1) ha1
      have := hprod (t * a) hta0 hta1 i
      have hpos : 0 < γ * ((1 - t * a * (1 - σk)) * μ) := by
        apply mul_pos hγ0 (mul_pos _ hmu)
        have := mul_le_mul_of_nonneg_right (le_trans hta1 hab1) (by linarith : (0:ℝ) ≤ 1 - σk)
        linarith
      have e : (x k i + t * (a * dx k i)) * (s k i + t * (a * ds k i)) =
          (x k i + t * a * dx k i) * (s k i + t * a * ds k i) := by ring
      rw [e]; exact lt_of_lt_of_le hpos this
    have hxpos : ∀ i, 0 < x k i + a * dx k i := fun i => g69b_pos_of_path _ _ _ _ (hx i) (hf i)
    have hspos : ∀ i, 0 < s k i + a * ds k i := fun i => g69b_pos_of_path _ _ _ _ (hs i)
      (fun t h0 h1 => by rw [mul_comm]; exact hf i t h0 h1)
    refine ⟨⟨?_, ?_, fun i => ?_, fun i => ?_⟩, fun i => ?_⟩
    · show A *ᵥ (x k + a • dx k) = b
      rw [mulVec_add, mulVec_smul, hAx, h2, smul_zero, add_zero]
    · show Aᵀ *ᵥ (lam k + a • dlam k) + (s k + a • ds k) = c
      rw [mulVec_add, mulVec_smul, add_add_add_comm, hAs, ← smul_add, h1, smul_zero, add_zero]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact hxpos i
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact hspos i
    · show γ * mu (x k + a • dx k) (s k + a • ds k) ≤ (x k + a • dx k) i * (s k + a • ds k) i
      rw [hmua]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact hprod a ha0 ha1 i
  have hge : ab ≤ α k := (hLPF.alpha_greatest k).2 ⟨⟨hab0, hab1⟩, hmem ab hab0 le_rfl⟩
  rw [hupd]
  apply mul_le_mul_of_nonneg_right _ hmu.le
  have hmin := g69b_sig_min σmin σmax σk hσk.1 hσk.2
  have hK0 : 0 ≤ C * γ * ((1 - γ) / (1 + γ)) := by
    apply mul_nonneg (mul_nonneg hC0.le hγ0.le)
    apply div_nonneg (by linarith) (by linarith)
  have q1 : ab * (1 - σk) ≤ α k * (1 - σk) := mul_le_mul_of_nonneg_right hge (by linarith)
  have q2 : C * γ * ((1 - γ) / (1 + γ)) * min (σmin * (1 - σmin)) (σmax * (1 - σmax)) / n ≤
      ab * (1 - σk) := by
    rw [habdef, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (by linarith)
    have := mul_le_mul_of_nonneg_left hmin hK0
    calc _ = C * γ * ((1 - γ) / (1 + γ)) * min (σmin * (1 - σmin)) (σmax * (1 - σmax)) := by ring
      _ ≤ C * γ * ((1 - γ) / (1 + γ)) * (σk * (1 - σk)) := this
      _ = _ := by ring
  linarith

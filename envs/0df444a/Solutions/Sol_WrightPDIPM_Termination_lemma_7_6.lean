-- Prove2me | solution 1 for WrightPDIPM.Termination.lemma_7_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:01:02.479637+00:00
-- url     : https://prove2.me/submissions/d77fb7b8-461a-4850-b6af-0d2aeeee1ac0

import Mathlib
import Definitions.Def_WrightPDIPM_Termination_Setup
open WrightPDIPM.Termination

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
theorem g69b_norm2_eq {n : ℕ} (v : Fin n → ℝ) :
    norm2 v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold norm2
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [Real.norm_eq_abs, sq_abs]

theorem g69b_norm2_comb {n : ℕ} (a b : ℝ) (u v : Fin n → ℝ) :
    norm2 (a • u + b • v) ≤ |a| * norm2 u + |b| * norm2 v := by
  rw [g69b_norm2_eq, g69b_norm2_eq u, g69b_norm2_eq v, WithLp.toLp_add, WithLp.toLp_smul,
    WithLp.toLp_smul]
  calc _ ≤ ‖a • (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ +
        ‖b • (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]

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

theorem g69b_55b {n : ℕ} (x s : Fin n → ℝ) (σ : ℝ)
    (dx ds : Fin n → ℝ) (h0 : dx ⬝ᵥ ds = 0)
    (h3 : ∀ i, s i * dx i + x i * ds i = -(x i * s i) + σ * mu x s) (α : ℝ) :
    norm2 (fun i => (x + α • dx) i * (s + α • ds) i - mu (x + α • dx) (s + α • ds)) ≤
        |1 - α| * norm2 (fun i => x i * s i - mu x s) + α ^ 2 * norm2 (fun i => dx i * ds i) := by
  have hmua := g69b_pf_mu_alpha x s dx ds σ h0 h3 α
  have e : (fun i => (x + α • dx) i * (s + α • ds) i - mu (x + α • dx) (s + α • ds)) =
      (1 - α) • (fun i => x i * s i - mu x s) + (α ^ 2) • (fun i => dx i * ds i) := by
    funext i
    rw [hmua]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := h3 i
    linear_combination α * this
  rw [e]
  have := g69b_norm2_comb (1 - α) (α ^ 2) (fun i => x i * s i - mu x s) (fun i => dx i * ds i)
  rwa [abs_of_nonneg (sq_nonneg α)] at this

theorem g69b_prod_bound {n : ℕ} (dx ds : Fin n → ℝ) :
    norm2 (fun i => dx i * ds i) ≤ norm2Pair dx ds ^ 2 / 2 := by
  unfold norm2 norm2Pair
  set X := ∑ i, dx i ^ 2
  set Y := ∑ i, ds i ^ 2
  have hX : 0 ≤ X := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hY : 0 ≤ Y := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [Real.sq_sqrt (by linarith), Real.sqrt_le_left (by positivity)]
  have h1 : ∑ i, (dx i * ds i) ^ 2 ≤ X * Y := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have : ds i ^ 2 ≤ Y := Finset.single_le_sum (f := fun j => ds j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  nlinarith [sq_nonneg (X - Y)]

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (C₅ : ℝ)
    (hC₅ : ∀ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ),
      (x, lam, s) ∈ NegInf A b c (1 / 2) →
        ∀ (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ),
          IsAffineStep A x s dx dlam ds → norm2Pair dx ds ≤ C₅ * mu x s)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hN : (x, lam, s) ∈ N2 A b c (1 / 4))
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hstep : IsAffineStep A x s dx dlam ds) :
    (∀ α ∈ Set.Icc (0 : ℝ) (1 - 4 * C₅ ^ 2 * mu x s),
        (x + α • dx, lam + α • dlam, s + α • ds) ∈ N2 A b c (1 / 2)) ∧
      ∀ αk : ℝ, IsGreatest {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧
          (x + a • dx, lam + a • dlam, s + a • ds) ∈ N2 A b c (1 / 2)} αk →
        1 - 4 * C₅ ^ 2 * mu x s ≤ αk := by
  obtain ⟨⟨hAx, hAs, hx, hs⟩, hw⟩ := hN
  simp only at hAx hAs hx hs hw
  have hstep' := hstep
  obtain ⟨h1, h2, h3a⟩ := hstep
  have h3 : ∀ i, s i * dx i + x i * ds i = -(x i * s i) + 0 * mu x s := by
    intro i; rw [h3a i]; ring
  have h0 := g69b_pf_dxds A dx dlam ds h1 h2
  have hmua := g69b_pf_mu_alpha x s dx ds 0 h0 h3
  simp only [sub_zero, mul_one] at hmua
  have hmu0 : 0 ≤ mu x s := by
    unfold mu
    apply div_nonneg _ (Nat.cast_nonneg n)
    exact Finset.sum_nonneg (fun i _ => (mul_pos (hx i) (hs i)).le)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hmz : mu x s = 0 := by simp [mu]
    have hmem : ∀ α : ℝ, (x + α • dx, lam + α • dlam, s + α • ds) ∈ N2 A b c (1 / 2) := by
      intro α
      refine ⟨⟨?_, ?_, fun i => i.elim0, fun i => i.elim0⟩, ?_⟩
      · show A *ᵥ (x + α • dx) = b; rw [mulVec_add, mulVec_smul, hAx, h2, smul_zero, add_zero]
      · show Aᵀ *ᵥ (lam + α • dlam) + (s + α • ds) = c
        rw [mulVec_add, mulVec_smul, add_add_add_comm, hAs, ← smul_add, h1, smul_zero, add_zero]
      · simp [norm2, mu]
    refine ⟨fun α _ => hmem α, fun αk hk => ?_⟩
    rw [hmz]
    have := hk.2 (show (1:ℝ) ∈ {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧
      (x + a • dx, lam + a • dlam, s + a • ds) ∈ N2 A b c (1 / 2)} from
      ⟨⟨zero_le_one, le_rfl⟩, hmem 1⟩)
    linarith
  have hmu := g69b_dot_pos hn x s hx hs
  set μ := mu x s with hμdef
  -- N2(1/4) ⊂ NegInf(1/2)
  have hwi : ∀ i, (3 / 4) * μ ≤ x i * s i := by
    intro i
    have := g69b_abs_le_norm2 (fun i => x i * s i - μ) i
    have := neg_abs_le (x i * s i - μ)
    try simp only at *
    linarith
  have hNI : (x, lam, s) ∈ NegInf A b c (1 / 2) :=
    ⟨⟨hAx, hAs, hx, hs⟩, fun i => by simp only; linarith [hwi i]⟩
  have hP := hC₅ x lam s hNI dx dlam ds hstep'
  have hP0 : 0 ≤ norm2Pair dx ds := Real.sqrt_nonneg _
  have hPpos : 0 < norm2Pair dx ds := by
    rcases lt_or_eq_of_le hP0 with h | h
    · exact h
    · exfalso
      have hz : ∑ i, dx i ^ 2 + ∑ j, ds j ^ 2 = 0 := by
        have := congrArg (· ^ 2) h
        try simp only at this
        unfold norm2Pair at this
        rw [Real.sq_sqrt (by positivity)] at this
        linarith
      have hX : 0 ≤ ∑ i, dx i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have hY : 0 ≤ ∑ i, ds i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have hdx0 : dx ⟨0, hn⟩ = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (dx i))).mp
          (by linarith) ⟨0, hn⟩ (Finset.mem_univ _)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      have hds0 : ds ⟨0, hn⟩ = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (ds i))).mp
          (by linarith) ⟨0, hn⟩ (Finset.mem_univ _)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      have := h3a ⟨0, hn⟩
      rw [hdx0, hds0] at this
      have := mul_pos (hx ⟨0, hn⟩) (hs ⟨0, hn⟩)
      linarith
  have hCμ : 0 < C₅ * μ := lt_of_lt_of_le hPpos hP
  have hC2 : 0 < C₅ ^ 2 * μ := by
    have : 0 < (C₅ * μ) ^ 2 := by positivity
    have : (C₅ * μ) ^ 2 = (C₅ ^ 2 * μ) * μ := by ring
    nlinarith
  have hdd : norm2 (fun i => dx i * ds i) ≤ C₅ ^ 2 * μ ^ 2 / 2 := by
    refine le_trans (g69b_prod_bound dx ds) ?_
    have : norm2Pair dx ds ^ 2 ≤ (C₅ * μ) ^ 2 := pow_le_pow_left₀ hP0 hP 2
    nlinarith
  have hkey : ∀ α, 0 ≤ α → α ≤ 1 - 4 * C₅ ^ 2 * μ →
      norm2 (fun i => (x + α • dx) i * (s + α • ds) i - mu (x + α • dx) (s + α • ds)) ≤
        (1 / 2) * mu (x + α • dx) (s + α • ds) := by
    intro α ha0 ha1
    have hα1 : α ≤ 1 := by linarith
    refine le_trans (g69b_55b x s 0 dx ds h0 h3 α) ?_
    rw [abs_of_nonneg (by linarith), hmua]
    have := mul_le_mul_of_nonneg_left hw (by linarith : (0:ℝ) ≤ 1 - α)
    have := mul_le_mul_of_nonneg_left hdd (sq_nonneg α)
    have : α ^ 2 ≤ 1 := by nlinarith
    have : α ^ 2 * (C₅ ^ 2 * μ ^ 2 / 2) ≤ C₅ ^ 2 * μ * μ / 2 := by
      have : 0 ≤ C₅ ^ 2 * μ ^ 2 / 2 := by positivity
      nlinarith
    have : 4 * C₅ ^ 2 * μ * μ ≤ (1 - α) * μ := mul_le_mul_of_nonneg_right (by linarith) hmu.le
    nlinarith
  have hmem : ∀ α ∈ Set.Icc (0 : ℝ) (1 - 4 * C₅ ^ 2 * μ),
      (x + α • dx, lam + α • dlam, s + α • ds) ∈ N2 A b c (1 / 2) := by
    rintro α ⟨ha0, ha1⟩
    have hf : ∀ i, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        0 < (x i + t * (α * dx i)) * (s i + t * (α * ds i)) := by
      intro i t ht0 ht1
      have hta0 : 0 ≤ t * α := mul_nonneg ht0 ha0
      have hta1 : t * α ≤ 1 - 4 * C₅ ^ 2 * μ := le_trans (mul_le_of_le_one_left ha0 ht1) ha1
      have hk := hkey (t * α) hta0 hta1
      have hab := g69b_abs_le_norm2
        (fun i => (x + (t * α) • dx) i * (s + (t * α) • ds) i -
          mu (x + (t * α) • dx) (s + (t * α) • ds)) i
      have := neg_abs_le ((x + (t * α) • dx) i * (s + (t * α) • ds) i -
          mu (x + (t * α) • dx) (s + (t * α) • ds))
      rw [hmua] at hk this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this hk hab
      rw [hmua] at hab
      have hpos : 0 < (1 - t * α) * μ := mul_pos (by linarith) hmu
      have e : (x i + t * (α * dx i)) * (s i + t * (α * ds i)) =
          (x i + t * α * dx i) * (s i + t * α * ds i) := by ring
      rw [e]
      linarith
    have hxpos : ∀ i, 0 < x i + α * dx i := fun i => g69b_pos_of_path _ _ _ _ (hx i) (hf i)
    have hspos : ∀ i, 0 < s i + α * ds i := fun i => g69b_pos_of_path _ _ _ _ (hs i)
      (fun t h0 h1 => by rw [mul_comm]; exact hf i t h0 h1)
    refine ⟨⟨?_, ?_, fun i => ?_, fun i => ?_⟩, ?_⟩
    · show A *ᵥ (x + α • dx) = b; rw [mulVec_add, mulVec_smul, hAx, h2, smul_zero, add_zero]
    · show Aᵀ *ᵥ (lam + α • dlam) + (s + α • ds) = c
      rw [mulVec_add, mulVec_smul, add_add_add_comm, hAs, ← smul_add, h1, smul_zero, add_zero]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact hxpos i
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact hspos i
    · exact hkey α ha0 ha1
  refine ⟨hmem, fun αk hk => ?_⟩
  have hk0 : 0 ≤ αk := hk.1.1.1
  rcases lt_or_ge (1 - 4 * C₅ ^ 2 * μ) 0 with h | h
  · linarith
  · exact hk.2 ⟨⟨h, by linarith⟩, hmem _ ⟨h, le_rfl⟩⟩

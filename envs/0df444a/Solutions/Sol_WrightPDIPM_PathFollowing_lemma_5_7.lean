-- Prove2me | solution 1 for WrightPDIPM.PathFollowing.lemma_5_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:20:48.44301+00:00
-- url     : https://prove2.me/submissions/cfc6a20f-e99d-4dbe-a230-692d8238052a

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

theorem g69b_55a {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (σ : ℝ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hstep : IsStep A x s σ dx dlam ds) (α : ℝ) :
    norm2 (fun i => (x + α • dx) i * (s + α • ds) i - mu (x + α • dx) (s + α • ds)) ≤
        |1 - α| * norm2 (fun i => x i * s i - mu x s) + α ^ 2 * norm2 (fun i => dx i * ds i) := by
  obtain ⟨h1, h2, h3⟩ := hstep
  have h0 := g69b_pf_dxds A dx dlam ds h1 h2
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

theorem g69b_alphaBar_props {n : ℕ} (x s dx ds : Fin n → ℝ) (hmu : 0 ≤ mu x s) :
    0 ≤ alphaBar x s dx ds ∧ alphaBar x s dx ds ≤ 1 / 2 ∧
      ∀ α, 0 ≤ α → α ≤ alphaBar x s dx ds →
        α ^ 2 * norm2 (fun i => dx i * ds i) ≤ mu x s / 8 := by
  unfold alphaBar
  split_ifs with h
  · refine ⟨by norm_num, le_rfl, fun α _ _ => ?_⟩
    rw [h, mul_zero]; positivity
  · have hN : 0 < norm2 (fun i => dx i * ds i) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h)
    refine ⟨le_min (by norm_num) (Real.sqrt_nonneg _), min_le_left _ _, fun α h0 h1 => ?_⟩
    have h2 : α ≤ Real.sqrt (mu x s / (8 * norm2 (fun i => dx i * ds i))) :=
      le_trans h1 (min_le_right _ _)
    have h3 : α ^ 2 ≤ mu x s / (8 * norm2 (fun i => dx i * ds i)) := by
      calc α ^ 2 ≤ (Real.sqrt (mu x s / (8 * norm2 (fun i => dx i * ds i)))) ^ 2 :=
            pow_le_pow_left₀ h0 h2 2
        _ = _ := Real.sq_sqrt (by positivity)
    rw [le_div_iff₀ (by positivity)] at h3
    linarith

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hN : (x, lam, s) ∈ N2 A b c (1 / 4))
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hstep : IsStep A x s 0 dx dlam ds) :
    (∀ α ∈ Set.Icc (0 : ℝ) (alphaBar x s dx ds),
        (x + α • dx, lam + α • dlam, s + α • ds) ∈ N2 A b c (1 / 2)) ∧
      ∀ αk : ℝ, IsGreatest {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧
          (x + a • dx, lam + a • dlam, s + a • ds) ∈ N2 A b c (1 / 2)} αk →
        alphaBar x s dx ds ≤ αk ∧
          mu (x + αk • dx) (s + αk • ds) ≤ (1 - alphaBar x s dx ds) * mu x s := by
  have h55 := g69b_55a A x s 0 dx dlam ds hstep
  obtain ⟨⟨hAx, hAs, hx, hs⟩, hw⟩ := hN
  simp only at hAx hAs hx hs hw
  obtain ⟨h1, h2, h3⟩ := hstep
  have h0 := g69b_pf_dxds A dx dlam ds h1 h2
  have hmua := g69b_pf_mu_alpha x s dx ds 0 h0 h3
  simp only [sub_zero, mul_one] at hmua
  have hmu0 : 0 ≤ mu x s := by
    unfold mu
    apply div_nonneg _ (Nat.cast_nonneg n)
    exact Finset.sum_nonneg (fun i _ => (mul_pos (hx i) (hs i)).le)
  obtain ⟨hab0, hab1, habN⟩ := g69b_alphaBar_props x s dx ds hmu0
  -- key bound
  have hkey : ∀ α, 0 ≤ α → α ≤ alphaBar x s dx ds →
      norm2 (fun i => (x + α • dx) i * (s + α • ds) i - mu (x + α • dx) (s + α • ds)) ≤
        (1 / 2) * mu (x + α • dx) (s + α • ds) := by
    intro α ha0 ha1
    have hα : α ≤ 1 / 2 := le_trans ha1 hab1
    refine le_trans (h55 α) ?_
    rw [abs_of_nonneg (by linarith), hmua]
    have := habN α ha0 ha1
    have := mul_le_mul_of_nonneg_left hw (by linarith : (0:ℝ) ≤ 1 - α)
    nlinarith
  have hmem : ∀ α ∈ Set.Icc (0 : ℝ) (alphaBar x s dx ds),
      (x + α • dx, lam + α • dlam, s + α • ds) ∈ N2 A b c (1 / 2) := by
    rintro α ⟨ha0, ha1⟩
    have hα : α ≤ 1 / 2 := le_trans ha1 hab1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨⟨?_, ?_, fun i => i.elim0, fun i => i.elim0⟩, ?_⟩
      · show A *ᵥ (x + α • dx) = b; rw [mulVec_add, mulVec_smul, hAx, h2, smul_zero, add_zero]
      · show Aᵀ *ᵥ (lam + α • dlam) + (s + α • ds) = c
        rw [mulVec_add, mulVec_smul, add_add_add_comm, hAs, ← smul_add, h1,
          smul_zero, add_zero]
      · simp [norm2, mu]
    have hmu := g69b_dot_pos hn x s hx hs
    -- positivity along the segment
    have hf : ∀ i, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        0 < (x i + t * (α * dx i)) * (s i + t * (α * ds i)) := by
      intro i t ht0 ht1
      have hta0 : 0 ≤ t * α := mul_nonneg ht0 ha0
      have hta1 : t * α ≤ alphaBar x s dx ds := by nlinarith
      have hk := hkey (t * α) hta0 hta1
      have hab := g69b_abs_le_norm2
        (fun i => (x + (t * α) • dx) i * (s + (t * α) • ds) i -
          mu (x + (t * α) • dx) (s + (t * α) • ds)) i
      have := neg_abs_le ((x + (t * α) • dx) i * (s + (t * α) • ds) i -
          mu (x + (t * α) • dx) (s + (t * α) • ds))
      rw [hmua] at hk this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this hk hab
      rw [hmua] at hab
      have hpos : 0 < (1 - t * α) * mu x s := mul_pos (by nlinarith) hmu
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
      rw [mulVec_add, mulVec_smul, add_add_add_comm, hAs, ← smul_add, h1,
        smul_zero, add_zero]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact hxpos i
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact hspos i
    · exact hkey α ha0 ha1
  refine ⟨hmem, fun αk hk => ?_⟩
  have hin : alphaBar x s dx ds ∈ {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧
      (x + a • dx, lam + a • dlam, s + a • ds) ∈ N2 A b c (1 / 2)} :=
    ⟨⟨hab0, by linarith⟩, hmem _ ⟨hab0, le_rfl⟩⟩
  have hle := hk.2 hin
  refine ⟨hle, ?_⟩
  rw [hmua]
  exact mul_le_mul_of_nonneg_right (by linarith) hmu0

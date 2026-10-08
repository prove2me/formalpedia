-- Prove2me | solution 1 for PrimalDualSubgrad.DA.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:43:17.258121+00:00
-- url     : https://prove2.me/submissions/66e43a94-9fa4-4b32-b545-ab37575d8785

import Theorems.Thm_PrimalDualSubgrad_DA_eq_2_18

open Finset PrimalDualSubgrad.DA

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem da_strong_growth {Q : Set E} {f : E → ℝ} {c : ℝ}
    (hc : StrongConvexOn Q c f) {a y : E} (ha : a ∈ Q) (hy : y ∈ Q)
    (hmin : ∀ z ∈ Q, f a ≤ f z) :
    f a + c / 2 * ‖y - a‖ ^ 2 ≤ f y := by
  let A := c / 2 * ‖y - a‖ ^ 2
  let B := f y - f a
  have hB : 0 ≤ B := sub_nonneg.mpr (hmin y hy)
  by_contra hn
  have hBA : B < A := by dsimp [A, B]; linarith
  have hA : 0 < A := lt_of_le_of_lt hB hBA
  let t := (A - B) / (2 * A)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have htEq : t * (2 * A) = A - B := by dsimp [t]; field_simp
  have hj := hc.2 hy ha ht.le (sub_nonneg.mpr ht1) (by ring : t + (1-t) = 1)
  have hm := hmin _ (hc.1 hy ha ht.le (sub_nonneg.mpr ht1) (by ring : t + (1-t) = 1))
  simp only [smul_eq_mul] at hj
  change f (t • y + (1-t) • a) ≤ t * f y + (1-t) * f a - t * (1-t) * A at hj
  have hineq : (1-t) * A ≤ B := by dsimp [B]; nlinarith
  nlinarith

private theorem da_initial (P : ProxSetting E) (b c : ℝ) (hb : 0 < b)
    (hbc : b ≤ c) (s : StrongDual ℝ E) :
    V P c s ≤ 1 / (2 * P.σ * b) * ‖s‖ ^ 2 := by
  apply csSup_le (show ((fun y => s (y - P.x0) - c * P.d y) '' P.Q).Nonempty from
    ⟨_, P.x0, P.x0_mem, rfl⟩)
  rintro _ ⟨y, hy, rfl⟩
  have hg := da_strong_growth P.strongConvexOn_d P.x0_mem hy P.x0_isMin
  rw [P.d_x0, zero_add] at hg
  have hd : 0 ≤ P.d y := by simpa [P.d_x0] using P.x0_isMin y hy
  have hquad := mul_le_mul_of_nonneg_left hg hb.le
  have hmono := mul_le_mul_of_nonneg_right hbc hd
  have hs : s (y - P.x0) ≤ ‖s‖ * ‖y - P.x0‖ :=
    (le_abs_self _).trans (s.le_opNorm _)
  let q := b * P.σ / 2
  have hq : 0 < q := by dsimp [q]; positivity [P.σ_pos]
  have hsq := mul_nonneg hq.le (sq_nonneg (‖y - P.x0‖ - ‖s‖ / (2 * q)))
  have hid : q * (‖y - P.x0‖ - ‖s‖ / (2 * q)) ^ 2 =
      q * ‖y - P.x0‖ ^ 2 - ‖s‖ * ‖y - P.x0‖ +
        1 / (2 * P.σ * b) * ‖s‖ ^ 2 := by
    dsimp [q]
    field_simp [ne_of_gt P.σ_pos, ne_of_gt hb]
    <;> ring
  rw [hid] at hsq
  dsimp [q] at hsq
  nlinarith

private theorem da_beta_pos (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E)
    (lam β : ℕ → ℝ) (g : ℕ → StrongDual ℝ E) (x : ℕ → E)
    (hrun : IsDARun P π lam β g x) (k : ℕ) : 0 < β k := by
  induction k with
  | zero => exact hrun.1
  | succ k ih => exact ih.trans_le (hrun.2.1 k)

private theorem da_value_at_prox (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E)
    (hπ : IsProxMap P π) (b : ℝ) (hb : 0 < b) (s : StrongDual ℝ E) :
    V P b s = s (π b s - P.x0) - b * P.d (π b s) := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨π b s, (hπ b hb s).1, rfl⟩, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  have hm := (hπ b hb s).2 y hy
  simp only [map_sub] at *
  linarith

private theorem da_growth (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E)
    (hπ : IsProxMap P π) (b : ℝ) (hb : 0 < b) (s : StrongDual ℝ E)
    (y : E) (hy : y ∈ P.Q) :
    -(s (π b s)) + b * P.d (π b s) +
        (b * P.σ) / 2 * ‖y - π b s‖ ^ 2 ≤ -(s y) + b * P.d y := by
  let f : E → ℝ := fun z => -(s z) + b * P.d z
  have hsc : StrongConvexOn P.Q (b * P.σ) f := by
    refine ⟨P.convex_Q, ?_⟩
    intro u hu v hv a c ha hc hac
    have hh := mul_le_mul_of_nonneg_left (P.strongConvexOn_d.2 hu hv ha hc hac) hb.le
    dsimp [f]
    simp only [map_add, map_smul, smul_eq_mul] at *
    nlinarith
  exact da_strong_growth hsc (hπ b hb s).1 hy (hπ b hb s).2

private theorem da_energy (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E)
    (hπ : IsProxMap P π) (lam β : ℕ → ℝ) (g : ℕ → StrongDual ℝ E)
    (x : ℕ → E) (hrun : IsDARun P π lam β g x) (k : ℕ) :
    (∑ i ∈ range (k + 1), lam i * g i (x i - P.x0)) +
      V P (β (k + 1)) (-(sAgg lam g (k + 1))) ≤
        1 / (2 * P.σ) * ∑ i ∈ range (k + 1), lam i ^ 2 / β i * ‖g i‖ ^ 2 := by
  have htel := eq_2_18 P π hπ lam β g x hrun k
  have hinit := da_initial P (β 0) (β 1) hrun.1 (hrun.2.1 0) (-(sAgg lam g 1))
  have hn : ‖-(sAgg lam g 1)‖ ^ 2 = (lam 0) ^ 2 * ‖g 0‖ ^ 2 := by
    simp [sAgg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hn] at hinit
  have hi : V P (β 1) (-(sAgg lam g 1)) ≤
      1 / (2 * P.σ) * (lam 0 ^ 2 / β 0 * ‖g 0‖ ^ 2) := by
    calc
      _ ≤ 1 / (2 * P.σ * β 0) * ((lam 0) ^ 2 * ‖g 0‖ ^ 2) := hinit
      _ = _ := by ring
  have hs : (∑ i ∈ range (k + 1), lam i ^ 2 / β i * ‖g i‖ ^ 2) =
      lam 0 ^ 2 / β 0 * ‖g 0‖ ^ 2 +
        ∑ i ∈ Icc 1 k, lam i ^ 2 / β i * ‖g i‖ ^ 2 := by
    have hh : range (k + 1) = insert 0 (Icc 1 k) := by
      ext i
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    rw [hh, sum_insert (by simp)]
  rw [hs]
  nlinarith

private theorem da_sum_shift (P : ProxSetting E) (lam : ℕ → ℝ)
    (g : ℕ → StrongDual ℝ E) (x : ℕ → E) (k : ℕ) (y : E) :
    (∑ i ∈ range (k + 1), lam i * g i (x i - y)) =
      (∑ i ∈ range (k + 1), lam i * g i (x i - P.x0)) -
        sAgg lam g (k + 1) (y - P.x0) := by
  simp only [sAgg, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, map_sub, mul_sub, sum_sub_distrib]
  ring

private theorem da_pointwise (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E)
    (hπ : IsProxMap P π) (lam β : ℕ → ℝ) (g : ℕ → StrongDual ℝ E)
    (x : ℕ → E) (hrun : IsDARun P π lam β g x) (k : ℕ) (D : ℝ)
    (y : E) (hy : y ∈ FD P D) :
    (∑ i ∈ range (k + 1), lam i * g i (x i - y)) ≤
      β (k + 1) * D +
        1 / (2 * P.σ) * ∑ i ∈ range (k + 1), lam i ^ 2 / β i * ‖g i‖ ^ 2 := by
  have hb := da_beta_pos P π lam β g x hrun (k + 1)
  have he := da_energy P π hπ lam β g x hrun k
  have hv := da_value_at_prox P π hπ (β (k + 1)) hb (-(sAgg lam g (k + 1)))
  have hm := (hπ (β (k + 1)) hb (-(sAgg lam g (k + 1)))).2 y hy.1
  rw [da_sum_shift P lam g x k y]
  simp only [ContinuousLinearMap.neg_apply, map_sub] at *
  have hd := mul_le_mul_of_nonneg_left hy.2 hb.le
  linarith

end

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (lam β : ℕ → ℝ) (g : ℕ → StrongDual ℝ E) (x : ℕ → E) (hrun : IsDARun P π lam β g x) :
    (∀ k : ℕ, ∀ D : ℝ, 0 ≤ D →
      delta P lam g x k D ≤ Delta P lam g x k (β (k + 1)) D ∧
        Delta P lam g x k (β (k + 1)) D ≤
          β (k + 1) * D + 1 / (2 * P.σ) * ∑ i ∈ range (k + 1), lam i ^ 2 / β i * ‖g i‖ ^ 2) ∧
    (∀ xstar ∈ P.Q, (∀ i, 0 ≤ g i (x i - xstar)) → ∀ k : ℕ,
      P.σ / 2 * ‖x (k + 1) - xstar‖ ^ 2 ≤
        P.d xstar + 1 / (2 * P.σ * β (k + 1)) *
          ∑ i ∈ range (k + 1), lam i ^ 2 / β i * ‖g i‖ ^ 2) ∧
    (∀ xstar ∈ P.Q, (∀ i, 0 ≤ g i (x i - xstar)) → ∀ r : ℝ, 0 < r → ∀ D : ℝ, 0 < D →
      Metric.closedBall xstar r ⊆ FD P D → ∀ k : ℕ,
        ‖(1 / Ssum lam k) • sAgg lam g (k + 1)‖ ≤
          1 / (r * Ssum lam k) *
            (β (k + 1) * D + 1 / (2 * P.σ) * ∑ i ∈ range (k + 1), lam i ^ 2 / β i * ‖g i‖ ^ 2)) := by
  have hb := da_beta_pos P π lam β g x hrun
  have hnonneg (xs : E) (hs : ∀ i, 0 ≤ g i (x i - xs)) (k : ℕ) :
      0 ≤ ∑ i ∈ range (k + 1), lam i * g i (x i - xs) :=
    sum_nonneg fun i _ => mul_nonneg (hrun.2.2.1 i).le (hs i)
  refine ⟨?_, ?_, ?_⟩
  · intro k D hD
    constructor
    · apply csSup_le (show ((fun y => ∑ i ∈ range (k + 1), lam i * g i (x i - y)) ''
        FD P D).Nonempty from ⟨_, P.x0, ⟨P.x0_mem, by simpa [P.d_x0] using hD⟩, rfl⟩)
      rintro _ ⟨y, hy, rfl⟩
      have hv := da_value_at_prox P π hπ (β (k + 1)) (hb _) (-(sAgg lam g (k + 1)))
      have hm := (hπ (β (k + 1)) (hb _) (-(sAgg lam g (k + 1)))).2 y hy.1
      have hd := mul_le_mul_of_nonneg_left hy.2 (hb (k + 1)).le
      change (∑ i ∈ range (k + 1), lam i * g i (x i - y)) ≤ _
      rw [da_sum_shift P lam g x k y]
      dsimp [Delta]
      simp only [ContinuousLinearMap.neg_apply, map_sub] at *
      linarith
    · have he := da_energy P π hπ lam β g x hrun k
      dsimp [Delta]
      linarith
  · intro xs hxs hs k
    have he := da_energy P π hπ lam β g x hrun k
    have hn := hnonneg xs hs k
    have hv := da_value_at_prox P π hπ (β (k + 1)) (hb _) (-(sAgg lam g (k + 1)))
    have hg := da_growth P π hπ (β (k + 1)) (hb _) (-(sAgg lam g (k + 1))) xs hxs
    rw [← hrun.2.2.2.2 k] at hv hg
    rw [da_sum_shift P lam g x k xs] at hn
    rw [norm_sub_rev xs] at hg
    simp only [ContinuousLinearMap.neg_apply, map_sub] at hv hg hn he
    have hgrowth : β (k + 1) * (P.σ / 2 * ‖x (k + 1) - xs‖ ^ 2) ≤
        β (k + 1) * P.d xs +
          1 / (2 * P.σ) * ∑ i ∈ range (k + 1), lam i ^ 2 / β i * ‖g i‖ ^ 2 := by
      nlinarith
    apply (mul_le_mul_iff_right₀ (hb (k + 1))).mp
    calc
      _ ≤ β (k + 1) * P.d xs +
          1 / (2 * P.σ) * ∑ i ∈ range (k + 1), lam i ^ 2 / β i * ‖g i‖ ^ 2 := hgrowth
      _ = _ := by field_simp [ne_of_gt (hb (k + 1)), ne_of_gt P.σ_pos]
  · intro xs hxs hs r hr D hD hball k
    let B : ℝ := β (k + 1) * D +
      1 / (2 * P.σ) * ∑ i ∈ range (k + 1), lam i ^ 2 / β i * ‖g i‖ ^ 2
    have hB : 0 ≤ B := by
      dsimp [B]
      apply add_nonneg (mul_nonneg (hb _).le hD.le)
      apply mul_nonneg (by positivity [P.σ_pos])
      exact sum_nonneg fun i _ => mul_nonneg (div_nonneg (sq_nonneg _) (hb i).le) (sq_nonneg _)
    have hnorm : ‖sAgg lam g (k + 1)‖ ≤ B / r := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hB hr.le)
      intro u hu
      have hmemb (v : E) (hv : ‖v‖ = 1) : xs + r • v ∈ FD P D := by
        apply hball
        rw [Metric.mem_closedBall, dist_eq_norm]
        simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hv]
      have hp := da_pointwise P π hπ lam β g x hrun k D (xs + r • u) (hmemb u hu)
      have hm := da_pointwise P π hπ lam β g x hrun k D (xs + r • (-u))
        (hmemb (-u) (by simpa using hu))
      have hn := hnonneg xs hs k
      rw [da_sum_shift P lam g x k (xs + r • u)] at hp
      rw [da_sum_shift P lam g x k (xs + r • (-u))] at hm
      rw [da_sum_shift P lam g x k xs] at hn
      simp only [map_add, map_sub, map_smul, map_neg, smul_eq_mul] at hp hm hn
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · rw [neg_le]
        apply (le_div_iff₀ hr).2
        dsimp [B] at *
        nlinarith
      · apply (le_div_iff₀ hr).2
        dsimp [B] at *
        nlinarith
    have hS : 0 < Ssum lam k := by
      apply sum_pos
      · intro i hi
        exact hrun.2.2.1 i
      · exact ⟨0, mem_range.mpr (Nat.zero_lt_succ k)⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hS)]
    have hh := mul_le_mul_of_nonneg_left hnorm (one_div_pos.mpr hS).le
    calc
      _ ≤ (1 / Ssum lam k) * (B / r) := hh
      _ = _ := by dsimp [B]; ring

#print axioms solution

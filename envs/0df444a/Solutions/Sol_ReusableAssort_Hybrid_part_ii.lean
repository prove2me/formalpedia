-- Prove2me | solution 1 for ReusableAssort.Hybrid.part_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T06:22:46.942993+00:00
-- url     : https://prove2.me/submissions/1aad7ddf-96e2-447f-a825-b5a02f446051

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Algorithms

open ReusableAssort.Hybrid

section PartII

variable {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]

private lemma V_gt (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (i : Fin n)
    {t : ℕ} (h : T < t) : V I y i t = 0 := by
  rw [V, dif_pos h]

private lemma V_le (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (i : Fin n)
    {t : ℕ} (h : t ≤ T) : V I y i t =
    ∑ z, ∑ S ∈ I.feas, X I y t z S *
    max (V I y i (t + 1))
      ((1 - I.phi z S i) * V I y i (t + 1)
        + I.phi z S i *
          ((1 / (I.c i : ℝ)) * ∑ d ∈ Finset.Icc 1 T,
              I.g z i d * (I.r z i + V I y i (t + d))
            + (((I.c i : ℝ) - 1) / (I.c i : ℝ)) * V I y i (t + 1))) := by
  rw [V, dif_neg (not_lt.mpr h)]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_attach (Finset.Icc 1 T) (fun d => I.g z i d * (I.r z i + V I y i (t + d)))]

private lemma sum_aux {ι κ : Type} (s : Finset ι) (u : ι → Finset κ)
    (X B P Q : ι → κ → ℝ) (c A : ℝ) (h : ∀ z S, c * B z S = c * A + P z S + Q z S) :
    c * ∑ z ∈ s, ∑ S ∈ u z, X z S * B z S
      = c * A * ∑ z ∈ s, ∑ S ∈ u z, X z S
        + ∑ z ∈ s, ∑ S ∈ u z, X z S * P z S + ∑ z ∈ s, ∑ S ∈ u z, X z S * Q z S := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun S _ => ?_
  rw [show c * (X z S * B z S) = X z S * (c * B z S) by ring, h]
  ring

/-- One step of the optimistic DP: `𝒱_{t+1} ≤ 𝒱_t` and the "Bellman" lower bound
`c (𝒱_t - 𝒱_{t+1}) ≥ Σ X φ r + Σ X φ Σ_d g(d) (𝒱_{t+d} - 𝒱_{t+1})`. -/
private lemma V_step (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPFeasible I y) (hN : Normalized I y)
    (i : Fin n) {t : ℕ} (ht : t ∈ Finset.Icc 1 T) :
    V I y i (t + 1) ≤ V I y i t ∧
    ∑ z, ∑ S ∈ I.feas, X I y t z S * I.phi z S i * I.r z i
      + ∑ z, ∑ S ∈ I.feas, X I y t z S * I.phi z S i *
          ∑ d ∈ Finset.Icc 1 T, I.g z i d * (V I y i (t + d) - V I y i (t + 1))
      ≤ (I.c i : ℝ) * (V I y i t - V I y i (t + 1)) := by
  have htT : t ≤ T := (Finset.mem_Icc.mp ht).2
  set A := V I y i (t + 1) with hA
  have hc : (0 : ℝ) < I.c i := by exact_mod_cast hI.one_le_c i
  have hX0 : ∀ z, ∀ S ∈ I.feas, 0 ≤ X I y t z S := fun z S hS =>
    mul_nonneg (hy.1 t ht z S hS) (hI.F_nonneg t z)
  have hXsum : ∑ z, ∑ S ∈ I.feas, X I y t z S = 1 := by
    unfold X
    simp_rw [← Finset.sum_mul]
    rw [← hI.F_sum t ht]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hN t ht z, one_mul]
  have hgs := hI.g_sum
  rw [V_le I y i htT]
  constructor
  · calc A = ∑ z, ∑ S ∈ I.feas, X I y t z S * A := by
          simp_rw [← Finset.sum_mul]; rw [hXsum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun S hS =>
          mul_le_mul_of_nonneg_left (le_max_left _ _) (hX0 z S hS)
  · -- the B branch
    have hB : ∀ z S, (I.c i : ℝ) * ((1 - I.phi z S i) * A
        + I.phi z S i *
          ((1 / (I.c i : ℝ)) * ∑ d ∈ Finset.Icc 1 T,
              I.g z i d * (I.r z i + V I y i (t + d))
            + (((I.c i : ℝ) - 1) / (I.c i : ℝ)) * A))
        = (I.c i : ℝ) * A + I.phi z S i * I.r z i
          + I.phi z S i * ∑ d ∈ Finset.Icc 1 T, I.g z i d * (V I y i (t + d) - A) := by
      intro z S
      have e1 : ∑ d ∈ Finset.Icc 1 T, I.g z i d * (I.r z i + V I y i (t + d))
          = I.r z i + ∑ d ∈ Finset.Icc 1 T, I.g z i d * V I y i (t + d) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, hgs z i, one_mul]
      have e2 : ∑ d ∈ Finset.Icc 1 T, I.g z i d * (V I y i (t + d) - A)
          = ∑ d ∈ Finset.Icc 1 T, I.g z i d * V I y i (t + d) - A := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        rw [← Finset.sum_mul, hgs z i, one_mul]
      rw [e1, e2]
      field_simp
      ring
    have hge : ∑ z, ∑ S ∈ I.feas, X I y t z S * ((1 - I.phi z S i) * A
        + I.phi z S i *
          ((1 / (I.c i : ℝ)) * ∑ d ∈ Finset.Icc 1 T,
              I.g z i d * (I.r z i + V I y i (t + d))
            + (((I.c i : ℝ) - 1) / (I.c i : ℝ)) * A))
        ≤ ∑ z, ∑ S ∈ I.feas, X I y t z S * max A ((1 - I.phi z S i) * A
        + I.phi z S i *
          ((1 / (I.c i : ℝ)) * ∑ d ∈ Finset.Icc 1 T,
              I.g z i d * (I.r z i + V I y i (t + d))
            + (((I.c i : ℝ) - 1) / (I.c i : ℝ)) * A)) :=
      Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun S hS =>
          mul_le_mul_of_nonneg_left (le_max_right _ _) (hX0 z S hS)
    have hmul := mul_le_mul_of_nonneg_left hge hc.le
    rw [sum_aux Finset.univ (fun _ => I.feas) (fun z S => X I y t z S) _
      (fun z S => I.phi z S i * I.r z i)
      (fun z S => I.phi z S i * ∑ d ∈ Finset.Icc 1 T, I.g z i d * (V I y i (t + d) - A))
      _ A hB, hXsum] at hmul
    simp only [← mul_assoc] at hmul ⊢
    linarith


private lemma Delta_nonneg (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPFeasible I y) (hN : Normalized I y)
    (i : Fin n) {s : ℕ} (hs : 1 ≤ s) : 0 ≤ V I y i s - V I y i (s + 1) := by
  by_cases h : s ≤ T
  · have := (V_step I hI y hy hN i (Finset.mem_Icc.mpr ⟨hs, h⟩)).1
    linarith
  · rw [V_gt I y i (by omega), V_gt I y i (by omega)]; simp

private lemma telescope (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (i : Fin n)
    {a b : ℕ} (hab : a ≤ b) :
    V I y i a - V I y i b = ∑ s ∈ Finset.Ico a b, (V I y i s - V I y i (s + 1)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ← ih]
    ring

private lemma ico_indicator (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (i : Fin n)
    (t d : ℕ) :
    ∑ s ∈ Finset.Ico (t + 1) (t + d), (V I y i s - V I y i (s + 1))
      = ∑ s ∈ Finset.Icc 1 T,
          if t < s ∧ s < t + d then V I y i s - V I y i (s + 1) else 0 := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_Icc] at hs
    simp only [Finset.mem_Ico]; omega
  · intro s hs hns
    simp only [Finset.mem_Ico] at hs
    have : T < s := by
      by_contra hc
      apply hns
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [V_gt I y i this, V_gt I y i (by omega)]; simp

private lemma Gbar_nonneg (I : Instance n T Z) (hI : I.Assumptions) (z : Z) (i : Fin n)
    (k : ℕ) : 0 ≤ Gbar I z i k :=
  Finset.sum_nonneg fun d _ => hI.g_nonneg z i d

/-- The coefficient of `𝒱_s - 𝒱_{s+1}` is at most `c_i`, by LP inventory feasibility. -/
private lemma coef_le (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPFeasible I y)
    (i : Fin n) {s : ℕ} (hs : s ∈ Finset.Icc 1 T) :
    ∑ t ∈ Finset.Icc 1 T, ∑ z, ∑ S ∈ I.feas, X I y t z S * I.phi z S i *
        ∑ d ∈ Finset.Icc 1 T, I.g z i d * (if t < s ∧ s < t + d then 1 else 0)
      ≤ (I.c i : ℝ) := by
  have hsT := (Finset.mem_Icc.mp hs).2
  have hg : ∀ t z, ∑ d ∈ Finset.Icc 1 T, I.g z i d * (if t < s ∧ s < t + d then 1 else 0)
      = if t < s then Gbar I z i (s - t) else 0 := by
    intro t z
    unfold Gbar
    rw [Finset.sum_filter]
    split_ifs with hts
    · refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hd : s - t < d
      · rw [if_pos ⟨hts, by omega⟩, if_pos hd, mul_one]
      · rw [if_neg (by omega), if_neg hd, mul_zero]
    · exact Finset.sum_eq_zero fun d _ => by rw [if_neg (by omega), mul_zero]
  set H : ℕ → ℝ := fun t => ∑ z, ∑ S ∈ I.feas,
    I.F t z * Gbar I z i (s - t) * I.phi z S i * y t z S with hH
  have hH0 : ∀ t ∈ Finset.Icc 1 T, 0 ≤ H t := by
    intro t ht
    refine Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun S hS => ?_
    have := hy.1 t ht z S hS
    have := hI.F_nonneg t z
    have := hI.phi_nonneg z S hS i
    have := Gbar_nonneg I hI z i (s - t)
    positivity
  have hterm : ∀ t ∈ Finset.Icc 1 T, (∑ z, ∑ S ∈ I.feas, X I y t z S * I.phi z S i *
        ∑ d ∈ Finset.Icc 1 T, I.g z i d * (if t < s ∧ s < t + d then 1 else 0))
      ≤ if t ≤ s then H t else 0 := by
    intro t ht
    simp_rw [hg]
    by_cases hts : t < s
    · rw [if_pos hts.le]
      simp only [hts, if_true, hH]
      exact le_of_eq (Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun S _ => by
        unfold X; ring)
    · simp only [hts, if_false, mul_zero, Finset.sum_const_zero]
      split_ifs
      · exact hH0 t ht
      · exact le_refl _
  calc _ ≤ ∑ t ∈ Finset.Icc 1 T, (if t ≤ s then H t else 0) := Finset.sum_le_sum hterm
    _ = ∑ t ∈ Finset.Icc 1 s, H t := by
        rw [← Finset.sum_filter]
        congr 1
        ext t
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
    _ ≤ (I.c i : ℝ) := by
        have := hy.2.1 i s hs
        refine le_trans (le_of_eq ?_) this
        rfl

end PartII

theorem solution {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]
    (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPFeasible I y) (hN : Normalized I y) :
    ∀ i, (1 / 2 : ℝ) * contrib I y i ≤ (I.c i : ℝ) * V I y i 1 := by
  intro i
  set Δ : ℕ → ℝ := fun s => V I y i s - V I y i (s + 1) with hΔ
  set c : ℝ := (I.c i : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  -- `𝒱_1 = Σ_t Δ_t`
  have hV1 : V I y i 1 = ∑ s ∈ Finset.Icc 1 T, Δ s := by
    have := telescope I y i (show 1 ≤ T + 1 by omega)
    rw [V_gt I y i (show T < T + 1 by omega), sub_zero] at this
    rw [this]
    rfl
  set a : ℕ → ℝ := fun t => ∑ z, ∑ S ∈ I.feas, X I y t z S * I.phi z S i * I.r z i with ha
  set E : ℕ → ℝ := fun t => ∑ z, ∑ S ∈ I.feas, X I y t z S * I.phi z S i *
      ∑ d ∈ Finset.Icc 1 T, I.g z i d *
        ∑ s ∈ Finset.Icc 1 T, (if t < s ∧ s < t + d then Δ s else 0) with hE
  have hstep : ∀ t ∈ Finset.Icc 1 T, a t - E t ≤ c * Δ t := by
    intro t ht
    have h2 := (V_step I hI y hy hN i ht).2
    have hQ : ∑ z, ∑ S ∈ I.feas, X I y t z S * I.phi z S i *
          ∑ d ∈ Finset.Icc 1 T, I.g z i d * (V I y i (t + d) - V I y i (t + 1)) = - E t := by
      simp only [hE, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun S _ => ?_
      rw [← mul_neg, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      rw [← mul_neg]
      congr 1
      have h1 := telescope I y i (show t + 1 ≤ t + d by omega)
      rw [ico_indicator I y i t d] at h1
      rw [← h1]; ring
    rw [hQ] at h2
    simpa [ha, hΔ] using (by linarith : a t - E t ≤ c * Δ t)
  -- swap the order of summation in `Σ_t E_t`
  have hswap : ∑ t ∈ Finset.Icc 1 T, E t = ∑ s ∈ Finset.Icc 1 T, Δ s *
      ∑ t ∈ Finset.Icc 1 T, ∑ z, ∑ S ∈ I.feas, X I y t z S * I.phi z S i *
        ∑ d ∈ Finset.Icc 1 T, I.g z i d * (if t < s ∧ s < t + d then 1 else 0) := by
    simp only [hE, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> ring
  have hEle : ∑ t ∈ Finset.Icc 1 T, E t ≤ c * V I y i 1 := by
    rw [hswap, hV1, Finset.mul_sum]
    refine Finset.sum_le_sum fun s hs => ?_
    have hΔ0 : 0 ≤ Δ s := Delta_nonneg I hI y hy hN i (Finset.mem_Icc.mp hs).1
    rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left (coef_le I hI y hy i hs) hΔ0
  have hsum : ∑ t ∈ Finset.Icc 1 T, (a t - E t) ≤ c * V I y i 1 := by
    rw [hV1, Finset.mul_sum]
    exact Finset.sum_le_sum hstep
  rw [Finset.sum_sub_distrib] at hsum
  have hcontrib : contrib I y i = ∑ t ∈ Finset.Icc 1 T, a t := by
    unfold contrib
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun z _ =>
      Finset.sum_congr rfl fun S _ => ?_
    unfold X; ring
  rw [hcontrib]
  linarith


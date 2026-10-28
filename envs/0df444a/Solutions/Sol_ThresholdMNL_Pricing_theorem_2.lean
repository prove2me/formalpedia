-- Prove2me | solution 1 for ThresholdMNL.Pricing.theorem_2
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-26T22:55:36.583669+00:00
-- url     : https://prove2.me/submissions/0fc049e5-525a-4147-8759-a9f0d8fd8c3b

import Mathlib
import Definitions.Def_ThresholdMNL_Pricing_Model

open ThresholdMNL.Pricing Finset Classical Real

lemma t2_top (a R v : ℝ) (hK : 0 ≤ a - R - 2) (hv1 : v ≤ 1) :
    (a - v - R) * exp v ≤ (a - 1 - R) * exp 1 := by
  have hd : exp 1 = exp v * exp (1 - v) := by rw [← exp_add]; ring_nf
  rw [hd]
  have h1 := add_one_le_exp (1 - v)
  have hev := exp_pos v
  have h2 : (a - v - R) ≤ (a - 1 - R) * exp (1 - v) := by nlinarith
  nlinarith

lemma t2_top_strict (a R v : ℝ) (hK : 0 ≤ a - R - 2) (hv1 : v < 1) :
    (a - v - R) * exp v < (a - 1 - R) * exp 1 := by
  have hd : exp 1 = exp v * exp (1 - v) := by rw [← exp_add]; ring_nf
  rw [hd]
  have h1 := add_one_lt_exp (show 1 - v ≠ 0 by linarith)
  have hev := exp_pos v
  have h2 : (a - v - R) < (a - 1 - R) * exp (1 - v) := by nlinarith
  nlinarith

lemma t2_bot (a R v : ℝ) (hK : a - R ≤ 1) (hv : 0 ≤ v) :
    (a - v - R) * exp v ≤ (a - R) := by
  have hd : exp v * exp (-v) = 1 := by rw [← exp_add]; simp
  have h1 := add_one_le_exp (-v)
  have h3 : exp (-v) ≤ 1 := by rw [exp_le_one_iff]; linarith
  have hev := exp_pos v
  have hen := exp_pos (-v)
  have h2 : (a - v - R) ≤ (a - R) * exp (-v) := by
    rcases le_or_gt (a - R) 0 with h | h
    · nlinarith
    · nlinarith
  calc (a - v - R) * exp v ≤ (a - R) * exp (-v) * exp v := by nlinarith
    _ = a - R := by rw [mul_assoc, mul_comm (exp (-v)), hd, mul_one]

lemma t2_neg_t (t : ℝ) : -t * exp (t + 1) ≤ 1 := by
  have h1 := add_one_le_exp (-(t+1))
  have hd : exp (t+1) * exp (-(t+1)) = 1 := by rw [← exp_add]; simp
  have he := exp_pos (t+1)
  nlinarith

noncomputable def t2A : Fin 4 → ℝ := ![13, 12, 11, 8 - 9 * exp 1]

lemma t2_sum_le (v : Fin 4 → ℝ) (h0 : ∀ i, 0 ≤ v i) (h1 : ∀ i, v i ≤ 1) :
    ∑ i, (t2A i - v i - 8) * exp (v i) ≤ 0 := by
  rw [Fin.sum_univ_four]
  have a0 := t2_top 13 8 (v 0) (by norm_num) (h1 0)
  have a1 := t2_top 12 8 (v 1) (by norm_num) (h1 1)
  have a2 := t2_top 11 8 (v 2) (by norm_num) (h1 2)
  have a3 := t2_bot (8 - 9 * exp 1) 8 (v 3) (by nlinarith [exp_pos 1]) (h0 3)
  simp only [t2A, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linarith

lemma t2_sum_lt (v : Fin 4 → ℝ) (h0 : ∀ i, 0 ≤ v i) (h1 : ∀ i, v i ≤ 1) (h2 : v 2 < 1) :
    ∑ i, (t2A i - v i - 8) * exp (v i) < 0 := by
  rw [Fin.sum_univ_four]
  have a0 := t2_top 13 8 (v 0) (by norm_num) (h1 0)
  have a1 := t2_top 12 8 (v 1) (by norm_num) (h1 1)
  have a2 := t2_top_strict 11 8 (v 2) (by norm_num) h2
  have a3 := t2_bot (8 - 9 * exp 1) 8 (v 3) (by nlinarith [exp_pos 1]) (h0 3)
  simp only [t2A, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linarith

/-- the window bound -/
lemma t2_window (x : Fin 4 → ℝ) (hw : ∀ i j, x j - 1 ≤ x i) (hl : ∀ i, -1 ≤ x i) :
    let M := max 0 (max (max (x 0) (x 1)) (max (x 2) (x 3)))
    (∀ i, x i ≤ M) ∧
    ∑ i, (t2A i - x i - 8) * exp (x i) ≤ -(M - 1) * ∑ i, exp (x i) := by
  intro M
  have hle : ∀ i, x i ≤ M := by
    intro i
    fin_cases i
    · exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    · exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hge : ∀ i, M - 1 ≤ x i := by
    intro i
    have : M ≤ x i + 1 := by
      refine max_le (by linarith [hl i]) (max_le (max_le ?_ ?_) (max_le ?_ ?_)) <;>
        linarith [hw i 0, hw i 1, hw i 2, hw i 3]
    linarith
  refine ⟨hle, ?_⟩
  set t := M - 1
  set v : Fin 4 → ℝ := fun i => x i - t
  have hs := t2_sum_le v (fun i => by simp only [v]; linarith [hge i])
    (fun i => by simp only [v]; linarith [hle i])
  have hid : ∀ i, (t2A i - x i - 8) * exp (x i) =
      exp t * ((t2A i - v i - 8) * exp (v i)) - t * exp (x i) := by
    intro i
    have : x i = v i + t := by simp only [v]; ring
    rw [this, exp_add]; ring
  rw [Finset.sum_congr rfl (fun i _ => hid i), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have := mul_nonpos_of_nonneg_of_nonpos (exp_pos t).le hs
  linarith

lemma t2_S : ordAssort 4 4 = univ := by
  ext i; simp [ordAssort]

lemma t1_profit_eq {N : ℕ} (S : Finset (Fin N)) (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) :
    profit S α c β u0 Δ p =
      (∑ i ∈ consSet S α β u0 Δ p, (p i - c i) * Real.exp (nomUtil α β p i))
        / consDenom S α β u0 Δ p := by
  unfold profit choiceProb
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have : InCons S α β u0 Δ p i := by
    unfold consSet at hi; exact (Finset.mem_filter.1 hi).2
  rw [if_pos this]; ring


lemma t2_profit (p : Fin 4 → ℝ)
    (hall : ∀ i ∈ ordAssort 4 4, InCons (ordAssort 4 4) t2A 1 0 1 p i) :
    profit (ordAssort 4 4) t2A 0 1 0 1 p =
      (∑ i, (t2A i - nomUtil t2A 1 p i) * exp (nomUtil t2A 1 p i)) /
      ((if OutsideInCons (ordAssort 4 4) t2A 1 0 1 p then 1 else 0) +
        ∑ i, exp (nomUtil t2A 1 p i)) := by
  have hcons : consSet (ordAssort 4 4) t2A 1 0 1 p = univ := by
    unfold consSet; rw [Finset.filter_true_of_mem hall, t2_S]
  rw [t1_profit_eq, hcons]
  unfold consDenom
  rw [hcons, Real.exp_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [nomUtil]

lemma t2_ub (p : Fin 4 → ℝ)
    (hall : ∀ i ∈ ordAssort 4 4, InCons (ordAssort 4 4) t2A 1 0 1 p i) :
    profit (ordAssort 4 4) t2A 0 1 0 1 p ≤ 8 := by
  rw [t2_profit p hall]
  set x : Fin 4 → ℝ := fun i => nomUtil t2A 1 p i with hx
  have hmem : ∀ i, i ∈ ordAssort 4 4 := fun i => by rw [t2_S]; exact mem_univ i
  have hw : ∀ i j, x j - 1 ≤ x i := fun i j => (hall i (hmem i)).2.2 j (hmem j)
  have hl : ∀ i, -1 ≤ x i := fun i => by
    have := (hall i (hmem i)).2.1; simp only [x]; linarith
  obtain ⟨hle, hF⟩ := t2_window x hw hl
  set M := max 0 (max (max (x 0) (x 1)) (max (x 2) (x 3))) with hM
  have hM0 : 0 ≤ M := le_max_left _ _
  set E := ∑ i, exp (x i) with hE
  have hEpos : 0 < E := Finset.sum_pos (fun i _ => exp_pos _) univ_nonempty
  have hsplit : ∑ i, (t2A i - x i - 8) * exp (x i) = ∑ i, (t2A i - x i) * exp (x i) - 8 * E := by
    rw [hE, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  by_cases hO : OutsideInCons (ordAssort 4 4) t2A 1 0 1 p
  · rw [if_pos hO]
    have hM1 : M ≤ 1 := by
      refine max_le (by norm_num) (max_le (max_le ?_ ?_) (max_le ?_ ?_)) <;>
        [have := hO 0 (hmem 0); have := hO 1 (hmem 1); have := hO 2 (hmem 2);
          have := hO 3 (hmem 3)] <;> simp only [x] <;> linarith
    have hEle : E ≤ 4 * exp M := by
      rw [hE, Fin.sum_univ_four]
      have := fun i => exp_le_exp.2 (hle i)
      linarith [this 0, this 1, this 2, this 3]
    have hneg := t2_neg_t (M - 1)
    have hMt : M - 1 + 1 = M := by ring
    rw [hMt] at hneg
    have h1 : -(M - 1) * E ≤ -(M - 1) * (4 * exp M) :=
      mul_le_mul_of_nonneg_left hEle (by linarith)
    rw [div_le_iff₀ (by linarith)]
    linarith
  · rw [if_neg hO, zero_add]
    have hM1 : 1 < M := by
      unfold OutsideInCons at hO
      push Not at hO
      obtain ⟨j, _, hj⟩ := hO
      have := hle j
      simp only [x] at this
      linarith
    have h1 : -(M - 1) * E ≤ 0 := by nlinarith
    rw [div_le_iff₀ hEpos]
    linarith

noncomputable def t2p (s : ℝ) : Fin 4 → ℝ := fun i => t2A i - (![1 + s, 1 + s, 1 + s, s] : Fin 4 → ℝ) i

lemma t2p_util (s : ℝ) (i : Fin 4) :
    nomUtil t2A 1 (t2p s) i = (![1 + s, 1 + s, 1 + s, s] : Fin 4 → ℝ) i := by
  simp [nomUtil, t2p]

lemma t2p_all (s : ℝ) (hs : 0 < s) :
    ∀ i ∈ ordAssort 4 4, InCons (ordAssort 4 4) t2A 1 0 1 (t2p s) i := by
  intro i hi
  refine ⟨hi, ?_, ?_⟩
  · rw [t2p_util]; fin_cases i <;> simp <;> linarith
  · intro j _
    rw [t2p_util, t2p_util]
    fin_cases i <;> fin_cases j <;> simp <;> linarith

lemma t2p_out (s : ℝ) (hs : 0 < s) : ¬ OutsideInCons (ordAssort 4 4) t2A 1 0 1 (t2p s) := by
  intro h
  have := h 0 (by rw [t2_S]; exact mem_univ _)
  rw [t2p_util] at this
  simp at this
  linarith

lemma t2p_profit (s : ℝ) (hs : 0 < s) : profit (ordAssort 4 4) t2A 0 1 0 1 (t2p s) = 8 - s := by
  rw [t2_profit _ (t2p_all s hs), if_neg (t2p_out s hs), zero_add]
  simp only [t2p_util, Fin.sum_univ_four]
  simp only [t2A, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have hpos : 0 < exp (1 + s) + exp (1 + s) + exp (1 + s) + exp s := by positivity
  rw [div_eq_iff hpos.ne', exp_add]
  ring

lemma t2_lub (P : (Fin 4 → ℝ) → Prop)
    (hP : ∀ p, P p → ∀ i ∈ ordAssort 4 4, InCons (ordAssort 4 4) t2A 1 0 1 p i)
    (hP2 : ∀ s, 0 < s → P (t2p s)) :
    IsLUB {x | ∃ p : Fin 4 → ℝ, P p ∧ x = profit (ordAssort 4 4) t2A 0 1 0 1 p} 8 := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨p, hp, rfl⟩; exact t2_ub p (hP p hp)
  · intro y hy
    by_contra hlt
    push Not at hlt
    have hs : 0 < (8 - y) / 2 := by linarith
    have := hy ⟨t2p ((8 - y) / 2), hP2 _ hs, (t2p_profit _ hs).symm⟩
    linarith

lemma t2_hord : Antitone fun i : Fin 4 => t2A i - 1 * (0 : Fin 4 → ℝ) i := by
  intro i j hij
  have he := exp_pos 1
  fin_cases i <;> fin_cases j <;> simp [t2A] at hij ⊢ <;> nlinarith


lemma t2_final (q : Fin 4 → ℝ)
    (hfeas : ∀ i ∈ ordAssort 4 4, (0:ℝ) ≤ nomUtil t2A 1 q i ∧ nomUtil t2A 1 q i ≤ 0 + 1)
    (h2 : nomUtil t2A 1 q 2 < 1) (hVeq : (8:ℝ) = exclProfit (ordAssort 4 4) t2A 0 1 q) : False := by
  have hmem : ∀ i, i ∈ ordAssort 4 4 := fun i => by rw [t2_S]; exact mem_univ i
  set u : Fin 4 → ℝ := fun i => nomUtil t2A 1 q i with hu
  unfold exclProfit at hVeq
  rw [t2_S] at hVeq
  have hD : 0 < ∑ i, exp (nomUtil t2A 1 q i) := Finset.sum_pos (fun i _ => exp_pos _) univ_nonempty
  rw [eq_div_iff hD.ne'] at hVeq
  have hlt := t2_sum_lt u (fun i => (hfeas i (hmem i)).1) (fun i => by
    have := (hfeas i (hmem i)).2; simp only [u]; linarith) h2
  have hid : ∑ i, (t2A i - u i - 8) * exp (u i) =
      ∑ i, (q i - (0 : Fin 4 → ℝ) i) * exp (nomUtil t2A 1 q i) - 8 * ∑ i, exp (nomUtil t2A 1 q i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [u, nomUtil, Pi.zero_apply]; ring
  linarith

theorem solution : ¬ (∀ {N : ℕ} (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (hβ : 0 < β) (hΔ : 0 ≤ Δ) (hord : Antitone fun i : Fin N => α i - β * c i)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (V : ℝ)
    (hV : IsLUB {x | ∃ p : Fin N → ℝ,
        (∀ i ∈ ordAssort N n, InCons (ordAssort N n) α β u0 Δ p i) ∧
        x = profit (ordAssort N n) α c β u0 Δ p} V)
    (hexcl : IsLUB {x | ∃ p : Fin N → ℝ,
        (∀ i ∈ ordAssort N n, InCons (ordAssort N n) α β u0 Δ p i) ∧
        ¬ OutsideInCons (ordAssort N n) α β u0 Δ p ∧
        x = profit (ordAssort N n) α c β u0 Δ p} V),
    let i₁ : Fin N := ⟨0, by omega⟩
    let m₁ : ℝ := (α i₁ - β * c i₁ - u0 - Δ) / β
    let pbar : ℕ → ℝ → Fin N → ℝ := fun n' m i =>
      if i.val = 0 then c i + m₁ else if i.val < n' then c i + m else (α i - u0) / β
    (n = 1 → V = m₁) ∧
    ∃ (n' : ℕ) (m : ℝ), 1 ≤ n' ∧ n' ≤ n ∧
      V = exclProfit (ordAssort N n) α c β (pbar n' m) ∧
      (∀ i ∈ ordAssort N n,
        u0 ≤ nomUtil α β (pbar n' m) i ∧ nomUtil α β (pbar n' m) i ≤ u0 + Δ) ∧
      (2 ≤ n' → ∃ m₀ : ℝ,
        StrictMonoOn (fun m' => exclProfit (ordAssort N n) α c β (pbar n' m')) (Set.Iic m₀) ∧
        StrictAntiOn (fun m' => exclProfit (ordAssort N n) α c β (pbar n' m')) (Set.Ici m₀))) := by
  intro h
  have hV := t2_lub (fun p => ∀ i ∈ ordAssort 4 4, InCons (ordAssort 4 4) t2A 1 0 1 p i)
    (fun p hp => hp) (fun s hs => t2p_all s hs)
  have hexcl := t2_lub (fun p => (∀ i ∈ ordAssort 4 4, InCons (ordAssort 4 4) t2A 1 0 1 p i) ∧
      ¬ OutsideInCons (ordAssort 4 4) t2A 1 0 1 p)
    (fun p hp => hp.1) (fun s hs => ⟨t2p_all s hs, t2p_out s hs⟩)
  have h' := @h 4 t2A 0 1 0 1 one_pos zero_le_one t2_hord 4 (by norm_num) le_rfl 8 hV
    (by simpa only [and_assoc] using hexcl)
  dsimp only at h'
  obtain ⟨_, n', m, hn'1, hn'4, hVeq, hfeas, _⟩ := h'
  refine t2_final _ hfeas ?_ hVeq
  have hmem : ∀ i, i ∈ ordAssort 4 4 := fun i => by rw [t2_S]; exact mem_univ i
  have f1 := (hfeas 1 (hmem 1)).2
  by_cases h2 : 2 < n'
  · have h1 : 1 < n' := by omega
    simp [nomUtil, t2A, h2, h1] at f1 ⊢
    linarith
  · simp [nomUtil, t2A, h2]

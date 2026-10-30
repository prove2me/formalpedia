-- Prove2me | solution 1 for ThresholdMNL.Pricing.theorem_4
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-29T06:01:44.621089+00:00
-- url     : https://prove2.me/submissions/da4dcd34-c8cd-4408-bc2e-c62d5ba9ccb6

import Mathlib
import Definitions.Def_ThresholdMNL_Pricing_Model

open ThresholdMNL.Pricing Finset Real Classical



namespace T4D

lemma L1 (c x : ℝ) : (c - x) * exp x ≤ exp (c - 1) := by
  have h := add_one_le_exp (c - 1 - x)
  have hd : exp (c - 1) = exp x * exp (c - 1 - x) := by rw [← exp_add]; ring_nf
  rw [hd]
  have := exp_pos x
  nlinarith

lemma L2 (c x s : ℝ) (hxs : x ≤ s) (hc : 1 ≤ c - s) : (c - x) * exp x ≤ (c - s) * exp s := by
  have hd : exp s = exp x * exp (s - x) := by rw [← exp_add]; ring_nf
  rw [hd]
  have h1 := add_one_le_exp (s - x)
  have hex := exp_pos x
  have h3 : 0 ≤ (c - s - 1) * (s - x) := mul_nonneg (by linarith) (by linarith)
  have h4 : 0 ≤ (c - s) * (exp (s - x) - (s - x + 1)) := mul_nonneg (by linarith) (by linarith)
  have h2 : c - x ≤ (c - s) * exp (s - x) := by nlinarith
  nlinarith

lemma L3 (c w z : ℝ) (hzw : z ≤ w) (h : c - z ≤ 1) : (c - w) * exp w ≤ (c - z) * exp z := by
  set d := w - z with hd
  have hw : w = z + d := by rw [hd]; ring
  rw [hw, exp_add]
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  set a := c - z with ha
  have hkey : (a - d) * exp d ≤ a := by
    have hdd : exp d * exp (-d) = 1 := by rw [← exp_add]; simp
    have h1 := add_one_le_exp (-d)
    have h3 : exp (-d) ≤ 1 := by rw [exp_le_one_iff]; linarith
    have hev := exp_pos d
    have hen := exp_pos (-d)
    have h2 : (a - d) ≤ a * exp (-d) := by
      rcases le_or_gt a 0 with h' | h'
      · nlinarith
      · nlinarith
    calc (a - d) * exp d ≤ a * exp (-d) * exp d := by nlinarith
      _ = a := by rw [mul_assoc, mul_comm (exp (-d)), hdd, mul_one]
  have hez := exp_pos z
  have : c - (z + d) = a - d := by rw [ha]; ring
  rw [this]
  nlinarith

lemma L4 (P Q s : ℝ) (hQ : 0 < Q) : (P - Q * s) * exp s ≤ Q * exp (P / Q - 1) := by
  have h := L1 (P / Q) s
  have he : (P - Q * s) * exp s = Q * ((P / Q - s) * exp s) := by field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left h hQ.le

lemma exp_ub4 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 * 5 / 96 := by
  have := Real.exp_bound' h0 h1 (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  norm_num at this
  linarith

lemma exp_neg_ub4 (g : ℝ) (h0 : 0 ≤ g) (h1 : g ≤ 1) :
    exp (-g) ≤ 1 - g + g ^ 2 / 2 - g ^ 3 / 6 + g ^ 4 * 5 / 96 := by
  have hg : |(-g)| ≤ 1 := by rw [abs_neg, abs_of_nonneg h0]; exact h1
  have := Real.exp_bound hg (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  rw [abs_neg, abs_of_nonneg h0] at this
  have := (abs_le.1 this).2
  norm_num at this
  linarith

lemma exp_neg_le_inv (a : ℝ) (ha : 0 ≤ a) : exp (-a) ≤ 1 / (1 + a) := by
  rw [exp_neg, ← one_div]
  apply one_div_le_one_div_of_le (by linarith)
  linarith [add_one_le_exp a]

noncomputable def Dl : ℝ := Real.log (19 / 4)

lemma exp_Dl : exp Dl = 19 / 4 := by
  unfold Dl; rw [exp_log (by norm_num)]

lemma Dl_lb : 155 / 100 ≤ Dl := by
  unfold Dl
  rw [le_log_iff_exp_le (by norm_num)]
  have h : exp (155 / 100) = exp (775 / 1000) * exp (775 / 1000) := by
    rw [← exp_add]; norm_num
  rw [h]
  have h1 := exp_ub4 (775 / 1000) (by norm_num) (by norm_num)
  have h2 := exp_pos (775 / 1000 : ℝ)
  have h3 : exp (775 / 1000 : ℝ) * exp (775 / 1000) ≤
      (1 + 775 / 1000 + (775 / 1000) ^ 2 / 2 + (775 / 1000) ^ 3 / 6 + (775 / 1000) ^ 4 * 5 / 96) *
      (1 + 775 / 1000 + (775 / 1000) ^ 2 / 2 + (775 / 1000) ^ 3 / 6 + (775 / 1000) ^ 4 * 5 / 96) :=
    mul_le_mul h1 h1 h2.le (by positivity)
  have h4 : (1 + 775 / 1000 + (775 / 1000 : ℝ) ^ 2 / 2 + (775 / 1000) ^ 3 / 6 +
      (775 / 1000) ^ 4 * 5 / 96) *
      (1 + 775 / 1000 + (775 / 1000 : ℝ) ^ 2 / 2 + (775 / 1000) ^ 3 / 6 +
      (775 / 1000) ^ 4 * 5 / 96) ≤ 19 / 4 := by norm_num
  linarith

lemma Dl_pos : 0 < Dl := by linarith [Dl_lb]

/-- the bound value -/
noncomputable def LL : ℝ := 32187 / 10000

lemma e983 : exp (983 / 10000 : ℝ) ≤ 1103300 / 1000000 := by
  have := exp_ub4 (983 / 10000) (by norm_num) (by norm_num)
  have h : (1 + 983 / 10000 + (983 / 10000 : ℝ) ^ 2 / 2 + (983 / 10000) ^ 3 / 6 +
    (983 / 10000) ^ 4 * 5 / 96) ≤ 1103300 / 1000000 := by norm_num
  linarith

lemma e103 : exp (103 / 10000 : ℝ) ≤ 1010354 / 1000000 := by
  have := exp_ub4 (103 / 10000) (by norm_num) (by norm_num)
  have h : (1 + 103 / 10000 + (103 / 10000 : ℝ) ^ 2 / 2 + (103 / 10000) ^ 3 / 6 +
    (103 / 10000) ^ 4 * 5 / 96) ≤ 1010354 / 1000000 := by norm_num
  linarith

/-- rho = exp(-g), g = 88/1000 -/
lemma erho : exp (-(88 / 1000 : ℝ)) ≤ 9157616 / 10000000 := by
  have := exp_neg_ub4 (88 / 1000) (by norm_num) (by norm_num)
  have h : (1 - 88 / 1000 + (88 / 1000 : ℝ) ^ 2 / 2 - (88 / 1000) ^ 3 / 6 +
    (88 / 1000) ^ 4 * 5 / 96) ≤ 9157616 / 10000000 := by norm_num
  linarith

/-- the tight constant. P = c0 + c1 (1 + ρ) + δ'/K, Q = 2 + ρ + 1/K with ρ = 9157616/10^7. -/
lemma N4 : (2 + 9157616 / 10000000 + 4 / 19 : ℝ) *
    exp ((10983 / 10000 + 10983 / 10000 * (1 + 9157616 / 10000000) + 643 / 10000 * (4 / 19)) /
      (2 + 9157616 / 10000000 + 4 / 19) - 1) ≤ 32187 / 10000 := by
  set x : ℝ := (10983 / 10000 + 10983 / 10000 * (1 + 9157616 / 10000000) + 643 / 10000 * (4 / 19)) /
      (2 + 9157616 / 10000000 + 4 / 19) - 1 with hx
  have hx0 : 0 ≤ x := by rw [hx]; norm_num
  have hx1 : x ≤ 1 := by rw [hx]; norm_num
  have := exp_ub4 x hx0 hx1
  have h : (2 + 9157616 / 10000000 + 4 / 19 : ℝ) * (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 * 5 / 96)
      ≤ 32187 / 10000 := by rw [hx]; norm_num
  have hQ : (0 : ℝ) < 2 + 9157616 / 10000000 + 4 / 19 := by norm_num
  nlinarith

end T4D



namespace T4D

noncomputable def A : Fin 4 → ℝ := ![4317 / 1000, 4317 / 1000, 4229 / 1000, 3283 / 1000 - Dl]

lemma hA0 : A 0 = 4317 / 1000 := by simp [A]
lemma hA1 : A 1 = 4317 / 1000 := by simp [A]
lemma hA2 : A 2 = 4229 / 1000 := by simp [A]
lemma hA3 : A 3 = 3283 / 1000 - Dl := by simp [A]

lemma u_eq (p : Fin 4 → ℝ) (i : Fin 4) : nomUtil A 1 p i = A i - p i := by
  simp [nomUtil]

noncomputable def F (p : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  (A i - nomUtil A 1 p i - LL) * exp (nomUtil A 1 p i)

noncomputable def G (S : Finset (Fin 4)) (p : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  if InCons S A 1 0 Dl p i then F p i else 0

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

lemma sum_cons (S : Finset (Fin 4)) (p : Fin 4 → ℝ) (f : Fin 4 → ℝ) :
    ∑ i ∈ consSet S A 1 0 Dl p, f i = ∑ i : Fin 4, if InCons S A 1 0 Dl p i then f i else 0 := by
  unfold consSet
  rw [Finset.sum_filter]
  apply Finset.sum_subset (Finset.subset_univ S)
  intro x _ hx
  rw [if_neg]
  intro h; exact hx h.1

lemma LL_pos : (0 : ℝ) < LL := by unfold LL; norm_num

lemma profit_le (S : Finset (Fin 4)) (p : Fin 4 → ℝ)
    (h : ∑ i : Fin 4, G S p i ≤ LL * (if OutsideInCons S A 1 0 Dl p then 1 else 0)) :
    profit S A 0 1 0 Dl p ≤ LL := by
  rw [t1_profit_eq]
  have hnum := sum_cons S p (fun i => F p i)
  have hsplit : ∑ i ∈ consSet S A 1 0 Dl p, F p i
      = ∑ i ∈ consSet S A 1 0 Dl p, (p i - (0 : Fin 4 → ℝ) i) * exp (nomUtil A 1 p i)
        - LL * ∑ i ∈ consSet S A 1 0 Dl p, exp (nomUtil A 1 p i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [F, nomUtil, Pi.zero_apply]; ring
  have hDdef : consDenom S A 1 0 Dl p = (if OutsideInCons S A 1 0 Dl p then 1 else 0) +
      ∑ i ∈ consSet S A 1 0 Dl p, exp (nomUtil A 1 p i) := by
    unfold consDenom; rw [Real.exp_zero]
  have hE0 : 0 ≤ ∑ i ∈ consSet S A 1 0 Dl p, exp (nomUtil A 1 p i) :=
    Finset.sum_nonneg (fun i _ => (exp_pos _).le)
  have hI0 : (0 : ℝ) ≤ (if OutsideInCons S A 1 0 Dl p then 1 else 0) := by
    split_ifs <;> norm_num
  have hD0 : 0 ≤ consDenom S A 1 0 Dl p := by rw [hDdef]; linarith
  have hG : ∑ i ∈ consSet S A 1 0 Dl p, F p i = ∑ i : Fin 4, G S p i := by
    rw [hnum]; rfl
  rcases hD0.lt_or_eq with hDp | hDz
  · rw [div_le_iff₀ hDp, hDdef, mul_add]
    linarith
  · rw [← hDz, div_zero]; exact LL_pos.le

/-- bound for a considered product, used generally -/
lemma F_le_L1 (p : Fin 4 → ℝ) (i : Fin 4) : F p i ≤ exp (A i - LL - 1) := by
  unfold F
  have := L1 (A i - LL) (nomUtil A 1 p i)
  have e : A i - nomUtil A 1 p i - LL = A i - LL - nomUtil A 1 p i := by ring
  rw [e]; linarith

lemma G_le_L1 (S : Finset (Fin 4)) (p : Fin 4 → ℝ) (i : Fin 4) :
    G S p i ≤ exp (A i - LL - 1) := by
  unfold G; split_ifs
  · exact F_le_L1 p i
  · exact (exp_pos _).le

lemma eA0 : exp (A 0 - LL - 1) ≤ 1103300 / 1000000 := by
  have : A 0 - LL - 1 = 983 / 10000 := by rw [hA0]; unfold LL; norm_num
  rw [this]; exact e983

lemma eA1 : exp (A 1 - LL - 1) ≤ 1103300 / 1000000 := by
  have : A 1 - LL - 1 = 983 / 10000 := by rw [hA1]; unfold LL; norm_num
  rw [this]; exact e983

lemma eA2 : exp (A 2 - LL - 1) ≤ 1010354 / 1000000 := by
  have : A 2 - LL - 1 = 103 / 10000 := by rw [hA2]; unfold LL; norm_num
  rw [this]; exact e103

/-- Family bound 0: product 3 not considered. -/
lemma fb0 (S : Finset (Fin 4)) (p : Fin 4 → ℝ) (h3 : ¬ InCons S A 1 0 Dl p 3) :
    ∑ i : Fin 4, G S p i ≤ LL := by
  rw [Fin.sum_univ_four]
  have g3 : G S p 3 = 0 := by unfold G; rw [if_neg h3]
  have := G_le_L1 S p 0
  have := G_le_L1 S p 1
  have := G_le_L1 S p 2
  have := eA0; have := eA1; have := eA2
  unfold LL at *
  linarith

lemma incons_congr (S : Finset (Fin 4)) (p : Fin 4 → ℝ) (i k : Fin 4) (hi : i ∈ S) (hk : k ∈ S)
    (h : nomUtil A 1 p i = nomUtil A 1 p k) :
    InCons S A 1 0 Dl p i ↔ InCons S A 1 0 Dl p k := by
  unfold InCons; rw [h]; simp [hi, hk]

lemma mem4 (i : Fin 4) : i ∈ ordAssort 4 4 := by simp [ordAssort]

/-- Family bound 1: products 1, 2, 3 share a utility. -/
lemma fb1 (p : Fin 4 → ℝ) (h12 : nomUtil A 1 p 1 = nomUtil A 1 p 2)
    (h13 : nomUtil A 1 p 1 = nomUtil A 1 p 3) :
    ∑ i : Fin 4, G (ordAssort 4 4) p i ≤ LL := by
  rw [Fin.sum_univ_four]
  have g0 := G_le_L1 (ordAssort 4 4) p 0
  have := eA0
  have hgrp : G (ordAssort 4 4) p 1 + G (ordAssort 4 4) p 2 + G (ordAssort 4 4) p 3 ≤
      3 * (1 / (1 + 79 / 100)) := by
    have i12 := incons_congr (ordAssort 4 4) p 1 2 (mem4 1) (mem4 2) h12
    have i13 := incons_congr (ordAssort 4 4) p 1 3 (mem4 1) (mem4 3) h13
    unfold G
    by_cases hI : InCons (ordAssort 4 4) A 1 0 Dl p 1
    · rw [if_pos hI, if_pos (i12.1 hI), if_pos (i13.1 hI)]
      set w := nomUtil A 1 p 1 with hw
      have hsum : F p 1 + F p 2 + F p 3 =
          ((A 1 + A 2 + A 3 - 3 * LL) - 3 * w) * exp w := by
        unfold F; rw [← h12, ← h13]; ring
      rw [hsum]
      have h4 := L4 (A 1 + A 2 + A 3 - 3 * LL) 3 w (by norm_num)
      have hx : (A 1 + A 2 + A 3 - 3 * LL) / 3 - 1 ≤ -(79 / 100) := by
        rw [hA1, hA2, hA3]; unfold LL; linarith [Dl_lb]
      have h5 := exp_le_exp.2 hx
      have h6 := exp_neg_le_inv (79 / 100) (by norm_num)
      linarith
    · rw [if_neg hI, if_neg (fun h => hI (i12.2 h)), if_neg (fun h => hI (i13.2 h))]
      norm_num
  unfold LL at *
  have : (3 : ℝ) * (1 / (1 + 79 / 100)) ≤ 168 / 100 := by norm_num
  linarith

/-- Family bound 2: products 2, 3 share a utility. -/
lemma fb2 (p : Fin 4 → ℝ) (h23 : nomUtil A 1 p 2 = nomUtil A 1 p 3) :
    ∑ i : Fin 4, G (ordAssort 4 4) p i ≤ LL := by
  rw [Fin.sum_univ_four]
  have g0 := G_le_L1 (ordAssort 4 4) p 0
  have g1 := G_le_L1 (ordAssort 4 4) p 1
  have := eA0; have := eA1
  have hgrp : G (ordAssort 4 4) p 2 + G (ordAssort 4 4) p 3 ≤ 2 * (1 / (1 + 123 / 100)) := by
    have i23 := incons_congr (ordAssort 4 4) p 2 3 (mem4 2) (mem4 3) h23
    unfold G
    by_cases hI : InCons (ordAssort 4 4) A 1 0 Dl p 2
    · rw [if_pos hI, if_pos (i23.1 hI)]
      set w := nomUtil A 1 p 2 with hw
      have hsum : F p 2 + F p 3 = ((A 2 + A 3 - 2 * LL) - 2 * w) * exp w := by
        unfold F; rw [← h23]; ring
      rw [hsum]
      have h4 := L4 (A 2 + A 3 - 2 * LL) 2 w (by norm_num)
      have hx : (A 2 + A 3 - 2 * LL) / 2 - 1 ≤ -(123 / 100) := by
        rw [hA2, hA3]; unfold LL; linarith [Dl_lb]
      have h5 := exp_le_exp.2 hx
      have h6 := exp_neg_le_inv (123 / 100) (by norm_num)
      linarith
    · rw [if_neg hI, if_neg (fun h => hI (i23.2 h))]
      norm_num
  unfold LL at *
  have : (2 : ℝ) * (1 / (1 + 123 / 100)) ≤ 897 / 1000 := by norm_num
  linarith

end T4D



namespace T4D

/-- Family bound 3: products 1, 2 share a markup (the tight family). -/
lemma fb3 (p : Fin 4 → ℝ) (h12 : p 1 = p 2) :
    ∑ i : Fin 4, G (ordAssort 4 4) p i ≤ LL := by
  rw [Fin.sum_univ_four]
  set S := ordAssort 4 4 with hS
  have hu2 : nomUtil A 1 p 2 = nomUtil A 1 p 1 - 88 / 1000 := by
    rw [u_eq, u_eq, hA1, hA2, ← h12]; ring
  set s := max (max 0 (nomUtil A 1 p 0)) (max (nomUtil A 1 p 1) (nomUtil A 1 p 3)) with hs
  have hs0 : 0 ≤ s := le_trans (le_max_left _ _) (le_max_left _ _)
  have hs_0 : nomUtil A 1 p 0 ≤ s := le_trans (le_max_right _ _) (le_max_left _ _)
  have hs_1 : nomUtil A 1 p 1 ≤ s := le_trans (le_max_left _ _) (le_max_right _ _)
  have hs_3 : nomUtil A 1 p 3 ≤ s := le_trans (le_max_right _ _) (le_max_right _ _)
  -- bound on product 3's term when it is considered
  have hF3 : InCons S A 1 0 Dl p 3 → F p 3 ≤ (643 / 10000 - s) * exp s * (4 / 19) := by
    intro hI
    have hlow : s - Dl ≤ nomUtil A 1 p 3 := by
      have a0 := hI.2.2 0 (mem4 0)
      have a1 := hI.2.2 1 (mem4 1)
      have a3 := hI.2.1
      have : s ≤ nomUtil A 1 p 3 + Dl := by
        refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> linarith [Dl_pos]
      linarith
    have h := L3 (A 3 - LL) (nomUtil A 1 p 3) (s - Dl) hlow (by
      rw [hA3]; unfold LL; linarith)
    unfold F
    have e1 : A 3 - nomUtil A 1 p 3 - LL = A 3 - LL - nomUtil A 1 p 3 := by ring
    have e2 : A 3 - LL - (s - Dl) = 643 / 10000 - s := by rw [hA3]; unfold LL; ring
    have e3 : exp (s - Dl) = exp s * (4 / 19) := by
      rw [exp_sub, exp_Dl]; field_simp
    rw [e1]; rw [e2, e3] at h; linarith
  by_cases hc : InCons S A 1 0 Dl p 3 ∧ s ≤ 643 / 10000
  · obtain ⟨hI3, hsd⟩ := hc
    have hc0 : 1 ≤ 10983 / 10000 - s := by linarith
    have hcs : (0 : ℝ) ≤ (10983 / 10000 - s) * exp s := by
      have := exp_pos s; nlinarith
    have g3 : G S p 3 ≤ (643 / 10000 - s) * exp s * (4 / 19) := by
      unfold G; rw [if_pos hI3]; exact hF3 hI3
    have g0 : G S p 0 ≤ (10983 / 10000 - s) * exp s := by
      unfold G; split_ifs
      · unfold F
        have := L2 (A 0 - LL) (nomUtil A 1 p 0) s hs_0 (by rw [hA0]; unfold LL; linarith)
        have e : A 0 - LL = 10983 / 10000 := by rw [hA0]; unfold LL; norm_num
        rw [e] at this
        have e1 : A 0 - nomUtil A 1 p 0 - LL = 10983 / 10000 - nomUtil A 1 p 0 := by
          rw [← e]; ring
        rw [e1]; exact this
      · exact hcs
    have hF1 : F p 1 ≤ (10983 / 10000 - s) * exp s := by
      unfold F
      have := L2 (A 1 - LL) (nomUtil A 1 p 1) s hs_1 (by rw [hA1]; unfold LL; linarith)
      have e : A 1 - LL = 10983 / 10000 := by rw [hA1]; unfold LL; norm_num
      rw [e] at this
      have e1 : A 1 - nomUtil A 1 p 1 - LL = 10983 / 10000 - nomUtil A 1 p 1 := by
        rw [← e]; ring
      rw [e1]; exact this
    have g1 : G S p 1 ≤ (10983 / 10000 - s) * exp s := by
      unfold G; split_ifs
      · exact hF1
      · exact hcs
    have g2 : G S p 2 ≤ (10983 / 10000 - s) * exp s * (9157616 / 10000000) := by
      have hF2 : F p 2 = F p 1 * exp (-(88 / 1000)) := by
        unfold F
        rw [hu2]
        have : A 2 - (nomUtil A 1 p 1 - 88 / 1000) - LL = A 1 - nomUtil A 1 p 1 - LL := by
          rw [hA1, hA2]; ring
        rw [this, show nomUtil A 1 p 1 - 88 / 1000 = nomUtil A 1 p 1 + -(88 / 1000) by ring,
          exp_add]
        ring
      have hr := erho
      have hrp := exp_pos (-(88 / 1000 : ℝ))
      unfold G; split_ifs
      · rw [hF2]
        calc F p 1 * exp (-(88 / 1000)) ≤ (10983 / 10000 - s) * exp s * exp (-(88 / 1000)) :=
              mul_le_mul_of_nonneg_right hF1 hrp.le
          _ ≤ (10983 / 10000 - s) * exp s * (9157616 / 10000000) :=
              mul_le_mul_of_nonneg_left hr hcs
      · positivity
    -- combine
    have hcomb : (10983 / 10000 - s) * exp s + (10983 / 10000 - s) * exp s +
        (10983 / 10000 - s) * exp s * (9157616 / 10000000) +
        (643 / 10000 - s) * exp s * (4 / 19) =
        ((10983 / 10000 + 10983 / 10000 * (1 + 9157616 / 10000000) + 643 / 10000 * (4 / 19)) -
          (2 + 9157616 / 10000000 + 4 / 19) * s) * exp s := by ring
    have h4 := L4 (10983 / 10000 + 10983 / 10000 * (1 + 9157616 / 10000000) + 643 / 10000 * (4 / 19))
      (2 + 9157616 / 10000000 + 4 / 19) s (by norm_num)
    have h5 := N4
    unfold LL
    linarith
  · have g3 : G S p 3 ≤ 0 := by
      unfold G; split_ifs with hI
      · have hgt : 643 / 10000 < s := by
          by_contra hh; exact hc ⟨hI, not_lt.1 hh⟩
        have := hF3 hI
        have : (643 / 10000 - s) * exp s * (4 / 19) ≤ 0 := by
          have := exp_pos s; nlinarith
        linarith
      · exact le_rfl
    have g0 := G_le_L1 S p 0
    have g1 := G_le_L1 S p 1
    have g2 := G_le_L1 S p 2
    have := eA0; have := eA1; have := eA2
    unfold LL at *
    linarith

/-- the outside option is not considered: the sum is nonpositive. -/
lemma noout (S : Finset (Fin 4)) (p : Fin 4 → ℝ) (hO : ¬ OutsideInCons S A 1 0 Dl p) :
    ∑ i : Fin 4, G S p i ≤ 0 := by
  unfold OutsideInCons at hO
  push Not at hO
  obtain ⟨j0, hj0S, hj0⟩ := hO
  obtain ⟨j, hjS, hjmax⟩ := Finset.exists_max_image S (fun i => nomUtil A 1 p i) ⟨j0, hj0S⟩
  have hjj0 := hjmax j0 hj0S
  set t := nomUtil A 1 p j - Dl with ht
  have htpos : 0 < t := by linarith
  have het : 1 ≤ exp t := by linarith [add_one_le_exp t]
  have hIj : InCons S A 1 0 Dl p j :=
    ⟨hjS, by linarith [Dl_pos], fun k hk => by have := hjmax k hk; linarith [Dl_pos]⟩
  have hlow : ∀ i, InCons S A 1 0 Dl p i → t ≤ nomUtil A 1 p i := fun i hi => hi.2.2 j hjS
  have hT : ∀ i : Fin 4, G S p i ≤ exp t * exp (A i - LL - 1) := by
    intro i
    have := G_le_L1 S p i
    have := exp_pos (A i - LL - 1)
    nlinarith
  have h3 : G S p 3 ≤ 0 := by
    unfold G; split_ifs with hI
    · have := hlow 3 hI
      unfold F
      have : A 3 - nomUtil A 1 p 3 - LL < 0 := by rw [hA3]; unfold LL; linarith [Dl_lb]
      have := exp_pos (nomUtil A 1 p 3)
      nlinarith
    · exact le_rfl
  have htop : G S p j ≤ exp t * ((A j - LL - Dl) * (19 / 4)) := by
    unfold G; rw [if_pos hIj]; unfold F
    have hu : nomUtil A 1 p j = t + Dl := by rw [ht]; ring
    rw [hu, exp_add, exp_Dl]
    have := exp_pos t
    nlinarith
  have he0 := eA0; have he1 := eA1; have he2 := eA2
  have hDl := Dl_lb
  have hx0 : exp t * exp (A 0 - LL - 1) ≤ exp t * (1103300 / 1000000) :=
    mul_le_mul_of_nonneg_left he0 (exp_pos t).le
  have hx1 : exp t * exp (A 1 - LL - 1) ≤ exp t * (1103300 / 1000000) :=
    mul_le_mul_of_nonneg_left he1 (exp_pos t).le
  have hx2 : exp t * exp (A 2 - LL - 1) ≤ exp t * (1010354 / 1000000) :=
    mul_le_mul_of_nonneg_left he2 (exp_pos t).le
  have hjc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by fin_cases j <;> simp
  rw [Fin.sum_univ_four]
  have hep := exp_pos t
  rcases hjc with rfl | rfl | rfl | rfl
  · have k := hT 1; have k2 := hT 2
    rw [hA0] at htop; unfold LL at htop
    have : exp t * ((4317 / 1000 - 32187 / 10000 - Dl) * (19 / 4)) + exp t * (1103300 / 1000000)
        + exp t * (1010354 / 1000000) ≤ 0 := by nlinarith
    linarith
  · have k := hT 0; have k2 := hT 2
    rw [hA1] at htop; unfold LL at htop
    have : exp t * ((4317 / 1000 - 32187 / 10000 - Dl) * (19 / 4)) + exp t * (1103300 / 1000000)
        + exp t * (1010354 / 1000000) ≤ 0 := by nlinarith
    linarith
  · have k := hT 0; have k2 := hT 1
    rw [hA2] at htop; unfold LL at htop
    have : exp t * ((4229 / 1000 - 32187 / 10000 - Dl) * (19 / 4)) + exp t * (1103300 / 1000000)
        + exp t * (1103300 / 1000000) ≤ 0 := by nlinarith
    linarith
  · have k := hT 0; have k1 := hT 1; have k2 := hT 2
    rw [hA3] at htop; unfold LL at htop
    have : exp t * ((3283 / 1000 - Dl - 32187 / 10000 - Dl) * (19 / 4)) +
        exp t * (1103300 / 1000000) + exp t * (1103300 / 1000000)
        + exp t * (1010354 / 1000000) ≤ 0 := by nlinarith
    linarith

lemma bound_of (S : Finset (Fin 4)) (p : Fin 4 → ℝ) (h : ∑ i : Fin 4, G S p i ≤ LL) :
    profit S A 0 1 0 Dl p ≤ LL := by
  apply profit_le
  by_cases hO : OutsideInCons S A 1 0 Dl p
  · rw [if_pos hO, mul_one]; exact h
  · rw [if_neg hO, mul_zero]; exact noout S p hO

lemma qsmsu_bound (n : ℕ) (hn1 : 1 ≤ n) (hn4 : n ≤ 4) (n' : ℕ) (p : Fin 4 → ℝ)
    (hq : IsQuasiSameMarkupSameUtility A 0 1 n n' p) :
    profit (ordAssort 4 n) A 0 1 0 Dl p ≤ LL := by
  apply bound_of
  have hnot3 : n ≤ 3 → ¬ InCons (ordAssort 4 n) A 1 0 Dl p 3 := by
    intro hn h
    have := h.1
    simp [ordAssort] at this
    omega
  interval_cases n
  · exact fb0 _ p (hnot3 (by norm_num))
  · exact fb0 _ p (hnot3 (by norm_num))
  · exact fb0 _ p (hnot3 (by norm_num))
  · obtain ⟨h1, h2, _, hM, hU⟩ := hq
    interval_cases n'
    · exact fb1 p (hU 1 2 (by decide) (by decide) (by decide) (by decide))
        (hU 1 3 (by decide) (by decide) (by decide) (by decide))
    · exact fb2 p (hU 2 3 (by decide) (by decide) (by decide) (by decide))
    · have := hM 1 2 (by decide) (by decide) (by decide) (by decide)
      simp only [Pi.zero_apply, sub_zero] at this
      exact fb3 p this
    · have := hM 1 3 (by decide) (by decide) (by decide) (by decide)
      simp only [Pi.zero_apply, sub_zero] at this
      apply fb0
      intro h
      have a := h.2.2 1 (mem4 1)
      rw [u_eq, u_eq, hA1, hA3, this] at a
      linarith [Dl_pos]

noncomputable def pstar : Fin 4 → ℝ := ![4317 / 1000, 4317 / 1000, 4229 / 1000, 3283 / 1000]

lemma ustar (i : Fin 4) : nomUtil A 1 pstar i = (![0, 0, 0, -Dl] : Fin 4 → ℝ) i := by
  rw [u_eq]; fin_cases i <;> simp [A, pstar]

lemma S4 : ordAssort 4 4 = univ := by ext i; simp [ordAssort]

lemma pstar_all : ∀ i, InCons (ordAssort 4 4) A 1 0 Dl pstar i := by
  intro i
  refine ⟨mem4 i, ?_, ?_⟩
  · rw [ustar]; fin_cases i <;> simp <;> linarith [Dl_pos]
  · intro j _
    rw [ustar, ustar]
    fin_cases i <;> fin_cases j <;> simp <;> linarith [Dl_pos]

lemma pstar_out : OutsideInCons (ordAssort 4 4) A 1 0 Dl pstar := by
  intro j _
  rw [ustar]; fin_cases j <;> simp <;> linarith [Dl_pos]

noncomputable def Rc : ℝ :=
  (4317 / 1000 + 4317 / 1000 + 4229 / 1000 + 3283 / 1000 * (4 / 19)) / (1 + (3 + 4 / 19))

lemma profit_pstar : profit (ordAssort 4 4) A 0 1 0 Dl pstar = Rc := by
  rw [t1_profit_eq]
  have hcons : consSet (ordAssort 4 4) A 1 0 Dl pstar = univ := by
    unfold consSet; rw [Finset.filter_true_of_mem (fun i _ => pstar_all i), S4]
  unfold consDenom
  rw [hcons, if_pos pstar_out, Real.exp_zero]
  simp only [Fin.sum_univ_four, ustar, Pi.zero_apply, sub_zero]
  simp [pstar, exp_neg, exp_Dl]
  unfold Rc
  norm_num

lemma Rc_gt : LL < Rc := by unfold LL Rc; norm_num

lemma hordA : Antitone fun i : Fin 4 => A i - 1 * (0 : Fin 4 → ℝ) i := by
  intro i j hij
  have := Dl_pos
  fin_cases i <;> fin_cases j <;> simp [A] at hij ⊢ <;> linarith

end T4D

open T4D in
theorem solution : ¬ (∀ {N : ℕ} (hN : 1 ≤ N) (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (hβ : 0 < β) (hΔ : 0 ≤ Δ) (hord : Antitone fun i : Fin N => α i - β * c i),
    ∃ V : ℝ,
      IsLUB {x | ∃ (S : Finset (Fin N)) (p : Fin N → ℝ), x = profit S α c β u0 Δ p} V ∧
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧
        IsLUB {x | ∃ p : Fin N → ℝ, x = profit (ordAssort N n) α c β u0 Δ p} V ∧
        IsLUB {x | ∃ (n' : ℕ) (p : Fin N → ℝ),
            IsQuasiSameMarkupSameUtility α c β n n' p ∧
            x = profit (ordAssort N n) α c β u0 Δ p} V ∧
        ((∃ (S : Finset (Fin N)) (p : Fin N → ℝ), profit S α c β u0 Δ p = V) →
          ∃ (n' : ℕ) (p : Fin N → ℝ), IsQuasiSameMarkupSameUtility α c β n n' p ∧
            profit (ordAssort N n) α c β u0 Δ p = V)) := by
  intro h
  obtain ⟨V, hV, n, hn1, hn4, _, hQ, _⟩ :=
    @h 4 (by norm_num) A 0 1 0 Dl one_pos Dl_pos.le hordA
  have h1 : Rc ≤ V := hV.1 ⟨ordAssort 4 4, pstar, profit_pstar.symm⟩
  have h2 : V ≤ LL := by
    apply hQ.2
    rintro x ⟨n', p, hq, rfl⟩
    exact qsmsu_bound n hn1 hn4 n' p hq
  linarith [Rc_gt]

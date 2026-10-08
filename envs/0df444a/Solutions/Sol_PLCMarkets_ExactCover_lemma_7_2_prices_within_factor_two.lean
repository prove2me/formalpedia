-- Prove2me | solution 1 for PLCMarkets.ExactCover.lemma_7_2_prices_within_factor_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T15:52:06.370285+00:00
-- url     : https://prove2.me/submissions/63bdd025-4035-40b2-b63d-eb4a5e10dfc0

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_X3C
import Definitions.Def_PLCMarkets_ExactCover_MarketD

set_option autoImplicit false

namespace C9e55ab3

open PLCMarkets.ExactCover

noncomputable def G (A x : ℝ) : ℝ := 2 * min (max x 0) A + max (x - A) 0

lemma reg_eval (n : ℕ) (x : ℝ) : (regulatorUtil n).eval x = G ((n : ℝ) ^ 3) x := by
  simp [PLUtility.eval, regulatorUtil, PLUtility.oneSeg, segEval, PLUtility.length, G]

lemma G_up (A u s : ℝ) (hA : 0 ≤ A) (hu : 0 ≤ u) (hs : 0 ≤ s) :
    s ≤ G A (u + s) - G A u := by
  unfold G
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma G_down (A u s : ℝ) (hA : 0 ≤ A) (_hu : 0 ≤ u) (hs : 0 ≤ s) :
    G A (u + s) - G A u ≤ 2 * s := by
  unfold G
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma util_reg {n : ℕ} (C : Fin n → Finset (Fin n)) (l : Good n) :
    (marketD C).util Agent.regulator l = regulatorUtil n := rfl

lemma nonreg_bound {n : ℕ} (C : Fin n → Finset (Fin n)) (i : Agent n)
    (hi : i ≠ Agent.regulator) (j : Good n) :
    ((marketD C).util i j).tail = 0 ∧ ((((marketD C).util i j).length : ℚ) : ℝ) ≤ 3 / 4 := by
  cases i with
  | regulator => exact absurd rfl hi
  | setAgent a =>
    cases j with
    | zero => simp [marketD, utilD, PLUtility.oneSeg, PLUtility.length]; norm_num
    | set b =>
      simp only [marketD, utilD]
      split_ifs <;> simp [PLUtility.oneSeg, PLUtility.flat, PLUtility.length] <;> norm_num
    | elem b =>
      simp only [marketD, utilD]
      split_ifs <;> simp [PLUtility.oneSeg, PLUtility.flat, PLUtility.length] <;> norm_num
  | elemAgent a =>
    cases j <;> simp [marketD, utilD, PLUtility.oneSeg, PLUtility.flat, PLUtility.length] <;> norm_num
  | extra =>
    cases j <;> simp [marketD, utilD, PLUtility.oneSeg, PLUtility.flat, PLUtility.length] <;> norm_num

lemma card_agent (n : ℕ) : Fintype.card (Agent n) ≤ 2 * n + 2 := by
  let f : Agent n → Option (Option (Fin n ⊕ Fin n)) := fun a => match a with
    | .regulator => none
    | .extra => some none
    | .setAgent i => some (some (Sum.inl i))
    | .elemAgent i => some (some (Sum.inr i))
  have hf : Function.Injective f := by
    intro a b h
    cases a <;> cases b <;> simp_all [f]
  have := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin] at this
  omega

end C9e55ab3

open PLCMarkets.ExactCover in
theorem solution (n : ℕ) (C : Fin n → Finset (Fin n))
    (hcard : ∀ i, (C i).card = 3) (hdiv : 3 ∣ n) (hn : 35 < n)
    (hcover : ∀ x : Fin n, ∃ i, x ∈ C i)
    (p : Good n → ℝ)
    (hp : (marketD C).IsApproxEquilibrium (((n : ℝ) ^ 5)⁻¹) p) :
    (∀ j, 0 < p j) ∧ ∀ j k, p j ≤ 2 * p k := by
  obtain ⟨⟨hp0, _hpsum⟩, x, hopt, hclear⟩ := hp
  obtain ⟨hy0, hycost, hymax, -⟩ := hopt Agent.regulator
  set y := x Agent.regulator with hy
  have hA : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  have hU : ∀ z : Good n → ℝ,
      (marketD C).utility Agent.regulator z = ∑ l, C9e55ab3.G ((n : ℝ) ^ 3) (z l) := by
    intro z; simp only [ADMarket.utility, C9e55ab3.util_reg, C9e55ab3.reg_eval]
  have hpos : ∀ j, 0 < p j := by
    intro j
    rcases (hp0 j).lt_or_eq with h | h
    · exact h
    exfalso
    let z : Good n → ℝ := fun l => y l + if l = j then 1 else 0
    have hz0 : ∀ l, 0 ≤ z l := by
      intro l; have := hy0 l; simp only [z]; split_ifs <;> linarith
    have hzc : ∑ l, p l * z l ≤ (marketD C).income p Agent.regulator := by
      have : ∑ l, p l * z l = ∑ l, p l * y l := by
        simp only [z, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, ← h, add_zero]
      rw [this]; exact hycost
    have h1 := hymax z hz0 hzc
    rw [hU, hU] at h1
    have h2 : ∀ l, (if l = j then (1 : ℝ) else 0) ≤ C9e55ab3.G ((n : ℝ) ^ 3) (z l) - C9e55ab3.G ((n : ℝ) ^ 3) (y l) := by
      intro l
      simp only [z]
      split_ifs
      · exact C9e55ab3.G_up _ _ _ hA (hy0 l) zero_le_one
      · simp
    have h3 := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => h2 l)
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq'] at h3
    simp only [Finset.mem_univ, if_true] at h3
    linarith
  refine ⟨hpos, ?_⟩
  intro j k
  by_contra hjk
  push Not at hjk
  have hjk' : j ≠ k := by rintro rfl; linarith [hpos j]
  have hyj : y j = 0 := by
    by_contra hne
    have hyjpos : 0 < y j := lt_of_le_of_ne (hy0 j) (Ne.symm hne)
    have hpk := hpos k
    set δ := y j with hδ
    set t := δ * p j / p k with ht
    have htpos : 0 ≤ t := div_nonneg (mul_nonneg hyjpos.le (hp0 j)) hpk.le
    have hpt : p k * t = δ * p j := by rw [ht]; field_simp
    have htd : 0 < t - 2 * δ := by
      have : t - 2 * δ = δ * (p j - 2 * p k) / p k := by rw [ht]; field_simp
      rw [this]; apply div_pos _ hpk; apply mul_pos hyjpos; linarith
    let z : Good n → ℝ := fun l => y l + ((if l = k then t else 0) - (if l = j then δ else 0))
    have hz0 : ∀ l, 0 ≤ z l := by
      intro l; have := hy0 l; simp only [z]
      split_ifs with h1 h2 h2
      · exact absurd (h2.symm.trans h1) hjk'
      · linarith
      · subst h2; linarith
      · linarith
    have hzc : ∑ l, p l * z l ≤ (marketD C).income p Agent.regulator := by
      have : ∑ l, p l * z l = ∑ l, p l * y l := by
        simp only [z, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [hpt]; ring
      rw [this]; exact hycost
    have h1 := hymax z hz0 hzc
    rw [hU, hU] at h1
    have h2 : ∀ l, (if l = k then t else 0) - 2 * (if l = j then δ else 0) ≤
        C9e55ab3.G ((n : ℝ) ^ 3) (z l) - C9e55ab3.G ((n : ℝ) ^ 3) (y l) := by
      intro l
      simp only [z]
      split_ifs with h1 h2 h2
      · exact absurd (h2.symm.trans h1) hjk'
      · have := C9e55ab3.G_up _ _ _ hA (hy0 l) htpos
        simp only [sub_zero, mul_zero]
        linarith
      · subst h2
        have := C9e55ab3.G_down ((n : ℝ) ^ 3) 0 δ hA le_rfl hyjpos.le
        simp only [zero_add] at this
        have e : y l + (0 - δ) = 0 := by rw [← hδ]; ring
        rw [e]; linarith
      · simp
    have h3 := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => h2 l)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      Finset.sum_ite_eq'] at h3
    simp only [Finset.mem_univ, if_true] at h3
    linarith
  -- demand bound
  have hb : ∀ i, x i j ≤ 3 / 4 := by
    intro i
    by_cases hi : i = Agent.regulator
    · subst hi; rw [← hy, hyj]; norm_num
    · obtain ⟨htail, hlen⟩ := C9e55ab3.nonreg_bound C i hi j
      have := (hopt i).2.2.2 j htail
      linarith
  have hsum : ∑ i, x i j ≤ (Fintype.card (Agent n) : ℝ) * (3 / 4) := by
    calc ∑ i, x i j ≤ ∑ _i : Agent n, (3 / 4 : ℝ) := Finset.sum_le_sum (fun i _ => hb i)
      _ = _ := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcardA : (Fintype.card (Agent n) : ℝ) ≤ 2 * n + 2 := by
    exact_mod_cast C9e55ab3.card_agent n
  -- supply bound
  have hS : (n : ℝ) ^ 3 ≤ (marketD C).supply j := by
    unfold ADMarket.supply
    have := Finset.single_le_sum (f := fun i => (((marketD C).endow i j : ℚ) : ℝ))
      (fun i _ => by exact_mod_cast (marketD C).endow_nonneg i j) (Finset.mem_univ Agent.regulator)
    simpa [marketD, endowD] using this
  have hn' : (36 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : (2 : ℝ) ≤ (n : ℝ) ^ 5 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 36) hn' 5]
  have hε : ((n : ℝ) ^ 5)⁻¹ ≤ 1 / 2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) h5
  have hc := hclear j
  have hc' := (abs_le.mp hc).1
  have hSnn : 0 ≤ (marketD C).supply j := le_trans hA hS
  have : ((n : ℝ) ^ 5)⁻¹ * (marketD C).supply j ≤ 1 / 2 * (marketD C).supply j :=
    mul_le_mul_of_nonneg_right hε hSnn
  have hn3 : (n : ℝ) ^ 3 = n * n * n := by ring
  nlinarith

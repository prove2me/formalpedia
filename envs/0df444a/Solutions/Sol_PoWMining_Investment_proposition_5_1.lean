-- Prove2me | solution 1 for PoWMining.Investment.proposition_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:12:09.598461+00:00
-- url     : https://prove2.me/submissions/5c90c272-0326-4635-b003-2aa963400ac7

import Mathlib
import Definitions.Def_PoWMining_Investment_Model

open PoWMining.Equilibrium (aggH)

namespace PoW51Aux
open PoWMining.Investment

variable {N : ℕ}

lemma aggH_update (h : Fin N → ℝ) (i : Fin N) (x : ℝ) :
    aggH (Function.update h i x) = aggH h - h i + x := by
  unfold aggH
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) h]
  ring

lemma payoff_eq (c : Fin N → ℝ) (R γ : ℝ) (h : Fin N → ℝ) (i : Fin N) (hH : aggH h ≠ 0) :
    payoff c R γ h i = h i / aggH h * R - c i * h i - γ / 2 * h i ^ 2 := by
  simp [payoff, hH]

lemma payoff_update (c : Fin N → ℝ) (R γ : ℝ) (h : Fin N → ℝ) (i : Fin N) (x : ℝ)
    (hx : aggH h - h i + x ≠ 0) :
    payoff c R γ (Function.update h i x) i
      = x / (aggH h - h i + x) * R - c i * x - γ / 2 * x ^ 2 := by
  rw [payoff_eq _ _ _ _ _ (by rwa [aggH_update]), aggH_update]
  simp

lemma aggH_pos {c : Fin N → ℝ} {R γ : ℝ} {h : Fin N → ℝ} (hN : 0 < N) (hc : ∀ j, 0 < c j)
    (hR : 0 < R) (hγ : 0 ≤ γ) (heq : IsMiningEq c R γ h) : 0 < aggH h := by
  obtain ⟨hnn, hdev⟩ := heq
  have h0 : 0 ≤ aggH h := Finset.sum_nonneg (fun j _ => hnn j)
  rcases h0.lt_or_eq with h0 | h0
  · exact h0
  exfalso
  have hall : ∀ j, h j = 0 := fun j =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).1 h0.symm j (Finset.mem_univ j)
  let i : Fin N := ⟨0, hN⟩
  have hci := hc i
  have hpos : 0 < c i + γ + R := by linarith
  set x := R / (2 * (c i + γ + R)) with hxdef
  have hx0 : 0 < x := by positivity
  have hx1 : x * (c i + γ + R) = R / 2 := by rw [hxdef]; field_simp
  have hx2 : x ≤ 1 / 2 := by nlinarith
  have hd := hdev i x hx0.le
  have hS : aggH h - h i + x = x := by rw [← h0, hall i]; ring
  rw [payoff_update _ _ _ _ _ _ (by rw [hS]; exact hx0.ne'), hS, div_self hx0.ne'] at hd
  have hp0 : payoff c R γ h i = 0 := by simp [payoff, ← h0]
  rw [hp0] at hd
  nlinarith [mul_nonneg hγ hx0.le, mul_nonneg (mul_nonneg hγ hx0.le) hx0.le]

/-- First-order condition for an active miner. -/
lemma foc {c : Fin N → ℝ} {R γ : ℝ} {h : Fin N → ℝ} (hc : ∀ j, 0 < c j)
    (hR : 0 < R) (hγ : 0 ≤ γ) (heq : IsMiningEq c R γ h) (i : Fin N) (hi : 0 < h i) :
    0 < aggH h - h i ∧ R * (aggH h - h i) = (c i + γ * h i) * aggH h ^ 2 := by
  obtain ⟨hnn, hdev⟩ := heq
  set S := aggH h - h i with hSdef
  have hS0 : 0 ≤ S := by
    have : aggH h = h i + ∑ j ∈ Finset.univ \ {i}, h j := by
      unfold aggH; exact Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) h
    have : 0 ≤ ∑ j ∈ Finset.univ \ {i}, h j := Finset.sum_nonneg (fun j _ => hnn j)
    linarith
  have hHi : aggH h = S + h i := by rw [hSdef]; ring
  have hci := hc i
  have hS : 0 < S := by
    rcases hS0.lt_or_eq with h1 | h1
    · exact h1
    exfalso
    have hd := hdev i (h i / 2) (by positivity)
    rw [payoff_update _ _ _ _ _ _ (by rw [← hSdef, ← h1]; positivity)] at hd
    rw [payoff_eq _ _ _ _ _ (by rw [hHi, ← h1]; simp; exact hi.ne')] at hd
    rw [← hSdef, ← h1, hHi, ← h1] at hd
    simp only [zero_add] at hd
    rw [div_self (by positivity), div_self hi.ne'] at hd
    nlinarith [mul_pos hci hi, mul_nonneg hγ (sq_nonneg (h i))]
  refine ⟨hS, ?_⟩
  -- derivative argument
  let f : ℝ → ℝ := fun x => x / (S + x) * R - c i * x - γ / 2 * x ^ 2
  have hmax : IsLocalMax f (h i) := by
    have : ∀ᶠ x in nhds (h i), 0 < x := Ioi_mem_nhds hi
    filter_upwards [this] with x hx
    have hd := hdev i x hx.le
    rw [payoff_update _ _ _ _ _ _ (by rw [← hSdef]; positivity)] at hd
    have hp : payoff c R γ h i = f (h i) := by
      rw [payoff_eq _ _ _ _ _ (by rw [hHi]; positivity), hHi]
    rw [hp] at hd
    exact hd
  have hder : HasDerivAt f (S / (S + h i) ^ 2 * R - c i - γ * h i) (h i) := by
    have h1 : HasDerivAt (fun x => x / (S + x)) ((1 * (S + h i) - h i * 1) / (S + h i) ^ 2) (h i) :=
      (hasDerivAt_id (h i)).div ((hasDerivAt_id (h i)).const_add S) (by positivity)
    have h2 : HasDerivAt f ((1 * (S + h i) - h i * 1) / (S + h i) ^ 2 * R - c i * 1
        - γ / 2 * (↑2 * h i ^ (2 - 1) * 1)) (h i) :=
      ((h1.mul_const R).sub ((hasDerivAt_id' (h i)).const_mul (c i))).sub
        (((hasDerivAt_id' (h i)).pow 2).const_mul (γ / 2))
    refine h2.congr_deriv ?_
    have hpos : S + h i ≠ 0 := by positivity
    field_simp
    ring
  have h0 := hmax.hasDerivAt_eq_zero hder
  rw [hHi]
  have hpos : 0 < S + h i := by positivity
  field_simp at h0
  linear_combination h0

end PoW51Aux


open PoWMining.Equilibrium (aggH)

namespace PoW51Aux
open PoWMining.Investment

variable {N : ℕ}

/-- Inactive miners face `R ≤ c_i H`. -/
lemma inactive_ge {c : Fin N → ℝ} {R γ : ℝ} {h : Fin N → ℝ} (hc : ∀ j, 0 < c j)
    (hR : 0 < R) (hγ : 0 ≤ γ) (heq : IsMiningEq c R γ h) (hH : 0 < aggH h) (i : Fin N)
    (hi : h i = 0) : R ≤ c i * aggH h := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨hnn, hdev⟩ := heq
  set H := aggH h with hHdef
  have hci := hc i
  set δ := R - c i * H with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set M := c i + γ * (H + 1) + 1 with hM
  have hM0 : 0 < M := by positivity
  set x := min 1 (δ / (2 * M)) with hx
  have hx0 : 0 < x := lt_min one_pos (by positivity)
  have hx1 : x ≤ 1 := min_le_left _ _
  have hx2 : x * M ≤ δ / 2 := by
    have : x ≤ δ / (2 * M) := min_le_right _ _
    calc x * M ≤ δ / (2 * M) * M := by gcongr
      _ = δ / 2 := by field_simp
  have hd := hdev i x hx0.le
  rw [payoff_update _ _ _ _ _ _ (by rw [hi]; positivity), hi] at hd
  have hp0 : payoff c R γ h i = 0 := by simp [payoff, hi]
  rw [hp0, sub_zero] at hd
  -- x/(H+x)*R - c x - γ/2 x^2 ≤ 0
  have hHx : 0 < H + x := by positivity
  rw [div_mul_eq_mul_div, sub_sub, sub_nonpos, div_le_iff₀ hHx] at hd
  nlinarith [mul_nonneg hγ hx0.le, mul_nonneg (mul_nonneg hγ hx0.le) hx0.le,
    mul_nonneg (mul_nonneg hγ hx0.le) hHx.le, mul_le_mul_of_nonneg_left hx1 (mul_nonneg hγ hx0.le),
    mul_nonneg (mul_nonneg hγ hx0.le) (sub_nonneg.2 hx1)]

/-- Basic structural facts of a mining equilibrium. -/
structure EqFacts {N : ℕ} (c : Fin N → ℝ) (R γ : ℝ) (h : Fin N → ℝ) : Prop where
  nn : ∀ j, 0 ≤ h j
  Hpos : 0 < aggH h
  form : ∀ j, h j * (R + γ * aggH h ^ 2) = aggH h * max 0 (R - c j * aggH h)
  root : ∑ j, max 0 (R - c j * aggH h) = R + γ * aggH h ^ 2
  Spos : ∀ j, 0 < aggH h - h j
  act : ∀ j, 0 < h j ↔ c j * aggH h < R
  pay : ∀ j, payoff c R γ h j * (R + γ * aggH h ^ 2) ^ 2
      = (max 0 (R - c j * aggH h)) ^ 2 * (R + γ * aggH h ^ 2 / 2)

lemma eqFacts {c : Fin N → ℝ} {R γ : ℝ} {h : Fin N → ℝ} (hN : 0 < N) (hc : ∀ j, 0 < c j)
    (hR : 0 < R) (hγ : 0 ≤ γ) (heq : IsMiningEq c R γ h) : EqFacts c R γ h := by
  have hH := aggH_pos hN hc hR hγ heq
  have hnn := heq.1
  set H := aggH h with hHdef
  have hD : 0 < R + γ * H ^ 2 := by positivity
  have form : ∀ j, h j * (R + γ * H ^ 2) = H * max 0 (R - c j * H) := by
    intro j
    rcases (hnn j).lt_or_eq with hj | hj
    · obtain ⟨hS, hF⟩ := foc hc hR hγ heq j hj
      have e1 : h j * (R + γ * H ^ 2) = H * (R - c j * H) := by
        rw [← hHdef] at hS hF; linear_combination -hF
      have : 0 < R - c j * H := by
        have := mul_pos hj hD
        rw [e1] at this
        exact pos_of_mul_pos_right this hH.le
      rw [max_eq_right this.le, e1]
    · have := inactive_ge hc hR hγ heq hH j hj.symm
      rw [← hj, max_eq_left (by rw [← hHdef] at this; linarith)]
      ring
  have root : ∑ j, max 0 (R - c j * H) = R + γ * H ^ 2 := by
    have : H * ∑ j, max 0 (R - c j * H) = H * (R + γ * H ^ 2) := by
      rw [Finset.mul_sum]
      simp_rw [← form]
      rw [← Finset.sum_mul]
      rfl
    exact mul_left_cancel₀ hH.ne' this
  refine ⟨hnn, hH, form, root, ?_, ?_, ?_⟩
  · intro j
    rcases (hnn j).lt_or_eq with hj | hj
    · exact (foc hc hR hγ heq j hj).1
    · rw [← hj]; simpa using hH
  · intro j
    constructor
    · intro hj
      have := form j
      have h1 := mul_pos hj hD
      rw [this] at h1
      have := pos_of_mul_pos_right h1 hH.le
      have : 0 < R - c j * H := by
        by_contra hc'
        push_neg at hc'
        rw [max_eq_left hc'] at this
        exact lt_irrefl _ this
      linarith
    · intro hj
      rcases (hnn j).lt_or_eq with h1 | h1
      · exact h1
      · have := inactive_ge hc hR hγ heq hH j h1.symm
        exact absurd this (by rw [← hHdef]; linarith)
  · intro j
    have hj := form j
    have hpj : payoff c R γ h j = h j / H * R - c j * h j - γ / 2 * h j ^ 2 :=
      payoff_eq _ _ _ _ _ hH.ne'
    have hh : h j = H * max 0 (R - c j * H) / (R + γ * H ^ 2) := by
      rw [eq_div_iff hD.ne']; exact hj
    rw [hpj, hh]
    rcases le_or_gt (R - c j * H) 0 with hm | hm
    · rw [max_eq_left hm]; ring
    · rw [max_eq_right hm.le]
      field_simp
      ring

end PoW51Aux


open PoWMining.Equilibrium (aggH)

namespace PoW51Aux
open PoWMining.Investment

variable {N : ℕ}

lemma exists_active {c : Fin N → ℝ} {R γ : ℝ} {h : Fin N → ℝ} (F : EqFacts c R γ h) :
    ∃ j, 0 < h j := by
  by_contra hne
  push_neg at hne
  have : aggH h ≤ 0 := Finset.sum_nonpos (fun j _ => hne j)
  linarith [F.Hpos]

/-- Aggregate comparison via the root equation. -/
lemma H_le_of_sum {c c' : Fin N → ℝ} {R γ : ℝ} {h h' : Fin N → ℝ} (hc : ∀ j, 0 < c j)
    (hγ : 0 ≤ γ) (F : EqFacts c R γ h) (F' : EqFacts c' R γ h')
    (hsum : ∑ j, max 0 (R - c j * aggH h') ≤ ∑ j, max 0 (R - c' j * aggH h')) :
    aggH h ≤ aggH h' := by
  by_contra hlt
  push_neg at hlt
  have hH' := F'.Hpos
  obtain ⟨j, hj⟩ := exists_active F
  have hj' := (F.act j).1 hj
  have hlt2 : ∑ j, max 0 (R - c j * aggH h) < ∑ j, max 0 (R - c j * aggH h') := by
    apply Finset.sum_lt_sum
    · intro k _
      have := hc k
      exact max_le_max le_rfl (by nlinarith)
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      have := hc j
      rw [max_eq_right (by linarith)]
      exact lt_max_of_lt_right (by nlinarith)
  rw [F.root] at hlt2
  rw [F'.root] at hsum
  nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH'.le hlt.le 2) hγ]

lemma H_le_of_le {c c' : Fin N → ℝ} {R γ : ℝ} {h h' : Fin N → ℝ} (hc : ∀ j, 0 < c j)
    (hγ : 0 ≤ γ) (F : EqFacts c R γ h) (F' : EqFacts c' R γ h') (hle : ∀ j, c' j ≤ c j) :
    aggH h ≤ aggH h' := by
  apply H_le_of_sum hc hγ F F'
  apply Finset.sum_le_sum
  intro j _
  exact max_le_max le_rfl (by nlinarith [hle j, F'.Hpos])

lemma payoff_val {c : Fin N → ℝ} {R γ : ℝ} {h : Fin N → ℝ} (hR : 0 < R) (hγ : 0 ≤ γ)
    (F : EqFacts c R γ h) (j : Fin N) :
    payoff c R γ h j = (max 0 (R - c j * aggH h)) ^ 2 * (R + γ * aggH h ^ 2 / 2)
      / (R + γ * aggH h ^ 2) ^ 2 := by
  have hD : 0 < R + γ * aggH h ^ 2 := by have := F.Hpos; positivity
  rw [eq_div_iff (by positivity)]
  exact F.pay j

lemma payoff_nonneg {c : Fin N → ℝ} {R γ : ℝ} {h : Fin N → ℝ} (hR : 0 < R) (hγ : 0 ≤ γ)
    (F : EqFacts c R γ h) (j : Fin N) : 0 ≤ payoff c R γ h j := by
  rw [payoff_val hR hγ F]
  have := F.Hpos
  positivity

lemma payoff_pos {c : Fin N → ℝ} {R γ : ℝ} {h : Fin N → ℝ} (hR : 0 < R) (hγ : 0 ≤ γ)
    (F : EqFacts c R γ h) (j : Fin N) (hj : 0 < h j) : 0 < payoff c R γ h j := by
  rw [payoff_val hR hγ F]
  have := F.Hpos
  have h1 := (F.act j).1 hj
  rw [max_eq_right (by linarith)]
  have : 0 < R - c j * aggH h := by linarith
  positivity

lemma payoff_zero {c : Fin N → ℝ} {R γ : ℝ} {h : Fin N → ℝ} (hR : 0 < R) (hγ : 0 ≤ γ)
    (F : EqFacts c R γ h) (j : Fin N) (hj : R ≤ c j * aggH h) : payoff c R γ h j = 0 := by
  rw [payoff_val hR hγ F, max_eq_left (by linarith)]
  ring

/-- Same equilibrium: cheaper miners earn more. -/
lemma payoff_mono_same {c : Fin N → ℝ} {R γ : ℝ} {h : Fin N → ℝ} (hR : 0 < R) (hγ : 0 ≤ γ)
    (F : EqFacts c R γ h) (i k : Fin N) (hik : c i ≤ c k) :
    payoff c R γ h k ≤ payoff c R γ h i := by
  rw [payoff_val hR hγ F, payoff_val hR hγ F]
  have := F.Hpos
  have hD : 0 < R + γ * aggH h ^ 2 := by positivity
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (le_max_left _ _)
  exact max_le_max le_rfl (by nlinarith)

lemma root_split {c : Fin N → ℝ} {R γ : ℝ} {h : Fin N → ℝ} (F : EqFacts c R γ h) (i : Fin N) :
    max 0 (R - c i * aggH h) + ∑ j ∈ Finset.univ.erase i, max 0 (R - c j * aggH h)
      = R + γ * aggH h ^ 2 := by
  have := Finset.add_sum_erase Finset.univ (fun j => max 0 (R - c j * aggH h)) (Finset.mem_univ i)
  rw [this]
  exact F.root

/-- Own cost up (rivals unchanged) ⇒ own profit down. -/
lemma payoff_own_mono {c c' : Fin N → ℝ} {R γ : ℝ} {h h' : Fin N → ℝ} (hc : ∀ j, 0 < c j)
    (hR : 0 < R) (hγ : 0 ≤ γ) (F : EqFacts c R γ h) (F' : EqFacts c' R γ h') (i : Fin N)
    (hsame : ∀ j, j ≠ i → c' j = c j) (hci : c i ≤ c' i) :
    payoff c' R γ h' i ≤ payoff c R γ h i := by
  have hc' : ∀ j, 0 < c' j := by
    intro j; by_cases hj : j = i
    · subst hj; linarith [hc j]
    · rw [hsame j hj]; exact hc j
  have hHH : aggH h' ≤ aggH h := H_le_of_le hc' hγ F' F (by
    intro j; by_cases hj : j = i
    · subst hj; exact hci
    · rw [hsame j hj])
  set H := aggH h
  set H' := aggH h'
  have hH := F.Hpos
  have hH' := F'.Hpos
  set D := R + γ * H ^ 2 with hDdef
  set D' := R + γ * H' ^ 2 with hD'def
  have hD : 0 < D := by positivity
  have hD' : 0 < D' := by positivity
  have hDD : D' ≤ D := by
    rw [hDdef, hD'def]; nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH'.le hHH 2) hγ]
  set s := ∑ j ∈ Finset.univ.erase i, max 0 (R - c j * H) with hs
  set s' := ∑ j ∈ Finset.univ.erase i, max 0 (R - c j * H') with hs'
  have hss : s ≤ s' := by
    apply Finset.sum_le_sum; intro j _
    exact max_le_max le_rfl (by nlinarith [hc j])
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun j _ => le_max_left _ _)
  have hr := root_split F i
  have hr' := root_split F' i
  have hsum' : ∑ j ∈ Finset.univ.erase i, max 0 (R - c' j * H')= s' := by
    apply Finset.sum_congr rfl; intro j hj
    rw [hsame j (Finset.ne_of_mem_erase hj)]
  rw [hsum'] at hr'
  set m := max 0 (R - c i * H) with hm
  set m' := max 0 (R - c' i * H') with hm'
  have hm0 : 0 ≤ m := le_max_left _ _
  have hm'0 : 0 ≤ m' := le_max_left _ _
  have key : m' * D ≤ m * D' := by nlinarith
  rw [payoff_val hR hγ F, payoff_val hR hγ F']
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hW : R + γ * H' ^ 2 / 2 ≤ R + γ * H ^ 2 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH'.le hHH 2) hγ]
  have hW0 : 0 ≤ R + γ * H' ^ 2 / 2 := by positivity
  have hsq : (m' * D) ^ 2 ≤ (m * D') ^ 2 := pow_le_pow_left₀ (by positivity) key 2
  calc m' ^ 2 * (R + γ * H' ^ 2 / 2) * D ^ 2 = (m' * D) ^ 2 * (R + γ * H' ^ 2 / 2) := by ring
    _ ≤ (m * D') ^ 2 * (R + γ * H' ^ 2 / 2) := mul_le_mul_of_nonneg_right hsq hW0
    _ ≤ (m * D') ^ 2 * (R + γ * H ^ 2 / 2) := mul_le_mul_of_nonneg_left hW (by positivity)
    _ = m ^ 2 * (R + γ * H ^ 2 / 2) * D' ^ 2 := by ring

/-- Own cost strictly down (rivals unchanged) for an active miner ⇒ profit strictly up. -/
lemma payoff_own_strict {c c' : Fin N → ℝ} {R γ : ℝ} {h h' : Fin N → ℝ} (hc' : ∀ j, 0 < c' j)
    (hR : 0 < R) (hγ : 0 ≤ γ) (F : EqFacts c R γ h) (F' : EqFacts c' R γ h') (i : Fin N)
    (hsame : ∀ j, j ≠ i → c' j = c j) (hci : c' i < c i) (hact : 0 < h i) :
    payoff c R γ h i < payoff c' R γ h' i := by
  have hc : ∀ j, 0 < c j := by
    intro j; by_cases hj : j = i
    · subst hj; linarith [hc' j]
    · rw [← hsame j hj]; exact hc' j
  have hHH : aggH h ≤ aggH h' := H_le_of_le hc hγ F F' (by
    intro j; by_cases hj : j = i
    · subst hj; exact hci.le
    · rw [hsame j hj])
  set H := aggH h
  set H' := aggH h'
  have hH := F.Hpos
  have hH' := F'.Hpos
  set D := R + γ * H ^ 2 with hDdef
  set D' := R + γ * H' ^ 2 with hD'def
  have hD : 0 < D := by positivity
  have hD' : 0 < D' := by positivity
  have hDD : D ≤ D' := by
    rw [hDdef, hD'def]; nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH.le hHH 2) hγ]
  set s := ∑ j ∈ Finset.univ.erase i, max 0 (R - c j * H) with hs
  set s' := ∑ j ∈ Finset.univ.erase i, max 0 (R - c j * H') with hs'
  have hs'0 : 0 ≤ s' := Finset.sum_nonneg (fun j _ => le_max_left _ _)
  have hr := root_split F i
  have hr' := root_split F' i
  have hsum' : ∑ j ∈ Finset.univ.erase i, max 0 (R - c' j * H')= s' := by
    apply Finset.sum_congr rfl; intro j hj
    rw [hsame j (Finset.ne_of_mem_erase hj)]
  rw [hsum'] at hr'
  have hai := (F.act i).1 hact
  set m := max 0 (R - c i * H) with hm
  set m' := max 0 (R - c' i * H') with hm'
  have hmv : m = R - c i * H := max_eq_right (by linarith)
  have hm'ge : R - c' i * H' ≤ m' := le_max_right _ _
  have hm0 : 0 < m := by rw [hmv]; linarith
  -- strict increase of the aggregate
  have hHlt : H < H' := by
    rcases hHH.lt_or_eq with h1 | h1
    · exact h1
    exfalso
    have : s = s' := by rw [hs, hs', h1]
    have : m' = m := by
      have : D = D' := by rw [hDdef, hD'def, h1]
      linarith
    rw [← h1] at hm'ge
    nlinarith [hc' i]
  obtain ⟨j, hjne, hj⟩ : ∃ j, j ≠ i ∧ 0 < h j := by
    have hsum : 0 < ∑ j ∈ Finset.univ.erase i, h j := by
      have := Finset.add_sum_erase Finset.univ h (Finset.mem_univ i)
      have hS := F.Spos i
      unfold aggH at hS; linarith
    obtain ⟨j, hjm, hjp⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ.erase i)
      (f := fun _ => (0:ℝ)) (g := h) (by simpa using hsum)
    exact ⟨j, Finset.ne_of_mem_erase hjm, hjp⟩
  have hss : s' < s := by
    apply Finset.sum_lt_sum
    · intro k _
      exact max_le_max le_rfl (by nlinarith [hc k])
    · refine ⟨j, Finset.mem_erase.2 ⟨hjne, Finset.mem_univ j⟩, ?_⟩
      have hj2 := (F.act j).1 hj
      rw [max_eq_right (show 0 ≤ R - c j * H by linarith) ]
      apply max_lt (by linarith)
      nlinarith [hc j]
  have key : m * D' < m' * D := by nlinarith
  rw [payoff_val hR hγ F, payoff_val hR hγ F']
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hW : R + γ * H ^ 2 / 2 ≤ R + γ * H' ^ 2 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH.le hHH 2) hγ]
  have hW0 : 0 < R + γ * H ^ 2 / 2 := by positivity
  have hsq : (m * D') ^ 2 < (m' * D) ^ 2 := pow_lt_pow_left₀ key (by positivity) two_ne_zero
  calc m ^ 2 * (R + γ * H ^ 2 / 2) * D' ^ 2 = (m * D') ^ 2 * (R + γ * H ^ 2 / 2) := by ring
    _ < (m' * D) ^ 2 * (R + γ * H ^ 2 / 2) := mul_lt_mul_of_pos_right hsq hW0
    _ ≤ (m' * D) ^ 2 * (R + γ * H' ^ 2 / 2) := mul_le_mul_of_nonneg_left hW (by positivity)
    _ = m' ^ 2 * (R + γ * H' ^ 2 / 2) * D ^ 2 := by ring

end PoW51Aux


open PoWMining.Equilibrium (aggH)

namespace PoW51Aux
open PoWMining.Investment

variable {N : ℕ}

/-- Rivals' aggregate as a function of the aggregate and the own cost. -/
lemma Sfun_mono {R γ : ℝ} (hR : 0 < R) (hγ : 0 ≤ γ) {c1 c2 H1 H2 : ℝ} (hc1 : 0 ≤ c1)
    (hc : c1 ≤ c2) (hH1 : 0 < H1) (hH : H1 ≤ H2) :
    H1 - H1 * max 0 (R - c1 * H1) / (R + γ * H1 ^ 2)
      ≤ H2 - H2 * max 0 (R - c2 * H2) / (R + γ * H2 ^ 2) := by
  have hH2 : 0 < H2 := lt_of_lt_of_le hH1 hH
  have hD1 : 0 < R + γ * H1 ^ 2 := by positivity
  have hD2 : 0 < R + γ * H2 ^ 2 := by positivity
  have step2 : H2 - H2 * max 0 (R - c1 * H2) / (R + γ * H2 ^ 2)
      ≤ H2 - H2 * max 0 (R - c2 * H2) / (R + γ * H2 ^ 2) := by
    have : max 0 (R - c2 * H2) ≤ max 0 (R - c1 * H2) :=
      max_le_max le_rfl (by nlinarith)
    have : H2 * max 0 (R - c2 * H2) / (R + γ * H2 ^ 2)
        ≤ H2 * max 0 (R - c1 * H2) / (R + γ * H2 ^ 2) := by
      apply div_le_div_of_nonneg_right _ hD2.le
      exact mul_le_mul_of_nonneg_left this hH2.le
    linarith
  refine le_trans ?_ step2
  rcases le_or_gt (R - c1 * H2) 0 with h2 | h2
  · rw [max_eq_left h2]
    have : 0 ≤ H1 * max 0 (R - c1 * H1) / (R + γ * H1 ^ 2) := by
      have := le_max_left 0 (R - c1 * H1); positivity
    simp; linarith
  · have h1 : 0 < R - c1 * H1 := by nlinarith
    rw [max_eq_right h2.le, max_eq_right h1.le]
    have e1 : H1 - H1 * (R - c1 * H1) / (R + γ * H1 ^ 2)
        = H1 * (γ * H1 ^ 2 + c1 * H1) / (R + γ * H1 ^ 2) := by field_simp; ring
    have e2 : H2 - H2 * (R - c1 * H2) / (R + γ * H2 ^ 2)
        = H2 * (γ * H2 ^ 2 + c1 * H2) / (R + γ * H2 ^ 2) := by field_simp; ring
    rw [e1, e2, div_le_div_iff₀ hD1 hD2]
    have key : H2 * (γ * H2 ^ 2 + c1 * H2) * (R + γ * H1 ^ 2)
        - H1 * (γ * H1 ^ 2 + c1 * H1) * (R + γ * H2 ^ 2)
        = γ * R * (H2 - H1) * (H2 ^ 2 + H2 * H1 + H1 ^ 2)
          + γ ^ 2 * H1 ^ 2 * H2 ^ 2 * (H2 - H1) + c1 * R * (H2 - H1) * (H2 + H1) := by ring
    have : 0 ≤ γ * R * (H2 - H1) * (H2 ^ 2 + H2 * H1 + H1 ^ 2)
          + γ ^ 2 * H1 ^ 2 * H2 ^ 2 * (H2 - H1) + c1 * R * (H2 - H1) * (H2 + H1) := by
      have : 0 ≤ H2 - H1 := by linarith
      positivity
    linarith

lemma S_eq {c : Fin N → ℝ} {R γ : ℝ} {h : Fin N → ℝ} (hR : 0 < R) (hγ : 0 ≤ γ)
    (F : EqFacts c R γ h) (i : Fin N) :
    aggH h - h i = aggH h - aggH h * max 0 (R - c i * aggH h) / (R + γ * aggH h ^ 2) := by
  have hD : 0 < R + γ * aggH h ^ 2 := by have := F.Hpos; positivity
  have : h i = aggH h * max 0 (R - c i * aggH h) / (R + γ * aggH h ^ 2) := by
    rw [eq_div_iff hD.ne']; exact F.form i
  rw [this]

/-- Revealed-preference comparison: if the aggregate is weakly larger in the second equilibrium
and miner `k`'s cost there is at least miner `i`'s cost in the first, then `k` earns weakly less. -/
lemma payoff_rp {c c' : Fin N → ℝ} {R γ : ℝ} {h h' : Fin N → ℝ} (hc : ∀ j, 0 < c j)
    (hR : 0 < R) (hγ : 0 ≤ γ) (heq : IsMiningEq c R γ h) (F : EqFacts c R γ h)
    (F' : EqFacts c' R γ h') (i k : Fin N) (hH : aggH h ≤ aggH h') (hck : c i ≤ c' k) :
    payoff c' R γ h' k ≤ payoff c R γ h i := by
  have hSS : aggH h - h i ≤ aggH h' - h' k := by
    rw [S_eq hR hγ F, S_eq hR hγ F']
    exact Sfun_mono hR hγ (hc i).le hck F.Hpos hH
  have hS := F.Spos i
  have hx := F'.nn k
  have hp' : payoff c' R γ h' k = h' k / ((aggH h' - h' k) + h' k) * R - c' k * h' k
      - γ / 2 * h' k ^ 2 := by
    rw [payoff_eq _ _ _ _ _ F'.Hpos.ne']; ring_nf
  set x := h' k
  have hdev := heq.2 i x hx
  rw [payoff_update _ _ _ _ _ _ (by positivity)] at hdev
  refine le_trans ?_ hdev
  rw [hp']
  have : x / ((aggH h' - x) + x) ≤ x / (aggH h - h i + x) :=
    div_le_div_of_nonneg_left hx (by positivity) (by linarith)
  have h2 : c i * x ≤ c' k * x := mul_le_mul_of_nonneg_right hck hx
  nlinarith

end PoW51Aux


open PoWMining.Equilibrium (aggH)

namespace PoW51Aux
open PoWMining.Investment

variable {N : ℕ}

lemma br_key (R c γ S y x : ℝ) (hS : 0 < S) (hy : 0 ≤ y) (hx : 0 ≤ x)
    (hfoc : R * S = (c + γ * y) * (S + y) ^ 2) :
    (y / (S + y) * R - c * y - γ / 2 * y ^ 2) - (x / (S + x) * R - c * x - γ / 2 * x ^ 2)
      = (y - x) ^ 2 * (c + γ * y + γ * (S + x) / 2) / (S + x) := by
  have h1 : S + y ≠ 0 := by positivity
  have h2 : S + x ≠ 0 := by positivity
  field_simp
  linear_combination (2 * (y - x)) * hfoc

/-- Existence of a mining equilibrium for any positive cost vector. -/
lemma exists_eq {c : Fin N → ℝ} {R γ : ℝ} (hN : 2 ≤ N) (hc : ∀ j, 0 < c j) (hR : 0 < R)
    (hγ : 0 ≤ γ) : ∃ h, IsMiningEq c R γ h := by
  let Φ : ℝ → ℝ := fun X => ∑ j, max 0 (R - c j * X) - R - γ * X ^ 2
  have hcont : Continuous Φ := by
    apply Continuous.sub
    apply Continuous.sub
    · apply continuous_finset_sum
      intro j _
      exact continuous_const.max (continuous_const.sub (continuous_const.mul continuous_id))
    · exact continuous_const
    · exact continuous_const.mul (continuous_id.pow 2)
  set B := ∑ j, R / c j with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun j _ => (div_pos hR (hc j)).le)
  have hΦB : Φ B < 0 := by
    have hz : ∀ j, max 0 (R - c j * B) = 0 := by
      intro j; apply max_eq_left
      have h1 : R / c j ≤ B :=
        Finset.single_le_sum (f := fun k => R / c k) (fun k _ => (div_pos hR (hc k)).le)
          (Finset.mem_univ j)
      have := hc j
      rw [div_le_iff₀ this] at h1
      nlinarith
    simp only [Φ, hz, Finset.sum_const_zero]
    nlinarith [mul_nonneg hγ (sq_nonneg B)]
  have hΦ0 : 0 < Φ 0 := by
    simp only [Φ, mul_zero, sub_zero, max_eq_right hR.le, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : (2:ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  obtain ⟨H0, hH0mem, hH0⟩ : ∃ H0 ∈ Set.Icc 0 B, Φ H0 = 0 :=
    intermediate_value_Icc' hB0 hcont.continuousOn ⟨hΦB.le, hΦ0.le⟩
  have hH0pos : 0 < H0 := by
    rcases hH0mem.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hH0; linarith
  set D := R + γ * H0 ^ 2 with hDdef
  have hD : 0 < D := by positivity
  have hroot : ∑ j, max 0 (R - c j * H0) = D := by
    simp only [Φ] at hH0; rw [hDdef]; linarith
  let h : Fin N → ℝ := fun j => H0 * max 0 (R - c j * H0) / D
  have hagg : aggH h = H0 := by
    unfold aggH
    simp only [h]
    rw [← Finset.sum_div, ← Finset.mul_sum, hroot]
    field_simp
  have hnn : ∀ j, 0 ≤ h j := by
    intro j
    have := le_max_left 0 (R - c j * H0)
    simp only [h]; positivity
  refine ⟨h, hnn, ?_⟩
  intro i x hx
  set m := max 0 (R - c i * H0) with hm
  have hm0 : 0 ≤ m := le_max_left _ _
  have hci := hc i
  have hmD : m < D := by
    rw [hm]
    apply max_lt hD
    have : 0 < c i * H0 := by positivity
    nlinarith [mul_nonneg hγ (sq_nonneg H0)]
  have hhi : h i = H0 * m / D := rfl
  have hhiH : h i < H0 := by
    rw [hhi, div_lt_iff₀ hD]; nlinarith
  set S := H0 - h i with hSdef
  have hS : 0 < S := by rw [hSdef]; linarith
  have hHS : H0 = S + h i := by rw [hSdef]; ring
  rw [payoff_update _ _ _ _ _ _ (by rw [hagg]; positivity),
    payoff_eq _ _ _ _ _ (by rw [hagg]; exact hH0pos.ne'), hagg]
  rw [← hSdef]
  rcases le_or_gt (R - c i * H0) 0 with hneg | hposm
  · have hm' : m = 0 := max_eq_left hneg
    have hi0 : h i = 0 := by rw [hhi, hm']; ring
    rw [hi0] at hSdef ⊢
    simp only [zero_div, zero_mul, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    rw [sub_zero] at hSdef
    rw [hSdef]
    have h1 : x / (H0 + x) * R ≤ x / H0 * R :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hx hH0pos (by linarith)) hR.le
    have h2 : x / H0 * R - c i * x ≤ 0 := by
      rw [div_mul_eq_mul_div, sub_nonpos, div_le_iff₀ hH0pos]
      nlinarith
    nlinarith [mul_nonneg hγ (sq_nonneg x)]
  · have hm' : m = R - c i * H0 := max_eq_right hposm.le
    have hfoc : R * S = (c i + γ * h i) * (S + h i) ^ 2 := by
      rw [← hHS, hSdef]
      have : h i * D = H0 * m := by rw [hhi]; field_simp
      rw [hm', hDdef] at this
      linear_combination -this
    have key := br_key R (c i) γ S (h i) x hS (hnn i) hx hfoc
    rw [← hHS] at key
    have : 0 ≤ (h i - x) ^ 2 * (c i + γ * h i + γ * (S + x) / 2) / (S + x) := by
      have := hnn i
      positivity
    linarith

end PoW51Aux


open PoWMining.Equilibrium (aggH)

namespace PoW51Aux
open PoWMining.Investment

variable {N : ℕ}

/-- `q(b) = b - η b² / 2`, so that `c_i(b) = c̃_i - (c̃_i - c̃_0) q(b)`. -/
noncomputable def qf (P : InvParams N) (b : ℝ) : ℝ := b - P.η / 2 * b ^ 2

noncomputable def qbar (P : InvParams N) : ℝ := qf P (betaBar P)

noncomputable def costAt (P : InvParams N) (j : Fin N) (b : ℝ) : ℝ :=
  P.ct j - (P.ct j - P.c0) * qf P b

noncomputable def ee (P : InvParams N) (j : Fin N) : ℝ := costAt P j (betaBar P)

lemma cost_eq (P : InvParams N) (β : Fin N → ℝ) (j : Fin N) :
    cost P β j = costAt P j (β j) := by
  simp only [cost, costAt, qf]; ring

lemma betaBar_mem (P : InvParams N) (hP : P.Standing) :
    0 < betaBar P ∧ betaBar P ≤ 1 := by
  unfold betaBar
  split_ifs with h
  · exact ⟨one_pos, le_rfl⟩
  · push_neg at h
    exact ⟨by positivity, by rw [div_le_one (by linarith)]; linarith⟩

lemma qbar_mem (P : InvParams N) (hP : P.Standing) : 0 < qbar P ∧ qbar P ≤ 1 := by
  have hη := hP.η_nonneg
  unfold qbar qf betaBar
  split_ifs with h
  · constructor <;> nlinarith
  · push_neg at h
    have : 1 / P.η - P.η / 2 * (1 / P.η) ^ 2 = 1 / (2 * P.η) := by field_simp; ring
    rw [this]
    constructor
    · positivity
    · rw [div_le_one (by linarith)]; linarith

lemma qf_le (P : InvParams N) (hP : P.Standing) (b : ℝ) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    qf P b ≤ qbar P ∧ (b ≠ betaBar P → qf P b < qbar P) := by
  have hη := hP.η_nonneg
  obtain ⟨hb0, hb1⟩ := hb
  unfold qbar qf betaBar
  split_ifs with h
  · have key : (1 - P.η / 2 * 1 ^ 2) - (b - P.η / 2 * b ^ 2)
        = (1 - b) * (2 - P.η * (1 + b)) / 2 := by ring
    have h2 : 0 ≤ 2 - P.η * (1 + b) := by nlinarith
    refine ⟨?_, fun hne => ?_⟩
    · have : 0 ≤ (1 - b) * (2 - P.η * (1 + b)) / 2 := by
        have : 0 ≤ 1 - b := by linarith
        positivity
      linarith
    · have hb1' : b < 1 := lt_of_le_of_ne hb1 hne
      have h2' : 0 < 2 - P.η * (1 + b) := by nlinarith
      have : 0 < (1 - b) * (2 - P.η * (1 + b)) / 2 := by
        have : 0 < 1 - b := by linarith
        positivity
      linarith
  · push_neg at h
    have hη0 : 0 < P.η := by linarith
    have key : (1 / P.η - P.η / 2 * (1 / P.η) ^ 2) - (b - P.η / 2 * b ^ 2)
        = P.η / 2 * (b - 1 / P.η) ^ 2 := by field_simp; ring
    refine ⟨?_, fun hne => ?_⟩
    · have : 0 ≤ P.η / 2 * (b - 1 / P.η) ^ 2 := by positivity
      linarith
    · have : b - 1 / P.η ≠ 0 := sub_ne_zero.2 hne
      have : 0 < P.η / 2 * (b - 1 / P.η) ^ 2 := by positivity
      linarith

lemma ee_eq (P : InvParams N) (j : Fin N) :
    ee P j = (1 - qbar P) * P.ct j + qbar P * P.c0 := by
  unfold ee costAt qbar; ring

lemma costAt_ge (P : InvParams N) (hP : P.Standing) (j : Fin N) (b : ℝ)
    (hb : b ∈ Set.Icc (0:ℝ) 1) :
    ee P j ≤ costAt P j b ∧ (b ≠ betaBar P → ee P j < costAt P j b) := by
  have hd : 0 < P.ct j - P.c0 := by linarith [hP.c0_lt j]
  obtain ⟨h1, h2⟩ := qf_le P hP b hb
  unfold ee costAt
  change _ - _ * qbar P ≤ _ ∧ (_ → _ - _ * qbar P < _)
  refine ⟨by nlinarith, fun hne => by nlinarith [h2 hne]⟩

lemma costAt_zero (P : InvParams N) (j : Fin N) : costAt P j 0 = P.ct j := by
  simp [costAt, qf]

lemma ee_lt_ct (P : InvParams N) (hP : P.Standing) (j : Fin N) : ee P j < P.ct j := by
  have := (costAt_ge P hP j 0 ⟨le_rfl, zero_le_one⟩).2
    (ne_of_lt (betaBar_mem P hP).1)
  rwa [costAt_zero] at this

lemma ee_pos (P : InvParams N) (hP : P.Standing) (j : Fin N) : 0 < ee P j := by
  rw [ee_eq]
  have := qbar_mem P hP
  have := hP.c0_pos
  have := hP.c0_lt j
  nlinarith

lemma ee_mono (P : InvParams N) (hP : P.Standing) {j k : Fin N} (h : P.ct j ≤ P.ct k) :
    ee P j ≤ ee P k := by
  rw [ee_eq, ee_eq]
  have := qbar_mem P hP
  nlinarith

lemma ee_ct_of_lt (P : InvParams N) (hP : P.Standing) {j k : Fin N} (h : ee P j < ee P k) :
    P.ct j < P.ct k := by
  by_contra h'
  push_neg at h'
  linarith [ee_mono P hP h']

def Box {N : ℕ} (β : Fin N → ℝ) : Prop := ∀ i, β i ∈ Set.Icc (0 : ℝ) 1

lemma cost_ge_ee (P : InvParams N) (hP : P.Standing) {β : Fin N → ℝ} (hβ : Box β)
    (j : Fin N) : ee P j ≤ cost P β j := by
  rw [cost_eq]; exact (costAt_ge P hP j (β j) (hβ j)).1

lemma cost_pos (P : InvParams N) (hP : P.Standing) {β : Fin N → ℝ} (hβ : Box β)
    (j : Fin N) : 0 < cost P β j :=
  lt_of_lt_of_le (ee_pos P hP j) (cost_ge_ee P hP hβ j)

lemma cost_zero (P : InvParams N) (j : Fin N) : cost P 0 j = P.ct j := by
  simp [cost]

lemma box_zero : Box (0 : Fin N → ℝ) := fun _ => ⟨le_rfl, zero_le_one⟩

lemma box_update {β : Fin N → ℝ} (hβ : Box β) (i : Fin N) (b : ℝ)
    (hb : b ∈ Set.Icc (0:ℝ) 1) : Box (Function.update β i b) := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hb
  · rw [Function.update_of_ne hj]; exact hβ j

lemma box_betaK (P : InvParams N) (hP : P.Standing) (n : ℕ) : Box (betaK P n) := by
  intro j
  unfold betaK
  have := betaBar_mem P hP
  split_ifs
  · exact ⟨this.1.le, this.2⟩
  · exact ⟨le_rfl, zero_le_one⟩

lemma cost_update_ne (P : InvParams N) (β : Fin N → ℝ) (i j : Fin N) (b : ℝ) (hj : j ≠ i) :
    cost P (Function.update β i b) j = cost P β j := by
  simp [cost, Function.update_of_ne hj]

lemma cost_update_self (P : InvParams N) (β : Fin N → ℝ) (i : Fin N) (b : ℝ) :
    cost P (Function.update β i b) i = costAt P i b := by
  rw [cost_eq]; simp

section game

variable (P : InvParams N) (hP : P.Standing) (hstar : (Fin N → ℝ) → Fin N → ℝ)
  (hsel : IsSelection P hstar)

include hP hsel in
lemma EF {β : Fin N → ℝ} (hβ : Box β) : EqFacts (cost P β) P.R P.γ (hstar β) :=
  eqFacts (by linarith [hP.two_le]) (cost_pos P hP hβ) hP.R_pos hP.γ_nonneg (hsel β hβ)

include hP hsel in
lemma invPayoff_eq' {β : Fin N → ℝ} (hβ : Box β) (i : Fin N) :
    invPayoff P hstar β i = payoff (cost P β) P.R P.γ (hstar β) i
      - (if i ∉ A0 hstar ∧ 0 < β i then P.K else 0) := by
  have := (EF P hP hstar hsel hβ).Hpos
  simp [invPayoff, this.ne']

include hP hsel in
lemma mem_A0_iff (i : Fin N) :
    i ∈ A0 hstar ↔ P.ct i * aggH (hstar 0) < P.R := by
  have F0 := EF P hP hstar hsel box_zero
  have := F0.act i
  rw [cost_zero] at this
  simp [A0, this]

include hP hsel in
lemma A0_down {i j : Fin N} (hij : j ≤ i) (hi : i ∈ A0 hstar) : j ∈ A0 hstar := by
  rw [mem_A0_iff P hP hstar hsel] at hi ⊢
  have F0 := EF P hP hstar hsel box_zero
  have := F0.Hpos
  have := hP.sorted hij
  nlinarith

include hP hsel in
/-- A miner outside `A(0)` that does not invest stays inactive when no cost exceeds its
initial value. -/
lemma inactive_of_le {β : Fin N → ℝ} (hβ : Box β) (hle : ∀ j, cost P β j ≤ P.ct j)
    (i : Fin N) (hi : i ∉ A0 hstar) (hci : cost P β i = P.ct i) :
    P.R ≤ cost P β i * aggH (hstar β) := by
  have F0 := EF P hP hstar hsel box_zero
  have F := EF P hP hstar hsel hβ
  have hH : aggH (hstar 0) ≤ aggH (hstar β) :=
    H_le_of_le (cost_pos P hP box_zero) hP.γ_nonneg F0 F (by
      intro j; rw [cost_zero]; exact hle j)
  rw [mem_A0_iff P hP hstar hsel] at hi
  push_neg at hi
  rw [hci]
  have := hP.c0_lt i
  have := hP.c0_pos
  nlinarith

end game

end PoW51Aux


open PoWMining.Equilibrium (aggH)

namespace PoW51Aux
open PoWMining.Investment

variable {N : ℕ}

section game

variable (P : InvParams N) (hP : P.Standing) (hstar : (Fin N → ℝ) → Fin N → ℝ)
  (hsel : IsSelection P hstar)

include hP hsel in
/-- The participation inequality inherited from `i ∈ A(0)`. -/
lemma A0_ineq (i : Fin N) (hi : i ∈ A0 hstar) :
    ((Finset.univ.filter (fun j => P.ct j ≤ P.ct i)).card : ℝ) * P.ct i
      - ∑ j ∈ Finset.univ.filter (fun j => P.ct j ≤ P.ct i), P.ct j
      < P.ct i + P.γ * P.R / P.ct i := by
  set T := Finset.univ.filter (fun j => P.ct j ≤ P.ct i) with hT
  have F0 := EF P hP hstar hsel box_zero
  have hroot := F0.root
  simp_rw [cost_zero] at hroot
  set H0 := aggH (hstar 0) with hH0
  have hH0 := F0.Hpos
  rw [mem_A0_iff P hP hstar hsel] at hi
  have hR := hP.R_pos
  have hγ := hP.γ_nonneg
  have hcti : 0 < P.ct i := lt_trans hP.c0_pos (hP.c0_lt i)
  have hctpos : ∀ j, 0 < P.ct j := fun j => lt_trans hP.c0_pos (hP.c0_lt j)
  have hsub : ∑ j ∈ T, (P.R - P.ct j * H0) ≤ P.R + P.γ * H0 ^ 2 := by
    calc ∑ j ∈ T, (P.R - P.ct j * H0) ≤ ∑ j ∈ T, max 0 (P.R - P.ct j * H0) :=
          Finset.sum_le_sum (fun j _ => le_max_right _ _)
      _ ≤ ∑ j, max 0 (P.R - P.ct j * H0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => le_max_left _ _)
      _ = _ := hroot
  have hexp : ∑ j ∈ T, (P.R - P.ct j * H0)
      = (T.card : ℝ) * P.R - H0 * ∑ j ∈ T, P.ct j := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hexp] at hsub
  have hiT : i ∈ T := by simp [hT]
  have hC : 0 < ∑ j ∈ T, P.ct j := Finset.sum_pos (fun j _ => hctpos j) ⟨i, hiT⟩
  set C := ∑ j ∈ T, P.ct j
  set x := P.R / P.ct i with hx
  have hxct : P.ct i * x = P.R := by rw [hx]; field_simp
  have hxH : H0 < x := by rw [hx, lt_div_iff₀ hcti]; linarith
  have hx0 : 0 < x := lt_trans hH0 hxH
  have h1 : (T.card : ℝ) * P.R - x * C < P.R + P.γ * x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0.le hxH.le 2) hγ]
  have h2 : ((T.card : ℝ) * P.ct i - C) * x < (P.ct i + P.γ * P.R / P.ct i) * x := by
    have e1 : ((T.card : ℝ) * P.ct i - C) * x = (T.card : ℝ) * P.R - x * C := by
      rw [← hxct]; ring
    have e2 : (P.ct i + P.γ * P.R / P.ct i) * x = P.R + P.γ * x ^ 2 := by
      rw [hx]; field_simp
    rw [e1, e2]; exact h1
  exact lt_of_mul_lt_mul_right h2 hx0.le

include hP hsel in
/-- Key step: a miner of `A(0)` whose cost is `c_i(min{1/η,1})`, while every miner's cost is at
least its invested cost, is active. -/
lemma A0_key (i : Fin N) (hi : i ∈ A0 hstar) {c' h' : Fin N → ℝ}
    (F' : EqFacts c' P.R P.γ h') (hc' : ∀ j, ee P j ≤ c' j) (hci : c' i = ee P i) :
    0 < h' i := by
  have hA := A0_ineq P hP hstar hsel i hi
  by_contra hneg
  have hi0 : h' i = 0 := le_antisymm (not_lt.1 hneg) (F'.nn i)
  have hRi : P.R ≤ ee P i * aggH h' := by
    have := (F'.act i).not.1 (by rw [hi0]; exact lt_irrefl 0)
    push_neg at this
    rwa [hci] at this
  set H' := aggH h' with hH'
  have hH'0 := F'.Hpos
  have hR := hP.R_pos
  have hγ := hP.γ_nonneg
  have hei := ee_pos P hP i
  have hcti : 0 < P.ct i := lt_trans hP.c0_pos (hP.c0_lt i)
  set T := Finset.univ.filter (fun j => P.ct j ≤ P.ct i) with hT
  set y := P.R / ee P i with hy
  have hy0 : 0 < y := by positivity
  have hyH : y ≤ H' := by rw [hy, div_le_iff₀ hei]; linarith
  have hye : y * ee P i = P.R := by rw [hy]; field_simp
  have hroot := F'.root
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => P.ct j ≤ P.ct i)] at hroot
  have hnot : ∑ j ∈ Finset.univ.filter (fun j => ¬ P.ct j ≤ P.ct i), max 0 (P.R - c' j * H') = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
    apply max_eq_left
    have h1 := ee_mono P hP hj.le
    have h2 := hc' j
    nlinarith
  rw [hnot, add_zero] at hroot
  have hTle : ∑ j ∈ T, max 0 (P.R - c' j * H') ≤ ∑ j ∈ T, (P.R - ee P j * y) := by
    apply Finset.sum_le_sum
    intro j hj
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have h1 := ee_mono P hP hj
    have h2 := hc' j
    have h3 := ee_pos P hP j
    apply max_le
    · nlinarith
    · nlinarith
  rw [← hT] at hroot
  rw [hroot] at hTle
  -- evaluate the right-hand side
  set u := 1 - qbar P with hu
  have hq := qbar_mem P hP
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  have hu1 : u < 1 := by rw [hu]; linarith
  have hee : ∀ j, ee P j = u * P.ct j + qbar P * P.c0 := fun j => by rw [ee_eq]
  have hsumT : ∑ j ∈ T, (P.R - ee P j * y)
      = y * (u * ((T.card : ℝ) * P.ct i - ∑ j ∈ T, P.ct j)) := by
    have : ∑ j ∈ T, (P.R - ee P j * y)
        = ∑ j ∈ T, (y * (u * (P.ct i - P.ct j))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← hye, hee, hee]; ring
    rw [this, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul]
  rw [hsumT] at hTle
  set A := (T.card : ℝ) * P.ct i - ∑ j ∈ T, P.ct j
  have hc0 := hP.c0_pos
  have he_i : ee P i = u * P.ct i + qbar P * P.c0 := hee i
  have hk1 : u * A ≤ u * (P.ct i + P.γ * P.R / P.ct i) := mul_le_mul_of_nonneg_left hA.le hu0
  have hk2 : u * P.ct i < ee P i := by rw [he_i]; nlinarith
  have hk3 : u * (P.γ * P.R / P.ct i) ≤ P.γ * P.R / ee P i := by
    rw [mul_div_assoc', div_le_div_iff₀ hcti hei]
    have : u * ee P i ≤ P.ct i := by
      have := ee_lt_ct P hP i
      nlinarith
    have : 0 ≤ P.γ * P.R := by positivity
    nlinarith
  have hk4 : u * A < ee P i + P.γ * P.R / ee P i := by
    have : u * (P.ct i + P.γ * P.R / P.ct i) = u * P.ct i + u * (P.γ * P.R / P.ct i) := by ring
    linarith
  have hk5 : y * (u * A) < y * (ee P i + P.γ * P.R / ee P i) := mul_lt_mul_of_pos_left hk4 hy0
  have hk6 : y * (ee P i + P.γ * P.R / ee P i) = P.R + P.γ * y ^ 2 := by
    rw [hy]; field_simp
  have hk7 : P.γ * y ^ 2 ≤ P.γ * H' ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0.le hyH 2) hγ
  linarith

variable {P hstar}

include hP hsel in
/-- Step 1: at every equilibrium investment, `A(0) ⊆ A(β*)`. -/
lemma A0_active {β : Fin N → ℝ} (hinv : IsInvEq P hstar β) (i : Fin N) (hi : i ∈ A0 hstar) :
    0 < hstar β i := by
  have hβ : Box β := hinv.1
  have F := EF P hP hstar hsel hβ
  by_contra hneg
  have hi0 : hstar β i = 0 := le_antisymm (not_lt.1 hneg) (F.nn i)
  have hbb := betaBar_mem P hP
  have hβ'box : Box (Function.update β i (betaBar P)) := box_update hβ i _ ⟨hbb.1.le, hbb.2⟩
  have F' := EF P hP hstar hsel hβ'box
  have hdev := hinv.2 i (betaBar P) ⟨hbb.1.le, hbb.2⟩
  rw [invPayoff_eq' P hP hstar hsel hβ'box, invPayoff_eq' P hP hstar hsel hβ] at hdev
  simp only [hi, not_true_eq_false, false_and, if_false, sub_zero] at hdev
  have hp0 : payoff (cost P β) P.R P.γ (hstar β) i = 0 := by
    rw [payoff_eq _ _ _ _ _ F.Hpos.ne', hi0]; ring
  rw [hp0] at hdev
  have hact : 0 < hstar (Function.update β i (betaBar P)) i :=
    A0_key P hP hstar hsel i hi F' (cost_ge_ee P hP hβ'box)
      (by rw [cost_update_self]; rfl)
  exact absurd hdev (not_le.2 (payoff_pos hP.R_pos hP.γ_nonneg F' i hact))

include hP hsel in
/-- Step 2: inactive miners invest `0`. -/
lemma inactive_zero {β : Fin N → ℝ} (hinv : IsInvEq P hstar β) (i : Fin N)
    (hi0 : hstar β i = 0) : β i = 0 := by
  have hβ : Box β := hinv.1
  have F := EF P hP hstar hsel hβ
  have hiA : i ∉ A0 hstar := fun hi => by
    have := A0_active hP hsel hinv i hi; rw [hi0] at this; exact lt_irrefl _ this
  by_contra hne
  have hpos : 0 < β i := lt_of_le_of_ne (hβ i).1 (Ne.symm hne)
  have hβ'box : Box (Function.update β i 0) := box_update hβ i _ ⟨le_rfl, zero_le_one⟩
  have F' := EF P hP hstar hsel hβ'box
  have hdev := hinv.2 i 0 ⟨le_rfl, zero_le_one⟩
  rw [invPayoff_eq' P hP hstar hsel hβ'box, invPayoff_eq' P hP hstar hsel hβ] at hdev
  simp only [Function.update_self, lt_irrefl, and_false, if_false, sub_zero, hiA, hpos,
    not_false_eq_true, and_self, if_true] at hdev
  have hp0 : payoff (cost P β) P.R P.γ (hstar β) i = 0 := by
    rw [payoff_eq _ _ _ _ _ F.Hpos.ne', hi0]; ring
  rw [hp0] at hdev
  have := payoff_nonneg hP.R_pos hP.γ_nonneg F' i
  linarith [hP.K_pos]

include hP hsel in
/-- Step 3: active miners in `A(0)` or already investing invest `min{1/η,1}`. -/
lemma active_inv {β : Fin N → ℝ} (hinv : IsInvEq P hstar β) (i : Fin N)
    (hact : 0 < hstar β i) (hcase : i ∈ A0 hstar ∨ 0 < β i) : β i = betaBar P := by
  have hβ : Box β := hinv.1
  have F := EF P hP hstar hsel hβ
  by_contra hne
  have hbb := betaBar_mem P hP
  have hβ'box : Box (Function.update β i (betaBar P)) := box_update hβ i _ ⟨hbb.1.le, hbb.2⟩
  have F' := EF P hP hstar hsel hβ'box
  have hdev := hinv.2 i (betaBar P) ⟨hbb.1.le, hbb.2⟩
  rw [invPayoff_eq' P hP hstar hsel hβ'box, invPayoff_eq' P hP hstar hsel hβ] at hdev
  have hlt : payoff (cost P β) P.R P.γ (hstar β) i
      < payoff (cost P (Function.update β i (betaBar P))) P.R P.γ
          (hstar (Function.update β i (betaBar P))) i := by
    apply payoff_own_strict (cost_pos P hP hβ'box) hP.R_pos hP.γ_nonneg F F' i
    · intro j hj; exact cost_update_ne P β i j _ hj
    · rw [cost_update_self, cost_eq]
      exact (costAt_ge P hP i (β i) (hβ i)).2 hne
    · exact hact
  have hK : (if i ∉ A0 hstar ∧ 0 < Function.update β i (betaBar P) i then P.K else 0)
      = (if i ∉ A0 hstar ∧ 0 < β i then P.K else 0) := by
    rcases hcase with h | h
    · simp [h]
    · simp [h, hbb.1]
  rw [hK] at hdev
  linarith

include hP hsel in
/-- Step 4: at an equilibrium investment no cost exceeds its initial value. -/
lemma cost_le_ct {β : Fin N → ℝ} (hinv : IsInvEq P hstar β) (j : Fin N) :
    cost P β j ≤ P.ct j := by
  have hβ : Box β := hinv.1
  have F := EF P hP hstar hsel hβ
  rcases (hβ j).1.lt_or_eq with hpos | hz
  · rcases (F.nn j).lt_or_eq with hact | hin
    · have := active_inv hP hsel hinv j hact (Or.inr hpos)
      rw [cost_eq, this]
      exact (ee_lt_ct P hP j).le
    · have := inactive_zero hP hsel hinv j hin.symm
      linarith
  · rw [cost_eq, ← hz, costAt_zero]

include hP hsel in
/-- Step 5: every active miner invests `min{1/η,1}`. -/
lemma active_betaBar {β : Fin N → ℝ} (hinv : IsInvEq P hstar β) (i : Fin N)
    (hact : 0 < hstar β i) : β i = betaBar P := by
  by_cases hcase : i ∈ A0 hstar ∨ 0 < β i
  · exact active_inv hP hsel hinv i hact hcase
  · exfalso
    push_neg at hcase
    have hβ : Box β := hinv.1
    have F := EF P hP hstar hsel hβ
    have hz : β i = 0 := le_antisymm hcase.2 (hβ i).1
    have hci : cost P β i = P.ct i := by rw [cost_eq, hz, costAt_zero]
    have := inactive_of_le P hP hstar hsel hβ (cost_le_ct hP hsel hinv) i hcase.1 hci
    have := (F.act i).1 hact
    linarith

include hP hsel in
lemma eq_form {β : Fin N → ℝ} (hinv : IsInvEq P hstar β) (i : Fin N) :
    β i = if i ∈ active hstar β then betaBar P else 0 := by
  have hmem : i ∈ active hstar β ↔ 0 < hstar β i := by simp [active]
  split_ifs with h
  · exact active_betaBar hP hsel hinv i (hmem.1 h)
  · have F := EF P hP hstar hsel hinv.1
    have : hstar β i = 0 := le_antisymm (not_lt.1 (fun h' => h (hmem.2 h'))) (F.nn i)
    exact inactive_zero hP hsel hinv i this

end game

end PoW51Aux


open PoWMining.Equilibrium (aggH)

namespace PoW51Aux
open PoWMining.Investment

variable {N : ℕ}

/-- Gross profit of the last investor at the threshold profile `β^{(i+1)}`. -/
noncomputable def G (P : InvParams N) (hstar : (Fin N → ℝ) → Fin N → ℝ) (i : Fin N) : ℝ :=
  payoff (cost P (betaK P (i.val + 1))) P.R P.γ (hstar (betaK P (i.val + 1))) i

lemma cost_betaK (P : InvParams N) (n : ℕ) (j : Fin N) :
    cost P (betaK P n) j = if j.val < n then ee P j else P.ct j := by
  rw [cost_eq]; unfold betaK
  split_ifs
  · rfl
  · exact costAt_zero P j

lemma cost_betaK_le_ct (P : InvParams N) (hP : P.Standing) (n : ℕ) (j : Fin N) :
    cost P (betaK P n) j ≤ P.ct j := by
  rw [cost_betaK]; split_ifs
  · exact (ee_lt_ct P hP j).le
  · exact le_rfl

lemma cost_betaK_anti (P : InvParams N) (hP : P.Standing) {m m' : ℕ} (hm : m ≤ m') (j : Fin N) :
    cost P (betaK P m') j ≤ cost P (betaK P m) j := by
  rw [cost_betaK, cost_betaK]
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact (ee_lt_ct P hP j).le
  · omega
  · exact le_rfl

lemma betaK_update_succ (P : InvParams N) (n : ℕ) (hn : n < N) :
    Function.update (betaK P n) ⟨n, hn⟩ (betaBar P) = betaK P (n + 1) := by
  funext j
  by_cases hj : j = ⟨n, hn⟩
  · subst hj; simp [betaK]
  · rw [Function.update_of_ne hj]
    have : j.val ≠ n := fun h => hj (Fin.ext h)
    unfold betaK
    split_ifs <;> first | rfl | omega

lemma betaK_update_pred (P : InvParams N) (n : ℕ) (hn1 : 1 ≤ n) (hn : n - 1 < N) :
    Function.update (betaK P n) ⟨n - 1, hn⟩ 0 = betaK P (n - 1) := by
  funext j
  by_cases hj : j = ⟨n - 1, hn⟩
  · subst hj; simp [betaK]
  · rw [Function.update_of_ne hj]
    have : j.val ≠ n - 1 := fun h => hj (Fin.ext h)
    unfold betaK
    split_ifs <;> first | rfl | omega

section game

variable {P : InvParams N} (hP : P.Standing) {hstar : (Fin N → ℝ) → Fin N → ℝ}
  (hsel : IsSelection P hstar)

include hP hsel in
lemma two_le_A0 : 2 ≤ (A0 hstar).card := by
  have F0 := EF P hP hstar hsel box_zero
  obtain ⟨j, hj⟩ := exists_active F0
  have hsum : 0 < ∑ k ∈ Finset.univ.erase j, hstar 0 k := by
    have := Finset.add_sum_erase Finset.univ (hstar 0) (Finset.mem_univ j)
    have hS := F0.Spos j
    unfold aggH at hS; linarith
  obtain ⟨k, hkm, hkp⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ.erase j)
    (f := fun _ => (0:ℝ)) (g := hstar 0) (by simpa using hsum)
  rw [Nat.succ_le_iff, Finset.one_lt_card]
  exact ⟨j, by simp [A0, hj], k, by simp [A0, hkp], (Finset.ne_of_mem_erase hkm).symm⟩

include hP hsel in
lemma mem_A0_lt (j : Fin N) : j ∈ A0 hstar ↔ j.val < (A0 hstar).card := by
  constructor
  · intro hj
    have hsub : Finset.Iic j ⊆ A0 hstar := fun k hk =>
      A0_down P hP hstar hsel (Finset.mem_Iic.1 hk) hj
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hj
    by_contra hn
    have hsub : A0 hstar ⊆ Finset.Iio j := by
      intro k hk
      rw [Finset.mem_Iio]
      by_contra hk'
      push_neg at hk'
      exact hn (A0_down P hP hstar hsel hk' hk)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

include hP hsel in
lemma inactive_betaK (n : ℕ) (j : Fin N) (hj : j ∉ A0 hstar) (hjn : ¬ j.val < n) :
    payoff (cost P (betaK P n)) P.R P.γ (hstar (betaK P n)) j = 0 := by
  have F := EF P hP hstar hsel (box_betaK P hP n)
  apply payoff_zero hP.R_pos hP.γ_nonneg F
  apply inactive_of_le P hP hstar hsel (box_betaK P hP n) (cost_betaK_le_ct P hP n) j hj
  rw [cost_betaK, if_neg hjn]

include hP hsel in
lemma G_step (i j : Fin N) (hij : j.val = i.val + 1) : G P hstar j ≤ G P hstar i := by
  unfold G
  have F1 := EF P hP hstar hsel (box_betaK P hP (i.val + 1))
  have F2 := EF P hP hstar hsel (box_betaK P hP (j.val + 1))
  have hij' : i ≤ j := by rw [Fin.le_def]; omega
  calc payoff (cost P (betaK P (j.val + 1))) P.R P.γ (hstar (betaK P (j.val + 1))) j
      ≤ payoff (cost P (betaK P (j.val + 1))) P.R P.γ (hstar (betaK P (j.val + 1))) i := by
        apply payoff_mono_same hP.R_pos hP.γ_nonneg F2
        rw [cost_betaK, cost_betaK, if_pos (by omega), if_pos (by omega)]
        exact ee_mono P hP (hP.sorted hij')
    _ ≤ _ := by
        apply payoff_rp (cost_pos P hP (box_betaK P hP _)) hP.R_pos hP.γ_nonneg
          (hsel _ (box_betaK P hP _)) F1 F2 i i
        · exact H_le_of_le (cost_pos P hP (box_betaK P hP _)) hP.γ_nonneg F1 F2
            (cost_betaK_anti P hP (by omega))
        · rw [cost_betaK, cost_betaK, if_pos (by omega), if_pos (by omega)]

include hP hsel in
lemma G_anti {i j : Fin N} (hij : i ≤ j) : G P hstar j ≤ G P hstar i := by
  have key : ∀ d : ℕ, ∀ i j : Fin N, j.val = i.val + d → G P hstar j ≤ G P hstar i := by
    intro d
    induction d with
    | zero =>
      intro i j h
      have : j = i := Fin.ext (by simpa using h)
      rw [this]
    | succ d ih =>
      intro i j h
      have hk : i.val + d < N := by omega
      exact le_trans (G_step hP hsel ⟨i.val + d, hk⟩ j (by simp; omega))
        (ih i ⟨i.val + d, hk⟩ rfl)
  exact key (j.val - i.val) i j (by rw [Fin.le_def] at hij; omega)

include hP hsel in
lemma eq_le_n {n : ℕ} (hinv : IsInvEq P hstar (betaK P n)) : (A0 hstar).card ≤ n := by
  have ha := two_le_A0 hP hsel
  have hcard : (A0 hstar).card ≤ N := by
    have := Finset.card_le_univ (A0 hstar); simpa using this
  have hlt : (A0 hstar).card - 1 < N := by omega
  have hj : (⟨(A0 hstar).card - 1, hlt⟩ : Fin N) ∈ A0 hstar := by
    rw [mem_A0_lt hP hsel]; show (A0 hstar).card - 1 < (A0 hstar).card; omega
  have hact := A0_active hP hsel hinv _ hj
  have := active_betaBar hP hsel hinv _ hact
  unfold betaK at this
  split_ifs at this with h
  · simp at h; omega
  · exact absurd this.symm (ne_of_gt (betaBar_mem P hP).1)

include hP hsel in
lemma eq_entry_le {n : ℕ} (hinv : IsInvEq P hstar (betaK P n)) (hn : n < N)
    (hiA : (⟨n, hn⟩ : Fin N) ∉ A0 hstar) : G P hstar ⟨n, hn⟩ ≤ P.K := by
  have hbb := betaBar_mem P hP
  have hdev := hinv.2 ⟨n, hn⟩ (betaBar P) ⟨hbb.1.le, hbb.2⟩
  rw [betaK_update_succ P n hn,
    invPayoff_eq' P hP hstar hsel (box_betaK P hP _),
    invPayoff_eq' P hP hstar hsel (box_betaK P hP _)] at hdev
  have h1 : betaK P (n + 1) ⟨n, hn⟩ = betaBar P := by simp [betaK]
  have h2 : betaK P n ⟨n, hn⟩ = 0 := by simp [betaK]
  rw [h1, h2, inactive_betaK hP hsel n _ hiA (by simp)] at hdev
  simp only [hiA, not_false_eq_true, hbb.1, and_self, if_true, lt_irrefl, and_false,
    if_false, sub_zero] at hdev
  unfold G
  linarith

include hP hsel in
lemma eq_exit_ge {n : ℕ} (hinv : IsInvEq P hstar (betaK P n)) (hn1 : 1 ≤ n) (hn : n - 1 < N)
    (hiA : (⟨n - 1, hn⟩ : Fin N) ∉ A0 hstar) : P.K ≤ G P hstar ⟨n - 1, hn⟩ := by
  have hdev := hinv.2 ⟨n - 1, hn⟩ 0 ⟨le_rfl, zero_le_one⟩
  rw [betaK_update_pred P n hn1 hn,
    invPayoff_eq' P hP hstar hsel (box_betaK P hP _),
    invPayoff_eq' P hP hstar hsel (box_betaK P hP _)] at hdev
  have h1 : betaK P (n - 1) ⟨n - 1, hn⟩ = 0 := by simp [betaK]
  have h2 : betaK P n ⟨n - 1, hn⟩ = betaBar P := by simp [betaK]; omega
  have hbb := betaBar_mem P hP
  rw [h1, h2] at hdev
  simp only [hiA, not_false_eq_true, hbb.1, and_self, if_true, lt_irrefl, and_false,
    if_false, sub_zero] at hdev
  have := payoff_nonneg hP.R_pos hP.γ_nonneg (EF P hP hstar hsel (box_betaK P hP (n - 1)))
    ⟨n - 1, hn⟩
  unfold G
  have e : (⟨n - 1, hn⟩ : Fin N).val + 1 = n := by simp; omega
  rw [e]
  linarith

end game

end PoW51Aux


open PoWMining.Equilibrium (aggH)

namespace PoW51Aux
open PoWMining.Investment

variable {N : ℕ}

section game

variable {P : InvParams N} (hP : P.Standing) {hstar : (Fin N → ℝ) → Fin N → ℝ}
  (hsel : IsSelection P hstar)

include hP hsel in
lemma not_mem_A0_of_ge (j : Fin N) (hj : (A0 hstar).card ≤ j.val) : j ∉ A0 hstar := by
  intro h
  have := (mem_A0_lt hP hsel j).1 h
  omega

include hP hsel in
lemma exists_threshold (hgen : Generic P hstar) :
    ∃ n, 2 ≤ n ∧ n ≤ N ∧ IsInvEq P hstar (betaK P n) := by
  classical
  set a := (A0 hstar).card with ha_def
  have ha2 := two_le_A0 hP hsel
  have haN : a ≤ N := by have := Finset.card_le_univ (A0 hstar); simpa using this
  have hN2 := hP.two_le
  let M := (Finset.range (N + 1)).filter
    (fun m => a ≤ m ∧ (m = a ∨ ∃ h : m - 1 < N, P.K ≤ G P hstar ⟨m - 1, h⟩))
  have haM : a ∈ M := by
    simp only [M, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, le_rfl, Or.inl trivial⟩
  set n := M.max' ⟨a, haM⟩ with hn_def
  have hnM : n ∈ M := Finset.max'_mem _ _
  have hmax : ∀ m ∈ M, m ≤ n := fun m hm => Finset.le_max' _ _ hm
  simp only [M, Finset.mem_filter, Finset.mem_range] at hnM
  obtain ⟨hnN1, han, hnor⟩ := hnM
  have hnN : n ≤ N := by omega
  have hgt : ∀ (h : n - 1 < N), a < n → P.K < G P hstar ⟨n - 1, h⟩ := by
    intro h hlt
    rcases hnor with he | ⟨h', hK⟩
    · omega
    · have hnA : (⟨n - 1, h⟩ : Fin N) ∉ A0 hstar :=
        not_mem_A0_of_ge hP hsel _ (by change a ≤ n - 1; omega)
      have hne := hgen ⟨n - 1, h⟩ hnA
      exact lt_of_le_of_ne hK (Ne.symm hne)
  have hlt : ∀ (h : n < N), G P hstar ⟨n, h⟩ < P.K := by
    intro h
    by_contra hge
    push_neg at hge
    have hM : n + 1 ∈ M := by
      simp only [M, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, Or.inr ⟨by omega, ?_⟩⟩
      simpa using hge
    have := hmax _ hM
    omega
  refine ⟨n, by omega, hnN, box_betaK P hP n, ?_⟩
  intro i b hb
  have F := EF P hP hstar hsel (box_betaK P hP n)
  have hbb := betaBar_mem P hP
  have hβ'box : Box (Function.update (betaK P n) i b) := box_update (box_betaK P hP n) i b hb
  have F' := EF P hP hstar hsel hβ'box
  rw [invPayoff_eq' P hP hstar hsel hβ'box, invPayoff_eq' P hP hstar hsel (box_betaK P hP n)]
  simp only [Function.update_self]
  by_cases hin : i.val < n
  · have hbi : betaK P n i = betaBar P := by simp [betaK, hin]
    rw [hbi]
    by_cases hb0 : b = 0
    · subst hb0
      simp only [lt_irrefl, and_false, if_false, sub_zero]
      by_cases hiA : i ∈ A0 hstar
      · simp only [hiA, not_true_eq_false, false_and, if_false, sub_zero]
        apply payoff_own_mono (cost_pos P hP (box_betaK P hP n)) hP.R_pos hP.γ_nonneg F F' i
        · intro j hj; exact cost_update_ne P _ i j _ hj
        · rw [cost_update_self, costAt_zero, cost_betaK, if_pos hin]
          exact (ee_lt_ct P hP i).le
      · simp only [hiA, not_false_eq_true, hbb.1, and_self, if_true]
        have hz : payoff (cost P (Function.update (betaK P n) i 0)) P.R P.γ
            (hstar (Function.update (betaK P n) i 0)) i = 0 := by
          apply payoff_zero hP.R_pos hP.γ_nonneg F'
          apply inactive_of_le P hP hstar hsel hβ'box _ i hiA
          · rw [cost_update_self, costAt_zero]
          · intro j
            by_cases hj : j = i
            · subst hj; rw [cost_update_self, costAt_zero]
            · rw [cost_update_ne P _ i j _ hj]; exact cost_betaK_le_ct P hP n j
        rw [hz]
        have hai : a ≤ i.val := by
          by_contra h
          push_neg at h
          exact hiA ((mem_A0_lt hP hsel i).2 h)
        have hn1 : n - 1 < N := by omega
        have h1 := hgt hn1 (by omega)
        have h2 : G P hstar ⟨n - 1, hn1⟩
            ≤ payoff (cost P (betaK P n)) P.R P.γ (hstar (betaK P n)) i := by
          unfold G
          have e : (⟨n - 1, hn1⟩ : Fin N).val + 1 = n := by simp; omega
          rw [e]
          apply payoff_mono_same hP.R_pos hP.γ_nonneg F
          rw [cost_betaK, cost_betaK, if_pos hin, if_pos (by simp; omega)]
          exact ee_mono P hP (hP.sorted (by rw [Fin.le_def]; simp; omega))
        linarith
    · have hbpos : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hb0)
      have hK : (if i ∉ A0 hstar ∧ 0 < b then P.K else 0)
          = (if i ∉ A0 hstar ∧ 0 < betaBar P then P.K else 0) := by
        simp [hbpos, hbb.1]
      rw [hK]
      have := payoff_own_mono (cost_pos P hP (box_betaK P hP n)) hP.R_pos hP.γ_nonneg F F' i
        (fun j hj => cost_update_ne P _ i j _ hj)
        (by rw [cost_update_self, cost_betaK, if_pos hin]; exact (costAt_ge P hP i b hb).1)
      linarith
  · have hiA : i ∉ A0 hstar := not_mem_A0_of_ge hP hsel i (by omega)
    have hbi : betaK P n i = 0 := by simp [betaK, hin]
    rw [hbi, inactive_betaK hP hsel n i hiA hin]
    simp only [lt_irrefl, and_false, if_false, sub_zero]
    by_cases hb0 : b = 0
    · subst hb0
      simp only [lt_irrefl, and_false, if_false, sub_zero]
      rw [show Function.update (betaK P n) i 0 = betaK P n by
        rw [← hbi]; exact Function.update_eq_self i _]
      rw [inactive_betaK hP hsel n i hiA hin]
    · have hbpos : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hb0)
      simp only [hiA, not_false_eq_true, hbpos, and_self, if_true]
      have hnN' : n < N := by have := i.isLt; omega
      have hGlt := hlt hnN'
      suffices hs : payoff (cost P (Function.update (betaK P n) i b)) P.R P.γ
          (hstar (Function.update (betaK P n) i b)) i ≤ G P hstar ⟨n, hnN'⟩ by linarith
      have hk1 : Box (betaK P (n + 1)) := box_betaK P hP _
      have F1 := EF P hP hstar hsel hk1
      by_cases hik : i.val = n
      · have hik' : i = ⟨n, hnN'⟩ := Fin.ext hik
        subst hik'
        unfold G
        apply payoff_own_mono (cost_pos P hP hk1) hP.R_pos hP.γ_nonneg F1 F' _
        · intro j hj
          have hjn : j.val ≠ n := fun h => hj (Fin.ext h)
          rw [cost_update_ne P _ _ j _ hj, cost_betaK, cost_betaK]
          split_ifs <;> first | rfl | omega
        · rw [cost_update_self, cost_betaK, if_pos (by simp)]
          exact (costAt_ge P hP _ b hb).1
      · have hni : n < i.val := by omega
        set k : Fin N := ⟨n, hnN'⟩ with hk
        have hki : k ≠ i := fun h => hik (by rw [← h])
        have hkle : k ≤ i := by rw [Fin.le_def]; simp [k]; omega
        set c' := cost P (Function.update (betaK P n) i b) with hc'
        let Z := Function.update c' i (ee P k)
        have hZpos : ∀ j, 0 < Z j := by
          intro j
          by_cases hj : j = i
          · subst hj; simp [Z]; exact ee_pos P hP k
          · simp only [Z, Function.update_of_ne hj]; exact cost_pos P hP hβ'box j
        obtain ⟨hZ, heqZ⟩ := exists_eq hP.two_le hZpos hP.R_pos hP.γ_nonneg
        have FZ := eqFacts (by omega) hZpos hP.R_pos hP.γ_nonneg heqZ
        have step1 : payoff c' P.R P.γ (hstar (Function.update (betaK P n) i b)) i
            ≤ payoff Z P.R P.γ hZ i := by
          apply payoff_own_mono hZpos hP.R_pos hP.γ_nonneg FZ F' i
          · intro j hj; simp [Z, Function.update_of_ne hj]
          · simp only [Z, Function.update_self]
            rw [hc', cost_update_self]
            exact le_trans (ee_mono P hP (hP.sorted hkle)) (costAt_ge P hP i b hb).1
        have hHZ : aggH (hstar (betaK P (n + 1))) ≤ aggH hZ := by
          apply H_le_of_sum (cost_pos P hP hk1) hP.γ_nonneg F1 FZ
          rw [← Equiv.sum_comp (Equiv.swap k i)]
          apply Finset.sum_le_sum
          intro j _
          apply max_le_max le_rfl
          apply sub_le_sub_left
          apply mul_le_mul_of_nonneg_right _ FZ.Hpos.le
          by_cases hj : j = i
          · subst hj
            rw [Equiv.swap_apply_right]
            simp only [Z, Function.update_self]
            rw [cost_betaK, if_pos (by simp [k])]
          · by_cases hj2 : j = k
            · subst hj2
              rw [Equiv.swap_apply_left]
              simp only [Z, Function.update_of_ne hj]
              rw [hc', cost_update_ne P _ i _ _ hj, cost_betaK, cost_betaK,
                if_neg (by simp [k]), if_neg (by omega)]
              exact hP.sorted hkle
            · rw [Equiv.swap_apply_of_ne_of_ne hj2 hj]
              simp only [Z, Function.update_of_ne hj]
              have hjn : j.val ≠ n := fun h => hj2 (Fin.ext h)
              rw [hc', cost_update_ne P _ i _ _ hj, cost_betaK, cost_betaK]
              split_ifs <;> first | exact le_rfl | omega
        have step2 : payoff Z P.R P.γ hZ i ≤ G P hstar k := by
          unfold G
          apply payoff_rp (cost_pos P hP hk1) hP.R_pos hP.γ_nonneg (hsel _ hk1) F1 FZ k i hHZ
          simp only [Z, Function.update_self]
          rw [cost_betaK, if_pos (by simp [k])]
        exact step1.trans step2

end game

end PoW51Aux

open PoWMining.Investment in
theorem solution {N : ℕ} (P : InvParams N) (hP : P.Standing)
    (hstar : (Fin N → ℝ) → Fin N → ℝ) (hsel : IsSelection P hstar)
    (hgen : Generic P hstar) :
    (∃! n : ℕ, 2 ≤ n ∧ n ≤ N ∧ IsInvEq P hstar (betaK P n)) ∧
    (∀ n : ℕ, 2 ≤ n → n ≤ N → IsInvEq P hstar (betaK P n) →
      (active hstar (betaK P n)).card = n ∧ A0 hstar ⊆ active hstar (betaK P n)) ∧
    (∀ β : Fin N → ℝ, IsInvEq P hstar β →
      A0 hstar ⊆ active hstar β ∧ ∀ i ∈ A0 hstar, β i = betaBar P) ∧
    (∀ K' : ℝ, P.K ≤ K' → Generic { P with K := K' } hstar →
      ∀ n n' : ℕ, 2 ≤ n → n ≤ N → 2 ≤ n' → n' ≤ N →
        IsInvEq P hstar (betaK P n) → IsInvEq { P with K := K' } hstar (betaK P n') →
        n' ≤ n) := by
  open PoW51Aux in
  have hA0sub : ∀ β : Fin N → ℝ, IsInvEq P hstar β → A0 hstar ⊆ active hstar β := by
    intro β hinv j hj
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
    exact A0_active hP hsel hinv j hj
  open PoW51Aux in
  have hnot : ∀ n m : ℕ, 2 ≤ n → n ≤ N → 2 ≤ m → m ≤ N →
      IsInvEq P hstar (betaK P n) → IsInvEq P hstar (betaK P m) → ¬ n < m := by
    intro n m _ _ _ hmN hn hm hlt
    have ha := eq_le_n hP hsel hn
    have hnN : n < N := by omega
    have hiA : (⟨n, hnN⟩ : Fin N) ∉ A0 hstar := not_mem_A0_of_ge hP hsel _ (by simpa using ha)
    have h1 := eq_entry_le hP hsel hn hnN hiA
    have h1' : G P hstar ⟨n, hnN⟩ < P.K := lt_of_le_of_ne h1 (hgen _ hiA)
    have hm1 : m - 1 < N := by omega
    have hjA : (⟨m - 1, hm1⟩ : Fin N) ∉ A0 hstar :=
      not_mem_A0_of_ge hP hsel _ (by change _ ≤ m - 1; omega)
    have h2 := eq_exit_ge hP hsel hm (by omega) hm1 hjA
    have h3 := G_anti hP hsel (i := ⟨n, hnN⟩) (j := ⟨m - 1, hm1⟩)
      (by rw [Fin.le_def]; simp; omega)
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨n, h2, hN, hEq⟩ := PoW51Aux.exists_threshold hP hsel hgen
    refine ⟨n, ⟨h2, hN, hEq⟩, ?_⟩
    rintro m ⟨hm2, hmN, hmEq⟩
    rcases lt_trichotomy m n with h | h | h
    · exact absurd h (hnot m n hm2 hmN h2 hN hmEq hEq)
    · exact h
    · exact absurd h (hnot n m h2 hN hm2 hmN hEq hmEq)
  · intro n h2 hN hinv
    refine ⟨?_, hA0sub _ hinv⟩
    have hbb := PoW51Aux.betaBar_mem P hP
    have F := PoW51Aux.EF P hP hstar hsel hinv.1
    have hact_eq : active hstar (betaK P n)
        = Finset.univ.filter (fun j : Fin N => j.val < n) := by
      ext j
      simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        have h1 := PoW51Aux.active_betaBar hP hsel hinv j hj
        by_contra hjn
        have h2 : betaK P n j = 0 := by simp [betaK, hjn]
        linarith
      · intro hjn
        by_contra hj
        have hz : hstar (betaK P n) j = 0 := le_antisymm (not_lt.1 hj) (F.nn j)
        have h1 := PoW51Aux.inactive_zero hP hsel hinv j hz
        have h2 : betaK P n j = betaBar P := by simp [betaK, hjn]
        linarith
    rw [hact_eq, Fin.card_filter_val_lt]
    omega
  · intro β hinv
    refine ⟨hA0sub β hinv, fun i hi => ?_⟩
    exact PoW51Aux.active_betaBar hP hsel hinv i (PoW51Aux.A0_active hP hsel hinv i hi)
  · intro K' hK hgen' n n' h2 hN h2' hN' hn hn'
    by_contra hlt
    push_neg at hlt
    have hP' : ({ P with K := K' } : InvParams N).Standing :=
      ⟨hP.two_le, hP.R_pos, hP.γ_nonneg, hP.η_nonneg, lt_of_lt_of_le hP.K_pos hK, hP.sorted,
        hP.c0_pos, hP.c0_lt⟩
    have hsel' : IsSelection { P with K := K' } hstar := hsel
    have ha := PoW51Aux.eq_le_n hP hsel hn
    have hnN : n < N := by omega
    have hiA : (⟨n, hnN⟩ : Fin N) ∉ A0 hstar :=
      PoW51Aux.not_mem_A0_of_ge hP hsel _ (by simpa using ha)
    have h1 := PoW51Aux.eq_entry_le hP hsel hn hnN hiA
    have h1' : PoW51Aux.G P hstar ⟨n, hnN⟩ < P.K := lt_of_le_of_ne h1 (hgen _ hiA)
    have hm1 : n' - 1 < N := by omega
    have hjA : (⟨n' - 1, hm1⟩ : Fin N) ∉ A0 hstar :=
      PoW51Aux.not_mem_A0_of_ge hP hsel _ (by change _ ≤ n' - 1; omega)
    have h2 := PoW51Aux.eq_exit_ge hP' hsel' hn' (by omega) hm1 hjA
    have h2' : K' ≤ PoW51Aux.G P hstar ⟨n' - 1, hm1⟩ := h2
    have h3 := PoW51Aux.G_anti hP hsel (i := ⟨n, hnN⟩) (j := ⟨n' - 1, hm1⟩)
      (by rw [Fin.le_def]; simp; omega)
    linarith


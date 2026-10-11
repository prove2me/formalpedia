-- Prove2me | solution 1 for PriceQualityService.Dealer.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:25:15.327185+00:00
-- url     : https://prove2.me/submissions/a3d0f910-1779-4add-9a4b-925a4cde0440

import Mathlib
import Definitions.Def_PriceQualityService_Dealer_Model
import Definitions.Def_PriceQualityService_Dealer_Breakpoints

open Finset

namespace RRAux_PriceQualityService_Dealer_theorem_5

open PriceQualityService.Dealer

theorem denom_pos {N : ℕ} (α s p q : Fin N → ℝ) (ts tl : ℝ) (Sl Ss : Finset (Fin N)) :
    0 < choiceDenom α s p q ts tl Sl Ss := by
  unfold choiceDenom
  have h1 := Finset.sum_nonneg (fun j (_ : j ∈ Sl) => (Real.exp_pos
    (α j * q j - p j + tl * s j)).le)
  have h2 := Finset.sum_nonneg (fun j (_ : j ∈ Ss) => (Real.exp_pos
    (α j * q j - p j + ts * s j)).le)
  unfold attraction
  linarith

theorem profit_mul {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (Sl Ss : Finset (Fin N))
    (hd : Disjoint Sl Ss) :
    dealerProfit α a b c s p q ts tl Sl Ss * choiceDenom α s p q ts tl Sl Ss =
      ∑ i ∈ Sl, markup a b c p q tl i * attraction α s p q tl i +
        ∑ i ∈ Ss, markup a b c p q ts i * attraction α s p q ts i := by
  have hD := (denom_pos α s p q ts tl Sl Ss).ne'
  unfold dealerProfit
  rw [add_mul, Finset.sum_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    unfold choiceProb; rw [if_pos hi]; field_simp
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hni : i ∉ Sl := Finset.disjoint_right.mp hd hi
    unfold choiceProb; rw [if_neg hni, if_pos hi]; field_simp

theorem profit_le {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (Sl Ss : Finset (Fin N))
    (hd : Disjoint Sl Ss) (R : ℝ)
    (h : ∑ i ∈ Sl, hLong α a b c s p q tl i R + ∑ i ∈ Ss, hShort α a b c s p q ts i R ≤ R) :
    dealerProfit α a b c s p q ts tl Sl Ss ≤ R := by
  have hD := denom_pos α s p q ts tl Sl Ss
  have hm := profit_mul α a b c s p q ts tl Sl Ss hd
  unfold hLong hShort at h
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  unfold choiceDenom at hm hD
  refine le_of_mul_le_mul_right ?_ hD
  rw [hm]; nlinarith

theorem profit_eq {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (Sl Ss : Finset (Fin N))
    (hd : Disjoint Sl Ss) (R : ℝ)
    (h : ∑ i ∈ Sl, hLong α a b c s p q tl i R + ∑ i ∈ Ss, hShort α a b c s p q ts i R = R) :
    dealerProfit α a b c s p q ts tl Sl Ss = R := by
  have hD := denom_pos α s p q ts tl Sl Ss
  have hm := profit_mul α a b c s p q ts tl Sl Ss hd
  unfold hLong hShort at h
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have : dealerProfit α a b c s p q ts tl Sl Ss * choiceDenom α s p q ts tl Sl Ss =
      R * choiceDenom α s p q ts tl Sl Ss := by
    rw [hm]; unfold choiceDenom; linarith
  exact mul_right_cancel₀ hD.ne' this

theorem hMax_nonneg {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) (r : ℝ) :
    0 ≤ hMax α a b c s p q ts tl i r := le_max_right _ _

theorem hMax_anti {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) {r1 r2 : ℝ}
    (h : r1 ≤ r2) : hMax α a b c s p q ts tl i r2 ≤ hMax α a b c s p q ts tl i r1 := by
  unfold hMax hLong hShort
  have e1 := Real.exp_pos (α i * q i - p i + tl * s i)
  have e2 := Real.exp_pos (α i * q i - p i + ts * s i)
  unfold attraction
  apply max_le_max _ le_rfl
  apply max_le_max
  · exact mul_le_mul_of_nonneg_right (by linarith) e1.le
  · exact mul_le_mul_of_nonneg_right (by linarith) e2.le

theorem H_anti {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) {r1 r2 : ℝ}
    (h : r1 ≤ r2) : bigH α a b c s p q ts tl r2 ≤ bigH α a b c s p q ts tl r1 :=
  Finset.sum_le_sum fun i _ => hMax_anti α a b c s p q ts tl i h

theorem H_nonneg {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (r : ℝ) :
    0 ≤ bigH α a b c s p q ts tl r :=
  Finset.sum_nonneg fun i _ => hMax_nonneg α a b c s p q ts tl i r

theorem H_cont {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) :
    Continuous (bigH α a b c s p q ts tl) := by
  unfold bigH hMax hLong hShort
  refine continuous_finsetSum _ fun i _ => ?_
  refine Continuous.max (Continuous.max ?_ ?_) continuous_const <;> fun_prop

theorem root_exists {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) :
    ∃ R, R = bigH α a b c s p q ts tl R := by
  set H := bigH α a b c s p q ts tl with hH
  have hcont : ContinuousOn (fun r : ℝ => r - H r) (Set.Icc 0 (H 0)) :=
    (continuous_id.sub (H_cont α a b c s p q ts tl)).continuousOn
  have h0 : (0:ℝ) - H 0 ≤ 0 := by have := H_nonneg α a b c s p q ts tl 0; linarith
  have h1 : 0 ≤ H 0 - H (H 0) := by
    have := H_anti α a b c s p q ts tl (H_nonneg α a b c s p q ts tl 0); linarith
  obtain ⟨R, _, hR⟩ := intermediate_value_Icc (H_nonneg α a b c s p q ts tl 0) hcont ⟨h0, h1⟩
  exact ⟨R, by simp only at hR; linarith⟩

-- per-product algebra
theorem adj_mul (s ts tl : ℝ) (hs : 0 < s) (hts : ts < tl) :
    ((tl * Real.exp (tl * s) - ts * Real.exp (ts * s)) /
      (Real.exp (tl * s) - Real.exp (ts * s))) * (Real.exp (tl * s) - Real.exp (ts * s)) =
      tl * Real.exp (tl * s) - ts * Real.exp (ts * s) ∧
    0 < Real.exp (tl * s) - Real.exp (ts * s) := by
  have hlt : Real.exp (ts * s) < Real.exp (tl * s) :=
    Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right hts hs)
  have hpos : 0 < Real.exp (tl * s) - Real.exp (ts * s) := by linarith
  exact ⟨div_mul_cancel₀ _ hpos.ne', hpos⟩

theorem diff_formula {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (hts : ts < tl)
    (hs : ∀ i, 0 < s i) (i : Fin N) (r : ℝ) :
    hLong α a b c s p q tl i r - hShort α a b c s p q ts i r =
      Real.exp (α i * q i - p i) * (Real.exp (tl * s i) - Real.exp (ts * s i)) *
        (adjustedMarkup a b c s p q ts tl i - r) ∧
    0 < Real.exp (α i * q i - p i) * (Real.exp (tl * s i) - Real.exp (ts * s i)) := by
  obtain ⟨hA, hpos⟩ := adj_mul (s i) ts tl (hs i) hts
  refine ⟨?_, mul_pos (Real.exp_pos _) hpos⟩
  unfold hLong hShort attraction adjustedMarkup markup adjFactor
  rw [Real.exp_add, Real.exp_add]
  generalize (tl * Real.exp (tl * s i) - ts * Real.exp (ts * s i)) /
      (Real.exp (tl * s i) - Real.exp (ts * s i)) = A at hA ⊢
  linear_combination (Real.exp (α i * q i - p i) * (a i - b i * q i)) * hA

theorem x_le_ml {N : ℕ} (a b c s p q : Fin N → ℝ) (ts tl : ℝ) (hts : ts < tl)
    (hs : ∀ i, 0 < s i) (hg : ∀ i, 0 ≤ a i - b i * q i) (i : Fin N) :
    adjustedMarkup a b c s p q ts tl i ≤ markup a b c p q tl i ∧
      markup a b c p q tl i ≤ markup a b c p q ts i := by
  obtain ⟨hA, hpos⟩ := adj_mul (s i) ts tl (hs i) hts
  unfold adjustedMarkup markup adjFactor
  generalize (tl * Real.exp (tl * s i) - ts * Real.exp (ts * s i)) /
      (Real.exp (tl * s i) - Real.exp (ts * s i)) = A at hA ⊢
  have hes := Real.exp_pos (ts * s i)
  have hAtl : tl ≤ A := by
    have : (A - tl) * (Real.exp (tl * s i) - Real.exp (ts * s i)) =
        (tl - ts) * Real.exp (ts * s i) := by linear_combination hA
    have h2 : 0 ≤ (A - tl) * (Real.exp (tl * s i) - Real.exp (ts * s i)) := by
      rw [this]; exact mul_nonneg (by linarith) hes.le
    have := nonneg_of_mul_nonneg_left h2 hpos
    linarith
  have := hg i
  constructor <;> nlinarith

end RRAux_PriceQualityService_Dealer_theorem_5

open PriceQualityService.Dealer in
open RRAux_PriceQualityService_Dealer_theorem_5 in
-- Theorem 5, Wang, Ke & Cui, p. 23
theorem solution {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (hts : ts < tl)
    (hs : ∀ i, 0 < s i) (hg : ∀ i, 0 ≤ a i - b i * q i) :
    ∃ θ θ' : ℝ,
      (univ.filter fun i => θ' ≤ adjustedMarkup a b c s p q ts tl i) ⊆
          (univ.filter fun i => θ ≤ markup a b c p q ts i) ∧
      ∀ Sl Ss : Finset (Fin N), Disjoint Sl Ss →
        dealerProfit α a b c s p q ts tl Sl Ss ≤
          dealerProfit α a b c s p q ts tl
            (univ.filter fun i => θ' ≤ adjustedMarkup a b c s p q ts tl i)
            ((univ.filter fun i => θ ≤ markup a b c p q ts i) \
              univ.filter fun i => θ' ≤ adjustedMarkup a b c s p q ts tl i) := by
  obtain ⟨R, hR⟩ := root_exists α a b c s p q ts tl
  have hLS : (univ.filter fun i => R ≤ adjustedMarkup a b c s p q ts tl i) ⊆
      (univ.filter fun i => R ≤ markup a b c p q ts i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨h1, h2⟩ := x_le_ml a b c s p q ts tl hts hs hg i
    linarith
  refine ⟨R, R, hLS, fun Sl Ss hd => ?_⟩
  set L := univ.filter fun i => R ≤ adjustedMarkup a b c s p q ts tl i with hL
  set S := univ.filter fun i => R ≤ markup a b c p q ts i with hS
  have hdLS : Disjoint L (S \ L) := Finset.disjoint_sdiff
  -- value of the constructed pair
  have hval : dealerProfit α a b c s p q ts tl L (S \ L) = R := by
    apply profit_eq α a b c s p q ts tl L (S \ L) hdLS R
    have e1 : ∀ i ∈ L, hLong α a b c s p q tl i R = hMax α a b c s p q ts tl i R := by
      intro i hi
      simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨hdf, hc⟩ := diff_formula α a b c s p q ts tl hts hs i R
      obtain ⟨h1, _⟩ := x_le_ml a b c s p q ts tl hts hs hg i
      have hls : hShort α a b c s p q ts i R ≤ hLong α a b c s p q tl i R := by
        have := mul_nonneg hc.le (show 0 ≤ adjustedMarkup a b c s p q ts tl i - R by linarith)
        linarith
      have hl0 : 0 ≤ hLong α a b c s p q tl i R := by
        unfold hLong
        exact mul_nonneg (by linarith) (Real.exp_pos _).le
      unfold hMax
      rw [max_eq_left hls, max_eq_left hl0]
    have e2 : ∀ i ∈ S \ L, hShort α a b c s p q ts i R = hMax α a b c s p q ts tl i R := by
      intro i hi
      simp only [hL, hS, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        not_le] at hi
      obtain ⟨hdf, hc⟩ := diff_formula α a b c s p q ts tl hts hs i R
      have hls : hLong α a b c s p q tl i R ≤ hShort α a b c s p q ts i R := by
        have := mul_nonneg hc.le (show 0 ≤ R - adjustedMarkup a b c s p q ts tl i by linarith)
        nlinarith
      have hs0 : 0 ≤ hShort α a b c s p q ts i R := by
        unfold hShort
        exact mul_nonneg (by linarith) (Real.exp_pos _).le
      unfold hMax
      rw [max_eq_right hls, max_eq_left hs0]
    have e3 : ∀ i ∈ univ, i ∉ S → hMax α a b c s p q ts tl i R = 0 := by
      intro i _ hi
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
      obtain ⟨_, h2⟩ := x_le_ml a b c s p q ts tl hts hs hg i
      have hl : hLong α a b c s p q tl i R ≤ 0 := by
        unfold hLong
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
      have hs' : hShort α a b c s p q ts i R ≤ 0 := by
        unfold hShort
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
      unfold hMax
      exact max_eq_right (max_le hl hs')
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, add_comm,
      Finset.sum_sdiff hLS, Finset.sum_subset (Finset.subset_univ S) e3]
    exact hR.symm
  rw [hval]
  apply profit_le α a b c s p q ts tl Sl Ss hd R
  have k1 : ∑ i ∈ Sl, hLong α a b c s p q tl i R ≤ ∑ i ∈ Sl, hMax α a b c s p q ts tl i R :=
    Finset.sum_le_sum fun i _ => (le_max_left _ _).trans (le_max_left _ _)
  have k2 : ∑ i ∈ Ss, hShort α a b c s p q ts i R ≤ ∑ i ∈ Ss, hMax α a b c s p q ts tl i R :=
    Finset.sum_le_sum fun i _ => (le_max_right _ _).trans (le_max_left _ _)
  have k3 : ∑ i ∈ Sl ∪ Ss, hMax α a b c s p q ts tl i R ≤ bigH α a b c s p q ts tl R :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => hMax_nonneg α a b c s p q ts tl i R
  rw [Finset.sum_union hd] at k3
  linarith

#print axioms solution

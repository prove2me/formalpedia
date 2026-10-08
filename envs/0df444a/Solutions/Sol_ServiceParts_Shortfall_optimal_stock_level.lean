-- Prove2me | solution 1 for ServiceParts.Shortfall.optimal_stock_level
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:19:16.308354+00:00
-- url     : https://prove2.me/submissions/970230d3-50e9-4300-a032-a5251a2e064e

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_RepairStock

set_option autoImplicit false

namespace P83233cc7

open ServiceParts.Shortfall Finset

lemma eta_bounds (lamI lam mu : ℝ) (hlamI : 0 < lamI) (hstable : lam < mu) :
    0 < repairEta lamI lam mu ∧ repairEta lamI lam mu < 1 := by
  unfold repairEta
  have hd : 0 < mu - lam + lamI := by linarith
  refine ⟨div_pos hlamI hd, ?_⟩
  rw [div_lt_one hd]; linarith

lemma tail_hasSum (η : ℝ) (h0 : 0 ≤ η) (h1 : η < 1) (s : ℕ) :
    HasSum (fun j : ℕ => if s + 1 ≤ j then geomPMF η j else 0) (η ^ (s + 1)) := by
  rw [← hasSum_nat_add_iff' (s + 1)]
  have hz : ∑ i ∈ range (s + 1), (if s + 1 ≤ i then geomPMF η i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [if_neg (by omega)]
  rw [hz, sub_zero]
  have hg := (hasSum_geometric_of_lt_one h0 h1).mul_left ((1 - η) * η ^ (s + 1))
  have hne : (1 - η) ≠ 0 := by linarith
  have hf : (fun n : ℕ => if s + 1 ≤ n + (s + 1) then geomPMF η (n + (s + 1)) else 0) =
      fun i : ℕ => (1 - η) * η ^ (s + 1) * η ^ i := by
    funext n
    rw [if_pos (by omega)]
    unfold geomPMF
    ring
  have hv : η ^ (s + 1) = (1 - η) * η ^ (s + 1) * (1 - η)⁻¹ := by field_simp
  rw [← hf] at hg
  rw [hv]
  exact hg

lemma back_hasSum (η : ℝ) (h0 : 0 ≤ η) (h1 : η < 1) (s : ℕ) :
    HasSum (fun j : ℕ => if s ≤ j then ((j : ℝ) - s) * geomPMF η j else 0)
      (η ^ (s + 1) / (1 - η)) := by
  rw [← hasSum_nat_add_iff' s]
  have hz : ∑ i ∈ range s, (if s ≤ i then ((i : ℝ) - s) * geomPMF η i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [if_neg (by omega)]
  rw [hz, sub_zero]
  have hn : ‖η‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hg := (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left ((1 - η) * η ^ s)
  have hne : (1 - η) ≠ 0 := by linarith
  have hf : (fun n : ℕ => if s ≤ n + s then (((n + s : ℕ) : ℝ) - s) * geomPMF η (n + s) else 0) =
      fun i : ℕ => (1 - η) * η ^ s * ((i : ℝ) * η ^ i) := by
    funext n
    rw [if_pos (by omega)]
    unfold geomPMF
    push_cast
    ring
  have hv : η ^ (s + 1) / (1 - η) = (1 - η) * η ^ s * (η / (1 - η) ^ 2) := by
    field_simp
    ring
  rw [← hf] at hg
  rw [hv]
  exact hg

lemma geom_partial (η : ℝ) (s : ℕ) :
    ∑ j ∈ range (s + 1), geomPMF η j = 1 - η ^ (s + 1) := by
  unfold geomPMF
  rw [← Finset.mul_sum]
  linear_combination (-1 : ℝ) * geom_sum_mul η (s + 1)

lemma fin_step (η : ℝ) (s : ℕ) :
    ∑ j ∈ range (s + 1 + 1), (((s + 1 : ℕ) : ℝ) - j) * geomPMF η j =
      ∑ j ∈ range (s + 1), ((s : ℝ) - j) * geomPMF η j + (1 - η ^ (s + 1)) := by
  rw [Finset.sum_range_succ, ← geom_partial η s, ← Finset.sum_add_distrib]
  have : (((s + 1 : ℕ) : ℝ) - ((s + 1 : ℕ) : ℝ)) * geomPMF η (s + 1) = 0 := by simp
  push_cast at this ⊢
  rw [this, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma cost_step (h b η : ℝ) (h0 : 0 ≤ η) (h1 : η < 1) (s : ℕ) :
    stockCost h b η (s + 1) - stockCost h b η s = h - (h + b) * η ^ (s + 1) := by
  unfold stockCost
  rw [(back_hasSum η h0 h1 (s + 1)).tsum_eq, (back_hasSum η h0 h1 s).tsum_eq, fin_step]
  have hne : (1 - η) ≠ 0 := by linarith
  field_simp
  ring

lemma min_iff (C D : ℕ → ℝ) (hD : ∀ s, C (s + 1) - C s = D s) (hmono : Monotone D) (s : ℕ) :
    ((∀ t, C s ≤ C t) ∧ ∀ t, C t ≤ C s → s ≤ t) ↔ (0 ≤ D s ∧ ∀ t, t < s → D t < 0) := by
  have up : 0 ≤ D s → ∀ k, s ≤ k → C s ≤ C k := by
    intro hs k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_refl _
    | succ k hk ih =>
      have := hD k
      have := hmono hk
      linarith
  have down : (∀ t, t < s → D t < 0) → ∀ t, t < s → C s < C t := by
    intro H t ht
    have key : ∀ m, t + 1 ≤ m → m ≤ s → C m < C t := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base =>
        intro _
        have := hD t
        have := H t ht
        linarith
      | succ m hm ih =>
        intro hms
        have := hD m
        have := H m (by omega)
        have := ih (by omega)
        linarith
    exact key s ht le_rfl
  constructor
  · rintro ⟨hmin, hsm⟩
    refine ⟨by have := hD s; have := hmin (s + 1); linarith, ?_⟩
    intro t ht
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hlt : C (s' + 1) < C s' := by
      by_contra hc
      push_neg at hc
      have := hsm s' hc
      omega
    have := hD s'
    have := hmono (show t ≤ s' by omega)
    linarith
  · rintro ⟨hs, hneg⟩
    refine ⟨fun t => ?_, fun t ht => ?_⟩
    · rcases le_or_gt s t with h | h
      · exact up hs t h
      · exact (down hneg t h).le
    · by_contra hc
      push_neg at hc
      have := down hneg t hc
      linarith

end P83233cc7

open ServiceParts.Shortfall MeasureTheory in
theorem solution (lamI lam mu h b : ℝ) (hlamI : 0 < lamI) (hlamI_le : lamI ≤ lam)
    (hstable : lam < mu) (hh : 0 < h) (hb : 0 < b) :
    (∀ s : ℕ, (∑' j : ℕ, if s + 1 ≤ j then geomPMF (repairEta lamI lam mu) j else 0) =
        repairEta lamI lam mu ^ (s + 1)) ∧
    ∀ s : ℕ,
      ((∀ t : ℕ, stockCost h b (repairEta lamI lam mu) s ≤
            stockCost h b (repairEta lamI lam mu) t) ∧
        ∀ t : ℕ, stockCost h b (repairEta lamI lam mu) t ≤
            stockCost h b (repairEta lamI lam mu) s → s ≤ t) ↔
      ((∑' j : ℕ, if s + 1 ≤ j then geomPMF (repairEta lamI lam mu) j else 0) ≤ h / (h + b) ∧
        ∀ t : ℕ, t < s →
          h / (h + b) < ∑' j : ℕ, if t + 1 ≤ j then geomPMF (repairEta lamI lam mu) j else 0) := by
  obtain ⟨he0, he1⟩ := P83233cc7.eta_bounds lamI lam mu hlamI hstable
  set η := repairEta lamI lam mu with hη
  have htail : ∀ s : ℕ, (∑' j : ℕ, if s + 1 ≤ j then geomPMF η j else 0) = η ^ (s + 1) :=
    fun s => (P83233cc7.tail_hasSum η he0.le he1 s).tsum_eq
  refine ⟨htail, ?_⟩
  intro s
  have hpos : 0 < h + b := by linarith
  have hmono : Monotone (fun t : ℕ => h - (h + b) * η ^ (t + 1)) := by
    intro a c hac
    have := pow_le_pow_of_le_one he0.le he1.le (show a + 1 ≤ c + 1 by omega)
    have := mul_le_mul_of_nonneg_left this hpos.le
    simp only
    linarith
  rw [P83233cc7.min_iff (stockCost h b η) (fun t : ℕ => h - (h + b) * η ^ (t + 1))
    (P83233cc7.cost_step h b η he0.le he1) hmono s]
  simp only [htail]
  have k1 : ∀ x : ℝ, (0 ≤ h - (h + b) * x ↔ x ≤ h / (h + b)) := by
    intro x
    rw [le_div_iff₀ hpos]
    constructor <;> intro H <;> linarith [mul_comm x (h + b)]
  have k2 : ∀ x : ℝ, (h - (h + b) * x < 0 ↔ h / (h + b) < x) := by
    intro x
    rw [div_lt_iff₀ hpos]
    constructor <;> intro H <;> linarith [mul_comm x (h + b)]
  simp only [k1, k2]

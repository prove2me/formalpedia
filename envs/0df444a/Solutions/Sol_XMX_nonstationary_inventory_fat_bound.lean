-- Prove2me | solution 1 for XMX.nonstationary_inventory_fat_bound
-- status  : ACCEPTED   (prove)
-- author  : @visuddhi
-- created : 2026-10-08T17:06:46.574488+00:00
-- url     : https://prove2.me/submissions/fde30a52-10f3-4e7f-8651-304d40cba8c6

import Definitions.Def_XMX_NonstationaryInventory
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

namespace XMX.FatAudit

theorem separated_card {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (lo hi : ℝ)
    (hne : s.Nonempty) (hb : ∀ i ∈ s, lo ≤ f i ∧ f i ≤ hi)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i + δ ≤ f j ∨ f j + δ ≤ f i) :
    ((s.card : ℝ) - 1) * δ ≤ hi - lo := by
  induction s using Finset.strongInductionOn generalizing lo hi with
  | _ s ih =>
    obtain ⟨a, ha, hmax⟩ := s.exists_max_image f hne
    have hc : ((s.erase a).card : ℝ) + 1 = (s.card : ℝ) := by
      exact_mod_cast Finset.card_erase_add_one ha
    by_cases he : (s.erase a).Nonempty
    · have hb' : ∀ i ∈ s.erase a, lo ≤ f i ∧ f i ≤ hi - δ := by
        intro i hi'
        have his := Finset.mem_of_mem_erase hi'
        have hia := (Finset.mem_erase.mp hi').1
        have hle := hmax i his
        rcases hsep i his a ha hia with h | h
        · exact ⟨(hb i his).1, by linarith [(hb a ha).2]⟩
        · linarith
      have hrec := ih (s.erase a) (Finset.erase_ssubset ha) lo (hi - δ) he hb'
        (fun i hi' j hj' hij => hsep i (Finset.mem_of_mem_erase hi')
          j (Finset.mem_of_mem_erase hj') hij)
      nlinarith
    · have hempty : s.erase a = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      rw [hempty, Finset.card_empty, Nat.cast_zero] at hc
      rw [← hc]
      simp only [zero_add, sub_self, zero_mul]
      linarith [(hb a ha).1, (hb a ha).2]

def demandAt (T L : ℕ) (U : ℝ) (d : Demand T L U) (r : ℕ) : ℝ :=
  if hr : r < T + L then (d ⟨r, hr⟩ : ℝ) else 0

def levelAt (T L : ℕ) (U : ℝ) (S : Levels T L U) (r : ℕ) : ℝ :=
  if hr : r < T + L then (S ⟨r, hr⟩ : ℝ) else 0

def tailDemand (T L : ℕ) (U : ℝ) (d : Demand T L U) (k j : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico j (k + L), demandAt T L U d r

theorem demandAt_nonneg (T L : ℕ) (U : ℝ) (d : Demand T L U) (r : ℕ) :
    0 ≤ demandAt T L U d r := by
  unfold demandAt
  split_ifs with hr
  · exact (d ⟨r, hr⟩).property.1
  · exact le_rfl

theorem tail_nonneg (T L : ℕ) (U : ℝ) (d : Demand T L U) (k j : ℕ) :
    0 ≤ tailDemand T L U d k j :=
  Finset.sum_nonneg (fun r _ => demandAt_nonneg T L U d r)

theorem tail_antitone (T L : ℕ) (U : ℝ) (d : Demand T L U) (k i j : ℕ)
    (hij : i ≤ j) : tailDemand T L U d k j ≤ tailDemand T L U d k i := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    exact Finset.mem_Ico.mpr ⟨hij.trans (Finset.mem_Ico.mp hr).1,
      (Finset.mem_Ico.mp hr).2⟩
  · intro r _ _
    exact demandAt_nonneg T L U d r

theorem level_bounds (T L : ℕ) (U : ℝ) (hU : 0 < U) (S : Levels T L U) (r : ℕ) :
    0 ≤ levelAt T L U S r ∧ levelAt T L U S r ≤ ((L : ℝ) + 1) * U := by
  unfold levelAt
  split_ifs with hr
  · exact (S ⟨r, hr⟩).property
  · constructor <;> positivity

theorem inventory_term_le (T L : ℕ) (U : ℝ) (S : Levels T L U)
    (d : Demand T L U) (k : ℕ) (j : Fin (k + 1)) :
    levelAt T L U S j - tailDemand T L U d k j ≤ inventory T L U S d k := by
  exact Finset.le_sup'
    (fun r : Fin (k + 1) => levelAt T L U S r - tailDemand T L U d k r)
    (Finset.mem_univ j)

theorem inventory_lower (T L : ℕ) (U : ℝ) (hU : 0 < U) (S : Levels T L U)
    (d : Demand T L U) (k : ℕ) :
    -(((L : ℝ) + 1) * U) ≤ inventory T L U S d k := by
  have htail : tailDemand T L U d k k ≤ (L : ℝ) * U := by
    calc
      tailDemand T L U d k k ≤ ∑ _r ∈ Finset.Ico k (k + L), U := by
        apply Finset.sum_le_sum
        intro r _
        unfold demandAt
        split_ifs with hr
        · exact (d ⟨r, hr⟩).property.2
        · exact le_of_lt hU
      _ = (L : ℝ) * U := by simp
  have ht := inventory_term_le T L U S d k ⟨k, Nat.lt_succ_self k⟩
  have hs := (level_bounds T L U hU S k).1
  simp only [Fin.val_mk] at ht
  nlinarith

theorem bound (T L : ℕ) (U γ : ℝ) (hU : 0 < U) (hγ : 0 < γ)
    (k m : ℕ) (x : Fin m → Demand T L U) (τ : Fin m → ℝ)
    (hshatter : Shatters (normalizedInventory T L U k) γ m x τ) :
    (m : ℝ) ≤ 2 / γ + 1 := by
  classical
  let A : ℝ := ((L : ℝ) + 1) * U
  have hA : 0 < A := by dsimp [A]; positivity
  have hγA : 0 < γ * A := mul_pos hγ hA
  obtain ⟨Slo, hlo⟩ := hshatter (fun _ => false)
  have htau : ∀ i, -A ≤ A * τ i := by
    intro i
    have hl : inventory T L U Slo (x i) k / A ≤ τ i - γ := by
      simpa [normalizedInventory, A] using hlo i
    have hmul := (div_le_iff₀ hA).mp hl
    have hi := inventory_lower T L U hU Slo (x i) k
    change -A ≤ inventory T L U Slo (x i) k at hi
    nlinarith
  have hw : ∀ i : Fin m, ∃ S : Levels T L U,
      (τ i + γ) * A < inventory T L U S (x i) k ∧
      ∀ j, j ≠ i → inventory T L U S (x j) k ≤ (τ j - γ) * A := by
    intro i
    obtain ⟨S, hS⟩ := hshatter (fun j => decide (j = i))
    refine ⟨S, ?_, ?_⟩
    · apply (lt_div_iff₀ hA).mp
      simpa [normalizedInventory, A] using hS i
    · intro j hji
      apply (div_le_iff₀ hA).mp
      simpa [normalizedInventory, A, hji] using hS j
  choose S hhigh hlow using hw
  have hmax : ∀ i, ∃ j : Fin (k + 1),
      inventory T L U (S i) (x i) k =
        levelAt T L U (S i) j - tailDemand T L U (x i) k j := by
    intro i
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j : Fin (k + 1) => levelAt T L U (S i) j - tailDemand T L U (x i) k j)
    exact ⟨j, hj⟩
  choose a ha using hmax
  let w : Fin m → ℝ := fun i => tailDemand T L U (x i) k (a i) + A * τ i
  have hwb : ∀ i, -A ≤ w i ∧ w i ≤ A := by
    intro i
    have hn := tail_nonneg T L U (x i) k (a i)
    have hh := hhigh i
    rw [ha i] at hh
    have hs := (level_bounds T L U hU (S i) (a i)).2
    change levelAt T L U (S i) (a i) ≤ A at hs
    dsimp [w]
    constructor <;> nlinarith [htau i]
  have hordered : ∀ i j : Fin m, i ≠ j → (a j : ℕ) ≤ a i →
      w i + 2 * γ * A ≤ w j := by
    intro i j hij haji
    have hh := hhigh i
    rw [ha i] at hh
    have hl := hlow i j (Ne.symm hij)
    have ht := inventory_term_le T L U (S i) (x j) k (a i)
    have hm := tail_antitone T L U (x j) k (a j) (a i) haji
    dsimp [w]
    nlinarith
  by_cases hm : m = 0
  · subst m
    simp only [Nat.cast_zero]
    positivity
  · have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
      exact ⟨⟨0, Nat.pos_of_ne_zero hm⟩, Finset.mem_univ _⟩
    have hpack := separated_card (Finset.univ : Finset (Fin m)) w (2 * γ * A)
      (by positivity) (-A) A hne (fun i _ => hwb i) (by
        intro i _ j _ hij
        rcases le_total (a j : ℕ) (a i : ℕ) with h | h
        · exact Or.inl (hordered i j hij h)
        · exact Or.inr (hordered j i (Ne.symm hij) h))
    simp only [Finset.card_univ, Fintype.card_fin] at hpack
    have hprod : (((m : ℝ) - 1) * (2 * γ)) * A ≤ 2 * A := by nlinarith
    have hcancel : ((m : ℝ) - 1) * (2 * γ) ≤ 2 :=
      (mul_le_mul_iff_left₀ hA).mp hprod
    have hg : (2 / γ) * γ = 2 := div_mul_cancel₀ 2 (ne_of_gt hγ)
    nlinarith

end XMX.FatAudit

open XMX

theorem solution
    (T L : ℕ) (hT : 0 < T) (U γ : ℝ) (hU : 0 < U)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (k : ℕ) (hk : k < T)
    (m : ℕ) (x : Fin m → Demand T L U) (τ : Fin m → ℝ)
    (hshatter : Shatters (normalizedInventory T L U k) γ m x τ) :
    (m : ℝ) ≤ 2 / γ + 1 := by
  exact FatAudit.bound T L U γ hU hγ k m x τ hshatter

#print axioms XMX.FatAudit.separated_card
#print axioms solution

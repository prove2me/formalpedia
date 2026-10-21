-- Prove2me | solution 1 for PrivLearn.Parity.claim_4_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:08:46.4257+00:00
-- url     : https://prove2.me/submissions/92b68137-03ae-4142-afc6-426c44b06b8d

import Mathlib
import Definitions.Def_PrivLearn_Parity_Learner

set_option autoImplicit false
open PrivLearn.Parity

namespace PLP

lemma zmod2_aux1 : ∀ a b c : ZMod 2, a = c → b = c → a + b + c = c := by decide
lemma zmod2_aux2 : ∀ a b c : ZMod 2, a ≠ c → b ≠ c → a + b + c = c := by decide

lemma mem_solSpace {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) (r : Fin d → ZMod 2) :
    r ∈ solSpace z S ↔ ∀ j ∈ S, parity (z j).1 r = (z j).2 := by
  simp [solSpace]

lemma halving_aux {d n : ℕ} (z : Fin n → Example d) (T : Finset (Fin n)) (i : Fin n)
    (h : (solSpace z (insert i T)).Nonempty) :
    (solSpace z T).card ≤ 2 * (solSpace z (insert i T)).card := by
  obtain ⟨r0, hr0⟩ := h
  have hsplit := Finset.card_filter_add_card_filter_not (s := solSpace z T)
    (fun r => parity (z i).1 r = (z i).2)
  have hgood : (solSpace z T).filter (fun r => parity (z i).1 r = (z i).2) = solSpace z (insert i T) := by
    ext r
    simp only [Finset.mem_filter, mem_solSpace, Finset.mem_insert, forall_eq_or_imp]
    tauto
  rw [hgood] at hsplit
  by_cases hex : ∃ r1 ∈ solSpace z T, ¬ parity (z i).1 r1 = (z i).2
  · obtain ⟨r1, hr1, hr1'⟩ := hex
    have hle : ((solSpace z T).filter (fun r => ¬ parity (z i).1 r = (z i).2)).card ≤
        (solSpace z (insert i T)).card := by
      apply Finset.card_le_card_of_injOn (fun r => r + r1 + r0)
      · intro r hr
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hr
        simp only [Finset.mem_coe, mem_solSpace, Finset.mem_insert, forall_eq_or_imp]
        have hrT := (mem_solSpace z T r).mp hr.1
        have hr1T := (mem_solSpace z T r1).mp hr1
        have hr0' := (mem_solSpace z (insert i T) r0).mp hr0
        have key : ∀ j, parity (z j).1 (r + r1 + r0) = parity (z j).1 r + parity (z j).1 r1 +
            parity (z j).1 r0 := by
          intro j; simp [parity, dotProduct_add]
        constructor
        · rw [key, hr0' i (Finset.mem_insert_self _ _)]
          exact zmod2_aux2 _ _ _ hr.2 hr1'
        · intro j hj
          rw [key, hrT j hj, hr1T j hj, hr0' j (Finset.mem_insert_of_mem hj)]
          exact zmod2_aux1 _ _ _ rfl rfl
      · intro a _ b _ hab
        simpa using hab
    omega
  · push Not at hex
    have : ((solSpace z T).filter (fun r => ¬ parity (z i).1 r = (z i).2)) = ∅ := by
      ext r; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      exact fun hr => by simpa using hex r hr
    rw [this] at hsplit
    simp at hsplit
    omega


lemma outProb_nonneg {d n : ℕ} (z : Fin n → Example d) (S : Finset (Fin n)) (r : Fin d → ZMod 2) :
    0 ≤ outProb z S r := by
  unfold outProb
  split_ifs
  · positivity
  · exact le_rfl

lemma outProb_le {d n : ℕ} (z : Fin n → Example d) (T : Finset (Fin n)) (i : Fin n)
    (r : Fin d → ZMod 2) : outProb z (insert i T) r ≤ 2 * outProb z T r := by
  by_cases hr : r ∈ solSpace z (insert i T)
  · have hrT : r ∈ solSpace z T := by
      rw [mem_solSpace] at hr ⊢
      exact fun j hj => hr j (Finset.mem_insert_of_mem hj)
    have hne : (solSpace z (insert i T)).Nonempty := ⟨r, hr⟩
    have hh := halving_aux z T i hne
    have hc1 : (0 : ℝ) < ((solSpace z (insert i T)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hne
    have hc2 : (0 : ℝ) < ((solSpace z T).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨r, hrT⟩
    have hh' : ((solSpace z T).card : ℝ) ≤ 2 * ((solSpace z (insert i T)).card : ℝ) := by
      exact_mod_cast hh
    unfold outProb
    rw [if_pos hr, if_pos hrT, mul_one_div, div_le_div_iff₀ hc1 hc2]
    linarith
  · unfold outProb
    rw [if_neg hr]
    have := outProb_nonneg z T r
    unfold outProb at this
    linarith

lemma claim43_main {d n : ℕ} (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 4) (z : Fin n → Example d)
    (i : Fin n) (r : Fin d → ZMod 2) :
    ∑ T ∈ (Finset.univ.erase i).powerset,
        (ε / 4) ^ T.card * (1 - ε / 4) ^ (n - 1 - T.card) * outProb z (insert i T) r ≤
      2 * ∑ T ∈ (Finset.univ.erase i).powerset,
        (ε / 4) ^ T.card * (1 - ε / 4) ^ (n - 1 - T.card) * outProb z T r := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T _
  have hw : 0 ≤ (ε / 4) ^ T.card * (1 - ε / 4) ^ (n - 1 - T.card) := by
    have h1 : 0 ≤ ε / 4 := by positivity
    have h2 : 0 ≤ 1 - ε / 4 := by linarith
    positivity
  have := outProb_le z T i r
  calc _ ≤ ((ε / 4) ^ T.card * (1 - ε / 4) ^ (n - 1 - T.card)) * (2 * outProb z T r) :=
        mul_le_mul_of_nonneg_left this hw
    _ = _ := by ring


end PLP

theorem solution {d n : ℕ} (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 4) (z : Fin n → Example d)
    (i : Fin n) (r : Fin d → ZMod 2) :
    ∑ T ∈ (Finset.univ.erase i).powerset,
        (ε / 4) ^ T.card * (1 - ε / 4) ^ (n - 1 - T.card) * outProb z (insert i T) r ≤
      2 * ∑ T ∈ (Finset.univ.erase i).powerset,
        (ε / 4) ^ T.card * (1 - ε / 4) ^ (n - 1 - T.card) * outProb z T r :=
  PLP.claim43_main ε hε hε4 z i r

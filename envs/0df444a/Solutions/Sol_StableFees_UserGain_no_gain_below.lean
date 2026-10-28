-- Prove2me | solution 1 for StableFees.UserGain.no_gain_below
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:08:53.989277+00:00
-- url     : https://prove2.me/submissions/3e81dd0c-3c52-45ab-92ed-ee13eb701a43

import Mathlib
import Definitions.Def_StableFees_UserGain_Model

open StableFees.UserGain in
theorem solution (K m : ℕ) (hK : 2 ≤ K) (hm : K ≤ m)
    (Vbar v : ℝ) (hv : v ∈ Set.Icc 0 Vbar)
    (x : Fin m → ℝ) (hx : ∀ j, x j ∈ Set.Icc 0 Vbar)
    (hbelow : v < kthHighest x K) :
    payoff K v v x = 0 ∧
    ∀ b ∈ Set.Icc 0 Vbar, payoff K v b x ≤ 0 := by
  have hsub : {t : ℝ | K ≤ (Finset.univ.filter (fun j => t ≤ x j)).card} ⊆
      {t : ℝ | K - 1 ≤ (Finset.univ.filter (fun j => t ≤ x j)).card} :=
    fun t ht => le_trans (Nat.sub_le K 1) ht
  have hbdd : BddAbove {t : ℝ | K - 1 ≤ (Finset.univ.filter (fun j => t ≤ x j)).card} := by
    refine ⟨Vbar, fun t ht => ?_⟩
    have hpos : 0 < (Finset.univ.filter (fun j => t ≤ x j)).card := by
      have : K - 1 ≤ (Finset.univ.filter (fun j => t ≤ x j)).card := ht
      omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hj
    exact le_trans hj.2 (hx j).2
  have hne : {t : ℝ | K ≤ (Finset.univ.filter (fun j => t ≤ x j)).card}.Nonempty := by
    refine ⟨0, ?_⟩
    show K ≤ (Finset.univ.filter (fun j => (0:ℝ) ≤ x j)).card
    rw [Finset.filter_true_of_mem (fun j _ => (hx j).1), Finset.card_univ, Fintype.card_fin]
    exact hm
  have hmono : kthHighest x K ≤ kthHighest x (K - 1) := csSup_le_csSup hbdd hne hsub
  refine ⟨?_, fun b _ => ?_⟩
  · unfold payoff
    rw [if_neg (by linarith)]
  · unfold payoff
    split_ifs with h
    · have : v ≤ min b (kthHighest x (K - 1)) := le_min (by linarith) (by linarith)
      linarith
    · exact le_rfl

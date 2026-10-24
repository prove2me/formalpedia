-- Prove2me | solution 1 for PandoraBO.Private20261023.pathwise_capped_reward_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:12:19.859659+00:00
-- url     : https://prove2.me/submissions/6aab5715-461d-43ff-8d27-66c51e7f93af

import Definitions.Def_PandoraBO_Model
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
The pointwise upper bound underlying the capped-reward proof of Weitzman's
theorem. This proof establishes its own two simple rollout invariants, so it
does not import any open mission theorem or policy-foundation placeholder.
-/

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

open PandoraBO

namespace PandoraBO.Private20261023.CappedReward

private theorem rollout_zero_slot {n : ℕ} (π : Policy n) (ω : Outcome n)
    (fuel step : ℕ) (h : History n) (hstep : 1 ≤ step) :
    rolloutAux π ω fuel step h 0 = h 0 := by
  induction fuel generalizing step h with
  | zero => rfl
  | succ fuel ih =>
      cases hd : π.next (h, ω.2) with
      | none => simp only [rolloutAux, hd]
      | some i =>
          by_cases hs : step < n + 1
          · simp only [rolloutAux, hd, dif_pos hs]
            rw [ih (step + 1) _ (le_trans hstep (Nat.le_succ step))]
            have hne : (0 : Fin (n + 1)) ≠ ⟨step, hs⟩ := by
              intro heq
              have hz : (0 : ℕ) = step := congrArg Fin.val heq
              exact (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hstep)) hz.symm
            simp only [Function.update_of_ne hne]
          · simp only [rolloutAux, hd, dif_neg hs]

private theorem terminal_zero_occupied {n : ℕ} (π : Policy n) (ω : Outcome n) :
    occupied (terminalHistory π ω) 0 := by
  unfold occupied terminalHistory
  rw [rollout_zero_slot π ω n 1 (initialHistory π ω) le_rfl]
  simp [initialHistory]

private theorem rollout_consistent {n : ℕ} (π : Policy n) (ω : Outcome n)
    (fuel step : ℕ) (h : History n)
    (hh : ∀ k, occupied h k → observedReward h k = ω.1 (observedBox h k)) :
    ∀ k, occupied (rolloutAux π ω fuel step h) k →
      observedReward (rolloutAux π ω fuel step h) k =
        ω.1 (observedBox (rolloutAux π ω fuel step h) k) := by
  induction fuel generalizing step h with
  | zero => exact hh
  | succ fuel ih =>
      cases hd : π.next (h, ω.2) with
      | none => simpa only [rolloutAux, hd] using hh
      | some i =>
          by_cases hs : step < n + 1
          · simp only [rolloutAux, hd, dif_pos hs]
            apply ih
            intro k hk
            by_cases hki : k = (⟨step, hs⟩ : Fin (n + 1))
            · subst k
              simp only [observedReward, observedBox, Function.update_self]
            · have hk' : occupied h k := by
                simpa only [occupied, Function.update_of_ne hki] using hk
              simpa only [observedReward, observedBox, Function.update_of_ne hki] using hh k hk'
          · simpa only [rolloutAux, hd, dif_neg hs] using hh

private theorem terminal_consistent {n : ℕ} (π : Policy n) (ω : Outcome n) :
    ∀ k, occupied (terminalHistory π ω) k →
      observedReward (terminalHistory π ω) k =
        ω.1 (observedBox (terminalHistory π ω) k) := by
  apply rollout_consistent
  intro k hk
  by_cases hk0 : k = 0
  · simp only [observedReward, observedBox, initialHistory, if_pos hk0]
  · simp [occupied, initialHistory, hk0] at hk

private theorem le_fold_max_seed {n : ℕ} (r : Box n → ℝ)
    (ks : List (Box n)) (v : ℝ) :
    v ≤ ks.foldl (fun incumbent i => max incumbent (r i)) v := by
  induction ks generalizing v with
  | nil => exact le_rfl
  | cons i ks ih =>
      exact (le_max_left v (r i)).trans (ih (max v (r i)))

private theorem le_fold_max_member {n : ℕ} (r : Box n → ℝ)
    (ks : List (Box n)) (v : ℝ) (i : Box n) (hi : i ∈ ks) :
    r i ≤ ks.foldl (fun incumbent j => max incumbent (r j)) v := by
  induction ks generalizing v with
  | nil => simp only [List.not_mem_nil] at hi
  | cons j ks ih =>
      rcases List.mem_cons.mp hi with hij | hik
      · subst i
        exact (le_max_right v (r j)).trans (le_fold_max_seed r ks (max v (r j)))
      · exact ih (max v (r j)) hik

private theorem le_full_payoff {n : ℕ} (r : Box n → ℝ) (i : Box n) :
    r i ≤ fullInformationPayoff r :=
  le_fold_max_member r (List.finRange (n + 1)) (r 0) i (List.mem_finRange i)

private theorem cap_plus_excess (y z : ℝ) : y = min y z + max (y - z) 0 := by
  by_cases hyz : y ≤ z
  · rw [min_eq_left hyz, max_eq_right (sub_nonpos.mpr hyz)]
    simp only [add_zero]
  · have hzy : z ≤ y := le_of_not_ge hyz
    rw [min_eq_right hzy, max_eq_left (sub_nonneg.mpr hzy)]
    linarith

private theorem history_reward_upper {n : ℕ} (h : History n) (K : ℝ)
    (hzero : occupied h 0)
    (hbound : ∀ k, occupied h k → observedReward h k ≤ K) :
    historyReward h ≤ K := by
  classical
  have hfold : ∀ (ks : List (Fin (n + 1))) (v : ℝ), v ≤ K →
      ks.foldl (fun incumbent k =>
        if occupied h k then max incumbent (observedReward h k) else incumbent) v ≤ K := by
    intro ks
    induction ks with
    | nil => intro v hv; exact hv
    | cons k ks ih =>
        intro v hv
        apply ih
        by_cases hk : occupied h k
        · simpa only [if_pos hk] using max_le hv (hbound k hk)
        · simpa only [if_neg hk] using hv
  exact hfold (List.finRange (n + 1)) (observedReward h 0) (hbound 0 hzero)

theorem pathwise_cap_upper {n : ℕ} (π : Policy n) (ω : Outcome n) (z : Box n → ℝ) :
    terminalReward π ω ≤
      fullInformationPayoff (fun i => min (ω.1 i) (z i)) +
        ∑ k : Fin (n + 1), if occupied (terminalHistory π ω) k then
          max (observedReward (terminalHistory π ω) k -
            z (observedBox (terminalHistory π ω) k)) 0 else 0 := by
  classical
  let h := terminalHistory π ω
  let K := fullInformationPayoff (fun i => min (ω.1 i) (z i))
  let excess : Fin (n + 1) → ℝ := fun k =>
    if occupied h k then max (observedReward h k - z (observedBox h k)) 0 else 0
  have hexcess : ∀ k, 0 ≤ excess k := by
    intro k
    by_cases hk : occupied h k
    · simp only [excess, if_pos hk]
      exact le_max_right _ _
    · simp only [excess, if_neg hk, le_refl]
  apply history_reward_upper h (K + ∑ k, excess k) (terminal_zero_occupied π ω)
  intro k hk
  have hsample : observedReward h k = ω.1 (observedBox h k) := terminal_consistent π ω k hk
  have hcap : min (observedReward h k) (z (observedBox h k)) ≤ K := by
    rw [hsample]
    exact le_full_payoff (fun i => min (ω.1 i) (z i)) (observedBox h k)
  have hsingle : max (observedReward h k - z (observedBox h k)) 0 ≤ ∑ j, excess j := by
    have h := Finset.single_le_sum (fun j _ => hexcess j) (Finset.mem_univ k)
    simpa only [excess, if_pos hk] using h
  calc
    observedReward h k = min (observedReward h k) (z (observedBox h k)) +
        max (observedReward h k - z (observedBox h k)) 0 := cap_plus_excess _ _
    _ ≤ K + ∑ j, excess j := add_le_add hcap hsingle

end PandoraBO.Private20261023.CappedReward

theorem solution {n : ℕ} (π : Policy n) (ω : Outcome n) (z : Box n → ℝ) :
    terminalReward π ω ≤
      fullInformationPayoff (fun i => min (ω.1 i) (z i)) +
        ∑ k : Fin (n + 1), if occupied (terminalHistory π ω) k then
          max (observedReward (terminalHistory π ω) k -
            z (observedBox (terminalHistory π ω) k)) 0 else 0 := by
  exact PandoraBO.Private20261023.CappedReward.pathwise_cap_upper π ω z

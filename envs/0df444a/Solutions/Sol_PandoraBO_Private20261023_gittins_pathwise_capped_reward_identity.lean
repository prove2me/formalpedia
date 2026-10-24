-- Prove2me | solution 1 for PandoraBO.Private20261023.gittins_pathwise_capped_reward_identity
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:17:08.72564+00:00
-- url     : https://prove2.me/submissions/f4df0649-cdbe-4a63-916f-9fc25fe6a09b

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_reservation_index_exists_unique
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Pointwise capped-payoff equality for the finite Gittins rollout.
The prefix invariants below are duplicated from the verified rollout proof,
inside this file's own namespace so the upload is self contained. -/

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
noncomputable section
open PandoraBO
namespace PandoraBO.Private20261023.CappedGittins

/-- An exact prefix together with distinct boxes and truthful observations. -/
def rolloutInvariant {n : ℕ} (ω : Outcome n) (step : ℕ) (h : History n) : Prop :=
  0 < step ∧ step ≤ n + 1 ∧
  (∀ k, occupied h k ↔ k.val < step) ∧
  (∀ k l, occupied h k → occupied h l →
    observedBox h k = observedBox h l → k = l) ∧
  (∀ k, occupied h k → observedReward h k = ω.1 (observedBox h k))

theorem rolloutInvariant_valid {n : ℕ} {ω : Outcome n} {step : ℕ} {h : History n}
    (hh : rolloutInvariant ω step h) : validHistory h := by
  rcases hh with ⟨hpos, hstep, hpref, hdistinct, hsample⟩
  refine ⟨(hpref 0).2 (by simpa using hpos), ?_, hdistinct⟩
  intro k l hkl hl
  exact (hpref k).2 (lt_of_le_of_lt hkl ((hpref l).1 hl))

theorem initialHistory_invariant {n : ℕ} (π : Policy n) (ω : Outcome n) :
    rolloutInvariant ω 1 (initialHistory π ω) := by
  have hfirst : ∀ k, occupied (initialHistory π ω) k → k = 0 := by
    intro k hk
    by_contra hk0
    simpa [occupied, initialHistory, hk0] using hk
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k = 0
    · subst k
      simp [occupied, initialHistory]
    · have hkval : ¬ k.val < 1 := by
        intro hlt
        apply hk
        apply Fin.ext
        simp only [Fin.val_zero]
        omega
      simp [occupied, initialHistory, hk, hkval]
  · intro k l hk hl heq
    exact (hfirst k hk).trans (hfirst l hl).symm
  · intro k hk
    rw [hfirst k hk]
    simp [observedReward, observedBox, initialHistory]

theorem rolloutInvariant_update {n : ℕ} (ω : Outcome n) (step : ℕ)
    (h : History n) (i : Box n) (hs : step < n + 1)
    (hh : rolloutInvariant ω step h) (hi : ¬ wasOpened h i) :
    rolloutInvariant ω (step + 1)
      (Function.update h (⟨step, hs⟩ : Fin (n + 1)) (true, i, ω.1 i)) := by
  rcases hh with ⟨hpos, hstep, hpref, hdistinct, hsample⟩
  let j : Fin (n + 1) := ⟨step, hs⟩
  change rolloutInvariant ω (step + 1) (Function.update h j (true, i, ω.1 i))
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k = j
    · subst k
      simp [occupied, j]
    · have hkval : k.val ≠ step := by
        intro heq
        apply hk
        exact Fin.ext heq
      have hlt : k.val < step ↔ k.val < step + 1 := by omega
      simpa only [occupied, Function.update_of_ne hk] using (hpref k).trans hlt
  · intro k l hkocc hlocc heq
    by_cases hk : k = j
    · subst k
      by_cases hl : l = j
      · exact hl.symm
      · have hlold : occupied h l := by
          simpa only [occupied, Function.update_of_ne hl] using hlocc
        have hbox : i = observedBox h l := by
          simpa only [observedBox, Function.update_self, Function.update_of_ne hl] using heq
        exact False.elim (hi ⟨l, hlold, hbox.symm⟩)
    · by_cases hl : l = j
      · subst l
        have hkold : occupied h k := by
          simpa only [occupied, Function.update_of_ne hk] using hkocc
        have hbox : observedBox h k = i := by
          simpa only [observedBox, Function.update_self, Function.update_of_ne hk] using heq
        exact False.elim (hi ⟨k, hkold, hbox⟩)
      · apply hdistinct
        · simpa only [occupied, Function.update_of_ne hk] using hkocc
        · simpa only [occupied, Function.update_of_ne hl] using hlocc
        · simpa only [observedBox, Function.update_of_ne hk,
            Function.update_of_ne hl] using heq
  · intro k hkocc
    by_cases hk : k = j
    · subst k
      simp only [observedReward, observedBox, Function.update_self]
    · have hkold : occupied h k := by
        simpa only [occupied, Function.update_of_ne hk] using hkocc
      simpa only [observedReward, observedBox, Function.update_of_ne hk] using hsample k hkold

def excess {n : ℕ} (z : Box n → ℝ) (h : History n) : ℝ :=
  ∑ k : Fin (n + 1), if occupied h k then
    max (observedReward h k - z (observedBox h k)) 0 else 0

def safe {n : ℕ} (z : Box n → ℝ) (h : History n) : Prop :=
  ∀ k, occupied h k → observedReward h k ≤ z (observedBox h k)

def nextRule {n : ℕ} (π : Policy n) (z : Box n → ℝ) : Prop :=
  ∀ h u, validHistory h →
    match π.next (h, u) with
    | none => ∀ i, ¬ wasOpened h i → z i ≤ historyReward h
    | some i => historyReward h ≤ z i ∧
      ∀ j, ¬ wasOpened h j → z j ≤ z i

private theorem history_upper {n : ℕ} (h : History n) (K : ℝ)
    (hzero : occupied h 0)
    (hbound : ∀ k, occupied h k → observedReward h k ≤ K) :
    historyReward h ≤ K := by
  have hf : ∀ (ks : List (Fin (n + 1))) (v : ℝ), v ≤ K →
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
  exact hf (List.finRange (n + 1)) (observedReward h 0) (hbound 0 hzero)

private theorem history_seed_le_fold {n : ℕ} (h : History n)
    (ks : List (Fin (n + 1))) (v : ℝ) :
    v ≤ ks.foldl (fun incumbent k =>
      if occupied h k then max incumbent (observedReward h k) else incumbent) v := by
  induction ks generalizing v with
  | nil => exact le_rfl
  | cons k ks ih =>
      by_cases hk : occupied h k
      · exact (le_max_left v (observedReward h k)).trans
          (by simpa only [List.foldl_cons, if_pos hk] using ih (max v (observedReward h k)))
      · simpa only [List.foldl_cons, if_neg hk] using ih v

private theorem history_member_le_fold {n : ℕ} (h : History n)
    (ks : List (Fin (n + 1))) (k : Fin (n + 1)) (hmem : k ∈ ks)
    (hk : occupied h k) (v : ℝ) :
    observedReward h k ≤ ks.foldl (fun incumbent j =>
      if occupied h j then max incumbent (observedReward h j) else incumbent) v := by
  induction ks generalizing v with
  | nil => cases hmem
  | cons j ks ih =>
      rcases List.mem_cons.mp hmem with hkj | htail
      · subst k
        simpa only [List.foldl_cons, if_pos hk] using
          (le_max_right v (observedReward h j)).trans
            (history_seed_le_fold h ks (max v (observedReward h j)))
      · exact ih htail (if occupied h j then max v (observedReward h j) else v)

theorem history_member {n : ℕ} (h : History n) (k : Fin (n + 1))
    (hk : occupied h k) : observedReward h k ≤ historyReward h :=
  history_member_le_fold h (List.finRange (n + 1)) k (List.mem_finRange k) hk
    (observedReward h 0)

private theorem payoff_upper {n : ℕ} (r : Box n → ℝ) (K : ℝ)
    (hbound : ∀ i, r i ≤ K) : fullInformationPayoff r ≤ K := by
  have hf : ∀ (ks : List (Box n)) (v : ℝ), v ≤ K →
      ks.foldl (fun incumbent i => max incumbent (r i)) v ≤ K := by
    intro ks
    induction ks with
    | nil => intro v hv; exact hv
    | cons i ks ih => intro v hv; exact ih (max v (r i)) (max_le hv (hbound i))
  exact hf (List.finRange (n + 1)) (r 0) (hbound 0)

private theorem payoff_seed {n : ℕ} (r : Box n → ℝ)
    (ks : List (Box n)) (v : ℝ) :
    v ≤ ks.foldl (fun incumbent i => max incumbent (r i)) v := by
  induction ks generalizing v with
  | nil => exact le_rfl
  | cons i ks ih => exact (le_max_left v (r i)).trans (ih (max v (r i)))

private theorem payoff_mem {n : ℕ} (r : Box n → ℝ)
    (ks : List (Box n)) (i : Box n) (hi : i ∈ ks) (v : ℝ) :
    r i ≤ ks.foldl (fun incumbent j => max incumbent (r j)) v := by
  induction ks generalizing v with
  | nil => cases hi
  | cons j ks ih =>
      rcases List.mem_cons.mp hi with hij | hitail
      · subst i
        exact (le_max_right v (r j)).trans (payoff_seed r ks (max v (r j)))
      · exact ih hitail (max v (r j))

private theorem payoff_member {n : ℕ} (r : Box n → ℝ) (i : Box n) :
    r i ≤ fullInformationPayoff r :=
  payoff_mem r (List.finRange (n + 1)) i (List.mem_finRange i) (r 0)

theorem safe_excess_zero {n : ℕ} (z : Box n → ℝ) (h : History n)
    (hsafe : safe z h) : excess z h = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : occupied h k
  · simp only [if_pos hk, max_eq_right (sub_nonpos.mpr (hsafe k hk))]
  · simp only [if_neg hk]

theorem safe_stopped_identity {n : ℕ} (ω : Outcome n) (z : Box n → ℝ)
    (h : History n) (hv : validHistory h)
    (hsample : ∀ k, occupied h k → observedReward h k = ω.1 (observedBox h k))
    (hsafe : safe z h)
    (hclosed : ∀ i, ¬ wasOpened h i → z i ≤ historyReward h) :
    historyReward h = fullInformationPayoff (fun i => min (ω.1 i) (z i)) + excess z h := by
  rw [safe_excess_zero z h hsafe, add_zero]
  apply le_antisymm
  · apply history_upper h _ hv.1
    intro k hk
    have hc := payoff_member (fun i => min (ω.1 i) (z i)) (observedBox h k)
    rw [← hsample k hk, min_eq_left (hsafe k hk)] at hc
    exact hc
  · apply payoff_upper
    intro i
    by_cases hi : wasOpened h i
    · obtain ⟨k, hk, hki⟩ := hi
      have hy : ω.1 i = observedReward h k := by rw [hsample k hk, hki]
      rw [hy]
      exact (min_le_left _ _).trans (history_member h k hk)
    · exact (min_le_right _ _).trans (hclosed i hi)

theorem full_history_opened {n : ℕ} (ω : Outcome n) (h : History n)
    (hh : rolloutInvariant ω (n + 1) h) : ∀ i, wasOpened h i := by
  have hall : ∀ k, occupied h k := fun k => (hh.2.2.1 k).2 k.isLt
  have hinj : Function.Injective (observedBox h) := by
    intro k l hkl
    exact hh.2.2.2.1 k l (hall k) (hall l) hkl
  intro i
  obtain ⟨k, hk⟩ := Finite.surjective_of_injective hinj i
  exact ⟨k, hall k, hk⟩

theorem rollout_stopped {n : ℕ} (π : Policy n) (ω : Outcome n)
    (fuel step : ℕ) (h : History n) (hstop : π.next (h, ω.2) = none) :
    rolloutAux π ω fuel step h = h := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [rolloutAux, hstop]

/-- Once a positive excess is observed, its index bounds every remaining
index and every earlier reward. Hence it is the last opening. -/
theorem positive_excess_terminal {n : ℕ} (π : Policy n) (ω : Outcome n)
    (z : Box n → ℝ) (hrule : nextRule π z) (h : History n) (hv : validHistory h)
    (hsample : ∀ l, occupied h l → observedReward h l = ω.1 (observedBox h l))
    (k : Fin (n + 1)) (hk : occupied h k)
    (hpositive : z (observedBox h k) < observedReward h k)
    (hother : ∀ l, occupied h l → l ≠ k →
      observedReward h l ≤ z (observedBox h l) ∧
      observedReward h l ≤ z (observedBox h k))
    (hclosed : ∀ i, ¬ wasOpened h i → z i ≤ z (observedBox h k)) :
    π.next (h, ω.2) = none ∧
    historyReward h = fullInformationPayoff (fun i => min (ω.1 i) (z i)) + excess z h := by
  have hR : historyReward h = observedReward h k := by
    apply le_antisymm
    · apply history_upper h _ hv.1
      intro l hl
      by_cases hlk : l = k
      · subst l; exact le_rfl
      · exact (hother l hl hlk).2.trans hpositive.le
    · exact history_member h k hk
  have hK : fullInformationPayoff (fun i => min (ω.1 i) (z i)) =
      z (observedBox h k) := by
    apply le_antisymm
    · apply payoff_upper
      intro i
      by_cases hi : wasOpened h i
      · obtain ⟨l, hl, hli⟩ := hi
        have hy : ω.1 i = observedReward h l := by rw [hsample l hl, hli]
        by_cases hlk : l = k
        · subst l
          rw [← hli]
          exact min_le_right _ _
        · rw [hy]
          exact (min_le_left _ _).trans (hother l hl hlk).2
      · exact (min_le_right _ _).trans (hclosed i hi)
    · have hc := payoff_member (fun i => min (ω.1 i) (z i)) (observedBox h k)
      rw [← hsample k hk, min_eq_right hpositive.le] at hc
      exact hc
  have hE : excess z h = observedReward h k - z (observedBox h k) := by
    unfold excess
    rw [Finset.sum_eq_single k]
    · simp only [if_pos hk, max_eq_left (sub_nonneg.mpr hpositive.le)]
    · intro l _ hlk
      by_cases hl : occupied h l
      · simp only [if_pos hl, max_eq_right (sub_nonpos.mpr (hother l hl hlk).1)]
      · simp only [if_neg hl]
    · intro hn
      exact False.elim (hn (Finset.mem_univ k))
  constructor
  · cases hd : π.next (h, ω.2) with
    | none => rfl
    | some i =>
        have hchoice : historyReward h ≤ z i := by
          have hx := hrule h ω.2 hv
          rw [hd] at hx
          exact hx.1
        have hi := π.next_unopened h ω.2 i hd
        have hzi := hclosed i hi
        rw [hR] at hchoice
        linarith
  · rw [hR, hK, hE]
    ring

theorem opened_update_mono {n : ℕ} (h : History n) (j : Fin (n + 1))
    (i : Box n) (y : ℝ) (hj : ¬ occupied h j) :
    ∀ b, wasOpened h b → wasOpened (Function.update h j (true, i, y)) b := by
  intro b hb
  obtain ⟨k, hk, hkb⟩ := hb
  have hkj : k ≠ j := by intro heq; subst k; exact hj hk
  refine ⟨k, ?_, ?_⟩
  · simpa only [occupied, Function.update_of_ne hkj] using hk
  · simpa only [observedBox, Function.update_of_ne hkj] using hkb

/-- Until the first strictly positive excess, all observed rewards are
uncapped. Either the policy stops, all boxes are open, or one more safe
opening preserves this invariant. -/
theorem safe_rollout_identity {n : ℕ} (π : Policy n) (ω : Outcome n)
    (z : Box n → ℝ) (hrule : nextRule π z) (fuel step : ℕ) (h : History n)
    (hbudget : fuel + step = n + 1) (hh : rolloutInvariant ω step h)
    (hsafe : safe z h) :
    historyReward (rolloutAux π ω fuel step h) =
      fullInformationPayoff (fun i => min (ω.1 i) (z i)) +
        excess z (rolloutAux π ω fuel step h) := by
  induction fuel generalizing step h with
  | zero =>
      have hstep : step = n + 1 := by omega
      subst step
      apply safe_stopped_identity ω z h (rolloutInvariant_valid hh) hh.2.2.2.2 hsafe
      intro i hi
      exact False.elim (hi (full_history_opened ω h hh i))
  | succ fuel ih =>
      have hv : validHistory h := rolloutInvariant_valid hh
      cases hd : π.next (h, ω.2) with
      | none =>
          simp only [rolloutAux, hd]
          apply safe_stopped_identity ω z h hv hh.2.2.2.2 hsafe
          have hx := hrule h ω.2 hv
          simpa only [hd] using hx
      | some i =>
          have hchoice : historyReward h ≤ z i ∧
              ∀ b, ¬ wasOpened h b → z b ≤ z i := by
            have hx := hrule h ω.2 hv
            simpa only [hd] using hx
          have hunopened : ¬ wasOpened h i := π.next_unopened h ω.2 i hd
          have hstep : step < n + 1 := by omega
          let j : Fin (n + 1) := ⟨step, hstep⟩
          let hnew : History n := Function.update h j (true, i, ω.1 i)
          have hjold : ¬ occupied h j := by
            intro hj
            have ht : step < step := (hh.2.2.1 j).1 hj
            exact (lt_irrefl step) ht
          have hhnew : rolloutInvariant ω (step + 1) hnew :=
            rolloutInvariant_update ω step h i hstep hh hunopened
          have hjnew : occupied hnew j := by simp [hnew, occupied]
          have hjbox : observedBox hnew j = i := by simp [hnew, observedBox]
          have hjreward : observedReward hnew j = ω.1 i := by simp [hnew, observedReward]
          have hrest : fuel + (step + 1) = n + 1 := by omega
          simp only [rolloutAux, hd, dif_pos hstep]
          change historyReward (rolloutAux π ω fuel (step + 1) hnew) =
            fullInformationPayoff (fun b => min (ω.1 b) (z b)) +
              excess z (rolloutAux π ω fuel (step + 1) hnew)
          by_cases hy : ω.1 i ≤ z i
          · apply ih (step + 1) hnew hrest hhnew
            intro k hk
            by_cases hkj : k = j
            · subst k
              simpa only [hjbox, hjreward] using hy
            · have hkold : occupied h k := by
                simpa only [occupied, hnew, Function.update_of_ne hkj] using hk
              simpa only [observedReward, observedBox, hnew,
                Function.update_of_ne hkj] using hsafe k hkold
          · have hpositive : z (observedBox hnew j) < observedReward hnew j := by
              rw [hjbox, hjreward]
              exact lt_of_not_ge hy
            have hother : ∀ k, occupied hnew k → k ≠ j →
                observedReward hnew k ≤ z (observedBox hnew k) ∧
                observedReward hnew k ≤ z (observedBox hnew j) := by
              intro k hk hkj
              have hkold : occupied h k := by
                simpa only [occupied, hnew, Function.update_of_ne hkj] using hk
              constructor
              · simpa only [observedReward, observedBox, hnew,
                  Function.update_of_ne hkj] using hsafe k hkold
              · have hr : observedReward h k ≤ z i :=
                  (history_member h k hkold).trans hchoice.1
                simpa only [hjbox, observedReward, hnew,
                  Function.update_of_ne hkj] using hr
            have hclosed : ∀ b, ¬ wasOpened hnew b → z b ≤ z (observedBox hnew j) := by
              intro b hb
              rw [hjbox]
              apply hchoice.2 b
              intro hbold
              exact hb (opened_update_mono h j i (ω.1 i) hjold b hbold)
            obtain ⟨hstop, heq⟩ := positive_excess_terminal π ω z hrule hnew
              (rolloutInvariant_valid hhnew) hhnew.2.2.2.2 j hjnew
              hpositive hother hclosed
            rw [rollout_stopped π ω fuel (step + 1) hnew hstop]
            exact heq

theorem pathwise_identity_of_rules {n : ℕ} (π : Policy n) (ω : Outcome n)
    (z : Box n → ℝ) (hfirst : ∀ u i, z i ≤ z (π.first u))
    (hrule : nextRule π z) :
    terminalReward π ω = fullInformationPayoff (fun i => min (ω.1 i) (z i)) +
      excess z (terminalHistory π ω) := by
  let h : History n := initialHistory π ω
  have hh : rolloutInvariant ω 1 h := initialHistory_invariant π ω
  have hoccupied : ∀ k, occupied h k → k = 0 := by
    intro k hk
    have hlt : k.val < 1 := (hh.2.2.1 k).1 hk
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  have hbox : observedBox h 0 = π.first ω.2 := by simp [h, observedBox, initialHistory]
  have hreward : observedReward h 0 = ω.1 (π.first ω.2) := by
    simp [h, observedReward, initialHistory]
  change historyReward (rolloutAux π ω n 1 h) =
    fullInformationPayoff (fun i => min (ω.1 i) (z i)) +
      excess z (rolloutAux π ω n 1 h)
  by_cases hy : ω.1 (π.first ω.2) ≤ z (π.first ω.2)
  · apply safe_rollout_identity π ω z hrule n 1 h rfl hh
    intro k hk
    rw [hoccupied k hk, hbox, hreward]
    exact hy
  · have hpositive : z (observedBox h 0) < observedReward h 0 := by
      rw [hbox, hreward]
      exact lt_of_not_ge hy
    have hother : ∀ k, occupied h k → k ≠ 0 →
        observedReward h k ≤ z (observedBox h k) ∧
        observedReward h k ≤ z (observedBox h 0) := by
      intro k hk hk0
      exact False.elim (hk0 (hoccupied k hk))
    have hclosed : ∀ i, ¬ wasOpened h i → z i ≤ z (observedBox h 0) := by
      intro i _
      rw [hbox]
      exact hfirst ω.2 i
    obtain ⟨hstop, heq⟩ := positive_excess_terminal π ω z hrule h
      (rolloutInvariant_valid hh) hh.2.2.2.2 0 (rolloutInvariant_valid hh).1
      hpositive hother hclosed
    rw [rollout_stopped π ω n 1 h hstop]
    exact heq

end PandoraBO.Private20261023.CappedGittins

theorem solution {n : ℕ} (M : Instance n) (multiplier : ℝ) (hpos : 0 < multiplier)
    (z : Box n → ℝ) (hz : reservationIndices M multiplier z) (π : Policy n)
    (hπ : isGittinsPolicy M multiplier π) (ω : Outcome n) :
    terminalReward π ω =
      fullInformationPayoff (fun i => min (ω.1 i) (z i)) +
        ∑ k : Fin (n + 1), if occupied (terminalHistory π ω) k then
          max (observedReward (terminalHistory π ω) k -
            z (observedBox (terminalHistory π ω) k)) 0 else 0 := by
  obtain ⟨w, hw, hfirst, hnext⟩ := hπ
  have heq : w = z := by
    funext i
    obtain ⟨root, _hroot, huniq⟩ :=
      PandoraBO.Private20261023.reservation_index_exists_unique M multiplier hpos i
    exact (huniq (w i) (hw i)).trans (huniq (z i) (hz i)).symm
  subst w
  exact PandoraBO.Private20261023.CappedGittins.pathwise_identity_of_rules π ω z hfirst hnext

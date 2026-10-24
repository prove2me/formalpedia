-- Prove2me | solution 1 for PandoraBO.Private20261023.policy_opening_regular
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:23:55.965029+00:00
-- url     : https://prove2.me/submissions/919ba8ac-442b-4864-a1ab-3eb97956a638

import Definitions.Def_PandoraBO_Model
import Lean.Elab.Tactic.Omega

/-!
# Opening decisions are nonanticipative

Changing only a box's reward cannot change whether that box is opened. The
argument uses preservation of every history slot strictly before the current
step; it does not assume that a policy stops when a given reward is observed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace PandoraBO.Private20261023.Opening

theorem rollout_preserves_before {n : ℕ} (π : Policy n) (ω : Outcome n)
    (fuel step : ℕ) (h : History n) (k : Fin (n + 1)) (hk : k.val < step) :
    rolloutAux π ω fuel step h k = h k := by
  induction fuel generalizing step h with
  | zero => rfl
  | succ fuel ih =>
      cases hd : π.next (h, ω.2) with
      | none => simp only [rolloutAux, hd]
      | some j =>
          by_cases hs : step < n + 1
          · simp only [rolloutAux, hd, dif_pos hs]
            rw [ih (step + 1) _ (by omega)]
            have hne : k ≠ (⟨step, hs⟩ : Fin (n + 1)) := by
              intro heq
              have hv := congrArg Fin.val heq
              simp only [Fin.val_mk] at hv
              omega
            exact Function.update_of_ne hne _ _
          · simp only [rolloutAux, hd, dif_neg hs]

theorem opened_before_preserved {n : ℕ} (π : Policy n) (ω : Outcome n)
    (fuel step : ℕ) (h : History n) (i : Box n)
    (hbefore : ∀ k, occupied h k → k.val < step) (hi : wasOpened h i) :
    wasOpened (rolloutAux π ω fuel step h) i := by
  obtain ⟨k, hk, hki⟩ := hi
  have heq := rollout_preserves_before π ω fuel step h k (hbefore k hk)
  exact ⟨k, by simpa only [occupied, heq] using hk,
    by simpa only [observedBox, heq] using hki⟩

theorem update_occupied_before {n : ℕ} (step : ℕ) (hs : step < n + 1)
    (h : History n) (i : Box n) (y : ℝ)
    (hb : ∀ k, occupied h k → k.val < step) :
    ∀ k, occupied (Function.update h (⟨step, hs⟩ : Fin (n + 1)) (true, i, y)) k →
      k.val < step + 1 := by
  intro k hk
  by_cases heq : k = (⟨step, hs⟩ : Fin (n + 1))
  · subst k
    exact Nat.lt_succ_self step
  · have hkold : occupied h k := by
      simpa only [occupied, Function.update_of_ne heq] using hk
    exact lt_trans (hb k hkold) (Nat.lt_succ_self step)

theorem updated_box_opened {n : ℕ} (π : Policy n) (ω : Outcome n)
    (fuel step : ℕ) (h : History n) (i : Box n) (hs : step < n + 1) (y : ℝ) :
    wasOpened (rolloutAux π ω fuel (step + 1)
      (Function.update h (⟨step, hs⟩ : Fin (n + 1)) (true, i, y))) i := by
  let k : Fin (n + 1) := ⟨step, hs⟩
  have heq := rollout_preserves_before π ω fuel (step + 1)
    (Function.update h k (true, i, y)) k (Nat.lt_succ_self step)
  change wasOpened (rolloutAux π ω fuel (step + 1) (Function.update h k (true, i, y))) i
  refine ⟨k, ?_, ?_⟩
  · simp only [occupied, heq, Function.update_self]
  · simp only [observedBox, heq, Function.update_self]

theorem rollout_opening_independent {n : ℕ} (π : Policy n) (i : Box n)
    (r r' : Box n → ℝ) (u : ℝ) (hr : ∀ j, j ≠ i → r j = r' j)
    (fuel step : ℕ) (h : History n)
    (hb : ∀ k, occupied h k → k.val < step) :
    wasOpened (rolloutAux π (r, u) fuel step h) i ↔
      wasOpened (rolloutAux π (r', u) fuel step h) i := by
  induction fuel generalizing step h with
  | zero => rfl
  | succ fuel ih =>
      by_cases hi : wasOpened h i
      · exact iff_of_true (opened_before_preserved π (r, u) (fuel + 1) step h i hb hi)
          (opened_before_preserved π (r', u) (fuel + 1) step h i hb hi)
      · cases hd : π.next (h, u) with
        | none => simp only [rolloutAux, hd]
        | some j =>
            by_cases hs : step < n + 1
            · by_cases hji : j = i
              · subst j
                simpa only [rolloutAux, hd, dif_pos hs] using
                  iff_of_true (updated_box_opened π (r, u) fuel step h i hs (r i))
                    (updated_box_opened π (r', u) fuel step h i hs (r' i))
              · have hnew := update_occupied_before step hs h j (r j) hb
                simpa only [rolloutAux, hd, dif_pos hs, hr j hji] using
                  ih (step + 1) (Function.update h ⟨step, hs⟩ (true, j, r j)) hnew
            · simp only [rolloutAux, hd, dif_neg hs]

theorem initial_occupied_before {n : ℕ} (π : Policy n) (ω : Outcome n) :
    ∀ k, occupied (initialHistory π ω) k → k.val < 1 := by
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp only [Fin.val_zero, Nat.zero_lt_succ]
  · simp [occupied, initialHistory, hk0] at hk

theorem terminal_opening_independent {n : ℕ} (π : Policy n) (i : Box n)
    (r r' : Box n → ℝ) (u : ℝ) (hr : ∀ j, j ≠ i → r j = r' j) :
    wasOpened (terminalHistory π (r, u)) i ↔
      wasOpened (terminalHistory π (r', u)) i := by
  by_cases hfirst : π.first u = i
  · have hopened : ∀ s : Box n → ℝ, wasOpened (initialHistory π (s, u)) i := by
      intro s
      refine ⟨0, ?_, ?_⟩
      · simp [occupied, initialHistory]
      · simpa [observedBox, initialHistory] using hfirst
    exact iff_of_true
      (opened_before_preserved π (r, u) n 1 _ i (initial_occupied_before π _) (hopened r))
      (opened_before_preserved π (r', u) n 1 _ i (initial_occupied_before π _) (hopened r'))
  · have heq : initialHistory π (r, u) = initialHistory π (r', u) := by
      funext k
      by_cases hk : k = 0
      · simp only [initialHistory, if_pos hk, hr (π.first u) hfirst]
      · simp only [initialHistory, if_neg hk]
    unfold terminalHistory
    rw [← heq]
    exact rollout_opening_independent π i r r' u hr n 1 _ (initial_occupied_before π _)

attribute [local instance] Classical.propDecidable

private theorem measurable_selection {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι]
    (f : ι → α → β) (hf : ∀ i, Measurable (f i))
    (g : α → ι) (hg : Measurable g) :
    Measurable (fun x => f (g x) x) := by
  have h : Measurable (fun p : α × ι => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  exact h.comp (measurable_id.prodMk hg)

theorem initialHistory_measurable {n : ℕ} (π : Policy n) :
    Measurable (initialHistory π) := by
  have hfirst : Measurable (fun ω : Outcome n => π.first ω.2) :=
    π.first_measurable.comp measurable_snd
  have hreward : Measurable (fun ω : Outcome n => ω.1 (π.first ω.2)) :=
    measurable_selection (fun i : Box n => fun ω : Outcome n => ω.1 i)
      (fun i => (measurable_pi_apply i).comp measurable_fst)
      (fun ω : Outcome n => π.first ω.2) hfirst
  apply measurable_pi_lambda
  intro k
  by_cases hk : k = 0
  · simpa only [initialHistory, if_pos hk] using
      ((measurable_const : Measurable (fun _ : Outcome n => true)).prodMk
        (hfirst.prodMk hreward))
  · simpa only [initialHistory, if_neg hk] using
      (measurable_const : Measurable (fun _ : Outcome n =>
        (false, (0 : Box n), (0 : ℝ))))

theorem rolloutAux_measurable {n : ℕ} (π : Policy n) (fuel step : ℕ)
    (h : Outcome n → History n) (hh : Measurable h) :
    Measurable (fun ω => rolloutAux π ω fuel step (h ω)) := by
  classical
  induction fuel generalizing step h with
  | zero => exact hh
  | succ fuel ih =>
      let branch : Decision n → Outcome n → History n := fun d ω =>
        match d with
        | none => h ω
        | some i =>
            if hs : step < n + 1 then
              rolloutAux π ω fuel (step + 1)
                (Function.update (h ω) ⟨step, hs⟩ (true, i, ω.1 i))
            else h ω
      have hbranch : ∀ d, Measurable (branch d) := by
        intro d
        cases d with
        | none => exact hh
        | some i =>
            by_cases hs : step < n + 1
            · have hnew : Measurable (fun ω : Outcome n =>
                  Function.update (h ω) (⟨step, hs⟩ : Fin (n + 1))
                    (true, i, ω.1 i)) :=
                (measurable_update' (a := (⟨step, hs⟩ : Fin (n + 1)))).comp
                  (hh.prodMk (measurable_const.prodMk
                    (measurable_const.prodMk ((measurable_pi_apply i).comp measurable_fst))))
              simpa only [branch, dif_pos hs] using ih (step + 1) _ hnew
            · simpa only [branch, dif_neg hs] using hh
      have hd : Measurable (fun ω : Outcome n => π.next (h ω, ω.2)) :=
        π.next_measurable.comp (hh.prodMk measurable_snd)
      have hm := measurable_selection branch hbranch (fun ω => π.next (h ω, ω.2)) hd
      have heq : (fun ω => branch (π.next (h ω, ω.2)) ω) =
          (fun ω => rolloutAux π ω (fuel + 1) step (h ω)) := by
        funext ω
        cases hd' : π.next (h ω, ω.2) with
        | none => simp only [branch, rolloutAux, hd']
        | some i =>
            by_cases hs : step < n + 1
            · simp only [branch, rolloutAux, hd', dif_pos hs]
            · simp only [branch, rolloutAux, hd', dif_neg hs]
      exact heq ▸ hm

theorem terminalHistory_measurable {n : ℕ} (π : Policy n) :
    Measurable (terminalHistory π) :=
  rolloutAux_measurable π n 1 (initialHistory π) (initialHistory_measurable π)

theorem opening_measurableSet {n : ℕ} (π : Policy n) (i : Box n) :
    MeasurableSet {ω : Outcome n | wasOpened (terminalHistory π ω) i} := by
  have ht := terminalHistory_measurable π
  have hk : ∀ k : Fin (n + 1), MeasurableSet {ω : Outcome n |
      occupied (terminalHistory π ω) k ∧ observedBox (terminalHistory π ω) k = i} := by
    intro k
    have hmocc : Measurable (fun h : History n => (h k).1) :=
      (measurable_pi_apply k).fst
    have hmbox : Measurable (fun h : History n => (h k).2.1) :=
      (measurable_pi_apply k).snd.fst
    have ho : MeasurableSet {ω : Outcome n | occupied (terminalHistory π ω) k} := by
      change MeasurableSet ((fun ω : Outcome n => (terminalHistory π ω k).1) ⁻¹' {true})
      exact (measurableSet_singleton true).preimage (hmocc.comp ht)
    have hb : MeasurableSet {ω : Outcome n | observedBox (terminalHistory π ω) k = i} := by
      change MeasurableSet ((fun ω : Outcome n => (terminalHistory π ω k).2.1) ⁻¹' {i})
      exact (measurableSet_singleton i).preimage (hmbox.comp ht)
    exact ho.inter hb
  simpa only [wasOpened, Set.ofPred_exists] using MeasurableSet.iUnion hk

end PandoraBO.Private20261023.Opening

theorem solution {n : ℕ} (π : PandoraBO.Policy n) (i : PandoraBO.Box n) :
    MeasurableSet {ω : PandoraBO.Outcome n |
      PandoraBO.wasOpened (PandoraBO.terminalHistory π ω) i} ∧
    (∀ (r r' : PandoraBO.Box n → ℝ) (u : ℝ),
      (∀ j, j ≠ i → r j = r' j) →
      (PandoraBO.wasOpened (PandoraBO.terminalHistory π (r, u)) i ↔
        PandoraBO.wasOpened (PandoraBO.terminalHistory π (r', u)) i)) := by
  exact ⟨PandoraBO.Private20261023.Opening.opening_measurableSet π i,
    PandoraBO.Private20261023.Opening.terminal_opening_independent π i⟩

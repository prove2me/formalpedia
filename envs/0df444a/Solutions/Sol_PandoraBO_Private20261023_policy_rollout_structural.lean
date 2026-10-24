-- Prove2me | solution 1 for PandoraBO.Private20261023.policy_rollout_structural
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:07:42.003987+00:00
-- url     : https://prove2.me/submissions/2ecf5982-7b02-4d7d-8614-92113b89ac86

import Definitions.Def_PandoraBO_Model
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.FinRange
import Lean.Elab.Tactic.Omega

/-!
# Structural invariants of finite policy rollouts

Every occupied slot records the original sampled reward of its box. The
occupied slots form a nonempty prefix, and no box occurs twice. These facts
also give the full-information reward bound and the sharp total-cost bound.
-/

set_option autoImplicit false

noncomputable section

namespace PandoraBO.Private20261023

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

theorem rolloutAux_invariant {n : ℕ} (π : Policy n) (ω : Outcome n)
    (fuel step : ℕ) (h : History n) (hh : rolloutInvariant ω step h) :
    ∃ t, rolloutInvariant ω t (rolloutAux π ω fuel step h) := by
  induction fuel generalizing step h with
  | zero => exact ⟨step, hh⟩
  | succ fuel ih =>
      cases hd : π.next (h, ω.2) with
      | none => simpa only [rolloutAux, hd] using Exists.intro step hh
      | some i =>
          by_cases hs : step < n + 1
          · have hnew := rolloutInvariant_update ω step h i hs hh
              (π.next_unopened h ω.2 i hd)
            simpa only [rolloutAux, hd, dif_pos hs] using
              ih (step + 1) (Function.update h ⟨step, hs⟩ (true, i, ω.1 i)) hnew
          · simpa only [rolloutAux, hd, dif_neg hs] using Exists.intro step hh

theorem terminalHistory_invariant {n : ℕ} (π : Policy n) (ω : Outcome n) :
    ∃ t, rolloutInvariant ω t (terminalHistory π ω) :=
  rolloutAux_invariant π ω n 1 (initialHistory π ω) (initialHistory_invariant π ω)

theorem terminalHistory_valid {n : ℕ} (π : Policy n) (ω : Outcome n) :
    validHistory (terminalHistory π ω) := by
  obtain ⟨t, ht⟩ := terminalHistory_invariant π ω
  exact rolloutInvariant_valid ht

theorem terminalHistory_sample {n : ℕ} (π : Policy n) (ω : Outcome n)
    (k : Fin (n + 1)) (hk : occupied (terminalHistory π ω) k) :
    observedReward (terminalHistory π ω) k =
      ω.1 (observedBox (terminalHistory π ω) k) := by
  obtain ⟨t, ht⟩ := terminalHistory_invariant π ω
  exact ht.2.2.2.2 k hk

private theorem maxFold_ge_initial {n : ℕ} (r : Box n → ℝ)
    (ks : List (Box n)) (v : ℝ) :
    v ≤ ks.foldl (fun incumbent i => max incumbent (r i)) v := by
  induction ks generalizing v with
  | nil => exact le_rfl
  | cons k ks ih =>
      exact (le_max_left v (r k)).trans (ih (max v (r k)))

private theorem maxFold_ge_member {n : ℕ} (r : Box n → ℝ)
    (ks : List (Box n)) (i : Box n) (hi : i ∈ ks) (v : ℝ) :
    r i ≤ ks.foldl (fun incumbent j => max incumbent (r j)) v := by
  induction ks generalizing v with
  | nil => cases hi
  | cons k ks ih =>
      rcases List.mem_cons.mp hi with hki | htail
      · subst i
        exact (le_max_right v (r k)).trans (maxFold_ge_initial r ks (max v (r k)))
      · exact ih htail (max v (r k))

theorem reward_le_fullInformationPayoff {n : ℕ} (r : Box n → ℝ) (i : Box n) :
    r i ≤ fullInformationPayoff r :=
  maxFold_ge_member r (List.finRange (n + 1)) i (List.mem_finRange i) (r 0)

attribute [local instance] Classical.propDecidable

private theorem historyFold_le {n : ℕ} (h : History n) (S : ℝ)
    (hh : ∀ k, occupied h k → observedReward h k ≤ S)
    (ks : List (Fin (n + 1))) (v : ℝ) (hv : v ≤ S) :
    ks.foldl (fun incumbent k =>
      if occupied h k then max incumbent (observedReward h k) else incumbent) v ≤ S := by
  induction ks generalizing v with
  | nil => exact hv
  | cons k ks ih =>
      apply ih
      dsimp only
      split_ifs with hk
      · exact max_le hv (hh k hk)
      · exact hv

theorem terminalReward_le_fullInformationPayoff {n : ℕ} (π : Policy n) (ω : Outcome n) :
    terminalReward π ω ≤ fullInformationPayoff ω.1 := by
  have hobs : ∀ k, occupied (terminalHistory π ω) k →
      observedReward (terminalHistory π ω) k ≤ fullInformationPayoff ω.1 := by
    intro k hk
    rw [terminalHistory_sample π ω k hk]
    exact reward_le_fullInformationPayoff ω.1 _
  exact historyFold_le (terminalHistory π ω) (fullInformationPayoff ω.1) hobs
    (List.finRange (n + 1)) (observedReward (terminalHistory π ω) 0)
    (hobs 0 (terminalHistory_valid π ω).1)

theorem historyCost_le_total_of_valid {n : ℕ} (M : Instance n) (h : History n)
    (hh : validHistory h) : historyCost M h ≤ ∑ i : Box n, M.cost i := by
  let active : Finset (Fin (n + 1)) := Finset.univ.filter (occupied h)
  have hinj : Set.InjOn (observedBox h) active := by
    intro k hk l hl heq
    exact hh.2.2 k l (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2 heq
  calc
    historyCost M h = ∑ k ∈ active, M.cost (observedBox h k) := by
      simp only [historyCost, active, Finset.sum_filter]
    _ = ∑ i ∈ active.image (observedBox h), M.cost i :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ i : Box n, M.cost i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i hi hnot
      exact (M.cost_positive i).le

theorem terminalCost_le_total {n : ℕ} (M : Instance n) (π : Policy n) (ω : Outcome n) :
    terminalCost M π ω ≤ ∑ i : Box n, M.cost i :=
  historyCost_le_total_of_valid M (terminalHistory π ω) (terminalHistory_valid π ω)

theorem policy_rollout_structural_core {n : ℕ} (M : Instance n) (π : Policy n)
    (ω : Outcome n) :
    validHistory (terminalHistory π ω) ∧
    (∀ k, occupied (terminalHistory π ω) k →
      observedReward (terminalHistory π ω) k = ω.1 (observedBox (terminalHistory π ω) k)) ∧
    terminalReward π ω ≤ fullInformationPayoff ω.1 ∧
    terminalCost M π ω ≤ ∑ i : Box n, M.cost i := by
  exact ⟨terminalHistory_valid π ω, terminalHistory_sample π ω,
    terminalReward_le_fullInformationPayoff π ω, terminalCost_le_total M π ω⟩

end PandoraBO.Private20261023

theorem solution {n : ℕ} (M : PandoraBO.Instance n) (π : PandoraBO.Policy n)
    (ω : PandoraBO.Outcome n) :
    PandoraBO.validHistory (PandoraBO.terminalHistory π ω) ∧
    (∀ k, PandoraBO.occupied (PandoraBO.terminalHistory π ω) k →
      PandoraBO.observedReward (PandoraBO.terminalHistory π ω) k =
        ω.1 (PandoraBO.observedBox (PandoraBO.terminalHistory π ω) k)) ∧
    PandoraBO.terminalReward π ω ≤ PandoraBO.fullInformationPayoff ω.1 ∧
    PandoraBO.terminalCost M π ω ≤ ∑ i : PandoraBO.Box n, M.cost i := by
  exact PandoraBO.Private20261023.policy_rollout_structural_core M π ω

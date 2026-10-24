-- Prove2me | solution 1 for PandoraBO.Private20261023.zero_gittins_full_information
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T01:23:28.333882+00:00
-- url     : https://prove2.me/submissions/ca3d9147-5b49-451c-aa34-710505d50339

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_policy_terminal_measurable_integrable
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Data.Fintype.Card
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
open MeasureTheory

namespace PandoraBO.Private20261023.ZeroFullInformation

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

theorem full_history_opened {n : ℕ} (ω : Outcome n) (h : History n)
    (hh : rolloutInvariant ω (n + 1) h) : ∀ i, wasOpened h i := by
  have hall : ∀ k, occupied h k := fun k => (hh.2.2.1 k).2 k.isLt
  have hinj : Function.Injective (observedBox h) := by
    intro k l hkl
    exact hh.2.2.2.1 k l (hall k) (hall l) hkl
  intro i
  obtain ⟨k, hk⟩ := Finite.surjective_of_injective hinj i
  exact ⟨k, hall k, hk⟩

theorem full_history_stops {n : ℕ} (π : Policy n) (ω : Outcome n)
    (h : History n) (hh : rolloutInvariant ω (n + 1) h) :
    π.next (h, ω.2) = none := by
  cases hd : π.next (h, ω.2) with
  | none => rfl
  | some i =>
      exact False.elim
        ((π.next_unopened h ω.2 i hd) (full_history_opened ω h hh i))

theorem rollout_terminal_stops {n : ℕ} (π : Policy n) (ω : Outcome n)
    (fuel step : ℕ) (h : History n) (hh : rolloutInvariant ω step h)
    (hbudget : step + fuel = n + 1) :
    π.next (rolloutAux π ω fuel step h, ω.2) = none := by
  induction fuel generalizing step h with
  | zero =>
      have hs : step = n + 1 := by omega
      subst step
      exact full_history_stops π ω h hh
  | succ fuel ih =>
      cases hd : π.next (h, ω.2) with
      | none => simpa only [rolloutAux, hd] using hd
      | some i =>
          have hs : step < n + 1 := by omega
          have hnew := rolloutInvariant_update ω step h i hs hh
            (π.next_unopened h ω.2 i hd)
          simpa only [rolloutAux, hd, dif_pos hs] using
            ih (step + 1) (Function.update h ⟨step, hs⟩ (true, i, ω.1 i))
              hnew (by omega)

theorem terminalHistory_stops {n : ℕ} (π : Policy n) (ω : Outcome n) :
    π.next (terminalHistory π ω, ω.2) = none :=
  rollout_terminal_stops π ω n 1 (initialHistory π ω)
    (initialHistory_invariant π ω) (by omega)

theorem zero_terminal_eq_full {n : ℕ} (M : Instance n) (π : Policy n)
    (hπ : isZeroGittinsPolicy M π) (ω : Outcome n)
    (hbound : ∀ i, (ω.1 i : EReal) ≤ zeroReservationIndex M i) :
    terminalReward π ω = fullInformationPayoff ω.1 := by
  apply le_antisymm (terminalReward_le_fullInformationPayoff π ω)
  apply payoff_upper
  intro i
  by_cases hi : wasOpened (terminalHistory π ω) i
  · obtain ⟨k, hk, hki⟩ := hi
    have heq := terminalHistory_sample π ω k hk
    rw [hki] at heq
    rw [← heq]
    exact history_member (terminalHistory π ω) k hk
  · have hstop := hπ.2 (terminalHistory π ω) ω.2 (terminalHistory_valid π ω)
    rw [terminalHistory_stops π ω] at hstop
    exact EReal.coe_le_coe_iff.mp ((hbound i).trans (hstop i hi))

theorem seedLaw_probability : IsProbabilityMeasure seedLaw := by
  constructor
  simp [seedLaw, Real.volume_Icc]

theorem rewards_ae_below_indices {n : ℕ} (M : Instance n) :
    ∀ᵐ ω ∂jointLaw M, ∀ i, (ω.1 i : EReal) ≤ zeroReservationIndex M i := by
  letI : ∀ j, IsProbabilityMeasure (M.law j) := M.law_probability
  letI : IsProbabilityMeasure seedLaw := seedLaw_probability
  have hi : ∀ i, ∀ᵐ ω ∂jointLaw M,
      (ω.1 i : EReal) ≤ zeroReservationIndex M i := by
    intro i
    have heval : MeasurePreserving (fun ω : Outcome n => ω.1 i)
        (jointLaw M) (M.law i) := by
      simpa only [jointLaw, Function.comp_def, Function.eval] using
        (measurePreserving_eval M.law i).comp
          (measurePreserving_fst (μ := Measure.pi M.law) (ν := seedLaw))
    have hle : ∀ᵐ (y : ℝ) ∂M.law i, (y : EReal) ≤ zeroReservationIndex M i := by
      change ∀ᵐ (y : ℝ) ∂M.law i,
        (y : EReal) ≤ essSup (fun y : ℝ => (y : EReal)) (M.law i)
      exact ae_le_essSup (f := fun y : ℝ => (y : EReal)) (μ := M.law i)
    exact heval.quasiMeasurePreserving.ae hle
  exact ae_all_iff.mpr hi

theorem zero_full_information {n : ℕ} (M : Instance n) (π : Policy n)
    (hπ : isZeroGittinsPolicy M π) :
    expectedReward M π = fullInformationReward M ∧ optimal M 0 π := by
  have hae : terminalReward π =ᵐ[jointLaw M]
      (fun ω : Outcome n => fullInformationPayoff ω.1) := by
    filter_upwards [rewards_ae_below_indices M] with ω hω
    exact zero_terminal_eq_full M π hπ ω hω
  have heq : expectedReward M π = fullInformationReward M := integral_congr_ae hae
  have hπint := (policy_terminal_measurable_integrable M π).2.2.1
  have hfullint := hπint.congr hae
  refine ⟨heq, ?_⟩
  intro ρ
  have hρint := (policy_terminal_measurable_integrable M ρ).2.2.1
  have hle : expectedReward M ρ ≤ fullInformationReward M :=
    integral_mono hρint hfullint (terminalReward_le_fullInformationPayoff ρ)
  simpa only [value, zero_mul, sub_zero, heq] using hle

end PandoraBO.Private20261023.ZeroFullInformation

theorem solution {n : ℕ} (M : PandoraBO.Instance n) (π : PandoraBO.Policy n)
    (hπ : PandoraBO.isZeroGittinsPolicy M π) :
    PandoraBO.expectedReward M π = PandoraBO.fullInformationReward M ∧
    PandoraBO.optimal M 0 π :=
  PandoraBO.Private20261023.ZeroFullInformation.zero_full_information M π hπ

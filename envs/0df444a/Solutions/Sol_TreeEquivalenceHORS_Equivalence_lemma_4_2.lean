-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T17:54:55.141538+00:00
-- url     : https://prove2.me/submissions/83d42a72-016c-4263-bca1-8484ce6702c2

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Machines
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_4_1

namespace TreeEquivalenceHORS.Equivalence

private theorem snoc_all (P : List Choice → Choice → Prop) (v : List Choice) (e : Choice) :
    (∀ (k : ℕ) (hk : k < (v ++ [e]).length), P ((v ++ [e]).take k) (v ++ [e])[k]) ↔
      (∀ (k : ℕ) (hk : k < v.length), P (v.take k) v[k]) ∧ P v e := by
  constructor
  · exact fun h => ⟨fun k hk => by
      have hk' : k < (v ++ [e]).length := by simp; omega
      simpa only [List.take_append_of_le_length hk.le, List.getElem_append_left hk (h' := hk')] using
        h k hk', by simpa using h v.length (by simp)⟩
  · rintro ⟨h, he⟩ k hk
    by_cases hlt : k < v.length
    · simpa only [List.take_append_of_le_length hlt.le, List.getElem_append_left hlt (h' := hk)] using h k hlt
    · have : k = v.length := by simp at hk; omega
      simpa [this] using he

theorem cand_snoc (M : Machine) (v : List Choice) (e : Choice) :
    M.IsCand (v ++ [e]) ↔ M.IsCand v ∧ M.Active (M.pc v) :=
  snoc_all (fun u _ => M.Active (M.pc u)) v e

private theorem legal_snoc (M : Machine) (v : List Choice) (e : Choice) :
    M.IsLegal (v ++ [e]) ↔ M.IsLegal v ∧ M.Active (M.pc v) ∧ M.guard e (M.conf v) := by
  simp only [Machine.IsLegal, cand_snoc,
    snoc_all (fun u c => M.guard c (M.conf u)), and_assoc, and_left_comm, and_comm]

private theorem go_snoc (M : Machine) (v : List Choice) (e : Choice)
    (m : ℕ) (sw : (ℕ × ℤ × ℤ) × ℤ) :
    M.go m sw (v ++ [e]) =
      (M.delta e (M.go m sw v).1, (M.go m sw v).2 * M.phi (m + v.length) e (M.go m sw v).1) := by
  induction v generalizing m sw with
  | nil => rfl
  | cons c v ih =>
    have clock : m + 1 + v.length = m + (v.length + 1) := by omega
    simpa only [List.cons_append, Machine.go, List.length_cons, clock] using
      ih (m + 1) (M.delta c sw.1, sw.2 * M.phi m c sw.1)

theorem conf_snoc (M : Machine) (v : List Choice) (e : Choice) :
    M.conf (v ++ [e]) = M.delta e (M.conf v) := by simp [Machine.conf, go_snoc]

theorem active_lookup (M : Machine) {i : ℕ} :
    M.Active i ↔ (M.lookup i).isSome := by
  cases i <;> simp [Machine.Active, Machine.lookup]

private def liftConfig (q : ℕ × ℕ × ℕ) : ℕ × ℤ × ℤ := (q.1, q.2.1, q.2.2)

private theorem choices_of_step {M : Machine} {q r : ℕ × ℕ × ℕ} (h : M.Step q r) :
    ∃ e, M.Active q.1 ∧ M.guard e (liftConfig q) ∧ M.delta e (liftConfig q) = liftConfig r := by
  cases h
  all_goals first
    | refine ⟨.one, (active_lookup M).mpr ?_, ?_⟩ <;> solve | simp_all [liftConfig, Machine.guard, Machine.delta]
    | refine ⟨.two, (active_lookup M).mpr ?_, ?_⟩ <;> simp_all [liftConfig, Machine.guard, Machine.delta]

private theorem step_of_choice {M : Machine} (q : ℕ × ℕ × ℕ) (e : Choice)
    (hg : M.guard e (liftConfig q)) :
    ∃ r, M.Step q r ∧ M.delta e (liftConfig q) = liftConfig r := by
  obtain ⟨i, a, b⟩ := q
  cases h : M.lookup i with
  | none => simp [Machine.guard, liftConfig, h] at hg
  | some ins =>
    cases ins with
    | incA => exact ⟨_, Machine.Step.incA h, by cases e <;> simp [liftConfig, Machine.delta, h]⟩
    | incB => exact ⟨_, Machine.Step.incB h, by cases e <;> simp [liftConfig, Machine.delta, h]⟩
    | decA j =>
      cases e <;> cases a <;> simp_all [Machine.guard, liftConfig, Machine.delta]
      · exact ⟨0, Machine.Step.decAZero h, rfl⟩
      · omega
      · exact Machine.Step.decAPos h
    | decB j =>
      cases e <;> cases b <;> simp_all [Machine.guard, liftConfig, Machine.delta]
      · exact ⟨0, Machine.Step.decBZero h, rfl⟩
      · omega
      · exact Machine.Step.decBPos h

private theorem word_of_run {M : Machine} {r : ℕ × ℕ × ℕ}
    (h : Relation.ReflTransGen M.Step (1, 0, 0) r) :
    ∃ v, M.IsLegal v ∧ M.conf v = liftConfig r := by
  induction h with
  | refl => exact ⟨[], by simp [Machine.IsLegal, Machine.IsCand], rfl⟩
  | tail _ hs ih =>
    obtain ⟨v, hv, hq⟩ := ih
    obtain ⟨e, ha, hg, hr⟩ := choices_of_step hs
    refine ⟨v ++ [e], (legal_snoc ..).mpr ⟨hv, ?_, ?_⟩, ?_⟩ <;> simp_all [Machine.pc, conf_snoc, liftConfig]

private theorem run_of_word {M : Machine} {v : List Choice} (hv : M.IsLegal v) :
    ∃ r, Relation.ReflTransGen M.Step (1, 0, 0) r ∧ M.conf v = liftConfig r := by
  induction v using List.reverseRecOn with
  | nil => exact ⟨(1, 0, 0), .refl, rfl⟩
  | append_singleton v e ih =>
    obtain ⟨hl, _, hg⟩ := (legal_snoc ..).mp hv
    obtain ⟨q, hq, hconf⟩ := ih hl
    obtain ⟨r, hs, hr⟩ := step_of_choice q e (hconf ▸ hg)
    exact ⟨r, hq.tail hs, by simpa [conf_snoc, hconf] using hr⟩

private theorem proved_here (M : Machine) :
    M.Halts ↔ ∃ v : List Choice, M.IsCand v ∧ ¬ M.Active (M.pc v) ∧ M.weight v ≠ 0 := by
  constructor
  · rintro ⟨q, a, b, hrun, halt⟩
    obtain ⟨v, hl, hc⟩ := word_of_run hrun
    exact ⟨v, hl.1, by simpa [Machine.pc, hc, liftConfig] using halt, (lemma_4_1 M v hl.1).mpr hl⟩
  · rintro ⟨v, hv, halt, hw⟩
    obtain ⟨⟨q, a, b⟩, hr, hc⟩ := run_of_word ((lemma_4_1 M v hv).mp hw)
    exact ⟨q, a, b, hr, by simpa [Machine.pc, hc, liftConfig] using halt⟩

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution (M : Machine) :
    M.Halts ↔ ∃ v : List Choice, M.IsCand v ∧ ¬ M.Active (M.pc v) ∧ M.weight v ≠ 0 := proved_here M

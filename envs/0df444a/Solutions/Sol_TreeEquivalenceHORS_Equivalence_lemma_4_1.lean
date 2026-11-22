-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T17:53:58.881076+00:00
-- url     : https://prove2.me/submissions/9c1356b1-f6e9-400f-a8a1-a53d5a7b9252

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Machines

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

private theorem weight_snoc (M : Machine) (v : List Choice) (e : Choice) :
    M.weight (v ++ [e]) = M.weight v * M.phi v.length e (M.conf v) := by
  simp [Machine.weight, Machine.conf, go_snoc]

private theorem zpoly_guard {m : ℕ} {x : ℤ} (hx : 0 ≤ x) (hm : x ≤ m) :
    Zpoly m x ≠ 0 ↔ x = 0 := by
  rw [Zpoly, Finset.prod_ne_zero_iff]
  constructor
  · intro h
    by_contra hn
    exact h (x.toNat - 1) (Finset.mem_range.mpr (by omega)) (by omega)
  · intro h a _
    omega

theorem active_lookup (M : Machine) {i : ℕ} :
    M.Active i ↔ (M.lookup i).isSome := by
  cases i <;> simp [Machine.Active, Machine.lookup]

private def Bounded (m : ℕ) (s : ℕ × ℤ × ℤ) : Prop :=
  0 ≤ s.2.1 ∧ s.2.1 ≤ m ∧ 0 ≤ s.2.2 ∧ s.2.2 ≤ m

private theorem phi_guard (M : Machine) {m : ℕ} (e : Choice) {s : ℕ × ℤ × ℤ}
    (ha : M.Active s.1) (hb : Bounded m s) :
    M.phi m e s ≠ 0 ↔ M.guard e s := by
  obtain ⟨a0, am, b0, bm⟩ := hb
  obtain ⟨ins, h⟩ := Option.isSome_iff_exists.mp ((active_lookup M).mp ha)
  cases ins <;> cases e <;> simp [Machine.phi, Machine.guard, h, zpoly_guard a0 am, zpoly_guard b0 bm] <;> omega

private theorem delta_bounded (M : Machine) {m : ℕ} (e : Choice) {s : ℕ × ℤ × ℤ}
    (hb : Bounded m s) (hg : M.guard e s) : Bounded (m + 1) (M.delta e s) := by
  obtain ⟨a0, am, b0, bm⟩ := hb
  cases h : M.lookup s.1 with
  | none => simp [Machine.guard, h] at hg
  | some ins => cases ins <;> cases e <;> simp_all [Bounded, Machine.delta, Machine.guard] <;> omega

private theorem prefixInvariant (M : Machine) (v : List Choice) (hv : M.IsCand v) :
    (M.weight v ≠ 0 ↔ M.IsLegal v) ∧
      (M.IsLegal v → Bounded v.length (M.conf v)) := by
  induction v using List.reverseRecOn with
  | nil => simp [Bounded, Machine.weight, Machine.conf, Machine.go, Machine.IsLegal, hv]
  | append_singleton v e ih =>
    obtain ⟨hc, ha⟩ := (cand_snoc M v e).mp hv
    obtain ⟨hw, hb⟩ := ih hc
    simp only [weight_snoc, mul_ne_zero_iff, hw, legal_snoc, ha, true_and, conf_snoc,
      List.length_append, List.length_singleton]
    exact ⟨and_congr_right fun hl => phi_guard M e ha (hb hl),
      fun ⟨hl, hg⟩ => delta_bounded M e (hb hl) hg⟩

private theorem proved_here (M : Machine) (v : List Choice) (hv : M.IsCand v) :
    M.weight v ≠ 0 ↔ M.IsLegal v :=
  (prefixInvariant M v hv).1

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution (M : Machine) (v : List Choice) (hv : M.IsCand v) :
    M.weight v ≠ 0 ↔ M.IsLegal v := proved_here M v hv

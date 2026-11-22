-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T17:54:56.009604+00:00
-- url     : https://prove2.me/submissions/0b914840-5999-4754-9fb2-4e437eb5ec38

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_3
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_4

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

theorem step_control (side : Side) (M : Machine) {i : ℕ} (hi : i ≤ M.length) (t : StateArgs) :
    (compile side M).headStep (Tm.apps (.nt (iF i)) t.toList) =
      some ((ctrlBody side M i).subst t.toList) := by
  have hsp : (Tm.apps (.nt (iF i)) t.toList).spine = (.nt (iF i), t.toList) := rfl
  have hty : (compile side M).nts[iF i]? = some tyF := by
    rw [show iF i = i + 13 by unfold iF; omega]
    exact List.getElem?_replicate_of_lt (Nat.lt_succ_of_le hi)
  have hr : (compile side M).rules[iF i]? = some (ctrlBody side M i) := by
    rw [show iF i = i + 13 by unfold iF; omega]
    change ((List.range (M.length + 1)).map (ctrlBody side M))[i]? = _
    simp [List.getElem?_range (Nat.lt_succ_of_le hi)]
  simp only [HORS.headStep, hsp, hty, hr]
  rfl

private theorem control_active (side : Side) (M : Machine) {i : ℕ} (ha : M.Active i) (t : StateArgs) :
    (compile side M).headStep (Tm.apps (.nt (iF i)) t.toList) =
      some (Tm.apps tb [tz, callF M (M.nextPos i .one) (M.contArgs i .one t).toList,
        callF M (M.nextPos i .two) (M.contArgs i .two t).toList]) := by
  rw [step_control side M ha.2]
  obtain ⟨ins, h⟩ := Option.isSome_iff_exists.mp ((active_lookup M).mp ha)
  cases ins <;> simp only [ctrlBody, Machine.nextPos, Machine.contArgs, h] <;> rfl

private theorem reg_step (side : Side) (M : Machine) (m i : ℕ) (t : StateArgs) (R : PairState)
    (ha : M.Active i) (reg : Reg (compile side M) m t R) (e : Choice) :
    Reg (compile side M) (m + 1) (M.contArgs i e t) (M.pairStep m i e R) := by
  obtain ⟨pol, hu, hv, hr, hs, hh, hk⟩ := reg
  have newpol := (lemma_5_4 side M).2 m _ _ pol
  obtain ⟨_, _, ops, pair, _⟩ := lemma_5_3 side M
  have succ_u := (ops _ _ _ _ hu hu).1
  have succ_v := (ops _ _ _ _ hv hv).1
  have succ_r := (ops _ _ _ _ hr hr).1
  have succ_s := (ops _ _ _ _ hs hs).1
  obtain ⟨pa, qa⟩ := pol.2.2 _ _ _ _ hu hv
  obtain ⟨pb, qb⟩ := pol.2.2 _ _ _ _ hr hs
  obtain ⟨ins, h⟩ := Option.isSome_iff_exists.mp ((active_lookup M).mp ha)
  cases ins <;> cases e <;>
    simp only [Reg, Machine.contArgs, Machine.pairStep, h, pinc, pdec, pmul]
  all_goals first
    | exact ⟨newpol, succ_u, hv, hr, hs, hh, hk⟩
    | exact ⟨newpol, hu, hv, succ_r, hs, hh, hk⟩
    | exact ⟨newpol, hu, hv, hr, hs, pair _ _ _ _ _ _ _ _ hh hk pa qa⟩
    | exact ⟨newpol, hu, succ_v, hr, hs, pair _ _ _ _ _ _ _ _ hh hk hu hv⟩
    | exact ⟨newpol, hu, hv, hr, hs, pair _ _ _ _ _ _ _ _ hh hk pb qb⟩
    | exact ⟨newpol, hu, hv, hr, succ_s, pair _ _ _ _ _ _ _ _ hh hk hr hs⟩

private theorem along_snoc (M : Machine) (v : List Choice) (e : Choice) (m i : ℕ)
    (t : StateArgs) (R : PairState) :
    M.along m i t R (v ++ [e]) =
      let s := M.along m i t R v
      (M.nextPos s.1 e, M.contArgs s.1 e s.2.1, M.pairStep (m + v.length) s.1 e s.2.2) := by
  induction v generalizing m i t R with
  | nil => rfl
  | cons c v ih =>
    have clock : m + 1 + v.length = m + (v.length + 1) := by omega
    simpa only [List.cons_append, Machine.along, List.length_cons, clock] using
      ih (m + 1) (M.nextPos i c) (M.contArgs i c t) (M.pairStep m i c R)

private theorem next_delta (M : Machine) (s : ℕ × ℤ × ℤ) (e : Choice) :
    M.nextPos s.1 e = (M.delta e s).1 := by
  cases h : M.lookup s.1 with
  | none => cases e <;> simp [Machine.nextPos, Machine.delta, h]
  | some ins => cases e <;> cases ins <;> simp [Machine.nextPos, Machine.delta, h]

private theorem along_pc (M : Machine) (v : List Choice) :
    (M.along 0 1 Machine.initArgs Machine.initPairs v).1 = M.pc v := by
  induction v using List.reverseRecOn with
  | nil => rfl
  | append_singleton v e ih =>
    simp only [along_snoc, ih, Machine.pc, conf_snoc, next_delta]

private theorem along_reg (side : Side) (M : Machine) (v : List Choice) (hc : M.IsCand v) :
    Reg (compile side M) v.length (M.argsAlong v) (M.pairsAlong v) := by
  induction v using List.reverseRecOn with
  | nil =>
    obtain ⟨hz, ho, _⟩ := lemma_5_3 side M
    exact ⟨(lemma_5_4 side M).1, hz, hz, hz, hz, ho, hz⟩
  | append_singleton v e ih =>
    obtain ⟨hv, ha⟩ := (cand_snoc M v e).mp hc
    simpa only [Machine.argsAlong, Machine.pairsAlong, along_snoc, along_pc,
      Nat.zero_add, List.length_append, List.length_singleton] using
      reg_step side M _ _ _ _ ha (ih hv) e

private theorem proved_here (side : Side) (M : Machine) :
    let G := compile side M
    (∀ (m i : ℕ) (t : StateArgs) (R : PairState), M.Active i → Reg G m t R →
      G.headStep (Tm.apps (.nt (iF i)) t.toList) =
          some (Tm.apps tb [tz, callF M (M.nextPos i .one) (M.contArgs i .one t).toList,
            callF M (M.nextPos i .two) (M.contArgs i .two t).toList]) ∧
        ∀ e : Choice, Reg G (m + 1) (M.contArgs i e t) (M.pairStep m i e R)) ∧
    (∀ v : List Choice, M.IsCand v → Reg G v.length (M.argsAlong v) (M.pairsAlong v)) :=
  ⟨fun m i t R ha hr => ⟨control_active side M ha t, reg_step side M m i t R ha hr⟩,
    along_reg side M⟩

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution (side : Side) (M : Machine) :
    let G := compile side M
    (∀ (m i : ℕ) (t : StateArgs) (R : PairState), M.Active i → Reg G m t R →
      G.headStep (Tm.apps (.nt (iF i)) t.toList) =
          some (Tm.apps tb [tz, callF M (M.nextPos i .one) (M.contArgs i .one t).toList,
            callF M (M.nextPos i .two) (M.contArgs i .two t).toList]) ∧
        ∀ e : Choice, Reg G (m + 1) (M.contArgs i e t) (M.pairStep m i e R)) ∧
    (∀ v : List Choice, M.IsCand v → Reg G v.length (M.argsAlong v) (M.pairsAlong v)) := proved_here side M

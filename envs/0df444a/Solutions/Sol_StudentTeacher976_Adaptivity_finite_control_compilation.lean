-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.finite_control_compilation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:41:03.708062+00:00
-- url     : https://prove2.me/submissions/bb70e072-2829-4b40-b5b4-ba8195de2b7c

import Definitions.Def_StudentTeacher976_Adaptivity_FiniteControl

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM

private theorem halted_state (M : OTM) (O : Oracle) (x : List Bool) (t : ℕ)
    (h : (M.result O x t).isSome) :
    (M.runCfg O x t).state = 1 ∨ (M.runCfg O x t).state = 2 := by
  unfold result at h
  dsimp only at h
  split at h
  · exact Or.inl ‹_›
  · split at h
    · exact Or.inr ‹_›
    · simp at h

 theorem runCfg_stable (M : OTM) (O : Oracle) (x : List Bool) (t s : ℕ)
    (h : (M.result O x t).isSome) : M.runCfg O x (t + s) = M.runCfg O x t := by
  have hstep : M.step O (M.runCfg O x t) = M.runCfg O x t := by
    simp [step, halted_state M O x t h]
  have hiter : ∀ s, (M.step O)^[s] (M.runCfg O x t) = M.runCfg O x t := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih => rw [Function.iterate_succ_apply', ih, hstep]
  unfold runCfg
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact hiter s

 theorem result_stable (M : OTM) (O : Oracle) (x : List Bool) (t s : ℕ)
    (h : (M.result O x t).isSome) : M.result O x (t + s) = M.result O x t := by
  unfold result
  rw [runCfg_stable M O x t s h]

 theorem output_stable (M : OTM) (O : Oracle) (x : List Bool) (t s : ℕ)
    (h : (M.result O x t).isSome) : M.output O x (t + s) = M.output O x t := by
  unfold output
  rw [runCfg_stable M O x t s h]

 theorem result_of_le (M : OTM) (O : Oracle) (x : List Bool) (t u : ℕ)
    (h : (M.result O x t).isSome) (htu : t ≤ u) : M.result O x u = M.result O x t := by
  rw [← Nat.add_sub_of_le htu]
  exact result_stable M O x t (u - t) h

 theorem output_of_le (M : OTM) (O : Oracle) (x : List Bool) (t u : ℕ)
    (h : (M.result O x t).isSome) (htu : t ≤ u) : M.output O x u = M.output O x t := by
  rw [← Nat.add_sub_of_le htu]
  exact output_stable M O x t (u - t) h

end QAdvFew.PoQOracle.OTM

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM

private theorem bitOf_zero (g : ℕ) : bitOf (0 : Fin (g + 3)) = none := by
  simp (disch := omega) [bitOf, Fin.ext_iff, Nat.mod_eq_of_lt]

private theorem readBits_nat {g : ℕ} (tape : ℤ → Fin (g + 3)) (hi : ℤ) :
    readBits tape hi = (((List.range (hi + 1).toNat).map
      (fun j : ℕ => bitOf (tape (j : ℤ)))).takeWhile (·.isSome)).reduceOption := by
  unfold readBits
  change ((List.map (fun j : ℤ => bitOf (tape j))
      ((List.range (hi + 1).toNat).flatMap (fun j : ℕ => [(j : ℤ)]))).takeWhile
      (·.isSome)).reduceOption = _
  rw [← List.map_eq_flatMap, List.map_map]
  rfl

private theorem takeWhile_none (A B : List (Option Bool)) :
    (A ++ none :: B).takeWhile (·.isSome) = A.takeWhile (·.isSome) := by
  induction A with
  | nil => rfl
  | cons a A ih => cases a <;> simp [List.takeWhile, ih]

private theorem readBits_more {g : ℕ} (tape : ℤ → Fin (g + 3)) (n extra : ℕ)
    (hblank : tape (n : ℤ) = 0) :
    ((((List.range (n + extra)).map (fun j : ℕ => bitOf (tape (j : ℤ)))).takeWhile (·.isSome)).reduceOption) =
      ((((List.range n).map (fun j : ℕ => bitOf (tape (j : ℤ)))).takeWhile (·.isSome)).reduceOption) := by
  rw [List.range_add, List.map_append, List.map_map]
  cases extra with
  | zero => simp
  | succ e =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, Function.comp_apply, Nat.add_zero, hblank, bitOf_zero, takeWhile_none]

 theorem readBits_of_le {g : ℕ} (tape : ℤ → Fin (g + 3)) (lo hi : ℤ)
    (hlo : 0 ≤ lo) (hle : lo ≤ hi) (hblank : tape (lo + 1) = 0) :
    readBits tape hi = readBits tape lo := by
  rw [readBits_nat, readBits_nat]
  have hn : (lo + 1).toNat ≤ (hi + 1).toNat := by omega
  have heq : (hi + 1).toNat = (lo + 1).toNat + ((hi + 1).toNat - (lo + 1).toNat) := by omega
  rw [heq]
  apply readBits_more
  simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ lo + 1), Int.natCast_natAbs] using hblank

structure TapeValid {g : ℕ} (tape : ℤ → Fin (g + 3)) (head lo hi : ℤ) : Prop where
  lo_head : lo ≤ head
  head_hi : head ≤ hi
  lo_zero : lo ≤ 0
  zero_hi : 0 ≤ hi
  outside : ∀ i, i < lo ∨ hi < i → tape i = 0

 theorem TapeValid.update_move {g : ℕ} {tape : ℤ → Fin (g + 3)} {head lo hi : ℤ}
    (h : TapeValid tape head lo hi) (a : Fin (g + 3)) (newhead : ℤ) :
    TapeValid (Function.update tape head a) newhead (min lo newhead) (max hi newhead) := by
  constructor
  · exact min_le_right _ _
  · exact le_max_right _ _
  · exact le_trans (min_le_left _ _) h.lo_zero
  · exact le_trans h.zero_hi (le_max_left _ _)
  · intro i hiout
    have hiold : i < lo ∨ hi < i := by rcases hiout with hl | hr <;> omega
    have hne : i ≠ head := by rcases hiold with hl | hr <;> have := h.lo_head <;> have := h.head_hi <;> omega
    rw [Function.update_of_ne hne]
    exact h.outside i hiold

structure Valid (M : OTM) (c : M.Cfg) : Prop where
  work : TapeValid c.work c.wh c.wlo c.whi
  query : TapeValid c.query c.qh c.qlo c.qhi

 theorem valid_init (M : OTM) (x : List Bool) : Valid M (M.init x) := by
  constructor
  · constructor
    · rfl
    · dsimp [init]; omega
    · rfl
    · dsimp [init]; omega
    · intro i hi
      simp only [init] at *
      rw [if_neg (by rcases hi with h | h <;> omega)]
  · constructor
    · rfl
    · rfl
    · rfl
    · rfl
    · intro i hi; rfl

 theorem valid_step (M : OTM) (O : Oracle) (c : M.Cfg) (h : Valid M c) : Valid M (M.step O c) := by
  unfold step
  split
  · exact h
  · split
    · exact ⟨h.work, h.query⟩
    · constructor
      · exact h.work.update_move _ _
      · exact h.query.update_move _ _

 theorem valid_runCfg (M : OTM) (O : Oracle) (x : List Bool) (t : ℕ) : Valid M (M.runCfg O x t) := by
  induction t with
  | zero => exact valid_init M x
  | succ t ih =>
    rw [runCfg, Function.iterate_succ_apply']
    change Valid M (M.step O (M.runCfg O x t))
    exact valid_step M O _ ih

structure CoreEq (M : OTM) (c d : M.Cfg) : Prop where
  state : c.state = d.state
  work : c.work = d.work
  wh : c.wh = d.wh
  query : c.query = d.query
  qh : c.qh = d.qh

 theorem TapeValid.readBits_eq {g : ℕ} {tape : ℤ → Fin (g + 3)} {h h' l l' u u' : ℤ}
    (ht : TapeValid tape h l u) (ht' : TapeValid tape h' l' u') :
    readBits tape u = readBits tape u' := by
  rcases le_total u u' with hle | hle
  · exact (readBits_of_le tape u u' ht.zero_hi hle (ht.outside _ (by omega))).symm
  · exact readBits_of_le tape u' u ht'.zero_hi hle (ht'.outside _ (by omega))

 theorem coreEq_step (M : OTM) (O : Oracle) (c d : M.Cfg)
    (hc : Valid M c) (hd : Valid M d) (h : CoreEq M c d) :
    CoreEq M (M.step O c) (M.step O d) := by
  have hread : readBits c.query c.qhi = readBits d.query d.qhi := by
    have hq := hc.query
    rw [h.query] at hq
    rw [h.query]
    exact hq.readBits_eq hd.query
  unfold step
  simp only [h.state, h.work, h.wh, h.qh]
  rw [hread]
  simp only [h.query]
  split
  · exact h
  · split <;> constructor <;> rfl

 theorem valid_iterate (M : OTM) (O : Oracle) (c : M.Cfg) (t : ℕ) (hc : Valid M c) :
    Valid M ((M.step O)^[t] c) := by
  induction t with
  | zero => exact hc
  | succ t ih => rw [Function.iterate_succ_apply']; exact valid_step M O _ ih

 theorem coreEq_iterate (M : OTM) (O : Oracle) (c d : M.Cfg) (t : ℕ)
    (hc : Valid M c) (hd : Valid M d) (h : CoreEq M c d) :
    CoreEq M ((M.step O)^[t] c) ((M.step O)^[t] d) := by
  induction t with
  | zero => exact h
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact coreEq_step M O _ _ (valid_iterate M O c t hc) (valid_iterate M O d t hd) ih

 theorem coreEq_readBits_work (M : OTM) (c d : M.Cfg)
    (hc : Valid M c) (hd : Valid M d) (h : CoreEq M c d) :
    readBits c.work c.whi = readBits d.work d.whi := by
  have hw := hc.work
  rw [h.work] at hw ⊢
  exact hw.readBits_eq hd.work

 theorem result_of_coreEq (M : OTM) (O : Oracle) (x y : List Bool) (s t : ℕ)
    (h : CoreEq M (M.runCfg O x s) (M.runCfg O y t)) : M.result O x s = M.result O y t := by
  unfold result
  dsimp only
  rw [h.state]

 theorem output_of_coreEq (M : OTM) (O : Oracle) (x y : List Bool) (s t : ℕ)
    (h : CoreEq M (M.runCfg O x s) (M.runCfg O y t)) : M.output O x s = M.output O y t :=
  coreEq_readBits_work M _ _ (valid_runCfg M O x s) (valid_runCfg M O y t) h

end QAdvFew.PoQOracle.OTM

namespace QAdvFew.PoQOracle.OTM.Precheck
theorem normal_step (N : OTM) (O : Oracle) (c : N.Cfg)
    (hh : ¬ (c.state = 1 ∨ c.state = 2)) (hq : c.state ≠ 3)
    (q : Fin (N.k + 6)) (a b : Fin (N.g + 3)) (m m' : Fin 3)
    (hd : N.δ c.state (c.work c.wh) (c.query c.qh) = (q, a, m, b, m')) :
    N.step O c =
      { state := q
        work := Function.update c.work c.wh a
        wh := c.wh + (m.val : ℤ) - 1
        query := Function.update c.query c.qh b
        qh := c.qh + (m'.val : ℤ) - 1
        wlo := min c.wlo (c.wh + (m.val : ℤ) - 1)
        whi := max c.whi (c.wh + (m.val : ℤ) - 1)
        qlo := min c.qlo (c.qh + (m'.val : ℤ) - 1)
        qhi := max c.qhi (c.qh + (m'.val : ℤ) - 1) } := by
  unfold step
  rw [if_neg hh, if_neg hq]
  dsimp only
  rw [hd]


end QAdvFew.PoQOracle.OTM.Precheck

open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity
private theorem bitOf_symOf (g : ℕ) (b : Bool) : OTM.bitOf (OTM.symOf g b) = some b := by
  cases b <;> rfl

theorem init_readBits (M : OTM) (x : Word) :
    OTM.readBits (M.init x).work (M.init x).whi = x := by
  classical
  have hmap : (List.range (x.length + 1)).map (fun j : ℕ => OTM.bitOf ((M.init x).work (j : ℤ))) =
      x.map some ++ [none] := by
    apply List.ext_getElem
    · simp
    · intro j hj1 hj2
      simp only [List.getElem_map, List.getElem_range]
      by_cases hj : j < x.length
      · rw [List.getElem_append_left (by simpa using hj), List.getElem_map]
        have hji : (j : ℤ) < x.length := by exact_mod_cast hj
        simp only [OTM.init, Int.natCast_nonneg, hji, and_self, if_true, Int.toNat_natCast]
        rw [List.getD_eq_getElem _ _ hj, bitOf_symOf]
      · have heq : j = x.length := by simp only [List.length_map, List.length_range] at hj1; omega
        subst j
        simp [OTM.init, OTM.bitOf, Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < M.g + 3 by omega)]
  unfold OTM.readBits
  change ((List.map (fun j : ℤ => OTM.bitOf ((M.init x).work j))
      ((List.range ((x.length : ℤ) + 1).toNat).flatMap (fun j : ℕ => [(j : ℤ)]))).takeWhile
      (·.isSome)).reduceOption = x
  rw [← List.map_eq_flatMap, List.map_map]
  change (((List.range ((x.length : ℤ) + 1).toNat).map (fun j : ℕ => OTM.bitOf ((M.init x).work (j : ℤ)))).takeWhile
      (·.isSome)).reduceOption = x
  have hnat : ((x.length : ℤ) + 1).toNat = x.length + 1 := by omega
  rw [hnat, hmap]
  clear hmap hnat
  induction x with
  | nil => rfl
  | cons b x ih => simpa using congrArg (List.cons b) ih


end StudentTeacher976.Adaptivity

namespace QAdvFew.PoQOracle.OTM.FiniteControl
section Encoding
variable {Q A : Type} [Fintype Q] [Fintype A]

noncomputable def base (a : Cell A) : Fin (Fintype.card A + 3) :=
  match a with
  | none => 0
  | some (.inl false) => 1
  | some (.inl true) => 2
  | some (.inr a) => ⟨3 + (Fintype.equivFin A a).val, by omega⟩

noncomputable def unbase (a : Fin (Fintype.card A + 3)) : Cell A :=
  if h0 : a.val = 0 then none
  else if h1 : a.val = 1 then bit false
  else if h2 : a.val = 2 then bit true
  else some (.inr ((Fintype.equivFin A).symm ⟨a.val - 3, by omega⟩))

theorem unbase_base (a : Cell A) : unbase (base a) = a := by
  cases a with
  | none => simp [base, unbase]
  | some a => cases a with
    | inl b => cases b <;> simp (disch := omega) [base, unbase, bit, Nat.mod_eq_of_lt]
    | inr a => simp [base, unbase, bit, Nat.add_comm 3, Nat.add_sub_cancel]

noncomputable def sym (a : Cell A) : Fin ((Fintype.card A + Fintype.card (Cell A × Q × Q)) + 3) :=
  ⟨(base a).val, by omega⟩
noncomputable def tag (a : Cell A) (yes no : Q) :
    Fin ((Fintype.card A + Fintype.card (Cell A × Q × Q)) + 3) :=
  ⟨Fintype.card A + 3 + (Fintype.equivFin (Cell A × Q × Q) (a, yes, no)).val, by omega⟩
noncomputable def decode (a : Fin ((Fintype.card A + Fintype.card (Cell A × Q × Q)) + 3)) : Cell A :=
  if h : a.val < Fintype.card A + 3 then unbase ⟨a.val, h⟩ else none
noncomputable def untag (a : Fin ((Fintype.card A + Fintype.card (Cell A × Q × Q)) + 3)) :
    Option (Cell A × Q × Q) :=
  if h : Fintype.card A + 3 ≤ a.val then
    some ((Fintype.equivFin (Cell A × Q × Q)).symm ⟨a.val - (Fintype.card A + 3), by omega⟩)
  else none

theorem decode_sym (a : Cell A) : decode (sym (Q := Q) a) = a := by
  simp only [decode, sym, (base a).isLt, ↓reduceDIte]
  exact unbase_base a

theorem untag_tag (a : Cell A) (yes no : Q) : untag (tag a yes no) = some (a, yes, no) := by
  simp [untag, tag, Nat.add_sub_cancel_left]

noncomputable def state (q : Q) : Fin (Fintype.card Q + 6) :=
  ⟨6 + (Fintype.equivFin Q q).val, by omega⟩
noncomputable def control : Bool ⊕ Q → Fin (Fintype.card Q + 6)
  | .inl b => if b then 1 else 2
  | .inr q => state q

noncomputable abbrev Program.machine (P : Program Q A) : OTM where
  k := Fintype.card Q
  g := Fintype.card A + Fintype.card (Cell A × Q × Q)
  δ := fun q a b =>
    if hstart : q.val = 0 then (state P.start, a, 1, b, 1)
    else if hyes : q.val = 4 ∨ q.val = 5 then
      match untag a with
      | none => (2, a, 1, b, 1)
      | some (old, yes, no) => (state (if q.val = 4 then yes else no), sym old, 1, b, 1)
    else if hrunning : 6 ≤ q.val then
      let s := (Fintype.equivFin Q).symm ⟨q.val - 6, by omega⟩
      match P.code s (decode a) (decode b) with
      | .halt result => (if result then 1 else 2, a, 1, b, 1)
      | .ask yes no => (3, tag (decode a) yes no, 1, b, 1)
      | .move next work wm query qm => (state next, sym work, wm, sym query, qm)
      | .stop result work wm query qm => (if result then 1 else 2, sym work, wm, sym query, qm)
    else (2, a, 1, b, 1)

noncomputable def Program.encode (P : Program Q A) (c : Cfg Q A) : P.machine.Cfg where
  state := control c.state
  work := fun i => sym (c.work i)
  wh := c.wh
  query := fun i => sym (c.query i)
  qh := c.qh
  wlo := c.wlo
  whi := c.whi
  qlo := c.qlo
  qhi := c.qhi

@[simp] theorem sym_none : sym (Q := Q) (none : Cell A) = 0 := by
  apply Fin.ext
  rfl
@[simp] theorem sym_bit (b : Bool) : sym (Q := Q) (bit (A := A) b) = symOf (Fintype.card A + Fintype.card (Cell A × Q × Q)) b := by
  cases b <;> rfl

theorem bitOf_sym (a : Cell A) : bitOf (sym (Q := Q) a) = readBit a := by
  cases a with
  | none => simp (disch := omega) [readBit, bitOf, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  | some a => cases a with
    | inl b => cases b <;> rfl
    | inr a =>
      simp (disch := omega) [bitOf, sym, base, readBit, Fin.ext_iff, Nat.mod_eq_of_lt] <;> split <;> simp_all <;> omega

theorem readBits_sym (tape : ℤ → Cell A) (hi : ℤ) :
    readBits (fun i => sym (Q := Q) (tape i)) hi = readWord tape hi := by
  unfold readBits readWord
  change ((((List.range (hi + 1).toNat).flatMap (fun j : ℕ => [(j : ℤ)])).map
    (fun i => bitOf (sym (Q := Q) (tape i)))).takeWhile (·.isSome)).reduceOption = _
  rw [← List.map_eq_flatMap, List.map_map]
  simp only [bitOf_sym]
  rfl


@[simp] theorem state_val (q : Q) : (state q).val = 6 + (Fintype.equivFin Q q).val := rfl

theorem state_special_ne (q : Q) (n : ℕ) (hn : n < 6) :
    state q ≠ (⟨n, by omega⟩ : Fin (Fintype.card Q + 6)) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [state_val] at hv
  omega

theorem Program.delta_move (P : Program Q A) (q next : Q) (a b work query : Cell A)
    (wm qm : Fin 3) (h : P.code q a b = .move next work wm query qm) :
    P.machine.δ (state q) (sym a) (sym b) = (state next, sym work, wm, sym query, qm) := by
  simp (disch := omega) [Program.machine, state, decode_sym, h] <;> omega

theorem Program.delta_halt (P : Program Q A) (q : Q) (a b : Cell A) (result : Bool)
    (h : P.code q a b = .halt result) :
    P.machine.δ (state q) (sym a) (sym b) = (if result then 1 else 2, sym a, 1, sym b, 1) := by
  simp (disch := omega) [Program.machine, state, decode_sym, h] <;> omega

theorem Program.delta_ask (P : Program Q A) (q yes no : Q) (a b : Cell A)
    (h : P.code q a b = .ask yes no) :
    P.machine.δ (state q) (sym a) (sym b) = (3, tag a yes no, 1, sym b, 1) := by
  simp (disch := omega) [Program.machine, state, decode_sym, h] <;> omega

theorem Program.delta_answer (P : Program Q A) (a : Cell A) (yes no : Q) (b : Cell A)
    (answer : Bool) :
    P.machine.δ (if answer then 4 else 5) (tag a yes no) (sym b) =
      (state (if answer then yes else no), sym a, 1, sym b, 1) := by
  cases answer <;>
    simp (disch := omega) [Program.machine, untag_tag, Nat.mod_eq_of_lt]

theorem sym_update (tape : ℤ → Cell A) (pos : ℤ) (a : Cell A) :
    (fun i => sym (Q := Q) (Function.update tape pos a i)) =
      Function.update (fun i => sym (Q := Q) (tape i)) pos (sym a) := by
  funext i
  by_cases h : i = pos <;> simp [Function.update, h]

def InRange {Q A : Type} (c : Cfg Q A) : Prop :=
  c.wlo ≤ c.wh ∧ c.wh ≤ c.whi ∧ c.qlo ≤ c.qh ∧ c.qh ≤ c.qhi

theorem Program.step_inRange (P : Program Q A) (O : Oracle) (c : Cfg Q A)
    (h : InRange c) : InRange (P.step O c) := by
  unfold Program.step
  split
  · exact h
  · split <;> try exact h
    all_goals exact ⟨min_le_right _ _, le_max_right _ _, min_le_right _ _, le_max_right _ _⟩

theorem Program.move_step (P : Program Q A) (O : Oracle) (c : Cfg Q A) (q next : Q)
    (a b : Cell A) (wm qm : Fin 3) (hc : c.state = .inr q)
    (h : P.code q (c.work c.wh) (c.query c.qh) = .move next a wm b qm) :
    P.machine.step O (P.encode c) = P.encode (P.step O c) := by
  have hs : ¬ ((state q : Fin (Fintype.card Q + 6)) = 1 ∨ state q = 2) := by
    simp (disch := omega) [state, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hq : (state q : Fin (Fintype.card Q + 6)) ≠ 3 := by
    simp (disch := omega) [state, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hd : P.machine.δ (P.encode c).state ((P.encode c).work (P.encode c).wh)
      ((P.encode c).query (P.encode c).qh) = (state next, sym a, wm, sym b, qm) := by
    change P.machine.δ (control c.state) (sym (c.work c.wh)) (sym (c.query c.qh)) = _
    rw [hc]
    exact P.delta_move q next _ _ a b wm qm h
  have hs' : ¬ ((P.encode c).state = 1 ∨ (P.encode c).state = 2) := by
    change ¬ (control c.state = 1 ∨ control c.state = 2)
    rw [hc]
    exact hs
  have hq' : (P.encode c).state ≠ 3 := by
    change control c.state ≠ 3
    rw [hc]
    exact hq
  rw [Precheck.normal_step _ _ _ hs' hq' _ _ _ _ _ hd]
  simp only [Program.step, hc, h, Program.encode, control, sym_update]


theorem Program.normal_step (P : Program Q A) (O : Oracle) (c : Cfg Q A) (q : Q)
    (hc : c.state = .inr q) (next : Fin (Fintype.card Q + 6))
    (a b : Fin ((Fintype.card A + Fintype.card (Cell A × Q × Q)) + 3)) (wm qm : Fin 3)
    (hd : P.machine.δ (state q) (sym (c.work c.wh)) (sym (c.query c.qh)) =
      (next, a, wm, b, qm)) :
    P.machine.step O (P.encode c) =
      { state := next
        work := Function.update (fun i => sym (c.work i)) c.wh a
        wh := c.wh + (wm.val : ℤ) - 1
        query := Function.update (fun i => sym (c.query i)) c.qh b
        qh := c.qh + (qm.val : ℤ) - 1
        wlo := min c.wlo (c.wh + (wm.val : ℤ) - 1)
        whi := max c.whi (c.wh + (wm.val : ℤ) - 1)
        qlo := min c.qlo (c.qh + (qm.val : ℤ) - 1)
        qhi := max c.qhi (c.qh + (qm.val : ℤ) - 1) } := by
  have hs : ¬ ((P.encode c).state = 1 ∨ (P.encode c).state = 2) := by
    change ¬ (control c.state = 1 ∨ control c.state = 2)
    rw [hc]
    simp (disch := omega) [control, state, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hq : (P.encode c).state ≠ 3 := by
    change control c.state ≠ 3
    rw [hc]
    simp (disch := omega) [control, state, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hd' : P.machine.δ (P.encode c).state ((P.encode c).work (P.encode c).wh)
      ((P.encode c).query (P.encode c).qh) = (next, a, wm, b, qm) := by
    change P.machine.δ (control c.state) (sym (c.work c.wh)) (sym (c.query c.qh)) = _
    rw [hc]
    exact hd
  exact Precheck.normal_step _ _ _ hs hq _ _ _ _ _ hd'

theorem Program.delta_stop (P : Program Q A) (q : Q) (result : Bool)
    (a b work query : Cell A) (wm qm : Fin 3)
    (h : P.code q a b = .stop result work wm query qm) :
    P.machine.δ (state q) (sym a) (sym b) =
      (if result then 1 else 2, sym work, wm, sym query, qm) := by
  simp (disch := omega) [Program.machine, state, decode_sym, h] <;> omega

theorem Program.stop_step (P : Program Q A) (O : Oracle) (c : Cfg Q A) (q : Q)
    (result : Bool) (a b : Cell A) (wm qm : Fin 3) (hc : c.state = .inr q)
    (h : P.code q (c.work c.wh) (c.query c.qh) = .stop result a wm b qm) :
    P.machine.step O (P.encode c) = P.encode (P.step O c) := by
  rw [P.normal_step O c q hc _ _ _ _ _ (P.delta_stop q result _ _ a b wm qm h)]
  simp only [Program.step, hc, h, Program.encode, control, sym_update]

theorem Program.halt_step (P : Program Q A) (O : Oracle) (c : Cfg Q A) (q : Q)
    (result : Bool) (hc : c.state = .inr q) (hrange : InRange c)
    (h : P.code q (c.work c.wh) (c.query c.qh) = .halt result) :
    P.machine.step O (P.encode c) = P.encode (P.step O c) := by
  rw [P.normal_step O c q hc _ _ _ _ _ (P.delta_halt q _ _ result h)]
  rcases hrange with ⟨hwlo, hwhi, hqlo, hqhi⟩
  simp [Program.step, hc, h, Program.encode, control,
    Function.update_eq_self, min_eq_left hwlo, max_eq_left hwhi,
    min_eq_left hqlo, max_eq_left hqhi]

noncomputable def Program.askCfg (P : Program Q A) (c : Cfg Q A) (yes no : Q) : P.machine.Cfg :=
  { P.encode c with
    state := 3
    work := Function.update (fun i => sym (c.work i)) c.wh (tag (c.work c.wh) yes no) }

theorem Program.ask_first (P : Program Q A) (O : Oracle) (c : Cfg Q A) (q yes no : Q)
    (hc : c.state = .inr q) (hrange : InRange c)
    (h : P.code q (c.work c.wh) (c.query c.qh) = .ask yes no) :
    P.machine.step O (P.encode c) = P.askCfg c yes no := by
  rw [P.normal_step O c q hc _ _ _ _ _ (P.delta_ask q yes no _ _ h)]
  rcases hrange with ⟨hwlo, hwhi, hqlo, hqhi⟩
  simp [Program.askCfg, Program.encode, Function.update_eq_self,
    min_eq_left hwlo, max_eq_left hwhi, min_eq_left hqlo, max_eq_left hqhi]

private theorem query_step (M : OTM) (O : Oracle) (c : M.Cfg) (hc : c.state = 3) :
    M.step O c = { c with state := if O (readBits c.query c.qhi) then 4 else 5 } := by
  have hs : ¬ (c.state = 1 ∨ c.state = 2) := by
    rw [hc]
    simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  unfold OTM.step
  rw [if_neg hs, if_pos hc]

noncomputable def Program.answerCfg (P : Program Q A) (c : Cfg Q A) (yes no : Q)
    (answer : Bool) : P.machine.Cfg :=
  {P.askCfg c yes no with state := if answer then 4 else 5}

theorem Program.ask_second (P : Program Q A) (O : Oracle) (c : Cfg Q A) (yes no : Q) :
    P.machine.step O (P.askCfg c yes no) =
      P.answerCfg c yes no (O (readWord c.query c.qhi)) := by
  rw [query_step _ _ _ rfl]
  simp only [Program.askCfg, Program.encode, readBits_sym, Program.answerCfg]

theorem Program.ask_third (P : Program Q A) (O : Oracle) (c : Cfg Q A) (yes no : Q)
    (answer : Bool) (hrange : InRange c) :
    P.machine.step O (P.answerCfg c yes no answer) =
      P.encode {c with state := .inr (if answer then yes else no)} := by
  have hs : ¬ ((P.answerCfg c yes no answer).state = 1 ∨
      (P.answerCfg c yes no answer).state = 2) := by
    cases answer <;>
      simp (disch := omega) [Program.answerCfg, Fin.ext_iff, Nat.mod_eq_of_lt]
  have hq : (P.answerCfg c yes no answer).state ≠ 3 := by
    cases answer <;>
      simp (disch := omega) [Program.answerCfg, Fin.ext_iff, Nat.mod_eq_of_lt]
  have hd : P.machine.δ (P.answerCfg c yes no answer).state
      ((P.answerCfg c yes no answer).work (P.answerCfg c yes no answer).wh)
      ((P.answerCfg c yes no answer).query (P.answerCfg c yes no answer).qh) =
      (state (if answer then yes else no), sym (c.work c.wh), 1, sym (c.query c.qh), 1) := by
    change P.machine.δ (if answer then 4 else 5)
      ((Function.update (fun i => sym (c.work i)) c.wh (tag (c.work c.wh) yes no)) c.wh)
      (sym (c.query c.qh)) = _
    rw [Function.update_self]
    exact P.delta_answer _ yes no _ answer
  rw [Precheck.normal_step _ _ _ hs hq _ _ _ _ _ hd]
  rcases hrange with ⟨hwlo, hwhi, hqlo, hqhi⟩
  simp [Program.answerCfg, Program.askCfg, Program.encode, control,
    Function.update_idem, Function.update_eq_self,
    min_eq_left hwlo, max_eq_left hwhi, min_eq_left hqlo, max_eq_left hqhi]

theorem Program.ask_steps (P : Program Q A) (O : Oracle) (c : Cfg Q A) (q yes no : Q)
    (hc : c.state = .inr q) (hrange : InRange c)
    (h : P.code q (c.work c.wh) (c.query c.qh) = .ask yes no) :
    (P.machine.step O)^[3] (P.encode c) = P.encode (P.step O c) := by
  change P.machine.step O (P.machine.step O (P.machine.step O (P.encode c))) = _
  rw [P.ask_first O c q yes no hc hrange h, P.ask_second, P.ask_third O c yes no _ hrange]
  simp only [Program.step, hc, h]


theorem Program.halted_step (P : Program Q A) (O : Oracle) (c : Cfg Q A)
    (b : Bool) (hc : c.state = .inl b) : P.machine.step O (P.encode c) = P.encode c := by
  have hs : (P.encode c).state = 1 ∨ (P.encode c).state = 2 := by
    change control c.state = 1 ∨ control c.state = 2
    rw [hc]
    cases b <;> simp [control]
  simp only [OTM.step, hs, ↓reduceIte]

theorem Program.step_simulation (P : Program Q A) (O : Oracle) (c : Cfg Q A)
    (hrange : InRange c) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ 3 ∧ (P.machine.step O)^[t] (P.encode c) = P.encode (P.step O c) := by
  cases hc : c.state with
  | inl b =>
    refine ⟨1, by omega, by omega, ?_⟩
    change P.machine.step O (P.encode c) = P.encode (P.step O c)
    rw [P.halted_step O c b hc]
    simp only [Program.step, hc]
  | inr q =>
    cases hh : P.code q (c.work c.wh) (c.query c.qh) with
    | move next a wm b qm =>
      exact ⟨1, by omega, by omega, P.move_step O c q next a b wm qm hc hh⟩
    | stop result a wm b qm =>
      exact ⟨1, by omega, by omega, P.stop_step O c q result a b wm qm hc hh⟩
    | halt b =>
      exact ⟨1, by omega, by omega, P.halt_step O c q b hc hrange hh⟩
    | ask yes no =>
      exact ⟨3, by omega, by omega, P.ask_steps O c q yes no hc hrange hh⟩

theorem Program.iterate_inRange (P : Program Q A) (O : Oracle) (c : Cfg Q A)
    (hrange : InRange c) (t : ℕ) : InRange ((P.step O)^[t] c) := by
  induction t with
  | zero => exact hrange
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact P.step_inRange O _ ih

theorem Program.iterate_simulation (P : Program Q A) (O : Oracle) (c : Cfg Q A)
    (hrange : InRange c) (t : ℕ) :
    ∃ u : ℕ, u ≤ 3 * t ∧ (P.machine.step O)^[u] (P.encode c) = P.encode ((P.step O)^[t] c) := by
  induction t with
  | zero => exact ⟨0, by omega, rfl⟩
  | succ t ih =>
    obtain ⟨u, hu, heq⟩ := ih
    obtain ⟨v, hvlo, hvhi, hv⟩ := P.step_simulation O ((P.step O)^[t] c)
      (P.iterate_inRange O c hrange t)
    refine ⟨v + u, by omega, ?_⟩
    rw [Function.iterate_add_apply, heq, hv, Function.iterate_succ_apply']

theorem Program.initial_inRange (P : Program Q A) (x : List Bool) : InRange (P.initial x) := by
  simp [InRange, Program.initial]

theorem Program.initial_step (P : Program Q A) (O : Oracle) (x : List Bool) :
    P.machine.step O (P.machine.init x) = P.encode (P.initial x) := by
  have hs : ¬ ((P.machine.init x).state = 1 ∨ (P.machine.init x).state = 2) := by
    simp (disch := omega) [OTM.init, Fin.ext_iff, Nat.mod_eq_of_lt]
  have hq : (P.machine.init x).state ≠ 3 := by
    simp (disch := omega) [OTM.init, Fin.ext_iff, Nat.mod_eq_of_lt]
  have hd : P.machine.δ (P.machine.init x).state
      ((P.machine.init x).work (P.machine.init x).wh)
      ((P.machine.init x).query (P.machine.init x).qh) =
      (state P.start, (P.machine.init x).work 0, 1, 0, 1) := by
    simp [OTM.init, Program.machine]
  rw [Precheck.normal_step _ _ _ hs hq _ _ _ _ _ hd]
  simp only [OTM.init, Program.encode, Program.initial, control]
  simp only [Function.update_eq_self]
  have hw : (fun i : ℤ => if 0 ≤ i ∧ i < x.length then
      symOf (Fintype.card A + Fintype.card (Cell A × Q × Q)) (x.getD i.toNat false) else 0) =
      (fun i : ℤ => sym (Q := Q) (if 0 ≤ i ∧ i < x.length then bit (x.getD i.toNat false) else none)) := by
    funext i
    split <;> simp only [sym_bit, sym_none]
  simp only [hw, sym_none]
  congr 1 <;> simp

theorem Program.run_simulation (P : Program Q A) (O : Oracle) (x : List Bool) (t : ℕ) :
    ∃ u : ℕ, u ≤ 3 * t + 1 ∧
      P.machine.runCfg O x u = P.encode ((P.step O)^[t] (P.initial x)) := by
  obtain ⟨u, hu, heq⟩ := P.iterate_simulation O (P.initial x) (P.initial_inRange x) t
  refine ⟨u + 1, by omega, ?_⟩
  rw [runCfg, Function.iterate_add_apply]
  change (P.machine.step O)^[u] (P.machine.step O (P.machine.init x)) = _
  rw [P.initial_step O x, heq]


theorem Program.halted_clock (P : Program Q A) (O : Oracle) (x : List Bool) (t : ℕ)
    (b : Bool) (hc : ((P.step O)^[t] (P.initial x)).state = .inl b) :
    P.machine.result O x (3 * t + 1) = some b ∧
    P.machine.output O x (3 * t + 1) =
      readWord ((P.step O)^[t] (P.initial x)).work ((P.step O)^[t] (P.initial x)).whi := by
  obtain ⟨u, hu, heq⟩ := P.run_simulation O x t
  have hresult : P.machine.result O x u = some b := by
    unfold OTM.result
    rw [heq]
    change (if control (((P.step O)^[t] (P.initial x)).state) = 1 then some true
      else if control (((P.step O)^[t] (P.initial x)).state) = 2 then some false else none) = some b
    rw [hc]
    cases b <;> simp (disch := omega) [control, Fin.ext_iff, Nat.mod_eq_of_lt]
  have hsome : (P.machine.result O x u).isSome := by rw [hresult]; rfl
  constructor
  · rw [P.machine.result_of_le O x u _ hsome hu, hresult]
  · rw [P.machine.output_of_le O x u _ hsome hu]
    unfold OTM.output
    rw [heq]
    exact readBits_sym _ _

/-- A finite symbolic program with a polynomial halting clock gives a concrete OTM
transducer. The same oracle is retained. -/
theorem Program.inFP {i : ℕ} (P : Program Q A) (O : Oracle) (clock : Polynomial ℕ)
    (f : List Bool → List Bool) (hO : {x | O x = true} ∈ StudentTeacher976.Adaptivity.Sigma i)
    (h : ∀ x, ∃ b : Bool,
      ((P.step O)^[clock.eval x.length] (P.initial x)).state = .inl b ∧
      readWord ((P.step O)^[clock.eval x.length] (P.initial x)).work
        ((P.step O)^[clock.eval x.length] (P.initial x)).whi = f x) :
    StudentTeacher976.Adaptivity.InFP i f := by
  refine ⟨O, P.machine, 3 * clock + 1, hO, ?_⟩
  intro x
  obtain ⟨b, hb, hout⟩ := h x
  have hh := P.halted_clock O x (clock.eval x.length) b hb
  have heval : (3 * clock + 1).eval x.length = 3 * clock.eval x.length + 1 := by simp
  rw [heval]
  constructor
  · rw [hh.1]; rfl
  · exact hh.2.trans hout


theorem Program.core_step (P : Program Q A) (hpure : P.Pure) (O : Oracle) (c : Cfg Q A) :
    (P.step O c).core = P.coreStep c.core := by
  cases hs : c.state with
  | inl b => simp only [Program.step, Cfg.core, hs, Program.coreStep]
  | inr q =>
    cases hh : P.code q (c.work c.wh) (c.query c.qh) with
    | halt b => simp only [Program.step, Cfg.core, hs, hh, Program.coreStep]
    | move next a wm b qm => simp only [Program.step, Cfg.core, hs, hh, Program.coreStep]
    | stop result a wm b qm => simp only [Program.step, Cfg.core, hs, hh, Program.coreStep]
    | ask yes no => exact False.elim (hpure q _ _ yes no hh)

theorem Program.core_iterate (P : Program Q A) (hpure : P.Pure) (O : Oracle)
    (c : Cfg Q A) (t : ℕ) :
    ((P.step O)^[t] c).core = P.coreStep^[t] c.core := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', P.core_step hpure, ih]

theorem Program.inFP_core {i : ℕ} (P : Program Q A) (hpure : P.Pure) (O : Oracle)
    (clock : Polynomial ℕ) (f : List Bool → List Bool)
    (hO : {x | O x = true} ∈ StudentTeacher976.Adaptivity.Sigma i)
    (h : ∀ x, ∃ b : Bool,
      (P.coreStep^[clock.eval x.length] (P.coreInitial x)).state = .inl b ∧
      (P.coreStep^[clock.eval x.length] (P.coreInitial x)).work = bitTape (f x)) :
    StudentTeacher976.Adaptivity.InFP i f := by
  apply P.inFP O clock f hO
  intro x
  obtain ⟨b, hb, hout⟩ := h x
  have hcore := P.core_iterate hpure O (P.initial x) (clock.eval x.length)
  change ((P.step O)^[clock.eval x.length] (P.initial x)).core =
    P.coreStep^[clock.eval x.length] (P.coreInitial x) at hcore
  have hstate : ((P.step O)^[clock.eval x.length] (P.initial x)).state = .inl b :=
    (congrArg Core.state hcore).trans hb
  refine ⟨b, hstate, ?_⟩
  obtain ⟨u, hu, heq⟩ := P.run_simulation O x (clock.eval x.length)
  have hw : (P.machine.runCfg O x u).work = (P.machine.init (f x)).work := by
    rw [heq]
    change (fun j => sym (((P.step O)^[clock.eval x.length] (P.initial x)).work j)) = _
    have hwork := (congrArg Core.work hcore).trans hout
    rw [show ((P.step O)^[clock.eval x.length] (P.initial x)).work = bitTape (f x) from hwork]
    funext j
    simp only [bitTape, OTM.init]
    split <;> simp only [sym_bit, sym_none]
  have hvalid := (valid_runCfg P.machine O x u).work
  rw [hw] at hvalid
  calc
    readWord _ _ = P.machine.output O x u := by
      unfold OTM.output
      rw [heq]
      exact (readBits_sym _ _).symm
    _ = readBits (P.machine.init (f x)).work (P.machine.init (f x)).whi := by
      unfold OTM.output
      dsimp only
      rw [hw]
      exact hvalid.readBits_eq (valid_init P.machine (f x)).work
    _ = f x := StudentTeacher976.Adaptivity.init_readBits _ _


theorem Program.core_stable (P : Program Q A) (c : Core Q A) (b : Bool)
    (hc : c.state = .inl b) (t : ℕ) : P.coreStep^[t] c = c := by
  have hstep : P.coreStep c = c := by simp only [Program.coreStep, hc]
  exact Function.iterate_fixed hstep t

theorem Program.inFP_core_bounded {i : ℕ} (P : Program Q A) (hpure : P.Pure) (O : Oracle)
    (clock : Polynomial ℕ) (f : List Bool → List Bool)
    (hO : {x | O x = true} ∈ StudentTeacher976.Adaptivity.Sigma i)
    (h : ∀ x, ∃ t ≤ clock.eval x.length, ∃ b : Bool,
      (P.coreStep^[t] (P.coreInitial x)).state = .inl b ∧
      (P.coreStep^[t] (P.coreInitial x)).work = bitTape (f x)) :
    StudentTeacher976.Adaptivity.InFP i f := by
  apply P.inFP_core hpure O clock f hO
  intro x
  obtain ⟨t, ht, b, hb, hout⟩ := h x
  have heq : P.coreStep^[clock.eval x.length] (P.coreInitial x) =
      P.coreStep^[t] (P.coreInitial x) := by
    rw [← Nat.add_sub_of_le ht, Nat.add_comm t, Function.iterate_add_apply]
    exact P.core_stable _ b hb _
  exact ⟨b, by rw [heq]; exact hb, by rw [heq]; exact hout⟩

end Encoding


end QAdvFew.PoQOracle.OTM.FiniteControl

theorem solution {Q A : Type} [Fintype Q] [Fintype A]
    (P : QAdvFew.PoQOracle.OTM.FiniteControl.Program Q A) :
    ∃ M : QAdvFew.PoQOracle.OTM, ∀ (O : QAdvFew.PoQOracle.Oracle)
      (x : List Bool) (t : ℕ) (b : Bool),
      (((P.step O)^[t]) (P.initial x)).state = Sum.inl b →
      M.result O x (3*t+1) = some b ∧
      M.output O x (3*t+1) =
        QAdvFew.PoQOracle.OTM.FiniteControl.readWord
          (((P.step O)^[t]) (P.initial x)).work (((P.step O)^[t]) (P.initial x)).whi := by
  exact ⟨P.machine, fun O x t b h => P.halted_clock O x t b h⟩

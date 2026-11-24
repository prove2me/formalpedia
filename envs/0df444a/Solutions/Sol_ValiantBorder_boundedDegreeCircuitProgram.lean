-- Prove2me | solution 1 for ValiantBorder.boundedDegreeCircuitProgram
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:06:11.591901+00:00
-- url     : https://prove2.me/submissions/09ece89b-43cc-4436-9f94-6fea7642ac7c

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_programWord
import Definitions.Def_VP_VNP_all_fields
/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field* (2026),
`anthropics/formal-math`, revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5.
The compiler, universal grid projection, and Laurent approximation arguments appear
in `Paper/Circuit.lean`, `Paper/LowDeg.lean` and `Paper/ApproxScales.lean`. Apache-2.0. -/

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Sum machines

Data are binary trees. A program is a formula of a small functional language; it is applied to a tree. A formula may
guess a bit, reject, multiply the weight of the run by a fixed constant `θ` of the ring `A` (named by a list of
bits), or by a constant that is *only named* (`mul`); the names are kept in the *bill* of the run. `run a b` applies
the program that is the value of `a` to the value of `b`. Every step costs 1.

`Ev θ F x l`: all runs of the formula `F` at the tree `x` stop, and `l` is the list of the accepting runs.
-/

namespace NS1
namespace Tree
@[simp] theorem hd_cons (a b : Tree) : (cons a b).hd = a := rfl
@[simp] theorem tl_cons (a b : Tree) : (cons a b).tl = b := rfl
@[simp] theorem hd_nil : nil.hd = nil := rfl
@[simp] theorem tl_nil : nil.tl = nil := rfl
@[simp] theorem len_num (k : ℕ) : (num k).len = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [num, len, ih]

theorem size_pos (x : Tree) : 0 < x.size := by cases x <;> simp [size]

@[simp] theorem path_ofBits (w : List Bool) : (ofBits w).path = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [ofBits, path, ih]
    cases b <;> simp [bit, one]

theorem bit_ne_nil {b : Bool} : bit b ≠ nil ↔ b = true := by cases b <;> simp [bit, one]

theorem size_ofBits (w : List Bool) : (ofBits w).size ≤ 4 * w.length + 1 := by
  induction w with
  | nil => simp [ofBits, size]
  | cons b w ih =>
    have : (bit b).size ≤ 3 := by cases b <;> simp [bit, one, size]
    simp only [ofBits, size, List.length_cons]
    omega

end Tree

open _root_.NS1.Tree

namespace Fm
theorem ofTree_code (F : Fm) : ofTree F.code = F := by
  induction F with
  | quote c => rw [code, ofTree]; rfl
  | id => rw [code, ofTree]; rfl
  | hd a ih => rw [code, ofTree]; simp [ih]
  | tl a ih => rw [code, ofTree]; simp [ih]
  | cons a b iha ihb => rw [code, ofTree]; simp [iha, ihb]
  | ite a b c iha ihb ihc => rw [code, ofTree]; simp [iha, ihb, ihc]
  | run a b iha ihb => rw [code, ofTree]; simp [iha, ihb]
  | guess => rw [code, ofTree]; simp
  | fail => rw [code, ofTree]; simp
  | theta a ih => rw [code, ofTree]; simp [ih]
  | mul a ih => rw [code, ofTree]; simp [ih]

end Fm

variable {A : Type} [CommRing A]

variable {θ : List Bool → A}
/-- The list of the accepting runs is determined. -/
theorem Ev.unique {F : Fm} {x : Tree} {l l' : List (Run A)} (h : Ev θ F x l) (h' : Ev θ F x l') : l = l' := by
  induction h generalizing l' with
  | quote c x => cases h'; rfl
  | id x => cases h'; rfl
  | hd _ ih => cases h' with | hd h => rw [ih h]
  | tl _ ih => cases h' with | tl h => rw [ih h]
  | cons _ _ iha ihb => cases h' with | cons ha hb => rw [iha ha, ihb hb]
  | ite _ _ _ iha ihb ihc =>
    cases h' with
    | ite ha hb hc =>
      obtain rfl := iha ha
      refine List.flatMap_congr fun r hr => ?_
      by_cases h : r.out = .nil
      · rw [ihc r hr h (hc r hr h)]
      · rw [ihb r hr h (hb r hr h)]
  | run _ _ _ iha ihb ih =>
    cases h' with
    | run ha hb h =>
      obtain rfl := iha ha
      obtain rfl := ihb hb
      refine List.flatMap_congr fun r hr => List.flatMap_congr fun s hs => ?_
      rw [ih r hr s hs (h r hr s hs)]
  | guess x => cases h'; rfl
  | fail x => cases h'; rfl
  | theta _ ih => cases h' with | theta h => rw [ih h]
  | mul _ ih => cases h' with | mul h => rw [ih h]

theorem Hl.ev {F : Fm} {x : Tree} (h : Hl θ F x) : Ev θ F x (evl θ F x) := by
  rw [evl, dif_pos h]
  exact h.choose_spec

theorem Ev.hl {F : Fm} {x : Tree} {l : List (Run A)} (h : Ev θ F x l) : Hl θ F x := ⟨l, h⟩

theorem Ev.evl {F : Fm} {x : Tree} {l : List (Run A)} (h : Ev θ F x l) : evl θ F x = l := h.hl.ev.unique h

theorem Ev.run' {a b : Fm} {x : Tree} {la lb : List (Run A)} (ha : Ev θ a x la) (hb : Ev θ b x lb)
    (h : ∀ r ∈ la, ∀ s ∈ lb, Hl θ (Fm.ofTree r.out) s.out) : Ev θ (.run a b) x
      (la.flatMap fun r => lb.flatMap fun s => (NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
        ((r.seq s).seq t).tick t.out) :=
  .run ha hb fun r hr s hs => (h r hr s hs).ev

/-- A run without guesses and weights. -/
def Dt (θ : List Bool → A) (F : Fm) (x o : Tree) (k : ℕ) : Prop := Ev θ F x [.det k o]

theorem Dt.quote (c x : Tree) : Dt θ (.quote c) x c 1 := Ev.quote c x

theorem Dt.id (x : Tree) : Dt θ .id x x 1 := Ev.id x

theorem Dt.hd {a : Fm} {x o : Tree} {k : ℕ} (h : Dt θ a x o k) : Dt θ (.hd a) x o.hd (k + 1) := Ev.hd h

theorem Dt.tl {a : Fm} {x o : Tree} {k : ℕ} (h : Dt θ a x o k) : Dt θ (.tl a) x o.tl (k + 1) := Ev.tl h

theorem Dt.cons {a b : Fm} {x o p : Tree} {k j : ℕ} (ha : Dt θ a x o k) (hb : Dt θ b x p j) :
    Dt θ (.cons a b) x (.cons o p) (k + j + 1) := by
  have := Ev.cons ha hb
  simpa [Dt, Run.det, Run.seq, Run.tick] using this

/-- Weights and costs of runs after a step without guesses. -/
def Run.delay (k : ℕ) (r : Run A) : Run A := ⟨k + r.cost, r.th, r.bill, r.out⟩

theorem Ev.ite_true {a b c : Fm} {x o : Tree} {k : ℕ} {l : List (Run A)} (ha : Dt θ a x o k) (ho : o ≠ .nil)
    (hb : Ev θ b x l) : Ev θ (.ite a b c) x (l.map (Run.delay (k + 1))) := by
  have := Ev.ite (c := c) (L := fun _ => l) ha (fun r _ _ => hb) (fun r hr h => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact absurd h ho)
  convert this using 1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine List.map_congr_left fun r _ => ?_
  simp [Run.delay, Run.det, Run.seq, Run.tick]
  omega

theorem Ev.ite_false {a b c : Fm} {x : Tree} {k : ℕ} {l : List (Run A)} (ha : Dt θ a x .nil k)
    (hc : Ev θ c x l) : Ev θ (.ite a b c) x (l.map (Run.delay (k + 1))) := by
  have := Ev.ite (b := b) (L := fun _ => l) ha (fun r hr h => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact absurd rfl h) (fun r _ _ => hc)
  convert this using 1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine List.map_congr_left fun r _ => ?_
  simp [Run.delay, Run.det, Run.seq, Run.tick]
  omega

theorem Ev.run_det {a b : Fm} {x p d : Tree} {k j : ℕ} {l : List (Run A)} (ha : Dt θ a x p k) (hb : Dt θ b x d j)
    (h : Ev θ (Fm.ofTree p) d l) : Ev θ (.run a b) x (l.map (Run.delay (k + j + 1))) := by
  have := Ev.run (L := fun _ _ => l) ha hb (fun r hr s hs => by
    simp only [List.mem_singleton] at hr hs
    subst hr hs
    exact h)
  convert this using 1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine List.map_congr_left fun r _ => ?_
  simp [Run.delay, Run.det, Run.seq, Run.tick]
  omega

/-- `let`: apply `body` to the value of `e`. -/
def lett (e body : Fm) : Fm := .run (.quote body.code) e

theorem Ev.lett {e body : Fm} {x : Tree} {le : List (Run A)} (he : Ev θ e x le)
    (h : ∀ s ∈ le, Hl θ body s.out) : Ev θ (lett e body) x
      (le.flatMap fun s => (NS1.evl θ body s.out).map fun t => ⟨s.cost + t.cost + 2, s.th * t.th, s.bill ++ t.bill, t.out⟩) := by
  have := Ev.run' (Dt.quote (θ := θ) body.code x) he (fun r hr s hs => by
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [Run.det, Fm.ofTree_code]
    exact h s hs)
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
  refine Eq.mp ?_ this
  unfold NS1.lett
  congr 1
  refine List.flatMap_congr fun s _ => ?_
  simp only [Run.det, Fm.ofTree_code]
  refine List.map_congr_left fun r _ => ?_
  simp only [Run.seq, Run.tick, one_mul, List.nil_append, Run.mk.injEq, and_true]
  omega

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Budgets

A budget is a trie with numbers (in binary, lowest digit first) at its leaves; the leaves are named by the paths.
-/

namespace NS1

/-- Budgets. -/
inductive Bt where
  /-- no name -/
  | none
  /-- a name with a number -/
  | leaf (w : List Bool)
  /-- names that begin with 0, names that begin with 1 -/
  | node (l r : Bt)

/-- Subtract 1. -/
def decw : List Bool → Option (List Bool)
  | [] => Option.none
  | true :: w => some (false :: w)
  | false :: w => (decw w).map (true :: ·)

theorem length_decw {w w' : List Bool} (h : decw w = some w') : w'.length = w.length := by
  induction w generalizing w' with
  | nil => simp [decw] at h
  | cons b w ih =>
    cases b with
    | true =>
      simp only [decw, Option.some.injEq] at h
      subst h
      rfl
    | false =>
      simp only [decw, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      simp [ih hv]

namespace Bt

/-- Subtract 1 at a name. -/
def dec : List Bool → Bt → Option Bt
  | _, none => Option.none
  | [], leaf w => (decw w).map leaf
  | _ :: _, leaf _ => Option.none
  | [], node _ _ => Option.none
  | true :: p, node l r => (dec p r).map (node l)
  | false :: p, node l r => (dec p l).map fun l' => node l' r

/-- Subtract 1 at all names of a bill. -/
def decAll : List (List Bool) → Bt → Option Bt
  | [], t => some t
  | p :: b, t => (dec p t).bind (decAll b)

/-- All numbers are 0. -/
def zero : Bt → Bool
  | none => true
  | leaf w => w.all (! ·)
  | node l r => l.zero && r.zero

/-- A bound for the time to subtract 1. -/
def ht : Bt → ℕ
  | none => 0
  | leaf w => w.length + 1
  | node l r => max l.ht r.ht + 1

/-- The number of nodes and digits. -/
def nds : Bt → ℕ
  | none => 1
  | leaf w => w.length + 1
  | node l r => l.nds + r.nds + 1

/-- Budgets as trees. -/
def enc : Bt → Tree
  | none => .nil
  | leaf w => .cons .nil (.ofBits w)
  | node l r => .cons (.cons l.enc r.enc) .nil

theorem size_enc (t : Bt) : t.enc.size ≤ 4 * t.nds := by
  induction t with
  | none => simp [enc, Tree.size, nds]
  | leaf w =>
    have := Tree.size_ofBits w
    simp only [enc, Tree.size, nds]
    omega
  | node l r ihl ihr =>
    simp only [enc, Tree.size, nds]
    omega

theorem ht_dec {p : List Bool} {t t' : Bt} (h : dec p t = some t') : t'.ht = t.ht := by
  induction t generalizing p t' with
  | none => simp [dec] at h
  | leaf w =>
    cases p with
    | nil =>
      simp only [dec, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      simp [ht, length_decw hv]
    | cons b p => simp [dec] at h
  | node l r ihl ihr =>
    cases p with
    | nil => simp [dec] at h
    | cons b p =>
      cases b with
      | true =>
        simp only [dec, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        simp [ht, ihr hv]
      | false =>
        simp only [dec, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        simp [ht, ihl hv]

theorem nds_dec {p : List Bool} {t t' : Bt} (h : dec p t = some t') : t'.nds = t.nds := by
  induction t generalizing p t' with
  | none => simp [dec] at h
  | leaf w =>
    cases p with
    | nil =>
      simp only [dec, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      simp [nds, length_decw hv]
    | cons b p => simp [dec] at h
  | node l r ihl ihr =>
    cases p with
    | nil => simp [dec] at h
    | cons b p =>
      cases b with
      | true =>
        simp only [dec, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        simp [nds, ihr hv]
      | false =>
        simp only [dec, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        simp [nds, ihl hv]

theorem decAll_append (b b' : List (List Bool)) (t : Bt) : decAll (b ++ b') t = (decAll b t).bind (decAll b') := by
  induction b generalizing t with
  | nil => rfl
  | cons p b ih =>
    simp only [List.cons_append, decAll, Option.bind_assoc]
    congr 1
    funext t
    exact ih t

theorem ht_decAll {b : List (List Bool)} {t t' : Bt} (h : decAll b t = some t') : t'.ht = t.ht := by
  induction b generalizing t with
  | nil =>
    simp only [decAll, Option.some.injEq] at h
    rw [h]
  | cons p b ih =>
    simp only [decAll, Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, h⟩ := h
    rw [ih h, ht_dec hs]

theorem nds_decAll {b : List (List Bool)} {t t' : Bt} (h : decAll b t = some t') : t'.nds = t.nds := by
  induction b generalizing t with
  | nil =>
    simp only [decAll, Option.some.injEq] at h
    rw [h]
  | cons p b ih =>
    simp only [decAll, Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, h⟩ := h
    rw [ih h, nds_dec hs]

end Bt

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# An interpreter that counts the names of constants

`IF` is a formula of the language that evaluates formulas; instead of multiplying by a named constant it subtracts 1
from a budget. `WF` also checks that in the end the budgets are used up. These formulas are plain: they use no
named constants.
-/

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem Dt.ite_true {a b c : Fm} {x o p : Tree} {k j : ℕ} (ha : Dt θ a x o k) (ho : o ≠ .nil) (hb : Dt θ b x p j) :
    Dt θ (.ite a b c) x p (k + 1 + j) := Ev.ite_true (c := c) ha ho hb

theorem Dt.ite_false {a b c : Fm} {x p : Tree} {k j : ℕ} (ha : Dt θ a x .nil k) (hc : Dt θ c x p j) :
    Dt θ (.ite a b c) x p (k + 1 + j) := Ev.ite_false (b := b) ha hc

theorem Dt.run {a b : Fm} {x p d o : Tree} {k j i : ℕ} (ha : Dt θ a x p k) (hb : Dt θ b x d j)
    (h : Dt θ (Fm.ofTree p) d o i) : Dt θ (.run a b) x o (k + j + 1 + i) := Ev.run_det ha hb h

theorem Ev.ite_true_nil {a b c : Fm} {x o : Tree} {k : ℕ} (ha : Dt θ a x o k) (ho : o ≠ .nil)
    (hb : Ev θ b x []) : Ev θ (.ite a b c) x [] := Ev.ite_true (c := c) ha ho hb

theorem Ev.ite_false_nil {a b c : Fm} {x : Tree} {k : ℕ} (ha : Dt θ a x .nil k)
    (hc : Ev θ c x []) : Ev θ (.ite a b c) x [] := Ev.ite_false (b := b) ha hc

theorem Ev.run_nil {a b : Fm} {x p d : Tree} {k j : ℕ} (ha : Dt θ a x p k) (hb : Dt θ b x d j)
    (h : Ev θ (Fm.ofTree p) d []) : Ev θ (.run a b) x [] := Ev.run_det ha hb h

theorem Ev.cons_nil_left {a b : Fm} {x : Tree} {l : List (Run A)} (ha : Ev θ a x []) (hb : Ev θ b x l) :
    Ev θ (.cons a b) x [] := Ev.cons ha hb

theorem Ev.cons_nil_right {a b : Fm} {x : Tree} {l : List (Run A)} (ha : Ev θ a x l) (hb : Ev θ b x []) :
    Ev θ (.cons a b) x [] := by
  have := Ev.cons ha hb
  have e : (l.flatMap fun r => ([] : List (Run A)).map fun s => (r.seq s).tick (.cons r.out s.out)) = [] :=
    List.flatMap_eq_nil_iff.2 fun _ _ => rfl
  rw [e] at this
  exact this

section Programs

/-- Subtract 1 from a number; the argument is (this program, the number). -/
def DW : Fm := .ite (.tl .id)
  (.ite (.hd (.tl .id)) (.cons (.quote .nil) (.tl (.tl .id)))
    (.cons (.quote one) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id)))))) .fail

theorem DW_some {w w' : List Bool} (h : decw w = some w') :
    ∃ k ≤ 20 * w.length, Dt θ DW (.cons DW.code (ofBits w)) (ofBits w') k := by
  induction w generalizing w' with
  | nil => simp [decw] at h
  | cons b w ih =>
    cases b with
    | true =>
      simp only [decw, Option.some.injEq] at h
      subst h
      refine ⟨_, ?_, Dt.ite_true (.tl (.id _)) (by simp [ofBits]) (Dt.ite_true (.hd (.tl (.id _)))
        (by simp [ofBits, bit, one]) (.cons (.quote _ _) (.tl (.tl (.id _)))))⟩
      simp only [List.length_cons]
      omega
    | false =>
      simp only [decw, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      obtain ⟨k, hk, hd⟩ := ih hv
      have hd' : Dt θ (Fm.ofTree DW.code) (.cons DW.code (ofBits w)) (ofBits v) k := by rwa [Fm.ofTree_code]
      refine ⟨_, ?_, Dt.ite_true (.tl (.id _)) (by simp [ofBits]) (Dt.ite_false (.hd (.tl (.id _)))
        (.cons (.quote _ _) (.run (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.tl (.id _)))) hd')))⟩
      simp only [List.length_cons]
      omega

theorem DW_none {w : List Bool} (h : decw w = none) : Ev θ DW (.cons DW.code (ofBits w)) [] := by
  induction w with
  | nil => exact Ev.ite_false_nil (.tl (.id _)) (.fail _)
  | cons b w ih =>
    cases b with
    | true => simp [decw] at h
    | false =>
      simp only [decw, Option.map_eq_none_iff] at h
      refine Ev.ite_true_nil (.tl (.id _)) (by simp [ofBits]) (Ev.ite_false_nil (.hd (.tl (.id _)))
        (Ev.cons_nil_right (.quote _ _) (Ev.run_nil (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.tl (.id _)))) ?_)))
      simp only [hd_cons, Fm.ofTree_code]
      exact ih h

/-- Subtract 1 in a budget; the argument is (this program, (the name, the budget)). -/
def DC : Fm :=
  .ite (.tl (.tl .id))
    (.ite (.hd (.tl (.tl .id)))
      (.ite (.hd (.tl .id))
        (.ite (.hd (.hd (.tl .id)))
          (.cons (.cons (.hd (.hd (.tl (.tl .id)))) (.run (.hd .id) (.cons (.hd .id)
            (.cons (.tl (.hd (.tl .id))) (.tl (.hd (.tl (.tl .id)))))))) (.quote .nil))
          (.cons (.cons (.run (.hd .id) (.cons (.hd .id)
            (.cons (.tl (.hd (.tl .id))) (.hd (.hd (.tl (.tl .id))))))) (.tl (.hd (.tl (.tl .id))))) (.quote .nil)))
        .fail)
      (.ite (.hd (.tl .id)) .fail
        (.cons (.quote .nil) (.run (.quote DW.code) (.cons (.quote DW.code) (.tl (.tl (.tl .id))))))))
    .fail

theorem DC_some {t t' : Bt} {x : Tree} (h : Bt.dec x.path t = some t') :
    ∃ k ≤ 60 * t.ht, Dt θ DC (.cons DC.code (.cons x t.enc)) t'.enc k := by
  induction t generalizing x t' with
  | none => simp [Bt.dec] at h
  | leaf w =>
    cases x with
    | cons a b => simp [path, Bt.dec] at h
    | nil =>
      simp only [path, Bt.dec, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      obtain ⟨k, hk, hd⟩ := DW_some (θ := θ) hv
      have hd' : Dt θ (Fm.ofTree DW.code) (.cons DW.code (ofBits w)) (ofBits v) k := by rwa [Fm.ofTree_code]
      refine ⟨_, ?_, Dt.ite_true (.tl (.tl (.id _))) (by simp [Bt.enc]) (Dt.ite_false (.hd (.tl (.tl (.id _))))
        (Dt.ite_false (.hd (.tl (.id _))) (.cons (.quote _ _) (.run (.quote _ _) (.cons (.quote _ _)
          (.tl (.tl (.tl (.id _))))) hd'))))⟩
      simp only [Bt.ht]
      omega
  | node l r ihl ihr =>
    cases x with
    | nil => simp [path, Bt.dec] at h
    | cons a b =>
      by_cases ha : a = .nil
      · subst ha
        simp only [path, ne_eq, not_true_eq_false, decide_false, Bt.dec, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        obtain ⟨k, hk, hd⟩ := ihl hv
        have hd' : Dt θ (Fm.ofTree DC.code) (.cons DC.code (.cons b l.enc)) v.enc k := by rwa [Fm.ofTree_code]
        refine ⟨_, ?_, Dt.ite_true (.tl (.tl (.id _))) (by simp [Bt.enc]) (Dt.ite_true (.hd (.tl (.tl (.id _))))
          (by simp [Bt.enc]) (Dt.ite_true (.hd (.tl (.id _))) (by simp) (Dt.ite_false (.hd (.hd (.tl (.id _))))
            (.cons (.cons (.run (.hd (.id _)) (.cons (.hd (.id _)) (.cons (.tl (.hd (.tl (.id _))))
              (.hd (.hd (.tl (.tl (.id _))))))) hd') (.tl (.hd (.tl (.tl (.id _)))))) (.quote _ _)))))⟩
        simp only [Bt.ht]
        omega
      · simp only [path, ne_eq, ha, not_false_eq_true, decide_true, Bt.dec, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        obtain ⟨k, hk, hd⟩ := ihr hv
        have hd' : Dt θ (Fm.ofTree DC.code) (.cons DC.code (.cons b r.enc)) v.enc k := by rwa [Fm.ofTree_code]
        refine ⟨_, ?_, Dt.ite_true (.tl (.tl (.id _))) (by simp [Bt.enc]) (Dt.ite_true (.hd (.tl (.tl (.id _))))
          (by simp [Bt.enc]) (Dt.ite_true (.hd (.tl (.id _))) (by simp) (Dt.ite_true (.hd (.hd (.tl (.id _))))
            (by simpa using ha) (.cons (.cons (.hd (.hd (.tl (.tl (.id _))))) (.run (.hd (.id _)) (.cons (.hd (.id _))
              (.cons (.tl (.hd (.tl (.id _)))) (.tl (.hd (.tl (.tl (.id _))))))) hd')) (.quote _ _)))))⟩
        simp only [Bt.ht]
        omega

theorem DC_none {t : Bt} {x : Tree} (h : Bt.dec x.path t = none) : Ev θ DC (.cons DC.code (.cons x t.enc)) [] := by
  induction t generalizing x with
  | none => exact Ev.ite_false_nil (.tl (.tl (.id _))) (.fail _)
  | leaf w =>
    refine Ev.ite_true_nil (.tl (.tl (.id _))) (by simp [Bt.enc]) (Ev.ite_false_nil (.hd (.tl (.tl (.id _)))) ?_)
    cases x with
    | cons a b => exact Ev.ite_true_nil (.hd (.tl (.id _))) (by simp) (.fail _)
    | nil =>
      simp only [path, Bt.dec, Option.map_eq_none_iff] at h
      refine Ev.ite_false_nil (.hd (.tl (.id _))) (Ev.cons_nil_right (.quote _ _) (Ev.run_nil (.quote _ _)
        (.cons (.quote _ _) (.tl (.tl (.tl (.id _))))) ?_))
      simp only [Fm.ofTree_code]
      exact DW_none h
  | node l r ihl ihr =>
    refine Ev.ite_true_nil (.tl (.tl (.id _))) (by simp [Bt.enc]) (Ev.ite_true_nil (.hd (.tl (.tl (.id _))))
      (by simp [Bt.enc]) ?_)
    cases x with
    | nil => exact Ev.ite_false_nil (.hd (.tl (.id _))) (.fail _)
    | cons a b =>
      refine Ev.ite_true_nil (.hd (.tl (.id _))) (by simp) ?_
      by_cases ha : a = .nil
      · subst ha
        simp only [path, ne_eq, not_true_eq_false, decide_false, Bt.dec, Option.map_eq_none_iff] at h
        refine Ev.ite_false_nil (.hd (.hd (.tl (.id _)))) (Ev.cons_nil_left (Ev.cons_nil_left (Ev.run_nil (.hd (.id _))
          (.cons (.hd (.id _)) (.cons (.tl (.hd (.tl (.id _)))) (.hd (.hd (.tl (.tl (.id _))))))) ?_)
          (Dt.tl (.hd (.tl (.tl (.id _)))))) (Dt.quote _ _))
        simp only [hd_cons, Fm.ofTree_code]
        exact ihl h
      · simp only [path, ne_eq, ha, not_false_eq_true, decide_true, Bt.dec, Option.map_eq_none_iff] at h
        refine Ev.ite_true_nil (.hd (.hd (.tl (.id _)))) (by simpa using ha) (Ev.cons_nil_left (Ev.cons_nil_right
          (Dt.hd (.hd (.tl (.tl (.id _))))) (Ev.run_nil (.hd (.id _)) (.cons (.hd (.id _))
          (.cons (.tl (.hd (.tl (.id _)))) (.tl (.hd (.tl (.tl (.id _))))))) ?_)) (Dt.quote _ _))
        simp only [hd_cons, Fm.ofTree_code]
        exact ihr h

/-- Check that a number is 0. -/
def AW : Fm := .ite (.tl .id)
  (.ite (.hd (.tl .id)) .fail (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) (.quote .nil)

theorem AW_ev (w : List Bool) : ∃ k ≤ 20 * w.length + 5, ∃ o, Ev θ AW (.cons AW.code (ofBits w))
    (if w.all (! ·) then [.det k o] else []) := by
  induction w with
  | nil => exact ⟨_, by norm_num, _, Dt.ite_false (.tl (.id _)) (.quote _ _)⟩
  | cons b w ih =>
    obtain ⟨k, hk, o, ih⟩ := ih
    cases b with
    | true =>
      refine ⟨0, Nat.zero_le _, .nil, ?_⟩
      simp only [List.all_cons, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
      exact Ev.ite_true_nil (.tl (.id _)) (by simp [ofBits]) (Ev.ite_true_nil (.hd (.tl (.id _)))
        (by simp [ofBits, bit, one]) (.fail _))
    | false =>
      simp only [List.all_cons, Bool.not_false, Bool.true_and]
      by_cases h : w.all (! ·)
      · simp only [h, if_true] at ih ⊢
        have ih' : Dt θ (Fm.ofTree AW.code) (.cons AW.code (ofBits w)) o k := by rwa [Fm.ofTree_code]
        refine ⟨_, ?_, o, Dt.ite_true (.tl (.id _)) (by simp [ofBits]) (Dt.ite_false (.hd (.tl (.id _)))
          (.run (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.tl (.id _)))) ih'))⟩
        simp only [List.length_cons]
        omega
      · simp only [h] at ih ⊢
        refine ⟨0, Nat.zero_le _, .nil, ?_⟩
        refine Ev.ite_true_nil (.tl (.id _)) (by simp [ofBits]) (Ev.ite_false_nil (.hd (.tl (.id _)))
          (Ev.run_nil (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.tl (.id _)))) ?_))
        simp only [hd_cons, Fm.ofTree_code]
        exact ih

/-- Check that all numbers of a budget are 0. -/
def AZ : Fm := .ite (.tl .id)
  (.ite (.hd (.tl .id))
    (.cons (.run (.hd .id) (.cons (.hd .id) (.hd (.hd (.tl .id)))))
      (.run (.hd .id) (.cons (.hd .id) (.tl (.hd (.tl .id))))))
    (.run (.quote AW.code) (.cons (.quote AW.code) (.tl (.tl .id)))))
  (.quote .nil)

theorem AZ_ev (t : Bt) : ∃ k ≤ 40 * t.nds, ∃ o, Ev θ AZ (.cons AZ.code t.enc) (if t.zero then [.det k o] else []) := by
  induction t with
  | none => exact ⟨_, by simp [Bt.nds], _, Dt.ite_false (.tl (.id _)) (.quote _ _)⟩
  | leaf w =>
    obtain ⟨k, hk, o, h⟩ := AW_ev (θ := θ) w
    simp only [Bt.zero]
    by_cases hz : w.all (! ·)
    · simp only [hz, if_true] at h ⊢
      have h' : Dt θ (Fm.ofTree AW.code) (.cons AW.code (ofBits w)) o k := by rwa [Fm.ofTree_code]
      refine ⟨_, ?_, o, Dt.ite_true (.tl (.id _)) (by simp [Bt.enc]) (Dt.ite_false (.hd (.tl (.id _)))
        (.run (.quote _ _) (.cons (.quote _ _) (.tl (.tl (.id _)))) h'))⟩
      simp only [Bt.nds]
      omega
    · simp only [hz] at h ⊢
      refine ⟨0, Nat.zero_le _, .nil, ?_⟩
      refine Ev.ite_true_nil (.tl (.id _)) (by simp [Bt.enc]) (Ev.ite_false_nil (.hd (.tl (.id _)))
        (Ev.run_nil (.quote _ _) (.cons (.quote _ _) (.tl (.tl (.id _)))) ?_))
      simp only [Fm.ofTree_code]
      exact h
  | node l r ihl ihr =>
    obtain ⟨kl, hkl, ol, hl⟩ := ihl
    obtain ⟨kr, hkr, or, hr⟩ := ihr
    have el : Ev θ (.run (.hd .id) (.cons (.hd .id) (.hd (.hd (.tl .id))))) (.cons AZ.code (Bt.node l r).enc)
        ((if l.zero then [.det kl ol] else []).map (Run.delay 10)) := by
      refine Ev.run_det (k := 2) (j := 7) (.hd (.id _)) (.cons (.hd (.id _)) (.hd (.hd (.tl (.id _))))) ?_
      simp only [hd_cons, Fm.ofTree_code]
      exact hl
    have er : Ev θ (.run (.hd .id) (.cons (.hd .id) (.tl (.hd (.tl .id))))) (.cons AZ.code (Bt.node l r).enc)
        ((if r.zero then [.det kr or] else []).map (Run.delay 10)) := by
      refine Ev.run_det (k := 2) (j := 7) (.hd (.id _)) (.cons (.hd (.id _)) (.tl (.hd (.tl (.id _))))) ?_
      simp only [hd_cons, Fm.ofTree_code]
      exact hr
    simp only [Bt.zero]
    by_cases hzl : l.zero
    · by_cases hzr : r.zero
      · simp only [hzl, hzr, if_true, Bool.and_self] at el er ⊢
        refine ⟨_, ?_, _, Dt.ite_true (.tl (.id _)) (by simp [Bt.enc]) (Dt.ite_true (.hd (.tl (.id _)))
          (by simp [Bt.enc]) (Dt.cons (k := 10 + kl) (j := 10 + kr) el er))⟩
        simp only [Bt.nds]
        omega
      · simp only [hzl, hzr, if_true, if_false, Bool.and_false, Bool.false_eq_true, List.map_nil] at el er ⊢
        exact ⟨0, Nat.zero_le _, .nil, Ev.ite_true_nil (.tl (.id _)) (by simp [Bt.enc])
          (Ev.ite_true_nil (.hd (.tl (.id _))) (by simp [Bt.enc]) (Ev.cons_nil_right el er))⟩
    · simp only [hzl, if_false, Bool.false_and, Bool.false_eq_true, List.map_nil] at el er ⊢
      exact ⟨0, Nat.zero_le _, .nil, Ev.ite_true_nil (.tl (.id _)) (by simp [Bt.enc])
        (Ev.ite_true_nil (.hd (.tl (.id _))) (by simp [Bt.enc]) (Ev.cons_nil_left el er))⟩

end Programs

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The interpreter

`IF` at `(IF, (f, (x, t)))` simulates the formula `f` at `x` with the budgets `t`; its value is the value of the run
and the budgets that are left.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

section Rel

variable {α β γ δ : Type*}

theorem forall₂_flatMap {R : α → β → Prop} {S : γ → δ → Prop} {l : List α} {l' : List β} {f : α → List γ}
    {g : β → List δ} (h : List.Forall₂ R l l') (hf : ∀ a ∈ l, ∀ b ∈ l', R a b → List.Forall₂ S (f a) (g b)) :
    List.Forall₂ S (l.flatMap f) (l'.flatMap g) := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    refine List.rel_append (hf _ List.mem_cons_self _ List.mem_cons_self hab) (ih fun a ha b hb =>
      hf a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))

theorem forall₂_exists {R : α → β → Prop} {l : List α} {l' : List β} (h : List.Forall₂ R l l') {a : α} (ha : a ∈ l) :
    ∃ b ∈ l', R a b := by
  induction h with
  | nil => simp at ha
  | cons hab _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

/-- `let`, for lists that correspond to other lists. -/
theorem lett_rel {e body : Fm} {x : Tree} {le : List (Run A)} (he : Ev θ e x le) {Q : List β}
    {R : Run A → β → Prop} (hR : List.Forall₂ R le Q) {Q2 : β → List γ} {R2 : Run A → γ → Prop}
    (h : ∀ s ∈ le, ∀ b ∈ Q, R s b → ∃ l2, Ev θ body s.out l2 ∧
      List.Forall₂ (fun t c => R2 ⟨s.cost + t.cost + 2, s.th * t.th, s.bill ++ t.bill, t.out⟩ c) l2 (Q2 b)) :
    ∃ l, Ev θ (lett e body) x l ∧ List.Forall₂ R2 l (Q.flatMap Q2) := by
  refine ⟨_, Ev.lett he fun s hs => ?_, forall₂_flatMap hR fun s hs b hb hsb => ?_⟩
  · obtain ⟨b, hb, hsb⟩ := forall₂_exists hR hs
    obtain ⟨l2, h2, -⟩ := h s hs b hb hsb
    exact h2.hl
  · obtain ⟨l2, h2, h3⟩ := h s hs b hb hsb
    rw [h2.evl, List.forall₂_map_left_iff]
    exact h3

end Rel

section Cases

/-- Choose by the length of the value of `b`. -/
def selF : List Fm → Fm → Fm
  | [], _ => .fail
  | c :: cs, b => .ite b (selF cs (.tl b)) c

theorem selF_ev {cs : List Fm} {b : Fm} {x o : Tree} {k : ℕ} (hb : Dt θ b x o k) {l : List (Run A)}
    (h : ∀ c, cs[o.len]? = some c → Ev θ c x l) (h0 : cs.length ≤ o.len → l = []) :
    ∃ k' ≤ cs.length * (k + cs.length + 1), Ev θ (selF cs b) x (l.map (Run.delay k')) := by
  induction cs generalizing b o k with
  | nil =>
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [h0 (Nat.zero_le _)]
    exact .fail x
  | cons c cs ih =>
    cases o with
    | nil =>
      refine ⟨k + 1, ?_, Ev.ite_false hb (h c rfl)⟩
      simp only [List.length_cons]
      nlinarith
    | cons a o =>
      obtain ⟨k', hk', h'⟩ := ih (b := .tl b) (o := o) hb.tl (fun c hc => h c (by simpa [len] using hc))
        (fun hl => h0 (by simp only [List.length_cons, len]; omega))
      refine ⟨k + 1 + k', ?_, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · have := Ev.ite_true (c := c) hb (by simp) h'
        rw [List.map_map] at this
        refine Eq.mp ?_ this
        congr 1
        refine List.map_congr_left fun r _ => ?_
        simp only [Run.delay, Function.comp_apply, Run.mk.injEq, and_true]
        omega

end Cases

section Code

/-- The formula in the environment. -/
def fF (b : Fm) : Fm := .hd (.tl b)
/-- The argument in the environment. -/
def fX (b : Fm) : Fm := .hd (.tl (.tl b))
/-- The budgets in the environment. -/
def fS (b : Fm) : Fm := .tl (.tl (.tl b))
/-- The opcode. -/
def fO (b : Fm) : Fm := .hd (fF b)
/-- The arguments of the formula. -/
def fA (b : Fm) : Fm := .tl (fF b)
/-- Recursive call. -/
def rec' (b a x s : Fm) : Fm := .run (.hd b) (.cons (.hd b) (.cons a (.cons x s)))

/-- First call, with the environment kept. -/
def call1 : Fm := .cons .id (rec' .id (.hd (fA .id)) (fX .id) (fS .id))

/-- Second call, with everything kept. -/
def call2 : Fm := .cons .id (rec' (.hd .id) (.tl (fA (.hd .id))) (fX (.hd .id)) (.tl (.tl .id)))

/-- The cases of the interpreter. -/
def caseL : List Fm := [
  -- quote
  .cons (fA .id) (fS .id),
  -- id
  .cons (fX .id) (fS .id),
  -- hd
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.hd (.hd .id)) (.tl .id)),
  -- tl
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.tl (.hd .id)) (.tl .id)),
  -- cons
  lett call1 (lett call2 (.cons (.cons (.hd (.tl (.hd .id))) (.hd (.tl .id))) (.tl (.tl .id)))),
  -- ite
  lett call1 (.ite (.hd (.tl .id))
    (rec' (.hd .id) (.hd (.tl (fA (.hd .id)))) (fX (.hd .id)) (.tl (.tl .id)))
    (rec' (.hd .id) (.tl (.tl (fA (.hd .id)))) (fX (.hd .id)) (.tl (.tl .id)))),
  -- run
  lett call1 (lett call2 (rec' (.hd (.hd .id)) (.hd (.tl (.hd .id))) (.hd (.tl .id)) (.tl (.tl .id)))),
  -- guess
  .cons .guess (fS .id),
  -- fail
  .fail,
  -- theta
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.theta (.hd .id)) (.tl .id)),
  -- mul
  lett (rec' .id (fA .id) (fX .id) (fS .id)) (.cons (.quote .nil) (.run (.quote DC.code) (.cons (.quote DC.code) .id)))
  ]

/-- The interpreter. -/
def IF : Fm := selF caseL (fO .id)

/-- The environment of the interpreter. -/
def env (f x : Tree) (t : Bt) : Tree := .cons IF.code (.cons f (.cons x t.enc))

theorem Dt.fX {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fX b) y x (k + 3) :=
  .hd (.tl (.tl h))

theorem Dt.fS {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fS b) y t.enc (k + 3) :=
  .tl (.tl (.tl h))

theorem Dt.fO {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fO b) y f.hd (k + 3) :=
  .hd (.hd (.tl h))

theorem Dt.fA {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fA b) y f.tl (k + 3) :=
  .tl (.hd (.tl h))

/-- A recursive call. -/
theorem rec_ev {b a x s : Fm} {y g z : Tree} {f' x' : Tree} {t t' : Bt} {kb ka kx ks : ℕ}
    (hb : Dt θ b y (env f' x' t') kb) (ha : Dt θ a y g ka) (hx : Dt θ x y z kx) (hs : Dt θ s y t.enc ks)
    {l : List (Run A)} (h : Ev θ IF (env g z t) l) :
    Ev θ (rec' b a x s) y (l.map (Run.delay (2 * kb + ka + kx + ks + 6))) := by
  have := Ev.run_det (Dt.hd hb) (.cons (.hd hb) (.cons ha (.cons hx hs))) (l := l) (by
    show Ev θ (Fm.ofTree IF.code) _ l
    rw [Fm.ofTree_code]
    exact h)
  refine Eq.mp ?_ this
  congr 1
  refine List.map_congr_left fun r _ => ?_
  simp only [Run.delay, Run.mk.injEq, and_true]
  omega

/-- The runs that stay within the budgets, with what is left. -/
def simS (t : Bt) (l : List (Run A)) : List (Run A × Bt) :=
  l.filterMap fun r => (Bt.decAll r.bill t).map fun t' => (r, t')

theorem mem_simS {t : Bt} {l : List (Run A)} {q : Run A × Bt} (h : q ∈ simS t l) :
    q.1 ∈ l ∧ Bt.decAll q.1.bill t = some q.2 := by
  rw [simS, List.mem_filterMap] at h
  obtain ⟨r, hr, h⟩ := h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨t', ht, rfl⟩ := h
  exact ⟨hr, ht⟩

theorem simS_map {t : Bt} {l : List (Run A)} {G : Run A → Run A} (h : ∀ r, (G r).bill = r.bill) :
    simS t (l.map G) = (simS t l).map fun q => (G q.1, q.2) := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    simp only [simS, List.map_cons, List.filterMap_cons, h] at ih ⊢
    cases Bt.decAll r.bill t with
    | none => exact ih
    | some t' =>
      simp only [Option.map_some, List.map_cons]
      rw [ih]

theorem simS_append {t : Bt} {l l' : List (Run A)} : simS t (l ++ l') = simS t l ++ simS t l' := by
  simp [simS]

theorem simS_flatMap {t : Bt} {la : List (Run A)} {L : Run A → List (Run A)} {G : Run A → Run A → Run A}
    (h : ∀ r s, (G r s).bill = r.bill ++ s.bill) : simS t (la.flatMap fun r => (L r).map (G r)) =
      (simS t la).flatMap fun q => (simS q.2 (L q.1)).map fun p => (G q.1 p.1, p.2) := by
  have one : ∀ (r : Run A) (l : List (Run A)), simS t (l.map (G r)) =
      ((Bt.decAll r.bill t).toList.map fun t' => (r, t')).flatMap fun q =>
        (simS q.2 l).map fun p => (G q.1 p.1, p.2) := by
    intro r l
    cases hd : Bt.decAll r.bill t with
    | none =>
      simp only [Option.toList_none, List.map_nil, List.flatMap_nil, simS, List.filterMap_map]
      rw [List.filterMap_eq_nil_iff]
      intro s _
      simp [h, Bt.decAll_append, hd]
    | some t' =>
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      induction l with
      | nil => rfl
      | cons s l ih =>
        simp only [simS, List.map_cons, List.filterMap_cons, h, Bt.decAll_append, hd, Option.bind_some] at ih ⊢
        cases Bt.decAll s.bill t' with
        | none => exact ih
        | some t'' =>
          simp only [Option.map_some, List.map_cons]
          rw [ih]
  induction la with
  | nil => rfl
  | cons r la ih =>
    rw [List.flatMap_cons, simS_append, ih, one]
    simp only [simS, List.filterMap_cons]
    cases Bt.decAll r.bill t with
    | none => simp
    | some t' => simp

end Code

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The interpreter is right
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem Run.seq_assoc (r s t : Run A) : (r.seq s).seq t = r.seq (s.seq t) := by
  simp [Run.seq, add_assoc, mul_assoc, List.append_assoc]

theorem Fm.ofTree_cases (f : Tree) :
    (f.hd.len = 0 ∧ ofTree f = quote f.tl) ∨ (f.hd.len = 1 ∧ ofTree f = id) ∨
    (f.hd.len = 2 ∧ ofTree f = hd (ofTree f.tl)) ∨ (f.hd.len = 3 ∧ ofTree f = tl (ofTree f.tl)) ∨
    (f.hd.len = 4 ∧ ofTree f = cons (ofTree f.tl.hd) (ofTree f.tl.tl)) ∨
    (f.hd.len = 5 ∧ ofTree f = ite (ofTree f.tl.hd) (ofTree f.tl.tl.hd) (ofTree f.tl.tl.tl)) ∨
    (f.hd.len = 6 ∧ ofTree f = run (ofTree f.tl.hd) (ofTree f.tl.tl)) ∨
    (f.hd.len = 7 ∧ ofTree f = guess) ∨ ((f.hd.len = 8 ∨ 11 ≤ f.hd.len) ∧ ofTree f = fail) ∨
    (f.hd.len = 9 ∧ ofTree f = theta (ofTree f.tl)) ∨ (f.hd.len = 10 ∧ ofTree f = mul (ofTree f.tl)) := by
  cases f with
  | nil => left; exact ⟨rfl, by rw [ofTree]; rfl⟩
  | cons o a =>
    rw [ofTree]
    simp only [hd_cons, tl_cons]
    rcases hn : o.len with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> simp

/-- What the interpreter does in one run: `q` is a run of the formula and the budgets that are left. -/
structure RelJ (M j : ℕ) (r : Run A) (q : Run A × Bt) : Prop where
  th : r.th = q.1.th
  bill : r.bill = []
  out : r.out = .cons q.1.out q.2.enc
  cost : r.cost + j ≤ M * q.1.cost

/-- The bound for the overhead. -/
def MM (H : ℕ) : ℕ := 1000 + 100 * H

theorem IF_case {f x : Tree} {t : Bt} {c : Fm} (hc : caseL[f.hd.len]? = some c) {M : ℕ}
    {Q : List (Run A × Bt)} (h : ∃ l, Ev θ c (env f x t) l ∧ List.Forall₂ (RelJ M 300) l Q) :
    ∃ l', Ev θ IF (env f x t) l' ∧ List.Forall₂ (RelJ M 0) l' Q := by
  obtain ⟨l, hl, hQ⟩ := h
  obtain ⟨k', hk', h'⟩ := selF_ev (cs := caseL) (b := fO .id) (Dt.fO (Dt.id (θ := θ) (env f x t))) (l := l)
    (fun c' hc' => by
      rw [hc] at hc'
      obtain rfl := Option.some.inj hc'
      exact hl)
    (fun hlen => by
      rw [List.getElem?_eq_none hlen] at hc
      simp at hc)
  refine ⟨_, h', ?_⟩
  rw [List.forall₂_map_left_iff]
  have hk : k' ≤ 300 := hk'.trans (by simp [caseL])
  refine hQ.imp fun r q hr => ⟨hr.th, hr.bill, hr.out, ?_⟩
  have := hr.cost
  simp only [Run.delay]
  omega

/-- A call for a single value: `let r = IF(args)`. -/
theorem call0 {f x : Tree} {t : Bt} {M : ℕ} {l : List (Run A)}
    (h : ∃ l', Ev θ IF (env f.tl x t) l' ∧ List.Forall₂ (RelJ M 0) l' (simS t l)) {body : Fm}
    {Q2 : Run A × Bt → List (Run A × Bt)}
    (hb : ∀ q ∈ simS t l, ∃ l2, Ev θ body (.cons q.1.out q.2.enc) l2 ∧ List.Forall₂ (fun s p => s.bill = [] ∧
      q.1.th * s.th = p.1.th ∧ s.out = .cons p.1.out p.2.enc ∧ M * q.1.cost + s.cost + 400 ≤ M * p.1.cost) l2 (Q2 q)) :
    ∃ l', Ev θ (lett (rec' .id (fA .id) (fX .id) (fS .id)) body) (env f x t) l' ∧
      List.Forall₂ (RelJ M 300) l' ((simS t l).flatMap Q2) := by
  obtain ⟨l1, h1, h1'⟩ := h
  have e := rec_ev (Dt.id (env f x t)) (Dt.fA (Dt.id _)) (Dt.fX (Dt.id _)) (Dt.fS (Dt.id _)) h1
  refine lett_rel e (Q := simS t l) (R := fun s q => s.th = q.1.th ∧ s.bill = [] ∧ s.out = .cons q.1.out q.2.enc ∧
    s.cost ≤ M * q.1.cost + 30) ?_ ?_
  · rw [List.forall₂_map_left_iff]
    refine h1'.imp fun r q hr => ⟨hr.th, hr.bill, hr.out, ?_⟩
    have := hr.cost
    simp only [Run.delay]
    omega
  · rintro s - q hq ⟨e1, e2, e3, e4⟩
    obtain ⟨l2, h2, h2'⟩ := hb q hq
    rw [← e3] at h2
    refine ⟨l2, h2, h2'.imp fun u p hu => ?_⟩
    obtain ⟨f1, f2, f3, f4⟩ := hu
    refine ⟨?_, ?_, f3, ?_⟩
    · simp only [e1, f2]
    · simp only [e2, f1, List.append_nil]
    · simp only
      omega

theorem call1_rel {f x : Tree} {t : Bt} {M : ℕ} {l : List (Run A)}
    (h : ∃ l', Ev θ IF (env f.tl.hd x t) l' ∧ List.Forall₂ (RelJ M 0) l' (simS t l)) :
    ∃ l', Ev θ call1 (env f x t) l' ∧ List.Forall₂ (fun s q => s.th = q.1.th ∧ s.bill = [] ∧
      s.out = .cons (env f x t) (.cons q.1.out q.2.enc) ∧ s.cost ≤ M * q.1.cost + 30) l' (simS t l) := by
  obtain ⟨l1, h1, h1'⟩ := h
  have e := Ev.cons (Dt.id (θ := θ) (env f x t))
    (rec_ev (Dt.id (env f x t)) (.hd (Dt.fA (Dt.id _))) (Dt.fX (Dt.id _)) (Dt.fS (Dt.id _)) h1)
  refine ⟨_, e, ?_⟩
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.forall₂_map_left_iff, List.forall₂_map_left_iff]
  refine h1'.imp fun r q hr => ⟨?_, ?_, ?_, ?_⟩
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.th]
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.bill]
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.out]
  · have := hr.cost
    simp only [Run.seq, Run.tick, Run.det, Run.delay]
    omega

theorem call2_rel {f x o : Tree} {t t1 : Bt} {M : ℕ} {l : List (Run A)}
    (h : ∃ l', Ev θ IF (env f.tl.tl x t1) l' ∧ List.Forall₂ (RelJ M 0) l' (simS t1 l)) :
    ∃ l', Ev θ call2 (.cons (env f x t) (.cons o t1.enc)) l' ∧ List.Forall₂ (fun s q => s.th = q.1.th ∧ s.bill = [] ∧
      s.out = .cons (.cons (env f x t) (.cons o t1.enc)) (.cons q.1.out q.2.enc) ∧ s.cost ≤ M * q.1.cost + 30) l'
      (simS t1 l) := by
  obtain ⟨l1, h1, h1'⟩ := h
  have hb : Dt θ (.hd .id) (.cons (env f x t) (.cons o t1.enc)) (env f x t) 2 := .hd (.id _)
  have e := Ev.cons (Dt.id (θ := θ) (.cons (env f x t) (.cons o t1.enc)))
    (rec_ev hb (.tl (Dt.fA hb)) (Dt.fX hb) (t := t1) (.tl (.tl (Dt.id _))) h1)
  refine ⟨_, e, ?_⟩
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.forall₂_map_left_iff, List.forall₂_map_left_iff]
  refine h1'.imp fun r q hr => ⟨?_, ?_, ?_, ?_⟩
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.th]
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.bill]
  · simp [Run.seq, Run.tick, Run.det, Run.delay, hr.out]
  · have := hr.cost
    simp only [Run.seq, Run.tick, Run.det, Run.delay]
    omega

theorem flatMap_single {α β : Type*} (l : List α) (g : α → β) : (l.flatMap fun a => [g a]) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- **The interpreter is right.** -/
theorem interp {H : ℕ} {F : Fm} {x : Tree} {l : List (Run A)} (h : Ev θ F x l) :
    ∀ f, Fm.ofTree f = F → ∀ t : Bt, t.ht ≤ H →
      ∃ l', Ev θ IF (env f x t) l' ∧ List.Forall₂ (RelJ (MM H) 0) l' (simS t l) := by
  have hM : 1000 ≤ MM H := by unfold MM; omega
  induction h with
  | quote c x =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := .cons (fA .id) (fS .id)) (by rw [h1]; rfl) ⟨_, Dt.cons (Dt.fA (Dt.id _)) (Dt.fS (Dt.id _)), ?_⟩
    simp only [simS, Run.det, List.filterMap_cons, Bt.decAll, Option.map_some, List.filterMap_nil]
    refine .cons ⟨rfl, rfl, rfl, ?_⟩ .nil
    simp only
    omega
  | id x =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := .cons (fX .id) (fS .id)) (by rw [h1]; rfl) ⟨_, Dt.cons (Dt.fX (Dt.id _)) (Dt.fS (Dt.id _)), ?_⟩
    simp only [simS, Run.det, List.filterMap_cons, Bt.decAll, Option.map_some, List.filterMap_nil]
    refine .cons ⟨rfl, rfl, rfl, ?_⟩ .nil
    simp only
    omega
  | @hd a x l h ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    rw [simS_map (G := fun r => r.tick r.out.hd) (fun _ => rfl), ← flatMap_single]
    refine call0 (ih f.tl rfl t ht) fun q hq => ⟨_, Dt.cons (.hd (.hd (.id _))) (.tl (.id _)), ?_⟩
    refine .cons ⟨rfl, mul_one _, rfl, ?_⟩ .nil
    simp only [Run.tick, Run.det]
    nlinarith
  | @tl a x l h ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    rw [simS_map (G := fun r => r.tick r.out.tl) (fun _ => rfl), ← flatMap_single]
    refine call0 (ih f.tl rfl t ht) fun q hq => ⟨_, Dt.cons (.tl (.hd (.id _))) (.tl (.id _)), ?_⟩
    refine .cons ⟨rfl, mul_one _, rfl, ?_⟩ .nil
    simp only [Run.tick, Run.det]
    nlinarith
  | @cons a b x la lb ha hb iha ihb =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    obtain ⟨l1, e1, r1⟩ := call1_rel (iha f.tl.hd rfl t ht)
    rw [simS_flatMap (G := fun r s => (r.seq s).tick (.cons r.out s.out)) (fun _ _ => rfl)]
    refine lett_rel e1 r1 fun s _ q hq hs => ?_
    obtain ⟨s1, s2, s3, s4⟩ := hs
    have hqt : q.2.ht ≤ H := (Bt.ht_decAll (mem_simS hq).2).trans_le ht
    obtain ⟨l2, e2, r2⟩ := call2_rel (f := f) (o := q.1.out) (t := t) (ihb f.tl.tl rfl q.2 hqt)
    rw [← s3] at e2
    rw [← flatMap_single]
    refine lett_rel e2 r2 fun u _ p hp hu => ?_
    obtain ⟨u1, u2, u3, u4⟩ := hu
    rw [u3]
    refine ⟨_, Dt.cons (.cons (.hd (.tl (.hd (.id _)))) (.hd (.tl (.id _)))) (.tl (.tl (.id _))), .cons ⟨?_, ?_, rfl, ?_⟩ .nil⟩
    · simp [Run.det, Run.seq, Run.tick, s1, u1]
    · simp [Run.det, s2, u2]
    · simp only [Run.det, Run.seq, Run.tick]
      nlinarith
  | @ite a b c x la L ha hb hc iha ihb ihc =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    obtain ⟨l1, e1, r1⟩ := call1_rel (iha f.tl.hd rfl t ht)
    rw [simS_flatMap (G := fun r s => (r.seq s).tick s.out) (fun _ _ => rfl)]
    refine lett_rel e1 r1 fun s _ q hq hs => ?_
    obtain ⟨s1, s2, s3, s4⟩ := hs
    have hqt : q.2.ht ≤ H := (Bt.ht_decAll (mem_simS hq).2).trans_le ht
    have hy : Dt θ (.hd .id) s.out (env f x t) 2 := by rw [s3]; exact .hd (.id _)
    have hv : Dt θ (.hd (.tl .id)) s.out q.1.out 3 := by rw [s3]; exact .hd (.tl (.id _))
    have ht' : Dt θ (.tl (.tl .id)) s.out q.2.enc 3 := by rw [s3]; exact .tl (.tl (.id _))
    by_cases hq0 : q.1.out = .nil
    · obtain ⟨l2, e2, r2⟩ := ihc q.1 (mem_simS hq).1 hq0 f.tl.tl.tl rfl q.2 hqt
      refine ⟨_, Ev.ite_false (hq0 ▸ hv) (rec_ev hy (.tl (.tl (Dt.fA hy))) (Dt.fX hy) ht' e2), ?_⟩
      rw [List.forall₂_map_left_iff, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine r2.imp fun u p hu => ⟨?_, ?_, ?_, ?_⟩
      · simp [Run.delay, Run.seq, Run.tick, s1, hu.th]
      · simp [Run.delay, s2, hu.bill]
      · simp [Run.delay, Run.tick, hu.out]
      · have := hu.cost
        simp only [Run.delay, Run.seq, Run.tick]
        nlinarith
    · obtain ⟨l2, e2, r2⟩ := ihb q.1 (mem_simS hq).1 hq0 f.tl.tl.hd rfl q.2 hqt
      refine ⟨_, Ev.ite_true hv hq0 (rec_ev hy (.hd (.tl (Dt.fA hy))) (Dt.fX hy) ht' e2), ?_⟩
      rw [List.forall₂_map_left_iff, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine r2.imp fun u p hu => ⟨?_, ?_, ?_, ?_⟩
      · simp [Run.delay, Run.seq, Run.tick, s1, hu.th]
      · simp [Run.delay, s2, hu.bill]
      · simp [Run.delay, Run.tick, hu.out]
      · have := hu.cost
        simp only [Run.delay, Run.seq, Run.tick]
        nlinarith
  | @run a b x la lb L ha hb hL iha ihb ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    obtain ⟨l1, e1, r1⟩ := call1_rel (iha f.tl.hd rfl t ht)
    have hlist : (la.flatMap fun r => lb.flatMap fun s => (L r s).map fun t => ((r.seq s).seq t).tick t.out) =
        la.flatMap fun r => (lb.flatMap fun s => (L r s).map fun t => s.seq t).map fun u => (r.seq u).tick u.out := by
      refine List.flatMap_congr fun r _ => ?_
      rw [List.map_flatMap]
      refine List.flatMap_congr fun s _ => ?_
      rw [List.map_map]
      refine List.map_congr_left fun u _ => ?_
      simp only [Function.comp_apply, Run.seq_assoc]
      rfl
    rw [hlist, simS_flatMap (G := fun r s => (r.seq s).tick s.out) (fun _ _ => rfl)]
    refine lett_rel e1 r1 fun s _ q hq hs => ?_
    obtain ⟨s1, s2, s3, s4⟩ := hs
    have hqt : q.2.ht ≤ H := (Bt.ht_decAll (mem_simS hq).2).trans_le ht
    obtain ⟨l2, e2, r2⟩ := call2_rel (f := f) (o := q.1.out) (t := t) (ihb f.tl.tl rfl q.2 hqt)
    rw [← s3] at e2
    rw [simS_flatMap (G := fun r s => r.seq s) (fun _ _ => rfl), List.map_flatMap]
    refine lett_rel e2 r2 fun u _ p hp hu => ?_
    obtain ⟨u1, u2, u3, u4⟩ := hu
    have hpt : p.2.ht ≤ H := (Bt.ht_decAll (mem_simS hp).2).trans_le hqt
    obtain ⟨l3, e3, r3⟩ := ih q.1 (mem_simS hq).1 p.1 (mem_simS hp).1 q.1.out rfl p.2 hpt
    have hy : Dt θ (.hd (.hd .id)) u.out (env f x t) 3 := by rw [u3]; exact .hd (.hd (.id _))
    have hf' : Dt θ (.hd (.tl (.hd .id))) u.out q.1.out 4 := by rw [u3]; exact .hd (.tl (.hd (.id _)))
    have hx : Dt θ (.hd (.tl .id)) u.out p.1.out 3 := by rw [u3]; exact .hd (.tl (.id _))
    have ht' : Dt θ (.tl (.tl .id)) u.out p.2.enc 3 := by rw [u3]; exact .tl (.tl (.id _))
    refine ⟨_, rec_ev hy hf' hx ht' e3, ?_⟩
    rw [List.forall₂_map_left_iff, List.map_map, List.forall₂_map_right_iff]
    refine r3.imp fun v w hv => ⟨?_, ?_, ?_, ?_⟩
    · simp [Run.delay, Run.seq, Run.tick, s1, u1, hv.th]
    · simp [Run.delay, s2, u2, hv.bill]
    · simp [Run.delay, Run.seq, Run.tick, hv.out]
    · have := hv.cost
      simp only [Run.delay, Run.seq, Run.tick, Function.comp_apply]
      nlinarith
  | guess x =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := .cons .guess (fS .id)) (by rw [h1]; rfl) ⟨_, Ev.cons (.guess _) (Dt.fS (Dt.id _)), ?_⟩
    simp only [simS, Run.det, List.filterMap_cons, Bt.decAll, Option.map_some, List.filterMap_nil]
    refine .cons ⟨?_, rfl, rfl, ?_⟩ (.cons ⟨?_, rfl, rfl, ?_⟩ .nil)
    · simp [Run.seq, Run.tick]
    · simp only [Run.seq, Run.tick]; omega
    · simp [Run.seq, Run.tick]
    · simp only [Run.seq, Run.tick]; omega
  | fail x =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    obtain ⟨k', hk', h'⟩ := selF_ev (cs := caseL) (b := fO .id) (Dt.fO (Dt.id (θ := θ) (env f x t))) (l := [])
      (fun c' hc' => by
        rcases h1 with h1 | h1
        · rw [h1] at hc'
          obtain rfl := Option.some.inj hc'
          exact .fail _
        · rw [List.getElem?_eq_none (by simpa [caseL] using h1)] at hc'
          simp at hc')
      (fun _ => rfl)
    exact ⟨_, h', by simp [simS]⟩
  | @theta a x l h ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    rw [simS_map (G := fun r => ⟨r.cost + 1, r.th * θ r.out.path, r.bill, .nil⟩) (fun _ => rfl), ← flatMap_single]
    refine call0 (ih f.tl rfl t ht) fun q hq => ⟨_, Ev.cons (Ev.theta (Dt.hd (.id _))) (Dt.tl (.id _)), ?_⟩
    refine .cons ⟨rfl, ?_, rfl, ?_⟩ .nil
    · simp [Run.seq, Run.tick, Run.det]
    · simp only [Run.seq, Run.tick, Run.det]
      nlinarith
  | @mul a x l h ih =>
    intro f hf t ht
    rcases Fm.ofTree_cases f with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hf] at h2 <;> try cases h2
    refine IF_case (c := _) (by rw [h1]; rfl) ?_
    have hlist : simS t (l.map fun r => (⟨r.cost + 1, r.th, r.bill ++ [r.out.path], .nil⟩ : Run A)) =
        (simS t l).flatMap fun q => ((Bt.dec q.1.out.path q.2).map fun t' =>
          ((⟨q.1.cost + 1, q.1.th, q.1.bill ++ [q.1.out.path], .nil⟩ : Run A), t')).toList := by
      clear ih h
      induction l with
      | nil => rfl
      | cons r l ih =>
        simp only [simS, List.map_cons, List.filterMap_cons, Bt.decAll_append] at ih ⊢
        cases hd : Bt.decAll r.bill t with
        | none =>
          simp only [Option.bind_none, Option.map_none]
          exact ih
        | some t1 =>
          simp only [Option.bind_some, Bt.decAll, Option.map_some, List.flatMap_cons]
          cases hd2 : Bt.dec r.out.path t1 with
          | none =>
            simp only [Option.bind_none, Option.map_none, Option.toList_none, List.nil_append]
            exact ih
          | some t2 =>
            simp only [Option.bind_some, Option.map_some, Option.toList_some, List.singleton_append]
            rw [ih]
    rw [hlist]
    refine call0 (ih f.tl rfl t ht) fun q hq => ?_
    have hqt : q.2.ht ≤ H := (Bt.ht_decAll (mem_simS hq).2).trans_le ht
    cases hd : Bt.dec q.1.out.path q.2 with
    | none =>
      refine ⟨_, Ev.cons_nil_right (Dt.quote _ _) (Ev.run_nil (.quote _ _) (.cons (.quote _ _) (.id _)) ?_), .nil⟩
      rw [Fm.ofTree_code]
      exact DC_none hd
    | some t2 =>
      obtain ⟨k, hk, hdc⟩ := DC_some (θ := θ) hd
      refine ⟨_, Dt.cons (.quote _ _) (.run (.quote _ _) (.cons (.quote _ _) (.id _)) (i := k) ?_), .cons ⟨rfl, ?_, rfl, ?_⟩ .nil⟩
      · rw [Fm.ofTree_code]
        exact hdc
      · simp [Run.det]
      · simp only [Run.det]
        have : 60 * q.2.ht + 420 ≤ MM H := by unfold MM; omega
        nlinarith

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Constants are postponed

`WF` applied to (program, (argument, budgets)) has, as plain weighted sum, the sum of the weights of the runs whose
names of constants are exactly the given budgets. Summed over all budgets with the powers of the constants this is
the value of the program.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R]

namespace KT
/-- The constant with a given name (0 if there is none). -/
def lookup : KT R → List Bool → R
  | none, _ => 0
  | leaf c, [] => c
  | leaf _, _ :: _ => 0
  | node _ _, [] => 0
  | node _ r, true :: p => r.lookup p
  | node l _, false :: p => l.lookup p

/-- Numbers with `J` digits. -/
def words : ℕ → List (List Bool)
  | 0 => [[]]
  | J + 1 => [false, true].flatMap fun b => (words J).map (b :: ·)

/-- The value of a number. -/
def val : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 1 else 0) + 2 * val w

/-- All budgets with `J` digits for the names of a trie, with the products of the powers of its constants. -/
def budg (J : ℕ) : KT R → List (Bt × R)
  | none => [(.none, 1)]
  | leaf c => (words J).map fun w => (.leaf w, c ^ val w)
  | node l r => (l.budg J).flatMap fun p => (r.budg J).map fun q => (.node p.1 q.1, p.2 * q.2)

end KT

/-- The bill uses up the budgets. -/
def ok (t : Bt) (b : List (List Bool)) : Bool := ((Bt.decAll b t).map Bt.zero).getD false

theorem ok_nil (t : Bt) : ok t [] = t.zero := rfl

theorem ok_cons (t : Bt) (p : List Bool) (b : List (List Bool)) :
    ok t (p :: b) = ((Bt.dec p t).map fun t' => ok t' b).getD false := by
  unfold ok
  simp only [Bt.decAll]
  cases Bt.dec p t <;> rfl

theorem all_not_iff (w : List Bool) : (w.all (! ·)) = true ↔ KT.val w = 0 := by
  induction w with
  | nil => simp [KT.val]
  | cons b w ih =>
    cases b with
    | true => simp [KT.val]
    | false => simp [KT.val, ← ih]

theorem decw_val (w : List Bool) : (decw w = none ∧ KT.val w = 0) ∨ ∃ w', decw w = some w' ∧ KT.val w = KT.val w' + 1 := by
  induction w with
  | nil => left; simp [decw, KT.val]
  | cons b w ih =>
    cases b with
    | true => right; exact ⟨false :: w, rfl, by simp [KT.val]; omega⟩
    | false =>
      rcases ih with ⟨h1, h2⟩ | ⟨w', h1, h2⟩
      · left; simp [decw, h1, KT.val, h2]
      · right
        refine ⟨true :: w', by simp [decw, h1], ?_⟩
        simp only [KT.val, h2]
        simp
        omega

theorem ok_leaf (w : List Bool) (b : List (List Bool)) :
    ok (.leaf w) b = true ↔ (∀ p ∈ b, p = []) ∧ KT.val w = b.length := by
  induction b generalizing w with
  | nil =>
    rw [ok_nil, Bt.zero, all_not_iff]
    simp
  | cons p b ih =>
    rw [ok_cons]
    cases p with
    | cons a p => simp [Bt.dec]
    | nil =>
      rcases decw_val w with ⟨h1, h2⟩ | ⟨w', h1, h2⟩
      · simp only [Bt.dec, h1, Option.map_none, Option.getD_none, Bool.false_eq_true, List.length_cons, false_iff]
        rintro ⟨-, h⟩
        omega
      · simp only [Bt.dec, h1, Option.map_some, Option.getD_some, ih, List.mem_cons, forall_eq_or_imp, true_and,
          List.length_cons]
        refine and_congr_right fun _ => ?_
        omega

/-- The names that begin with a given bit. -/
def part (a : Bool) (b : List (List Bool)) : List (List Bool) := b.filterMap fun p => match p with
  | [] => none
  | c :: p => if c = a then some p else none

theorem part_cons (a c : Bool) (p : List Bool) (b : List (List Bool)) :
    part a ((c :: p) :: b) = if c = a then p :: part a b else part a b := by
  unfold part
  by_cases h : c = a <;> simp [h]

theorem length_part_le (a : Bool) (b : List (List Bool)) : (part a b).length ≤ b.length :=
  List.length_filterMap_le _ _

theorem ok_node (l r : Bt) (b : List (List Bool)) :
    ok (.node l r) b = true ↔ [] ∉ b ∧ ok l (part false b) = true ∧ ok r (part true b) = true := by
  induction b generalizing l r with
  | nil => simp [ok_nil, part, Bt.zero]
  | cons p b ih =>
    rw [ok_cons]
    cases p with
    | nil => simp [Bt.dec]
    | cons a p =>
      cases a with
      | true =>
        rw [part_cons, part_cons, if_neg (by simp), if_pos rfl, ok_cons]
        cases h : Bt.dec p r with
        | none => simp [Bt.dec, h]
        | some r' => simp [Bt.dec, h, ih]
      | false =>
        rw [part_cons, part_cons, if_pos rfl, if_neg (by simp), ok_cons]
        cases h : Bt.dec p l with
        | none => simp [Bt.dec, h]
        | some l' => simp [Bt.dec, h, ih]

theorem ok_none (b : List (List Bool)) : ok .none b = true ↔ b = [] := by
  cases b with
  | nil => simp [ok_nil, Bt.zero]
  | cons p b => simp [ok_cons, Bt.dec]

theorem sum_words (J n : ℕ) (c : R) :
    ((KT.words J).map fun w => if KT.val w = n then c else 0).sum = if n < 2 ^ J then c else 0 := by
  induction J generalizing n with
  | zero =>
    by_cases h : n = 0
    · subst h
      simp [KT.words, KT.val]
    · have h' : ¬ 0 = n := fun e => h e.symm
      simp [KT.words, KT.val, h, h']
  | succ J ih =>
    have e0 : ((KT.words J).map fun w => if KT.val (false :: w) = n then c else 0).sum =
        if n % 2 = 0 ∧ n < 2 ^ (J + 1) then c else 0 := by
      by_cases h : n % 2 = 0
      · have : ∀ w, (KT.val (false :: w) = n) = (KT.val w = n / 2) := by
          intro w
          simp only [KT.val, Bool.false_eq_true, if_false, zero_add, eq_iff_iff]
          omega
        simp only [this, ih, h, true_and]
        refine if_congr ?_ rfl rfl
        rw [pow_succ]
        omega
      · have : ∀ w, (KT.val (false :: w) = n) = False := by
          intro w
          simp only [KT.val, Bool.false_eq_true, if_false, zero_add, eq_iff_iff, iff_false]
          omega
        simp [this, h]
    have e1 : ((KT.words J).map fun w => if KT.val (true :: w) = n then c else 0).sum =
        if n % 2 = 1 ∧ n < 2 ^ (J + 1) then c else 0 := by
      by_cases h : n % 2 = 1
      · have : ∀ w, (KT.val (true :: w) = n) = (KT.val w = n / 2) := by
          intro w
          simp only [KT.val, if_true, eq_iff_iff]
          omega
        simp only [this, ih, h, true_and]
        refine if_congr ?_ rfl rfl
        rw [pow_succ]
        omega
      · have : ∀ w, (KT.val (true :: w) = n) = False := by
          intro w
          simp only [KT.val, if_true, eq_iff_iff, iff_false]
          omega
        simp [this, h]
    simp only [KT.words, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.map_map,
      List.sum_append, Function.comp_def]
    rw [e0, e1]
    by_cases hn : n < 2 ^ (J + 1)
    · rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h, hn]
    · simp [hn]

theorem sum_flatMap_map {α β : Type*} (l : List α) (f : α → List β) (g : β → R) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem prod_lookup_node (l r : KT R) (b : List (List Bool)) : (b.map (KT.node l r).lookup).prod =
    if [] ∈ b then 0 else ((part false b).map l.lookup).prod * ((part true b).map r.lookup).prod := by
  induction b with
  | nil => simp [part]
  | cons p b ih =>
    cases p with
    | nil => simp [KT.lookup]
    | cons a p =>
      rw [List.map_cons, List.prod_cons, ih, part_cons, part_cons]
      cases a with
      | true =>
        by_cases h : [] ∈ b
        · simp [h]
        · simp only [h, KT.lookup, List.mem_cons, if_false, Bool.true_eq_false, if_true, List.map_cons, List.prod_cons,
            reduceCtorEq, or_self]
          ring
      | false =>
        by_cases h : [] ∈ b
        · simp [h]
        · simp only [h, KT.lookup, List.mem_cons, if_false, Bool.false_eq_true, if_true, List.map_cons, List.prod_cons,
            reduceCtorEq, or_self]
          ring

/-- **All budgets together.** -/
theorem sum_budg (J : ℕ) (K : KT R) (b : List (List Bool)) (hb : b.length < 2 ^ J) :
    ((K.budg J).map fun q => if ok q.1 b = true then q.2 else 0).sum = (b.map K.lookup).prod := by
  induction K generalizing b with
  | none =>
    simp only [KT.budg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ok_none]
    cases b with
    | nil => simp
    | cons p b => simp [KT.lookup]
  | leaf c =>
    simp only [KT.budg, List.map_map, Function.comp_def, ok_leaf]
    by_cases h : ∀ p ∈ b, p = []
    · have e1 : ((KT.words J).map fun w => if (∀ p ∈ b, p = []) ∧ KT.val w = b.length then c ^ KT.val w else 0) =
          (KT.words J).map fun w => if KT.val w = b.length then c ^ b.length else 0 := by
        refine List.map_congr_left fun w _ => ?_
        by_cases h2 : KT.val w = b.length
        · simp [h2, if_pos h]
        · simp [h2]
      rw [e1, sum_words, if_pos hb]
      have : b.map (KT.leaf c).lookup = List.replicate b.length c := by
        rw [List.eq_replicate_iff]
        refine ⟨by simp, fun x hx => ?_⟩
        rw [List.mem_map] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        rw [h p hp]
        rfl
      rw [this, List.prod_replicate]
    · simp only [h, false_and, if_false, List.map_const', List.sum_replicate, smul_zero]
      push Not at h
      obtain ⟨p, hp, hne⟩ := h
      symm
      apply List.prod_eq_zero
      rw [List.mem_map]
      refine ⟨p, hp, ?_⟩
      cases p with
      | nil => exact absurd rfl hne
      | cons a p => rfl
  | node l r ihl ihr =>
    have h1 := ihl (part false b) (lt_of_le_of_lt (length_part_le _ _) hb)
    have h2 := ihr (part true b) (lt_of_le_of_lt (length_part_le _ _) hb)
    rw [prod_lookup_node, ← h1, ← h2]
    simp only [KT.budg, sum_flatMap_map, List.map_map, Function.comp_def, ok_node]
    by_cases h : [] ∈ b
    · simp [h]
    · simp only [h, not_false_eq_true, true_and, if_false]
      rw [← List.sum_map_mul_right]
      congr 1
      refine List.map_congr_left fun p _ => ?_
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun q _ => ?_
      by_cases h3 : ok p.1 (part false b) = true <;> by_cases h4 : ok q.1 (part true b) = true <;> simp [h3, h4]



/-- Apply a program; then check that the budgets are used up. The argument is (program, (argument, budgets)). -/
def WF : Fm := lett (.cons (.quote AZ.code) (.tl (lett (.cons (.quote IF.code) .id) IF))) AZ

theorem simS_cons (t : Bt) (r : Run A) (l : List (Run A)) :
    simS t (r :: l) = ((Bt.decAll r.bill t).map fun t' => (r, t')).toList ++ simS t l := by
  simp only [simS, List.filterMap_cons]
  cases Bt.decAll r.bill t <;> rfl

theorem map_simS (t : Bt) (l : List (Run A)) :
    ((simS t l).flatMap fun q => if q.2.zero then [q] else []).map (fun q => q.1.th) =
      (l.filter fun r => ok t r.bill).map Run.th := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    rw [simS_cons, List.flatMap_append, List.map_append, ih, List.filter_cons]
    cases hd : Bt.decAll r.bill t with
    | none =>
      have : ok t r.bill = false := by rw [ok, hd]; rfl
      simp [this]
    | some t' =>
      have : ok t r.bill = t'.zero := by rw [ok, hd]; rfl
      rw [this]
      by_cases hz : t'.zero <;> simp [hz]

theorem sum_filter_th (t : Bt) (l : List (Run A)) :
    ((l.filter fun r => ok t r.bill).map Run.th).sum = (l.map fun r => if ok t r.bill = true then r.th else 0).sum := by
  induction l with
  | nil => rfl
  | cons r l ih => cases hr : ok t r.bill <;> simp [hr, ih]

/-- **Lemma 1, one bill**: `WF` is plain; it has the runs whose bill is the budget. -/
theorem WF_ev {H T : ℕ} {p d : Tree} {l : List (Run A)} (h : Ev θ (Fm.ofTree p) d l) (hT : ∀ r ∈ l, r.cost ≤ T)
    {t : Bt} (ht : t.ht ≤ H) : ∃ l', Ev θ WF (.cons p (.cons d t.enc)) l' ∧
      (∀ r ∈ l', r.bill = [] ∧ r.cost ≤ MM H * T + 40 * t.nds + 40) ∧
      l'.map Run.th = (l.filter fun r => ok t r.bill).map Run.th := by
  obtain ⟨l1, e1, r1⟩ := interp h p rfl t ht
  -- the interpreter
  obtain ⟨l2, e2, r2⟩ := lett_rel (body := IF) (Dt.cons (.quote IF.code (.cons p (.cons d t.enc))) (.id _))
    (Q := [()]) (R := fun s _ => s = .det 3 (env p d t)) (.cons rfl .nil) (Q2 := fun _ => simS t l)
    (R2 := fun r q => r.th = q.1.th ∧ r.bill = [] ∧ r.out = .cons q.1.out q.2.enc ∧ r.cost ≤ MM H * q.1.cost + 5)
    (by
      rintro s - - - rfl
      refine ⟨l1, e1, r1.imp fun r q hr => ⟨?_, ?_, hr.out, ?_⟩⟩
      · simp [Run.det, hr.th]
      · simp [Run.det, hr.bill]
      · have := hr.cost
        simp only [Run.det]
        omega)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at r2
  -- the check
  have e3 := Ev.cons (Dt.quote (θ := θ) AZ.code (.cons p (.cons d t.enc))) (Ev.tl e2)
  obtain ⟨l4, e4, r4⟩ := lett_rel (body := AZ) e3 (Q := simS t l)
    (R := fun r q => r.th = q.1.th ∧ r.bill = [] ∧ r.out = .cons AZ.code q.2.enc ∧ r.cost ≤ MM H * q.1.cost + 10) (by
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.forall₂_map_left_iff, List.forall₂_map_left_iff]
      refine r2.imp fun r q hr => ?_
      obtain ⟨h1, h2, h3, h4⟩ := hr
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Run.seq, Run.tick, Run.det, h1]
      · simp [Run.seq, Run.tick, Run.det, h2]
      · simp [Run.seq, Run.tick, Run.det, h3]
      · simp only [Run.seq, Run.tick, Run.det]
        omega) (Q2 := fun q => if q.2.zero then [q] else [])
    (R2 := fun r q => r.th = q.1.th ∧ r.bill = [] ∧ r.cost ≤ MM H * q.1.cost + 40 * t.nds + 40) (by
      rintro s - q hq ⟨h1, h2, h3, h4⟩
      obtain ⟨k, hk, o, h5⟩ := AZ_ev (θ := θ) q.2
      rw [← h3] at h5
      refine ⟨_, h5, ?_⟩
      have hn : q.2.nds = t.nds := Bt.nds_decAll (mem_simS hq).2
      by_cases hz : q.2.zero
      · simp only [hz, if_true]
        refine .cons ⟨?_, ?_, ?_⟩ .nil
        · simp [Run.det, h1]
        · simp [Run.det, h2]
        · simp only [Run.det]
          omega
      · simp only [hz]
        exact .nil)
  refine ⟨l4, e4, ?_, ?_⟩
  · intro r hr
    obtain ⟨q, hq, h1, h2, h3⟩ := forall₂_exists r4 hr
    refine ⟨h2, h3.trans ?_⟩
    rw [List.mem_flatMap] at hq
    obtain ⟨q', hq', hq⟩ := hq
    have : q = q' := by
      split_ifs at hq
      · simpa using hq
      · simp at hq
    subst this
    have := hT _ (mem_simS hq').1
    have := Nat.mul_le_mul_left (MM H) this
    omega
  · rw [← map_simS]
    clear e4
    generalize ((simS t l).flatMap fun q => if q.2.zero then [q] else []) = Q at r4
    induction r4 with
    | nil => rfl
    | cons h _ ih => simp [h.1, ih]

variable [Algebra A R]

/-- **Lemma 1 (postponing).** The value of a list of runs is the sum, over all budgets, of the powers of the constants
times the sums of the weights of the runs that use up the budgets. -/
theorem val_eq_sum_budg {J : ℕ} {K : KT R} {κ : List Bool → R} {l : List (Run A)}
    (hJ : ∀ r ∈ l, r.bill.length < 2 ^ J) (hκ : ∀ r ∈ l, ∀ p ∈ r.bill, κ p = K.lookup p) :
    val κ l = ((K.budg J).map fun q =>
      q.2 * algebraMap A R (l.map fun r => if ok q.1 r.bill = true then r.th else 0).sum).sum := by
  induction l with
  | nil => simp [val]
  | cons r l ih =>
    have h1 := ih (fun r hr => hJ r (List.mem_cons_of_mem _ hr)) fun r hr => hκ r (List.mem_cons_of_mem _ hr)
    have h2 := sum_budg J K r.bill (hJ r List.mem_cons_self)
    have h3 : (r.bill.map κ).prod = (r.bill.map K.lookup).prod := by
      congr 1
      exact List.map_congr_left fun p hp => hκ r List.mem_cons_self p hp
    have h4 : val κ (r :: l) = wt κ r + val κ l := by simp [val]
    rw [h4, h1, wt, h3, ← h2, ← List.sum_map_mul_left, ← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    simp only [List.map_cons, List.sum_cons, map_add, mul_add]
    congr 1
    by_cases h : ok q.1 r.bill = true
    · simp only [h, if_true]
      ring
    · simp [h]

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Guessing the budgets and multiplying by the powers of the constants
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R]

namespace KT

/-- The constants `c, c², c⁴, …` (`n` of them); the names are `0, 10, 110, …`. -/
def comb (c : R) : ℕ → KT R
  | 0 => none
  | n + 1 => node (leaf c) (comb (c ^ 2) n)

/-- The powers `c ^ (2 ^ b)`, `b < B`, of all constants. -/
def expand (B : ℕ) : KT R → KT R
  | none => none
  | leaf c => comb c B
  | node l r => node (l.expand B) (r.expand B)

/-- Names of the constants. -/
def Leaf : KT R → List Bool → Prop
  | none, _ => False
  | leaf _, p => p = []
  | node _ _, [] => False
  | node _ r, true :: p => r.Leaf p
  | node l _, false :: p => l.Leaf p

theorem Leaf.inB {K : KT R} {p : List Bool} (h : K.Leaf p) {b B : ℕ} (hb : b < B) : K.InB B (p ++ pw b) := by
  induction K generalizing p with
  | none => exact h.elim
  | leaf c =>
    have h : p = [] := h
    subst h
    exact ⟨b, hb, rfl⟩
  | node l r ihl ihr =>
    cases p with
    | nil => exact h.elim
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem pw_succ (b : ℕ) : pw (b + 1) = true :: pw b := rfl

theorem combVal_pw (c : R) (b : ℕ) : combVal c (pw b) = c ^ 2 ^ b := by
  induction b generalizing c with
  | zero => simp [pw, combVal]
  | succ b ih => rw [pw_succ, combVal, ih, ← pow_mul, pow_succ' 2 b]

theorem Leaf.lk {K : KT R} {p : List Bool} (h : K.Leaf p) : ∃ c, ∀ i, K.lk (p ++ pw i) = c ^ 2 ^ i := by
  induction K generalizing p with
  | none => exact h.elim
  | leaf c =>
    have h : p = [] := h
    subst h
    exact ⟨c, fun i => combVal_pw c i⟩
  | node l r ihl ihr =>
    cases p with
    | nil => exact h.elim
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem lookup_comb (c : R) {B b : ℕ} (h : b < B) : (comb c B).lookup (pw b) = combVal c (pw b) := by
  induction b generalizing c B with
  | zero =>
    cases B with
    | zero => omega
    | succ B => rfl
  | succ b ih =>
    cases B with
    | zero => omega
    | succ B =>
      rw [pw_succ, comb, lookup, combVal]
      exact ih _ (by omega)

theorem lookup_expand {B : ℕ} {K : KT R} {p : List Bool} (h : K.InB B p) : K.lk p = (K.expand B).lookup p := by
  induction K generalizing p with
  | none => exact h.elim
  | leaf c =>
    obtain ⟨b, hb, rfl⟩ := h
    rw [expand, lookup_comb c hb, lk]
  | node l r ihl ihr =>
    cases p with
    | nil => exact h.elim
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem InB.mono {B B' : ℕ} (hB : B ≤ B') {K : KT R} {p : List Bool} (h : K.InB B p) : K.InB B' p := by
  induction K generalizing p with
  | none => exact h
  | leaf c =>
    obtain ⟨b, hb, rfl⟩ := h
    exact ⟨b, lt_of_lt_of_le hb hB, rfl⟩
  | node l r ihl ihr =>
    cases p with
    | nil => exact h
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem nds_comb (c : R) (n : ℕ) : (comb c n).nds = 2 * n + 1 := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [comb, nds, ih]; omega

theorem nds_pos (K : KT R) : 0 < K.nds := by cases K <;> simp [nds]

theorem nds_expand (B : ℕ) (K : KT R) : (K.expand B).nds ≤ K.nds * (2 * B + 1) := by
  induction K with
  | none => simp [expand, nds]
  | leaf c => simp [expand, nds, nds_comb]
  | node l r ihl ihr =>
    simp only [expand, nds]
    nlinarith

theorem ht_comb (c : R) (n : ℕ) : (comb c n).ht ≤ n := by
  induction n generalizing c with
  | zero => exact le_rfl
  | succ n ih =>
    have := ih (c ^ 2)
    simp only [comb, ht]
    omega

theorem ht_expand (B : ℕ) (K : KT R) : (K.expand B).ht ≤ K.ht + B := by
  induction K with
  | none => simp [expand, ht]
  | leaf c =>
    have := ht_comb c B
    simp only [expand, ht]
    omega
  | node l r ihl ihr =>
    simp only [expand, ht]
    omega

theorem length_words {J : ℕ} {w : List Bool} (h : w ∈ words J) : w.length = J := by
  induction J generalizing w with
  | zero => simp [words] at h; simp [h]
  | succ J ih =>
    simp only [words, List.mem_flatMap, List.mem_map] at h
    obtain ⟨b, -, v, hv, rfl⟩ := h
    simp [ih hv]

theorem ht_budg {J : ℕ} {K : KT R} {q : Bt × R} (h : q ∈ K.budg J) : q.1.ht ≤ K.ht + J + 1 := by
  induction K generalizing q with
  | none =>
    simp only [budg, List.mem_singleton] at h
    subst h
    simp [Bt.ht]
  | leaf c =>
    simp only [budg, List.mem_map] at h
    obtain ⟨w, hw, rfl⟩ := h
    simp [Bt.ht, length_words hw, ht]
  | node l r ihl ihr =>
    simp only [budg, List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hp, q', hq, rfl⟩ := h
    have h1 := ihl hp
    have h2 := ihr hq
    simp only [Bt.ht, ht]
    omega

theorem nds_budg {J : ℕ} {K : KT R} {q : Bt × R} (h : q ∈ K.budg J) : q.1.nds ≤ K.nds * (J + 1) := by
  induction K generalizing q with
  | none =>
    simp only [budg, List.mem_singleton] at h
    subst h
    simp [Bt.nds, nds]
  | leaf c =>
    simp only [budg, List.mem_map] at h
    obtain ⟨w, hw, rfl⟩ := h
    simp [Bt.nds, length_words hw, nds]
  | node l r ihl ihr =>
    simp only [budg, List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hp, q', hq, rfl⟩ := h
    have h1 := ihl hp
    have h2 := ihr hq
    simp only [Bt.nds, nds]
    nlinarith

end KT

section Formulas

/-- Guess a bit; if it is 1, multiply by the constant with the name `p`. -/
def gbit (p : List Bool) : Fm := .ite .guess (.cons (.mul (.quote (ofBits p))) (.quote .nil)) (.quote .nil)

theorem gbit_ev (p : List Bool) (x : Tree) : Ev θ (gbit p) x [⟨3, 1, [], .nil⟩, ⟨6, 1, [p], one⟩] := by
  have h1 : Ev θ (.cons (.mul (.quote (ofBits p))) (.quote .nil)) x [⟨4, 1, [p], one⟩] := by
    have := Ev.cons (Ev.mul (Ev.quote (θ := θ) (ofBits p) x)) (Ev.quote .nil x)
    simpa [Run.det, Run.seq, Run.tick, one] using this
  have := Ev.ite (L := fun r => if r.out = .nil then [.det 1 .nil] else [⟨4, 1, [p], one⟩]) (Ev.guess (θ := θ) x)
    (b := .cons (.mul (.quote (ofBits p))) (.quote .nil)) (c := .quote .nil)
    (fun r _ h => by rw [if_neg h]; exact h1) (fun r _ h => by rw [if_pos h]; exact Ev.quote .nil x)
  simpa [Run.det, Run.seq, Run.tick, one, gbit] using this

/-- Guess the digits of a number; multiply by the powers of a constant. `ν i` is the exponent in the name that is
used for the power `2 ^ i`. -/
def gw (ν : ℕ → ℕ) (pre : List Bool) (b : ℕ) : ℕ → ℕ → Fm
  | _, 0 => .quote .nil
  | j, n + 1 => .cons (gbit (pre ++ KT.pw (ν (b + j)))) (gw ν pre b (j + 1) n)

/-- The budgets of the powers of a constant. -/
def gcomb (ν : ℕ → ℕ) (J : ℕ) (pre : List Bool) : ℕ → ℕ → Fm
  | _, 0 => .quote .nil
  | b, n + 1 => .cons (.cons (.cons (.quote .nil) (gw ν pre b 0 J)) (gcomb ν J pre (b + 1) n)) (.quote .nil)

/-- The budgets of all powers `2 ^ b`, `b < B`, of all constants. -/
def gt (ν : ℕ → ℕ) (J B : ℕ) : KT R → List Bool → Fm
  | .none, _ => .quote .nil
  | .leaf _, pre => gcomb ν J pre 0 B
  | .node l r, pre => .cons (.cons (gt ν J B l (pre ++ [false])) (gt ν J B r (pre ++ [true]))) (.quote .nil)

/-- A run that guesses a budget and multiplies by the powers of the constants. -/
structure RelG (κ : List Bool → R) (P : List Bool → Prop) (c : ℕ) (r : Run A) (q : Bt × R) : Prop where
  th : r.th = 1
  out : r.out = q.1.enc
  bill : (r.bill.map κ).prod = q.2
  names : ∀ p ∈ r.bill, P p
  cost : r.cost ≤ c

variable {κ : List Bool → R} {P : List Bool → Prop} {ν : ℕ → ℕ}

theorem gw_ev {pre : List Bool} {b : ℕ} {c : R} (x : Tree) {n j : ℕ}
    (h : ∀ i < j + n, κ (pre ++ KT.pw (ν (b + i))) = c ^ 2 ^ (b + i) ∧ P (pre ++ KT.pw (ν (b + i)))) :
    ∃ l, Ev θ (gw ν pre b j n) x l ∧ List.Forall₂ (fun r w => r.th = 1 ∧ r.out = ofBits w ∧
      (r.bill.map κ).prod = (c ^ 2 ^ (b + j)) ^ KT.val w ∧ (∀ p ∈ r.bill, P p) ∧ r.cost ≤ 8 * n + 1) l (KT.words n) := by
  induction n generalizing j with
  | zero => exact ⟨_, .quote .nil x, .cons ⟨rfl, rfl, by simp [Run.det, KT.val], by simp [Run.det], by simp [Run.det]⟩ .nil⟩
  | succ n ih =>
    obtain ⟨l, e, hl⟩ := ih (j := j + 1) (fun i hi => h i (by omega))
    obtain ⟨hκ, hP⟩ := h j (by omega)
    refine ⟨_, Ev.cons (gbit_ev _ x) e, ?_⟩
    simp only [KT.words, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine List.rel_append ?_ ?_
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine hl.imp fun r w hr => ?_
      obtain ⟨h1, h2, h3, h4, h5⟩ := hr
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [Run.seq, Run.tick, h1]
      · simp [Run.seq, Run.tick, h2, ofBits, bit]
      · simp only [Run.seq, Run.tick, List.nil_append, h3, KT.val, Bool.false_eq_true, if_false, zero_add, ← pow_mul]
        congr 1
        rw [← add_assoc, pow_succ]
        ring
      · simpa [Run.seq, Run.tick] using h4
      · simp only [Run.seq, Run.tick]
        omega
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine hl.imp fun r w hr => ?_
      obtain ⟨h1, h2, h3, h4, h5⟩ := hr
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [Run.seq, Run.tick, h1]
      · simp [Run.seq, Run.tick, h2, ofBits, bit]
      · simp only [Run.seq, Run.tick, List.singleton_append, List.map_cons, List.prod_cons, h3, hκ, KT.val, if_true,
          ← pow_mul, ← pow_add]
        congr 1
        rw [← add_assoc, pow_succ]
        ring
      · intro p hp
        simp only [Run.seq, Run.tick, List.singleton_append, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hP
        · exact h4 p hp
      · simp only [Run.seq, Run.tick]
        omega

theorem node_rel {f g : Fm} {x : Tree} {lf lg : List (Run A)} {Qf Qg : List (Bt × R)} {cf cg : ℕ}
    (hf : Ev θ f x lf) (hg : Ev θ g x lg) (rf : List.Forall₂ (RelG κ P cf) lf Qf)
    (rg : List.Forall₂ (RelG κ P cg) lg Qg) : ∃ l, Ev θ (.cons (.cons f g) (.quote .nil)) x l ∧
      List.Forall₂ (RelG κ P (cf + cg + 3)) l
        (Qf.flatMap fun p => Qg.map fun q => (Bt.node p.1 q.1, p.2 * q.2)) := by
  refine ⟨_, Ev.cons (Ev.cons hf hg) (Ev.quote .nil x), ?_⟩
  rw [List.flatMap_assoc]
  refine forall₂_flatMap rf fun r _ p _ hr => ?_
  have e : ((lg.map fun s => (r.seq s).tick (.cons r.out s.out)).flatMap fun u =>
      [Run.det 1 Tree.nil].map fun s => (u.seq s).tick (.cons u.out s.out)) =
      lg.map fun s => ((r.seq s).tick (.cons r.out s.out)).seq (.det 1 .nil) |>.tick (.cons (.cons r.out s.out) .nil) := by
    rw [List.flatMap_map]
    simp only [List.map_cons, List.map_nil]
    exact flatMap_single _ _
  rw [e, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine rg.imp fun s q hs => ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Run.seq, Run.tick, Run.det, hr.th, hs.th]
  · simp [Run.tick, hr.out, hs.out, Bt.enc]
  · simp [Run.seq, Run.tick, Run.det, hr.bill, hs.bill]
  · intro p hp
    simp only [Run.seq, Run.tick, Run.det, List.append_nil, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hr.names p hp
    · exact hs.names p hp
  · have h1 := hr.cost
    have h2 := hs.cost
    simp only [Run.seq, Run.tick, Run.det]
    omega

theorem gcomb_ev {J : ℕ} {pre : List Bool} {c : R} (x : Tree) {n b : ℕ}
    (h : ∀ i < b + n + J, κ (pre ++ KT.pw (ν i)) = c ^ 2 ^ i ∧ P (pre ++ KT.pw (ν i))) :
    ∃ l, Ev θ (gcomb ν J pre b n) x l ∧
      List.Forall₂ (RelG κ P ((8 * J + 10) * n + 1)) l ((KT.comb (c ^ 2 ^ b) n).budg J) := by
  induction n generalizing b with
  | zero =>
    refine ⟨_, .quote .nil x, .cons ⟨rfl, rfl, ?_, ?_, ?_⟩ .nil⟩ <;> simp [Run.det]
  | succ n ih =>
    obtain ⟨lg, eg, rg⟩ := ih (b := b + 1) (fun i hi => h i (by omega))
    obtain ⟨lw, ew, rw'⟩ := gw_ev (θ := θ) (κ := κ) (P := P) (ν := ν) (pre := pre) (b := b) (c := c) x (n := J) (j := 0)
      (fun i hi => h (b + i) (by omega))
    have ef := Ev.cons (Ev.quote (θ := θ) .nil x) ew
    have rf : List.Forall₂ (RelG κ P (8 * J + 3)) ([Run.det 1 Tree.nil].flatMap fun r => lw.map fun s =>
        (r.seq s).tick (.cons r.out s.out)) ((KT.leaf (c ^ 2 ^ b)).budg J) := by
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, KT.budg]
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine rw'.imp fun r w hr => ?_
      obtain ⟨h1, h2, h3, h4, h5⟩ := hr
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [Run.seq, Run.tick, Run.det, h1]
      · simp [Run.tick, Run.det, h2, Bt.enc]
      · simpa [Run.seq, Run.tick, Run.det] using h3
      · simpa [Run.seq, Run.tick, Run.det] using h4
      · simp only [Run.seq, Run.tick, Run.det]
        omega
    obtain ⟨l, e, r⟩ := node_rel ef eg rf rg
    refine ⟨l, e, ?_⟩
    have hc : (c ^ 2 ^ b) ^ 2 = c ^ 2 ^ (b + 1) := by rw [← pow_mul, ← pow_succ]
    simp only [KT.comb, KT.budg, hc] at r ⊢
    refine r.imp fun s q hs => ⟨hs.th, hs.out, hs.bill, hs.names, hs.cost.trans ?_⟩
    ring_nf
    omega

/-- Runs of `gt` = budgets. The hypothesis: the names that are used name the right powers. -/
theorem gt_ev {J B : ℕ} (x : Tree) (K : KT R) (pre : List Bool)
    (h : ∀ p, K.Leaf p → ∀ i < B + J,
      κ (pre ++ (p ++ KT.pw (ν i))) = K.lk (p ++ KT.pw i) ∧ P (pre ++ (p ++ KT.pw (ν i)))) :
    ∃ l, Ev θ (gt ν J B K pre) x l ∧
      List.Forall₂ (RelG κ P ((8 * J + 10) * (K.expand B).nds)) l ((K.expand B).budg J) := by
  induction K generalizing pre with
  | none =>
    refine ⟨_, .quote .nil x, .cons ⟨rfl, rfl, ?_, ?_, ?_⟩ .nil⟩
    · simp [Run.det]
    · simp [Run.det]
    · simp [Run.det, KT.expand, KT.nds]
  | leaf c =>
    have h' : ∀ i < B + J, κ (pre ++ KT.pw (ν i)) = c ^ 2 ^ i ∧ P (pre ++ KT.pw (ν i)) := by
      intro i hi
      have := h [] rfl i hi
      simpa [KT.lk, KT.combVal_pw] using this
    obtain ⟨l, e, r⟩ := gcomb_ev (θ := θ) (J := J) (pre := pre) (c := c) x (n := B) (b := 0)
      (fun i hi => h' i (by omega))
    refine ⟨l, e, ?_⟩
    simp only [pow_zero, pow_one] at r
    refine r.imp fun s q hs => ⟨hs.th, hs.out, hs.bill, hs.names, hs.cost.trans ?_⟩
    simp only [KT.expand, KT.nds_comb]
    nlinarith
  | node l r ihl ihr =>
    obtain ⟨ll, el, rl⟩ := ihl (pre ++ [false]) (fun p hp i hi => by
      have := h (false :: p) hp i hi
      simpa [KT.lk] using this)
    obtain ⟨lr, er, rr⟩ := ihr (pre ++ [true]) (fun p hp i hi => by
      have := h (true :: p) hp i hi
      simpa [KT.lk] using this)
    obtain ⟨l', e', r'⟩ := node_rel el er rl rr
    refine ⟨l', e', r'.imp fun s q hs => ⟨hs.th, hs.out, hs.bill, hs.names, hs.cost.trans ?_⟩⟩
    simp only [KT.expand, KT.nds]
    nlinarith

end Formulas

section Sizes

theorem size_num (k : ℕ) : (num k).size = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [num, Tree.size, ih]; omega

theorem size_gw (ν : ℕ → ℕ) (pre : List Bool) (b N : ℕ) (n j : ℕ) (h : ∀ i < j + n, ν (b + i) ≤ N) :
    (gw ν pre b j n).code.size ≤ n * (4 * (pre.length + N) + 100) + 4 := by
  induction n generalizing j with
  | zero => simp [gw, Fm.code, Tree.size, size_num]
  | succ n ih =>
    have h1 := ih (j + 1) (fun i hi => h i (by omega))
    have h2 := size_ofBits (pre ++ KT.pw (ν (b + j)))
    have h3 := h j (by omega)
    simp only [KT.pw, List.length_append, List.length_replicate, List.length_singleton] at h2
    simp only [gw, gbit, Fm.code, Tree.size, size_num, KT.pw]
    nlinarith

theorem size_gcomb (ν : ℕ → ℕ) (J : ℕ) (pre : List Bool) (N : ℕ) (n b : ℕ) (h : ∀ i < b + n + J, ν i ≤ N) :
    (gcomb ν J pre b n).code.size ≤ n * ((J + 1) * (4 * (pre.length + N) + 100)) + 4 := by
  induction n generalizing b with
  | zero => simp [gcomb, Fm.code, Tree.size, size_num]
  | succ n ih =>
    have h1 := ih (b + 1) (fun i hi => h i (by omega))
    have h2 := size_gw ν pre b N J 0 (fun i hi => h _ (by omega))
    simp only [gcomb, Fm.code, Tree.size, size_num]
    nlinarith

theorem size_gt (ν : ℕ → ℕ) (J B : ℕ) (K : KT R) (pre : List Bool) (N : ℕ) (h : ∀ i < B + J, ν i ≤ N) :
    (gt ν J B K pre).code.size ≤ (K.expand B).nds * ((J + 1) * (4 * (pre.length + K.ht + N) + 100)) := by
  induction K generalizing pre with
  | none =>
    simp only [gt, Fm.code, Tree.size, size_num, KT.expand, KT.nds, KT.ht]
    nlinarith
  | leaf c =>
    have h1 := size_gcomb ν J pre N B 0 (fun i hi => h i (by omega))
    simp only [gt, KT.expand, KT.nds_comb, KT.ht, add_zero] at h1 ⊢
    refine h1.trans ?_
    have : 100 ≤ (J + 1) * (4 * (pre.length + N) + 100) := by nlinarith
    nlinarith
  | node l r ihl ihr =>
    have h1 := ihl (pre ++ [false])
    have h2 := ihr (pre ++ [true])
    simp only [List.length_append, List.length_singleton] at h1 h2
    simp only [gt, Fm.code, Tree.size, size_num, KT.expand, KT.nds, KT.ht]
    have e1 : (J + 1) * (4 * (pre.length + 1 + l.ht + N) + 100) ≤
        (J + 1) * (4 * (pre.length + (max l.ht r.ht + 1) + N) + 100) := by
      apply Nat.mul_le_mul_left
      have := le_max_left l.ht r.ht
      omega
    have e2 : (J + 1) * (4 * (pre.length + 1 + r.ht + N) + 100) ≤
        (J + 1) * (4 * (pre.length + (max l.ht r.ht + 1) + N) + 100) := by
      apply Nat.mul_le_mul_left
      have := le_max_right l.ht r.ht
      omega
    have e3 : 100 ≤ (J + 1) * (4 * (pre.length + (max l.ht r.ht + 1) + N) + 100) := by nlinarith
    have e4 := h1.trans (Nat.mul_le_mul_left _ e1)
    have e5 := h2.trans (Nat.mul_le_mul_left _ e2)
    nlinarith

end Sizes

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# One round

A program that guesses budgets, multiplies by the powers of the constants, forms a plain instance, cuts it into
pieces, and applies a given program to every piece.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R] {κ : List Bool → R}

section Values

theorem wt_seq (r s : Run A) : wt κ (r.seq s) = wt κ r * wt κ s := by
  simp only [wt, Run.seq, map_mul, List.map_append, List.prod_append]
  ring

theorem wt_tick (r : Run A) (o : Tree) : wt κ (r.tick o) = wt κ r := rfl

theorem wt_delay (k : ℕ) (r : Run A) : wt κ (r.delay k) = wt κ r := rfl

theorem wt_det (k : ℕ) (o : Tree) : wt κ (Run.det k o : Run A) = 1 := by simp [wt, Run.det]

/-- Sums over runs, with a function of the value. -/
def sumF (κ : List Bool → R) (l : List (Run A)) (f : Tree → R) : R := (l.map fun r => wt κ r * f r.out).sum

theorem val_eq_sumF (l : List (Run A)) : val κ l = sumF κ l fun _ => 1 := by simp [val, sumF]

theorem sumF_delay (k : ℕ) (l : List (Run A)) (f : Tree → R) : sumF κ (l.map (Run.delay k)) f = sumF κ l f := by
  simp only [sumF, List.map_map]
  rfl

theorem sum_rel {β : Type*} {l : List (Run A)} {Q : List β} {c : β → R} {o : β → Tree} {f : Tree → R}
    (h : List.Forall₂ (fun r q => wt κ r = c q ∧ r.out = o q) l Q) :
    sumF κ l f = (Q.map fun q => c q * f (o q)).sum := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    simp only [sumF, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, h.1, h.2]

end Values

section App

/-- Apply a fixed program. -/
def app (p : Tree) (e : Fm) : Fm := .run (.quote p) e

theorem Ev.app {p x : Tree} {e : Fm} {le : List (Run A)} (he : Ev θ e x le)
    (h : ∀ s ∈ le, Hl θ (Fm.ofTree p) s.out) : Ev θ (app p e) x
      (le.flatMap fun s => (NS1.evl θ (Fm.ofTree p) s.out).map fun t => ((Run.det 1 p).seq s).seq t |>.tick t.out) := by
  have := Ev.run' (Dt.quote (θ := θ) p x) he (fun r hr s hs => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact h s hs)
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
  exact this

theorem sumF_app {p : Tree} {le : List (Run A)} {f : Tree → R} :
    sumF κ (le.flatMap fun s => (NS1.evl θ (Fm.ofTree p) s.out).map fun t =>
      ((Run.det 1 p).seq s).seq t |>.tick t.out) f = sumF κ le fun o => sumF κ (NS1.evl θ (Fm.ofTree p) o) f := by
  simp only [sumF]
  rw [sum_flatMap_map]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  show wt κ (((Run.det 1 p).seq s).seq t) * f t.out = wt κ s * (wt κ t * f t.out)
  rw [wt_seq, wt_seq, wt_det, one_mul, mul_assoc]

theorem mem_app {p : Tree} {le : List (Run A)} {u : Run A}
    (h : u ∈ le.flatMap fun s => (NS1.evl θ (Fm.ofTree p) s.out).map fun t =>
      ((Run.det 1 p).seq s).seq t |>.tick t.out) :
    ∃ s ∈ le, ∃ t ∈ NS1.evl θ (Fm.ofTree p) s.out, u.cost = s.cost + t.cost + 2 ∧ u.bill = s.bill ++ t.bill ∧
      u.out = t.out ∧ u.th = s.th * t.th := by
  rw [List.mem_flatMap] at h
  obtain ⟨s, hs, h⟩ := h
  rw [List.mem_map] at h
  obtain ⟨t, ht, rfl⟩ := h
  refine ⟨s, hs, t, ht, ?_, ?_, rfl, ?_⟩
  · simp only [Run.seq, Run.tick, Run.det]
    omega
  · simp [Run.seq, Run.tick, Run.det]
  · simp [Run.seq, Run.tick, Run.det]

end App

section Loop

/-- Apply the program `D` to all trees of a list. The argument is (this program, the list). -/
def LP (D : Tree) : Fm := .ite (.tl .id)
  (.cons (.run (.quote D) (.hd (.tl .id))) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) (.quote .nil)

theorem LP_ev {D : Tree} {T : ℕ} {P : List Bool → Prop} (ys : Tree) (h : ∀ y ∈ ys.toList, Hl θ (Fm.ofTree D) y ∧
    ∀ r ∈ evl θ (Fm.ofTree D) y, r.cost ≤ T ∧ ∀ p ∈ r.bill, P p) :
    ∃ l, Ev θ (LP D) (.cons (LP D).code ys) l ∧
      (∀ r ∈ l, r.cost ≤ (T + 30) * ys.toList.length + 10 ∧ ∀ p ∈ r.bill, P p) ∧
      val κ l = (ys.toList.map fun y => val κ (evl θ (Fm.ofTree D) y)).prod := by
  induction ys with
  | nil =>
    refine ⟨_, Dt.ite_false (.tl (.id _)) (.quote _ _), ?_, ?_⟩
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      simp [Run.det]
    · simp [val, wt_det, toList]
  | cons a ys _ ih =>
    obtain ⟨lr, er, hr, vr⟩ := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    obtain ⟨ha, ha'⟩ := h a List.mem_cons_self
    have e1 := Ev.run_det (Dt.quote (θ := θ) D (.cons (LP D).code (.cons a ys))) (.hd (.tl (.id _))) ha.ev
    have er' : Ev θ (Fm.ofTree (LP D).code) (.cons (LP D).code ys) lr := by rwa [Fm.ofTree_code]
    have e2 := Ev.run_det (Dt.hd (Dt.id (θ := θ) (.cons (LP D).code (.cons a ys)))) (.cons (.hd (.id _))
      (.tl (.tl (.id _)))) er'
    refine ⟨_, Ev.ite_true (.tl (.id _)) (by simp) (Ev.cons e1 e2), ?_, ?_⟩
    · intro r hr0
      simp only [List.mem_map, List.mem_flatMap] at hr0
      obtain ⟨_, ⟨_, ⟨r1, hr1, rfl⟩, ⟨_, ⟨r2, hr2, rfl⟩, rfl⟩⟩, rfl⟩ := hr0
      obtain ⟨c1, p1⟩ := ha' r1 hr1
      obtain ⟨c2, p2⟩ := hr r2 hr2
      refine ⟨?_, ?_⟩
      · simp only [Run.delay, Run.seq, Run.tick, toList, List.length_cons]
        nlinarith
      · intro p hp
        simp only [Run.delay, Run.seq, Run.tick, List.mem_append] at hp
        rcases hp with hp | hp
        · exact p1 p hp
        · exact p2 p hp
    · rw [val_eq_sumF, sumF_delay, toList, List.map_cons, List.prod_cons, ← vr]
      simp only [sumF, mul_one]
      rw [sum_flatMap_map, List.map_map]
      simp only [List.map_map, Function.comp_def, wt_tick, wt_seq, wt_delay]
      simp only [List.sum_map_mul_left]
      rw [List.sum_map_mul_right]
      rfl

end Loop

section Inst

/-- The plain instance for a program `p`, an argument `z` and budgets `t`. -/
def zq (p z : Tree) (t : Bt) : Tree := .cons WF.code (.cons p (.cons z t.enc))

/-- Form the plain instance: `fp` gives the program, `g` guesses the budgets. -/
def ZE (fp g : Fm) : Fm := .cons (.quote WF.code) (.cons fp (.cons .id g))

theorem ZE_ev {fp g : Fm} {p z : Tree} {k cg : ℕ} {P : List Bool → Prop} {lg : List (Run A)} {Q : List (Bt × R)}
    (hp : Dt θ fp z p k) (hg : Ev θ g z lg) (rg : List.Forall₂ (RelG κ P cg) lg Q) :
    ∃ l, Ev θ (ZE fp g) z l ∧ List.Forall₂ (fun r q => wt κ r = q.2 ∧ r.out = zq p z q.1 ∧ (∀ n ∈ r.bill, P n) ∧
      r.cost ≤ cg + k + 5) l Q := by
  refine ⟨_, Ev.cons (Dt.quote _ _) (Ev.cons hp (Ev.cons (Dt.id _) hg)), ?_⟩
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.forall₂_map_left_iff]
  refine rg.imp fun r q hr => ⟨?_, ?_, ?_, ?_⟩
  · rw [wt_tick, wt_seq, wt_tick, wt_seq, wt_tick, wt_seq, wt_det, wt_det, wt_det]
    simp [wt, hr.th, hr.bill]
  · simp [Run.tick, Run.det, hr.out, zq]
  · simpa [Run.seq, Run.tick, Run.det] using hr.names
  · have := hr.cost
    simp only [Run.seq, Run.tick, Run.det]
    omega

/-- One round: guess budgets, multiply, form the plain instance, cut it with `G`, apply `D` to the pieces. -/
def stepF (D G p : Tree) (g : Fm) : Fm :=
  app (LP D).code (.cons (.quote (LP D).code) (app G (ZE (.quote p) g)))

theorem stepF_ev {D G p z : Tree} {g : Fm} {cg tG tD Ln : ℕ} {P : List Bool → Prop} {lg : List (Run A)}
    {Q : List (Bt × R)} (hg : Ev θ g z lg) (rg : List.Forall₂ (RelG κ P cg) lg Q)
    (hG : ∀ q ∈ Q, Hl θ (Fm.ofTree G) (zq p z q.1) ∧ ∀ r ∈ evl θ (Fm.ofTree G) (zq p z q.1), r.bill = [] ∧
      r.cost ≤ tG ∧ r.out.toList.length ≤ Ln ∧ ∀ y ∈ r.out.toList, Hl θ (Fm.ofTree D) y ∧
        ∀ r ∈ evl θ (Fm.ofTree D) y, r.cost ≤ tD ∧ ∀ n ∈ r.bill, P n) :
    ∃ l, Ev θ (stepF D G p g) z l ∧
      (∀ r ∈ l, r.cost ≤ cg + tG + (tD + 30) * Ln + 30 ∧ ∀ n ∈ r.bill, P n) ∧
      val κ l = (Q.map fun q => q.2 * sumF κ (evl θ (Fm.ofTree G) (zq p z q.1)) fun o =>
        (o.toList.map fun y => val κ (evl θ (Fm.ofTree D) y)).prod).sum := by
  obtain ⟨lZ, eZ, rZ⟩ := ZE_ev (Dt.quote p z) hg rg
  have hZ : ∀ s ∈ lZ, ∃ q ∈ Q, wt κ s = q.2 ∧ s.out = zq p z q.1 ∧ (∀ n ∈ s.bill, P n) ∧ s.cost ≤ cg + 1 + 5 :=
    fun s hs => forall₂_exists rZ hs
  have eG := Ev.app (p := G) eZ fun s hs => by
    obtain ⟨q, hq, -, h, -⟩ := hZ s hs
    rw [h]
    exact (hG q hq).1
  set lG := lZ.flatMap fun s => (evl θ (Fm.ofTree G) s.out).map fun t => ((Run.det 1 G).seq s).seq t |>.tick t.out
    with hlG
  have hmem : ∀ u ∈ lG, u.out.toList.length ≤ Ln ∧ (∀ y ∈ u.out.toList, Hl θ (Fm.ofTree D) y ∧
      ∀ r ∈ evl θ (Fm.ofTree D) y, r.cost ≤ tD ∧ ∀ n ∈ r.bill, P n) ∧ u.cost ≤ cg + tG + 8 ∧ ∀ n ∈ u.bill, P n := by
    intro u hu
    obtain ⟨s, hs, t, ht, h1, h2, h3, -⟩ := mem_app hu
    obtain ⟨q, hq, -, h4, h5, h6⟩ := hZ s hs
    rw [h4] at ht
    obtain ⟨g1, g2, g3, g4⟩ := (hG q hq).2 t ht
    refine ⟨by rw [h3]; exact g3, by rw [h3]; exact g4, by omega, ?_⟩
    rw [h2, g1, List.append_nil]
    exact h5
  have eC := Ev.cons (Dt.quote (θ := θ) (LP D).code z) eG
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at eC
  have hLP : ∀ u ∈ lG, ∃ l, Ev θ (LP D) (.cons (LP D).code u.out) l ∧
      (∀ r ∈ l, r.cost ≤ (tD + 30) * u.out.toList.length + 10 ∧ ∀ p ∈ r.bill, P p) ∧
      val κ l = (u.out.toList.map fun y => val κ (evl θ (Fm.ofTree D) y)).prod := fun u hu =>
    LP_ev u.out (hmem u hu).2.1
  have eL := Ev.app (p := (LP D).code) eC fun s hs => by
    rw [List.mem_map] at hs
    obtain ⟨u, hu, rfl⟩ := hs
    rw [Fm.ofTree_code]
    obtain ⟨l, hl, -⟩ := hLP u hu
    exact hl.hl
  refine ⟨_, eL, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, t, ht, h1, h2, -, -⟩ := mem_app hr
    rw [List.mem_map] at hs
    obtain ⟨u, hu, rfl⟩ := hs
    rw [Fm.ofTree_code] at ht
    obtain ⟨l, hl, hl2, -⟩ := hLP u hu
    have ht' : t ∈ l := by
      have := hl.evl
      rw [← this]
      exact ht
    obtain ⟨m1, m2, m3, m4⟩ := hmem u hu
    obtain ⟨c1, p1⟩ := hl2 t ht'
    have := Nat.mul_le_mul_left (tD + 30) m1
    refine ⟨?_, ?_⟩
    · simp only [Run.seq, Run.tick, Run.det] at h1
      omega
    · intro n hn
      rw [h2] at hn
      simp only [Run.seq, Run.tick, Run.det, List.nil_append, List.mem_append] at hn
      rcases hn with hn | hn
      · exact m4 n hn
      · exact p1 n hn
  · rw [val_eq_sumF, sumF_app]
    have s1 : sumF κ (lG.map fun s => ((Run.det 1 (LP D).code).seq s).tick (.cons (Run.det 1 (LP D).code : Run A).out s.out))
        (fun o => sumF κ (evl θ (Fm.ofTree (LP D).code) o) fun _ => 1) =
        sumF κ lG fun o => (o.toList.map fun y => val κ (evl θ (Fm.ofTree D) y)).prod := by
      simp only [sumF, List.map_map, Function.comp_def]
      congr 1
      refine List.map_congr_left fun u hu => ?_
      obtain ⟨l, hl, -, hl3⟩ := hLP u hu
      rw [← hl3, wt_tick, wt_seq, wt_det, one_mul, Fm.ofTree_code]
      congr 1
      have e : (((Run.det 1 (LP D).code).seq u).tick (.cons (Run.det 1 (LP D).code : Run A).out u.out)).out =
          .cons (LP D).code u.out := rfl
      rw [e, hl.evl, val_eq_sumF, sumF]
    rw [s1, hlG, sumF_app]
    exact sum_rel (c := fun q : Bt × R => q.2) (o := fun q : Bt × R => zq p z q.1)
      (rZ.imp fun r q hr => ⟨hr.1, hr.2.1⟩)

end Inst

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Accelerators, the cut

Scales are `v ^ H` (`H = 16 / η`). `pv θ z` is the universal plain sum at `z = (program, argument)`.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {R : Type} [CommRing R] [Algebra A R]

/-- A program `G` that cuts plain sums of `τ` steps on instances of size `s` into pieces of `v ^ H` steps. Its values
are lists of instances. -/
structure CutProg (θ : List Bool → A) (H v τ s : ℕ) (G : Tree) : Prop where
  size : G.size ≤ v ^ H
  list : ∀ z, z.size ≤ s → Hl θ (Fm.ofTree G) z ∧ ∀ r ∈ evl θ (Fm.ofTree G) z, r.bill = [] ∧ r.cost * v ^ 24 ≤ τ ∧
    r.out.toList.length * v ^ H ≤ τ * v ^ 2 ∧ ∀ y ∈ r.out.toList, y.size ≤ v ^ (H - 32)
  val : ∀ z, z.size ≤ s → Plain θ τ z →
    (∀ r ∈ evl θ (Fm.ofTree G) z, ∀ y ∈ r.out.toList, Plain θ (v ^ H) y) ∧
    pv θ z = ((evl θ (Fm.ofTree G) z).map fun r => r.th * (r.out.toList.map (pv θ)).prod).sum

/-- **Theorem C (the cut, at all scales)**, as a property of the ring and its constants. -/
def CutHyp (θ : List Bool → A) (H C₀ v₀ : ℕ) : Prop :=
  ∀ v, v₀ ≤ v → ∀ α τ s, lg v ^ (C₀ * α) ≤ v → v ^ H ≤ τ → τ ≤ v ^ (H * α) → s * v ^ 48 ≤ τ →
    ∃ G, CutProg θ H v τ s G

/-- The program `D`, with the constants `K` and their powers `2 ^ b`, `b < B`, has the values of all universal plain
sums of `v ^ H` steps on instances of size `v ^ (H - 32)`, in `t` steps. -/
structure IsAccT (θ : List Bool → A) (H v t : ℕ) (K : KT R) (B : ℕ) (D : Tree) : Prop where
  run : ∀ z, z.size ≤ v ^ (H - 32) → Hl θ (Fm.ofTree D) z ∧ ∀ r ∈ evl θ (Fm.ofTree D) z, r.cost ≤ t ∧
    ∀ p ∈ r.bill, K.InB B p
  val : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
    val K.lk (evl θ (Fm.ofTree D) z) = algebraMap A R (pv θ z)

/-- The same, where runs have to stop only if the sum is plain. -/
structure IsPre (θ : List Bool → A) (H v t : ℕ) (K : KT R) (B : ℕ) (D : Tree) : Prop where
  run : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z → Hl θ (Fm.ofTree D) z ∧
    ∀ r ∈ evl θ (Fm.ofTree D) z, r.cost ≤ t ∧ ∀ p ∈ r.bill, K.InB B p
  val : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
    val K.lk (evl θ (Fm.ofTree D) z) = algebraMap A R (pv θ z)

variable {θ : List Bool → A}

theorem IsAccT.pre {H v t : ℕ} {K : KT R} {B : ℕ} {D : Tree} (h : IsAccT θ H v t K B D) : IsPre θ H v t K B D :=
  ⟨fun z hz _ => h.run z hz, h.val⟩

theorem IsPre.mono {H v t t' : ℕ} {K : KT R} {B B' : ℕ} {D : Tree} (h : IsPre θ H v t K B D) (ht : t ≤ t')
    (hB : B ≤ B') : IsPre θ H v t' K B' D :=
  ⟨fun z hz hp => ⟨(h.run z hz hp).1, fun r hr => ⟨((h.run z hz hp).2 r hr).1.trans ht, fun p hp' =>
    (((h.run z hz hp).2 r hr).2 p hp').mono hB⟩⟩, h.val⟩

theorem IsAccT.mono {H v t t' : ℕ} {K : KT R} {B B' : ℕ} {D : Tree} (h : IsAccT θ H v t K B D) (ht : t ≤ t')
    (hB : B ≤ B') : IsAccT θ H v t' K B' D :=
  ⟨fun z hz => ⟨(h.run z hz).1, fun r hr => ⟨((h.run z hz).2 r hr).1.trans ht, fun p hp' =>
    (((h.run z hz).2 r hr).2 p hp').mono hB⟩⟩, h.val⟩

/-- A run wants at most one constant a step. -/
theorem bill_le {F : Fm} {x : Tree} {l : List (Run A)} (h : Ev θ F x l) : ∀ r ∈ l, r.bill.length ≤ r.cost := by
  induction h with
  | quote c x => simp [Run.det]
  | id x => simp [Run.det]
  | hd _ ih =>
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Run.tick]
    exact fun r hr => Nat.le_succ_of_le (ih r hr)
  | tl _ ih =>
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Run.tick]
    exact fun r hr => Nat.le_succ_of_le (ih r hr)
  | cons _ _ iha ihb =>
    intro r hr
    simp only [List.mem_flatMap, List.mem_map] at hr
    obtain ⟨r1, h1, r2, h2, rfl⟩ := hr
    have := iha r1 h1
    have := ihb r2 h2
    simp only [Run.tick, Run.seq, List.length_append]
    omega
  | ite _ _ _ iha ihb ihc =>
    intro r hr
    simp only [List.mem_flatMap, List.mem_map] at hr
    obtain ⟨r1, h1, r2, h2, rfl⟩ := hr
    have := iha r1 h1
    have : r2.bill.length ≤ r2.cost := by
      by_cases h : r1.out = .nil
      · exact ihc r1 h1 h r2 h2
      · exact ihb r1 h1 h r2 h2
    simp only [Run.tick, Run.seq, List.length_append]
    omega
  | run _ _ _ iha ihb ih =>
    intro r hr
    simp only [List.mem_flatMap, List.mem_map] at hr
    obtain ⟨r1, h1, r2, h2, r3, h3, rfl⟩ := hr
    have := iha r1 h1
    have := ihb r2 h2
    have := ih r1 h1 r2 h2 r3 h3
    simp only [Run.tick, Run.seq, List.length_append]
    omega
  | guess x => simp [Run.det]
  | fail x => simp
  | theta _ ih =>
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun r hr => Nat.le_succ_of_le (ih r hr)
  | mul _ ih =>
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, List.length_append,
      List.length_singleton]
    exact fun r hr => Nat.succ_le_succ (ih r hr)

/-- The universal program. -/
def UF : Fm := .run (.hd .id) (.tl .id)

theorem UF_ev {z : Tree} {l : List (Run A)} (h : Ev θ (Fm.ofTree z.hd) z.tl l) :
    Ev θ UF z (l.map (Run.delay 5)) := Ev.run_det (Dt.hd (Dt.id z)) (Dt.tl (Dt.id z)) h

theorem val_plain {κ : List Bool → R} {l : List (Run A)} (h : ∀ r ∈ l, r.bill = []) :
    val κ l = algebraMap A R (pval l) := by
  rw [val, pval, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun r hr => ?_
  simp [wt, h r hr]

/-- The universal program is a program for the universal plain sums. -/
theorem UF_pre (θ : List Bool → A) (H v : ℕ) (K : KT R) (B : ℕ) : IsPre θ H v (v ^ H + 5) K B UF.code := by
  constructor
  · intro z _ hp
    have e := UF_ev hp.1.ev
    rw [Fm.ofTree_code]
    refine ⟨e.hl, fun r hr => ?_⟩
    rw [e.evl, List.mem_map] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    obtain ⟨h1, h2⟩ := hp.2 s hs
    refine ⟨?_, ?_⟩
    · simp only [Run.delay]
      omega
    · simp [Run.delay, h1]
  · intro z _ hp
    have e := UF_ev hp.1.ev
    rw [Fm.ofTree_code, e.evl, val_plain]
    · congr 1
      simp [pval, pv, Function.comp_def, Run.delay]
    · intro r hr
      rw [List.mem_map] at hr
      obtain ⟨s, hs, rfl⟩ := hr
      exact (hp.2 s hs).1

/-- The instances that arise from budgets are plain, and their sums are those of the runs that use up the budgets. -/
theorem zq_plain {p z : Tree} {l : List (Run A)} (h : Ev θ (Fm.ofTree p) z l) {T H τ : ℕ} (hT : ∀ r ∈ l, r.cost ≤ T)
    {t : Bt} (ht : t.ht ≤ H) (hτ : MM H * T + 40 * t.nds + 40 ≤ τ) : Plain θ τ (zq p z t) ∧
      pv θ (zq p z t) = (l.map fun r => if ok t r.bill = true then r.th else 0).sum ∧
      (evl θ (Fm.ofTree (zq p z t).hd) (zq p z t).tl).map Run.th = (l.filter fun r => ok t r.bill).map Run.th := by
  obtain ⟨l', e, h1, h2⟩ := WF_ev h hT ht
  have e' : Ev θ (Fm.ofTree (zq p z t).hd) (zq p z t).tl l' := by
    show Ev θ (Fm.ofTree WF.code) _ l'
    rw [Fm.ofTree_code]
    exact e
  refine ⟨⟨e'.hl, fun r hr => ?_⟩, ?_, by rw [e'.evl, h2]⟩
  · rw [e'.evl] at hr
    exact ⟨(h1 r hr).1, (h1 r hr).2.trans hτ⟩
  · rw [pv, e'.evl, pval, h2, sum_filter_th]

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Weighted functions computed by formulas

`Does θ F x Q c`: all runs of the formula `F` at the tree `x` stop, they use no named constants, the accepting ones
have cost at most `c`, and for every function of the value their weighted sum is that of the list `Q` of pairs
(weight, value).
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- Weighted sums over a list of pairs (weight, value). -/
def wsum (Q : List (A × Tree)) (φ : Tree → A) : A := (Q.map fun q => q.1 * φ q.2).sum

@[simp] theorem wsum_nil (φ : Tree → A) : wsum ([] : List (A × Tree)) φ = 0 := rfl

@[simp] theorem wsum_cons (q : A × Tree) (Q : List (A × Tree)) (φ : Tree → A) :
    wsum (q :: Q) φ = q.1 * φ q.2 + wsum Q φ := by simp [wsum]

theorem wsum_append (Q Q' : List (A × Tree)) (φ : Tree → A) : wsum (Q ++ Q') φ = wsum Q φ + wsum Q' φ := by
  simp [wsum]

theorem wsum_congr {Q : List (A × Tree)} {φ φ' : Tree → A} (h : ∀ q ∈ Q, φ q.2 = φ' q.2) : wsum Q φ = wsum Q φ' := by
  unfold wsum
  congr 1
  exact List.map_congr_left fun q hq => by rw [h q hq]

/-- First `Q`, then `R` at the value. -/
def bindW (Q : List (A × Tree)) (R : Tree → List (A × Tree)) : List (A × Tree) :=
  Q.flatMap fun q => (R q.2).map fun p => (q.1 * p.1, p.2)

theorem wsum_bindW (Q : List (A × Tree)) (R : Tree → List (A × Tree)) (φ : Tree → A) :
    wsum (bindW Q R) φ = wsum Q fun o => wsum (R o) φ := by
  unfold wsum bindW
  rw [sum_flatMap_map]
  congr 1
  refine List.map_congr_left fun q _ => ?_
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, mul_assoc]

theorem mem_bindW {Q : List (A × Tree)} {R : Tree → List (A × Tree)} {p : A × Tree} (h : p ∈ bindW Q R) :
    ∃ q ∈ Q, ∃ r ∈ R q.2, p.2 = r.2 ∧ p.1 = q.1 * r.1 := by
  unfold bindW at h
  rw [List.mem_flatMap] at h
  obtain ⟨q, hq, h⟩ := h
  rw [List.mem_map] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨q, hq, r, hr, rfl, rfl⟩

theorem mem_bindW_of {Q : List (A × Tree)} {R : Tree → List (A × Tree)} {q r : A × Tree} (hq : q ∈ Q)
    (hr : r ∈ R q.2) : (q.1 * r.1, r.2) ∈ bindW Q R :=
  List.mem_flatMap.2 ⟨q, hq, List.mem_map.2 ⟨r, hr, rfl⟩⟩

/-- The formula computes the weighted list `Q` at `x`. -/
def Does (θ : List Bool → A) (F : Fm) (x : Tree) (Q : List (A × Tree)) (c : ℕ) : Prop :=
  ∃ l, Ev θ F x l ∧ (∀ r ∈ l, r.bill = [] ∧ r.cost ≤ c ∧ ∃ q ∈ Q, q.2 = r.out) ∧
    ∀ φ : Tree → A, (l.map fun r => r.th * φ r.out).sum = wsum Q φ

/-- The formula has the value `o` at `x`, with weight 1. -/
def Gives (θ : List Bool → A) (F : Fm) (x o : Tree) (c : ℕ) : Prop := Does θ F x [(1, o)] c

namespace Does

variable {F G H : Fm} {x : Tree} {Q : List (A × Tree)} {c d : ℕ}

theorem mono (h : Does θ F x Q c) (hc : c ≤ d) : Does θ F x Q d := by
  obtain ⟨l, h1, h2, h3⟩ := h
  exact ⟨l, h1, fun r hr => ⟨(h2 r hr).1, (h2 r hr).2.1.trans hc, (h2 r hr).2.2⟩, h3⟩

/-- Replace the list by an equivalent one. -/
theorem congr {Q' : List (A × Tree)} (h : Does θ F x Q c) (h1 : ∀ q ∈ Q, ∃ q' ∈ Q', q'.2 = q.2)
    (h2 : ∀ φ : Tree → A, wsum Q φ = wsum Q' φ) : Does θ F x Q' c := by
  obtain ⟨l, e1, e2, e3⟩ := h
  refine ⟨l, e1, fun r hr => ⟨(e2 r hr).1, (e2 r hr).2.1, ?_⟩, fun φ => (e3 φ).trans (h2 φ)⟩
  obtain ⟨q, hq, hqr⟩ := (e2 r hr).2.2
  obtain ⟨q', hq', e⟩ := h1 q hq
  exact ⟨q', hq', e.trans hqr⟩

theorem hl (h : Does θ F x Q c) : Hl θ F x := by
  obtain ⟨l, h1, -⟩ := h
  exact h1.hl

theorem evl (h : Does θ F x Q c) : (∀ r ∈ NS1.evl θ F x, r.bill = [] ∧ r.cost ≤ c ∧ ∃ q ∈ Q, q.2 = r.out) ∧
    ∀ φ : Tree → A, ((NS1.evl θ F x).map fun r => r.th * φ r.out).sum = wsum Q φ := by
  obtain ⟨l, h1, h2, h3⟩ := h
  rw [h1.evl]
  exact ⟨h2, h3⟩

/-- A computation is a plain sum. -/
theorem plain (h : Does θ F x Q c) : Plain θ c (.cons F.code x) ∧ pv θ (.cons F.code x) = (Q.map Prod.fst).sum := by
  obtain ⟨h1, h2⟩ := h.evl
  refine ⟨⟨?_, fun r hr => ?_⟩, ?_⟩
  · simp only [hd_cons, tl_cons, Fm.ofTree_code]
    exact h.hl
  · simp only [hd_cons, tl_cons, Fm.ofTree_code] at hr
    exact ⟨(h1 r hr).1, (h1 r hr).2.1⟩
  · simp only [pv, hd_cons, tl_cons, Fm.ofTree_code, pval]
    have := h2 fun _ => 1
    simpa [wsum] using this

theorem of_dt {o : Tree} (h : Dt θ F x o c) : Does θ F x [(1, o)] c := by
  refine ⟨_, h, ?_, fun φ => ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨rfl, le_rfl, (1, o), List.mem_singleton_self _, rfl⟩
  · simp [Run.det]

/-- Pairs. -/
theorem cons {R : List (A × Tree)} (hF : Does θ F x Q c) (hG : Does θ G x R d) : Does θ (.cons F G) x
    (Q.flatMap fun q => R.map fun r => (q.1 * r.1, .cons q.2 r.2)) (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  refine ⟨_, Ev.cons e1 f1, ?_, fun φ => ?_⟩
  · intro r hr
    simp only [List.mem_flatMap, List.mem_map] at hr
    obtain ⟨r1, h1, r2, h2, rfl⟩ := hr
    obtain ⟨a1, a2, q, hq, a3⟩ := e2 r1 h1
    obtain ⟨b1, b2, p, hp, b3⟩ := f2 r2 h2
    refine ⟨?_, ?_, (q.1 * p.1, .cons q.2 p.2), List.mem_flatMap.2 ⟨q, hq, List.mem_map.2 ⟨p, hp, rfl⟩⟩, ?_⟩
    · simp [Run.seq, Run.tick, a1, b1]
    · simp only [Run.seq, Run.tick]
      omega
    · simp [Run.tick, a3, b3]
  · rw [sum_flatMap_map]
    have h1 : ∀ r : Run A, ((l'.map fun s => (r.seq s).tick (.cons r.out s.out)).map fun u => u.th * φ u.out).sum =
        r.th * wsum R fun o => φ (.cons r.out o) := by
      intro r
      rw [← f3, List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun s _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick, mul_assoc]
    simp only [h1]
    rw [e3 fun o => wsum R fun o' => φ (.cons o o'), wsum, wsum, sum_flatMap_map]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    rw [wsum, List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, mul_assoc]

/-- Apply a fixed program to the value. -/
theorem app {p : Tree} {R : Tree → List (A × Tree)} (hF : Does θ F x Q c)
    (hG : ∀ q ∈ Q, Does θ (Fm.ofTree p) q.2 (R q.2) d) : Does θ (app p F) x (bindW Q R) (c + d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  have hG' : ∀ s ∈ l, Does θ (Fm.ofTree p) s.out (R s.out) d := by
    intro s hs
    obtain ⟨-, -, q, hq, h⟩ := e2 s hs
    rw [← h]
    exact hG q hq
  refine ⟨_, Ev.app e1 fun s hs => (hG' s hs).hl, ?_, fun φ => ?_⟩
  · intro u hu
    obtain ⟨s, hs, t, ht, h1, h2, h3, -⟩ := mem_app hu
    obtain ⟨a1, a2, q, hq, a3⟩ := e2 s hs
    obtain ⟨b1, b2, r, hr, b3⟩ := (hG' s hs).evl.1 t ht
    rw [← a3] at hr
    refine ⟨by rw [h2, a1, b1]; rfl, by omega, (q.1 * r.1, r.2), mem_bindW_of hq hr, ?_⟩
    rw [h3, ← b3]
  · rw [wsum_bindW, sum_flatMap_map, ← wsum_congr (φ := fun o => ((NS1.evl θ (Fm.ofTree p) o).map fun t =>
      t.th * φ t.out).sum) (fun q hq => (hG q hq).evl.2 φ), ← e3]
    congr 1
    refine List.map_congr_left fun s _ => ?_
    rw [List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, Run.seq, Run.tick, Run.det, one_mul, mul_assoc]

/-- `let`. -/
theorem lett {R : Tree → List (A × Tree)} (hF : Does θ F x Q c) (hG : ∀ q ∈ Q, Does θ G q.2 (R q.2) d) :
    Does θ (lett F G) x (bindW Q R) (c + d + 2) :=
  app (p := G.code) hF (by rw [Fm.ofTree_code]; exact hG)

/-- `let`, with the argument kept. -/
theorem letk {R : Tree → List (A × Tree)} (hF : Does θ F x Q c) (hG : ∀ q ∈ Q, Does θ G (.cons x q.2) (R q.2) d) :
    Does θ (NS1.lett (.cons .id F) G) x (bindW Q R) (c + d + 4) := by
  have h1 := (of_dt (Dt.id x)).cons hF
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, one_mul] at h1
  have h2 := h1.lett (G := G) (R := fun o => R o.tl) (d := d) (by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact hG q' hq')
  refine (h2.congr ?_ fun φ => ?_).mono (by omega)
  · intro p hp
    obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hp
    rw [List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact ⟨_, mem_bindW_of hq' hr, h3.symm⟩
  · rw [wsum_bindW, wsum_bindW]
    simp [wsum, Function.comp_def]

/-- Apply a program that is the value of a formula. -/
theorem run {p y : Tree} {R : List (A × Tree)} {e : ℕ} (hF : Gives θ F x p c) (hG : Gives θ G x y d)
    (h : Does θ (Fm.ofTree p) y R e) : Does θ (.run F G) x R (c + d + e + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  have ho : ∀ r ∈ l, r.out = p := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  have ho' : ∀ r ∈ l', r.out = y := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := f2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.run' e1 f1 fun r hr s hs => by rw [ho r hr, ho' s hs]; exact h.hl, ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := hu
    rw [ho r hr, ho' s hs] at ht
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, -⟩ := f2 s hs
    obtain ⟨c1, c2, c3⟩ := h.evl.1 t ht
    refine ⟨by simp [Run.seq, Run.tick, a1, b1, c1], ?_, c3⟩
    simp only [Run.seq, Run.tick]
    omega
  · rw [sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.flatMap fun s => (NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
        ((r.seq s).seq t).tick t.out).map fun u => u.th * φ u.out).sum = r.th * wsum R φ := by
      intro r hr
      rw [sum_flatMap_map]
      have h2 : ∀ s ∈ l', (((NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
          ((r.seq s).seq t).tick t.out).map fun u => u.th * φ u.out).sum = s.th * (r.th * wsum R φ) := by
        intro s hs
        rw [ho r hr, ho' s hs, List.map_map, ← h.evl.2 φ, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun t _ => ?_
        simp only [Function.comp_apply, Run.seq, Run.tick]
        ring
      rw [List.map_congr_left h2]
      have := f3 fun _ => r.th * wsum R φ
      rw [this]
      simp [wsum]
    rw [List.map_congr_left h1]
    have := e3 fun _ => wsum R φ
    rw [this]
    simp [wsum]

theorem ite_true {o : Tree} (hF : Gives θ F x o c) (ho : o ≠ .nil) (hG : Does θ G x Q d) :
    Does θ (.ite F G H) x Q (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  have hout : ∀ r ∈ l, r.out = o := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r _ _ => f1) (fun r hr h => absurd ((hout r hr).symm.trans h) ho), ?_,
    fun φ => ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, b3⟩ := f2 s hs
    refine ⟨by simp [Run.seq, Run.tick, a1, b1], ?_, b3⟩
    simp only [Run.seq, Run.tick]
    omega
  · rw [sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.map fun s => (r.seq s).tick s.out).map fun u => u.th * φ u.out).sum = r.th * wsum Q φ := by
      intro r _
      rw [List.map_map, ← f3 φ, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick, mul_assoc]
    rw [List.map_congr_left h1]
    have := e3 fun _ => wsum Q φ
    rw [this]
    simp [wsum]

theorem ite_false (hF : Gives θ F x .nil c) (hH : Does θ H x Q d) : Does θ (.ite F G H) x Q (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hH
  have hout : ∀ r ∈ l, r.out = .nil := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r hr h => absurd (hout r hr) h) (fun r _ _ => f1), ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, b3⟩ := f2 s hs
    refine ⟨by simp [Run.seq, Run.tick, a1, b1], ?_, b3⟩
    simp only [Run.seq, Run.tick]
    omega
  · rw [sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.map fun s => (r.seq s).tick s.out).map fun u => u.th * φ u.out).sum = r.th * wsum Q φ := by
      intro r _
      rw [List.map_map, ← f3 φ, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick, mul_assoc]
    rw [List.map_congr_left h1]
    have := e3 fun _ => wsum Q φ
    rw [this]
    simp [wsum]

/-- Guess between two formulas. -/
theorem either {R : List (A × Tree)} (hG : Does θ G x Q c) (hH : Does θ H x R d) :
    Does θ (.ite .guess G H) x (Q ++ R) (max c d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hG
  obtain ⟨l', f1, f2, f3⟩ := hH
  refine ⟨_, Ev.ite (L := fun r => if r.out = .nil then l' else l) (Ev.guess x) (fun r _ h => by rw [if_neg h]; exact e1)
    (fun r _ h => by rw [if_pos h]; exact f1), ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, List.mem_map, Run.det, Tree.one,
      if_true, reduceCtorEq, if_false] at hu
    rcases hu with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · obtain ⟨a1, a2, q, hq, a3⟩ := f2 s hs
      refine ⟨by simp [Run.seq, Run.tick, a1], ?_, q, List.mem_append_right _ hq, a3⟩
      simp only [Run.seq, Run.tick]
      omega
    · obtain ⟨a1, a2, q, hq, a3⟩ := e2 s hs
      refine ⟨by simp [Run.seq, Run.tick, a1], ?_, q, List.mem_append_left _ hq, a3⟩
      simp only [Run.seq, Run.tick]
      omega
  · rw [wsum_append, ← e3 φ, ← f3 φ]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.sum_append, List.map_map,
      Run.det, Tree.one, if_true, reduceCtorEq, if_false]
    rw [add_comm]
    congr 1
    · congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick, one_mul]
    · congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick, one_mul]

theorem fail (x : Tree) : Does θ .fail x [] 0 := ⟨[], .fail x, by simp, by simp⟩

/-- Multiply by a constant of `A`. -/
theorem theta {o : Tree} (h : Gives θ F x o c) : Does θ (.theta F) x [(θ o.path, .nil)] (c + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := h
  have hout : ∀ r ∈ l, r.out = o := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.theta e1, ?_, fun φ => ?_⟩
  · intro u hu
    rw [List.mem_map] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    exact ⟨a1, by simpa using a2, _, List.mem_singleton_self _, rfl⟩
  · rw [List.map_map]
    have h1 : ∀ r ∈ l, ((fun r : Run A => r.th * φ r.out) ∘ fun r : Run A =>
        (⟨r.cost + 1, r.th * θ r.out.path, r.bill, .nil⟩ : Run A)) r = r.th * (θ o.path * φ .nil) := by
      intro r hr
      simp only [Function.comp_apply, hout r hr, mul_assoc]
    rw [List.map_congr_left h1]
    have := e3 fun _ => θ o.path * φ .nil
    rw [this]
    simp [wsum]

theorem hd {o : Tree} (h : Gives θ F x o c) : Gives θ (.hd F) x o.hd (c + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := h
  have hout : ∀ r ∈ l, r.out = o := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.hd e1, ?_, fun φ => ?_⟩
  · intro u hu
    rw [List.mem_map] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    refine ⟨a1, by simpa [Run.tick] using a2, _, List.mem_singleton_self _, ?_⟩
    simp [Run.tick, hout r hr]
  · rw [List.map_map]
    have h1 : ∀ r ∈ l, ((fun r : Run A => r.th * φ r.out) ∘ fun r : Run A => r.tick r.out.hd) r = r.th * φ o.hd := by
      intro r hr
      simp only [Function.comp_apply, Run.tick, hout r hr]
    rw [List.map_congr_left h1]
    have := e3 fun _ => φ o.hd
    rw [this]
    simp [wsum]

theorem tl {o : Tree} (h : Gives θ F x o c) : Gives θ (.tl F) x o.tl (c + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := h
  have hout : ∀ r ∈ l, r.out = o := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.tl e1, ?_, fun φ => ?_⟩
  · intro u hu
    rw [List.mem_map] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    refine ⟨a1, by simpa [Run.tick] using a2, _, List.mem_singleton_self _, ?_⟩
    simp [Run.tick, hout r hr]
  · rw [List.map_map]
    have h1 : ∀ r ∈ l, ((fun r : Run A => r.th * φ r.out) ∘ fun r : Run A => r.tick r.out.tl) r = r.th * φ o.tl := by
      intro r hr
      simp only [Function.comp_apply, Run.tick, hout r hr]
    rw [List.map_congr_left h1]
    have := e3 fun _ => φ o.tl
    rw [this]
    simp [wsum]

end Does

namespace Gives

variable {F G H : Fm} {x o o' : Tree} {c d : ℕ}

theorem mono (h : Gives θ F x o c) (hc : c ≤ d) : Gives θ F x o d := Does.mono h hc

theorem id (x : Tree) : Gives θ .id x x 1 := Does.of_dt (Dt.id x)

theorem quote (a x : Tree) : Gives θ (.quote a) x a 1 := Does.of_dt (Dt.quote a x)

theorem hd (h : Gives θ F x o c) : Gives θ (.hd F) x o.hd (c + 1) := Does.hd h

theorem tl (h : Gives θ F x o c) : Gives θ (.tl F) x o.tl (c + 1) := Does.tl h

theorem cons (h : Gives θ F x o c) (h' : Gives θ G x o' d) : Gives θ (.cons F G) x (.cons o o') (c + d + 1) := by
  have := Does.cons h h'
  simpa [Gives] using this

theorem app {p : Tree} (h : Gives θ F x o c) (h' : Gives θ (Fm.ofTree p) o o' d) :
    Gives θ (NS1.app p F) x o' (c + d + 2) := by
  have := Does.app (p := p) (R := fun _ => [(1, o')]) h (d := d) (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact h')
  simpa [Gives, bindW] using this

theorem lett (h : Gives θ F x o c) (h' : Gives θ G o o' d) : Gives θ (NS1.lett F G) x o' (c + d + 2) :=
  app (p := G.code) h (by rw [Fm.ofTree_code]; exact h')

theorem letk (h : Gives θ F x o c) (h' : Gives θ G (.cons x o) o' d) :
    Gives θ (NS1.lett (.cons .id F) G) x o' (c + d + 4) :=
  (((id x).cons h).lett h').mono (by omega)

theorem run {p y : Tree} {e : ℕ} (hF : Gives θ F x p c) (hG : Gives θ G x y d) (h : Gives θ (Fm.ofTree p) y o e) :
    Gives θ (.run F G) x o (c + d + e + 1) := Does.run hF hG h

theorem ite_true (hF : Gives θ F x o c) (ho : o ≠ .nil) (hG : Gives θ G x o' d) :
    Gives θ (.ite F G H) x o' (c + d + 1) := Does.ite_true hF ho hG

theorem ite_false (hF : Gives θ F x .nil c) (hH : Gives θ H x o' d) : Gives θ (.ite F G H) x o' (c + d + 1) :=
  Does.ite_false hF hH

/-- A computation, then a deterministic one. -/
theorem after {Q : List (A × Tree)} (h : Does θ F x Q c) {f : Tree → Tree} (h' : ∀ q ∈ Q, Gives θ G q.2 (f q.2) d) :
    Does θ (NS1.lett F G) x (Q.map fun q => (q.1, f q.2)) (c + d + 2) := by
  have := h.lett (R := fun o => [(1, f o)]) h'
  simpa [bindW, flatMap_single] using this

end Gives

/-- The weighted list of a deterministic computation followed by another one. -/
theorem Does.of_gives {F G : Fm} {x o : Tree} {Q : List (A × Tree)} {c d : ℕ} (h : Gives θ F x o c)
    (h' : Does θ G o Q d) : Does θ (NS1.lett F G) x Q (c + d + 2) := by
  have := Does.lett (R := fun _ => Q) h (G := G) (d := d) (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact h')
  simpa [bindW] using this

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Lists, equality, tries
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- A list of trees as a tree. -/
def listT : List Tree → Tree
  | [] => .nil
  | x :: xs => .cons x (listT xs)

@[simp] theorem toList_listT (xs : List Tree) : (listT xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listT, toList, ih]

theorem listT_toList (x : Tree) : listT x.toList = x := by
  induction x with
  | nil => rfl
  | cons a b _ ih => simp [listT, toList, ih]

theorem listT_ofBits (w : List Bool) : listT (w.map bit) = ofBits w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [listT, ofBits, ih]

/-- Apply the program that is the value of a formula to the values of another one. -/
theorem Does.runW {F G : Fm} {x p : Tree} {Q : List (A × Tree)} {R : Tree → List (A × Tree)} {c d e : ℕ}
    (hF : Gives θ F x p c) (hG : Does θ G x Q d) (h : ∀ q ∈ Q, Does θ (Fm.ofTree p) q.2 (R q.2) e) :
    Does θ (.run F G) x (bindW Q R) (c + d + e + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  have ho : ∀ r ∈ l, r.out = p := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  have hG' : ∀ s ∈ l', Does θ (Fm.ofTree p) s.out (R s.out) e := by
    intro s hs
    obtain ⟨-, -, q, hq, h'⟩ := f2 s hs
    rw [← h']
    exact h q hq
  refine ⟨_, Ev.run' e1 f1 fun r hr s hs => by rw [ho r hr]; exact (hG' s hs).hl, ?_, fun φ => ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := hu
    rw [ho r hr] at ht
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, q, hq, b3⟩ := f2 s hs
    obtain ⟨c1, c2, q', hq', c3⟩ := (hG' s hs).evl.1 t ht
    rw [← b3] at hq'
    refine ⟨by simp [Run.seq, Run.tick, a1, b1, c1], ?_, (q.1 * q'.1, q'.2), mem_bindW_of hq hq', c3⟩
    simp only [Run.seq, Run.tick]
    omega
  · rw [sum_flatMap_map, wsum_bindW]
    have h1 : ∀ r ∈ l, ((l'.flatMap fun s => (NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
        ((r.seq s).seq t).tick t.out).map fun u => u.th * φ u.out).sum = r.th * wsum Q fun o => wsum (R o) φ := by
      intro r hr
      rw [sum_flatMap_map, ← f3 fun o => wsum (R o) φ, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun s hs => ?_
      rw [ho r hr, List.map_map, ← (hG' s hs).evl.2 φ, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Run.seq, Run.tick]
      ring
    rw [List.map_congr_left h1]
    have := e3 fun _ => wsum Q fun o => wsum (R o) φ
    rw [this]
    simp [wsum]

section Fold

/-- Fold over a list with a state. The argument is (this program, (state, list)); `step` is applied to
(element, state). -/
def foldB (step : Fm) : Fm := .ite (.tl (.tl .id))
  (.run (.hd .id) (.cons (.hd .id) (.cons (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
    (.tl (.tl (.tl .id)))))) (.hd (.tl .id))

/-- Fold: `s` gives the state at the beginning, `l` the list. -/
def foldF (step s l : Fm) : Fm := app (foldB step).code (.cons (.quote (foldB step).code) (.cons s l))

/-- The weighted list of a fold. -/
def foldW (f : Tree → Tree → List (A × Tree)) : List Tree → Tree → List (A × Tree)
  | [], σ => [(1, σ)]
  | x :: xs, σ => bindW (f x σ) (foldW f xs)

theorem foldB_does {step : Fm} {f : Tree → Tree → List (A × Tree)} {Inv : List Tree → Tree → Prop} {d : Tree → ℕ}
    {xs : List Tree} (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ → Does θ step (.cons x σ) (f x σ) (d x) ∧
      ∀ q ∈ f x σ, Inv ys q.2) {σ : Tree} (hσ : Inv xs σ) :
    Does θ (foldB step) (.cons (foldB step).code (.cons σ (listT xs))) (foldW f xs σ)
      ((xs.map fun x => d x + 30).sum + 10) := by
  induction xs generalizing σ with
  | nil => exact (Does.ite_false (Gives.id _).tl.tl (Gives.id _).tl.hd).mono (by simp)
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := h x xs σ List.mem_cons_self hσ
    have e1 : Does θ (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
        (.cons (foldB step).code (.cons σ (listT (x :: xs)))) (f x σ) (8 + d x + 2) :=
      Does.of_gives (Gives.cons (Gives.id _).tl.tl.hd (Gives.id _).tl.hd) h1
    have e2 := Does.cons (Gives.id (θ := θ) (.cons (foldB step).code (.cons σ (listT (x :: xs))))).hd
      (Does.cons e1 (Gives.id (.cons (foldB step).code (.cons σ (listT (x :: xs))))).tl.tl.tl)
    have e3 := Does.runW (R := fun o => foldW f xs o.tl.hd) (e := (xs.map fun x => d x + 30).sum + 10)
      (Gives.id (θ := θ) (.cons (foldB step).code (.cons σ (listT (x :: xs))))).hd e2 (by
      intro q hq
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map, List.mem_flatMap,
        List.map_cons, List.map_nil, List.mem_singleton] at hq
      obtain ⟨q1, ⟨q2, hq2, rfl⟩, rfl⟩ := hq
      show Does θ (Fm.ofTree (foldB step).code) (.cons (foldB step).code (.cons q2.2 (listT xs))) _ _
      rw [Fm.ofTree_code]
      exact ih (fun y ys σ hy => h y ys σ (List.mem_cons_of_mem _ hy)) (h2 q2 hq2))
    refine ((Does.ite_true (Gives.id _).tl.tl (by simp [listT]) e3).congr ?_ fun φ => ?_).mono ?_
    · intro p hp
      obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hp
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map, List.mem_flatMap,
        List.map_cons, List.map_nil, List.mem_singleton] at hq
      obtain ⟨q1, ⟨q2, hq2, rfl⟩, rfl⟩ := hq
      exact ⟨_, mem_bindW_of hq2 hr, h3.symm⟩
    · rw [foldW, wsum_bindW, wsum_bindW]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil]
      simp only [wsum, List.map_map, one_mul, mul_one, flatMap_single, Function.comp_def, hd_cons, tl_cons]
    · simp only [List.map_cons, List.sum_cons]
      omega

theorem foldF_does {step s l : Fm} {x σ : Tree} {cs cl : ℕ} {f : Tree → Tree → List (A × Tree)}
    {Inv : List Tree → Tree → Prop} {d : Tree → ℕ} {xs : List Tree} (hs : Gives θ s x σ cs)
    (hl : Gives θ l x (listT xs) cl) (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ →
      Does θ step (.cons x σ) (f x σ) (d x) ∧ ∀ q ∈ f x σ, Inv ys q.2) (hσ : Inv xs σ) :
    Does θ (foldF step s l) x (foldW f xs σ) (cs + cl + (xs.map fun x => d x + 30).sum + 20) := by
  have h1 := Gives.cons (Gives.quote (θ := θ) (foldB step).code x) (Gives.cons hs hl)
  have h2 := Does.app (p := (foldB step).code) (R := fun _ => foldW f xs σ) h1 (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    rw [Fm.ofTree_code]
    exact foldB_does h hσ)
  refine (h2.congr ?_ fun φ => ?_).mono (by omega)
  · intro p hp
    obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hp
    exact ⟨r, hr, h3.symm⟩
  · rw [wsum_bindW]
    simp [wsum]

theorem foldW_det (g : Tree → Tree → Tree) (xs : List Tree) (σ : Tree) :
    foldW (A := A) (fun x σ => [(1, g x σ)]) xs σ = [(1, xs.foldl (fun σ x => g x σ) σ)] := by
  induction xs generalizing σ with
  | nil => rfl
  | cons x xs ih => simp [foldW, bindW, ih]

/-- A deterministic fold. -/
theorem foldF_gives {step s l : Fm} {x σ : Tree} {cs cl : ℕ} {g : Tree → Tree → Tree}
    {Inv : List Tree → Tree → Prop} {d : Tree → ℕ} {xs : List Tree} (hs : Gives θ s x σ cs)
    (hl : Gives θ l x (listT xs) cl) (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ →
      Gives θ step (.cons x σ) (g x σ) (d x) ∧ Inv ys (g x σ)) (hσ : Inv xs σ) :
    Gives θ (foldF step s l) x (xs.foldl (fun σ x => g x σ) σ) (cs + cl + (xs.map fun x => d x + 30).sum + 20) := by
  have := foldF_does (f := fun x σ => [(1, g x σ)]) hs hl (fun x ys σ hx hσ => by
    obtain ⟨h1, h2⟩ := h x ys σ hx hσ
    refine ⟨h1, fun q hq => ?_⟩
    rw [List.mem_singleton] at hq
    subst hq
    exact h2) hσ
  rwa [foldW_det] at this

/-- Reverse a list onto another one. -/
theorem foldl_rev (xs : List Tree) (ys : List Tree) :
    xs.foldl (fun σ x => Tree.cons x σ) (listT ys) = listT (xs.reverse ++ ys) := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, show Tree.cons x (listT ys) = listT (x :: ys) from rfl, ih]
    simp

theorem rev_gives {s l : Fm} {x : Tree} {cs cl : ℕ} {xs ys : List Tree} (hs : Gives θ s x (listT ys) cs)
    (hl : Gives θ l x (listT xs) cl) :
    Gives θ (foldF .id s l) x (listT (xs.reverse ++ ys)) (cs + cl + xs.length * 31 + 20) := by
  have := foldF_gives (step := .id) (g := fun x σ => .cons x σ) (Inv := fun _ _ => True) (d := fun _ => 1) hs hl
    (fun x _ σ _ _ => ⟨Gives.id _, trivial⟩) trivial
  rw [foldl_rev] at this
  simpa using this

/-- Concatenation. -/
def appF (a b : Fm) : Fm := foldF .id b (foldF .id (.quote .nil) a)

theorem appF_gives {a b : Fm} {x : Tree} {ca cb : ℕ} {xs ys : List Tree} (ha : Gives θ a x (listT xs) ca)
    (hb : Gives θ b x (listT ys) cb) :
    Gives θ (appF a b) x (listT (xs ++ ys)) (ca + cb + xs.length * 62 + 41) := by
  have h1 := rev_gives (Gives.quote (θ := θ) (listT []) x) ha
  rw [List.append_nil] at h1
  have h2 := rev_gives hb h1
  rw [List.reverse_reverse, List.length_reverse] at h2
  exact h2.mono (by omega)

end Fold

section Map

/-- Apply `step` to (parameter, element) for all elements of a list. The argument is (this program, (parameter,
list)). -/
def mapB (step : Fm) : Fm := .ite (.tl (.tl .id))
  (.cons (lett (.cons (.hd (.tl .id)) (.hd (.tl (.tl .id)))) step)
    (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.tl .id)) (.tl (.tl (.tl .id))))))) (.quote .nil)

/-- Map: `e` gives the parameter, `l` the list. -/
def mapF (step e l : Fm) : Fm := app (mapB step).code (.cons (.quote (mapB step).code) (.cons e l))

theorem mapB_gives {step : Fm} {e : Tree} {g : Tree → Tree} {d : Tree → ℕ} {xs : List Tree}
    (h : ∀ x ∈ xs, Gives θ step (.cons e x) (g x) (d x)) :
    Gives θ (mapB step) (.cons (mapB step).code (.cons e (listT xs))) (listT (xs.map g))
      ((xs.map fun x => d x + 40).sum + 10) := by
  induction xs with
  | nil => exact ((Gives.id _).tl.tl.ite_false (Gives.quote _ _)).mono (by simp)
  | cons x xs ih =>
    have e1 : Gives θ (lett (.cons (.hd (.tl .id)) (.hd (.tl (.tl .id)))) step)
        (.cons (mapB step).code (.cons e (listT (x :: xs)))) (g x) (8 + d x + 2) :=
      Gives.lett (Gives.cons (Gives.id _).tl.hd (Gives.id _).tl.tl.hd) (h x List.mem_cons_self)
    have ih' : Gives θ (Fm.ofTree (mapB step).code) (.cons (mapB step).code (.cons e (listT xs))) (listT (xs.map g))
        ((xs.map fun x => d x + 40).sum + 10) := by
      rw [Fm.ofTree_code]
      exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    have e2 := Gives.run (Gives.id (θ := θ) (.cons (mapB step).code (.cons e (listT (x :: xs))))).hd
      (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd (Gives.id _).tl.tl.tl)) ih'
    refine (Gives.ite_true (Gives.id _).tl.tl (by simp [listT]) (Gives.cons e1 e2)).mono ?_
    simp only [List.map_cons, List.sum_cons]
    omega

theorem mapF_gives {step ef l : Fm} {x e : Tree} {ce cl : ℕ} {g : Tree → Tree} {d : Tree → ℕ} {xs : List Tree}
    (he : Gives θ ef x e ce) (hl : Gives θ l x (listT xs) cl) (h : ∀ x ∈ xs, Gives θ step (.cons e x) (g x) (d x)) :
    Gives θ (mapF step ef l) x (listT (xs.map g)) (ce + cl + (xs.map fun x => d x + 40).sum + 20) := by
  refine (Gives.app (p := (mapB step).code) (Gives.cons (Gives.quote _ _) (Gives.cons he hl)) (by
    rw [Fm.ofTree_code]
    exact mapB_gives h)).mono (by omega)

end Map

section Eq

/-- Equality of trees: 1 if equal, else empty. The argument is (this program, (a, b)). -/
def eqB : Fm := .ite (.hd (.tl .id))
  (.ite (.tl (.tl .id))
    (.ite (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.hd (.tl .id))) (.hd (.tl (.tl .id))))))
      (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.tl (.tl (.tl .id))))))
      (.quote .nil))
    (.quote .nil))
  (.ite (.tl (.tl .id)) (.quote .nil) (.quote one))

/-- Equality of two values. -/
def eqF (a b : Fm) : Fm := app eqB.code (.cons (.quote eqB.code) (.cons a b))

theorem eqB_gives (a b : Tree) : Gives θ eqB (.cons eqB.code (.cons a b)) (bit (decide (a = b))) (60 * a.size) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil =>
      refine ((Gives.id _).tl.hd.ite_false ((Gives.id _).tl.tl.ite_false (Gives.quote one _))).mono ?_
      simp [size]
    | cons b1 b2 =>
      refine ((Gives.id _).tl.hd.ite_false ((Gives.id _).tl.tl.ite_true (by simp) (Gives.quote .nil _))).mono ?_
      simp [size]
  | cons a1 a2 ih1 ih2 =>
    cases b with
    | nil =>
      refine ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.tl.ite_false (Gives.quote .nil _))).mono ?_
      simp only [size]
      omega
    | cons b1 b2 =>
      have h1 : Gives θ (Fm.ofTree eqB.code) (.cons eqB.code (.cons a1 b1)) (bit (decide (a1 = b1))) (60 * a1.size) := by
        rw [Fm.ofTree_code]; exact ih1 b1
      have h2 : Gives θ (Fm.ofTree eqB.code) (.cons eqB.code (.cons a2 b2)) (bit (decide (a2 = b2))) (60 * a2.size) := by
        rw [Fm.ofTree_code]; exact ih2 b2
      have r1 := Gives.run (Gives.id (θ := θ) (.cons eqB.code (.cons (.cons a1 a2) (.cons b1 b2)))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.hd (Gives.id _).tl.tl.hd)) h1
      have r2 := Gives.run (Gives.id (θ := θ) (.cons eqB.code (.cons (.cons a1 a2) (.cons b1 b2)))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.id _).tl.tl.tl)) h2
      by_cases hab : a1 = b1
      · have hb : bit (decide (a1 = b1)) ≠ .nil := by simp [hab, bit, one]
        have e : decide (Tree.cons a1 a2 = Tree.cons b1 b2) = decide (a2 = b2) := by simp [hab]
        rw [e]
        refine ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.tl.ite_true (by simp)
          (Gives.ite_true r1 hb r2))).mono ?_
        simp only [size]
        omega
      · have hb : bit (decide (a1 = b1)) = .nil := by simp [hab, bit]
        rw [hb] at r1
        have e : bit (decide (Tree.cons a1 a2 = Tree.cons b1 b2)) = .nil := by simp [hab, bit]
        rw [e]
        refine ((Gives.id _).tl.hd.ite_true (by simp) ((Gives.id _).tl.tl.ite_true (by simp)
          (Gives.ite_false r1 (Gives.quote .nil _)))).mono ?_
        simp only [size]
        omega

theorem eqF_gives {a b : Fm} {x u v : Tree} {ca cb : ℕ} (ha : Gives θ a x u ca) (hb : Gives θ b x v cb) :
    Gives θ (eqF a b) x (bit (decide (u = v))) (ca + cb + 60 * u.size + 10) := by
  refine (Gives.app (p := eqB.code) (Gives.cons (Gives.quote _ _) (Gives.cons ha hb)) (by
    rw [Fm.ofTree_code]
    exact eqB_gives u v)).mono (by omega)

end Eq

section Choice

/-- Choose an element of a list. The argument is (this program, list). -/
def pickB : Fm := .ite (.tl .id)
  (.ite .guess (.hd (.tl .id)) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) .fail

/-- Choose an element of a list. -/
def pickF (l : Fm) : Fm := app pickB.code (.cons (.quote pickB.code) l)

theorem pickB_does (xs : List Tree) :
    Does θ pickB (.cons pickB.code (listT xs)) (xs.map fun x => (1, x)) (20 * xs.length + 10) := by
  induction xs with
  | nil => exact (Does.ite_false (Gives.id _).tl (Does.fail _)).mono (by simp)
  | cons x xs ih =>
    have ih' : Does θ (Fm.ofTree pickB.code) (.cons pickB.code (listT xs)) (xs.map fun x => (1, x)) (20 * xs.length + 10) := by
      rw [Fm.ofTree_code]; exact ih
    have r := Does.run (Gives.id (θ := θ) (.cons pickB.code (listT (x :: xs)))).hd
      (Gives.cons (Gives.id _).hd (Gives.id _).tl.tl) ih'
    refine (Does.ite_true (Gives.id _).tl (by simp [listT]) (Does.either (Gives.id _).tl.hd r)).mono ?_
    simp only [List.length_cons]
    omega

theorem pickF_does {l : Fm} {x : Tree} {cl : ℕ} {xs : List Tree} (hl : Gives θ l x (listT xs) cl) :
    Does θ (pickF l) x (xs.map fun x => (1, x)) (cl + 20 * xs.length + 20) := by
  have h1 := Gives.cons (Gives.quote (θ := θ) pickB.code x) hl
  have h2 := Does.app (p := pickB.code) (R := fun _ => xs.map fun x => ((1 : A), x)) h1 (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    rw [Fm.ofTree_code]
    exact pickB_does xs)
  refine (h2.congr ?_ fun φ => ?_).mono (by omega)
  · intro p hp
    obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hp
    exact ⟨r, hr, h3.symm⟩
  · rw [wsum_bindW]
    simp [wsum]

end Choice

section Tries

/-- Tries: (value, (left, right)); the empty tree is the empty trie. -/
def tget : List Bool → Tree → Tree
  | [], t => t.hd
  | true :: p, t => tget p t.tl.tl
  | false :: p, t => tget p t.tl.hd

/-- Write a value. -/
def tset : List Bool → Tree → Tree → Tree
  | [], v, t => .cons v t.tl
  | true :: p, v, t => .cons t.hd (.cons t.tl.hd (tset p v t.tl.tl))
  | false :: p, v, t => .cons t.hd (.cons (tset p v t.tl.hd) t.tl.tl)

theorem tget_nil (p : List Bool) : tget p .nil = .nil := by
  induction p with
  | nil => rfl
  | cons b p ih => cases b <;> exact ih

theorem tget_tset (p p' : List Bool) (v t : Tree) : tget p (tset p' v t) = if p = p' then v else tget p t := by
  induction p' generalizing p t with
  | nil =>
    cases p with
    | nil => rfl
    | cons b p => cases b <;> simp [tset, tget]
  | cons b' p' ih =>
    cases p with
    | nil => cases b' <;> simp [tset, tget]
    | cons b p =>
      cases b <;> cases b' <;> simp [tset, tget, ih]

/-- Read a value. The argument is (this program, (path, trie)). -/
def getB : Fm := .ite (.hd (.tl .id))
  (.ite (.hd (.hd (.tl .id)))
    (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.tl (.tl (.tl (.tl .id)))))))
    (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.hd (.tl (.tl (.tl .id))))))))
  (.hd (.tl (.tl .id)))

/-- Read a value: `p` gives the path, `t` the trie. -/
def getF (p t : Fm) : Fm := app getB.code (.cons (.quote getB.code) (.cons p t))

theorem getB_gives (p : Tree) (t : Tree) :
    Gives θ getB (.cons getB.code (.cons p t)) (tget p.path t) (30 * p.len + 10) := by
  induction p generalizing t with
  | nil => exact ((Gives.id _).tl.hd.ite_false (Gives.id _).tl.tl.hd).mono (by simp [len])
  | cons a p _ ih =>
    by_cases ha : a = .nil
    · subst ha
      have h1 : Gives θ (Fm.ofTree getB.code) (.cons getB.code (.cons p t.tl.hd)) (tget p.path t.tl.hd)
          (30 * p.len + 10) := by rw [Fm.ofTree_code]; exact ih _
      have r := Gives.run (Gives.id (θ := θ) (.cons getB.code (.cons (.cons .nil p) t))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.id _).tl.tl.tl.hd)) h1
      refine (Gives.ite_true (Gives.id _).tl.hd (by simp) (Gives.ite_false (Gives.id _).tl.hd.hd r)).mono ?_
      simp only [len]
      omega
    · have h1 : Gives θ (Fm.ofTree getB.code) (.cons getB.code (.cons p t.tl.tl)) (tget p.path t.tl.tl)
          (30 * p.len + 10) := by rw [Fm.ofTree_code]; exact ih _
      have r := Gives.run (Gives.id (θ := θ) (.cons getB.code (.cons (.cons a p) t))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.id _).tl.tl.tl.tl)) h1
      have e : tget (Tree.cons a p).path t = tget p.path t.tl.tl := by simp [path, ha, tget]
      rw [e]
      refine (Gives.ite_true (Gives.id _).tl.hd (by simp) (Gives.ite_true (Gives.id _).tl.hd.hd (by simpa using ha) r)).mono ?_
      simp only [len]
      omega

theorem getF_gives {pf tf : Fm} {x p t : Tree} {cp ct : ℕ} (hp : Gives θ pf x p cp) (ht : Gives θ tf x t ct) :
    Gives θ (getF pf tf) x (tget p.path t) (cp + ct + 30 * p.len + 20) := by
  refine (Gives.app (p := getB.code) (Gives.cons (Gives.quote _ _) (Gives.cons hp ht)) (by
    rw [Fm.ofTree_code]
    exact getB_gives p t)).mono (by omega)

/-- Write a value. The argument is (this program, (path, (value, trie))). -/
def setB : Fm := .ite (.hd (.tl .id))
  (.ite (.hd (.hd (.tl .id)))
    (.cons (.hd (.tl (.tl (.tl .id)))) (.cons (.hd (.tl (.tl (.tl (.tl .id)))))
      (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.cons (.hd (.tl (.tl .id)))
        (.tl (.tl (.tl (.tl (.tl .id)))))))))))
    (.cons (.hd (.tl (.tl (.tl .id)))) (.cons
      (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.cons (.hd (.tl (.tl .id)))
        (.hd (.tl (.tl (.tl (.tl .id)))))))))
      (.tl (.tl (.tl (.tl (.tl .id))))))))
  (.cons (.hd (.tl (.tl .id))) (.tl (.tl (.tl (.tl .id)))))

/-- Write a value: `p` gives the path, `v` the value, `t` the trie. -/
def setF (p v t : Fm) : Fm := app setB.code (.cons (.quote setB.code) (.cons p (.cons v t)))

theorem setB_gives (p v t : Tree) :
    Gives θ setB (.cons setB.code (.cons p (.cons v t))) (tset p.path v t) (60 * p.len + 20) := by
  induction p generalizing t with
  | nil =>
    exact ((Gives.id _).tl.hd.ite_false (Gives.cons (Gives.id _).tl.tl.hd (Gives.id _).tl.tl.tl.tl)).mono (by simp [len])
  | cons a p _ ih =>
    by_cases ha : a = .nil
    · subst ha
      have h1 : Gives θ (Fm.ofTree setB.code) (.cons setB.code (.cons p (.cons v t.tl.hd))) (tset p.path v t.tl.hd)
          (60 * p.len + 20) := by rw [Fm.ofTree_code]; exact ih _
      have r := Gives.run (Gives.id (θ := θ) (.cons setB.code (.cons (.cons .nil p) (.cons v t)))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.cons (Gives.id _).tl.tl.hd
          (Gives.id _).tl.tl.tl.tl.hd))) h1
      refine (Gives.ite_true (Gives.id _).tl.hd (by simp) (Gives.ite_false (Gives.id _).tl.hd.hd
        (Gives.cons (Gives.id _).tl.tl.tl.hd (Gives.cons r (Gives.id _).tl.tl.tl.tl.tl)))).mono ?_
      simp only [len]
      omega
    · have h1 : Gives θ (Fm.ofTree setB.code) (.cons setB.code (.cons p (.cons v t.tl.tl))) (tset p.path v t.tl.tl)
          (60 * p.len + 20) := by rw [Fm.ofTree_code]; exact ih _
      have r := Gives.run (Gives.id (θ := θ) (.cons setB.code (.cons (.cons a p) (.cons v t)))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.cons (Gives.id _).tl.tl.hd
          (Gives.id _).tl.tl.tl.tl.tl))) h1
      have e : tset (Tree.cons a p).path v t = .cons t.hd (.cons t.tl.hd (tset p.path v t.tl.tl)) := by
        simp [path, ha, tset]
      rw [e]
      refine (Gives.ite_true (Gives.id _).tl.hd (by simp) (Gives.ite_true (Gives.id _).tl.hd.hd (by simpa using ha)
        (Gives.cons (Gives.id _).tl.tl.tl.hd (Gives.cons (Gives.id _).tl.tl.tl.tl.hd r)))).mono ?_
      simp only [len]
      omega

theorem setF_gives {pf vf tf : Fm} {x p v t : Tree} {cp cv ct : ℕ} (hp : Gives θ pf x p cp) (hv : Gives θ vf x v cv)
    (ht : Gives θ tf x t ct) : Gives θ (setF pf vf tf) x (tset p.path v t) (cp + cv + ct + 60 * p.len + 30) := by
  refine (Gives.app (p := setB.code) (Gives.cons (Gives.quote _ _) (Gives.cons hp (Gives.cons hv ht))) (by
    rw [Fm.ofTree_code]
    exact setB_gives p v t)).mono (by omega)

end Tries

section Weights

/-- Formulas for elements of `A`. -/
inductive WE where
  /-- 0 -/
  | zero
  /-- 1 -/
  | one
  /-- a named constant -/
  | nm (p : List Bool)
  /-- sum -/
  | add (a b : WE)
  /-- product -/
  | mul (a b : WE)

/-- The value. -/
def WE.val (θ : List Bool → A) : WE → A
  | zero => 0
  | one => 1
  | nm p => θ p
  | add a b => a.val θ + b.val θ
  | mul a b => a.val θ * b.val θ

/-- The formula of the machine. -/
def WE.fm : WE → Fm
  | zero => .fail
  | one => .quote .nil
  | nm p => .theta (.quote (ofBits p))
  | add a b => .ite .guess a.fm b.fm
  | mul a b => lett a.fm (lett b.fm (.quote .nil))

/-- The cost. -/
def WE.cost : WE → ℕ
  | zero => 1
  | one => 1
  | nm _ => 2
  | add a b => max a.cost b.cost + 2
  | mul a b => a.cost + b.cost + 10

/-- Multiply the weight by an element of `A`. -/
theorem WE.does (e : WE) (x : Tree) : Does θ e.fm x [(e.val θ, .nil)] e.cost := by
  induction e generalizing x with
  | zero =>
    refine ((Does.fail x).congr (by simp) fun φ => ?_).mono (Nat.zero_le _)
    simp [WE.val]
  | one => exact Gives.quote .nil x
  | nm p =>
    have := Does.theta (Gives.quote (θ := θ) (ofBits p) x)
    rwa [path_ofBits] at this
  | add a b iha ihb =>
    refine (Does.either (iha x) (ihb x)).congr ?_ fun φ => ?_
    · intro q hq
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> rfl
    · simp [WE.val, add_mul]
  | mul a b iha ihb =>
    have h1 := Does.lett (R := fun _ => [(b.val θ, .nil)]) (G := lett b.fm (.quote .nil)) (iha x)
      (d := b.cost + 1 + 2) (by
        intro q hq
        have := Does.lett (R := fun _ => [((1 : A), Tree.nil)]) (G := .quote .nil) (ihb q.2) (d := 1)
          fun p _ => Gives.quote .nil p.2
        simpa [bindW] using this)
    refine (h1.congr ?_ fun φ => ?_).mono ?_
    · intro q hq
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [bindW, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
        List.mem_singleton] at hq
      subst hq
      rfl
    · simp [bindW, WE.val]
    · simp only [WE.cost]
      omega

/-- Every element of the subring generated by the constants has a formula, if −1 is a constant. -/
theorem WE.exists_of_adjoin {p₀ : List Bool} (h : θ p₀ = -1) {a : A} (ha : a ∈ Subring.closure (Set.range θ)) :
    ∃ e : WE, e.val θ = a := by
  induction ha using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨.nm p, rfl⟩
  | zero => exact ⟨.zero, rfl⟩
  | one => exact ⟨.one, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨f, rfl⟩ := hy
    exact ⟨.add e f, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨f, rfl⟩ := hy
    exact ⟨.mul e f, rfl⟩
  | neg x _ hx =>
    obtain ⟨e, rfl⟩ := hx
    exact ⟨.mul (.nm p₀) e, by simp [WE.val, h]⟩

end Weights

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Words of trees, parts of lists, choices, straight-line programs
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

section Word

/-- The brackets of a tree, in preorder; `t0`: empty, `t1`: a node. -/
def wordT (t0 t1 : Tree) : Tree → List Tree
  | .nil => [t0]
  | .cons a b => t1 :: (wordT t0 t1 a ++ wordT t0 t1 b)

theorem length_wordT (t0 t1 z : Tree) : (wordT t0 t1 z).length = z.size := by
  induction z with
  | nil => rfl
  | cons a b iha ihb =>
    simp only [wordT, List.length_cons, List.length_append, iha, ihb, Tree.size]

/-- Write the brackets of a tree in front of a list. The argument is (this program, (tree, list)). -/
def wordB (t0 t1 : Tree) : Fm := .ite (.hd (.tl .id))
  (.cons (.quote t1) (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.hd (.tl .id)))
    (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.tl (.tl .id)))))))))
  (.cons (.quote t0) (.tl (.tl .id)))

/-- The brackets of a tree. -/
def wordF (t0 t1 : Tree) (z : Fm) : Fm :=
  app (wordB t0 t1).code (.cons (.quote (wordB t0 t1).code) (.cons z (.quote .nil)))

theorem wordB_gives (t0 t1 z : Tree) (acc : List Tree) :
    Gives θ (wordB t0 t1) (.cons (wordB t0 t1).code (.cons z (listT acc))) (listT (wordT t0 t1 z ++ acc))
      (60 * z.size) := by
  induction z generalizing acc with
  | nil =>
    refine ((Gives.id _).tl.hd.ite_false (Gives.cons (Gives.quote t0 _) (Gives.id _).tl.tl)).mono ?_
    simp [Tree.size]
  | cons a b iha ihb =>
    have hb : Gives θ (Fm.ofTree (wordB t0 t1).code) (.cons (wordB t0 t1).code (.cons b (listT acc)))
        (listT (wordT t0 t1 b ++ acc)) (60 * b.size) := by rw [Fm.ofTree_code]; exact ihb acc
    have ha : Gives θ (Fm.ofTree (wordB t0 t1).code) (.cons (wordB t0 t1).code (.cons a (listT (wordT t0 t1 b ++ acc))))
        (listT (wordT t0 t1 a ++ (wordT t0 t1 b ++ acc))) (60 * a.size) := by rw [Fm.ofTree_code]; exact iha _
    have r1 := Gives.run (Gives.id (θ := θ) (.cons (wordB t0 t1).code (.cons (.cons a b) (listT acc)))).hd
      (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.tl (Gives.id _).tl.tl)) hb
    have r2 := Gives.run (Gives.id (θ := θ) (.cons (wordB t0 t1).code (.cons (.cons a b) (listT acc)))).hd
      (Gives.cons (Gives.id _).hd (Gives.cons (Gives.id _).tl.hd.hd r1)) ha
    have h := Gives.ite_true (H := .cons (.quote t0) (.tl (.tl .id)))
      (Gives.id (θ := θ) (.cons (wordB t0 t1).code (.cons (.cons a b) (listT acc)))).tl.hd (by simp)
      (Gives.cons (Gives.quote t1 _) r2)
    rw [wordT, List.cons_append, List.append_assoc]
    refine Gives.mono h ?_
    simp only [Tree.size]
    omega

theorem wordF_gives {t0 t1 : Tree} {zf : Fm} {x z : Tree} {cz : ℕ} (hz : Gives θ zf x z cz) :
    Gives θ (wordF t0 t1 zf) x (listT (wordT t0 t1 z)) (cz + 60 * z.size + 10) := by
  have h := wordB_gives (θ := θ) t0 t1 z []
  rw [List.append_nil] at h
  refine (Gives.app (p := (wordB t0 t1).code) (Gives.cons (Gives.quote _ _) (Gives.cons hz (Gives.quote (listT []) _)))
    (by rw [Fm.ofTree_code]; exact h)).mono (by omega)

end Word

section Take

/-- Is a number not 0? The argument is (this program, number). -/
def nzB : Fm := .ite (.tl .id) (.ite (.hd (.tl .id)) (.quote one) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id)))))
  (.quote .nil)

theorem nzB_gives (w : List Bool) :
    Gives θ nzB (.cons nzB.code (ofBits w)) (bit (decide (KT.val w ≠ 0))) (20 * w.length + 10) := by
  induction w with
  | nil => exact ((Gives.id _).tl.ite_false (Gives.quote .nil _)).mono (by simp)
  | cons b w ih =>
    cases b with
    | true =>
      have e : bit (decide (KT.val (true :: w) ≠ 0)) = one := by
        have : KT.val (true :: w) ≠ 0 := by simp [KT.val]
        simp [this, bit]
      rw [e]
      refine ((Gives.id _).tl.ite_true (by simp [ofBits]) ((Gives.id _).tl.hd.ite_true (by simp [ofBits, bit, one])
        (Gives.quote one _))).mono ?_
      simp only [List.length_cons]
      omega
    | false =>
      have ih' : Gives θ (Fm.ofTree nzB.code) (.cons nzB.code (ofBits w)) (bit (decide (KT.val w ≠ 0)))
          (20 * w.length + 10) := by rw [Fm.ofTree_code]; exact ih
      have r := Gives.run (Gives.id (θ := θ) (.cons nzB.code (ofBits (false :: w)))).hd
        (Gives.cons (Gives.id _).hd (Gives.id _).tl.tl) ih'
      have e : decide (KT.val (false :: w) ≠ 0) = decide (KT.val w ≠ 0) := by
        simp [KT.val]
      rw [e]
      refine ((Gives.id _).tl.ite_true (by simp [ofBits]) ((Gives.id _).tl.hd.ite_false r)).mono ?_
      simp only [List.length_cons]
      omega

/-- Take elements from a list, as many as a binary number says. The argument is (this program, (number, (elements
taken, in reversed order, list))); the value is (elements taken, rest). -/
def takeB : Fm := .ite (.tl (.tl (.tl .id)))
  (.ite (app nzB.code (.cons (.quote nzB.code) (.hd (.tl .id))))
    (.run (.hd .id) (.cons (.hd .id) (.cons (app DW.code (.cons (.quote DW.code) (.hd (.tl .id))))
      (.cons (.cons (.hd (.tl (.tl (.tl .id)))) (.hd (.tl (.tl .id)))) (.tl (.tl (.tl (.tl .id))))))))
    (.tl (.tl .id)))
  (.tl (.tl .id))

theorem takeB_gives (w : List Bool) (acc l : List Tree) :
    Gives θ takeB (.cons takeB.code (.cons (ofBits w) (.cons (listT acc) (listT l))))
      (.cons (listT ((l.take (KT.val w)).reverse ++ acc)) (listT (l.drop (KT.val w))))
      (((l.take (KT.val w)).length + 1) * (60 * w.length + 100)) := by
  induction l generalizing w acc with
  | nil =>
    have h : Gives θ takeB (.cons takeB.code (.cons (ofBits w) (.cons (listT acc) (listT []))))
        (.cons (listT acc) (listT [])) 20 := (Gives.ite_false (Gives.id _).tl.tl.tl (Gives.id _).tl.tl).mono (by norm_num)
    rw [List.take_nil, List.drop_nil, List.reverse_nil, List.nil_append]
    refine h.mono ?_
    simp only [List.length_nil, zero_add, one_mul]
    omega
  | cons a l ih =>
    have hnz := Gives.app (p := nzB.code) (Gives.cons (Gives.quote (θ := θ) nzB.code
      (.cons takeB.code (.cons (ofBits w) (.cons (listT acc) (listT (a :: l)))))) (Gives.id _).tl.hd)
      (o' := bit (decide (KT.val w ≠ 0))) (d := 20 * w.length + 10) (by rw [Fm.ofTree_code]; exact nzB_gives w)
    rcases decw_val w with ⟨h1, h2⟩ | ⟨w', h1, h2⟩
    · have e : bit (decide (KT.val w ≠ 0)) = .nil := by simp [h2, bit]
      rw [e] at hnz
      have h : Gives θ takeB (.cons takeB.code (.cons (ofBits w) (.cons (listT acc) (listT (a :: l)))))
          (.cons (listT acc) (listT (a :: l))) _ :=
        Gives.ite_true (Gives.id _).tl.tl.tl (by simp [listT]) (Gives.ite_false hnz (Gives.id _).tl.tl)
      rw [h2, List.take_zero, List.drop_zero, List.reverse_nil, List.nil_append]
      refine h.mono ?_
      simp only [List.length_nil, zero_add, one_mul]
      omega
    · have e : bit (decide (KT.val w ≠ 0)) ≠ .nil := by
        have : KT.val w ≠ 0 := by omega
        simp [this, bit, one]
      obtain ⟨k, hk, hdw⟩ := DW_some (θ := θ) h1
      have hd : Gives θ (app DW.code (.cons (.quote DW.code) (.hd (.tl .id))))
          (.cons takeB.code (.cons (ofBits w) (.cons (listT acc) (listT (a :: l))))) (ofBits w') (1 + 3 + 1 + 20 * w.length + 2) :=
        Gives.app (p := DW.code) (Gives.cons (Gives.quote DW.code _) (Gives.id _).tl.hd) (by
          rw [Fm.ofTree_code]
          exact (Does.of_dt hdw).mono hk)
      have hl : w'.length = w.length := length_decw h1
      have ih' : Gives θ (Fm.ofTree takeB.code) (.cons takeB.code (.cons (ofBits w') (.cons (listT (a :: acc)) (listT l))))
          (.cons (listT ((l.take (KT.val w')).reverse ++ (a :: acc))) (listT (l.drop (KT.val w'))))
          (((l.take (KT.val w')).length + 1) * (60 * w.length + 100)) := by
        rw [Fm.ofTree_code, ← hl]
        exact ih w' (a :: acc)
      have r := Gives.run (Gives.id (θ := θ) (.cons takeB.code (.cons (ofBits w) (.cons (listT acc) (listT (a :: l)))))).hd
        (Gives.cons (Gives.id _).hd (Gives.cons hd (Gives.cons (Gives.cons (Gives.id _).tl.tl.tl.hd (Gives.id _).tl.tl.hd)
          (Gives.id _).tl.tl.tl.tl))) ih'
      have := ((Gives.id (θ := θ) (.cons takeB.code (.cons (ofBits w) (.cons (listT acc) (listT (a :: l)))))).tl.tl.tl.ite_true
        (H := .tl (.tl .id)) (by simp [listT]) (hnz.ite_true (H := .tl (.tl .id)) e r))
      rw [h2, List.take_succ_cons, List.drop_succ_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
      refine this.mono ?_
      simp only [List.length_cons]
      nlinarith

end Take

section Picks

end Picks

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Values of formulas with named constants

`KV θ κ S F x w c`: all runs of the formula `F` at `x` stop; the accepting ones have cost at most `c` and use names of
constants in `S`; with the constants `κ` the sum of their weights is `w`.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- The value of a formula. -/
def KV (θ : List Bool → A) (κ : List Bool → R) (S : Set (List Bool)) (F : Fm) (x : Tree) (w : R) (c : ℕ) : Prop :=
  ∃ l, Ev θ F x l ∧ (∀ r ∈ l, r.cost ≤ c ∧ ∀ p ∈ r.bill, p ∈ S) ∧ val κ l = w

theorem wt_mul (κ : List Bool → R) {r s u : Run A} (h1 : u.th = r.th * s.th) (h2 : u.bill = r.bill ++ s.bill) :
    wt κ u = wt κ r * wt κ s := by
  rw [wt, wt, wt, h1, h2, map_mul, List.map_append, List.prod_append]
  ring

namespace KV

variable {κ : List Bool → R} {S : Set (List Bool)} {F G H : Fm} {x : Tree} {w w' : R} {c d : ℕ}

theorem mono (h : KV θ κ S F x w c) (hc : c ≤ d) : KV θ κ S F x w d := by
  obtain ⟨l, h1, h2, h3⟩ := h
  exact ⟨l, h1, fun r hr => ⟨(h2 r hr).1.trans hc, (h2 r hr).2⟩, h3⟩

theorem congr (h : KV θ κ S F x w c) (hw : w = w') : KV θ κ S F x w' c := hw ▸ h

theorem hl (h : KV θ κ S F x w c) : Hl θ F x := by
  obtain ⟨l, h1, -⟩ := h
  exact h1.hl

theorem evl (h : KV θ κ S F x w c) : (∀ r ∈ NS1.evl θ F x, r.cost ≤ c ∧ ∀ p ∈ r.bill, p ∈ S) ∧
    val κ (NS1.evl θ F x) = w := by
  obtain ⟨l, h1, h2, h3⟩ := h
  rw [h1.evl]
  exact ⟨h2, h3⟩

theorem of_does {Q : List (A × Tree)} (h : Does θ F x Q c) :
    KV θ κ S F x (algebraMap A R (Q.map Prod.fst).sum) c := by
  obtain ⟨l, h1, h2, h3⟩ := h
  refine ⟨l, h1, fun r hr => ⟨(h2 r hr).2.1, ?_⟩, ?_⟩
  · rw [(h2 r hr).1]
    simp
  · rw [val_plain fun r hr => (h2 r hr).1, pval]
    have := h3 fun _ => 1
    simp only [mul_one, wsum] at this
    rw [this]

theorem of_gives {o : Tree} (h : Gives θ F x o c) : KV θ κ S F x 1 c := (of_does h).congr (by simp)

theorem fail (x : Tree) : KV θ κ S .fail x 0 0 := ⟨[], .fail x, by simp, by simp [val]⟩

theorem mul {o : Tree} (h : Gives θ F x o c) (ho : o.path ∈ S) : KV θ κ S (.mul F) x (κ o.path) (c + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := h
  have hout : ∀ r ∈ l, r.out = o := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.mul e1, ?_, ?_⟩
  · intro u hu
    rw [List.mem_map] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    refine ⟨by simpa using a2, fun p hp => ?_⟩
    rw [a1, List.nil_append, List.mem_singleton] at hp
    rw [hp, hout r hr]
    exact ho
  · have h1 : (l.map fun r : Run A => (⟨r.cost + 1, r.th, r.bill ++ [r.out.path], .nil⟩ : Run A)).map (wt κ) =
        l.map fun r => algebraMap A R r.th * κ o.path := by
      rw [List.map_map]
      refine List.map_congr_left fun r hr => ?_
      simp [wt, (e2 r hr).1, hout r hr]
    rw [val, h1, List.sum_map_mul_right]
    have h2 := e3 fun _ => 1
    simp only [mul_one, wsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h2
    have h3 : (l.map fun r => algebraMap A R r.th).sum = 1 := by
      have h4 := congrArg (algebraMap A R) h2
      rw [map_list_sum, List.map_map, map_one] at h4
      exact h4
    rw [h3, one_mul]

theorem cons (hF : KV θ κ S F x w c) (hG : KV θ κ S G x w' d) : KV θ κ S (.cons F G) x (w * w') (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  refine ⟨_, Ev.cons e1 f1, ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    refine ⟨?_, fun p hp => ?_⟩
    · have h1 := (e2 r hr).1
      have h2 := (f2 s hs).1
      simp only [Run.tick, Run.seq]
      omega
    · simp only [Run.tick, Run.seq, List.mem_append] at hp
      exact hp.elim ((e2 r hr).2 p) ((f2 s hs).2 p)
  · rw [val, sum_flatMap_map]
    have h1 : ∀ r : Run A, ((l'.map fun s => (r.seq s).tick (.cons r.out s.out)).map (wt κ)).sum = wt κ r * w' := by
      intro r
      rw [← f3, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      exact List.map_congr_left fun s _ => wt_mul κ rfl rfl
    simp only [h1]
    rw [List.sum_map_mul_right, ← e3]
    rfl

theorem ite_true {o : Tree} (hF : Gives θ F x o c) (ho : o ≠ .nil) (hG : KV θ κ S G x w d) :
    KV θ κ S (.ite F G H) x w (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  have hout : ∀ r ∈ l, r.out = o := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r _ _ => f1) (fun r hr h => absurd ((hout r hr).symm.trans h) ho), ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2⟩ := f2 s hs
    refine ⟨?_, fun p hp => ?_⟩
    · simp only [Run.seq, Run.tick]
      omega
    · simp only [Run.tick, Run.seq, a1, List.nil_append] at hp
      exact b2 p hp
  · rw [val, sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.map fun s => (r.seq s).tick s.out).map (wt κ)).sum = algebraMap A R r.th * w := by
      intro r hr
      rw [← f3, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun s _ => ?_
      rw [Function.comp_apply, wt_mul κ (r := r) (s := s) rfl rfl, wt, (e2 r hr).1]
      simp
    rw [List.map_congr_left h1, List.sum_map_mul_right]
    have h2 := e3 fun _ => 1
    simp only [mul_one, wsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h2
    have h4 := congrArg (algebraMap A R) h2
    rw [map_list_sum, List.map_map, map_one] at h4
    have h3 : (l.map fun r => algebraMap A R r.th).sum = 1 := h4
    rw [h3, one_mul]

theorem ite_false (hF : Gives θ F x .nil c) (hH : KV θ κ S H x w d) : KV θ κ S (.ite F G H) x w (c + d + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hH
  have hout : ∀ r ∈ l, r.out = .nil := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  refine ⟨_, Ev.ite (L := fun _ => l') e1 (fun r hr h => absurd (hout r hr) h) (fun r _ _ => f1), ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, rfl⟩ := hu
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2⟩ := f2 s hs
    refine ⟨?_, fun p hp => ?_⟩
    · simp only [Run.seq, Run.tick]
      omega
    · simp only [Run.tick, Run.seq, a1, List.nil_append] at hp
      exact b2 p hp
  · rw [val, sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.map fun s => (r.seq s).tick s.out).map (wt κ)).sum = algebraMap A R r.th * w := by
      intro r hr
      rw [← f3, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun s _ => ?_
      rw [Function.comp_apply, wt_mul κ (r := r) (s := s) rfl rfl, wt, (e2 r hr).1]
      simp
    rw [List.map_congr_left h1, List.sum_map_mul_right]
    have h2 := e3 fun _ => 1
    simp only [mul_one, wsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h2
    have h4 := congrArg (algebraMap A R) h2
    rw [map_list_sum, List.map_map, map_one] at h4
    have h3 : (l.map fun r => algebraMap A R r.th).sum = 1 := h4
    rw [h3, one_mul]

theorem either (hG : KV θ κ S G x w c) (hH : KV θ κ S H x w' d) :
    KV θ κ S (.ite .guess G H) x (w + w') (max c d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hG
  obtain ⟨l', f1, f2, f3⟩ := hH
  refine ⟨_, Ev.ite (L := fun r => if r.out = .nil then l' else l) (Ev.guess x) (fun r _ h => by rw [if_neg h]; exact e1)
    (fun r _ h => by rw [if_pos h]; exact f1), ?_, ?_⟩
  · intro u hu
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, List.mem_map, Run.det, Tree.one,
      if_true, reduceCtorEq, if_false] at hu
    rcases hu with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · obtain ⟨a1, a2⟩ := f2 s hs
      refine ⟨?_, fun p hp => ?_⟩
      · simp only [Run.seq, Run.tick]
        omega
      · simp only [Run.seq, Run.tick, List.nil_append] at hp
        exact a2 p hp
    · obtain ⟨a1, a2⟩ := e2 s hs
      refine ⟨?_, fun p hp => ?_⟩
      · simp only [Run.seq, Run.tick]
        omega
      · simp only [Run.seq, Run.tick, List.nil_append] at hp
        exact a2 p hp
  · rw [← e3, ← f3, val, val, val, add_comm]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.sum_append, List.map_map,
      Run.det, Tree.one, if_true, reduceCtorEq, if_false]
    congr 1
    · congr 1
      refine List.map_congr_left fun t _ => ?_
      simp [wt, Run.seq, Run.tick]
    · congr 1
      refine List.map_congr_left fun t _ => ?_
      simp [wt, Run.seq, Run.tick]

/-- A plain computation, then a value. -/
theorem app {p : Tree} {Q : List (A × Tree)} {ω : Tree → R} (hF : Does θ F x Q c)
    (hG : ∀ q ∈ Q, KV θ κ S (Fm.ofTree p) q.2 (ω q.2) d) :
    KV θ κ S (NS1.app p F) x (Q.map fun q => algebraMap A R q.1 * ω q.2).sum (c + d + 2) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  have hG' : ∀ s ∈ l, KV θ κ S (Fm.ofTree p) s.out (ω s.out) d := by
    intro s hs
    obtain ⟨-, -, q, hq, h⟩ := e2 s hs
    rw [← h]
    exact hG q hq
  refine ⟨_, Ev.app e1 fun s hs => (hG' s hs).hl, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, hs, t, ht, h1, h2, h3, -⟩ := mem_app hu
    obtain ⟨a1, a2, -⟩ := e2 s hs
    obtain ⟨b1, b2⟩ := (hG' s hs).evl.1 t ht
    refine ⟨by omega, fun p hp => ?_⟩
    rw [h2, a1, List.nil_append] at hp
    exact b2 p hp
  · rw [val, sum_flatMap_map]
    have h1 : ∀ s ∈ l, (((NS1.evl θ (Fm.ofTree p) s.out).map fun t => ((Run.det 1 p).seq s).seq t |>.tick t.out).map
        (wt κ)).sum = algebraMap A R s.th * ω s.out := by
      intro s hs
      rw [← (hG' s hs).evl.2, val, List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp [wt, Run.seq, Run.tick, Run.det, (e2 s hs).1, mul_assoc]
    rw [List.map_congr_left h1]
    -- functions with values in `R`
    have h2 : ∀ (L : List (Run A)) (P : List (A × Tree)),
        (∀ φ : Tree → A, (L.map fun r => r.th * φ r.out).sum = wsum P φ) →
        (L.map fun s => algebraMap A R s.th * ω s.out).sum = (P.map fun q => algebraMap A R q.1 * ω q.2).sum := by
      intro L P hLP
      classical
      let D : Finset Tree := (L.map Run.out).toFinset ∪ (P.map Prod.snd).toFinset
      have k1 : (L.map fun s => algebraMap A R s.th * ω s.out).sum =
          ∑ o ∈ D, algebraMap A R (L.map fun r => r.th * if r.out = o then 1 else 0).sum * ω o := by
        have : ∀ s ∈ L, algebraMap A R s.th * ω s.out =
            ∑ o ∈ D, algebraMap A R (s.th * if s.out = o then 1 else 0) * ω o := by
          intro s hs
          rw [Finset.sum_eq_single s.out]
          · simp
          · intro o _ ho
            rw [if_neg (Ne.symm ho), mul_zero, map_zero, zero_mul]
          · intro h
            exact absurd (Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_map_of_mem hs))) h
        rw [List.map_congr_left this]
        clear this
        have : ∀ L : List (Run A), (L.map fun s => ∑ o ∈ D, algebraMap A R (s.th * if s.out = o then 1 else 0) * ω o).sum =
            ∑ o ∈ D, algebraMap A R (L.map fun r => r.th * if r.out = o then 1 else 0).sum * ω o := by
          intro L
          induction L with
          | nil => simp
          | cons s L ih =>
            rw [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun o _ => ?_
            rw [List.map_cons, List.sum_cons, map_add, add_mul]
        exact this L
      have k2 : (P.map fun q => algebraMap A R q.1 * ω q.2).sum =
          ∑ o ∈ D, algebraMap A R (P.map fun q => q.1 * if q.2 = o then 1 else 0).sum * ω o := by
        have : ∀ q ∈ P, algebraMap A R q.1 * ω q.2 =
            ∑ o ∈ D, algebraMap A R (q.1 * if q.2 = o then 1 else 0) * ω o := by
          intro q hq
          rw [Finset.sum_eq_single q.2]
          · simp
          · intro o _ ho
            rw [if_neg (Ne.symm ho), mul_zero, map_zero, zero_mul]
          · intro h
            exact absurd (Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map_of_mem hq))) h
        rw [List.map_congr_left this]
        clear this
        have : ∀ P : List (A × Tree), (P.map fun q => ∑ o ∈ D, algebraMap A R (q.1 * if q.2 = o then 1 else 0) * ω o).sum =
            ∑ o ∈ D, algebraMap A R (P.map fun q => q.1 * if q.2 = o then 1 else 0).sum * ω o := by
          intro P
          induction P with
          | nil => simp
          | cons s P ih =>
            rw [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun o _ => ?_
            rw [List.map_cons, List.sum_cons, map_add, add_mul]
        exact this P
      rw [k1, k2]
      refine Finset.sum_congr rfl fun o _ => ?_
      have := hLP fun t => if t = o then 1 else 0
      rw [this]
      rfl
    exact h2 l Q e3

theorem lett {Q : List (A × Tree)} {ω : Tree → R} (hF : Does θ F x Q c)
    (hG : ∀ q ∈ Q, KV θ κ S G q.2 (ω q.2) d) :
    KV θ κ S (NS1.lett F G) x (Q.map fun q => algebraMap A R q.1 * ω q.2).sum (c + d + 2) :=
  app (p := G.code) hF (by rw [Fm.ofTree_code]; exact hG)

theorem app_gives {p o : Tree} (hF : Gives θ F x o c) (hG : KV θ κ S (Fm.ofTree p) o w d) :
    KV θ κ S (NS1.app p F) x w (c + d + 2) :=
  (app (Q := [(1, o)]) (ω := fun _ => w) hF (by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hG)).congr (by simp)

/-- Apply a program that is the value of a formula. -/
theorem run {p y : Tree} {e : ℕ} (hF : Gives θ F x p c) (hG : Gives θ G x y d)
    (h : KV θ κ S (Fm.ofTree p) y w e) : KV θ κ S (.run F G) x w (c + d + e + 1) := by
  obtain ⟨l, e1, e2, e3⟩ := hF
  obtain ⟨l', f1, f2, f3⟩ := hG
  have ho : ∀ r ∈ l, r.out = p := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := e2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  have ho' : ∀ r ∈ l', r.out = y := by
    intro r hr
    obtain ⟨-, -, q, hq, h⟩ := f2 r hr
    rw [List.mem_singleton] at hq
    subst hq
    exact h.symm
  have one : ∀ {L : List (Run A)} {o : Tree}, (∀ φ : Tree → A, (L.map fun r => r.th * φ r.out).sum = wsum [(1, o)] φ) →
      (L.map fun r => algebraMap A R r.th).sum = 1 := by
    intro L o hL
    have h2 := hL fun _ => 1
    simp only [mul_one, wsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h2
    have h4 := congrArg (algebraMap A R) h2
    rw [map_list_sum, List.map_map, map_one] at h4
    exact h4
  refine ⟨_, Ev.run' e1 f1 fun r hr s hs => by rw [ho r hr, ho' s hs]; exact h.hl, ?_, ?_⟩
  · intro u hu
    simp only [List.mem_flatMap, List.mem_map] at hu
    obtain ⟨r, hr, s, hs, t, ht, rfl⟩ := hu
    rw [ho r hr, ho' s hs] at ht
    obtain ⟨a1, a2, -⟩ := e2 r hr
    obtain ⟨b1, b2, -⟩ := f2 s hs
    obtain ⟨c1, c2⟩ := h.evl.1 t ht
    refine ⟨?_, fun p hp => ?_⟩
    · simp only [Run.seq, Run.tick]
      omega
    · simp only [Run.seq, Run.tick, a1, b1, List.nil_append] at hp
      exact c2 p hp
  · rw [val, sum_flatMap_map]
    have h1 : ∀ r ∈ l, ((l'.flatMap fun s => (NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
        ((r.seq s).seq t).tick t.out).map (wt κ)).sum = algebraMap A R r.th * w := by
      intro r hr
      rw [sum_flatMap_map]
      have h2 : ∀ s ∈ l', (((NS1.evl θ (Fm.ofTree r.out) s.out).map fun t =>
          ((r.seq s).seq t).tick t.out).map (wt κ)).sum = algebraMap A R s.th * (algebraMap A R r.th * w) := by
        intro s hs
        rw [ho r hr, ho' s hs, List.map_map, ← h.evl.2, val, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun t _ => ?_
        simp only [Function.comp_apply, wt, Run.seq, Run.tick, (e2 r hr).1, (f2 s hs).1, List.nil_append, map_mul]
        ring
      rw [List.map_congr_left h2, List.sum_map_mul_right, one f3, one_mul]
    rw [List.map_congr_left h1, List.sum_map_mul_right, one e3, one_mul]

end KV

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Full tries of constants; reading in a tree of pairs
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R]

namespace KT

/-- All names of length `n`. -/
def full : ℕ → (List Bool → R) → KT R
  | 0, f => leaf (f [])
  | n + 1, f => node (full n fun w => f (false :: w)) (full n fun w => f (true :: w))

theorem lk_full {n : ℕ} (f : List Bool → R) {w : List Bool} (h : w.length = n) : (full n f).lk (w ++ [false]) = f w := by
  induction n generalizing f w with
  | zero =>
    rw [List.length_eq_zero_iff] at h
    subst h
    rfl
  | succ n ih =>
    cases w with
    | nil => simp at h
    | cons b w =>
      rw [List.length_cons, Nat.add_right_cancel_iff] at h
      cases b with
      | true => exact ih (fun w => f (true :: w)) h
      | false => exact ih (fun w => f (false :: w)) h

theorem inB_full {n : ℕ} (f : List Bool → R) {w : List Bool} (h : w.length = n) : (full n f).InB 1 (w ++ [false]) := by
  induction n generalizing f w with
  | zero =>
    rw [List.length_eq_zero_iff] at h
    subst h
    exact ⟨0, zero_lt_one, rfl⟩
  | succ n ih =>
    cases w with
    | nil => simp at h
    | cons b w =>
      rw [List.length_cons, Nat.add_right_cancel_iff] at h
      cases b with
      | true => exact ih (fun w => f (true :: w)) h
      | false => exact ih (fun w => f (false :: w)) h

theorem nds_full (n : ℕ) (f : List Bool → R) : (full n f).nds + 1 = 2 ^ (n + 1) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    have h1 := ih fun w => f (false :: w)
    have h2 := ih fun w => f (true :: w)
    rw [full, nds, pow_succ]
    omega

theorem ht_full (n : ℕ) (f : List Bool → R) : (full n f).ht = n := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [full, ht, ih, ih, max_self]

end KT

/-- All words of a given length. -/
def wd : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => (wd m).map (true :: ·) ++ (wd m).map (false :: ·)

theorem length_of_mem_wd {m : ℕ} {w : List Bool} (h : w ∈ wd m) : w.length = m := by
  induction m generalizing w with
  | zero =>
    simp only [wd, List.mem_singleton] at h
    subst h
    rfl
  | succ m ih =>
    simp only [wd, List.mem_append, List.mem_map] at h
    rcases h with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;> simp [ih hv]

theorem val_lt_of_length {m : ℕ} {w : List Bool} (h : w.length = m) : KT.val w < 2 ^ m := by
  induction w generalizing m with
  | nil =>
    subst h
    simp [KT.val]
  | cons b w ih =>
    subst h
    have := ih rfl
    rw [KT.val, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem exists_word {m k : ℕ} (h : k < 2 ^ m) : ∃ w : List Bool, w.length = m ∧ KT.val w = k := by
  induction m generalizing k with
  | zero => exact ⟨[], rfl, by simp [KT.val]; omega⟩
  | succ m ih =>
    rw [pow_succ] at h
    obtain ⟨w, h1, h2⟩ := ih (k := k / 2) (by omega)
    refine ⟨decide (k % 2 = 1) :: w, by simp [h1], ?_⟩
    rw [KT.val, h2]
    by_cases h3 : k % 2 = 1
    · simp [h3]
      omega
    · simp [h3]
      omega

/-- Sums over words. -/
theorem sum_wd (m : ℕ) (f : ℕ → R) : ((wd m).map fun w => f (KT.val w)).sum = ∑ k ∈ Finset.range (2 ^ m), f k := by
  induction m generalizing f with
  | zero => simp [wd, KT.val]
  | succ m ih =>
    have h1 := ih fun k => f (1 + 2 * k)
    have h2 := ih fun k => f (2 * k)
    have e1 : ((wd (m + 1)).map fun w => f (KT.val w)).sum =
        ((wd m).map fun w => f (1 + 2 * KT.val w)).sum + ((wd m).map fun w => f (2 * KT.val w)).sum := by
      simp [wd, KT.val, Function.comp_def]
    rw [e1, h1, h2, pow_succ, mul_comm]
    clear e1 h1 h2 ih
    induction 2 ^ m with
    | zero => simp
    | succ n ih =>
      rw [mul_add, mul_one, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        ← ih]
      have e : 1 + 2 * n = 2 * n + 1 := by ring
      rw [e]
      ring

/-- Sums over reversed words. -/
theorem sum_wd_reverse (m : ℕ) (f : List Bool → R) :
    ((wd m).map fun w => f w.reverse).sum = ((wd m).map f).sum := by
  have h : ∀ (n : ℕ) (f : List Bool → R), ((wd (n + 1)).map f).sum =
      ((wd n).map fun w => f (w ++ [true])).sum + ((wd n).map fun w => f (w ++ [false])).sum := by
    intro n
    induction n with
    | zero => intro f; simp [wd]
    | succ n ih =>
      intro f
      have e : ((wd (n + 1 + 1)).map f).sum = ((wd (n + 1)).map fun w => f (true :: w)).sum +
          ((wd (n + 1)).map fun w => f (false :: w)).sum := by
        rw [wd]
        simp [Function.comp_def]
      rw [e, ih, ih]
      have e2 : ∀ b : Bool, ((wd (n + 1)).map fun w => f (w ++ [b])).sum =
          ((wd n).map fun w => f (true :: (w ++ [b]))).sum + ((wd n).map fun w => f (false :: (w ++ [b]))).sum := by
        intro b
        simp [wd, Function.comp_def]
      rw [e2, e2]
      ring
  induction m generalizing f with
  | zero => simp [wd]
  | succ m ih =>
    rw [h m f]
    have e : ((wd (m + 1)).map fun w => f w.reverse).sum = ((wd m).map fun w => f (w.reverse ++ [true])).sum +
        ((wd m).map fun w => f (w.reverse ++ [false])).sum := by
      simp [wd, Function.comp_def]
    rw [e, ih fun w => f (w ++ [true]), ih fun w => f (w ++ [false])]

/-- Reading along a path. -/
def look : List Bool → Tree → Tree
  | [], t => t
  | true :: p, t => look p t.tl
  | false :: p, t => look p t.hd

theorem look_append (p q : List Bool) (t : Tree) : look (p ++ q) t = look q (look p t) := by
  induction p generalizing t with
  | nil => rfl
  | cons b p ih => cases b <;> exact ih _

/-- Pairs of neighbours. -/
def pairL : List Tree → List Tree
  | [] => []
  | [a] => [.cons a .nil]
  | a :: b :: l => .cons a b :: pairL l

theorem length_pairL (l : List Tree) : (pairL l).length = (l.length + 1) / 2 := by
  induction l using pairL.induct with
  | case1 => rfl
  | case2 a => simp [pairL]
  | case3 a b l ih =>
    simp only [pairL, List.length_cons, ih]
    omega

theorem getD_pairL (l : List Tree) (k : ℕ) : ((pairL l).getD k .nil).hd = l.getD (2 * k) .nil ∧
    ((pairL l).getD k .nil).tl = l.getD (1 + 2 * k) .nil := by
  induction l using pairL.induct generalizing k with
  | case1 => simp [pairL]
  | case2 a =>
    cases k with
    | zero => simp [pairL]
    | succ k => simp [pairL]
  | case3 a b l ih =>
    cases k with
    | zero => simp [pairL]
    | succ k =>
      have h := ih k
      have e1 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      have e2 : 1 + 2 * (k + 1) = 1 + 2 * k + 1 + 1 := by ring
      rw [e2, e1]
      simpa only [pairL, List.getD_cons_succ] using h

/-- Reading in the tree of pairs. -/
theorem look_pairs (m : ℕ) (xs : List Tree) (hx : xs.length ≤ 2 ^ m) (p : List Bool) (hp : p.length = m) :
    look p (listT (pairL^[m] xs)).hd = xs.getD (KT.val p.reverse) .nil := by
  induction m generalizing xs p with
  | zero =>
    rw [List.length_eq_zero_iff] at hp
    subst hp
    cases xs <;> rfl
  | succ m ih =>
    obtain ⟨p, b, rfl⟩ : ∃ q b, p = q ++ [b] := by
      rcases List.eq_nil_or_concat p with rfl | ⟨q, b, h⟩
      · simp at hp
      · exact ⟨q, b, by simpa using h⟩
    rw [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hp
    rw [Function.iterate_succ_apply, look_append, ih (pairL xs) (by rw [length_pairL]; rw [pow_succ] at hx; omega) p hp,
      List.reverse_append, List.reverse_singleton, List.singleton_append, KT.val]
    have h := getD_pairL xs (KT.val p.reverse)
    cases b with
    | true => exact h.2
    | false =>
      have e : (if false = true then 1 else 0) + 2 * KT.val p.reverse = 2 * KT.val p.reverse := by simp
      rw [e]
      exact h.1

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Low degree is fast (Lemma 1)

A polynomial of degree at most `d` that is computed by an arithmetic circuit with `s` gates has, at every
point, a value that is a sum over parse trees. A parse tree with `i` leaves reads `2 * i - 1` entries of
fixed tables of the circuit and `i` coordinates of the point; only `i ≤ d` occurs.
-/

namespace Nc

open Finset

section Circuits

variable {F : Type*} [CommSemiring F] {σ : Type*}

/-- Entry `k` of the list `l` is a variable, a constant, or the sum or product of two earlier entries. -/
def IsStep (l : ℕ → MvPolynomial σ F) (k : ℕ) : Prop :=
  (∃ i : σ, l k = MvPolynomial.X i) ∨ (∃ a : F, l k = MvPolynomial.C a) ∨
    (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)

/-- `p` is computed by an arithmetic circuit with `s` gates (inputs and constants count as gates). -/
def Computes (p : MvPolynomial σ F) (s : ℕ) : Prop :=
  ∃ l : ℕ → MvPolynomial σ F, (∀ k < s, IsStep l k) ∧ ∃ k < s, l k = p

end Circuits

variable {F : Type*} [Field F] {σ : Type*} {s : ℕ}

section Proof

/-- `p` along the line through 0 and `u`. -/
noncomputable def line (u : σ → F) : MvPolynomial σ F →ₐ[F] Polynomial F :=
  MvPolynomial.aeval fun l => Polynomial.C (u l) * Polynomial.X

theorem eval_one_line (u : σ → F) (p : MvPolynomial σ F) :
    (line u p).eval 1 = MvPolynomial.eval u p := by
  have : ((Polynomial.evalRingHom (1 : F)).comp (line u).toRingHom) =
      (MvPolynomial.eval u : MvPolynomial σ F →+* F) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [line]
    · intro i; simp [line]
  exact DFunLike.congr_fun this p

end Proof

end Nc

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# A polynomial along a line

The parts of positive degree of the gates of a circuit, along a line, are power series that satisfy quadratic
equations; `W` sums the coefficients of products of them.
-/

set_option linter.unusedSectionVars false

namespace Nc.Acc

open Finset

variable {F : Type*} [CommRing F] {σ : Type*} {s : ℕ}

/-- `p` along the line through 0 and `u`. -/
noncomputable def line (u : σ → F) : MvPolynomial σ F →ₐ[F] Polynomial F :=
  MvPolynomial.aeval fun l => Polynomial.C (u l) * Polynomial.X

theorem line_coeff_zero (u : σ → F) (p : MvPolynomial σ F) :
    (line u p).coeff 0 = MvPolynomial.constantCoeff p := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have : ((Polynomial.evalRingHom (0 : F)).comp (line u).toRingHom) =
      (MvPolynomial.constantCoeff : MvPolynomial σ F →+* F) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [line]
    · intro i; simp [line]
  exact DFunLike.congr_fun this p

theorem eval_one_line (u : σ → F) (p : MvPolynomial σ F) :
    (line u p).eval 1 = MvPolynomial.eval u p := by
  have : ((Polynomial.evalRingHom (1 : F)).comp (line u).toRingHom) =
      (MvPolynomial.eval u : MvPolynomial σ F →+* F) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [line]
    · intro i; simp [line]
  exact DFunLike.congr_fun this p

/-- The inner part of a product. -/
theorem coeff_mul_succ (a b : Polynomial F) (m : ℕ) :
    (a * b).coeff (m + 1) = a.coeff 0 * b.coeff (m + 1) + b.coeff 0 * a.coeff (m + 1) +
      ∑ j ∈ range m, a.coeff (j + 1) * b.coeff (m - j) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_succ']
  simp only [Nat.sub_zero, Nat.sub_self, Nat.add_sub_add_right]
  ring

end Nc.Acc

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, proof of Lemma lem:lowdeg: chains
-/

namespace Paper

open Finset Nc.Acc
open Nc (IsStep)

variable {F : Type*} [CommRing F] {σ : Type*} {s : ℕ}

/-- **Paper: proof of Lemma lem:lowdeg, the chain constants and the degree identity.** "(g,1) = ∑_l λ_{g,l} x_l,
(g,i) = ∑ κ_{g,g′,g″} ∑_{0<j<i} (g′,j)(g″,i−j) for i ≥ 2. These constants do not depend on i." Here (g,m+1) is the
coefficient of degree m+1 of the gate along the line through the point u, which is the part of that degree at u. -/
theorem lem_lowdeg_chains [Fintype σ] (l : ℕ → MvPolynomial σ F) (hl : ∀ k < s, IsStep l k) :
    ∃ (κ : Fin s → Fin s → F) (lam : Fin s → σ → F) (left right : Fin s → Fin s),
      ∀ (k : Fin s) (u : σ → F) (m : ℕ),
        (line u (l k)).coeff (m + 1) = (if m = 0 then ∑ i, lam k i * u i else 0) +
          ∑ h, κ k h * ∑ j ∈ range m, (line u (l (left h))).coeff (j + 1) *
            (line u (l (right h))).coeff (m - j) := by
  classical
  have hch : ∀ k : Fin s, ∃ a b : Fin s, (∃ i < k.1, ∃ j < k.1, l k = l i * l j) →
      (a.1 < k.1 ∧ b.1 < k.1 ∧ l k = l a * l b) := by
    intro k
    by_cases h : ∃ i < k.1, ∃ j < k.1, l k = l i * l j
    · obtain ⟨i, hi, j, hj, e⟩ := h
      exact ⟨⟨i, hi.trans k.2⟩, ⟨j, hj.trans k.2⟩, fun _ => ⟨hi, hj, e⟩⟩
    · exact ⟨k, k, fun h' => absurd h' h⟩
  choose left right hlr using hch
  have key : ∀ n (hn : n < s), ∃ (κ : Fin s → F) (lam : σ → F), ∀ (u : σ → F) (m : ℕ),
        (line u (l n)).coeff (m + 1) = (if m = 0 then ∑ i, lam i * u i else 0) +
          ∑ h, κ h * ∑ j ∈ range m, (line u (l (left h))).coeff (j + 1) *
            (line u (l (right h))).coeff (m - j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases hmul : ∃ i < n, ∃ j < n, l n = l i * l j
      · obtain ⟨ha, hb, e⟩ := hlr ⟨n, hn⟩ hmul
        obtain ⟨κa, la, Ha⟩ := ih _ ha (left ⟨n, hn⟩).2
        obtain ⟨κb, lb, Hb⟩ := ih _ hb (right ⟨n, hn⟩).2
        set a := left ⟨n, hn⟩ with hadef
        set b := right ⟨n, hn⟩ with hbdef
        refine ⟨fun h => MvPolynomial.constantCoeff (l a) * κb h +
          MvPolynomial.constantCoeff (l b) * κa h + (if h = ⟨n, hn⟩ then 1 else 0),
          fun i => MvPolynomial.constantCoeff (l a) * lb i +
          MvPolynomial.constantCoeff (l b) * la i, fun u m => ?_⟩
        have e' : l n = l a * l b := e
        rw [e', map_mul, coeff_mul_succ, line_coeff_zero, line_coeff_zero, Ha, Hb]
        have h1 : ∀ X : Fin s → F, ∑ h, (MvPolynomial.constantCoeff (l a) * κb h +
          MvPolynomial.constantCoeff (l b) * κa h + (if h = ⟨n, hn⟩ then 1 else 0)) * X h =
          MvPolynomial.constantCoeff (l a) * ∑ h, κb h * X h +
          MvPolynomial.constantCoeff (l b) * ∑ h, κa h * X h + X ⟨n, hn⟩ := by
          intro X
          simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, ite_mul, one_mul,
            zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [h1]
        by_cases hm : m = 0
        · subst hm
          simp only [if_true, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
          simp [Finset.mul_sum]
        · simp only [hm, if_false]
          ring
      · have hs := hl n hn
        rcases hs with ⟨i, e⟩ | ⟨c, e⟩ | ⟨i, hi, j, hj, e⟩ | h
        · refine ⟨0, fun i' => if i' = i then 1 else 0, fun u m => ?_⟩
          rw [e]
          simp only [line, MvPolynomial.aeval_X, Polynomial.coeff_C_mul, Polynomial.coeff_X]
          by_cases hm : m = 0
          · subst hm; simp
          · simp [hm]
        · refine ⟨0, 0, fun u m => ?_⟩
          rw [e]
          simp [line]
        · obtain ⟨κa, la, Ha⟩ := ih i hi (hi.trans hn)
          obtain ⟨κb, lb, Hb⟩ := ih j hj (hj.trans hn)
          refine ⟨κa + κb, la + lb, fun u m => ?_⟩
          rw [e, map_add, Polynomial.coeff_add, Ha, Hb]
          simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
          by_cases hm : m = 0
          · simp only [hm, if_true]; ring
          · simp only [hm, if_false]; ring
        · exact absurd h hmul
  choose κ lam H using key
  exact ⟨fun k => κ k k.2, fun k => lam k k.2, left, right, fun k u m => H k k.2 u m⟩

end Paper

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Low degree is fast, over commutative rings

The parts of positive degree of the gates of a circuit, along a line, are power series that satisfy quadratic
equations; `W` sums the coefficients of products of them.
-/

set_option linter.unusedSectionVars false

namespace Nc.Acc

open Finset

variable {F : Type*} [CommRing F] {σ : Type*} {s : ℕ}

open PowerSeries in
/-- The parts of positive degree along the line. -/
noncomputable def ser (u : σ → F) (q : MvPolynomial σ F) : PowerSeries F := PowerSeries.mk fun m => (line u q).coeff (m + 1)

theorem ser_zero (u : σ → F) : ser u (0 : MvPolynomial σ F) = 0 := by
  ext m
  simp [ser]

/-- The quadratic equations. -/
theorem exists_series [Fintype σ] {p : MvPolynomial σ F} {M : ℕ} (hp : Computes p s) (hs : s ≤ 2 ^ M) :
    ∃ (κ : ℕ → ℕ → ℕ → F) (lam : ℕ → σ → F) (P : ℕ → MvPolynomial σ F) (out : ℕ), out < 2 ^ M ∧ P out = p ∧
      ∀ (u : σ → F) (g : ℕ), ser u (P g) = PowerSeries.C (∑ i, lam g i * u i) + PowerSeries.X *
        ∑ l ∈ range (2 ^ M), ∑ r ∈ range (2 ^ M), PowerSeries.C (κ g l r) * (ser u (P l) * ser u (P r)) := by
  classical
  obtain ⟨l, hl, k, hk, rfl⟩ := hp
  obtain ⟨κ, lam, left, right, H⟩ := Paper.lem_lowdeg_chains l hl
  refine ⟨fun g a b => if h : g < s then ∑ j, if (left j).1 = a ∧ (right j).1 = b then κ ⟨g, h⟩ j else 0 else 0,
    fun g => if h : g < s then lam ⟨g, h⟩ else 0, fun g => if g < s then l g else 0, k, hk.trans_le hs,
    if_pos hk, fun u g => ?_⟩
  by_cases hg : g < s
  · simp only [dif_pos hg, if_pos hg]
    have h1 : ∑ a ∈ range (2 ^ M), ∑ b ∈ range (2 ^ M),
        PowerSeries.C (∑ j, if (left j).1 = a ∧ (right j).1 = b then κ ⟨g, hg⟩ j else 0) *
          (ser u (if a < s then l a else 0) * ser u (if b < s then l b else 0)) =
        ∑ j, PowerSeries.C (κ ⟨g, hg⟩ j) * (ser u (l (left j)) * ser u (l (right j))) := by
      simp only [map_sum, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single (left j).1, Finset.sum_eq_single (right j).1]
      · simp
      · intro b _ hb
        rw [if_neg fun h => hb h.2.symm, map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_range.2 ((right j).2.trans_le hs)) h
      · intro a _ ha
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [if_neg fun h => ha h.1.symm, map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_range.2 ((left j).2.trans_le hs)) h
    rw [h1]
    ext m
    have h2 := H ⟨g, hg⟩ u m
    cases m with
    | zero =>
      simp only [ser, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_zero_X_mul, add_zero]
      simpa using h2
    | succ m =>
      simp only [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        if_false, map_sum, PowerSeries.coeff_C_mul, Finset.sum_const_zero, zero_add]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, zero_add] at h2
      rw [ser, PowerSeries.coeff_mk, h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp only [ser, PowerSeries.coeff_mk]
      congr 2
      omega
  · simp only [dif_neg hg, if_neg hg, ser_zero]
    simp

/-- The sum of the coefficients of degree at most `b` of a product. -/
noncomputable def W (E : ℕ → PowerSeries F) (b : ℕ) (gs : List ℕ) : F :=
  ∑ n ∈ range (b + 1), PowerSeries.coeff n (gs.map E).prod

theorem W_nil (E : ℕ → PowerSeries F) (b : ℕ) : W E b [] = 1 := by
  simp [W, PowerSeries.coeff_one]

/-- The contribution of the product gates. -/
noncomputable def Wi (E : ℕ → PowerSeries F) (n : ℕ) (κ : ℕ → ℕ → F) (gs : List ℕ) : ℕ → F
  | 0 => 0
  | b + 1 => ∑ l ∈ range n, ∑ r ∈ range n, κ l r * W E b (l :: r :: gs)

theorem W_cons {E : ℕ → PowerSeries F} {g : ℕ} {a : F} {n : ℕ} {κ : ℕ → ℕ → F}
    (h : E g = PowerSeries.C a + PowerSeries.X * ∑ l ∈ range n, ∑ r ∈ range n, PowerSeries.C (κ l r) * (E l * E r))
    (b : ℕ) (gs : List ℕ) : W E b (g :: gs) = a * W E b gs + Wi E n κ gs b := by
  have h1 : (List.map E (g :: gs)).prod = PowerSeries.C a * (gs.map E).prod + PowerSeries.X *
      ∑ l ∈ range n, ∑ r ∈ range n, PowerSeries.C (κ l r) * (List.map E (l :: r :: gs)).prod := by
    rw [List.map_cons, List.prod_cons, h, add_mul, mul_assoc, Finset.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [List.map_cons, List.prod_cons]
    ring
  unfold W
  simp only [h1, map_add, PowerSeries.coeff_C_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_range_succ']
  simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul, add_zero]
  cases b with
  | zero => simp [Wi]
  | succ b =>
    simp only [map_sum, PowerSeries.coeff_C_mul, Wi, W]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]

/-- The parts of degree at most `N`. -/
theorem sum_coeff_line (u : σ → F) (P : ℕ → MvPolynomial σ F) (out N : ℕ) (hN : 0 < N) :
    ∑ i ∈ range (N + 1), (line u (P out)).coeff i =
      MvPolynomial.constantCoeff (P out) + W (fun g => ser u (P g)) (N - 1) [out] := by
  rw [Finset.sum_range_succ', line_coeff_zero, add_comm, W, Nat.sub_add_cancel hN]
  simp [ser]

/-- All parts of a polynomial. -/
theorem sum_coeff_eq_eval (u : σ → F) (p : MvPolynomial σ F) {d n : ℕ} (hd : p.totalDegree ≤ d) (hn : d < n) :
    ∑ i ∈ range n, (line u p).coeff i = MvPolynomial.eval u p := by
  have hdeg : (line u p).natDegree ≤ d := by
    have := MvPolynomial.aeval_natDegree_le p hd
      (fun i => Polynomial.C (u i) * Polynomial.X) (n := 1)
      (fun i => (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
    simpa [line] using this
  rw [← eval_one_line, Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hdeg hn)]
  simp

end Nc.Acc

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The program that guesses a parse tree

The argument of the loop is (the loop, (budget, (stack of gates, tree of pairs of letters))).
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- Concatenation of lists of bits. -/
theorem appBits_gives {a b : Fm} {x : Tree} {ca cb : ℕ} {v w : List Bool} (ha : Gives θ a x (ofBits v) ca)
    (hb : Gives θ b x (ofBits w) cb) : Gives θ (appF a b) x (ofBits (v ++ w)) (ca + cb + v.length * 62 + 41) := by
  rw [← listT_ofBits] at ha hb ⊢
  have := appF_gives ha hb
  rw [← List.map_append, List.length_map] at this
  exact this

/-- Guess a word. -/
def gwd : ℕ → Fm
  | 0 => .quote .nil
  | M + 1 => .cons (.ite .guess (.quote one) (.quote .nil)) (gwd M)

theorem gwd_does (M : ℕ) (x : Tree) : Does θ (gwd M) x ((wd M).map fun w => (1, ofBits w)) (6 * M + 1) := by
  induction M with
  | zero => exact (Gives.quote .nil x).mono (by norm_num)
  | succ M ih =>
    have h := ((Gives.quote (θ := θ) one x).either (Gives.quote .nil x)).cons ih
    have e : (([(1, one)] ++ [(1, Tree.nil)] : List (A × Tree)).flatMap fun q =>
        ((wd M).map fun w => ((1 : A), ofBits w)).map fun r => (q.1 * r.1, Tree.cons q.2 r.2)) =
        (wd (M + 1)).map fun w => (1, ofBits w) := by
      simp [wd, Function.comp_def, ofBits, bit]
    rw [e] at h
    exact h.mono (by omega)

/-- A step of the walk. The argument is (tree, path so far, reversed). -/
def stepW : Fm := .ite .guess (.cons (.tl (.hd .id)) (.cons (.quote one) (.tl .id)))
  (.cons (.hd (.hd .id)) (.cons (.quote .nil) (.tl .id)))

/-- Guess a path in a tree. -/
def walkF : ℕ → Fm
  | 0 => .id
  | m + 1 => lett stepW (walkF m)

theorem walkF_does (m : ℕ) (T : Tree) (acc : List Bool) : Does θ (walkF m) (.cons T (ofBits acc))
    ((wd m).map fun p => (1, .cons (look p T) (ofBits (p.reverse ++ acc)))) (12 * m + 1) := by
  induction m generalizing T acc with
  | zero => exact (Gives.id _).mono (by norm_num)
  | succ m ih =>
    have h0 := (Gives.cons (Gives.id (θ := θ) (.cons T (ofBits acc))).hd.tl
      (Gives.cons (Gives.quote one _) (Gives.id _).tl)).either
      (Gives.cons (Gives.id (θ := θ) (.cons T (ofBits acc))).hd.hd (Gives.cons (Gives.quote .nil _) (Gives.id _).tl))
    have h := h0.lett (G := walkF m) (R := fun o => (wd m).map fun p => (1, .cons (look p o.hd)
      (ofBits (p.reverse ++ o.tl.path)))) (d := 12 * m + 1) (by
        intro q hq
        simp only [hd_cons, tl_cons, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · have := ih T.tl (true :: acc)
          have e : (Tree.cons one (ofBits acc)).path = true :: acc := by
            have : ofBits (true :: acc) = Tree.cons one (ofBits acc) := rfl
            rw [← this, path_ofBits]
          simp only [hd_cons, tl_cons, e]
          exact this
        · have := ih T.hd (false :: acc)
          have e : (Tree.cons Tree.nil (ofBits acc)).path = false :: acc := by
            have : ofBits (false :: acc) = Tree.cons .nil (ofBits acc) := rfl
            rw [← this, path_ofBits]
          simp only [hd_cons, tl_cons, e]
          exact this)
    have e1 : (Tree.cons one (ofBits acc)).path = true :: acc := by
      have : ofBits (true :: acc) = Tree.cons one (ofBits acc) := rfl
      rw [← this, path_ofBits]
    have e2 : (Tree.cons Tree.nil (ofBits acc)).path = false :: acc := by
      have : ofBits (false :: acc) = Tree.cons .nil (ofBits acc) := rfl
      rw [← this, path_ofBits]
    simp only [bindW, hd_cons, tl_cons, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_map, Function.comp_def, one_mul, e1, e2] at h
    have e : ((wd (m + 1)).map fun p => ((1 : A), Tree.cons (look p T) (ofBits (p.reverse ++ acc)))) =
        ((wd m).map fun p => ((1 : A), Tree.cons (look p T.tl) (ofBits (p.reverse ++ true :: acc)))) ++
        (wd m).map fun p => ((1 : A), Tree.cons (look p T.hd) (ofBits (p.reverse ++ false :: acc))) := by
      simp [wd, Function.comp_def, look]
    rw [e]
    exact h.mono (by omega)

/-- The code of a letter. -/
def lc (t : Tree) : List Bool := if t = .nil then [false, false] else t.path

/-- The gate on top of the stack; the argument is (argument of the loop, anything). -/
def topF : Fm := .hd (.hd (.tl (.tl (.hd .id))))

/-- The name of the weight of an input. -/
def nameL : Fm := .cons (.quote .nil) (.cons (.quote one) (appF topF (appF (.tl (.tl .id))
  (appF (.ite (.hd (.tl .id)) (.hd (.tl .id)) (.quote (ofBits [false, false]))) (.quote (ofBits [false]))))))

/-- The name of the weight of a product gate. -/
def nameK : Fm := .cons (.quote .nil) (.cons (.quote .nil) (appF topF (appF (.hd (.tl .id))
  (appF (.tl (.tl .id)) (.quote (ofBits [false]))))))

/-- An input is read. -/
def leafB : Fm := .cons (.mul nameL) (.run (.hd (.hd .id)) (.cons (.hd (.hd .id)) (.cons (.hd (.tl (.hd .id)))
  (.cons (.tl (.hd (.tl (.tl (.hd .id))))) (.tl (.tl (.tl (.hd .id))))))))

/-- A product gate. -/
def intB : Fm := .cons (.mul nameK) (.run (.hd (.hd .id)) (.cons (.hd (.hd .id)) (.cons (.tl (.hd (.tl (.hd .id))))
  (.cons (.cons (.hd (.tl .id)) (.cons (.tl (.tl .id)) (.tl (.hd (.tl (.tl (.hd .id)))))))
    (.tl (.tl (.tl (.hd .id))))))))

/-- Guess an input. -/
def leafF (m : ℕ) : Fm := lett (.cons .id (lett (.cons (.tl (.tl (.tl .id))) (.quote .nil)) (walkF m))) leafB

/-- Guess a product gate. -/
def intF (M : ℕ) : Fm := .ite (.hd (.tl .id)) (lett (.cons .id (.cons (gwd M) (gwd M))) intB) .fail

/-- The loop. -/
def loopF (M m : ℕ) : Fm := .ite (.hd (.tl (.tl .id))) (.ite .guess (leafF m) (intF M)) (.quote .nil)

theorem nameL_gives {self T t : Tree} {b : Tree} {g acc : List Bool} {ws : List (List Bool)}
    (ht : t = .nil ∨ ∃ c : List Bool, c.length = 2 ∧ t = ofBits c) :
    Gives θ nameL (.cons (.cons self (.cons b (.cons (listT ((g :: ws).map ofBits)) T))) (.cons t (ofBits acc)))
      (ofBits ([false, true] ++ g ++ acc ++ lc t ++ [false])) (62 * (g.length + acc.length) + 500) := by
  set y := Tree.cons (.cons self (.cons b (.cons (listT ((g :: ws).map ofBits)) T))) (.cons t (ofBits acc)) with hy
  have hg : Gives θ topF y (ofBits g) 6 := (Gives.id y).hd.tl.tl.hd.hd
  have hacc : Gives θ (.tl (.tl .id)) y (ofBits acc) 3 := (Gives.id y).tl.tl
  have hc : Gives θ (.ite (.hd (.tl .id)) (.hd (.tl .id)) (.quote (ofBits [false, false]))) y (ofBits (lc t)) 8 := by
    have h1 : Gives θ (.hd (.tl .id)) y t 3 := (Gives.id y).tl.hd
    rcases ht with rfl | ⟨c, hc2, rfl⟩
    · exact (h1.ite_false (Gives.quote _ _)).mono (by norm_num)
    · have hne : ofBits c ≠ .nil := by
        cases c with
        | nil => simp at hc2
        | cons a c => simp [ofBits]
      have e : lc (ofBits c) = c := by rw [lc, if_neg hne, path_ofBits]
      rw [e]
      exact (h1.ite_true hne h1).mono (by norm_num)
  have hlc : (lc t).length ≤ 2 := by
    rcases ht with rfl | ⟨c, hc2, rfl⟩
    · simp [lc]
    · unfold lc
      split_ifs
      · simp
      · rw [path_ofBits, hc2]
  have h := Gives.cons (Gives.quote (θ := θ) .nil y) (Gives.cons (Gives.quote one y) (appBits_gives hg (appBits_gives hacc
    (appBits_gives hc (Gives.quote (ofBits [false]) y)))))
  have e : ofBits ([false, true] ++ g ++ acc ++ lc t ++ [false]) =
      Tree.cons .nil (.cons one (ofBits (g ++ (acc ++ (lc t ++ [false]))))) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl
  rw [e]
  exact h.mono (by omega)

theorem nameK_gives {self T : Tree} {b : Tree} {g l r : List Bool} {ws : List (List Bool)} :
    Gives θ nameK (.cons (.cons self (.cons b (.cons (listT ((g :: ws).map ofBits)) T))) (.cons (ofBits l) (ofBits r)))
      (ofBits ([false, false] ++ g ++ l ++ r ++ [false])) (62 * (g.length + l.length + r.length) + 500) := by
  set y := Tree.cons (.cons self (.cons b (.cons (listT ((g :: ws).map ofBits)) T))) (.cons (ofBits l) (ofBits r)) with hy
  have hg : Gives θ topF y (ofBits g) 6 := (Gives.id y).hd.tl.tl.hd.hd
  have hl : Gives θ (.hd (.tl .id)) y (ofBits l) 3 := (Gives.id y).tl.hd
  have hr : Gives θ (.tl (.tl .id)) y (ofBits r) 3 := (Gives.id y).tl.tl
  have h := Gives.cons (Gives.quote (θ := θ) .nil y) (Gives.cons (Gives.quote .nil y) (appBits_gives hg (appBits_gives hl
    (appBits_gives hr (Gives.quote (ofBits [false]) y)))))
  have e : ofBits ([false, false] ++ g ++ l ++ r ++ [false]) =
      Tree.cons .nil (.cons .nil (ofBits (g ++ (l ++ (r ++ [false]))))) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl
  rw [e]
  exact h.mono (by omega)

open Nc.Acc in
/-- **The loop computes the sum over the parse trees.** -/
theorem loopF_kv {M m : ℕ} {T : Tree} {κ : List Bool → R} {S : Set (List Bool)} {E : ℕ → PowerSeries R} {a : ℕ → R}
    {k : ℕ → ℕ → ℕ → R}
    (hE : ∀ g, E g = PowerSeries.C (a g) + PowerSeries.X * ∑ l ∈ Finset.range (2 ^ M), ∑ r ∈ Finset.range (2 ^ M),
      PowerSeries.C (k g l r) * (E l * E r))
    (hk : ∀ g l r : List Bool, g.length = M → l.length = M → r.length = M →
      κ ([false, false] ++ g ++ l ++ r ++ [false]) = k (KT.val g) (KT.val l) (KT.val r) ∧
      [false, false] ++ g ++ l ++ r ++ [false] ∈ S)
    (ha : ∀ g : List Bool, g.length = M →
      ((wd m).map fun p => κ ([false, true] ++ g ++ p.reverse ++ lc (look p T) ++ [false])).sum = a (KT.val g))
    (hS : ∀ g p c : List Bool, g.length = M → p.length = m → c.length = 2 → [false, true] ++ g ++ p ++ c ++ [false] ∈ S)
    (hT : ∀ p : List Bool, p.length = m → look p T = .nil ∨ ∃ c : List Bool, c.length = 2 ∧ look p T = ofBits c)
    (n b : ℕ) (ws : List (List Bool)) (hn : 2 * b + ws.length ≤ n) (hws : ∀ w ∈ ws, w.length = M) :
    KV θ κ S (loopF M m) (.cons (loopF M m).code (.cons (num b) (.cons (listT (ws.map ofBits)) T)))
      (W E b (ws.map KT.val)) ((n + 1) * (400 * (M + m) + 2000)) := by
  induction n generalizing b ws with
  | zero =>
    have hws0 : ws = [] := List.length_eq_zero_iff.1 (by omega)
    subst hws0
    refine (KV.ite_false (Gives.id _).tl.tl.hd (KV.of_gives (Gives.quote .nil _))).mono ?_ |>.congr (W_nil E b).symm
    omega
  | succ n ih =>
    cases ws with
    | nil =>
      refine (KV.ite_false (Gives.id _).tl.tl.hd (KV.of_gives (Gives.quote .nil _))).mono ?_ |>.congr (W_nil E b).symm
      nlinarith
    | cons g ws =>
      have hg : g.length = M := hws g List.mem_cons_self
      have hws' : ∀ w ∈ ws, w.length = M := fun w hw => hws w (List.mem_cons_of_mem _ hw)
      set x := Tree.cons (loopF M m).code (.cons (num b) (.cons (listT ((g :: ws).map ofBits)) T)) with hx
      rw [List.length_cons] at hn
      have hlc : ∀ p : List Bool, p.length = m → (lc (look p T)).length = 2 := by
        intro p hp
        rcases hT p hp with h | ⟨c, hc, h⟩
        · rw [h]
          rfl
        · rw [h, lc]
          split_ifs with h2
          · rfl
          · rw [path_ofBits, hc]
      -- an input
      have h1 : KV θ κ S (leafF m) x (a (KT.val g) * W E b (ws.map KT.val))
          ((n + 1) * (400 * (M + m) + 2000) + 100 * (M + m) + 800) := by
        have hq := Does.cons (Gives.id (θ := θ) x) (Does.of_gives (Gives.cons (Gives.id (θ := θ) x).tl.tl.tl
          (Gives.quote (ofBits []) x)) (walkF_does m T []))
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, Function.comp_def, one_mul] at hq
        have h := KV.lett (κ := κ) (S := S) (G := leafB) (ω := fun o => κ ([false, true] ++ g ++ o.tl.tl.path ++ lc o.tl.hd
          ++ [false]) * W E b (ws.map KT.val)) hq (d := (n + 1) * (400 * (M + m) + 2000) + 62 * (M + m) + 600) (by
            intro q hq
            rw [List.mem_map] at hq
            obtain ⟨p, hp, rfl⟩ := hq
            have hpm := length_of_mem_wd hp
            simp only [tl_cons, hd_cons, path_ofBits]
            have m1 := KV.mul (κ := κ) (S := S) (nameL_gives (θ := θ) (self := (loopF M m).code) (b := num b) (T := T)
              (g := g) (ws := ws) (acc := p.reverse) (hT p hpm)) (by
                rw [path_ofBits]
                exact hS g p.reverse _ hg (by simpa using hpm) (hlc p hpm))
            rw [path_ofBits] at m1
            have r1 := KV.run (κ := κ) (S := S) (p := (loopF M m).code)
              (Gives.id (θ := θ) (.cons x (.cons (look p T) (ofBits p.reverse)))).hd.hd
              (Gives.cons (Gives.id _).hd.hd (Gives.cons (Gives.id _).hd.tl.hd (Gives.cons (Gives.id _).hd.tl.tl.hd.tl
                (Gives.id _).hd.tl.tl.tl))) (by
                rw [Fm.ofTree_code]
                exact ih b ws (by omega) hws')
            refine (KV.cons m1 r1).mono ?_
            simp only [List.length_reverse]
            omega)
        refine (h.mono (by omega)).congr ?_
        rw [List.map_map]
        simp only [Function.comp_def, map_one, one_mul, tl_cons, hd_cons, path_ofBits]
        rw [List.sum_map_mul_right, ha g hg]
      -- a product gate
      have h2 : KV θ κ S (intF M) x (Wi E (2 ^ M) (k (KT.val g)) (ws.map KT.val) b) ((n + 1) * (400 * (M + m) + 2000) + 300 * (M + m) + 900) := by
        cases b with
        | zero =>
          refine (KV.ite_false (Gives.id _).tl.hd (KV.fail x)).mono ?_
          omega
        | succ b =>
          have hq := Does.cons (Gives.id (θ := θ) x) (Does.cons (gwd_does (θ := θ) M x) (gwd_does M x))
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, Function.comp_def, one_mul,
            List.flatMap_map, List.map_flatMap] at hq
          have h := KV.lett (κ := κ) (S := S) (G := intB) (ω := fun o => κ ([false, false] ++ g ++ o.tl.hd.path ++ o.tl.tl.path
            ++ [false]) * W E b (KT.val o.tl.hd.path :: KT.val o.tl.tl.path :: ws.map KT.val)) hq
            (d := (n + 1) * (400 * (M + m) + 2000) + 62 * (3 * M) + 600) (by
              intro q hq
              rw [List.mem_flatMap] at hq
              obtain ⟨l, hl, hq⟩ := hq
              rw [List.mem_map] at hq
              obtain ⟨r, hr, rfl⟩ := hq
              have hlm := length_of_mem_wd hl
              have hrm := length_of_mem_wd hr
              simp only [tl_cons, hd_cons, path_ofBits]
              have m1 := KV.mul (κ := κ) (S := S) (nameK_gives (θ := θ) (self := (loopF M m).code) (b := num (b + 1)) (T := T)
                (g := g) (ws := ws) (l := l) (r := r)) (by
                  rw [path_ofBits]
                  exact (hk g l r hg hlm hrm).2)
              rw [path_ofBits] at m1
              have r1 := KV.run (κ := κ) (S := S) (p := (loopF M m).code)
                (Gives.id (θ := θ) (.cons x (.cons (ofBits l) (ofBits r)))).hd.hd
                (Gives.cons (Gives.id _).hd.hd (Gives.cons (Gives.id _).hd.tl.hd.tl (Gives.cons
                  (Gives.cons (Gives.id _).tl.hd (Gives.cons (Gives.id _).tl.tl (Gives.id _).hd.tl.tl.hd.tl))
                  (Gives.id _).hd.tl.tl.tl))) (by
                  rw [Fm.ofTree_code]
                  exact ih b (l :: r :: ws) (by simp only [List.length_cons]; omega) (by
                    intro w hw
                    simp only [List.mem_cons] at hw
                    rcases hw with rfl | rfl | hw
                    · exact hlm
                    · exact hrm
                    · exact hws' w hw))
              refine (KV.cons m1 r1).mono ?_
              omega)
          refine ((KV.ite_true (H := .fail) (Gives.id _).tl.hd (by rw [hx]; simp [num]) h).mono ?_).congr ?_
          · omega
          · rw [sum_flatMap_map, Wi]
            simp only [List.map_map, Function.comp_def, map_one, one_mul, tl_cons, hd_cons, path_ofBits]
            rw [← sum_wd M fun l => ∑ r ∈ Finset.range (2 ^ M), k (KT.val g) l r * W E b (l :: r :: ws.map KT.val)]
            congr 1
            refine List.map_congr_left fun l hl => ?_
            rw [← sum_wd M fun r => k (KT.val g) (KT.val l) r * W E b (KT.val l :: r :: ws.map KT.val)]
            congr 1
            refine List.map_congr_left fun r hr => ?_
            rw [(hk g l r hg (length_of_mem_wd hl) (length_of_mem_wd hr)).1]
      have h3 := KV.ite_true (H := .quote .nil) (Gives.id (θ := θ) x).tl.tl.hd (by rw [hx]; simp [listT]) (KV.either h1 h2)
      refine (h3.mono ?_).congr ?_
      · have e : (n + 1 + 1) * (400 * (M + m) + 2000) = (n + 1) * (400 * (M + m) + 2000) + (400 * (M + m) + 2000) := by ring
        rw [e]
        omega
      · rw [List.map_cons, W_cons (hE (KT.val g))]

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The program of an accelerator
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- Pair the neighbours of a list. The argument is (this program, list). -/
def pairB : Fm := .ite (.tl .id) (.cons (.cons (.hd (.tl .id)) (.hd (.tl (.tl .id))))
  (.run (.hd .id) (.cons (.hd .id) (.tl (.tl (.tl .id)))))) (.quote .nil)

theorem pairB_gives (l : List Tree) :
    Gives θ pairB (.cons pairB.code (listT l)) (listT (pairL l)) (40 * (l.length + 1)) := by
  induction l using pairL.induct with
  | case1 => exact ((Gives.id _).tl.ite_false (Gives.quote .nil _)).mono (by norm_num)
  | case2 a =>
    have h0 : Gives θ (Fm.ofTree pairB.code) (.cons pairB.code (listT [])) (listT (pairL [])) 40 := by
      rw [Fm.ofTree_code]
      exact ((Gives.id _).tl.ite_false (Gives.quote .nil _)).mono (by norm_num)
    have h := (Gives.id (θ := θ) (.cons pairB.code (listT [a]))).tl.ite_true (H := .quote .nil) (by simp [listT])
      (Gives.cons (Gives.cons (Gives.id _).tl.hd (Gives.id _).tl.tl.hd)
        (Gives.run (Gives.id _).hd (Gives.cons (Gives.id _).hd (Gives.id _).tl.tl.tl) h0))
    exact h.mono (by simp)
  | case3 a b l ih =>
    have h0 : Gives θ (Fm.ofTree pairB.code) (.cons pairB.code (listT l)) (listT (pairL l)) (40 * (l.length + 1)) := by
      rw [Fm.ofTree_code]
      exact ih
    have h := (Gives.id (θ := θ) (.cons pairB.code (listT (a :: b :: l)))).tl.ite_true (H := .quote .nil)
      (by simp [listT]) (Gives.cons (Gives.cons (Gives.id _).tl.hd (Gives.id _).tl.tl.hd)
        (Gives.run (Gives.id _).hd (Gives.cons (Gives.id _).hd (Gives.id _).tl.tl.tl) h0))
    refine h.mono ?_
    simp only [List.length_cons]
    omega

/-- Pair the neighbours several times. -/
def pairsF : ℕ → Fm → Fm
  | 0, l => l
  | m + 1, l => pairsF m (app pairB.code (.cons (.quote pairB.code) l))

theorem length_pairL_le (l : List Tree) : (pairL l).length ≤ l.length := by
  rw [length_pairL]
  omega

theorem pairsF_gives (m : ℕ) {l : Fm} {x : Tree} {xs : List Tree} {c : ℕ} (hl : Gives θ l x (listT xs) c) :
    Gives θ (pairsF m l) x (listT (pairL^[m] xs)) (c + m * (40 * (xs.length + 1) + 10)) := by
  induction m generalizing l xs c with
  | zero => simpa [pairsF] using hl
  | succ m ih =>
    have h := Gives.app (p := pairB.code) (Gives.cons (Gives.quote pairB.code x) hl) (by
      rw [Fm.ofTree_code]
      exact pairB_gives xs)
    have h2 := ih h
    rw [Function.iterate_succ_apply]
    refine h2.mono ?_
    have h3 : m * (40 * ((pairL xs).length + 1) + 10) ≤ m * (40 * (xs.length + 1) + 10) := by
      apply Nat.mul_le_mul_left
      have := length_pairL_le xs
      omega
    have h4 : (m + 1) * (40 * (xs.length + 1) + 10) = m * (40 * (xs.length + 1) + 10) + (40 * (xs.length + 1) + 10) := by
      ring
    omega

/-- The letter of the empty tree. -/
def lt0 : Tree := ofBits [true, false]

/-- The letter of a node. -/
def lt1 : Tree := ofBits [true, true]

/-- The letter at the end. -/
def lt2 : Tree := ofBits [false, true]

/-- The tree of pairs of the letters of the word of the argument. -/
def treeF (m : ℕ) : Fm := .hd (pairsF m (app (wordB lt0 lt1).code
  (.cons (.quote (wordB lt0 lt1).code) (.cons .id (.quote (listT [lt2]))))))

/-- The program. -/
def accF (M m d : ℕ) (out : List Bool) : Fm := .ite .guess (.mul (.quote (ofBits [true, false])))
  (app (loopF M m).code (.cons (.quote (loopF M m).code) (.cons (.quote (num (d - 1)))
    (.cons (.quote (listT ([out].map ofBits))) (treeF m)))))

/-- The tree of pairs. -/
def pairTree (m : ℕ) (z : Tree) : Tree := (listT (pairL^[m] (wordT lt0 lt1 z ++ [lt2]))).hd

theorem treeF_gives (m : ℕ) (z : Tree) :
    Gives θ (treeF m) z (pairTree m z) (60 * z.size + m * (40 * (z.size + 2) + 10) + 12) := by
  have h0 := Gives.app (p := (wordB lt0 lt1).code) (Gives.cons (Gives.quote (θ := θ) (wordB lt0 lt1).code z)
    (Gives.cons (Gives.id z) (Gives.quote (listT [lt2]) z))) (by
      rw [Fm.ofTree_code]
      exact wordB_gives lt0 lt1 z [lt2])
  have h := (pairsF_gives m h0).hd
  rw [List.length_append, length_wordT, List.length_singleton] at h
  have e : m * (40 * (z.size + 1 + 1) + 10) = m * (40 * (z.size + 2) + 10) := rfl
  refine h.mono ?_
  rw [e]
  omega

theorem length_tbits (z : Tree) : (tbits z).length = z.size := by
  induction z with
  | nil => rfl
  | cons a b iha ihb =>
    simp only [tbits, List.length_cons, List.length_append, iha, ihb, Tree.size]

/-- The letter as a tree. -/
def ltr : Option Bool → Tree
  | some false => lt0
  | some true => lt1
  | none => lt2

theorem wordT_eq (z : Tree) : wordT lt0 lt1 z ++ [lt2] = ((tbits z).map some ++ [none]).map ltr := by
  have h : wordT lt0 lt1 z = ((tbits z).map some).map ltr := by
    induction z with
    | nil => rfl
    | cons a b iha ihb => simp only [wordT, tbits, List.map_cons, List.map_append, iha, ihb]; rfl
  rw [h, List.map_append]
  rfl

/-- The letter at a place of the tree of pairs. -/
theorem look_pairTree {m : ℕ} {z : Tree} (hz : z.size < 2 ^ m) {p : List Bool} (hp : p.length = m) :
    look p (pairTree m z) = ((((tbits z).map some ++ [none])[KT.val p.reverse]?).map ltr).getD .nil := by
  rw [pairTree, look_pairs m _ (by rw [List.length_append, length_wordT]; exact hz) p hp, wordT_eq,
    List.getD_eq_getElem?_getD, List.getElem?_map]

/-- The letter with a given code. -/
def decL (c : List Bool) : Option (Option Bool) :=
  if c = [true, false] then some (some false) else if c = [true, true] then some (some true)
  else if c = [false, true] then some none else none

theorem decL_lc (o : Option (Option Bool)) : decL (lc ((o.map ltr).getD .nil)) = o := by
  rcases o with _ | _ | _ | _ <;> rfl

theorem length_lc (o : Option (Option Bool)) : (lc ((o.map ltr).getD .nil)).length = 2 := by
  rcases o with _ | _ | _ | _ <;> rfl

theorem ltr_cases (o : Option (Option Bool)) :
    (o.map ltr).getD .nil = .nil ∨ ∃ w : List Bool, w.length = 2 ∧ (o.map ltr).getD .nil = ofBits w := by
  rcases o with _ | _ | _ | _
  · exact Or.inl rfl
  · exact Or.inr ⟨[false, true], rfl, rfl⟩
  · exact Or.inr ⟨[true, false], rfl, rfl⟩
  · exact Or.inr ⟨[true, true], rfl, rfl⟩

/-- The weight of a letter at a place. -/
def lamK {N : ℕ} (lam : Fin N × Option Bool → R) (i : ℕ) (o : Option (Option Bool)) : R :=
  match o with
  | none => 0
  | some γ => if h : i < N then lam (⟨i, h⟩, γ) else 0

theorem lamK_ge {N : ℕ} (lam : Fin N × Option Bool → R) {i : ℕ} (h : ¬ i < N) (o : Option (Option Bool)) :
    lamK lam i o = 0 := by
  cases o with
  | none => rfl
  | some γ => exact dif_neg h

/-- The constants of an accelerator. -/
def accK (M m N : ℕ) (γ : R) (k : ℕ → ℕ → ℕ → R) (lam : ℕ → Fin N × Option Bool → R) : KT R :=
  .node (.node (KT.full (M + M + M) fun w => k (KT.val (w.take M)) (KT.val ((w.drop M).take M)) (KT.val (w.drop (M + M))))
    (KT.full (M + m + 2) fun w => lamK (lam (KT.val (w.take M))) (KT.val ((w.drop M).take m)) (decL (w.drop (M + m)))))
    (.leaf γ)

section names

variable {M m N : ℕ} {γ : R} {k : ℕ → ℕ → ℕ → R} {lam : ℕ → Fin N × Option Bool → R}

theorem accK_k {g l r : List Bool} (hg : g.length = M) (hl : l.length = M) (hr : r.length = M) :
    (accK M m N γ k lam).lk ([false, false] ++ g ++ l ++ r ++ [false]) = k (KT.val g) (KT.val l) (KT.val r) ∧
    (accK M m N γ k lam).InB 1 ([false, false] ++ g ++ l ++ r ++ [false]) := by
  have e : [false, false] ++ g ++ l ++ r ++ [false] = false :: false :: ((g ++ l ++ r) ++ [false]) := by simp
  have h : (g ++ l ++ r).length = M + M + M := by
    simp only [List.length_append, hg, hl, hr]
  rw [e]
  refine ⟨?_, KT.inB_full _ h⟩
  have h1 := KT.lk_full (fun w => k (KT.val (w.take M)) (KT.val ((w.drop M).take M)) (KT.val (w.drop (M + M)))) h
  refine h1.trans ?_
  have e1 : (g ++ l ++ r).take M = g := by rw [List.append_assoc, List.take_left' hg]
  have e2 : ((g ++ l ++ r).drop M).take M = l := by
    rw [List.append_assoc, List.drop_left' hg, List.take_left' hl]
  have e3 : (g ++ l ++ r).drop (M + M) = r := List.drop_left' (by simp [hg, hl])
  simp only [e1, e2, e3]

theorem accK_l {g p c : List Bool} (hg : g.length = M) (hp : p.length = m) (hc : c.length = 2) :
    (accK M m N γ k lam).lk ([false, true] ++ g ++ p ++ c ++ [false]) =
      lamK (lam (KT.val g)) (KT.val p) (decL c) ∧
    (accK M m N γ k lam).InB 1 ([false, true] ++ g ++ p ++ c ++ [false]) := by
  have e : [false, true] ++ g ++ p ++ c ++ [false] = false :: true :: ((g ++ p ++ c) ++ [false]) := by simp
  have h : (g ++ p ++ c).length = M + m + 2 := by
    simp only [List.length_append, hg, hp, hc]
  rw [e]
  refine ⟨?_, KT.inB_full _ h⟩
  have h1 := KT.lk_full (fun w => lamK (lam (KT.val (w.take M))) (KT.val ((w.drop M).take m)) (decL (w.drop (M + m)))) h
  refine h1.trans ?_
  have e1 : (g ++ p ++ c).take M = g := by rw [List.append_assoc, List.take_left' hg]
  have e2 : ((g ++ p ++ c).drop M).take m = p := by
    rw [List.append_assoc, List.drop_left' hg, List.take_left' hp]
  have e3 : (g ++ p ++ c).drop (M + m) = c := List.drop_left' (by simp [hg, hp])
  simp only [e1, e2, e3]

theorem accK_c : (accK M m N γ k lam).lk [true, false] = γ ∧ (accK M m N γ k lam).InB 1 [true, false] :=
  ⟨rfl, ⟨0, zero_lt_one, rfl⟩⟩

theorem nds_accK : (accK M m N γ k lam).nds ≤ 2 ^ (3 * M + 1) + 2 ^ (M + m + 3) + 3 := by
  have h1 := KT.nds_full (M + M + M) fun w => k (KT.val (w.take M)) (KT.val ((w.drop M).take M)) (KT.val (w.drop (M + M)))
  have h2 := KT.nds_full (M + m + 2) fun w =>
    lamK (lam (KT.val (w.take M))) (KT.val ((w.drop M).take m)) (decL (w.drop (M + m)))
  have e : M + M + M + 1 = 3 * M + 1 := by ring
  have e2 : M + m + 2 + 1 = M + m + 3 := by ring
  rw [e] at h1
  rw [e2] at h2
  rw [accK, KT.nds, KT.nds, KT.nds]
  omega

theorem ht_accK : (accK M m N γ k lam).ht ≤ 3 * M + m + 4 := by
  rw [accK, KT.ht, KT.ht, KT.ht, KT.ht_full, KT.ht_full]
  omega

end names

open Nc.Acc in
/-- **The program computes the part of degree at most `d` of a polynomial with a small circuit.** -/
theorem accF_kv {M m N d s : ℕ} {p : MvPolynomial (Fin N × Option Bool) R} (hp : Nc.Computes p s) (hs : s ≤ 2 ^ M)
    (hd : 0 < d) (hNm : N ≤ 2 ^ m) : ∃ (K : KT R) (out : List Bool), out.length = M ∧
      K.nds ≤ 2 ^ (3 * M + 1) + 2 ^ (M + m + 3) + 3 ∧ K.ht ≤ 3 * M + m + 4 ∧
      ∀ (A : Type) [CommRing A] [Algebra A R] (θ : List Bool → A) (z : Tree), z.size < N →
        KV θ K.lk {q | K.InB 1 q} (accF M m d out) z
          (∑ i ∈ Finset.range (d + 1), (line (codeB R N (tbits z)) p).coeff i)
          (d * (800 * (M + m) + 4000) + (z.size + 2) * (40 * m + 60) + 10 * m + 100) := by
  obtain ⟨k, lam, P, o, ho, rfl, hE⟩ := exists_series hp hs
  obtain ⟨out, hout, hval⟩ := exists_word ho
  set K := accK M m N (MvPolynomial.constantCoeff (P o)) k lam with hK
  refine ⟨K, out, hout, nds_accK, ht_accK, fun A _ _ θ z hz => ?_⟩
  have hzm : z.size < 2 ^ m := hz.trans_le hNm
  have hT : ∀ p : List Bool, p.length = m → look p (pairTree m z) = .nil ∨
      ∃ c : List Bool, c.length = 2 ∧ look p (pairTree m z) = ofBits c := by
    intro p hp
    rw [look_pairTree hzm hp]
    exact ltr_cases _
  have ha : ∀ g : List Bool, g.length = M →
      ((wd m).map fun p => K.lk ([false, true] ++ g ++ p.reverse ++ lc (look p (pairTree m z)) ++ [false])).sum =
        ∑ i, lam (KT.val g) i * codeB R N (tbits z) i := by
    intro g hg
    have h1 : ∀ p ∈ wd m, K.lk ([false, true] ++ g ++ p.reverse ++ lc (look p (pairTree m z)) ++ [false]) =
        (fun w => lamK (lam (KT.val g)) (KT.val w) (((tbits z).map some ++ [none])[KT.val w]?)) p.reverse := by
      intro p hp
      have hpm := length_of_mem_wd hp
      rw [look_pairTree hzm hpm, hK, (accK_l hg (by simpa using hpm) (length_lc _)).1, decL_lc]
    rw [List.map_congr_left h1]
    refine (sum_wd_reverse m fun w => lamK (lam (KT.val g)) (KT.val w)
      (((tbits z).map some ++ [none])[KT.val w]?)).trans ?_
    refine (sum_wd m fun i => lamK (lam (KT.val g)) i (((tbits z).map some ++ [none])[i]?)).trans ?_
    rw [← Finset.sum_subset (Finset.range_mono hNm), Finset.sum_range, Fintype.sum_prod_type]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rcases Option.eq_none_or_eq_some (((tbits z).map some ++ [none])[(i : ℕ)]?) with hc | ⟨γ, hc⟩
      · simp [codeB, hc, lamK]
      · rw [Finset.sum_eq_single γ]
        · simp [codeB, hc, lamK, i.2]
        · intro c _ hne
          simp only [codeB, hc, Option.some.injEq]
          rw [if_neg hne.symm, mul_zero]
        · simp
    · intro i _ hi
      exact lamK_ge _ (by simpa using hi) _
  have hloop := loopF_kv (θ := θ) (M := M) (m := m) (T := pairTree m z) (κ := K.lk) (S := {q | K.InB 1 q})
    (E := fun g => ser (codeB R N (tbits z)) (P g)) (a := fun g => ∑ i, lam g i * codeB R N (tbits z) i) (k := k)
    (hE (codeB R N (tbits z)))
    (fun g l r hg hl hr => accK_k hg hl hr) ha
    (fun g p c hg hp hc => (accK_l (γ := MvPolynomial.constantCoeff (P o)) (k := k) (lam := lam) hg hp hc).2) hT
    (2 * (d - 1) + 1) (d - 1) [out] (by simp) (by simpa using hout)
  have h1 := KV.mul (κ := K.lk) (S := {q | K.InB 1 q}) (Gives.quote (θ := θ) (ofBits [true, false]) z) (by
    rw [path_ofBits]
    exact (accK_c (M := M) (m := m) (γ := MvPolynomial.constantCoeff (P o)) (k := k) (lam := lam)).2)
  rw [path_ofBits, hK, accK_c.1, ← hK] at h1
  have h2 := KV.app_gives (κ := K.lk) (S := {q | K.InB 1 q}) (p := (loopF M m).code)
    (Gives.cons (Gives.quote (θ := θ) (loopF M m).code z) (Gives.cons (Gives.quote (num (d - 1)) z)
      (Gives.cons (Gives.quote (listT ([out].map ofBits)) z) (treeF_gives m z)))) (by
        rw [Fm.ofTree_code]
        exact hloop)
  refine ((KV.either h1 h2).mono ?_).congr ?_
  · have e : 2 * (d - 1) + 1 + 1 = 2 * d := by omega
    rw [e]
    have h4 : d * (800 * (M + m) + 4000) = 2 * d * (400 * (M + m) + 2000) := by ring
    have h5 : m * (40 * (z.size + 2) + 10) = 40 * ((z.size + 2) * m) + 10 * m := by ring
    have h6 : (z.size + 2) * (40 * m + 60) = 40 * ((z.size + 2) * m) + 60 * (z.size + 2) := by ring
    omega
  · rw [sum_coeff_line _ _ _ _ hd, List.map_singleton, hval]

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "One scale is all scales": constants are postponed
-/

namespace Paper

open NS1
open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- The instance z_e of the paper: run p on the argument and accept exactly the runs whose bill uses each name the
prescribed number of times. -/
def postponed (p z : Tree) (e : Bt) : Tree := zq p z e

/-- **Paper: Lemma lem:postpone.** "Let all runs of a program p on an argument halt, the accepting ones within T < 2^J
steps and with names among the leaves of a binary trie with Q′ nodes and height η; let its leaves stand for powers
λ_1, λ_2, … Its value is ∑_e λ^e sum(z_e) over the vectors e with one entry in {0, …, 2^J−1} for every leaf, where the
instance z_e accepts exactly the runs of p whose bill uses each name the prescribed number of times. It is plain within
O(T(J + η + 1) + Q′J) steps, and its size is that of p and the argument plus O(Q′J)." The trie is L and L.budg J lists
the exponent vectors e with their λ^e. "Accepts exactly": the accepting runs of z_e, in their order, are those of p with ok e bill (every counter of e is 0
after the bill), with the same weights; pv(z_e) is therefore the sum of these weights. -/
theorem lem_postpone (p z : Tree) {T J : ℕ} (hJ : T < 2 ^ J) (hh : Hl θ (Fm.ofTree p) z)
    (hc : ∀ r ∈ evl θ (Fm.ofTree p) z, r.cost ≤ T) (L : KT R) (κ : List Bool → R)
    (hκ : ∀ r ∈ evl θ (Fm.ofTree p) z, ∀ n ∈ r.bill, κ n = L.lookup n) :
    val κ (evl θ (Fm.ofTree p) z) = ((L.budg J).map fun e => e.2 * algebraMap A R (pv θ (postponed p z e.1))).sum ∧
      ∀ e ∈ L.budg J,
        Plain θ ((1000 + 100 * (L.ht + J + 1)) * T + 40 * (L.nds * (J + 1)) + 40) (postponed p z e.1) ∧
        (postponed p z e.1).size ≤ WF.code.size + p.size + z.size + 4 * (L.nds * (J + 1)) + 3 ∧
        pv θ (postponed p z e.1) = ((evl θ (Fm.ofTree p) z).map fun r => if ok e.1 r.bill = true then r.th else 0).sum ∧
        (evl θ (Fm.ofTree (postponed p z e.1).hd) (postponed p z e.1).tl).map Run.th =
          ((evl θ (Fm.ofTree p) z).filter fun r => ok e.1 r.bill).map Run.th := by
  have hp : ∀ e ∈ L.budg J, Plain θ ((1000 + 100 * (L.ht + J + 1)) * T + 40 * (L.nds * (J + 1)) + 40) (zq p z e.1) ∧
      pv θ (zq p z e.1) = ((evl θ (Fm.ofTree p) z).map fun r => if ok e.1 r.bill = true then r.th else 0).sum ∧
      (evl θ (Fm.ofTree (zq p z e.1).hd) (zq p z e.1).tl).map Run.th =
        ((evl θ (Fm.ofTree p) z).filter fun r => ok e.1 r.bill).map Run.th :=
    fun e he => zq_plain hh.ev hc (KT.ht_budg he) (by
      have := Nat.mul_le_mul_left 40 (KT.nds_budg he)
      unfold MM
      omega)
  refine ⟨?_, fun e he => ⟨(hp e he).1, ?_, (hp e he).2⟩⟩
  · rw [val_eq_sum_budg (J := J) (K := L) (fun r hr => lt_of_le_of_lt ((bill_le hh.ev r hr).trans (hc r hr)) hJ) hκ]
    refine congrArg List.sum (List.map_congr_left fun e he => ?_)
    rw [← (hp e he).2.1]
    rfl
  · have h1 := Bt.size_enc e.1
    have h2 := KT.nds_budg he
    simp only [postponed, zq, Tree.size]
    omega

end Paper

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# One round: guess exponents, postpone, cut, accelerate
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- The cut at the scale `v ^ H`, for times up to `v ^ (H * α)`. -/
def CutAt (θ : List Bool → A) (H v α : ℕ) : Prop :=
  ∀ τ s, v ^ H ≤ τ → τ ≤ v ^ (H * α) → s * v ^ 48 ≤ τ → ∃ G, CutProg θ H v τ s G

theorem CutHyp.at {H C₀ v₀ v α : ℕ} (h : CutHyp θ H C₀ v₀) (hv : v₀ ≤ v) (hl : lg v ^ (C₀ * α) ≤ v) : CutAt θ H v α :=
  fun τ s => h v hv α τ s hl

theorem Plain.of_le {T T' : ℕ} {z : Tree} (h : Plain θ T z) (hT : T ≤ T') : Plain θ T' z :=
  ⟨h.1, fun r hr => ⟨(h.2 r hr).1, (h.2 r hr).2.trans hT⟩⟩

/-- A constant: it bounds the sizes of the fixed programs. -/
def cst : ℕ := WF.code.size + UF.code.size + 2000

theorem cst_def : cst = WF.code.size + UF.code.size + 2000 := rfl

theorem size_LP (D : Tree) : (LP D).code.size ≤ D.size + 300 := by
  simp only [LP, Fm.code, Tree.size, size_num]
  omega

theorem size_stepF (D G p : Tree) (g : Fm) :
    (stepF D G p g).code.size ≤ 2 * D.size + G.size + p.size + g.code.size + WF.code.size + 1500 := by
  have := size_LP D
  simp only [stepF, app, ZE, Fm.code, Tree.size, size_num]
  omega

theorem pow_le_pow {u a b : ℕ} (hu : 1 ≤ u) (h : a ≤ b) : u ^ a ≤ u ^ b := Nat.pow_le_pow_right hu h

/-- **One round.** `τ'` bounds the time of the plain instances; `s` their size. -/
theorem round {H u v : ℕ} {K : KT R} {B' : ℕ} {D : Tree} (hD : IsAccT θ H u (u ^ (H - 16)) K B' D)
    {p : Tree} {B τ : ℕ} (hp : IsPre θ H v τ K B p) {J : ℕ} (hJ : τ < 2 ^ J) {τ' s t tG Ln : ℕ} {G : Tree}
    (hG : CutProg θ H u τ' s G)
    (hτ' : MM (K.ht + B + J + 1) * τ + 40 * ((K.expand B).nds * (J + 1)) + 40 ≤ τ')
    (hs : WF.code.size + p.size + v ^ (H - 32) + 4 * ((K.expand B).nds * (J + 1)) + 3 ≤ s)
    (htG : ∀ k, k * u ^ 24 ≤ τ' → k ≤ tG) (hLn : ∀ k, k * u ^ H ≤ τ' * u ^ 2 → k ≤ Ln)
    (ht : (8 * J + 10) * (K.expand B).nds + tG + (u ^ (H - 16) + 30) * Ln + 30 ≤ t) :
    IsAccT θ H v t K (max (B + J) B') (stepF D G p (gt id J B K [])).code := by
  have hg : ∀ z : Tree, ∃ l, Ev θ (gt id J B K []) z l ∧ List.Forall₂
      (RelG K.lk (K.InB (max (B + J) B')) ((8 * J + 10) * (K.expand B).nds)) l ((K.expand B).budg J) := by
    intro z
    refine gt_ev z K [] fun q hq i hi => ⟨?_, ?_⟩
    · rfl
    · exact hq.inB (lt_of_lt_of_le hi (le_max_left _ _))
  have hqs : ∀ q ∈ (K.expand B).budg J, q.1.ht ≤ K.ht + B + J + 1 ∧ q.1.nds ≤ (K.expand B).nds * (J + 1) := by
    intro q hq
    have h1 := KT.ht_budg hq
    have h2 := KT.ht_expand B K
    exact ⟨by omega, KT.nds_budg hq⟩
  have hsz : ∀ z : Tree, z.size ≤ v ^ (H - 32) → ∀ q ∈ (K.expand B).budg J, (zq p z q.1).size ≤ s := by
    intro z hz q hq
    have h1 := Bt.size_enc q.1
    have h2 := (hqs q hq).2
    simp only [zq, Tree.size]
    omega
  have key : ∀ z : Tree, z.size ≤ v ^ (H - 32) → ∀ q ∈ (K.expand B).budg J,
      Hl θ (Fm.ofTree G) (zq p z q.1) ∧ ∀ r ∈ evl θ (Fm.ofTree G) (zq p z q.1), r.bill = [] ∧
      r.cost ≤ tG ∧ r.out.toList.length ≤ Ln ∧ ∀ y ∈ r.out.toList, Hl θ (Fm.ofTree D) y ∧
        ∀ r ∈ evl θ (Fm.ofTree D) y, r.cost ≤ u ^ (H - 16) ∧ ∀ n ∈ r.bill, K.InB (max (B + J) B') n := by
    intro z hz q hq
    obtain ⟨h1, h2⟩ := hG.list _ (hsz z hz q hq)
    refine ⟨h1, fun r hr => ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := h2 r hr
    refine ⟨a1, htG _ a2, hLn _ a3, fun y hy => ?_⟩
    obtain ⟨b1, b2⟩ := hD.run y (a4 y hy)
    exact ⟨b1, fun r hr => ⟨(b2 r hr).1, fun n hn => ((b2 r hr).2 n hn).mono (le_max_right _ _)⟩⟩
  constructor
  · intro z hz
    obtain ⟨lg, eg, rg⟩ := hg z
    obtain ⟨l, e, h1, -⟩ := stepF_ev (p := p) eg rg (key z hz)
    rw [Fm.ofTree_code]
    refine ⟨e.hl, fun r hr => ?_⟩
    rw [e.evl] at hr
    obtain ⟨c1, c2⟩ := h1 r hr
    exact ⟨c1.trans ht, c2⟩
  · intro z hz hpl
    obtain ⟨lg, eg, rg⟩ := hg z
    obtain ⟨l, e, -, h2⟩ := stepF_ev (p := p) eg rg (key z hz)
    rw [Fm.ofTree_code, e.evl, h2, ← hp.val z hz hpl]
    obtain ⟨hp1, hp2⟩ := hp.run z hz hpl
    -- Lemma lem:postpone: the value of p, by the exponent vectors
    obtain ⟨hsum, hze⟩ := Paper.lem_postpone p z hJ hp1 (fun r hr => (hp2 r hr).1) (K.expand B) K.lk
      fun r hr n hn => KT.lookup_expand ((hp2 r hr).2 n hn)
    rw [hsum]
    refine congrArg List.sum (List.map_congr_left fun q hq => congrArg (q.2 * ·) ?_)
    obtain ⟨pl, -, -⟩ := hze q hq
    have hht := KT.ht_expand B K
    have pl' : Plain θ τ' (zq p z q.1) := Plain.of_le pl ((Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (show 1000 + 100 * ((K.expand B).ht + J + 1) ≤ MM (K.ht + B + J + 1) by
        unfold MM; omega)) _) _).trans hτ')
    obtain ⟨v1, v2⟩ := hG.val _ (hsz z hz q hq) pl'
    show sumF K.lk _ _ = algebraMap A R (pv θ (zq p z q.1))
    rw [v2, map_list_sum, List.map_map, sumF]
    congr 1
    refine List.map_congr_left fun r hr => ?_
    obtain ⟨a1, a2, a3, a4⟩ := (hG.list _ (hsz z hz q hq)).2 r hr
    simp only [Function.comp_apply, map_mul, map_list_prod, List.map_map]
    congr 1
    · simp [wt, a1]
    · congr 1
      refine List.map_congr_left fun y hy => ?_
      exact hD.val y (a4 y hy) (v1 r hr y hy)

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Accelerators and changes of the ring of constants
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

section Map

variable {R' : Type} [CommRing R'] [Algebra A R']

namespace KT

/-- The images of the constants. -/
def map (f : R → R') : KT R → KT R'
  | none => none
  | leaf c => leaf (f c)
  | node l r => node (l.map f) (r.map f)

theorem nds_map (f : R → R') (K : KT R) : (K.map f).nds = K.nds := by
  induction K with
  | none => rfl
  | leaf c => rfl
  | node l r ihl ihr => simp [map, nds, ihl, ihr]

theorem ht_map (f : R → R') (K : KT R) : (K.map f).ht = K.ht := by
  induction K with
  | none => rfl
  | leaf c => rfl
  | node l r ihl ihr => simp [map, ht, ihl, ihr]

theorem combVal_map (f : R →+* R') (c : R) (p : List Bool) : combVal (f c) p = f (combVal c p) := by
  induction p generalizing c with
  | nil => simp [combVal]
  | cons b p ih =>
    cases b with
    | true => rw [combVal, combVal, ← map_pow, ih]
    | false =>
      cases p with
      | nil => rfl
      | cons a p => simp [combVal]

theorem lk_map (f : R →+* R') (K : KT R) (p : List Bool) : (K.map f).lk p = f (K.lk p) := by
  induction K generalizing p with
  | none => simp [map, lk]
  | leaf c => exact combVal_map f c p
  | node l r ihl ihr =>
    cases p with
    | nil => simp [map, lk]
    | cons a p =>
      cases a with
      | true => exact ihr p
      | false => exact ihl p

theorem inB_map (f : R → R') (B : ℕ) (K : KT R) (p : List Bool) : (K.map f).InB B p ↔ K.InB B p := by
  induction K generalizing p with
  | none => exact Iff.rfl
  | leaf c => exact Iff.rfl
  | node l r ihl ihr =>
    cases p with
    | nil => exact Iff.rfl
    | cons a p =>
      cases a with
      | true => exact ihr p
      | false => exact ihl p

/-- The constants. -/
def consts : KT R → Set R
  | none => ∅
  | leaf c => {c}
  | node l r => l.consts ∪ r.consts

theorem consts_finite (K : KT R) : K.consts.Finite := by
  induction K with
  | none => exact Set.finite_empty
  | leaf c => exact Set.finite_singleton c
  | node l r ihl ihr => exact ihl.union ihr

theorem exists_lift (S : Subalgebra A R) (K : KT R) (h : K.consts ⊆ S) : ∃ K' : KT S, K'.map S.val = K := by
  induction K with
  | none => exact ⟨none, rfl⟩
  | leaf c => exact ⟨leaf ⟨c, h rfl⟩, rfl⟩
  | node l r ihl ihr =>
    obtain ⟨l', rfl⟩ := ihl fun c hc => h (Or.inl hc)
    obtain ⟨r', rfl⟩ := ihr fun c hc => h (Or.inr hc)
    exact ⟨node l' r', rfl⟩

end KT

theorem val_map (f : R →ₐ[A] R') (K : KT R) (l : List (Run A)) : val (K.map f).lk l = f (val K.lk l) := by
  rw [val, val, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun r _ => ?_
  simp only [wt, Function.comp_apply, map_mul, AlgHom.commutes, map_list_prod, List.map_map]
  congr 2
  refine List.map_congr_left fun p _ => ?_
  exact KT.lk_map (f : R →+* R') K p

theorem IsAccT.map {H v t : ℕ} {K : KT R} {B : ℕ} {D : Tree} (h : IsAccT θ H v t K B D) (f : R →ₐ[A] R') :
    IsAccT θ H v t (K.map f) B D := by
  refine ⟨fun z hz => ⟨(h.run z hz).1, fun r hr => ⟨((h.run z hz).2 r hr).1, fun p hp =>
    (KT.inB_map f B K p).2 (((h.run z hz).2 r hr).2 p hp)⟩⟩, fun z hz hp => ?_⟩
  rw [val_map, h.val z hz hp, AlgHom.commutes]

theorem IsAccT.of_map {H v t : ℕ} {K : KT R} {B : ℕ} {D : Tree} {f : R →ₐ[A] R'} (hf : Function.Injective f)
    (h : IsAccT θ H v t (K.map f) B D) : IsAccT θ H v t K B D := by
  refine ⟨fun z hz => ⟨(h.run z hz).1, fun r hr => ⟨((h.run z hz).2 r hr).1, fun p hp =>
    (KT.inB_map f B K p).1 (((h.run z hz).2 r hr).2 p hp)⟩⟩, fun z hz hp => hf ?_⟩
  rw [← val_map, h.val z hz hp, AlgHom.commutes]

end Map

section Logs

theorem lt_two_pow_lg (n : ℕ) : n < 2 ^ lg n := Nat.lt_pow_succ_log_self (by norm_num) n

theorem lg_mono {a b : ℕ} (h : a ≤ b) : lg a ≤ lg b := Nat.succ_le_succ (Nat.log_mono_right h)

theorem lg_pow_le {n k : ℕ} (hk : 1 ≤ k) : lg (n ^ k) ≤ k * lg n := by
  have h1 : n ^ k < 2 ^ (k * lg n) := by
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left (lt_two_pow_lg n) (by omega)
  unfold lg at h1 ⊢
  refine Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow' ?_ h1)
  have : 1 * 1 ≤ k * (Nat.log 2 n + 1) := Nat.mul_le_mul hk (by omega)
  omega

theorem le_lg_pow {n k : ℕ} (hn : n ≠ 0) : k * (lg n - 1) + 1 ≤ lg (n ^ k) := by
  unfold lg
  rw [Nat.add_sub_cancel]
  refine Nat.succ_le_succ (Nat.le_log_of_pow_le (by norm_num) ?_)
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn) k

theorem le_lg_of_two_pow_le {n k : ℕ} (h : 2 ^ k ≤ n) : k + 1 ≤ lg n :=
  Nat.succ_le_succ (Nat.le_log_of_pow_le (by norm_num) h)

theorem two_pow_lg_le {n : ℕ} (hn : n ≠ 0) : 2 ^ (lg n - 1) ≤ n := by
  unfold lg
  rw [Nat.add_sub_cancel]
  exact Nat.pow_log_le_self 2 hn

/-- Powers of the logarithm are small. -/
theorem poly_lg (c k : ℕ) : ∃ n₀, ∀ n, n₀ ≤ n → c * lg n ^ k ≤ n := by
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt k (show (1 : ℝ) < 2 by norm_num)
  have h2 : ∀ᶠ L : ℕ in Filter.atTop, (L : ℝ) ^ k / 2 ^ L < 1 / (2 * (c + 1)) :=
    h1.eventually (gt_mem_nhds (by positivity))
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 h2
  refine ⟨2 ^ L₀ + 1, fun n hn => ?_⟩
  have hp : 1 ≤ 2 ^ L₀ := Nat.one_le_two_pow
  have hn0 : n ≠ 0 := by omega
  have hL : L₀ ≤ lg n := (Nat.le_succ _).trans (le_lg_of_two_pow_le (by omega))
  have h3 := hL₀ (lg n) hL
  have h4 := two_pow_lg_le hn0
  have hlg : 1 ≤ lg n := by unfold lg; omega
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h3
  have h5 : (c : ℝ) * (lg n : ℝ) ^ k ≤ 2 ^ (lg n - 1) := by
    have e : (2 : ℝ) ^ lg n = 2 * 2 ^ (lg n - 1) := by
      have : lg n = lg n - 1 + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    rw [e] at h3
    have : (0 : ℝ) ≤ (lg n : ℝ) ^ k := by positivity
    nlinarith
  have h6 : c * lg n ^ k ≤ 2 ^ (lg n - 1) := by exact_mod_cast h5
  exact h6.trans h4

end Logs

theorem lg_ge_two {u : ℕ} (hu : 4 ≤ u) : 2 ≤ lg u := le_trans (by norm_num) (le_lg_of_two_pow_le (k := 2) (by omega))

/-- There is an accelerator of size `s` at the scale `V = v ^ H` over `R`: a trie of at most `s` nodes with constants
of `R`, and a program of size at most `s` that has the values of the universal plain sums of `V` steps on all
instances of size `V ^ (1 - 2 η)` in `V ^ (1 - η)` steps, `η = 16 / H`; names of constants and exponents are of
polylogarithmic length. -/
def HasAcc (θ : List Bool → A) (R : Type) [CommRing R] [Algebra A R] (H v s : ℕ) : Prop :=
  ∃ (K : KT R) (B : ℕ) (D : Tree), IsAccT θ H v (v ^ (H - 16)) K B D ∧ K.nds ≤ s ∧ D.size ≤ s ∧
    K.ht ≤ lg (max (v ^ H) s) ^ 2 ∧ B ≤ lg (max (v ^ H) s) ^ 3

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The size of the program of low degree
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

section Size

theorem size_quote (c : Tree) : (Fm.quote c).code.size = c.size + 2 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_id : Fm.id.code.size = 5 := by
  simp only [Fm.code, Tree.size, size_num]

theorem size_hd (a : Fm) : (Fm.hd a).code.size = a.code.size + 6 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_tl (a : Fm) : (Fm.tl a).code.size = a.code.size + 8 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_cons (a b : Fm) : (Fm.cons a b).code.size = a.code.size + b.code.size + 11 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_ite (a b c : Fm) : (Fm.ite a b c).code.size = a.code.size + b.code.size + c.code.size + 14 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_run (a b : Fm) : (Fm.run a b).code.size = a.code.size + b.code.size + 15 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_guess : Fm.guess.code.size = 17 := by
  simp only [Fm.code, Tree.size, size_num]

theorem size_mul (a : Fm) : (Fm.mul a).code.size = a.code.size + 22 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_app (p : Tree) (e : Fm) : (app p e).code.size = p.size + e.code.size + 17 := by
  rw [app, size_run, size_quote]; ring

theorem size_lett (e b : Fm) : (lett e b).code.size = b.code.size + e.code.size + 17 := by
  rw [lett, size_run, size_quote]; ring

theorem size_gwd (M : ℕ) : (gwd M).code.size = 50 * M + 3 := by
  induction M with
  | zero => simp [gwd, size_quote, Tree.size]
  | succ M ih =>
    rw [gwd, size_cons, size_ite, size_guess, size_quote, size_quote, ih]
    simp only [one, Tree.size]
    ring

theorem size_walkF (m : ℕ) : (walkF m).code.size = (stepW.code.size + 17) * m + 5 := by
  induction m with
  | zero => simp [walkF, size_id]
  | succ m ih =>
    rw [walkF, size_lett, ih]
    ring

theorem size_pairsF (m : ℕ) (l : Fm) : (pairsF m l).code.size = l.code.size + (2 * pairB.code.size + 30) * m := by
  induction m generalizing l with
  | zero => simp [pairsF]
  | succ m ih =>
    rw [pairsF, ih, size_app, size_cons, size_quote]
    ring

/-- The size of the program. -/
theorem size_accF : ∃ c : ℕ, ∀ (M m d : ℕ) (out : List Bool), out.length = M →
    (accF M m d out).code.size ≤ c * (M + m + 1) + 2 * d := by
  obtain ⟨c1, hc1⟩ : ∃ n, n = stepW.code.size := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ n, n = leafB.code.size := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ n, n = intB.code.size := ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ n, n = pairB.code.size := ⟨_, rfl⟩
  obtain ⟨c5, hc5⟩ : ∃ n, n = (wordB lt0 lt1).code.size := ⟨_, rfl⟩
  obtain ⟨c6, hc6⟩ : ∃ n, n = lt2.size := ⟨_, rfl⟩
  obtain ⟨c7, hc7⟩ : ∃ n, n = (ofBits [true, false]).size := ⟨_, rfl⟩
  obtain ⟨c8, hc8⟩ : ∃ n, n = Fm.fail.code.size := ⟨_, rfl⟩
  have hloop : ∀ M m, (loopF M m).code.size ≤ 200 * M + (c1 + 17) * m + (c2 + c3 + c8 + 500) := by
    intro M m
    rw [loopF, size_ite, size_ite, leafF, intF, size_lett, size_ite, size_lett, size_cons, size_cons, size_cons, size_lett,
      size_cons, size_gwd, size_walkF]
    simp only [size_hd, size_tl, size_id, size_guess, size_quote, Tree.size, ← hc1, ← hc2, ← hc3, ← hc8]
    omega
  refine ⟨2 * (200 + c1 + 17 + c2 + c3 + c8 + 500) + (2 * c4 + 30) + 2 * c5 + c6 + c7 + 500, fun M m d out ho => ?_⟩
  have h1 := hloop M m
  have h2 := size_ofBits out
  rw [ho] at h2
  rw [accF, size_ite, size_mul, size_app, size_cons, size_cons, size_cons, treeF, size_hd, size_pairsF, size_app, size_cons,
    size_cons]
  simp only [size_guess, size_quote, size_id, size_num, ← hc4, ← hc5, ← hc6, ← hc7, List.map_cons, List.map_nil, listT,
    Tree.size]
  have h3 : (c1 + 17) * m ≤ (c1 + 17) * (M + m + 1) := Nat.mul_le_mul_left _ (by omega)
  have h4 : (2 * c4 + 30) * m ≤ (2 * c4 + 30) * (M + m + 1) := Nat.mul_le_mul_left _ (by omega)
  have h5 : c2 + c3 + c8 + 500 ≤ (c2 + c3 + c8 + 500) * (M + m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h6 : 2 * c5 + c6 + c7 + 400 ≤ (2 * c5 + c6 + c7 + 400) * (M + m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h7 : (2 * (200 + c1 + 17 + c2 + c3 + c8 + 500) + (2 * c4 + 30) + 2 * c5 + c6 + c7 + 500) * (M + m + 1) =
      400 * (M + m + 1) + 2 * ((c1 + 17) * (M + m + 1)) + 2 * ((c2 + c3 + c8 + 500) * (M + m + 1)) +
      (2 * c4 + 30) * (M + m + 1) + (2 * c5 + c6 + c7 + 400) * (M + m + 1) + 100 * (M + m + 1) := by ring
  omega

end Size

end NS1

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The classes VP and VNP

Valiant's classes over a commutative semiring: families of polynomials with polynomially many variables,
polynomial degree and circuits of polynomial size; and sums of such polynomials over all values 0, 1 of some of
the variables.
-/

namespace Nc

open Finset

section Definitions

/-- A family of polynomials, with finitely many variables for every n. -/
structure Family (F : Type*) [CommSemiring F] where
  /-- the variables -/
  X : ℕ → Type
  /-- finitely many -/
  [fin : ∀ n, Fintype (X n)]
  /-- the polynomials -/
  poly : ∀ n, MvPolynomial (X n) F

attribute [instance] Family.fin

variable (F : Type*) [CommSemiring F]

/-- VP: the families with polynomially many variables, polynomial degree and circuits of polynomial size. -/
def VP : Set (Family F) :=
  {p | ∃ C : ℕ, ∀ n, Fintype.card (p.X n) ≤ n ^ C + C ∧ (p.poly n).totalDegree ≤ n ^ C + C ∧
    Computes (p.poly n) (n ^ C + C)}

variable {F} in
/-- Substitute the bits e for the variables of the second kind. -/
noncomputable def bits {X : Type*} {m : ℕ} (q : MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    MvPolynomial X F :=
  MvPolynomial.aeval (Sum.elim MvPolynomial.X fun i => if e i then 1 else 0) q

/-- VNP: the families p n (x) = ∑ q n (x, e), the sum over all e in {0, 1} ^ m n, for a family q in VP (so m is
polynomially bounded). -/
def VNP : Set (Family F) :=
  {p | ∃ (m : ℕ → ℕ) (q : ∀ n, MvPolynomial (p.X n ⊕ Fin (m n)) F),
    ({ X := fun n => p.X n ⊕ Fin (m n), poly := q } : Family F) ∈ VP F ∧
      ∀ n, p.poly n = ∑ e : Fin (m n) → Bool, bits (q n) e}

end Definitions

section Size

variable {F : Type*} [CommSemiring F] {X Y : Type*}

theorem Computes.mono {p : MvPolynomial X F} {s t : ℕ} (h : Computes p s) (hst : s ≤ t) : Computes p t := by
  obtain ⟨l, hl, a, ha, rfl⟩ := h
  refine ⟨fun k => if k < s then l k else MvPolynomial.C 0, fun k hk => ?_, a, by omega, if_pos ha⟩
  by_cases h : k < s
  · have e : ∀ i < k, (if i < s then l i else MvPolynomial.C 0) = l i := fun i hi => if_pos (by omega)
    rcases hl k h with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
    · exact Or.inl ⟨i, by simp only [h, if_true, h1]⟩
    · exact Or.inr (Or.inl ⟨c, by simp only [h, if_true, h1]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by
        simp only [h, if_true, h1, show i < s by omega, show j < s by omega]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by
        simp only [h, if_true, h1, show i < s by omega, show j < s by omega]⟩))
  · exact Or.inr (Or.inl ⟨0, by simp only [h, if_false]⟩)

/-- Circuits over a larger ring. -/
theorem Computes.map {K : Type*} [CommSemiring K] (φ : F →+* K) {p : MvPolynomial X F} {s : ℕ}
    (h : Computes p s) : Computes (MvPolynomial.map φ p) s := by
  obtain ⟨l, hl, a, ha, rfl⟩ := h
  refine ⟨fun k => MvPolynomial.map φ (l k), fun k hk => ?_, a, ha, rfl⟩
  rcases hl k hk with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
  · exact Or.inl ⟨i, by simp [h1]⟩
  · exact Or.inr (Or.inl ⟨φ c, by simp [h1]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by simp [h1]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by simp [h1]⟩))

/-- Circuits with renamed variables. -/
theorem Computes.rename (f : X → Y) {p : MvPolynomial X F} {s : ℕ} (h : Computes p s) :
    Computes (MvPolynomial.rename f p) s := by
  obtain ⟨l, hl, a, ha, rfl⟩ := h
  refine ⟨fun k => MvPolynomial.rename f (l k), fun k hk => ?_, a, ha, rfl⟩
  rcases hl k hk with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
  · exact Or.inl ⟨f i, by simp [h1]⟩
  · exact Or.inr (Or.inl ⟨c, by simp [h1]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by simp [h1]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by simp [h1]⟩))

/-- Two circuits side by side, and one more gate. -/
theorem Computes.join {p q r : MvPolynomial X F} {s t : ℕ} (hp : Computes p s) (hq : Computes q t)
    (hr : r = p + q ∨ r = p * q) : Computes r (s + t + 1) := by
  obtain ⟨l, hl, a, ha, rfl⟩ := hp
  obtain ⟨l', hl', b, hb, rfl⟩ := hq
  let L : ℕ → MvPolynomial X F := fun k => if k < s then l k else if k < s + t then l' (k - s) else r
  have L1 : ∀ k < s, L k = l k := fun k hk => if_pos hk
  have L2 : ∀ k < t, L (s + k) = l' k := fun k hk => by
    simp only [L]
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  have L3 : L (s + t) = r := by
    simp only [L]
    rw [if_neg (by omega), if_neg (by omega)]
  refine ⟨L, fun k hk => ?_, s + t, by omega, L3⟩
  rcases lt_or_ge k s with h | h
  · unfold IsStep
    rw [L1 k h]
    rcases hl k h with e | e | ⟨i, hi, j, hj, e⟩ | ⟨i, hi, j, hj, e⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by rw [L1 i (by omega), L1 j (by omega), e]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by rw [L1 i (by omega), L1 j (by omega), e]⟩))
  · rcases lt_or_ge k (s + t) with h' | h'
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
      have hk' : k < t := by omega
      unfold IsStep
      rw [L2 k hk']
      rcases hl' k hk' with e | e | ⟨i, hi, j, hj, e⟩ | ⟨i, hi, j, hj, e⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl ⟨s + i, by omega, s + j, by omega, by
          rw [L2 i (by omega), L2 j (by omega), e]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨s + i, by omega, s + j, by omega, by
          rw [L2 i (by omega), L2 j (by omega), e]⟩))
    · obtain rfl : k = s + t := by omega
      unfold IsStep
      rw [L3]
      rcases hr with hr | hr
      · exact Or.inr (Or.inr (Or.inl ⟨a, by omega, s + b, by omega, by rw [L1 a ha, L2 b hb, hr]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨a, by omega, s + b, by omega, by rw [L1 a ha, L2 b hb, hr]⟩))

/-- The polynomial has circuits with s gates and degree at most d. -/
def CSize (p : MvPolynomial X F) (s d : ℕ) : Prop := Computes p s ∧ p.totalDegree ≤ d

namespace CSize

theorem mono {p : MvPolynomial X F} {s d s' d' : ℕ} (h : CSize p s d) (hs : s ≤ s') (hd : d ≤ d') :
    CSize p s' d' := ⟨h.1.mono hs, h.2.trans hd⟩

theorem var (x : X) : CSize (MvPolynomial.X x : MvPolynomial X F) 1 1 := by
  refine ⟨⟨fun _ => MvPolynomial.X x, fun _ _ => Or.inl ⟨x, rfl⟩, 0, by omega, rfl⟩, ?_⟩
  refine (MvPolynomial.totalDegree_monomial_le (R := F) (Finsupp.single x 1) 1).trans ?_
  rw [Finsupp.sum_single_index rfl]
  exact le_rfl

theorem const (a : F) : CSize (MvPolynomial.C a : MvPolynomial X F) 1 0 := by
  refine ⟨⟨fun _ => MvPolynomial.C a, fun _ _ => Or.inr (Or.inl ⟨a, rfl⟩), 0, by omega, rfl⟩, ?_⟩
  rw [MvPolynomial.totalDegree_C]

theorem add {p q : MvPolynomial X F} {s d t : ℕ} (hp : CSize p s d) (hq : CSize q t d) :
    CSize (p + q) (s + t + 1) d :=
  ⟨hp.1.join hq.1 (Or.inl rfl), (MvPolynomial.totalDegree_add p q).trans (max_le hp.2 hq.2)⟩

theorem mul {p q : MvPolynomial X F} {s d t e : ℕ} (hp : CSize p s d) (hq : CSize q t e) :
    CSize (p * q) (s + t + 1) (d + e) :=
  ⟨hp.1.join hq.1 (Or.inr rfl), (MvPolynomial.totalDegree_mul p q).trans (add_le_add hp.2 hq.2)⟩

theorem sum {ι : Type*} (A : Finset ι) {f : ι → MvPolynomial X F} {s d : ℕ} (h : ∀ i ∈ A, CSize (f i) s d) :
    CSize (∑ i ∈ A, f i) (A.card * (s + 1) + 1) d := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have := (const (X := X) (0 : F)).mono (s' := 1) (d' := d) le_rfl (Nat.zero_le _)
    rw [map_zero] at this
    simpa using this
  | insert i A hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    refine ((h i (Finset.mem_insert_self i A)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).mono ?_ le_rfl
    ring_nf
    omega

theorem prod {ι : Type*} (A : Finset ι) {f : ι → MvPolynomial X F} {s d : ℕ} (h : ∀ i ∈ A, CSize (f i) s d) :
    CSize (∏ i ∈ A, f i) (A.card * (s + 1) + 1) (A.card * d) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    have := const (X := X) (1 : F)
    rw [map_one] at this
    simpa using this
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    refine ((h i (Finset.mem_insert_self i A)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).mono ?_ ?_
    · ring_nf
      omega
    · ring_nf
      omega

end CSize

end Size

section Subset

variable {F : Type*} [CommSemiring F] {X : Type*}

theorem bits_rename {m : ℕ} (p : MvPolynomial X F) (e : Fin m → Bool) :
    bits (MvPolynomial.rename (Sum.inl : X → X ⊕ Fin m) p) e = p := by
  rw [bits, MvPolynomial.aeval_rename]
  exact MvPolynomial.aeval_X_left_apply p

theorem bits_add {m : ℕ} (p q : MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    bits (p + q) e = bits p e + bits q e := map_add _ _ _

theorem bits_mul {m : ℕ} (p q : MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    bits (p * q) e = bits p e * bits q e := map_mul _ _ _

theorem bits_sum {m : ℕ} {ι : Type*} (A : Finset ι) (f : ι → MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    bits (∑ i ∈ A, f i) e = ∑ i ∈ A, bits (f i) e := map_sum _ _ _

theorem bits_prod {m : ℕ} {ι : Type*} (A : Finset ι) (f : ι → MvPolynomial (X ⊕ Fin m) F) (e : Fin m → Bool) :
    bits (∏ i ∈ A, f i) e = ∏ i ∈ A, bits (f i) e := map_prod _ _ _

theorem bits_C {m : ℕ} (a : F) (e : Fin m → Bool) :
    bits (MvPolynomial.C a : MvPolynomial (X ⊕ Fin m) F) e = MvPolynomial.C a := by
  rw [bits, MvPolynomial.aeval_C]
  rfl

theorem bits_inl {m : ℕ} (x : X) (e : Fin m → Bool) :
    bits (MvPolynomial.X (Sum.inl x) : MvPolynomial (X ⊕ Fin m) F) e = MvPolynomial.X x := by
  simp [bits]

theorem bits_inr {m : ℕ} (i : Fin m) (e : Fin m → Bool) :
    bits (MvPolynomial.X (Sum.inr i) : MvPolynomial (X ⊕ Fin m) F) e = if e i then 1 else 0 := by
  simp [bits]

end Subset

end Nc

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "One scale is all scales": low degree is fast
-/

namespace Paper

open Finset NS1
open _root_.NS1.Tree

open Nc.Acc in
/-- The part of degree i is what the point scales by the ith power. -/
theorem line_coeff_eq {R σ : Type} [CommRing R] (u : σ → R) (p : MvPolynomial σ R) (i : ℕ) :
    (line u p).coeff i = MvPolynomial.eval u (MvPolynomial.homogeneousComponent i p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).2
      (MvPolynomial.isHomogeneous_monomial a rfl : (MvPolynomial.monomial d a).IsHomogeneous d.degree))]
    have e : line u (MvPolynomial.monomial d a) =
        Polynomial.C (MvPolynomial.eval u (MvPolynomial.monomial d a)) * Polynomial.X ^ d.degree := by
      simp only [line, MvPolynomial.aeval_monomial, MvPolynomial.eval_monomial, Finsupp.prod, mul_pow,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_eq]
      simp [Finsupp.degree, mul_assoc]
      rfl
    rw [e, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp
  | add p q hp hq => simp [map_add, hp, hq]

open Nc.Acc in
/-- **Paper: Lemma lem:lowdeg.** "Let a polynomial over R in variables (place, symbol), with n places, have a circuit
with S gates. A program of size O(log S + log n + d), with O((S+n)³) constants, has as value the sum of its parts of
degree at most d at the code of the word of every z with |z| < n, in (d+|z|+1)(log(S+n+d))^O(1) steps. All its runs halt, and it names only constants, not powers." The bound on
the height of the trie, O(log S + log n), is the one that Lemma lem:circuit needs. -/
theorem lem_lowdeg : ∃ c : ℕ, ∀ (R : Type) [CommRing R] (M m N d S : ℕ) (p : MvPolynomial (Fin N × Option Bool) R),
    Nc.Computes p S → S ≤ 2 ^ M → N ≤ 2 ^ m →
    ∃ (K : KT R) (D : Tree),
      K.nds ≤ 2 ^ (3 * M + 1) + 2 ^ (M + m + 3) + 3 ∧ K.ht ≤ 3 * M + m + 4 ∧ D.size ≤ c * (M + m + 1) + 2 * (d + 1) ∧
      ∀ (A : Type) [CommRing A] [Algebra A R] (θ : List Bool → A) (z : Tree), z.size < N →
        Hl θ (Fm.ofTree D) z ∧
        (∀ r ∈ evl θ (Fm.ofTree D) z,
          r.cost ≤ (d + 1) * (800 * (M + m) + 4000) + (z.size + 2) * (40 * m + 60) + 10 * m + 100 ∧
          ∀ q ∈ r.bill, K.InB 1 q) ∧
        val K.lk (evl θ (Fm.ofTree D) z) =
          ∑ i ∈ Finset.range (d + 1), MvPolynomial.eval (codeB R N (tbits z)) (MvPolynomial.homogeneousComponent i p) := by
  obtain ⟨c, hc⟩ := size_accF
  refine ⟨c, fun R _ M m N d S p hp hS hN => ?_⟩
  -- d' = d, but a constant needs d' = 1
  obtain ⟨d', q, hd', hd'1, hq, hqv⟩ : ∃ (d' : ℕ) (q : MvPolynomial (Fin N × Option Bool) R), 0 < d' ∧ d' ≤ d + 1 ∧
      Nc.Computes q S ∧ ∀ u : Fin N × Option Bool → R, ∑ i ∈ Finset.range (d' + 1), (line u q).coeff i =
        ∑ i ∈ Finset.range (d + 1), MvPolynomial.eval u (MvPolynomial.homogeneousComponent i p) := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · refine ⟨1, MvPolynomial.C (MvPolynomial.constantCoeff p), one_pos, le_rfl, ?_, fun u => ?_⟩
      · have hS1 : 1 ≤ S := by
          obtain ⟨l, -, a, ha, -⟩ := hp
          omega
        exact (Nc.CSize.const _).1.mono hS1
      · simp [Finset.sum_range_succ, line, MvPolynomial.homogeneousComponent_zero, MvPolynomial.constantCoeff_eq]
    · exact ⟨d, p, hd, Nat.le_succ d, hp, fun u => Finset.sum_congr rfl fun i _ => line_coeff_eq u p i⟩
  obtain ⟨K, out, hout, hnds, hht, hkv⟩ := accF_kv hq hS hd' hN
  refine ⟨K, (accF M m d' out).code, hnds, hht, (hc M m d' out hout).trans (by omega), fun A _ _ θ z hz => ?_⟩
  have h := hkv A θ z hz
  rw [Fm.ofTree_code]
  refine ⟨h.hl, fun r hr => ⟨(h.evl.1 r hr).1.trans ?_, (h.evl.1 r hr).2⟩, by rw [h.evl.2, hqv]⟩
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hd'1) _) _) _

end Paper

end

open NS1 MvPolynomial
namespace Paper
open Finset NS1
theorem lem_circuit_program (H : ℕ) (hH : 32 ≤ H) : ∃ c : ℕ, ∀ v a, 100 ≤ v → c * (a + H + 2) * lg v ≤ v →
    ∀ (A : Type) [CommRing A] (R : Type) [CommRing R] [Algebra A R] (θ : List Bool → A) (s : ℕ)
      (p : MvPolynomial (Fin (v ^ (H - 32) + 1) × Option Bool) R), s ≤ v ^ a → Nc.Computes p s →
    ∃ (K : KT R) (D : Tree), (∀ z : Tree, z.size ≤ v ^ (H - 32) → Hl θ (Fm.ofTree D) z ∧
        (∀ r ∈ evl θ (Fm.ofTree D) z, r.cost ≤ v ^ (H - 16) ∧ ∀ q ∈ r.bill, K.InB 1 q) ∧
        val K.lk (evl θ (Fm.ofTree D) z) = ∑ i ∈ Finset.range (v ^ (H - 32) + 1 + 1),
          MvPolynomial.eval (codeB R (v ^ (H - 32) + 1) (tbits z)) (MvPolynomial.homogeneousComponent i p)) ∧
      K.nds ≤ v ^ (3 * a + H + 20) ∧ D.size ≤ v ^ (3 * a + H + 20) ∧ K.ht ≤ (3 * a + H + 20) * lg v := by
  obtain ⟨c, hc⟩ := lem_lowdeg
  refine ⟨c + 10000, fun v a hv hlv A _ R _ _ θ s p hs hp => ?_⟩
  obtain ⟨d, hdd⟩ : ∃ d, d = v ^ (H - 32) + 1 := ⟨_, rfl⟩
  have hN1 : v ^ (H - 32) < v ^ (H - 32) + 1 := Nat.lt_succ_self _
  have hd : d ≤ v ^ (H - 24) := by
    rw [hdd]
    exact Nat.succ_le_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
  have hN2 : v ^ (H - 32) + 1 ≤ v ^ H := Nat.succ_le_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
  have hv1 : 1 ≤ v := by omega
  have hv100 : 100 ≤ v := by omega
  obtain ⟨l, hl⟩ : ∃ l, l = lg v := ⟨_, rfl⟩
  have hl2 : 2 ≤ l := hl ▸ lg_ge_two (by omega)
  rw [← hl] at hlv
  obtain ⟨M, hM⟩ : ∃ M, M = lg (v ^ (a + 1)) := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = lg (v ^ H) := ⟨_, rfl⟩
  have hMl : M ≤ (a + 1) * l := by rw [hM, hl]; exact lg_pow_le (by omega)
  have hml : m ≤ H * l := by rw [hm, hl]; exact lg_pow_le (by omega)
  have hMm : M + m + 1 ≤ (a + H + 2) * l := by
    have : (a + H + 2) * l = (a + 1) * l + H * l + l := by ring
    omega
  have hsM : s ≤ 2 ^ M := by
    have h1 := lt_two_pow_lg (v ^ (a + 1))
    rw [← hM] at h1
    exact (hs.trans (Nat.pow_le_pow_right hv1 (Nat.le_succ a))).trans h1.le
  have hNm : v ^ (H - 32) + 1 ≤ 2 ^ m := by
    have h1 := lt_two_pow_lg (v ^ H)
    rw [← hm] at h1
    exact hN2.trans h1.le
  obtain ⟨K, D, hnds, hht, hDsize, hkv⟩ := hc R M m (v ^ (H - 32) + 1) d s p hp hsM hNm
  have hcost : ∀ z : Tree, z.size ≤ v ^ (H - 32) →
      (d + 1) * (800 * (M + m) + 4000) + (z.size + 2) * (40 * m + 60) + 10 * m + 100 ≤ v ^ (H - 16) := by
    intro z hz
    have e1 : 10000 * ((a + H + 2) * l) ≤ v := by
      refine le_trans ?_ hlv
      have : (c + 10000) * (a + H + 2) * l = c * ((a + H + 2) * l) + 10000 * ((a + H + 2) * l) := by ring
      rw [this]
      exact Nat.le_add_left _ _
    have e2 : 800 * (M + m) + 4000 ≤ v := by omega
    have e3 : 40 * m + 60 ≤ v := by omega
    have e4 : v ^ (H - 24) * v ^ 8 = v ^ (H - 16) := by rw [← pow_add]; congr 1; omega
    have e5 : v ^ (H - 32) ≤ v ^ (H - 24) := Nat.pow_le_pow_right hv1 (by omega)
    have e6 : 1 ≤ v ^ (H - 24) := Nat.one_le_pow _ _ hv1
    have e7 : (d + 1) * (800 * (M + m) + 4000) ≤ 2 * v ^ (H - 24) * v := Nat.mul_le_mul (by omega) e2
    have e8 : (z.size + 2) * (40 * m + 60) ≤ 3 * v ^ (H - 24) * v := Nat.mul_le_mul (by omega) e3
    have e9 : 10 * m + 100 ≤ 2 * v ^ (H - 24) * v := by
      have : v ≤ v ^ (H - 24) * v := Nat.le_mul_of_pos_left _ (by omega)
      have h2 : 2 * v ^ (H - 24) * v = 2 * (v ^ (H - 24) * v) := by ring
      omega
    have e10 : 7 * v ≤ v ^ 8 := by
      calc 7 * v ≤ v * v := Nat.mul_le_mul_right _ (by omega)
        _ = v ^ 2 := (pow_two v).symm
        _ ≤ v ^ 8 := Nat.pow_le_pow_right hv1 (by norm_num)
    calc (d + 1) * (800 * (M + m) + 4000) + (z.size + 2) * (40 * m + 60) + 10 * m + 100
        ≤ 2 * v ^ (H - 24) * v + 3 * v ^ (H - 24) * v + 2 * v ^ (H - 24) * v := by omega
      _ = v ^ (H - 24) * (7 * v) := by ring
      _ ≤ v ^ (H - 24) * v ^ 8 := Nat.mul_le_mul_left _ e10
      _ = v ^ (H - 16) := e4
  refine ⟨K, D, fun z hz => ?_, ?_, ?_, ?_⟩
  · obtain ⟨a1, a2, a3⟩ := hkv A θ z (lt_of_le_of_lt hz hN1)
    rw [hdd] at a3
    exact ⟨a1, fun r hr => ⟨(a2 r hr).1.trans (hcost z hz), (a2 r hr).2⟩, a3⟩
  · -- the number of constants
    have h1 : 2 ^ M ≤ 2 * v ^ (a + 1) := by
      have h2 := two_pow_lg_le (n := v ^ (a + 1)) (by positivity)
      have h3 : M = M - 1 + 1 := by
        have : 1 ≤ lg (v ^ (a + 1)) := by unfold lg; omega
        omega
      rw [← hM] at h2
      rw [h3, pow_succ]
      omega
    have h2 : 2 ^ m ≤ 2 * v ^ H := by
      have h2 := two_pow_lg_le (n := v ^ H) (by positivity)
      have h3 : m = m - 1 + 1 := by
        have : 1 ≤ lg (v ^ H) := by unfold lg; omega
        omega
      rw [← hm] at h2
      rw [h3, pow_succ]
      omega
    have h3 : 2 ^ (3 * M + 1) ≤ 16 * v ^ (3 * a + H + 3) := by
      calc 2 ^ (3 * M + 1) = 2 * (2 ^ M) ^ 3 := by rw [pow_succ, mul_comm 3 M, pow_mul]; ring
        _ ≤ 2 * (2 * v ^ (a + 1)) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 3)
        _ = 16 * v ^ (3 * a + 3) := by rw [mul_pow, ← pow_mul]; ring
        _ ≤ 16 * v ^ (3 * a + H + 3) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hv1 (by omega))
    have h4 : 2 ^ (M + m + 3) ≤ 32 * v ^ (3 * a + H + 3) := by
      calc 2 ^ (M + m + 3) = 8 * (2 ^ M * 2 ^ m) := by rw [pow_add, pow_add]; ring
        _ ≤ 8 * (2 * v ^ (a + 1) * (2 * v ^ H)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)
        _ = 32 * v ^ (a + 1 + H) := by rw [pow_add v (a + 1) H]; ring
        _ ≤ 32 * v ^ (3 * a + H + 3) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hv1 (by omega))
    have h5 : 1 ≤ v ^ (3 * a + H + 3) := Nat.one_le_pow _ _ hv1
    calc K.nds ≤ 2 ^ (3 * M + 1) + 2 ^ (M + m + 3) + 3 := hnds
      _ ≤ 100 * v ^ (3 * a + H + 3) := by omega
      _ ≤ v * v ^ (3 * a + H + 3) := Nat.mul_le_mul_right _ hv100
      _ = v ^ (3 * a + H + 4) := by ring
      _ ≤ v ^ (3 * a + H + 20) := Nat.pow_le_pow_right hv1 (by omega)
  · -- the size of the program
    have h2 : c * (M + m + 1) ≤ v := by
      refine le_trans (Nat.mul_le_mul_left c hMm) (le_trans ?_ hlv)
      have : (c + 10000) * (a + H + 2) * l = c * ((a + H + 2) * l) + 10000 * ((a + H + 2) * l) := by ring
      rw [this]
      exact Nat.le_add_right _ _
    have h3 : d ≤ v ^ H := hd.trans (Nat.pow_le_pow_right hv1 (by omega))
    have h4 : v ≤ v ^ H := Nat.le_self_pow (by omega) v
    calc D.size ≤ 100 * v ^ H := by omega
      _ ≤ v * v ^ H := Nat.mul_le_mul_right _ hv100
      _ = v ^ (H + 1) := by ring
      _ ≤ v ^ (3 * a + H + 20) := Nat.pow_le_pow_right hv1 (by omega)
  · -- the length of names
    refine hht.trans ?_
    rw [← hl]
    have : (3 * a + H + 20) * l = 3 * ((a + 1) * l) + H * l + 17 * l := by ring
    omega

end Paper
theorem solution (H : ℕ) (hH : 32 ≤ H) : ∃ c : ℕ, ∀ v a, 100 ≤ v → c * (a + H + 2) * lg v ≤ v →
    ∀ (A : Type) [CommRing A] (R : Type) [CommRing R] [Algebra A R] (θ : List Bool → A) (s : ℕ)
      (p : MvPolynomial (Fin (v ^ (H - 32) + 1) × Option Bool) R), s ≤ v ^ a → Statement.Computes p s →
    ∃ (K : KT R) (D : Tree), (∀ z : Tree, z.size ≤ v ^ (H - 32) → Hl θ (Fm.ofTree D) z ∧
        (∀ r ∈ evl θ (Fm.ofTree D) z, r.cost ≤ v ^ (H - 16) ∧ ∀ q ∈ r.bill, K.InB 1 q) ∧
        val K.lk (evl θ (Fm.ofTree D) z) = ∑ i ∈ Finset.range (v ^ (H - 32) + 1 + 1),
          MvPolynomial.eval (codeB R (v ^ (H - 32) + 1) (tbits z)) (MvPolynomial.homogeneousComponent i p)) ∧
      K.nds ≤ v ^ (3 * a + H + 20) ∧ D.size ≤ v ^ (3 * a + H + 20) ∧ K.ht ≤ (3 * a + H + 20) * lg v := Paper.lem_circuit_program H hH

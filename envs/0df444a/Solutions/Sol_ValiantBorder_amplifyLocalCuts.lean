-- Prove2me | solution 1 for ValiantBorder.amplifyLocalCuts
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:06:13.017017+00:00
-- url     : https://prove2.me/submissions/343434bb-6eb3-489c-a03f-9339e6cb4b1d

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_localCuts
/-! Based on Claude (Anthropic), *VP ≠ VNP over every field*, Theorems onecut and cut,
https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp .
This arrangement refactors the single-cut hypothesis from its quantitative amplification.
The upstream Lean source is copyright 2026 Anthropic, PBC and released under Apache 2.0,
https://www.apache.org/licenses/LICENSE-2.0. -/
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
# Weighted functions computed by formulas

`Does θ F x Q c`: all runs of the formula `F` at the tree `x` stop, they use no named constants, the accepting ones
have cost at most `c`, and for every function of the value their weighted sum is that of the list `Q` of pairs
(weight, value).
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

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
# Cuts one after the other
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- A cut gives the program of the cut hypothesis. -/
theorem CutD.cutProg {H v τ s P t : ℕ} {G : Tree} (h : CutD θ τ s (v ^ H) (v ^ (H - 32)) P t G) (hG : G.size ≤ v ^ H)
    (ht : t * v ^ 24 ≤ τ) (hP : P * v ^ H ≤ τ * v ^ 2) : CutProg θ H v τ s G := by
  refine ⟨hG, fun z hz => ?_, fun z hz hp => ?_⟩
  · obtain ⟨Q, hD, hQ, -⟩ := h z hz
    refine ⟨hD.hl, fun r hr => ?_⟩
    obtain ⟨h1, h2, q, hq, h3⟩ := hD.evl.1 r hr
    obtain ⟨h4, h5⟩ := hQ q hq
    rw [← h3]
    exact ⟨h1, (Nat.mul_le_mul_right _ h2).trans ht, (Nat.mul_le_mul_right _ h4).trans hP, h5⟩
  · obtain ⟨Q, hD, hQ, hv⟩ := h z hz
    obtain ⟨h1, h2⟩ := hv hp
    refine ⟨fun r hr y hy => ?_, ?_⟩
    · obtain ⟨-, -, q, hq, h3⟩ := hD.evl.1 r hr
      rw [← h3] at hy
      exact h1 q hq y hy
    · rw [h2, ← hD.evl.2 (pvs θ)]
      rfl

/-- One more cut for every element: the argument is (element, list of pieces so far). -/
def stepC (G : Tree) : Fm := lett (.cons (app G (.hd .id)) (.tl .id)) (appF (.hd .id) (.tl .id))

/-- First `G`, then `G'` on every piece. -/
def compC (G G' : Tree) : Fm := lett (app G .id) (foldF (stepC G') (.quote .nil) .id)

theorem wsum_foldW_pvs {f : Tree → Tree → List (A × Tree)} {xs : List Tree} {Inv : List Tree → Tree → Prop}
    (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ → (∀ q ∈ f x σ, Inv ys q.2) ∧ wsum (f x σ) (pvs θ) = pv θ x * pvs θ σ)
    {σ : Tree} (hσ : Inv xs σ) : wsum (foldW f xs σ) (pvs θ) = (xs.map (pv θ)).prod * pvs θ σ := by
  induction xs generalizing σ with
  | nil => simp [foldW]
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := h x xs σ List.mem_cons_self hσ
    rw [foldW, wsum_bindW, wsum_congr (φ' := fun o => (xs.map (pv θ)).prod * pvs θ o) fun q hq =>
      ih (fun y ys σ hy => h y ys σ (List.mem_cons_of_mem _ hy)) (h1 q hq)]
    have h3 : wsum (f x σ) (fun o => (xs.map (pv θ)).prod * pvs θ o) = (xs.map (pv θ)).prod * wsum (f x σ) (pvs θ) := by
      unfold wsum
      rw [← List.sum_map_mul_left]
      congr 1
      exact List.map_congr_left fun q _ => by ring
    rw [h3, h2, List.map_cons, List.prod_cons]
    ring

theorem mem_foldW {f : Tree → Tree → List (A × Tree)} {xs : List Tree} {Inv : List Tree → Tree → Prop}
    (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ → ∀ q ∈ f x σ, Inv ys q.2) {σ : Tree} (hσ : Inv xs σ) :
    ∀ q ∈ foldW f xs σ, Inv [] q.2 := by
  induction xs generalizing σ with
  | nil =>
    intro q hq
    simp only [foldW, List.mem_singleton] at hq
    subst hq
    exact hσ
  | cons x xs ih =>
    intro q hq
    obtain ⟨q', hq', r, hr, h1, -⟩ := mem_bindW hq
    rw [h1]
    exact ih (fun y ys σ hy => h y ys σ (List.mem_cons_of_mem _ hy)) (h x xs σ List.mem_cons_self hσ q' hq') r hr

/-- **Paper: Theorem thm:cut, composition of cuts.** "Composing the programs: the next one is run on every piece in
the list ... The sum formulas compose." -/
theorem _root_.Paper.thm_cut_compose {τ s τ₁ s₁ P₁ t₁ τ₂ s₂ P₂ t₂ : ℕ} {G₁ G₂ : Tree} (h₁ : CutD θ τ s τ₁ s₁ P₁ t₁ G₁)
    (h₂ : CutD θ τ₁ s₁ τ₂ s₂ P₂ t₂ G₂) :
    CutD θ τ s τ₂ s₂ (P₁ * P₂) (t₁ + P₁ * (t₂ + 62 * P₂ + 110) + 100) (compC G₁ G₂).code := by
  intro z hz
  obtain ⟨Q₁, hD₁, hQ₁, hv₁⟩ := h₁ z hz
  choose! R hR using h₂
  -- one step
  let f : Tree → Tree → List (A × Tree) := fun x σ =>
    (R x).map fun q => (q.1, listT (q.2.toList ++ σ.toList))
  have hstep : ∀ x σ, x.size ≤ s₁ → Does θ (stepC G₂) (.cons x σ) (f x σ) (t₂ + 62 * P₂ + 70) := by
    intro x σ hx
    obtain ⟨hD, hq, -⟩ := hR x hx
    have e1 : Does θ (app G₂ (.hd .id)) (.cons x σ) (R x) (2 + t₂ + 2) := by
      have := Does.app (p := G₂) (R := fun _ => R x) (Gives.id (θ := θ) (.cons x σ)).hd (d := t₂) (by
        intro q hq
        rw [List.mem_singleton] at hq
        subst hq
        exact hD)
      simpa [bindW] using this
    have e2 := Does.cons e1 (Gives.id (θ := θ) (.cons x σ)).tl
    have e3 := Gives.after (G := appF (.hd .id) (.tl .id)) (f := fun o => listT (o.hd.toList ++ o.tl.toList))
      (d := 62 * P₂ + 50) e2 (by
      intro q hq'
      simp only [List.mem_flatMap, List.map_cons, List.map_nil, List.mem_singleton] at hq'
      obtain ⟨q1, hq1, rfl⟩ := hq'
      have h1 : Gives θ (.hd .id) (.cons q1.2 σ) (listT q1.2.toList) 2 := by
        rw [listT_toList]; exact (Gives.id _).hd
      have h2 : Gives θ (.tl .id) (.cons q1.2 σ) (listT σ.toList) 2 := by
        rw [listT_toList]; exact (Gives.id _).tl
      refine (appF_gives h1 h2).mono ?_
      have := Nat.mul_le_mul_right 62 (hq q1 hq1).1
      omega)
    refine (e3.congr ?_ fun φ => ?_).mono (by omega)
    · intro q hq'
      simp only [List.mem_map, List.mem_flatMap, List.map_cons, List.map_nil, List.mem_singleton] at hq'
      obtain ⟨q1, ⟨q2, hq2, rfl⟩, rfl⟩ := hq'
      exact ⟨_, List.mem_map.2 ⟨q2, hq2, rfl⟩, rfl⟩
    · simp only [f, wsum, List.map_map, List.map_cons, List.map_nil, mul_one, flatMap_single,
        Function.comp_def, hd_cons, tl_cons]
  -- the fold
  have hfold : ∀ q ∈ Q₁, Does θ (foldF (stepC G₂) (.quote .nil) .id) q.2 (foldW f q.2.toList .nil)
      (P₁ * (t₂ + 62 * P₂ + 100) + 30) := by
    intro q hq
    have hl : Gives θ .id q.2 (listT q.2.toList) 1 := by rw [listT_toList]; exact Gives.id _
    have := foldF_does (f := f) (Inv := fun ys _ => ∀ y ∈ ys, y.size ≤ s₁) (d := fun _ => t₂ + 62 * P₂ + 70)
      (Gives.quote (θ := θ) .nil q.2) hl (fun x ys σ _ hI => ⟨hstep x σ (hI x List.mem_cons_self), fun _ _ y hy =>
        hI y (List.mem_cons_of_mem _ hy)⟩) (hQ₁ q hq).2
    refine this.mono ?_
    rw [List.map_const', List.sum_replicate, smul_eq_mul, show t₂ + 62 * P₂ + 70 + 30 = t₂ + 62 * P₂ + 100 by omega]
    have := Nat.mul_le_mul_right (t₂ + 62 * P₂ + 100) (hQ₁ q hq).1
    omega
  have hDz : Does θ (app G₁ .id) z Q₁ (1 + t₁ + 2) := by
    have := Does.app (p := G₁) (R := fun _ => Q₁) (Gives.id (θ := θ) z) (d := t₁) (by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact hD₁)
    simpa [bindW] using this
  refine ⟨bindW Q₁ fun o => foldW f o.toList .nil, ?_, ?_, ?_⟩
  · rw [Fm.ofTree_code]
    refine (hDz.lett (R := fun o => foldW f o.toList .nil) hfold).mono ?_
    have : P₁ * (t₂ + 62 * P₂ + 100) ≤ P₁ * (t₂ + 62 * P₂ + 110) := Nat.mul_le_mul_left _ (by omega)
    omega
  · intro p hp
    obtain ⟨q, hq, r, hr, h1, -⟩ := mem_bindW hp
    rw [h1]
    have hinv : ∀ r ∈ foldW f q.2.toList .nil, (r.2.toList.length + ([] : List Tree).length * P₂ ≤ P₁ * P₂ ∧
        ∀ y ∈ r.2.toList, y.size ≤ s₂) ∧ ∀ y ∈ ([] : List Tree), y.size ≤ s₁ := by
      refine mem_foldW (f := f) (Inv := fun ys σ => (σ.toList.length + ys.length * P₂ ≤ P₁ * P₂ ∧
        ∀ y ∈ σ.toList, y.size ≤ s₂) ∧ ∀ y ∈ ys, y.size ≤ s₁) ?_ ?_
      · rintro x ys σ - ⟨⟨a1, a2⟩, a3⟩ q' hq'
        simp only [f, List.mem_map] at hq'
        obtain ⟨q2, hq2, rfl⟩ := hq'
        obtain ⟨-, b1, -⟩ := hR x (a3 x List.mem_cons_self)
        obtain ⟨b2, b3⟩ := b1 q2 hq2
        refine ⟨⟨?_, ?_⟩, fun y hy => a3 y (List.mem_cons_of_mem _ hy)⟩
        · simp only [toList_listT, List.length_append]
          simp only [List.length_cons, add_mul, one_mul] at a1
          omega
        · intro y hy
          rw [toList_listT, List.mem_append] at hy
          rcases hy with hy | hy
          · exact b3 y hy
          · exact a2 y hy
      · refine ⟨⟨?_, by simp [toList]⟩, (hQ₁ q hq).2⟩
        have := Nat.mul_le_mul_right P₂ (hQ₁ q hq).1
        simpa [toList] using this
    have := (hinv r hr).1
    simpa using this
  · intro hp
    obtain ⟨hp1, hv⟩ := hv₁ hp
    have hpiece : ∀ q ∈ Q₁, wsum (foldW f q.2.toList .nil) (pvs θ) = pvs θ q.2 := by
      intro q hq
      rw [wsum_foldW_pvs (θ := θ) (Inv := fun ys _ => ∀ y ∈ ys, y.size ≤ s₁ ∧ Plain θ τ₁ y)]
      · simp [pvs, toList]
      · intro x ys σ _ hI
        refine ⟨fun _ _ y hy => hI y (List.mem_cons_of_mem _ hy), ?_⟩
        obtain ⟨hx, hpx⟩ := hI x List.mem_cons_self
        obtain ⟨-, -, b⟩ := hR x hx
        obtain ⟨-, b2⟩ := b hpx
        rw [b2]
        simp only [f, wsum, List.map_map, Function.comp_def, pvs, toList_listT, List.map_append, List.prod_append]
        rw [← List.sum_map_mul_right]
        congr 1
        exact List.map_congr_left fun q _ => by ring
      · exact fun y hy => ⟨(hQ₁ q hq).2 y hy, hp1 q hq y hy⟩
    refine ⟨?_, ?_⟩
    · intro p hp' y hy
      obtain ⟨q, hq, r, hr, h1, -⟩ := mem_bindW hp'
      rw [h1] at hy
      have hinv : ∀ r ∈ foldW f q.2.toList .nil, (∀ y ∈ r.2.toList, Plain θ τ₂ y) ∧
          ∀ y ∈ ([] : List Tree), y.size ≤ s₁ ∧ Plain θ τ₁ y := by
        refine mem_foldW (f := f) (Inv := fun ys σ => (∀ y ∈ σ.toList, Plain θ τ₂ y) ∧
          ∀ y ∈ ys, y.size ≤ s₁ ∧ Plain θ τ₁ y) ?_ ?_
        · rintro x ys σ - ⟨a1, a2⟩ q' hq'
          simp only [f, List.mem_map] at hq'
          obtain ⟨q2, hq2, rfl⟩ := hq'
          obtain ⟨hx, hpx⟩ := a2 x List.mem_cons_self
          obtain ⟨-, -, b⟩ := hR x hx
          obtain ⟨b1, -⟩ := b hpx
          refine ⟨fun y hy => ?_, fun y hy => a2 y (List.mem_cons_of_mem _ hy)⟩
          rw [toList_listT, List.mem_append] at hy
          rcases hy with hy | hy
          · exact b1 q2 hq2 y hy
          · exact a1 y hy
        · exact ⟨by simp [toList], fun y hy => ⟨(hQ₁ q hq).2 y hy, hp1 q hq y hy⟩⟩
      exact (hinv r hr).1 y hy
    · rw [hv, wsum_bindW]
      exact wsum_congr fun q hq => (hpiece q hq).symm

theorem size_compC (G G' : Tree) : (compC G G').code.size ≤ G.size + 3 * G'.size + 3000 := by
  simp only [compC, stepC, appF, foldF, foldB, lett, app, Fm.code, Tree.size, size_num]
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
# Cuts one after the other

From one cut by any factor k ≤ v ^ 64 at the scale v, cuts down to v ^ H steps: the induction on the numbers of steps,
sizes and pieces.
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem Plain.mono {τ τ' : ℕ} {z : Tree} (h : Plain θ τ z) (hτ : τ ≤ τ') : Plain θ τ' z :=
  ⟨h.1, fun r hr => ⟨(h.2 r hr).1, (h.2 r hr).2.trans hτ⟩⟩

theorem CutD.mono {τ s τ' s' P t τ'' s'' P' t' : ℕ} {G : Tree} (h : CutD θ τ s τ' s' P t G) (h1 : τ' ≤ τ'')
    (h2 : s' ≤ s'') (h3 : P ≤ P') (h4 : t ≤ t') : CutD θ τ s τ'' s'' P' t' G := by
  intro z hz
  obtain ⟨Q, hD, hQ, hv⟩ := h z hz
  exact ⟨Q, hD.mono h4, fun q hq => ⟨(hQ q hq).1.trans h3, fun y hy => ((hQ q hq).2 y hy).trans h2⟩, fun hp =>
    ⟨fun q hq y hy => ((hv hp).1 q hq y hy).mono h1, (hv hp).2⟩⟩

section Iterate

variable {v a₀ α H Λ : ℕ}

/-- The hypothesis at one `v`. -/
def OneCutAt (θ : List Bool → A) (v a₀ α Λ : ℕ) : Prop := ∀ τ s k, v ^ a₀ ≤ τ → τ ≤ v ^ α → s ≤ τ →
  2 ≤ k → k ≤ v ^ 64 → ∃ G : Tree, G.size ≤ v ^ a₀ ∧ CutD θ τ s (τ * Λ / k)
    ((s / k + τ / v ^ 256) * Λ) (k * Λ) ((s + τ * k / v ^ 256) * Λ) G

set_option maxHeartbeats 1000000 in
/-- **Paper: Theorem thm:cut, the induction on (τ_i, s_i, P_i).** Cut by v^63 as long as the steps are many, and at last
once to v^H; sizes, pieces and time. -/
theorem _root_.Paper.thm_cut_iterate (hc : OneCutAt θ v a₀ α Λ) (hv : 1000 ≤ v) (hΛ2 : 2 ≤ Λ) (hΛv : Λ ≤ v) (hH : a₀ ≤ H) (hH' : 200 ≤ H) :
    ∀ r τ s c, v ^ H ≤ τ → τ ≤ v ^ α → τ * Λ < v ^ H * v ^ (64 + 62 * r) → s * v ^ 48 ≤ c * τ → 1 ≤ c →
      c * 4 ^ (r + 1) ≤ v → ∃ (G : Tree) (P t s' : ℕ), CutD θ τ s (v ^ H) s' P t G ∧
      P * v ^ H ≤ τ * (4 * Λ ^ 2) ^ (r + 1) ∧ t * v ^ 48 ≤ c * τ * (100 * Λ ^ 3) ^ (r + 1) ∧
      s' * v ^ 48 ≤ c * v ^ H * (8 * Λ) ^ (r + 1) ∧ G.size ≤ 4 ^ r * (v ^ a₀ + 3000) := by
  have hv1 : 1 ≤ v := by omega
  have hΛ1 : 1 ≤ Λ := by omega
  have ppos : ∀ a, 0 < v ^ a := fun a => Nat.pow_pos (by omega)
  have pmono : ∀ {a b}, a ≤ b → v ^ a ≤ v ^ b := fun h => Nat.pow_le_pow_right hv1 h
  -- the first cut to the target
  have base : ∀ τ s c, v ^ H ≤ τ → τ ≤ v ^ α → τ * Λ < v ^ H * v ^ 64 → s * v ^ 48 ≤ c * τ → 1 ≤ c → c ≤ v →
      ∃ (G : Tree) (P t s' : ℕ), CutD θ τ s (v ^ H) s' P t G ∧ P * v ^ H ≤ τ * (4 * Λ ^ 2) ∧
      t * v ^ 48 ≤ c * τ * (100 * Λ ^ 3) ∧ s' * v ^ 48 ≤ c * v ^ H * (8 * Λ) ∧ G.size ≤ v ^ a₀ := by
    intro τ s c hτ hτα hτΛ hs hc1 hcv
    obtain ⟨k, hk⟩ : ∃ k, k = τ * Λ / v ^ H + 1 := ⟨_, rfl⟩
    have hk1 : τ * Λ < k * v ^ H := by
      rw [hk]
      have := Nat.div_add_mod (τ * Λ) (v ^ H)
      have h2 := Nat.mod_lt (τ * Λ) (ppos H)
      rw [add_mul, one_mul, Nat.mul_comm (τ * Λ / v ^ H)]
      omega
    have hk2 : k ≤ v ^ 64 := by
      rw [hk]
      exact Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul (ppos H)).2 (by rw [Nat.mul_comm (v ^ 64)]; exact hτΛ))
    have hk3 : k * v ^ H ≤ τ * Λ + v ^ H := by
      rw [hk, add_mul, one_mul]
      exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
    have hk0 : 2 ≤ k := by
      rw [hk]
      have : Λ ≤ τ * Λ / v ^ H := by
        rw [Nat.le_div_iff_mul_le (ppos H), Nat.mul_comm]
        exact Nat.mul_le_mul_right _ hτ
      omega
    have hsτ : s ≤ τ := by
      have h1 : s * v ^ 48 ≤ τ * v ^ 48 := hs.trans (by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (hcv.trans (Nat.le_self_pow (by norm_num) v)))
      exact Nat.le_of_mul_le_mul_right h1 (ppos 48)
    obtain ⟨G, hG, hcut⟩ := hc τ s k ((pmono hH).trans hτ) hτα hsτ hk0 hk2
    refine ⟨G, _, _, _, hcut.mono ?_ le_rfl le_rfl le_rfl, ?_, ?_, ?_, hG⟩
    · rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
      rw [Nat.mul_comm k (v ^ H), Nat.mul_comm] at hk1
      have : v ^ H * k = k * v ^ H := Nat.mul_comm _ _
      nlinarith
    · calc k * Λ * v ^ H = k * v ^ H * Λ := by ring
        _ ≤ (τ * Λ + v ^ H) * Λ := Nat.mul_le_mul_right _ hk3
        _ ≤ (τ * Λ + τ * Λ) * Λ := Nat.mul_le_mul_right _ (Nat.add_le_add_left (hτ.trans (Nat.le_mul_of_pos_right _ hΛ1)) _)
        _ ≤ τ * (4 * Λ ^ 2) := by nlinarith [Nat.zero_le (τ * Λ ^ 2)]
    · have h1 : τ * k / v ^ 256 * v ^ 48 ≤ τ := by
        have h2 : τ * k / v ^ 256 * v ^ 256 ≤ τ * v ^ 64 :=
          (Nat.div_mul_le_self _ _).trans (Nat.mul_le_mul_left _ hk2)
        have h3 : τ * k / v ^ 256 * v ^ 48 * v ^ 208 ≤ τ * v ^ 208 := by
          calc τ * k / v ^ 256 * v ^ 48 * v ^ 208 = τ * k / v ^ 256 * v ^ 256 := by rw [Nat.mul_assoc, ← pow_add]
            _ ≤ τ * v ^ 64 := h2
            _ ≤ τ * v ^ 208 := Nat.mul_le_mul_left _ (pmono (by norm_num))
        exact Nat.le_of_mul_le_mul_right h3 (ppos 208)
      calc (s + τ * k / v ^ 256) * Λ * v ^ 48 = (s * v ^ 48 + τ * k / v ^ 256 * v ^ 48) * Λ := by ring
        _ ≤ (c * τ + c * τ) * Λ := Nat.mul_le_mul_right _ (Nat.add_le_add hs (h1.trans (Nat.le_mul_of_pos_left _ hc1)))
        _ = c * τ * (2 * Λ) := by ring
        _ ≤ c * τ * (100 * Λ ^ 3) := Nat.mul_le_mul_left _ (by
            have : Λ ≤ Λ ^ 3 := Nat.le_self_pow (by norm_num) Λ
            omega)
    · have h1 : s / k * v ^ 48 ≤ c * v ^ H := by
        have h2 : s / k * v ^ 48 * k ≤ c * v ^ H * k := by
          calc s / k * v ^ 48 * k = s / k * k * v ^ 48 := by ring
            _ ≤ s * v ^ 48 := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
            _ ≤ c * τ := hs
            _ ≤ c * (τ * Λ) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hΛ1)
            _ ≤ c * (k * v ^ H) := Nat.mul_le_mul_left _ hk1.le
            _ = c * v ^ H * k := by ring
        exact Nat.le_of_mul_le_mul_right h2 (by omega)
      have h2 : τ / v ^ 256 * v ^ 48 ≤ c * v ^ H := by
        have h3 : τ / v ^ 256 * v ^ 48 * v ^ 208 ≤ c * v ^ H * v ^ 208 := by
          calc τ / v ^ 256 * v ^ 48 * v ^ 208 = τ / v ^ 256 * v ^ 256 := by rw [Nat.mul_assoc, ← pow_add]
            _ ≤ τ := Nat.div_mul_le_self _ _
            _ ≤ τ * Λ := Nat.le_mul_of_pos_right _ hΛ1
            _ ≤ v ^ H * v ^ 64 := hτΛ.le
            _ ≤ c * v ^ H * v ^ 208 := Nat.mul_le_mul (Nat.le_mul_of_pos_left _ hc1) (pmono (by norm_num))
        exact Nat.le_of_mul_le_mul_right h3 (ppos 208)
      calc (s / k + τ / v ^ 256) * Λ * v ^ 48 = (s / k * v ^ 48 + τ / v ^ 256 * v ^ 48) * Λ := by ring
        _ ≤ (c * v ^ H + c * v ^ H) * Λ := Nat.mul_le_mul_right _ (Nat.add_le_add h1 h2)
        _ = c * v ^ H * (2 * Λ) := by ring
        _ ≤ c * v ^ H * (8 * Λ) := Nat.mul_le_mul_left _ (by omega)
  intro r
  induction r with
  | zero =>
    intro τ s c hτ hτα hτΛ hs hc1 hcv
    obtain ⟨G, P, t, s', h1, h2, h3, h4, h5⟩ := base τ s c hτ hτα (by simpa using hτΛ) hs hc1 (by omega)
    refine ⟨G, P, t, s', h1, by simpa using h2, by simpa using h3, by simpa using h4, ?_⟩
    simp only [pow_zero, one_mul]
    omega
  | succ r ih =>
    intro τ s c hτ hτα hτΛ hs hc1 hcv
    have hc4 : 4 * c * 4 ^ (r + 1) ≤ v := by
      calc 4 * c * 4 ^ (r + 1) = c * 4 ^ (r + 1 + 1) := by rw [pow_succ 4 (r + 1)]; ring
        _ ≤ v := hcv
    have h41 : 1 ≤ 4 ^ (r + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hc4v : 4 * c ≤ v := (Nat.le_mul_of_pos_right _ h41).trans hc4
    have hX1 : 1 ≤ (4 * Λ ^ 2) ^ (r + 1) := Nat.one_le_pow _ _ (by positivity)
    have hX2 : 1 ≤ (100 * Λ ^ 3) ^ (r + 1) := Nat.one_le_pow _ _ (by positivity)
    have hX3 : 1 ≤ (8 * Λ) ^ (r + 1) := Nat.one_le_pow _ _ (by positivity)
    by_cases hbase : τ * Λ < v ^ H * v ^ 64
    · obtain ⟨G, P, t, s', h1, h2, h3, h4, h5⟩ := base τ s c hτ hτα hbase hs hc1 (by omega)
      refine ⟨G, P, t, s', h1, ?_, ?_, ?_, ?_⟩
      · refine h2.trans (Nat.mul_le_mul_left _ ?_)
        rw [pow_succ (4 * Λ ^ 2) (r + 1)]
        exact Nat.le_mul_of_pos_left _ hX1
      · refine h3.trans (Nat.mul_le_mul_left _ ?_)
        rw [pow_succ (100 * Λ ^ 3) (r + 1)]
        exact Nat.le_mul_of_pos_left _ hX2
      · refine h4.trans (Nat.mul_le_mul_left _ ?_)
        rw [pow_succ (8 * Λ) (r + 1)]
        exact Nat.le_mul_of_pos_left _ hX3
      · have : 1 ≤ 4 ^ (r + 1) := h41
        calc G.size ≤ 1 * (v ^ a₀ + 3000) := by omega
          _ ≤ 4 ^ (r + 1) * (v ^ a₀ + 3000) := Nat.mul_le_mul_right _ this
    -- one cut by v ^ 63, then the rest
    push Not at hbase
    have hsτ : s ≤ τ := by
      have h1 : s * v ^ 48 ≤ τ * v ^ 48 := hs.trans (by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left _ ((by omega : c ≤ v).trans (Nat.le_self_pow (by norm_num) v)))
      exact Nat.le_of_mul_le_mul_right h1 (ppos 48)
    have hk63 : 2 ≤ v ^ 63 := (by omega : 2 ≤ v).trans (Nat.le_self_pow (by norm_num) v)
    obtain ⟨G₁, hG₁, hcut₁⟩ := hc τ s (v ^ 63) ((pmono hH).trans hτ) hτα hsτ hk63 (pmono (by norm_num))
    obtain ⟨τ₁, hτ₁⟩ : ∃ n, n = τ * Λ / v ^ 63 := ⟨_, rfl⟩
    obtain ⟨s₁, hs₁⟩ : ∃ n, n = (s / v ^ 63 + τ / v ^ 256) * Λ := ⟨_, rfl⟩
    obtain ⟨t₁, ht₁⟩ : ∃ n, n = (s + τ * v ^ 63 / v ^ 256) * Λ := ⟨_, rfl⟩
    rw [← hτ₁, ← hs₁, ← ht₁] at hcut₁
    have hτ₁le : τ₁ * v ^ 63 ≤ τ * Λ := by rw [hτ₁]; exact Nat.div_mul_le_self _ _
    have hτ₁V : v ^ H ≤ τ₁ := by
      rw [hτ₁, Nat.le_div_iff_mul_le (ppos 63)]
      exact (Nat.mul_le_mul_left _ (pmono (by norm_num))).trans hbase
    have hτ₁half : τ * Λ ≤ 2 * (τ₁ * v ^ 63) := by
      have h1 := Nat.div_add_mod (τ * Λ) (v ^ 63)
      have h2 := Nat.mod_lt (τ * Λ) (ppos 63)
      have h3 : v ^ 63 ≤ τ₁ * v ^ 63 := Nat.le_mul_of_pos_left _ (lt_of_lt_of_le (ppos H) hτ₁V)
      rw [← hτ₁, Nat.mul_comm (v ^ 63)] at h1
      omega
    have hτ₁τ : τ₁ ≤ τ := by
      have : τ₁ * v ^ 63 ≤ τ * v ^ 63 := hτ₁le.trans (Nat.mul_le_mul_left _ (hΛv.trans (Nat.le_self_pow (by norm_num) v)))
      exact Nat.le_of_mul_le_mul_right this (ppos 63)
    have hτ₁Λ : τ₁ * Λ < v ^ H * v ^ (64 + 62 * r) := by
      have h1 : τ₁ * v ^ 63 < v ^ H * v ^ (63 + 62 * r) * v ^ 63 := by
        calc τ₁ * v ^ 63 ≤ τ * Λ := hτ₁le
          _ < v ^ H * v ^ (64 + 62 * (r + 1)) := hτΛ
          _ = v ^ H * v ^ (63 + 62 * r) * v ^ 63 := by
            rw [Nat.mul_assoc, ← pow_add]
            congr 2
            ring
      have h2 : τ₁ < v ^ H * v ^ (63 + 62 * r) := lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
      calc τ₁ * Λ ≤ τ₁ * v := Nat.mul_le_mul_left _ hΛv
        _ < v ^ H * v ^ (63 + 62 * r) * v := Nat.mul_lt_mul_of_pos_right h2 (by omega)
        _ = v ^ H * v ^ (64 + 62 * r) := by
          rw [Nat.mul_assoc, ← pow_succ]
          congr 2
          ring
    have hs₁c : s₁ * v ^ 48 ≤ 4 * c * τ₁ := by
      have h1 : s₁ * v ^ 48 * v ^ 63 ≤ 4 * c * τ₁ * v ^ 63 := by
        have a1 : s / v ^ 63 * v ^ 63 * v ^ 48 ≤ c * τ := (Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)).trans hs
        have a2 : τ / v ^ 256 * v ^ 63 * v ^ 48 ≤ c * τ := by
          calc τ / v ^ 256 * v ^ 63 * v ^ 48 = τ / v ^ 256 * v ^ 111 := by rw [Nat.mul_assoc, ← pow_add]
            _ ≤ τ / v ^ 256 * v ^ 256 := Nat.mul_le_mul_left _ (pmono (by norm_num))
            _ ≤ τ := Nat.div_mul_le_self _ _
            _ ≤ c * τ := Nat.le_mul_of_pos_left _ hc1
        calc s₁ * v ^ 48 * v ^ 63 = (s / v ^ 63 * v ^ 63 * v ^ 48 + τ / v ^ 256 * v ^ 63 * v ^ 48) * Λ := by
              rw [hs₁]; ring
          _ ≤ (c * τ + c * τ) * Λ := Nat.mul_le_mul_right _ (Nat.add_le_add a1 a2)
          _ = 2 * c * (τ * Λ) := by ring
          _ ≤ 2 * c * (2 * (τ₁ * v ^ 63)) := Nat.mul_le_mul_left _ hτ₁half
          _ = 4 * c * τ₁ * v ^ 63 := by ring
      exact Nat.le_of_mul_le_mul_right h1 (ppos 63)
    obtain ⟨G₂, P₂, t₂, s₂, hcut₂, hP₂, ht₂, hs₂, hG₂⟩ := ih τ₁ s₁ (4 * c) hτ₁V (hτ₁τ.trans hτα) hτ₁Λ hs₁c (by omega) hc4
    have hP : v ^ 63 * Λ * P₂ * v ^ H ≤ τ * (4 * Λ ^ 2) ^ (r + 1 + 1) := by
      calc v ^ 63 * Λ * P₂ * v ^ H = v ^ 63 * Λ * (P₂ * v ^ H) := by ring
        _ ≤ v ^ 63 * Λ * (τ₁ * (4 * Λ ^ 2) ^ (r + 1)) := Nat.mul_le_mul_left _ hP₂
        _ = τ₁ * v ^ 63 * (Λ * (4 * Λ ^ 2) ^ (r + 1)) := by ring
        _ ≤ τ * Λ * (Λ * (4 * Λ ^ 2) ^ (r + 1)) := Nat.mul_le_mul_right _ hτ₁le
        _ = τ * (Λ ^ 2 * (4 * Λ ^ 2) ^ (r + 1)) := by ring
        _ ≤ τ * (4 * Λ ^ 2 * (4 * Λ ^ 2) ^ (r + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
        _ = τ * (4 * Λ ^ 2) ^ (r + 1 + 1) := by rw [pow_succ (4 * Λ ^ 2) (r + 1)]; ring
    refine ⟨_, _, _, _, Paper.thm_cut_compose hcut₁ hcut₂, hP, ?_, ?_, ?_⟩
    · -- time
      have b1 : t₁ * v ^ 48 ≤ c * τ * (2 * Λ) := by
        have h1 : τ * v ^ 63 / v ^ 256 * v ^ 48 ≤ τ := by
          have h2 : τ * v ^ 63 / v ^ 256 * v ^ 48 * v ^ 208 ≤ τ * v ^ 208 := by
            calc τ * v ^ 63 / v ^ 256 * v ^ 48 * v ^ 208 = τ * v ^ 63 / v ^ 256 * v ^ 256 := by
                  rw [Nat.mul_assoc, ← pow_add]
              _ ≤ τ * v ^ 63 := Nat.div_mul_le_self _ _
              _ ≤ τ * v ^ 208 := Nat.mul_le_mul_left _ (pmono (by norm_num))
          exact Nat.le_of_mul_le_mul_right h2 (ppos 208)
        calc t₁ * v ^ 48 = (s * v ^ 48 + τ * v ^ 63 / v ^ 256 * v ^ 48) * Λ := by rw [ht₁]; ring
          _ ≤ (c * τ + c * τ) * Λ := Nat.mul_le_mul_right _ (Nat.add_le_add hs (h1.trans (Nat.le_mul_of_pos_left _ hc1)))
          _ = c * τ * (2 * Λ) := by ring
      have b2 : v ^ 63 * Λ * t₂ * v ^ 48 ≤ c * τ * (4 * Λ ^ 2 * (100 * Λ ^ 3) ^ (r + 1)) := by
        calc v ^ 63 * Λ * t₂ * v ^ 48 = v ^ 63 * Λ * (t₂ * v ^ 48) := by ring
          _ ≤ v ^ 63 * Λ * (4 * c * τ₁ * (100 * Λ ^ 3) ^ (r + 1)) := Nat.mul_le_mul_left _ ht₂
          _ = τ₁ * v ^ 63 * (4 * c * Λ * (100 * Λ ^ 3) ^ (r + 1)) := by ring
          _ ≤ τ * Λ * (4 * c * Λ * (100 * Λ ^ 3) ^ (r + 1)) := Nat.mul_le_mul_right _ hτ₁le
          _ = c * τ * (4 * Λ ^ 2 * (100 * Λ ^ 3) ^ (r + 1)) := by ring
      have b3 : v ^ 63 * Λ * (62 * P₂) * v ^ 48 ≤ c * τ * (4 * Λ ^ 2) ^ (r + 1 + 1) := by
        have hv62 : 62 * v ^ 48 ≤ v ^ H := by
          calc 62 * v ^ 48 ≤ v * v ^ 48 := Nat.mul_le_mul_right _ (by omega)
            _ = v ^ 49 := by rw [← pow_succ']
            _ ≤ v ^ H := pmono (by omega)
        calc v ^ 63 * Λ * (62 * P₂) * v ^ 48 = v ^ 63 * Λ * P₂ * (62 * v ^ 48) := by ring
          _ ≤ v ^ 63 * Λ * P₂ * v ^ H := Nat.mul_le_mul_left _ hv62
          _ ≤ τ * (4 * Λ ^ 2) ^ (r + 1 + 1) := hP
          _ ≤ c * (τ * (4 * Λ ^ 2) ^ (r + 1 + 1)) := Nat.le_mul_of_pos_left _ hc1
          _ = c * τ * (4 * Λ ^ 2) ^ (r + 1 + 1) := by ring
      have b4 : v ^ 63 * Λ * 110 * v ^ 48 + 100 * v ^ 48 ≤ c * τ * 2 := by
        have h1 : v ^ 63 * Λ * 110 * v ^ 48 ≤ τ := by
          calc v ^ 63 * Λ * 110 * v ^ 48 ≤ v ^ 63 * v * v * v ^ 48 :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hΛv) (by omega))
            _ = v ^ 113 := by ring
            _ ≤ v ^ H := pmono (by omega)
            _ ≤ τ := hτ
        have h2 : 100 * v ^ 48 ≤ τ := by
          calc 100 * v ^ 48 ≤ v * v ^ 48 := Nat.mul_le_mul_right _ (by omega)
            _ = v ^ 49 := by rw [← pow_succ']
            _ ≤ v ^ H := pmono (by omega)
            _ ≤ τ := hτ
        have h3 : τ ≤ c * τ := Nat.le_mul_of_pos_left _ hc1
        omega
      have hL3 : Λ ≤ Λ ^ 3 := Nat.le_self_pow (by norm_num) Λ
      have hL2 : Λ ^ 2 ≤ Λ ^ 3 := Nat.pow_le_pow_right hΛ1 (by norm_num)
      obtain ⟨X, hX⟩ : ∃ X, X = (100 * Λ ^ 3) ^ (r + 1) := ⟨_, rfl⟩
      have c1 : 2 * Λ ≤ 2 * Λ ^ 3 * X := by
        rw [hX]
        calc 2 * Λ ≤ 2 * Λ ^ 3 * 1 := by omega
          _ ≤ _ := Nat.mul_le_mul_left _ hX2
      have c2 : 4 * Λ ^ 2 * X ≤ 4 * Λ ^ 3 * X := Nat.mul_le_mul_right _ (by omega)
      have c3 : (4 * Λ ^ 2) ^ (r + 1 + 1) ≤ 4 * Λ ^ 3 * X := by
        rw [pow_succ, hX, Nat.mul_comm]
        exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)
      have c4 : 2 ≤ 2 * Λ ^ 3 * X := by
        have : 1 ≤ Λ ^ 3 := Nat.one_le_pow _ _ hΛ1
        have hX' : 1 ≤ X := hX ▸ hX2
        calc 2 = 2 * 1 * 1 := rfl
          _ ≤ 2 * Λ ^ 3 * X := Nat.mul_le_mul (Nat.mul_le_mul_left 2 this) hX'
      have c5 : (100 * Λ ^ 3) ^ (r + 1 + 1) = 100 * Λ ^ 3 * X := by rw [pow_succ, hX]; ring
      calc (t₁ + v ^ 63 * Λ * (t₂ + 62 * P₂ + 110) + 100) * v ^ 48 = t₁ * v ^ 48 + v ^ 63 * Λ * t₂ * v ^ 48 +
            v ^ 63 * Λ * (62 * P₂) * v ^ 48 + (v ^ 63 * Λ * 110 * v ^ 48 + 100 * v ^ 48) := by ring
        _ ≤ c * τ * (2 * Λ) + c * τ * (4 * Λ ^ 2 * X) + c * τ * (4 * Λ ^ 2) ^ (r + 1 + 1) + c * τ * 2 := by
            rw [hX]
            exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add b1 b2) b3) b4
        _ = c * τ * (2 * Λ + 4 * Λ ^ 2 * X + (4 * Λ ^ 2) ^ (r + 1 + 1) + 2) := by ring
        _ ≤ c * τ * (100 * Λ ^ 3 * X) := Nat.mul_le_mul_left _ (by
            have : 2 * Λ ^ 3 * X + 4 * Λ ^ 3 * X + 4 * Λ ^ 3 * X + 2 * Λ ^ 3 * X ≤ 100 * Λ ^ 3 * X := by
              have e : 2 * Λ ^ 3 * X + 4 * Λ ^ 3 * X + 4 * Λ ^ 3 * X + 2 * Λ ^ 3 * X = 12 * (Λ ^ 3 * X) := by ring
              have e' : 100 * Λ ^ 3 * X = 100 * (Λ ^ 3 * X) := by ring
              omega
            omega)
        _ = c * τ * (100 * Λ ^ 3) ^ (r + 1 + 1) := by rw [c5]
    · calc s₂ * v ^ 48 ≤ 4 * c * v ^ H * (8 * Λ) ^ (r + 1) := hs₂
        _ = c * v ^ H * (4 * (8 * Λ) ^ (r + 1)) := by ring
        _ ≤ c * v ^ H * (8 * Λ * (8 * Λ) ^ (r + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
        _ = c * v ^ H * (8 * Λ) ^ (r + 1 + 1) := by rw [pow_succ (8 * Λ) (r + 1)]; ring
    · have := size_compC G₁ G₂
      have e : 4 ^ (r + 1) * (v ^ a₀ + 3000) = 4 * (4 ^ r * (v ^ a₀ + 3000)) := by rw [pow_succ]; ring
      have h4r : 1 ≤ 4 ^ r := Nat.one_le_pow _ _ (by norm_num)
      have : v ^ a₀ + 3000 ≤ 4 ^ r * (v ^ a₀ + 3000) := Nat.le_mul_of_pos_left _ h4r
      omega

end Iterate

theorem OneCutAt.mono {v a₀ α Λ Λ' : ℕ} (h : OneCutAt θ v a₀ α Λ) (hΛ : Λ ≤ Λ') : OneCutAt θ v a₀ α Λ' := by
  intro τ s k h1 h2 h3 h4 h5
  obtain ⟨G, hG, hcut⟩ := h τ s k h1 h2 h3 h4 h5
  exact ⟨G, hG, hcut.mono (Nat.div_le_div_right (Nat.mul_le_mul_left _ hΛ)) (Nat.mul_le_mul_left _ hΛ)
    (Nat.mul_le_mul_left _ hΛ) (Nat.mul_le_mul_left _ hΛ)⟩

/-- Powers of the logarithm that are at most `v` bound the exponent by the logarithm. -/
theorem le_lg_of_lg_pow_le {v k : ℕ} (hv : 4 ≤ v) (hk : lg v ^ k ≤ v) : k ≤ lg v := by
  have h1 : 2 ^ k < 2 ^ lg v :=
    lt_of_le_of_lt ((Nat.pow_le_pow_left (lg_ge_two hv) k).trans hk) (lt_two_pow_lg v)
  exact ((Nat.pow_lt_pow_iff_right (by norm_num)).1 h1).le

/-- The iterated cuts lose at most `v`, if `(lg v) ^ (C₀ * α) ≤ v` for the constant `C₀` below. -/
theorem polylog_loss_le {h C v α : ℕ} (hl : 100 ≤ lg v) (hα : 1 ≤ α)
    (hlog : lg v ^ ((3 * C + 4) * (32 * h + 2) * α) ≤ v) :
    (100 * (lg v ^ (C + 1)) ^ 3) ^ (16 * h * α + 1) ≤ v := by
  calc (100 * (lg v ^ (C + 1)) ^ 3) ^ (16 * h * α + 1) ≤ (lg v * (lg v ^ (C + 1)) ^ 3) ^ (16 * h * α + 1) :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hl) _
    _ = lg v ^ ((3 * C + 4) * (16 * h * α + 1)) := by
        rw [← pow_mul (lg v) (C + 1) 3, ← pow_succ', ← pow_mul]
        congr 1
        ring
    _ ≤ lg v ^ ((3 * C + 4) * (32 * h + 2) * α) := Nat.pow_le_pow_right (by omega) (by
        rw [Nat.mul_assoc (3 * C + 4) (32 * h + 2)]
        refine Nat.mul_le_mul_left _ ?_
        have : (32 * h + 2) * α = 16 * h * α + 16 * h * α + 2 * α := by ring
        omega)
    _ ≤ v := hlog

end NS1

end

open NS1
open _root_.NS1.Tree
private theorem amplify_intermediate {A : Type} [CommRing A] {θ : List Bool → A} (hc : NS1.LocalCuts θ) :
    ∃ H C₀ v₀ : ℕ, 272 ≤ H ∧ 16 ∣ H ∧ ∀ v, v₀ ≤ v → ∀ α τ s, lg v ^ (C₀ * α) ≤ v → v ^ H ≤ τ → τ ≤ v ^ (H * α) →
      s * v ^ 48 ≤ τ → ∃ G : Tree, G.size ≤ v ^ H ∧
        CutD θ τ s (v ^ H) (v ^ (H - 32)) (τ * v ^ 2 / v ^ H) (τ / v ^ 24) G := by
  obtain ⟨a₀, C, v₀, hv₀⟩ := hc
  obtain ⟨h, hhdef⟩ : ∃ h, h = a₀ + 217 := ⟨_, rfl⟩
  have hh : a₀ + 200 ≤ 16 * h := by omega
  refine ⟨16 * h, (3 * C + 4) * (32 * h + 2), v₀ + 2 ^ 100 + 4000, by omega, dvd_mul_right 16 h,
    fun v hv α τ s hlog hτ hτα hs => ?_⟩
  obtain ⟨r, hr⟩ : ∃ r, r = 16 * h * α := ⟨_, rfl⟩
  have hv1 : 4000 ≤ v := by omega
  have hv0 : 1 ≤ v := by omega
  have hl100 : 100 ≤ lg v := (Nat.le_succ _).trans (le_lg_of_two_pow_le (by omega))
  have hα : 1 ≤ α := by
    by_contra hne
    have h0 : α = 0 := by omega
    rw [h0, Nat.mul_zero, pow_zero] at hτα
    have : v ≤ v ^ (16 * h) := Nat.le_self_pow (by omega) v
    omega
  have hαl : 2 * r ≤ lg v := by
    refine le_trans ?_ (le_lg_of_lg_pow_le (by omega) hlog)
    rw [hr, Nat.mul_assoc (3 * C + 4), ← Nat.mul_assoc 2]
    refine le_trans (Nat.mul_le_mul_right _ (?_ : 2 * (16 * h) ≤ 32 * h + 2)) (Nat.le_mul_of_pos_left _ (by omega))
    omega
  obtain ⟨q4, hq4⟩ : ∃ n, n = 4 ^ (r + 1) := ⟨_, rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ n, n = lg v ^ (C + 1) := ⟨_, rfl⟩
  have hl2 := lg_ge_two (show 4 ≤ v by omega)
  have hΛ2 : 2 ≤ Λ := by
    rw [hΛ]
    exact hl2.trans (Nat.le_self_pow (by omega) _)
  have hΛ1 : 1 ≤ Λ := by omega
  have hX : (100 * Λ ^ 3) ^ (r + 1) ≤ v := hΛ ▸ hr ▸ polylog_loss_le hl100 hα hlog
  have hq4v : q4 ≤ v := by
    refine hq4 ▸ le_trans (Nat.pow_le_pow_left ?_ _) hX
    exact le_trans (by norm_num) (Nat.le_mul_of_pos_right 100 (Nat.pow_pos (show 0 < Λ by omega)))
  have hX1 : 100 * Λ ^ 3 ≤ v := (Nat.le_self_pow (by omega) _).trans hX
  have hL3 : Λ ≤ Λ ^ 3 := Nat.le_self_pow (by norm_num) Λ
  have hL2 : Λ ^ 2 ≤ Λ ^ 3 := Nat.pow_le_pow_right hΛ1 (by norm_num)
  have hat0 : OneCutAt θ v a₀ (16 * h * α) (lg v ^ C) := by
    intro τ' s' k' h1 h2 h3' h4 h5
    refine hv₀ v (by omega) τ' s' k' h1 ?_ h3' h4 h5
    have h6 : lg τ' ≤ 16 * h * α * lg v := (lg_mono h2).trans (lg_pow_le (Nat.mul_pos (by omega) hα))
    have h7 : 4 * (16 * h * α) ≤ lg v := by
      refine le_trans ?_ (le_lg_of_lg_pow_le (by omega) hlog)
      have h8 : 4 * (16 * h) * α ≤ (3 * C + 4) * (32 * h + 2) * α := by
        refine Nat.mul_le_mul_right _ ?_
        calc 4 * (16 * h) ≤ 4 * (32 * h + 2) := by omega
          _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
      calc 4 * (16 * h * α) = 4 * (16 * h) * α := by ring
        _ ≤ _ := h8
    calc 4 * lg τ' ≤ 4 * (16 * h * α * lg v) := Nat.mul_le_mul_left _ h6
      _ = 4 * (16 * h * α) * lg v := by ring
      _ ≤ lg v * lg v := Nat.mul_le_mul_right _ h7
      _ = lg v ^ 2 := by ring
  have hat : OneCutAt θ v a₀ (16 * h * α) Λ := OneCutAt.mono (Λ := lg v ^ C) hat0 (by
    rw [hΛ]
    exact Nat.pow_le_pow_right (by omega) (Nat.le_succ C))
  have pmono : ∀ {a b}, a ≤ b → v ^ a ≤ v ^ b := fun h => Nat.pow_le_pow_right hv0 h
  have ppos : ∀ a, 0 < v ^ a := fun a => Nat.pow_pos (by omega)
  obtain ⟨G, P, t, s', hcut, hP, ht, hs', hG⟩ := Paper.thm_cut_iterate hat (by omega) hΛ2 (by omega) (H := 16 * h) (by omega) (by omega)
    r τ s 1 hτ hτα (by
      calc τ * Λ < τ * v := Nat.mul_lt_mul_of_pos_left (by omega) (lt_of_lt_of_le (ppos _) hτ)
        _ ≤ v ^ (16 * h * α) * v := Nat.mul_le_mul_right _ hτα
        _ = v ^ (r + 1) := by rw [hr, pow_succ]
        _ ≤ v ^ (16 * h + (64 + 62 * r)) := pmono (by omega)
        _ = _ := pow_add _ _ _) (by simpa using hs) le_rfl (by rw [one_mul, ← hq4]; omega)
  have e8 : (8 * Λ) ^ (r + 1) ≤ v := (Nat.pow_le_pow_left (by omega) _).trans hX
  have e4 : (4 * Λ ^ 2) ^ (r + 1) ≤ v := (Nat.pow_le_pow_left (by omega) _).trans hX
  refine ⟨G, ?_, hcut.mono le_rfl ?_ ((Nat.le_div_iff_mul_le (ppos _)).2 ?_) ((Nat.le_div_iff_mul_le (ppos _)).2 ?_)⟩
  · have hq : 4 ^ r ≤ v := (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ r)).trans (by rw [← hq4]; omega)
    calc G.size ≤ 4 ^ r * (v ^ a₀ + 3000) := hG
      _ ≤ v * (v ^ a₀ + v) := Nat.mul_le_mul hq (by omega)
      _ ≤ v * (v ^ (a₀ + 1) + v ^ (a₀ + 1)) := Nat.mul_le_mul_left _ (Nat.add_le_add (pmono (Nat.le_succ _)) (by
          calc v = v ^ 1 := (pow_one v).symm
            _ ≤ _ := pmono (by omega)))
      _ = 2 * v ^ (a₀ + 2) := by rw [pow_succ v (a₀ + 1)]; ring
      _ ≤ v * v ^ (a₀ + 2) := Nat.mul_le_mul_right _ (by omega)
      _ = v ^ (a₀ + 3) := by rw [pow_succ v (a₀ + 2)]; ring
      _ ≤ v ^ (16 * h) := pmono (by omega)
  · have h1 : s' * v ^ 48 ≤ v ^ (16 * h - 32) * v ^ 48 := by
      calc s' * v ^ 48 ≤ 1 * v ^ (16 * h) * (8 * Λ) ^ (r + 1) := hs'
        _ ≤ 1 * v ^ (16 * h) * v := Nat.mul_le_mul_left _ e8
        _ = v ^ (16 * h + 1) := by rw [one_mul, pow_succ]
        _ ≤ v ^ (16 * h - 32 + 48) := pmono (by omega)
        _ = _ := pow_add _ _ _
    exact Nat.le_of_mul_le_mul_right h1 (ppos 48)
  · calc P * v ^ (16 * h) ≤ τ * (4 * Λ ^ 2) ^ (r + 1) := hP
      _ ≤ τ * v := Nat.mul_le_mul_left _ e4
      _ ≤ τ * v ^ 2 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) v)

  · have h1 : t * v ^ 24 * v ^ 24 ≤ τ * v ^ 24 := by
      calc t * v ^ 24 * v ^ 24 = t * v ^ 48 := by rw [Nat.mul_assoc, ← pow_add]
        _ ≤ 1 * τ * (100 * Λ ^ 3) ^ (r + 1) := ht
        _ ≤ τ * v := by rw [one_mul]; exact Nat.mul_le_mul_left _ hX
        _ ≤ τ * v ^ 24 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) v)
    exact Nat.le_of_mul_le_mul_right h1 (ppos 24)

theorem solution {A : Type} [CommRing A] {θ : List Bool → A} (hc : NS1.LocalCuts θ) :
    ∃ h C₀ v₀ : ℕ, 17 ≤ h ∧ NS1.CutHyp θ (16 * h) C₀ v₀ := by
  obtain ⟨H, C₀, v₀, hH, ⟨h, rfl⟩, hcut⟩ := amplify_intermediate hc
  refine ⟨h, C₀, v₀ + 1, by omega, fun v hv α τ s hl h1 h2 h4 => ?_⟩
  obtain ⟨G, hsize, hG⟩ := hcut v (by omega) α τ s hl h1 h2 h4
  have hp : ∀ a, 0 < v ^ a := fun a => Nat.pow_pos (by omega)
  exact ⟨G, hG.cutProg hsize ((Nat.le_div_iff_mul_le (hp _)).1 le_rfl) ((Nat.le_div_iff_mul_le (hp _)).1 le_rfl)⟩


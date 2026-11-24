-- Prove2me | solution 1 for ValiantBorder.lawsToLocalCuts
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:32:25.416795+00:00
-- url     : https://prove2.me/submissions/25749741-76de-4150-b8f3-ef0b00985bf7

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Theorems.Thm_ValiantBorder_weightedGroupEvaluator
import Theorems.Thm_ValiantBorder_universalAutomaton
import Theorems.Thm_ValiantBorder_lawTapePieces
import Definitions.Def_ValiantBorder_localCuts
/-! Based on Claude (Anthropic), *VP ≠ VNP over every field*, Theorems onecut and cut,
https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp .
This arrangement refactors the single-cut hypothesis from its quantitative amplification.
The upstream Lean source is copyright 2026 Anthropic, PBC and released under Apache 2.0,
https://www.apache.org/licenses/LICENSE-2.0. -/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
/- Source module NS1.Machine. -/
section
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


def Dt (θ : List Bool → A) (F : Fm) (x o : Tree) (k : ℕ) : Prop := Ev θ F x [.det k o]

theorem Dt.quote (c x : Tree) : Dt θ (.quote c) x c 1 := Ev.quote c x

theorem Dt.id (x : Tree) : Dt θ .id x x 1 := Ev.id x

theorem Dt.hd {a : Fm} {x o : Tree} {k : ℕ} (h : Dt θ a x o k) : Dt θ (.hd a) x o.hd (k + 1) := Ev.hd h

theorem Dt.tl {a : Fm} {x o : Tree} {k : ℕ} (h : Dt θ a x o k) : Dt θ (.tl a) x o.tl (k + 1) := Ev.tl h

theorem Dt.cons {a b : Fm} {x o p : Tree} {k j : ℕ} (ha : Dt θ a x o k) (hb : Dt θ b x p j) :
    Dt θ (.cons a b) x (.cons o p) (k + j + 1) := by
  have := Ev.cons ha hb
  simpa [Dt, Run.det, Run.seq, Run.tick] using this


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
/- Source module NS1.Budget. -/
section
namespace NS1


inductive Bt where
  
  | none
  
  | leaf (w : List Bool)
  
  | node (l r : Bt)


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


def dec : List Bool → Bt → Option Bt
  | _, none => Option.none
  | [], leaf w => (decw w).map leaf
  | _ :: _, leaf _ => Option.none
  | [], node _ _ => Option.none
  | true :: p, node l r => (dec p r).map (node l)
  | false :: p, node l r => (dec p l).map fun l' => node l' r


def decAll : List (List Bool) → Bt → Option Bt
  | [], t => some t
  | p :: b, t => (dec p t).bind (decAll b)


def zero : Bt → Bool
  | none => true
  | leaf w => w.all (! ·)
  | node l r => l.zero && r.zero


def ht : Bt → ℕ
  | none => 0
  | leaf w => w.length + 1
  | node l r => max l.ht r.ht + 1


def nds : Bt → ℕ
  | none => 1
  | leaf w => w.length + 1
  | node l r => l.nds + r.nds + 1


def enc : Bt → Tree
  | none => .nil
  | leaf w => .cons .nil (.ofBits w)
  | node l r => .cons (.cons l.enc r.enc) .nil













end Bt

end NS1
end
/- Source module NS1.Interp. -/
section
namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem Dt.ite_true {a b c : Fm} {x o p : Tree} {k j : ℕ} (ha : Dt θ a x o k) (ho : o ≠ .nil) (hb : Dt θ b x p j) :
    Dt θ (.ite a b c) x p (k + 1 + j) := Ev.ite_true (c := c) ha ho hb

theorem Dt.ite_false {a b c : Fm} {x p : Tree} {k j : ℕ} (ha : Dt θ a x .nil k) (hc : Dt θ c x p j) :
    Dt θ (.ite a b c) x p (k + 1 + j) := Ev.ite_false (b := b) ha hc

theorem Dt.run {a b : Fm} {x p d o : Tree} {k j i : ℕ} (ha : Dt θ a x p k) (hb : Dt θ b x d j)
    (h : Dt θ (Fm.ofTree p) d o i) : Dt θ (.run a b) x o (k + j + 1 + i) := Ev.run_det ha hb h











section Programs


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






def AW : Fm := .ite (.tl .id)
  (.ite (.hd (.tl .id)) .fail (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) (.quote .nil)




def AZ : Fm := .ite (.tl .id)
  (.ite (.hd (.tl .id))
    (.cons (.run (.hd .id) (.cons (.hd .id) (.hd (.hd (.tl .id)))))
      (.run (.hd .id) (.cons (.hd .id) (.tl (.hd (.tl .id))))))
    (.run (.quote AW.code) (.cons (.quote AW.code) (.tl (.tl .id)))))
  (.quote .nil)



end Programs

end NS1
end
/- Source module NS1.Eval. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

section Rel

variable {α β γ δ : Type*}








end Rel

section Cases


def selF : List Fm → Fm → Fm
  | [], _ => .fail
  | c :: cs, b => .ite b (selF cs (.tl b)) c



end Cases

section Code


def fF (b : Fm) : Fm := .hd (.tl b)

def fX (b : Fm) : Fm := .hd (.tl (.tl b))

def fS (b : Fm) : Fm := .tl (.tl (.tl b))

def fO (b : Fm) : Fm := .hd (fF b)

def fA (b : Fm) : Fm := .tl (fF b)

def rec' (b a x s : Fm) : Fm := .run (.hd b) (.cons (.hd b) (.cons a (.cons x s)))


def call1 : Fm := .cons .id (rec' .id (.hd (fA .id)) (fX .id) (fS .id))


def call2 : Fm := .cons .id (rec' (.hd .id) (.tl (fA (.hd .id))) (fX (.hd .id)) (.tl (.tl .id)))


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


def IF : Fm := selF caseL (fO .id)


def env (f x : Tree) (t : Bt) : Tree := .cons IF.code (.cons f (.cons x t.enc))

theorem Dt.fX {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fX b) y x (k + 3) :=
  .hd (.tl (.tl h))

theorem Dt.fS {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fS b) y t.enc (k + 3) :=
  .tl (.tl (.tl h))

theorem Dt.fO {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fO b) y f.hd (k + 3) :=
  .hd (.hd (.tl h))

theorem Dt.fA {b : Fm} {y f x : Tree} {t : Bt} {k : ℕ} (h : Dt θ b y (env f x t) k) : Dt θ (fA b) y f.tl (k + 3) :=
  .tl (.hd (.tl h))





def simS (t : Bt) (l : List (Run A)) : List (Run A × Bt) :=
  l.filterMap fun r => (Bt.decAll r.bill t).map fun t' => (r, t')









end Code

end NS1
end
/- Source module NS1.EvalThm. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}






structure RelJ (M j : ℕ) (r : Run A) (q : Run A × Bt) : Prop where
  th : r.th = q.1.th
  bill : r.bill = []
  out : r.out = .cons q.1.out q.2.enc
  cost : r.cost + j ≤ M * q.1.cost


def MM (H : ℕ) : ℕ := 1000 + 100 * H










theorem flatMap_single {α β : Type*} (l : List α) (g : α → β) : (l.flatMap fun a => [g a]) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]




end NS1
end
/- Source module NS1.Postpone. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R]

namespace KT

def lookup : KT R → List Bool → R
  | none, _ => 0
  | leaf c, [] => c
  | leaf _, _ :: _ => 0
  | node _ _, [] => 0
  | node _ r, true :: p => r.lookup p
  | node l _, false :: p => l.lookup p


def words : ℕ → List (List Bool)
  | 0 => [[]]
  | J + 1 => [false, true].flatMap fun b => (words J).map (b :: ·)


def val : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 1 else 0) + 2 * val w


def budg (J : ℕ) : KT R → List (Bt × R)
  | none => [(.none, 1)]
  | leaf c => (words J).map fun w => (.leaf w, c ^ val w)
  | node l r => (l.budg J).flatMap fun p => (r.budg J).map fun q => (.node p.1 q.1, p.2 * q.2)

end KT


def ok (t : Bt) (b : List (List Bool)) : Bool := ((Bt.decAll b t).map Bt.zero).getD false







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




def part (a : Bool) (b : List (List Bool)) : List (List Bool) := b.filterMap fun p => match p with
  | [] => none
  | c :: p => if c = a then some p else none











theorem sum_flatMap_map {α β : Type*} (l : List α) (f : α → List β) (g : β → R) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]









def WF : Fm := lett (.cons (.quote AZ.code) (.tl (lett (.cons (.quote IF.code) .id) IF))) AZ










variable [Algebra A R]





end NS1
end
/- Source module NS1.Guess. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R]

namespace KT


def comb (c : R) : ℕ → KT R
  | 0 => none
  | n + 1 => node (leaf c) (comb (c ^ 2) n)


def expand (B : ℕ) : KT R → KT R
  | none => none
  | leaf c => comb c B
  | node l r => node (l.expand B) (r.expand B)


def Leaf : KT R → List Bool → Prop
  | none, _ => False
  | leaf _, p => p = []
  | node _ _, [] => False
  | node _ r, true :: p => r.Leaf p
  | node l _, false :: p => l.Leaf p



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

















end KT

section Formulas


def gbit (p : List Bool) : Fm := .ite .guess (.cons (.mul (.quote (ofBits p))) (.quote .nil)) (.quote .nil)





def gw (ν : ℕ → ℕ) (pre : List Bool) (b : ℕ) : ℕ → ℕ → Fm
  | _, 0 => .quote .nil
  | j, n + 1 => .cons (gbit (pre ++ KT.pw (ν (b + j)))) (gw ν pre b (j + 1) n)


def gcomb (ν : ℕ → ℕ) (J : ℕ) (pre : List Bool) : ℕ → ℕ → Fm
  | _, 0 => .quote .nil
  | b, n + 1 => .cons (.cons (.cons (.quote .nil) (gw ν pre b 0 J)) (gcomb ν J pre (b + 1) n)) (.quote .nil)


def gt (ν : ℕ → ℕ) (J B : ℕ) : KT R → List Bool → Fm
  | .none, _ => .quote .nil
  | .leaf _, pre => gcomb ν J pre 0 B
  | .node l r, pre => .cons (.cons (gt ν J B l (pre ++ [false])) (gt ν J B r (pre ++ [true]))) (.quote .nil)


structure RelG (κ : List Bool → R) (P : List Bool → Prop) (c : ℕ) (r : Run A) (q : Bt × R) : Prop where
  th : r.th = 1
  out : r.out = q.1.enc
  bill : (r.bill.map κ).prod = q.2
  names : ∀ p ∈ r.bill, P p
  cost : r.cost ≤ c

variable {κ : List Bool → R} {P : List Bool → Prop} {ν : ℕ → ℕ}










end Formulas

section Sizes

theorem size_num (k : ℕ) : (num k).size = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [num, Tree.size, ih]; omega







end Sizes

end NS1
end
/- Source module NS1.Step. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R] {κ : List Bool → R}

section Values










def sumF (κ : List Bool → R) (l : List (Run A)) (f : Tree → R) : R := (l.map fun r => wt κ r * f r.out).sum







end Values

section App


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


def LP (D : Tree) : Fm := .ite (.tl .id)
  (.cons (.run (.quote D) (.hd (.tl .id))) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) (.quote .nil)



end Loop

section Inst


def zq (p z : Tree) (t : Bt) : Tree := .cons WF.code (.cons p (.cons z t.enc))


def ZE (fp g : Fm) : Fm := .cons (.quote WF.code) (.cons fp (.cons .id g))




def stepF (D G p : Tree) (g : Fm) : Fm :=
  app (LP D).code (.cons (.quote (LP D).code) (app G (ZE (.quote p) g)))



end Inst

end NS1
end
/- Source module NS1.Accel. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {R : Type} [CommRing R] [Algebra A R]



structure IsAccT (θ : List Bool → A) (H v t : ℕ) (K : KT R) (B : ℕ) (D : Tree) : Prop where
  run : ∀ z, z.size ≤ v ^ (H - 32) → Hl θ (Fm.ofTree D) z ∧ ∀ r ∈ evl θ (Fm.ofTree D) z, r.cost ≤ t ∧
    ∀ p ∈ r.bill, K.InB B p
  val : ∀ z, z.size ≤ v ^ (H - 32) → Plain θ (v ^ H) z →
    val K.lk (evl θ (Fm.ofTree D) z) = algebraMap A R (pv θ z)


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





def UF : Fm := .run (.hd .id) (.tl .id)











end NS1
end
/- Source module NS1.Comp. -/
section
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


def Gives (θ : List Bool → A) (F : Fm) (x o : Tree) (c : ℕ) : Prop := Does θ F x [(1, o)] c

namespace Does

variable {F G H : Fm} {x : Tree} {Q : List (A × Tree)} {c d : ℕ}

theorem mono (h : Does θ F x Q c) (hc : c ≤ d) : Does θ F x Q d := by
  obtain ⟨l, h1, h2, h3⟩ := h
  exact ⟨l, h1, fun r hr => ⟨(h2 r hr).1, (h2 r hr).2.1.trans hc, (h2 r hr).2.2⟩, h3⟩


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




theorem of_dt {o : Tree} (h : Dt θ F x o c) : Does θ F x [(1, o)] c := by
  refine ⟨_, h, ?_, fun φ => ?_⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨rfl, le_rfl, (1, o), List.mem_singleton_self _, rfl⟩
  · simp [Run.det]


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


theorem lett {R : Tree → List (A × Tree)} (hF : Does θ F x Q c) (hG : ∀ q ∈ Q, Does θ G q.2 (R q.2) d) :
    Does θ (lett F G) x (bindW Q R) (c + d + 2) :=
  app (p := G.code) hF (by rw [Fm.ofTree_code]; exact hG)


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


theorem after {Q : List (A × Tree)} (h : Does θ F x Q c) {f : Tree → Tree} (h' : ∀ q ∈ Q, Gives θ G q.2 (f q.2) d) :
    Does θ (NS1.lett F G) x (Q.map fun q => (q.1, f q.2)) (c + d + 2) := by
  have := h.lett (R := fun o => [(1, f o)]) h'
  simpa [bindW, flatMap_single] using this

end Gives


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
/- Source module NS1.Lists. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}




@[simp] theorem toList_listT (xs : List Tree) : (listT xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listT, toList, ih]

theorem listT_toList (x : Tree) : listT x.toList = x := by
  induction x with
  | nil => rfl
  | cons a b _ ih => simp [listT, toList, ih]




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



def foldB (step : Fm) : Fm := .ite (.tl (.tl .id))
  (.run (.hd .id) (.cons (.hd .id) (.cons (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) step)
    (.tl (.tl (.tl .id)))))) (.hd (.tl .id))


def foldF (step s l : Fm) : Fm := app (foldB step).code (.cons (.quote (foldB step).code) (.cons s l))


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



def mapB (step : Fm) : Fm := .ite (.tl (.tl .id))
  (.cons (lett (.cons (.hd (.tl .id)) (.hd (.tl (.tl .id)))) step)
    (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.tl .id)) (.tl (.tl (.tl .id))))))) (.quote .nil)


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


def eqB : Fm := .ite (.hd (.tl .id))
  (.ite (.tl (.tl .id))
    (.ite (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.hd (.tl .id))) (.hd (.tl (.tl .id))))))
      (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.tl (.tl (.tl .id))))))
      (.quote .nil))
    (.quote .nil))
  (.ite (.tl (.tl .id)) (.quote .nil) (.quote one))


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


def pickB : Fm := .ite (.tl .id)
  (.ite .guess (.hd (.tl .id)) (.run (.hd .id) (.cons (.hd .id) (.tl (.tl .id))))) .fail


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


def tget : List Bool → Tree → Tree
  | [], t => t.hd
  | true :: p, t => tget p t.tl.tl
  | false :: p, t => tget p t.tl.hd


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


def getB : Fm := .ite (.hd (.tl .id))
  (.ite (.hd (.hd (.tl .id)))
    (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.tl (.tl (.tl (.tl .id)))))))
    (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.hd (.tl (.tl (.tl .id))))))))
  (.hd (.tl (.tl .id)))


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








def WE.fm : WE → Fm
  | zero => .fail
  | one => .quote .nil
  | nm p => .theta (.quote (ofBits p))
  | add a b => .ite .guess a.fm b.fm
  | mul a b => lett a.fm (lett b.fm (.quote .nil))


def WE.cost : WE → ℕ
  | zero => 1
  | one => 1
  | nm _ => 2
  | add a b => max a.cost b.cost + 2
  | mul a b => a.cost + b.cost + 10





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
/- Source module Nc.Dl.Last. -/
section
namespace Nc.Dl
open NS1 NS1.Tree
theorem exists_theta (A : Type) [CommRing A] [Algebra.FiniteType ℤ A] :
    ∃ θ : List Bool → A, (Function.support θ).Finite ∧ ∀ a, ∃ w : WE, w.val θ = a := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType ℤ A).out
  let gens : List A := (-1) :: s.toList
  let θ : List Bool → A := fun p => if p = List.replicate p.length true then gens.getD p.length 0 else 0
  have hθ : ∀ k, θ (List.replicate k true) = gens.getD k 0 := by
    intro k
    simp [θ]
  refine ⟨θ, ?_, fun a => ?_⟩
  · refine ((Set.finite_lt_nat gens.length).image fun k => List.replicate k true).subset ?_
    intro p hp
    rw [Function.mem_support] at hp
    by_cases h : p = List.replicate p.length true
    · refine ⟨p.length, ?_, h.symm⟩
      show p.length < gens.length
      by_contra hlt
      apply hp
      simp only [θ]
      rw [if_pos h, List.getD_eq_default _ _ (not_lt.1 hlt)]
    · exact absurd (if_neg h) hp
  · refine WE.exists_of_adjoin (p₀ := []) ?_ ?_
    · have := hθ 0
      simpa [gens] using this
    · have h1 : (s : Set A) ⊆ Set.range θ := by
        intro x hx
        have hx' : x ∈ gens := List.mem_cons_of_mem _ (Finset.mem_toList.2 hx)
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx'
        refine ⟨List.replicate k true, ?_⟩
        rw [hθ, List.getD_eq_getElem _ _ hk]
      have h2 : a ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; exact Algebra.mem_top
      rw [Algebra.adjoin_int] at h2
      exact Subring.closure_mono h1 h2



end Nc.Dl
end
/- Source module NS1.Util. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

section Word


def wordT (t0 t1 : Tree) : Tree → List Tree
  | .nil => [t0]
  | .cons a b => t1 :: (wordT t0 t1 a ++ wordT t0 t1 b)

theorem length_wordT (t0 t1 z : Tree) : (wordT t0 t1 z).length = z.size := by
  induction z with
  | nil => rfl
  | cons a b iha ihb =>
    simp only [wordT, List.length_cons, List.length_append, iha, ihb, Tree.size]


def wordB (t0 t1 : Tree) : Fm := .ite (.hd (.tl .id))
  (.cons (.quote t1) (.run (.hd .id) (.cons (.hd .id) (.cons (.hd (.hd (.tl .id)))
    (.run (.hd .id) (.cons (.hd .id) (.cons (.tl (.hd (.tl .id))) (.tl (.tl .id)))))))))
  (.cons (.quote t0) (.tl (.tl .id)))


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
/- Source module NS1.Deal. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

section Assign


def RepW (W : Tree) (σ : List Bool → Tree) : Prop := ∀ p, tget p W = σ p

theorem RepW.set {W : Tree} {σ : List Bool → Tree} (h : RepW W σ) (p : List Bool) (v : Tree) :
    RepW (tset p v W) (Function.update σ p v) := by
  intro q
  rw [tget_tset, Function.update_apply, h q]


def assignT (W : Tree) (o : Tree) : Tree := o.toList.foldl (fun W x => tset x.hd.path x.tl W) W


def assignS (σ : List Bool → Tree) (o : Tree) : List Bool → Tree :=
  o.toList.foldl (fun σ x => Function.update σ x.hd.path x.tl) σ

theorem RepW.assign {W : Tree} {σ : List Bool → Tree} (h : RepW W σ) (o : Tree) : RepW (assignT W o) (assignS σ o) := by
  unfold assignT assignS
  generalize o.toList = l
  induction l generalizing W σ with
  | nil => exact h
  | cons x l ih => exact ih (h.set _ _)


def assignF (o w : Fm) : Fm := foldF (setF (.hd (.hd .id)) (.tl (.hd .id)) (.tl .id)) w o

theorem assignF_gives {of wf : Fm} {x o W : Tree} {co cw : ℕ} (ho : Gives θ of x o co) (hw : Gives θ wf x W cw) :
    Gives θ (assignF of wf) x (assignT W o) (co + cw + (o.toList.map fun y => 60 * y.hd.len + 80).sum + 20) := by
  have ho' : Gives θ of x (listT o.toList) co := by rw [listT_toList]; exact ho
  have := foldF_gives (step := setF (.hd (.hd .id)) (.tl (.hd .id)) (.tl .id)) (g := fun y W => tset y.hd.path y.tl W)
    (Inv := fun _ _ => True) (d := fun y => 60 * y.hd.len + 50) hw ho' (fun y _ W _ _ =>
      ⟨(setF_gives (Gives.id _).hd.hd (Gives.id _).hd.tl (Gives.id _).tl).mono (by simp only [hd_cons]; omega), trivial⟩)
    trivial
  refine this.mono ?_
  have e : (o.toList.map fun y => 60 * y.hd.len + 50 + 30).sum = (o.toList.map fun y => 60 * y.hd.len + 80).sum := by
    congr 1
  omega

end Assign

section Bits


def allBits : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBits n).map (true :: ·) ++ (allBits n).map (false :: ·)


def bitsB : Fm := .ite (app nzB.code (.cons (.quote nzB.code) (.hd (.tl .id))))
  (.ite .guess
    (.run (.hd .id) (.cons (.hd .id) (.cons (app DW.code (.cons (.quote DW.code) (.hd (.tl .id))))
      (.cons (.quote one) (.tl (.tl .id))))))
    (.run (.hd .id) (.cons (.hd .id) (.cons (app DW.code (.cons (.quote DW.code) (.hd (.tl .id))))
      (.cons (.quote .nil) (.tl (.tl .id)))))))
  (.tl (.tl .id))

theorem bitsB_does (n : ℕ) : ∀ (w : List Bool) (acc : List Bool), KT.val w = n →
    ∃ Q, Does θ bitsB (.cons bitsB.code (.cons (ofBits w) (ofBits acc))) Q ((n + 1) * (60 * w.length + 100)) ∧
      (∀ q ∈ Q, ∃ u ∈ allBits n, q.2 = ofBits (u.reverse ++ acc)) ∧
      ∀ φ : Tree → A, wsum Q φ = ((allBits n).map fun u => φ (ofBits (u.reverse ++ acc))).sum := by
  induction n with
  | zero =>
    intro w acc hw
    have hnz := Gives.app (p := nzB.code) (Gives.cons (Gives.quote (θ := θ) nzB.code
      (.cons bitsB.code (.cons (ofBits w) (ofBits acc)))) (Gives.id _).tl.hd)
      (o' := bit (decide (KT.val w ≠ 0))) (d := 20 * w.length + 10) (by rw [Fm.ofTree_code]; exact nzB_gives w)
    have e : bit (decide (KT.val w ≠ 0)) = .nil := by simp [hw, bit]
    rw [e] at hnz
    refine ⟨_, (Does.ite_false hnz (Gives.id _).tl.tl).mono (by omega), ?_, ?_⟩
    · intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact ⟨[], by simp [allBits], rfl⟩
    · intro φ
      simp [allBits]
  | succ n ih =>
    intro w acc hw
    have hnz := Gives.app (p := nzB.code) (Gives.cons (Gives.quote (θ := θ) nzB.code
      (.cons bitsB.code (.cons (ofBits w) (ofBits acc)))) (Gives.id _).tl.hd)
      (o' := bit (decide (KT.val w ≠ 0))) (d := 20 * w.length + 10) (by rw [Fm.ofTree_code]; exact nzB_gives w)
    have e : bit (decide (KT.val w ≠ 0)) ≠ .nil := by
      have : KT.val w ≠ 0 := by omega
      simp [this, bit, one]
    rcases decw_val w with ⟨h1, h2⟩ | ⟨w', h1, h2⟩
    · omega
    obtain ⟨k, hk, hdw⟩ := DW_some (θ := θ) h1
    have hd : Gives θ (app DW.code (.cons (.quote DW.code) (.hd (.tl .id))))
        (.cons bitsB.code (.cons (ofBits w) (ofBits acc))) (ofBits w') (1 + 3 + 1 + 20 * w.length + 2) :=
      Gives.app (p := DW.code) (Gives.cons (Gives.quote DW.code _) (Gives.id _).tl.hd) (by
        rw [Fm.ofTree_code]
        exact (Does.of_dt hdw).mono hk)
    have hl : w'.length = w.length := length_decw h1
    obtain ⟨Q1, d1, q1, v1⟩ := ih w' (true :: acc) (by omega)
    obtain ⟨Q0, d0, q0, v0⟩ := ih w' (false :: acc) (by omega)
    have d1' : Does θ (Fm.ofTree bitsB.code) (.cons bitsB.code (.cons (ofBits w') (.cons one (ofBits acc)))) Q1
        ((n + 1) * (60 * w.length + 100)) := by rw [Fm.ofTree_code, ← hl]; exact d1
    have d0' : Does θ (Fm.ofTree bitsB.code) (.cons bitsB.code (.cons (ofBits w') (.cons .nil (ofBits acc)))) Q0
        ((n + 1) * (60 * w.length + 100)) := by rw [Fm.ofTree_code, ← hl]; exact d0
    have r1 := Does.run (Gives.id (θ := θ) (.cons bitsB.code (.cons (ofBits w) (ofBits acc)))).hd
      (Gives.cons (Gives.id _).hd (Gives.cons hd (Gives.cons (Gives.quote one _) (Gives.id _).tl.tl))) d1'
    have r0 := Does.run (Gives.id (θ := θ) (.cons bitsB.code (.cons (ofBits w) (ofBits acc)))).hd
      (Gives.cons (Gives.id _).hd (Gives.cons hd (Gives.cons (Gives.quote .nil _) (Gives.id _).tl.tl))) d0'
    refine ⟨Q1 ++ Q0, (Does.ite_true hnz e (Does.either r1 r0)).mono ?_, ?_, ?_⟩
    · have : max (2 + (2 + (1 + 3 + 1 + 20 * w.length + 2 + (1 + 3 + 1) + 1) + 1) + (n + 1) * (60 * w.length + 100) + 1)
          (2 + (2 + (1 + 3 + 1 + 20 * w.length + 2 + (1 + 3 + 1) + 1) + 1) + (n + 1) * (60 * w.length + 100) + 1) =
          2 + (2 + (1 + 3 + 1 + 20 * w.length + 2 + (1 + 3 + 1) + 1) + 1) + (n + 1) * (60 * w.length + 100) + 1 := max_self _
      have e2 : (n + 1 + 1) * (60 * w.length + 100) = (n + 1) * (60 * w.length + 100) + (60 * w.length + 100) := by ring
      omega
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨u, hu, h⟩ := q1 q hq
        exact ⟨true :: u, List.mem_append_left _ (List.mem_map.2 ⟨u, hu, rfl⟩), by simp [h]⟩
      · obtain ⟨u, hu, h⟩ := q0 q hq
        exact ⟨false :: u, List.mem_append_right _ (List.mem_map.2 ⟨u, hu, rfl⟩), by simp [h]⟩
    · intro φ
      rw [wsum_append, v1, v0, allBits, List.map_append, List.sum_append, List.map_map, List.map_map]
      simp [Function.comp_def]


def bitsF (n : List Bool) : Fm := app bitsB.code (.quote (.cons bitsB.code (.cons (ofBits n) .nil)))

theorem bitsF_does (n : List Bool) (x : Tree) : ∃ Q, Does θ (bitsF n) x Q ((KT.val n + 1) * (60 * n.length + 100) + 5) ∧
    (∀ q ∈ Q, ∃ u ∈ allBits (KT.val n), q.2 = ofBits u.reverse) ∧
    ∀ φ : Tree → A, wsum Q φ = ((allBits (KT.val n)).map fun u => φ (ofBits u.reverse)).sum := by
  obtain ⟨Q, d, h1, h2⟩ := bitsB_does (θ := θ) (KT.val n) n [] rfl
  have h := Does.app (p := bitsB.code) (R := fun _ => Q) (Gives.quote (θ := θ) (.cons bitsB.code (.cons (ofBits n) .nil)) x)
    (by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      rw [Fm.ofTree_code]
      exact d)
  refine ⟨Q, (h.congr ?_ fun φ => ?_).mono (by omega), ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, r, hr, h3, h4⟩ := mem_bindW hp
    exact ⟨r, hr, h3.symm⟩
  · rw [wsum_bindW]
    simp
  · intro q hq
    obtain ⟨u, hu, h⟩ := h1 q hq
    exact ⟨u, hu, by simpa using h⟩
  · intro φ
    rw [h2]
    simp

end Bits

end NS1
end
/- Source module NS1.DSteps. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}


def gets (W : Tree) : List Bool → Tree := fun p => tget p W

theorem gets_nil : gets .nil = fun _ => .nil := funext tget_nil

theorem gets_tset (W : Tree) (p : List Bool) (v : Tree) : gets (tset p v W) = Function.update (gets W) p v :=
  funext ((show RepW W (gets W) from fun _ => rfl).set p v)

theorem gets_assign (W o : Tree) : gets (assignT W o) = assignS (gets W) o :=
  funext ((show RepW W (gets W) from fun _ => rfl).assign o)


inductive DStep where
  
  | pick (p : List Bool) (tab : Tree)
  
  | op (p q dst : List Bool) (φ : Tree)
  
  | bits (p dst : List Bool)
  
  | check (p : List Bool)

namespace DStep


def tree : DStep → Tree
  | pick p tab => .cons (num 0) (.cons (ofBits p) tab)
  | op p q dst φ => .cons (num 1) (.cons (ofBits p) (.cons (ofBits q) (.cons (ofBits dst) φ)))
  | bits p dst => .cons (num 2) (.cons (ofBits p) (ofBits dst))
  | check p => .cons (num 3) (ofBits p)


def exec (m : ℕ) : DStep → (List Bool → Tree) → List (List Bool → Tree)
  | pick p tab, σ => (tget (σ p).path tab).toList.map fun o => assignS σ o
  | op p q dst φ, σ => [Function.update σ dst (tget (σ q).path (tget (σ p).path φ))]
  | bits p dst, σ => if σ p = .nil then [σ] else (allBits m).map fun u => Function.update σ dst (ofBits u.reverse)
  | check p, σ => if σ p = .nil then [] else [σ]


def cost (m mb : ℕ) : DStep → (List Bool → Tree) → ℕ
  | pick p tab, σ => 30 * p.length + 30 * (σ p).len + 20 * (tget (σ p).path tab).toList.length +
      ((tget (σ p).path tab).toList.map fun o => (o.toList.map fun y => 60 * y.hd.len + 80).sum).sum + 200
  | op p q dst _, σ => 30 * p.length + 30 * q.length + 60 * dst.length + 30 * (σ p).len + 30 * (σ q).len + 200
  | bits p dst, σ => 30 * p.length + 60 * dst.length + (if σ p = .nil then 0 else (m + 1) * (60 * mb + 100)) + 200
  | check p, _ => 30 * p.length + 100

end DStep


def dstepF (n : List Bool) : Fm := .ite (.hd (.hd .id))
  (.ite (.tl (.hd (.hd .id)))
    (.ite (.tl (.tl (.hd (.hd .id))))
      -- check
      (.ite (getF (.tl (.hd .id)) (.tl .id)) (.tl .id) .fail)
      -- bits
      (.ite (getF (.hd (.tl (.hd .id))) (.tl .id))
        (lett (.cons .id (bitsF n)) (setF (.tl (.tl (.hd (.hd .id)))) (.tl .id) (.tl (.hd .id))))
        (.tl .id)))
    -- op
    (setF (.hd (.tl (.tl (.tl (.hd .id)))))
      (getF (getF (.hd (.tl (.tl (.hd .id)))) (.tl .id))
        (getF (getF (.hd (.tl (.hd .id))) (.tl .id)) (.tl (.tl (.tl (.tl (.hd .id)))))))
      (.tl .id)))
  -- pick
  (lett (.cons .id (pickF (getF (getF (.hd (.tl (.hd .id))) (.tl .id)) (.tl (.tl (.hd .id))))))
    (assignF (.tl .id) (.tl (.hd .id))))

theorem len_ofBits (w : List Bool) : (ofBits w).len = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ofBits, len, ih]

theorem dstepF_does (n : List Bool) (st : DStep) (W : Tree) : ∃ Q,
    Does θ (dstepF n) (.cons st.tree W) Q (st.cost (KT.val n) n.length (gets W)) ∧
    (∀ q ∈ Q, gets q.2 ∈ st.exec (KT.val n) (gets W)) ∧
    ∀ Φ : (List Bool → Tree) → A, wsum Q (fun o => Φ (gets o)) = ((st.exec (KT.val n) (gets W)).map Φ).sum := by
  cases st with
  | check p =>
    have hg : Gives θ (getF (.tl (.hd .id)) (.tl .id)) (.cons (DStep.check p).tree W) (tget p W)
        (3 + 2 + 30 * p.length + 20) := by
      have := getF_gives (Gives.id (θ := θ) (.cons (DStep.check p).tree W)).hd.tl (Gives.id _).tl
      simp only [DStep.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at this ⊢
      exact this
    by_cases h : tget p W = .nil
    · rw [h] at hg
      refine ⟨[], ((Does.ite_true (Gives.id _).hd.hd (by simp [DStep.tree, num]) (Does.ite_true (Gives.id _).hd.hd.tl
        (by simp [DStep.tree, num]) (Does.ite_true (Gives.id _).hd.hd.tl.tl (by simp [DStep.tree, num])
        (Does.ite_false hg (Does.fail _)))))).mono ?_, by simp, fun Φ => ?_⟩
      · simp only [DStep.cost]
        omega
      · simp [DStep.exec, gets, h]
    · refine ⟨[(1, W)], ((Does.ite_true (Gives.id _).hd.hd (by simp [DStep.tree, num]) (Does.ite_true (Gives.id _).hd.hd.tl
        (by simp [DStep.tree, num]) (Does.ite_true (Gives.id _).hd.hd.tl.tl (by simp [DStep.tree, num])
        (Does.ite_true hg h (Gives.id _).tl))))).mono ?_, ?_, fun Φ => ?_⟩
      · simp only [DStep.cost]
        omega
      · intro q hq
        rw [List.mem_singleton] at hq
        subst hq
        simp [DStep.exec, gets, h]
      · simp [DStep.exec, gets, h]
  | bits p dst =>
    have hg : Gives θ (getF (.hd (.tl (.hd .id))) (.tl .id)) (.cons (DStep.bits p dst).tree W) (tget p W)
        (4 + 2 + 30 * p.length + 20) := by
      have := getF_gives (Gives.id (θ := θ) (.cons (DStep.bits p dst).tree W)).hd.tl.hd (Gives.id _).tl
      simp only [DStep.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at this ⊢
      exact this
    by_cases h : tget p W = .nil
    · rw [h] at hg
      refine ⟨[(1, W)], ((Does.ite_true (Gives.id _).hd.hd (by simp [DStep.tree, num]) (Does.ite_true (Gives.id _).hd.hd.tl
        (by simp [DStep.tree, num]) (Does.ite_false (Gives.id _).hd.hd.tl.tl
        (Does.ite_false hg (Gives.id _).tl))))).mono ?_, ?_, fun Φ => ?_⟩
      · simp only [DStep.cost, gets, h, if_true]
        omega
      · intro q hq
        rw [List.mem_singleton] at hq
        subst hq
        simp [DStep.exec, gets, h]
      · simp [DStep.exec, gets, h]
    · obtain ⟨Q, d, h1, h2⟩ := bitsF_does (θ := θ) n (.cons (DStep.bits p dst).tree W)
      have hs : ∀ q ∈ Q, Does θ (setF (.tl (.tl (.hd (.hd .id)))) (.tl .id) (.tl (.hd .id)))
          (.cons (.cons (DStep.bits p dst).tree W) q.2) [(1, tset dst q.2 W)] (5 + 2 + 3 + 60 * dst.length + 30) := by
        intro q _
        have := setF_gives (Gives.id (θ := θ) (.cons (.cons (DStep.bits p dst).tree W) q.2)).hd.hd.tl.tl (Gives.id _).tl
          (Gives.id _).hd.tl
        simp only [DStep.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at this ⊢
        exact this
      refine ⟨_, ((Does.ite_true (Gives.id _).hd.hd (by simp [DStep.tree, num]) (Does.ite_true (Gives.id _).hd.hd.tl
        (by simp [DStep.tree, num]) (Does.ite_false (Gives.id _).hd.hd.tl.tl
        (Does.ite_true hg h (Does.letk (R := fun o => [(1, tset dst o W)]) d hs)))))).mono ?_, ?_, fun Φ => ?_⟩
      · simp only [DStep.cost, gets, h, if_false]
        omega
      · intro q hq
        obtain ⟨q1, hq1, r, hr, e, -⟩ := mem_bindW hq
        rw [List.mem_singleton] at hr
        subst hr
        obtain ⟨u, hu, hu'⟩ := h1 q1 hq1
        rw [e, gets_tset, hu']
        simp only [DStep.exec, gets, h, if_false]
        exact List.mem_map.2 ⟨u, hu, rfl⟩
      · rw [wsum_bindW]
        simp only [wsum_cons, wsum_nil, one_mul, add_zero, gets_tset]
        rw [h2 fun o => Φ (Function.update (gets W) dst o)]
        simp [DStep.exec, gets, h, Function.comp_def]
  | op p q dst φ =>
    have hp : Gives θ (getF (.hd (.tl (.hd .id))) (.tl .id)) (.cons (DStep.op p q dst φ).tree W) (tget p W)
        (4 + 2 + 30 * p.length + 20) := by
      have := getF_gives (Gives.id (θ := θ) (.cons (DStep.op p q dst φ).tree W)).hd.tl.hd (Gives.id _).tl
      simp only [DStep.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at this ⊢
      exact this
    have hq : Gives θ (getF (.hd (.tl (.tl (.hd .id)))) (.tl .id)) (.cons (DStep.op p q dst φ).tree W) (tget q W)
        (5 + 2 + 30 * q.length + 20) := by
      have := getF_gives (Gives.id (θ := θ) (.cons (DStep.op p q dst φ).tree W)).hd.tl.tl.hd (Gives.id _).tl
      simp only [DStep.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at this ⊢
      exact this
    have hφ := getF_gives hq (getF_gives hp (Gives.id (θ := θ) (.cons (DStep.op p q dst φ).tree W)).hd.tl.tl.tl.tl)
    have hs := setF_gives (Gives.id (θ := θ) (.cons (DStep.op p q dst φ).tree W)).hd.tl.tl.tl.hd hφ (Gives.id _).tl
    simp only [DStep.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at hs
    refine ⟨[(1, tset dst (tget (tget q W).path (tget (tget p W).path φ)) W)], (Does.ite_true (Gives.id _).hd.hd
      (by simp [DStep.tree, num]) (Does.ite_false (Gives.id _).hd.hd.tl hs)).mono ?_, ?_, fun Φ => ?_⟩
    · simp only [DStep.cost, gets]
      omega
    · intro r hr
      rw [List.mem_singleton] at hr
      subst hr
      rw [gets_tset]
      simp [DStep.exec, gets]
    · simp only [wsum_cons, wsum_nil, one_mul, add_zero, gets_tset]
      simp [DStep.exec, gets]
  | pick p tab =>
    have hp : Gives θ (getF (.hd (.tl (.hd .id))) (.tl .id)) (.cons (DStep.pick p tab).tree W) (tget p W)
        (4 + 2 + 30 * p.length + 20) := by
      have := getF_gives (Gives.id (θ := θ) (.cons (DStep.pick p tab).tree W)).hd.tl.hd (Gives.id _).tl
      simp only [DStep.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at this ⊢
      exact this
    have hl := getF_gives hp (Gives.id (θ := θ) (.cons (DStep.pick p tab).tree W)).hd.tl.tl
    obtain ⟨opts, ho⟩ : ∃ l, l = (tget (tget p W).path tab).toList := ⟨_, rfl⟩
    have hl' : Gives θ (getF (getF (.hd (.tl (.hd .id))) (.tl .id)) (.tl (.tl (.hd .id)))) (.cons (DStep.pick p tab).tree W)
        (listT opts) (4 + 2 + 30 * p.length + 20 + 4 + 30 * (tget p W).len + 20) := by
      rw [ho, listT_toList]
      exact hl
    have hpk := pickF_does hl'
    have hs : ∀ q ∈ opts.map fun x => ((1 : A), x), Does θ (assignF (.tl .id) (.tl (.hd .id)))
        (.cons (.cons (DStep.pick p tab).tree W) q.2) [(1, assignT W q.2)]
        (2 + 3 + (opts.map fun o => (o.toList.map fun y => 60 * y.hd.len + 80).sum).sum + 20) := by
      intro q hq
      rw [List.mem_map] at hq
      obtain ⟨o, ho', rfl⟩ := hq
      refine (assignF_gives (Gives.id _).tl (Gives.id _).hd.tl).mono ?_
      have := List.single_le_sum (l := opts.map fun o => (o.toList.map fun y => 60 * y.hd.len + 80).sum)
        (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨o, ho', rfl⟩)
      simp only [tl_cons]
      omega
    refine ⟨_, (Does.ite_false (Gives.id _).hd.hd (Does.letk (R := fun o => [(1, assignT W o)]) hpk hs)).mono ?_, ?_,
      fun Φ => ?_⟩
    · simp only [DStep.cost, gets, ← ho]
      omega
    · intro r hr
      obtain ⟨q1, hq1, r', hr', e, -⟩ := mem_bindW hr
      rw [List.mem_singleton] at hr'
      subst hr'
      rw [List.mem_map] at hq1
      obtain ⟨o, ho', rfl⟩ := hq1
      rw [e, gets_assign]
      simp only [DStep.exec, gets, ← ho]
      exact List.mem_map.2 ⟨o, ho', rfl⟩
    · rw [wsum_bindW]
      simp only [wsum_cons, wsum_nil, one_mul, add_zero, gets_assign]
      simp [DStep.exec, gets, ← ho, wsum, Function.comp_def]


def execAll (m : ℕ) : List DStep → (List Bool → Tree) → List (List Bool → Tree)
  | [], σ => [σ]
  | st :: sts, σ => (st.exec m σ).flatMap (execAll m sts)

theorem sum_execAll_cons (m : ℕ) (st : DStep) (sts : List DStep) (σ : List Bool → Tree) (Φ : (List Bool → Tree) → A) :
    ((execAll m (st :: sts) σ).map Φ).sum = ((st.exec m σ).map fun σ' => ((execAll m sts σ').map Φ).sum).sum := by
  rw [execAll, sum_flatMap_map]

theorem execAll_append (m : ℕ) (sts sts' : List DStep) (σ : List Bool → Tree) :
    execAll m (sts ++ sts') σ = (execAll m sts σ).flatMap (execAll m sts') := by
  induction sts generalizing σ with
  | nil => simp [execAll]
  | cons st sts ih =>
    rw [List.cons_append, execAll, execAll, List.flatMap_assoc]
    exact List.flatMap_congr fun σ' _ => ih σ'


def dstepsF (n : List Bool) (sts : List DStep) (w : Fm) : Fm :=
  foldF (dstepF n) w (.quote (listT (sts.map DStep.tree)))

theorem dstepsF_does (n : List Bool) (sts : List DStep) {wf : Fm} {x W : Tree} {cw : ℕ} (hw : Gives θ wf x W cw)
    {I : List DStep → (List Bool → Tree) → Prop} {c : DStep → ℕ}
    (hI : ∀ st sts' σ, I (st :: sts') σ → st.cost (KT.val n) n.length σ ≤ c st ∧
      ∀ σ' ∈ st.exec (KT.val n) σ, I sts' σ') (hW : I sts (gets W)) : ∃ Q,
    Does θ (dstepsF n sts wf) x Q (cw + (sts.map fun st => c st + 30).sum + 30) ∧
    (∀ q ∈ Q, gets q.2 ∈ execAll (KT.val n) sts (gets W)) ∧
    ∀ Φ : (List Bool → Tree) → A, wsum Q (fun o => Φ (gets o)) = ((execAll (KT.val n) sts (gets W)).map Φ).sum := by
  choose f hf1 hf2 hf3 using fun st W => dstepF_does (θ := θ) n st W
  -- a function of trees
  classical
  let F : Tree → Tree → List (A × Tree) := fun t W => if h : ∃ st : DStep, st.tree = t then f h.choose W else []
  have hF : ∀ st : DStep, ∃ st' : DStep, st'.tree = st.tree ∧ ∀ W, F st.tree W = f st' W := by
    intro st
    have h : ∃ st' : DStep, st'.tree = st.tree := ⟨st, rfl⟩
    exact ⟨h.choose, h.choose_spec, fun W => dif_pos h⟩
  have hinj : ∀ st st' : DStep, st.tree = st'.tree → st = st' := by
    have hob : ∀ a b : List Bool, ofBits a = ofBits b → a = b := fun a b h => by
      rw [← path_ofBits a, h, path_ofBits]
    intro st st' h
    cases st <;> cases st' <;> simp only [DStep.tree, Tree.cons.injEq, num] at h <;>
      simp only [reduceCtorEq, false_and, and_false, true_and, and_true, Tree.cons.injEq] at h
    · rw [hob _ _ h.1, h.2]
    · rw [hob _ _ h.1, hob _ _ h.2.1, hob _ _ h.2.2.1, h.2.2.2]
    · rw [hob _ _ h.1, hob _ _ h.2]
    · rw [hob _ _ h]
  have hF' : ∀ (st : DStep) W, F st.tree W = f st W := by
    intro st W
    obtain ⟨st', h1, h2⟩ := hF st
    rw [h2, hinj _ _ h1]
  have hsum : ∀ (sts : List DStep) (W : Tree) (Φ : (List Bool → Tree) → A),
      wsum (foldW F (sts.map DStep.tree) W) (fun o => Φ (gets o)) = ((execAll (KT.val n) sts (gets W)).map Φ).sum := by
    intro sts
    induction sts with
    | nil =>
      intro W Φ
      simp [foldW, execAll]
    | cons st sts ih =>
      intro W Φ
      rw [List.map_cons, foldW, wsum_bindW, sum_execAll_cons, ← hf3 st W, hF']
      exact wsum_congr fun q _ => ih q.2 Φ
  have hmem : ∀ (sts : List DStep) (W : Tree), ∀ q ∈ foldW F (sts.map DStep.tree) W,
      gets q.2 ∈ execAll (KT.val n) sts (gets W) := by
    intro sts
    induction sts with
    | nil =>
      intro W q hq
      simp only [List.map_nil, foldW, List.mem_singleton] at hq
      subst hq
      simp [execAll]
    | cons st sts ih =>
      intro W q hq
      rw [List.map_cons, foldW] at hq
      obtain ⟨q1, hq1, r, hr, e, -⟩ := mem_bindW hq
      rw [hF'] at hq1
      rw [e, execAll, List.mem_flatMap]
      exact ⟨_, hf2 st W q1 hq1, ih q1.2 r hr⟩
  let d : Tree → ℕ := fun t => if h : ∃ st : DStep, st.tree = t then c h.choose else 0
  have hd : ∀ st : DStep, d st.tree = c st := by
    intro st
    have h : ∃ st' : DStep, st'.tree = st.tree := ⟨st, rfl⟩
    have h1 : d st.tree = c h.choose := dif_pos h
    rw [h1, hinj _ _ h.choose_spec]
  have hfold := foldF_does (f := F) (xs := sts.map DStep.tree) (d := d)
    (Inv := fun ys W => ∃ sts' : List DStep, ys = sts'.map DStep.tree ∧ I sts' (gets W)) hw
    (Gives.quote (θ := θ) (listT (sts.map DStep.tree)) x) (step := dstepF n) (by
      rintro t ys W - ⟨sts', h1, h2⟩
      cases sts' with
      | nil => simp at h1
      | cons st sts' =>
        rw [List.map_cons, List.cons.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        obtain ⟨h3, h4⟩ := hI st sts' _ h2
        rw [hF', hd]
        exact ⟨(hf1 st W).mono h3, fun q hq => ⟨sts', rfl, h4 _ (hf2 st W q hq)⟩⟩) ⟨sts, rfl, hW⟩
  refine ⟨_, hfold.mono ?_, hmem sts W, hsum sts W⟩
  rw [List.map_map]
  have e : (sts.map ((fun x => d x + 30) ∘ DStep.tree)) = sts.map fun st => c st + 30 :=
    List.map_congr_left fun st _ => by simp only [Function.comp_apply, hd]
  rw [e]
  omega

section Templates


inductive Tm where
  
  | c (t : Tree)
  
  | get (p : List Bool)
  
  | cons (a b : Tm)
  
  | ifeq (p : List Bool) (t : Tree) (a b : Tm)
  
  | app (a b : Tm)

namespace Tm


def tree : Tm → Tree
  | c t => .cons (num 0) t
  | get p => .cons (num 1) (ofBits p)
  | cons a b => .cons (num 2) (.cons a.tree b.tree)
  | ifeq p t a b => .cons (num 3) (.cons (ofBits p) (.cons t (.cons a.tree b.tree)))
  | app a b => .cons (num 4) (.cons a.tree b.tree)


def expand (σ : List Bool → Tree) : Tm → Tree
  | c t => t
  | get p => σ p
  | cons a b => .cons (a.expand σ) (b.expand σ)
  | ifeq p t a b => if σ p = t then a.expand σ else b.expand σ
  | app a b => listT ((a.expand σ).toList ++ (b.expand σ).toList)


def cost (σ : List Bool → Tree) : Tm → ℕ
  | c _ => 20
  | get p => 30 * p.length + 50
  | cons a b => a.cost σ + b.cost σ + 100
  | ifeq p _ a b => 30 * p.length + 60 * (σ p).size + (if σ p = .nil then 0 else 0) + a.cost σ + b.cost σ + 200
  | app a b => a.cost σ + b.cost σ + 62 * (a.expand σ).toList.length + 250

end Tm


def tmRec (t : Fm) : Fm := .run (.hd .id) (.cons (.hd .id) (.cons t (.tl (.tl .id))))


def tmB : Fm := .ite (.hd (.hd (.tl .id)))
  (.ite (.tl (.hd (.hd (.tl .id))))
    (.ite (.tl (.tl (.hd (.hd (.tl .id)))))
      (.ite (.tl (.tl (.tl (.hd (.hd (.tl .id))))))
        (appF (tmRec (.hd (.tl (.hd (.tl .id))))) (tmRec (.tl (.tl (.hd (.tl .id))))))
        (.ite (eqF (getF (.hd (.tl (.hd (.tl .id)))) (.tl (.tl .id))) (.hd (.tl (.tl (.hd (.tl .id))))))
          (tmRec (.hd (.tl (.tl (.tl (.hd (.tl .id))))))) (tmRec (.tl (.tl (.tl (.tl (.hd (.tl .id)))))))))
      (.cons (tmRec (.hd (.tl (.hd (.tl .id))))) (tmRec (.tl (.tl (.hd (.tl .id)))))))
    (getF (.tl (.hd (.tl .id))) (.tl (.tl .id))))
  (.tl (.hd (.tl .id)))

theorem tmRec_gives {t : Fm} {x s W o : Tree} {ct d : ℕ} (ht : Gives θ t (.cons tmB.code (.cons x W)) s ct)
    (h : Gives θ tmB (.cons tmB.code (.cons s W)) o d) :
    Gives θ (tmRec t) (.cons tmB.code (.cons x W)) o (ct + d + 15) := by
  refine (Gives.run (Gives.id (θ := θ) (.cons tmB.code (.cons x W))).hd (Gives.cons (Gives.id _).hd
    (Gives.cons ht (Gives.id _).tl.tl)) (by rw [hd_cons, Fm.ofTree_code]; exact h)).mono (by omega)

theorem tmB_gives (t : Tm) (W : Tree) :
    Gives θ tmB (.cons tmB.code (.cons t.tree W)) (t.expand (gets W)) (t.cost (gets W)) := by
  induction t with
  | c t =>
    exact ((Gives.id _).tl.hd.hd.ite_false (Gives.id _).tl.hd.tl).mono (by simp [Tm.cost])
  | get p =>
    have hg := getF_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.get p).tree W))).tl.hd.tl (Gives.id _).tl.tl
    simp only [Tm.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at hg
    refine ((Gives.id _).tl.hd.hd.ite_true (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.ite_false hg)).mono ?_
    simp only [Tm.cost]
    omega
  | cons a b iha ihb =>
    have ha := tmRec_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.cons a b).tree W))).tl.hd.tl.hd iha
    have hb := tmRec_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.cons a b).tree W))).tl.hd.tl.tl ihb
    refine ((Gives.id _).tl.hd.hd.ite_true (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.ite_true
      (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.tl.ite_false (Gives.cons ha hb)))).mono ?_
    simp only [Tm.cost]
    omega
  | ifeq p t a b iha ihb =>
    have ha := tmRec_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.ifeq p t a b).tree W))).tl.hd.tl.tl.tl.hd iha
    have hb := tmRec_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.ifeq p t a b).tree W))).tl.hd.tl.tl.tl.tl ihb
    have hg := getF_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.ifeq p t a b).tree W))).tl.hd.tl.hd (Gives.id _).tl.tl
    simp only [Tm.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at hg
    have he := eqF_gives hg (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.ifeq p t a b).tree W))).tl.hd.tl.tl.hd
    have e0 : (Tm.ifeq p t a b).expand (gets W) = if tget p W = t then a.expand (gets W) else b.expand (gets W) := rfl
    have hc : (Tm.ifeq p t a b).cost (gets W) = 30 * p.length + 60 * (tget p W).size + (if gets W p = .nil then 0 else 0) +
      a.cost (gets W) + b.cost (gets W) + 200 := rfl
    have hc0 : (if gets W p = .nil then 0 else 0) = 0 := by split_ifs <;> rfl
    rw [e0]
    by_cases h : tget p W = t
    · rw [if_pos h]
      have hb' : bit (decide (tget p W = t)) ≠ .nil := by simp [h, bit, one]
      refine ((Gives.id _).tl.hd.hd.ite_true (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.ite_true
        (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.tl.ite_true (by simp [Tm.tree, num])
        ((Gives.id _).tl.hd.hd.tl.tl.tl.ite_false (Gives.ite_true he hb' ha))))).mono ?_
      rw [hc, hc0]
      omega
    · rw [if_neg h]
      have hb' : bit (decide (tget p W = t)) = .nil := by simp [h, bit]
      rw [show (Tree.cons tmB.code (.cons (Tm.ifeq p t a b).tree W)).tl.hd.tl.tl.hd = t from rfl, hb'] at he
      refine ((Gives.id _).tl.hd.hd.ite_true (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.ite_true
        (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.tl.ite_true (by simp [Tm.tree, num])
        ((Gives.id _).tl.hd.hd.tl.tl.tl.ite_false (Gives.ite_false he hb))))).mono ?_
      rw [hc, hc0]
      omega
  | app a b iha ihb =>
    have ha := tmRec_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.app a b).tree W))).tl.hd.tl.hd iha
    have hb := tmRec_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.app a b).tree W))).tl.hd.tl.tl ihb
    rw [← listT_toList (a.expand (gets W))] at ha
    rw [← listT_toList (b.expand (gets W))] at hb
    have happ := appF_gives ha hb
    refine ((Gives.id _).tl.hd.hd.ite_true (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.ite_true
      (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.tl.ite_true (by simp [Tm.tree, num])
      ((Gives.id _).tl.hd.hd.tl.tl.tl.ite_true (by simp [Tm.tree, num]) happ)))).mono ?_
    simp only [Tm.cost]
    omega


def tmF (t w : Fm) : Fm := app tmB.code (.cons (.quote tmB.code) (.cons t w))

theorem tmF_gives {tf wf : Fm} {x W : Tree} {ct cw : ℕ} {t : Tm} (ht : Gives θ tf x t.tree ct) (hw : Gives θ wf x W cw) :
    Gives θ (tmF tf wf) x (t.expand (gets W)) (ct + cw + t.cost (gets W) + 10) := by
  refine (Gives.app (p := tmB.code) (Gives.cons (Gives.quote _ _) (Gives.cons ht hw)) (by
    rw [Fm.ofTree_code]
    exact tmB_gives t W)).mono (by omega)


def tmsF (ts : List Tm) (w : Fm) : Fm := mapF (tmF (.tl .id) (.hd .id)) w (.quote (listT (ts.map Tm.tree)))

theorem tmsF_gives {wf : Fm} {x W : Tree} {cw c : ℕ} {ts : List Tm} (hw : Gives θ wf x W cw)
    (hc : ∀ t ∈ ts, t.cost (gets W) ≤ c) :
    Gives θ (tmsF ts wf) x (listT (ts.map fun t => t.expand (gets W))) (cw + ts.length * (c + 60) + 30) := by
  classical
  let g : Tree → Tree := fun y => if h : ∃ t ∈ ts, t.tree = y then h.choose.expand (gets W) else .nil
  have hg : ∀ y ∈ ts.map Tm.tree, ∃ t ∈ ts, t.tree = y ∧ g y = t.expand (gets W) := by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    have h : ∃ t' ∈ ts, t'.tree = t.tree := ⟨t, ht, rfl⟩
    exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, dif_pos h⟩
  have hall : ∀ t ∈ ts, g t.tree = t.expand (gets W) := by
    intro t ht
    obtain ⟨t', ht', h1, h2⟩ := hg t.tree (List.mem_map.2 ⟨t, ht, rfl⟩)
    rw [h2]
    have e1 := tmB_gives (θ := fun _ => (0 : ℤ)) t W
    have e2 := tmB_gives (θ := fun _ => (0 : ℤ)) t' W
    rw [h1] at e2
    -- both are the value of the program at the same tree
    have h3 := e1.evl.2 fun o => if o = t.expand (gets W) then 1 else 0
    have h4 := e2.evl.2 fun o => if o = t.expand (gets W) then 1 else 0
    rw [h3] at h4
    simp only [wsum_cons, wsum_nil, if_true, mul_one, add_zero, one_mul] at h4
    by_contra hne
    rw [if_neg hne] at h4
    exact one_ne_zero h4
  have := mapF_gives (step := tmF (.tl .id) (.hd .id)) (g := g) (d := fun _ => c + 20) (xs := ts.map Tm.tree) hw
    (Gives.quote (θ := θ) (listT (ts.map Tm.tree)) x) (by
      intro y hy
      obtain ⟨t, ht, rfl, h2⟩ := hg y hy
      rw [h2]
      refine (tmF_gives (t := t) (Gives.id _).tl (Gives.id _).hd).mono ?_
      have := hc t ht
      simp only [hd_cons]
      omega)
  rw [List.map_map] at this
  have e : ts.map (g ∘ Tm.tree) = ts.map fun t => t.expand (gets W) := List.map_congr_left fun t ht => hall t ht
  rw [e] at this
  refine this.mono ?_
  rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map]
  have e2 : ts.length * (c + 20 + 40) = ts.length * (c + 60) := by ring
  omega

end Templates

end NS1
end
/- Source module NS1.Picks. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A]

variable {ι : Type} [DecidableEq ι]


def funs {α : Type} (opts : ι → List α) (f0 : ι → α) : List ι → List (ι → α)
  | [] => [f0]
  | i :: s => (opts i).flatMap fun a => (funs opts (Function.update f0 i a) s)

theorem funs_eq_of_not_mem {α : Type} (opts : ι → List α) {s : List ι} {f0 f : ι → α} (h : f ∈ funs opts f0 s) {i : ι}
    (hi : i ∉ s) : f i = f0 i := by
  induction s generalizing f0 with
  | nil =>
    simp only [funs, List.mem_singleton] at h
    rw [h]
  | cons j s ih =>
    simp only [funs, List.mem_flatMap] at h
    obtain ⟨a, ha, h⟩ := h
    rw [List.mem_cons, not_or] at hi
    rw [ih h hi.2, Function.update_of_ne hi.1]


theorem sum_funs {α : Type} [Fintype α] [DecidableEq α] [Fintype ι] (opts : ι → List α) (hopts : ∀ i, (opts i).Nodup)
    (s : List ι) (hs : s.Nodup) (f0 : ι → α) (Φ : (ι → α) → A) :
    ((funs opts f0 s).map Φ).sum = ∑ f : ι → α, if (∀ i ∈ s, f i ∈ opts i) ∧ (∀ i, i ∉ s → f i = f0 i) then Φ f else 0 := by
  induction s generalizing f0 with
  | nil =>
    have : ∀ f : ι → α, ((∀ i ∈ ([] : List ι), f i ∈ opts i) ∧ ∀ i, i ∉ ([] : List ι) → f i = f0 i) ↔ f = f0 := by
      intro f
      simp [funext_iff]
    simp only [this, funs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  | cons i s ih =>
    rw [List.nodup_cons] at hs
    rw [funs, sum_flatMap_map]
    simp only [ih hs.2]
    have h1 : ∀ a, (∑ f : ι → α, if (∀ j ∈ s, f j ∈ opts j) ∧ (∀ j, j ∉ s → f j = Function.update f0 i a j) then Φ f else 0) =
        ∑ f : ι → α, if f i = a then (if (∀ j ∈ s, f j ∈ opts j) ∧ (∀ j, j ∉ i :: s → f j = f0 j) then Φ f else 0) else 0 := by
      intro a
      refine Finset.sum_congr rfl fun f _ => ?_
      by_cases ha : f i = a
      · rw [if_pos ha]
        refine if_congr (and_congr_right fun _ => ?_) rfl rfl
        constructor
        · intro h j hj
          rw [List.mem_cons, not_or] at hj
          rw [h j hj.2, Function.update_of_ne hj.1]
        · intro h j hj
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self, ha]
          · rw [Function.update_of_ne hji]
            exact h j (by rw [List.mem_cons, not_or]; exact ⟨hji, hj⟩)
      · rw [if_neg ha, if_neg]
        rintro ⟨-, h⟩
        apply ha
        rw [h i hs.1, Function.update_self]
    simp only [h1]
    have h2 : ((opts i).map fun a => ∑ f : ι → α, if f i = a then
        (if (∀ j ∈ s, f j ∈ opts j) ∧ (∀ j, j ∉ i :: s → f j = f0 j) then Φ f else 0) else 0).sum =
        ∑ a ∈ (opts i).toFinset, ∑ f : ι → α, if f i = a then
        (if (∀ j ∈ s, f j ∈ opts j) ∧ (∀ j, j ∉ i :: s → f j = f0 j) then Φ f else 0) else 0 := by
      rw [List.sum_toFinset _ (hopts i)]
    rw [h2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [List.mem_toFinset]
    by_cases hf : f i ∈ opts i
    · rw [if_pos hf]
      refine if_congr (and_congr_left fun _ => ?_) rfl rfl
      simp [hf]
    · rw [if_neg hf, if_neg]
      rintro ⟨h, -⟩
      exact hf (h i List.mem_cons_self)


theorem execAll_choices {α St : Type} {m : ℕ} {L : St → List Bool → Tree} {opts : ι → List α} {step : ι → DStep}
    {ov : ι → α → St → St} (good : St → Prop)
    (hst : ∀ i st, good st → (step i).exec m (L st) = (opts i).map fun a => L (ov i a st))
    (hgood : ∀ i st, ∀ a ∈ opts i, good st → good (ov i a st)) {s : List ι} (hs : s.Nodup) {st : St}
    (hσ : good st) (f0 : ι → α) (Φ : (List Bool → Tree) → A) :
    ((execAll m (s.map step) (L st)).map Φ).sum =
      ((funs opts f0 s).map fun f => Φ (L (s.foldl (fun st i => ov i (f i) st) st))).sum := by
  induction s generalizing st f0 with
  | nil => simp [execAll, funs]
  | cons i s ih =>
    rw [List.nodup_cons] at hs
    rw [List.map_cons, sum_execAll_cons, hst i st hσ, List.map_map, funs, sum_flatMap_map]
    congr 1
    refine List.map_congr_left fun a ha => ?_
    simp only [Function.comp_apply]
    rw [ih hs.2 (hgood i st a ha hσ) (Function.update f0 i a)]
    congr 1
    refine List.map_congr_left fun f hf => ?_
    have hfi : f i = a := by
      rw [funs_eq_of_not_mem opts hf hs.1, Function.update_self]
    rw [List.foldl_cons, hfi]


theorem execAll_det {St : Type} {m : ℕ} {L : St → List Bool → Tree} {step : ι → DStep} {ov : ι → St → St}
    (good : List ι → St → Prop) (hst : ∀ i s st, good (i :: s) st → (step i).exec m (L st) = [L (ov i st)] ∧ good s (ov i st))
    {s : List ι} {st : St} (hσ : good s st) :
    execAll m (s.map step) (L st) = [L (s.foldl (fun st i => ov i st) st)] := by
  induction s generalizing st with
  | nil => rfl
  | cons i s ih =>
    obtain ⟨h1, h2⟩ := hst i s st hσ
    rw [List.map_cons, execAll, h1, List.flatMap_cons, List.flatMap_nil, List.append_nil, ih h2, List.foldl_cons]


theorem execAll_checks_pos {m : ℕ} {ps : List (List Bool)} {σ : List Bool → Tree} (h : ∀ p ∈ ps, σ p ≠ .nil) :
    execAll m (ps.map DStep.check) σ = [σ] := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, execAll, DStep.exec, if_neg (h p List.mem_cons_self), List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact ih fun q hq => h q (List.mem_cons_of_mem _ hq)


theorem execAll_checks_neg {m : ℕ} {ps : List (List Bool)} {σ : List Bool → Tree} (h : ∃ p ∈ ps, σ p = .nil) :
    execAll m (ps.map DStep.check) σ = [] := by
  induction ps with
  | nil => simp at h
  | cons p ps ih =>
    rw [List.map_cons, execAll, DStep.exec]
    by_cases hp : σ p = .nil
    · rw [if_pos hp]
      rfl
    · rw [if_neg hp, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine ih ?_
      obtain ⟨q, hq, hq'⟩ := h
      rcases List.mem_cons.1 hq with rfl | hq
      · exact absurd hq' hp
      · exact ⟨q, hq, hq'⟩

end NS1
end
/- Source module Nc.Dl.Names. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree

section Names

variable {ν : Type} [DecidableEq ν] (nm : ν → List Bool)

open Classical in

noncomputable def byPath (st : ν → Tree) : List Bool → Tree := fun p =>
  if h : ∃ x, nm x = p then st h.choose else .nil

variable {nm} (hnm : Function.Injective nm)

include hnm

theorem byPath_nm (st : ν → Tree) (x : ν) : byPath nm st (nm x) = st x := by
  have h : ∃ y, nm y = nm x := ⟨x, rfl⟩
  rw [byPath, dif_pos h, hnm h.choose_spec]

theorem update_byPath (st : ν → Tree) (x : ν) (v : Tree) :
    Function.update (byPath nm st) (nm x) v = byPath nm (Function.update st x v) := by
  classical
  funext p
  by_cases h : ∃ y, nm y = p
  · obtain ⟨y, rfl⟩ := h
    rw [byPath_nm hnm, Function.update_apply, Function.update_apply, byPath_nm hnm]
    simp only [hnm.eq_iff]
  · rw [Function.update_of_ne]
    · rw [byPath, dif_neg h, byPath, dif_neg h]
    · rintro rfl
      exact h ⟨x, rfl⟩


def optT (nm : ν → List Bool) (o : List (ν × Tree)) : Tree := listT (o.map fun a => .cons (ofBits (nm a.1)) a.2)


def upds (st : ν → Tree) (o : List (ν × Tree)) : ν → Tree := o.foldl (fun st a => Function.update st a.1 a.2) st

theorem assignS_byPath (st : ν → Tree) (o : List (ν × Tree)) :
    assignS (byPath nm st) (optT nm o) = byPath nm (upds st o) := by
  unfold assignS optT upds
  rw [toList_listT]
  induction o generalizing st with
  | nil => rfl
  | cons a o ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, hd_cons, tl_cons, path_ofBits, update_byPath hnm, ih]

theorem exec_pick {m : ℕ} {st : ν → Tree} {x : ν} {tab : Tree} {opts : List (List (ν × Tree))}
    (h : (tget (st x).path tab).toList = opts.map (optT nm)) :
    (DStep.pick (nm x) tab).exec m (byPath nm st) = opts.map fun o => byPath nm (upds st o) := by
  rw [DStep.exec, byPath_nm hnm, h, List.map_map]
  exact List.map_congr_left fun o _ => assignS_byPath hnm st o

theorem exec_op {m : ℕ} {st : ν → Tree} {x y z : ν} {φ : Tree} :
    (DStep.op (nm x) (nm y) (nm z) φ).exec m (byPath nm st) =
      [byPath nm (Function.update st z (tget (st y).path (tget (st x).path φ)))] := by
  rw [DStep.exec, byPath_nm hnm, byPath_nm hnm, update_byPath hnm]

theorem exec_bits {m : ℕ} {st : ν → Tree} {x y : ν} :
    (DStep.bits (nm x) (nm y)).exec m (byPath nm st) = if st x = .nil then [byPath nm st] else
      (allBits m).map fun u => byPath nm (Function.update st y (ofBits u.reverse)) := by
  rw [DStep.exec, byPath_nm hnm]
  split_ifs
  · rfl
  · exact List.map_congr_left fun u _ => update_byPath hnm st y _

end Names

section Tries


def mkTrie (l : List (List Bool × Tree)) : Tree := l.foldr (fun a t => tset a.1 a.2 t) .nil


noncomputable def trieOf {α : Type} [Fintype α] (code : α → List Bool) (f : α → Tree) : Tree :=
  mkTrie ((Finset.univ : Finset α).toList.map fun a => (code a, f a))

theorem tget_trieOf {α : Type} [Fintype α] {code : α → List Bool} (hc : Function.Injective code) (f : α → Tree) (a : α) :
    tget (code a) (trieOf code f) = f a := by
  have : ∀ l : List α, a ∈ l → tget (code a) (mkTrie (l.map fun a => (code a, f a))) = f a := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih =>
      intro h
      rw [List.map_cons, mkTrie, List.foldr_cons, tget_tset]
      by_cases hab : a = b
      · subst hab
        simp
      · rw [if_neg fun h => hab (hc h)]
        exact ih ((List.mem_cons.1 h).resolve_left hab)
  exact this _ (Finset.mem_toList.2 (Finset.mem_univ a))

theorem size_tset (p : List Bool) (v t : Tree) : (tset p v t).size ≤ t.size + v.size + 4 * p.length + 4 := by
  induction p generalizing t with
  | nil =>
    have := size_tl_le t
    simp only [tset, Tree.size, List.length_nil]
    omega
  | cons b p ih =>
    cases t with
    | nil =>
      cases b
      · have := ih .nil
        simp only [tset, tl_nil, hd_nil, Tree.size, List.length_cons] at this ⊢
        omega
      · have := ih .nil
        simp only [tset, tl_nil, hd_nil, Tree.size, List.length_cons] at this ⊢
        omega
    | cons a t =>
      cases t with
      | nil =>
        cases b
        · have := ih .nil
          simp only [tset, tl_nil, hd_nil, tl_cons, hd_cons, Tree.size, List.length_cons] at this ⊢
          omega
        · have := ih .nil
          simp only [tset, tl_nil, hd_nil, tl_cons, hd_cons, Tree.size, List.length_cons] at this ⊢
          omega
      | cons l r =>
        cases b
        · have := ih l
          simp only [tset, tl_cons, hd_cons, Tree.size, List.length_cons] at this ⊢
          omega
        · have := ih r
          simp only [tset, tl_cons, hd_cons, Tree.size, List.length_cons] at this ⊢
          omega

theorem size_trieOf_le {α : Type} [Fintype α] {code : α → List Bool} {f : α → Tree} {L s : ℕ}
    (hL : ∀ a, (code a).length ≤ L) (hs : ∀ a, (f a).size ≤ s) :
    (trieOf code f).size ≤ Fintype.card α * (s + 4 * L + 4) + 1 := by
  have : ∀ l : List α, (mkTrie (l.map fun a => (code a, f a))).size ≤ l.length * (s + 4 * L + 4) + 1 := by
    intro l
    induction l with
    | nil => simp [mkTrie, Tree.size]
    | cons a l ih =>
      have h1 := size_tset (code a) (f a) (mkTrie (l.map fun a => (code a, f a)))
      have h2 := hL a
      have h3 := hs a
      rw [List.map_cons, mkTrie, List.foldr_cons]
      rw [mkTrie] at ih h1
      simp only [List.length_cons]
      rw [add_mul, one_mul]
      omega
  have h := this (Finset.univ : Finset α).toList
  rwa [Finset.length_toList, Finset.card_univ] at h

end Tries

section Folds

variable {ν ι : Type} [DecidableEq ν] [DecidableEq ι]


theorem foldl_upds {own : ν → Option ι} {o : ι → List (ν × Tree)} {v : ν → Tree}
    (ho : ∀ i, ∀ a ∈ o i, own a.1 = some i ∧ a.2 = v a.1) (hall : ∀ i x, own x = some i → ∃ a ∈ o i, a.1 = x)
    (s : List ι) (st : ν → Tree) :
    s.foldl (fun st i => upds st (o i)) st = fun x => match own x with
      | none => st x
      | some i => if i ∈ s then v x else st x := by
  classical
  have one : ∀ (l : List (ν × Tree)) (st : ν → Tree) (x : ν), (∀ a ∈ l, a.2 = v a.1) →
      upds st l x = if ∃ a ∈ l, a.1 = x then v x else st x := by
    intro l
    induction l with
    | nil =>
      intro st x _
      simp [upds]
    | cons b l ih =>
      intro st x hl
      have h1 := ih (Function.update st b.1 b.2) x fun a ha => hl a (List.mem_cons_of_mem _ ha)
      rw [upds, List.foldl_cons]
      rw [upds] at h1
      rw [h1]
      by_cases hx : ∃ a ∈ l, a.1 = x
      · rw [if_pos hx, if_pos]
        obtain ⟨a, ha, h⟩ := hx
        exact ⟨a, List.mem_cons_of_mem _ ha, h⟩
      · rw [if_neg hx]
        by_cases hb : b.1 = x
        · rw [if_pos ⟨b, List.mem_cons_self, hb⟩, ← hb, Function.update_self]
          exact hl b List.mem_cons_self
        · rw [if_neg, Function.update_of_ne (Ne.symm hb)]
          rintro ⟨a, ha, h⟩
          rcases List.mem_cons.1 ha with rfl | ha
          · exact hb h
          · exact hx ⟨a, ha, h⟩
  induction s generalizing st with
  | nil =>
    funext x
    cases own x <;> simp
  | cons i s ih =>
    rw [List.foldl_cons, ih]
    funext x
    have h1 := one (o i) st x fun a ha => (ho i a ha).2
    have h2 : (∃ a ∈ o i, a.1 = x) ↔ own x = some i := by
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact (ho i a ha).1
      · exact hall i x
    rw [h1]
    cases hx : own x with
    | none => simp [h2, hx]
    | some j =>
      by_cases hj : j = i
      · subst hj
        simp [h2, hx]
      · have : ¬ (some j = some i) := fun h => hj (Option.some.inj h)
        simp only [h2, hx, this, if_false, List.mem_cons, hj, false_or]

end Folds

end Nc.Dl
end
/- Source module Nc.Cut.Play. -/
section
set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {A U W O : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]
  [Fintype W] [DecidableEq W] [Fintype O]







def Contents (h0 h1 : U → A) (e : W) (Seen : Finset U) : Finset (A → U → W) :=
  univ.filter fun y => ∀ a id, ¬ (id ∈ Seen ∧ Holds h0 h1 a id) → y a id = e


def Agree (h0 h1 : U → A) (Cur : Finset U) (y : A → U → W) : Prop :=
  ∀ id ∈ Cur, y (h0 id) id = y (h1 id) id

instance (h0 h1 : U → A) (Cur : Finset U) (y : A → U → W) : Decidable (Agree h0 h1 Cur y) := by
  unfold Agree; infer_instance


def posVal (h0 h1 : U → A) (e : W) (Seen Cur : Finset U) (E : (A → U → W) → F) : F :=
  ∑ y ∈ Contents h0 h1 e Seen, if Agree h0 h1 Cur y then E y else 0


def ext (h0 h1 : U → A) (New : Finset U) (y : A → U → W) (z : U → W) : A → U → W := fun a id =>
  if id ∈ New ∧ Holds h0 h1 a id then z id else y a id








end Nc
end
/- Source module Nc.Cut.Groups. -/
section
set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {A U W G : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]
  [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G]













theorem mem_common_iff {e : W} {New : Finset U} {z : U → W} :
    z ∈ Common e New ↔ ∀ id, id ∉ New → z id = e := by simp [Common]








end Nc
end
/- Source module Nc.Grp.Steps. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset

variable {F : Type*} [CommRing F] {Ce W : Type*} [Fintype Ce] [DecidableEq Ce] [Fintype W] [DecidableEq W]


def ovr (wr : Finset Ce) (v σ : Ce → W) : Ce → W := fun c => if c ∈ wr then v c else σ c



structure WStep (F Ce W : Type*) where
  
  ι : Type
  
  Om : Finset ι
  
  wr : Finset Ce
  
  w : ι → (Ce → W) → F
  
  v : ι → (Ce → W) → Ce → W
  
  rd : Finset Ce

namespace WStep


def phi (s : WStep F Ce W) (y : Ce → W) : F :=
  ∑ ω ∈ s.Om, if ∀ c ∈ s.wr, y c = s.v ω y c then s.w ω y else 0


def wrs : List (WStep F Ce W) → Finset Ce
  | [] => ∅
  | s :: l => s.wr ∪ wrs l


def exec : List (WStep F Ce W) → ((Ce → W) → F) → (Ce → W) → F
  | [], G, σ => G σ
  | s :: l, G, σ => ∑ ω ∈ s.Om, s.w ω σ * exec l G (ovr s.wr (s.v ω σ) σ)


def Seq : List (WStep F Ce W) → Prop
  | [] => True
  | s :: l => Disjoint s.wr (wrs l) ∧ (∀ ω ∈ s.Om, ∀ y y' : Ce → W, (∀ c, c ∉ s.wr ∪ wrs l → y c = y' c) →
      s.w ω y = s.w ω y' ∧ ∀ c ∈ s.wr, s.v ω y c = s.v ω y' c) ∧ Seq l









end WStep

end Nc.Grp
end
/- Source module Nc.Tape.Rep. -/
section
namespace Nc

open Finset Matrix

variable {F : Type*} [CommRing F] {Ω : Type*}


abbrev Series (F Ω : Type*) := List Ω → F

namespace Series


def mul (f g : Series F Ω) : Series F Ω := fun o =>
  ∑ k ∈ range (o.length + 1), f (o.take k) * g (o.drop k)


def one : Series F Ω := fun o => if o = [] then 1 else 0


def kstar (f : Series F Ω) : Series F Ω
  | [] => 1
  | a :: o => ∑ k ∈ range (o.length + 1), f (a :: o.take k) * kstar f (o.drop k)
  termination_by o => o.length
  decreasing_by simp

theorem kstar_nil (f : Series F Ω) : kstar f [] = 1 := by rw [kstar]

theorem kstar_cons (f : Series F Ω) (a : Ω) (o : List Ω) : kstar f (a :: o) =
    ∑ k ∈ range (o.length + 1), f (a :: o.take k) * kstar f (o.drop k) := by rw [kstar]

end Series

theorem elim_dot {α β : Type*} [Fintype α] [Fintype β] (a c : α → F) (b d : β → F) :
    Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by simp [dotProduct]


structure Rep (F Ω Q : Type*) where
  
  lam : Q → F
  
  mu : Ω → Matrix Q Q F
  
  gam : Q → F

namespace Rep

variable {Q Q₁ Q₂ : Type*} [Fintype Q] [Fintype Q₁] [Fintype Q₂]


def tail (r : Rep F Ω Q) : List Ω → Q → F
  | [] => r.gam
  | a :: o => r.mu a *ᵥ tail r o


def series (r : Rep F Ω Q) : Series F Ω := fun o => r.lam ⬝ᵥ r.tail o


def add (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) : Rep F Ω (Q₁ ⊕ Q₂) where
  lam := Sum.elim r₁.lam r₂.lam
  mu a := Matrix.fromBlocks (r₁.mu a) 0 0 (r₂.mu a)
  gam := Sum.elim r₁.gam r₂.gam

theorem add_tail (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) (o : List Ω) :
    (r₁.add r₂).tail o = Sum.elim (r₁.tail o) (r₂.tail o) := by
  induction o with
  | nil => rfl
  | cons a o ih =>
    simp only [tail, ih]
    simp [add, Matrix.fromBlocks_mulVec]

theorem add_series (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) (o : List Ω) :
    (r₁.add r₂).series o = r₁.series o + r₂.series o := by
  rw [series, add_tail]
  simp [series, add]


def mul (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) : Rep F Ω (Q₁ ⊕ Q₂) where
  lam := Sum.elim r₁.lam ((r₁.lam ⬝ᵥ r₁.gam) • r₂.lam)
  mu a := Matrix.fromBlocks (r₁.mu a) (Matrix.vecMulVec (r₁.mu a *ᵥ r₁.gam) r₂.lam) 0 (r₂.mu a)
  gam := Sum.elim 0 r₂.gam

theorem mul_tail (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) (o : List Ω) :
    (r₁.mul r₂).tail o = Sum.elim
      (∑ k ∈ range o.length, (r₂.series (o.drop (k + 1))) • r₁.tail (o.take (k + 1))) (r₂.tail o) := by
  induction o with
  | nil => simp [tail, mul]
  | cons a o ih =>
    rw [tail, ih]
    simp only [mul, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add, Sum.elim_comp_inl,
      Sum.elim_comp_inr]
    congr 1
    rw [List.length_cons, Finset.sum_range_succ']
    congr 1
    · rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [tail, Matrix.mulVec_smul]
    · ext i
      simp [tail, series, Matrix.vecMulVec_mulVec, mul_comm]

theorem mul_series (r₁ : Rep F Ω Q₁) (r₂ : Rep F Ω Q₂) (o : List Ω) :
    (r₁.mul r₂).series o = Series.mul r₁.series r₂.series o := by
  rw [series, mul_tail, Series.mul, Finset.sum_range_succ']
  have e : (r₁.mul r₂).lam = Sum.elim r₁.lam ((r₁.lam ⬝ᵥ r₁.gam) • r₂.lam) := rfl
  rw [e, elim_dot, dotProduct_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [series, mul_comm]
  · simp [series, tail]


def star (r : Rep F Ω Q) : Rep F Ω (Unit ⊕ Q) where
  lam := Sum.elim 1 0
  mu a := Matrix.fromBlocks
    (Matrix.of fun _ _ => r.lam ⬝ᵥ (r.mu a *ᵥ r.gam)) (Matrix.of fun _ q => (r.lam ᵥ* r.mu a) q)
    (Matrix.of fun q _ => (r.mu a *ᵥ r.gam) q) (r.mu a)
  gam := Sum.elim 1 0

theorem star_tail (r : Rep F Ω Q) (o : List Ω) :
    r.star.tail o = Sum.elim (fun _ => Series.kstar r.series o)
      (∑ k ∈ range o.length, (Series.kstar r.series (o.drop (k + 1))) • r.tail (o.take (k + 1))) := by
  induction o with
  | nil => ext q; rcases q with q | q <;> simp [tail, star, Series.kstar_nil]
  | cons a o ih =>
    rw [tail, ih]
    have h2 : ∑ k ∈ range (a :: o).length, (Series.kstar r.series ((a :: o).drop (k + 1))) •
        r.tail ((a :: o).take (k + 1)) = r.mu a *ᵥ (∑ k ∈ range o.length,
          (Series.kstar r.series (o.drop (k + 1))) • r.tail (o.take (k + 1))) +
          (Series.kstar r.series o) • (r.mu a *ᵥ r.gam) := by
      rw [List.length_cons, Finset.sum_range_succ']
      congr 1
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [tail, Matrix.mulVec_smul]
    simp only [star, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]
    congr 1
    · ext _
      rw [Series.kstar_cons, Finset.sum_range_succ']
      simp only [Pi.add_apply]
      rw [add_comm]
      congr 1
      · have : ∀ v : Q → F, ((Matrix.of fun (_ : Unit) q => (r.lam ᵥ* r.mu a) q) *ᵥ v) () =
            r.lam ⬝ᵥ (r.mu a *ᵥ v) := by
          intro v
          rw [Matrix.dotProduct_mulVec]
          simp [Matrix.mulVec, dotProduct]
        rw [this, Matrix.mulVec_sum, dotProduct_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [series, tail, Matrix.mulVec_smul, mul_comm]
      · simp [series, tail, Matrix.mulVec, dotProduct]
    · rw [h2, add_comm]
      congr 1
      ext q
      simp [Matrix.mulVec, dotProduct, mul_comm]

theorem star_series (r : Rep F Ω Q) (o : List Ω) : r.star.series o = Series.kstar r.series o := by
  rw [series, star_tail]
  have e : r.star.lam = Sum.elim (1 : Unit → F) (0 : Q → F) := rfl
  rw [e, elim_dot]
  simp [dotProduct]

end Rep

end Nc
end
/- Source module Nc.Tape.Rat. -/
section
set_option linter.unusedSimpArgs false

namespace Nc

open Finset Matrix

variable {F : Type*} [CommRing F] {Ω : Type*}


def RatLe (n : ℕ) (f : Series F Ω) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (r : Rep F Ω Q), Fintype.card Q ≤ n ∧ r.series = f

namespace RatLe

theorem mono {n m : ℕ} {f : Series F Ω} (h : RatLe n f) (hm : n ≤ m) : RatLe m f := by
  obtain ⟨Q, _, r, h1, h2⟩ := h
  exact ⟨Q, _, r, h1.trans hm, h2⟩

theorem zero : RatLe 0 (0 : Series F Ω) :=
  ⟨Empty, inferInstance, ⟨0, 0, 0⟩, by simp, by ext o; simp [Rep.series]⟩

theorem add {n m : ℕ} {f g : Series F Ω} (hf : RatLe n f) (hg : RatLe m g) : RatLe (n + m) (f + g) := by
  obtain ⟨Q₁, _, r₁, h1, rfl⟩ := hf
  obtain ⟨Q₂, _, r₂, h2, rfl⟩ := hg
  refine ⟨Q₁ ⊕ Q₂, inferInstance, r₁.add r₂, by simp; omega, ?_⟩
  ext o
  exact Rep.add_series r₁ r₂ o

theorem mul {n m : ℕ} {f g : Series F Ω} (hf : RatLe n f) (hg : RatLe m g) :
    RatLe (n + m) (Series.mul f g) := by
  obtain ⟨Q₁, _, r₁, h1, rfl⟩ := hf
  obtain ⟨Q₂, _, r₂, h2, rfl⟩ := hg
  refine ⟨Q₁ ⊕ Q₂, inferInstance, r₁.mul r₂, by simp; omega, ?_⟩
  ext o
  exact Rep.mul_series r₁ r₂ o

theorem kstar {n : ℕ} {f : Series F Ω} (hf : RatLe n f) : RatLe (n + 1) (Series.kstar f) := by
  obtain ⟨Q₁, _, r₁, h1, rfl⟩ := hf
  refine ⟨Unit ⊕ Q₁, inferInstance, r₁.star, by simp; omega, ?_⟩
  ext o
  exact Rep.star_series r₁ o

theorem smul {n : ℕ} {f : Series F Ω} (c : F) (hf : RatLe n f) : RatLe n (c • f) := by
  obtain ⟨Q, _, r, h1, rfl⟩ := hf
  refine ⟨Q, _, ⟨c • r.lam, r.mu, r.gam⟩, h1, ?_⟩
  ext o
  have : ∀ o, (⟨c • r.lam, r.mu, r.gam⟩ : Rep F Ω Q).tail o = r.tail o := by
    intro o
    induction o with
    | nil => rfl
    | cons a o ih => simp [Rep.tail, ih]
  simp [Rep.series, this]

theorem one : RatLe 1 (Series.one : Series F Ω) := by
  refine ⟨Unit, inferInstance, ⟨1, 0, 1⟩, by simp, ?_⟩
  ext o
  cases o with
  | nil => simp [Rep.series, Rep.tail, Series.one, dotProduct]
  | cons a o => simp [Rep.series, Rep.tail, Series.one]

theorem sum {ι : Type*} (s : Finset ι) (n : ι → ℕ) (f : ι → Series F Ω) (h : ∀ i ∈ s, RatLe (n i) (f i)) :
    RatLe (∑ i ∈ s, n i) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end RatLe


def Series.letter [DecidableEq Ω] (a : Ω) : Series F Ω := fun o => if o = [a] then 1 else 0

theorem RatLe.letter [DecidableEq Ω] (a : Ω) : RatLe 2 (Series.letter a : Series F Ω) := by
  refine ⟨Bool, inferInstance, ⟨fun q => if q then 0 else 1,
    fun b => Matrix.of fun q q' => if b = a ∧ q = false ∧ q' = true then 1 else 0,
    fun q => if q then 1 else 0⟩, by simp, ?_⟩
  ext o
  match o with
  | [] => simp [Rep.series, Rep.tail, Series.letter, dotProduct]
  | [b] =>
    by_cases h : b = a <;> simp [Rep.series, Rep.tail, Series.letter, dotProduct, Matrix.mulVec, h]
  | b :: c :: o =>
    simp [Rep.series, Rep.tail, Series.letter, dotProduct, Matrix.mulVec]




end Nc
end
/- Source module Nc.Tape.Hat. -/
section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Fintype Γ] [DecidableEq Γ]

@[simp] theorem proj_nil : proj ([] : List (Z × Γ)) = fun _ => [] := rfl



theorem proj_cons (a : Z × Γ) (o : List (Z × Γ)) (z : Z) :
    proj (a :: o) z = if a.1 = z then a.2 :: proj o z else proj o z := by
  by_cases h : a.1 = z <;> simp [proj, h]

theorem sum_length_proj (o : List (Z × Γ)) : ∑ z, (proj o z).length = o.length := by
  induction o with
  | nil => simp
  | cons a o ih =>
    have : ∀ z, (proj (a :: o) z).length = (proj o z).length + if a.1 = z then 1 else 0 := by
      intro z
      rw [proj_cons]
      by_cases h : a.1 = z <;> simp [h]
    simp only [this, Finset.sum_add_distrib, ih]
    simp


noncomputable def fib (v : Z → List Γ) : Finset (List (Z × Γ)) :=
  (show {o : List (Z × Γ) | proj o = v}.Finite from
    (List.finite_length_eq (Z × Γ) (∑ z, (v z).length)).subset (by
      rintro o rfl
      exact (sum_length_proj o).symm)).toFinset




noncomputable def hat (f : Series F (Z × Γ)) (v : Z → List Γ) : F := ∑ o ∈ fib v, f o


def anti (v : Z → List Γ) : Finset ((Z → List Γ) × (Z → List Γ)) :=
  (Fintype.piFinset fun z => range ((v z).length + 1)).image fun k =>
    (fun z => (v z).take (k z), fun z => (v z).drop (k z))














def Series.ne (f : Series F (Z × Γ)) : Series F (Z × Γ) := fun o => if o = [] then 0 else f o








end Nc
end
/- Source module Nc.Tape.Loop. -/
section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Fintype Γ] [DecidableEq Γ]


def Series.word {Ω : Type*} [DecidableEq Ω] (w : List Ω) : Series F Ω := fun o => if o = w then 1 else 0

theorem RatLe.word {Ω : Type*} [DecidableEq Ω] (w : List Ω) :
    RatLe (2 * w.length + 1) (Series.word w : Series F Ω) := by
  induction w with
  | nil => exact RatLe.one
  | cons a w ih =>
    have h := (RatLe.letter (F := F) a).mul ih
    have e : Series.mul (Series.letter a) (Series.word w) = (Series.word (a :: w) : Series F Ω) := by
      funext o
      cases o with
      | nil => simp [Series.mul, Series.letter, Series.word]
      | cons b o =>
        rw [Series.mul, List.length_cons, Finset.sum_range_succ', Finset.sum_range_succ']
        have : ∀ k, Series.letter (F := F) a ((b :: o).take (k + 1 + 1)) *
            Series.word w ((b :: o).drop (k + 1 + 1)) = if k + 1 ≤ o.length then 0 else
            Series.letter (F := F) a ((b :: o).take (k + 1 + 1)) *
            Series.word w ((b :: o).drop (k + 1 + 1)) := by
          intro k
          split_ifs with hk
          · obtain ⟨c, o, rfl⟩ : ∃ c o', o = c :: o' := by
              cases o with
              | nil => simp at hk
              | cons c o => exact ⟨c, o, rfl⟩
            simp [Series.letter]
          · rfl
        rw [Finset.sum_congr rfl fun k _ => this k]
        rw [Finset.sum_congr rfl (g := fun _ => (0 : F)) (fun k hk => by
          rw [if_pos (by have := Finset.mem_range.1 hk; omega)])]
        simp only [Finset.sum_const_zero, zero_add]
        by_cases hb : b = a
        · subst hb
          by_cases ho : o = w <;> simp [Series.letter, Series.word, ho]
        · simp [Series.letter, Series.word, hb]
    rw [e] at h
    exact h.mono (by simp; omega)



section Loop

variable {κ : Type*} [Fintype κ] [DecidableEq κ]


def Series.body (wd : κ → List (Z × Γ)) (c : κ → F) : Series F (Z × Γ) :=
  ∑ k, c k • Series.word (wd k)

theorem RatLe.body (wd : κ → List (Z × Γ)) (c : κ → F) :
    RatLe (∑ k, (2 * (wd k).length + 1)) (Series.body wd c) :=
  RatLe.sum _ _ _ fun k _ => (RatLe.word (wd k)).smul (c k)



end Loop

section Phases

end Phases

end Nc
end
/- Source module Nc.Tape.Task. -/
section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]


def tup (W : S → List Γ) (u : J → List Γ) : Ch S J → List Γ
  | .tp s _ => W s
  | .inp j => u j


noncomputable def contents (S Γ : Type*) [Fintype S] [DecidableEq S] [Fintype Γ] (t : ℕ) :
    Finset (S → List Γ) :=
  open Classical in
  (Fintype.piFinset fun _ => (List.finite_length_le Γ t).toFinset).filter fun W => ∑ s, (W s).length ≤ t




noncomputable def val (t : ℕ) (P : Series F (Ch S J × Γ)) (u : J → List Γ) : F :=
  ∑ W ∈ contents S Γ t, hat P (tup W u)


def Bdd (t : ℕ) (P : Series F (Ch S J × Γ)) (u : J → List Γ) : Prop :=
  ∀ W, hat P (tup W u) ≠ 0 → ∑ s, (W s).length ≤ t



end Nc
end
/- Source module Nc.Tape.Refine. -/
section
namespace Nc

variable {Γ : Type*} {K : ℕ}




theorem cat_succ (A : Fin (K + 1) → List Γ) : cat A = A 0 ++ cat fun i => A i.succ := by
  simp [cat, List.ofFn_succ]

theorem cat_eq_nil {A : Fin K → List Γ} : cat A = [] ↔ ∀ i, A i = [] := by
  induction K with
  | zero => simp [cat]
  | succ K ih =>
    rw [cat_succ, List.append_eq_nil_iff, ih, Fin.forall_fin_succ]

theorem cat_eq_cons {A : Fin K → List Γ} {a : Γ} {W : List Γ} (h : cat A = a :: W) :
    ∃ i l, (∀ j < i, A j = []) ∧ A i = a :: l ∧ cat (Function.update A i l) = W := by
  induction K with
  | zero => simp [cat] at h
  | succ K ih =>
    rw [cat_succ] at h
    rcases hA : A 0 with _ | ⟨b, l⟩
    · rw [hA, List.nil_append] at h
      obtain ⟨i, l, h1, h2, h3⟩ := ih h
      refine ⟨i.succ, l, ?_, h2, ?_⟩
      · intro j hj
        refine Fin.cases (fun _ => hA) (fun j hj => h1 j (by simpa using hj)) j hj
      · rw [cat_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm, hA, List.nil_append, ← h3]
        congr 1
        funext j
        by_cases e : j = i
        · subst e; simp
        · rw [Function.update_of_ne e, Function.update_of_ne (fun h => e (Fin.succ_injective _ h))]
    · rw [hA, List.cons_append, List.cons.injEq] at h
      refine ⟨0, l, fun j hj => absurd hj (Fin.not_lt_zero j), by rw [hA, h.1], ?_⟩
      rw [cat_succ, Function.update_self, ← h.2]
      congr 2

theorem cat_of_cons {A : Fin K → List Γ} {a : Γ} {i : Fin K} {l : List Γ} (h1 : ∀ j < i, A j = [])
    (h2 : A i = a :: l) : cat A = a :: cat (Function.update A i l) := by
  induction K with
  | zero => exact i.elim0
  | succ K ih =>
    rw [cat_succ, cat_succ]
    by_cases e : i = 0
    · subst e
      rw [h2, Function.update_self, List.cons_append]
      congr 3
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 e
      rw [Function.update_of_ne (Ne.symm e), h1 0 (Fin.succ_pos i'), List.nil_append, List.nil_append]
      rw [ih (A := fun j => A j.succ) (i := i') (fun j hj => h1 _ (by simpa using hj)) h2]
      congr 2
      funext j
      by_cases e' : j = i'
      · subst e'; simp
      · rw [Function.update_of_ne e', Function.update_of_ne (fun h => e' (Fin.succ_injective _ h))]


def Stair (X : Fin K → Fin K → List Γ) : Prop :=
  ∀ a a' b b', X a b ≠ [] → X a' b' ≠ [] → a < a' → b ≤ b'


structure IsRef (A B : Fin K → List Γ) (X : Fin K → Fin K → List Γ) : Prop where
  stair : Stair X
  row : ∀ a, cat (X a) = A a
  col : ∀ b, cat (fun a => X a b) = B b


def upd (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) : Fin K → Fin K → List Γ :=
  fun a' b' => if a' = a ∧ b' = b then l else X a' b'

theorem upd_row (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) :
    upd X a b l a = Function.update (X a) b l := by
  funext b'
  by_cases e : b' = b
  · subst e; simp [upd]
  · simp [upd, e]

theorem upd_row_ne (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) {a' : Fin K} (h : a' ≠ a) :
    upd X a b l a' = X a' := by
  funext b'; simp [upd, h]

theorem upd_col (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) :
    (fun a' => upd X a b l a' b) = Function.update (fun a' => X a' b) a l := by
  funext a'
  by_cases e : a' = a
  · subst e; simp [upd]
  · simp [upd, e]

theorem upd_col_ne (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) {b' : Fin K} (h : b' ≠ b) :
    (fun a' => upd X a b l a' b') = fun a' => X a' b' := by
  funext a'; simp [upd, h]


theorem IsRef.first {A B : Fin K → List Γ} {X : Fin K → Fin K → List Γ} (h : IsRef A B X) {a : Fin K}
    {c : Γ} {l : List Γ} (h1 : ∀ j < a, A j = []) (h2 : A a = c :: l) :
    ∃ b x m, X a b = c :: x ∧ (∀ j < b, B j = []) ∧ B b = c :: m ∧
      IsRef (Function.update A a l) (Function.update B b m) (upd X a b x) := by
  obtain ⟨b, x, hx1, hx2, hx3⟩ := cat_eq_cons ((h.row a).trans h2)
  have hrow : ∀ j < a, ∀ b', X j b' = [] := fun j hj b' => cat_eq_nil.1 ((h.row j).trans (h1 j hj)) b'
  have hcol : ∀ j < b, ∀ a', X a' j = [] := by
    intro j hj a'
    rcases lt_trichotomy a' a with h' | h' | h'
    · exact hrow a' h' j
    · subst h'; exact hx1 j hj
    · by_contra hne
      exact absurd (h.stair a a' b j (by simp [hx2]) hne h') (not_le.2 hj)
  have hB := cat_of_cons (A := fun a' => X a' b) (i := a) (l := x) (fun j hj => hrow j hj b) hx2
  rw [h.col b] at hB
  refine ⟨b, x, _, hx2, fun j hj => ?_, hB, ?_, ?_, ?_⟩
  · rw [← h.col j]; exact cat_eq_nil.2 fun a' => hcol j hj a'
  · intro a₁ a₂ b₁ b₂ n1 n2 hlt
    have key : ∀ a' b', upd X a b x a' b' ≠ [] → X a' b' ≠ [] := by
      intro a' b' hn
      by_cases e : a' = a ∧ b' = b
      · obtain ⟨rfl, rfl⟩ := e; simp [hx2]
      · simpa [upd, e] using hn
    exact h.stair _ _ _ _ (key _ _ n1) (key _ _ n2) hlt
  · intro a'
    by_cases e : a' = a
    · subst e; rw [upd_row, Function.update_self, hx3]
    · rw [upd_row_ne _ _ _ _ e, Function.update_of_ne e, h.row]
  · intro b'
    by_cases e : b' = b
    · subst e; rw [upd_col, Function.update_self]
    · rw [upd_col_ne _ _ _ _ e, Function.update_of_ne e, h.col]



theorem IsRef.unique {A B : Fin K → List Γ} {X Y : Fin K → Fin K → List Γ} (h : IsRef A B X)
    (h' : IsRef A B Y) : X = Y := by
  generalize hW : cat A = W
  induction W generalizing A B X Y with
  | nil =>
    rw [cat_eq_nil] at hW
    funext a b
    rw [cat_eq_nil.1 ((h.row a).trans (hW a)) b, cat_eq_nil.1 ((h'.row a).trans (hW a)) b]
  | cons c W ih =>
    obtain ⟨a, l, h1, h2, h3⟩ := cat_eq_cons hW
    obtain ⟨b, x, m, hx, hb, hB, href⟩ := h.first h1 h2
    obtain ⟨b', y, m', hy, hb', hB', href'⟩ := h'.first h1 h2
    have eb : b = b' := by
      rcases lt_trichotomy b b' with e | e | e
      · rw [hb' b e] at hB; simp at hB
      · exact e
      · rw [hb b' e] at hB'; simp at hB'
    subst eb
    rw [hB] at hB'
    obtain rfl : m = m' := by simpa using hB'
    have := ih href href' h3
    funext a' b'
    by_cases e : a' = a ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := e
      have h4 := congrFun (congrFun this a') b'
      simp only [upd, and_self, if_true] at h4
      rw [hx, hy, h4]
    · have h4 := congrFun (congrFun this a') b'
      simpa [upd, e] using h4



end Nc
end
/- Source module Nc.Cut.Blocks. -/
section
set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Γ S J Q : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype J] [DecidableEq J] [Fintype Q] [DecidableEq Q]
























end Nc
end
/- Source module Nc.Cut.Units. -/
section
set_option linter.unusedSectionVars false

namespace Nc

variable (ub : ℕ)













variable {ub}



theorem unitsOf_eq_none {L : List Bool} {k : ℕ} : unitsOf ub L k = none ↔ ucount ub L ≤ k := by
  simp [unitsOf]

section Segments

variable {Γ : Type*} {c : ℕ}








end Segments

end Nc
end
/- Source module Nc.LowDegree. -/
section
namespace Nc

open Finset

section Circuits

variable {F : Type*} [CommSemiring F] {σ : Type*}


def IsStep (l : ℕ → MvPolynomial σ F) (k : ℕ) : Prop :=
  (∃ i : σ, l k = MvPolynomial.X i) ∨ (∃ a : F, l k = MvPolynomial.C a) ∨
    (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)


def Computes (p : MvPolynomial σ F) (s : ℕ) : Prop :=
  ∃ l : ℕ → MvPolynomial σ F, (∀ k < s, IsStep l k) ∧ ∃ k < s, l k = p

end Circuits

variable {F : Type*} [Field F] {σ : Type*} {s : ℕ}

section Proof


noncomputable def line (u : σ → F) : MvPolynomial σ F →ₐ[F] Polynomial F :=
  MvPolynomial.aeval fun l => Polynomial.C (u l) * Polynomial.X



end Proof

end Nc
end
/- Source module Nc.Cut.Rows. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

section Rows

variable {Γ : Type} {A : ℕ}


def ValidRow (ρ : Fin A → RowData A) (p : Fin A) : Prop :=
  if (ρ p).1 then (ρ p).2.1.1 = prevHi ρ p ∧ (ρ p).2.2.1 = prevHi ρ p
  else prevHi ρ p ≤ (ρ p).2.1.1 ∧ (ρ p).2.1 ≤ (ρ p).2.2





theorem RowOk.flag {d : RowData A} {X : Fin A → List Γ} (h : RowOk d X) {b : Fin A} (hb : X b ≠ []) :
    d.1 = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  rw [RowOk, if_pos hc] at h
  exact hb (h b)





noncomputable def hiBefore (X : Fin A → Fin A → List Γ) (q : ℕ) : ℕ :=
  open Classical in (univ.filter fun z : Fin A × Fin A => z.1.1 < q ∧ X z.1 z.2 ≠ []).sup fun z => z.2.1








where
  row_eq {X : Fin A → Fin A → List Γ} {ρ ρ' : Fin A → RowData A} (h : ∀ p, ValidRow ρ p)
      (h' : ∀ p, ValidRow ρ' p) (hX : ∀ p, RowOk (ρ p) (X p)) (hX' : ∀ p, RowOk (ρ' p) (X p)) {p : Fin A}
      (hp : prevHi ρ p = prevHi ρ' p) : ρ p = ρ' p := by
    have v := h p
    have v' := h' p
    have r := hX p
    have r' := hX' p
    rw [ValidRow] at v v'
    by_cases he : ∀ b, X p b = []
    · have f : (ρ p).1 = true := by
        by_contra hc
        rw [RowOk, if_neg hc] at r
        exact r.1 (he _)
      have f' : (ρ' p).1 = true := by
        by_contra hc
        rw [RowOk, if_neg hc] at r'
        exact r'.1 (he _)
      rw [if_pos f] at v
      rw [if_pos f'] at v'
      refine Prod.ext (f.trans f'.symm) (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
      · rw [v.1, v'.1, hp]
      · rw [v.2, v'.2, hp]
    · push Not at he
      obtain ⟨b, hb⟩ := he
      have f := r.flag hb
      have f' := r'.flag hb
      rw [RowOk, if_neg (by simp [f])] at r
      rw [RowOk, if_neg (by simp [f'])] at r'
      refine Prod.ext (f.trans f'.symm) (Prod.ext ?_ ?_)
      · exact le_antisymm (r.2.2 _ r'.1).1 (r'.2.2 _ r.1).1
      · exact le_antisymm (r'.2.2 _ r.2.1).2 (r.2.2 _ r'.2.1).2

end Rows

section Strings

variable {Γ S : Type} [Fintype S] [DecidableEq S]







variable {c : ℕ} {cb : Option Γ → Fin c → Bool}





end Strings

end Nc.Cut
end
/- Source module Nc.Cut.StartA. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

section Cat

variable {Γ : Type}









theorem length_parts_le {K : ℕ} (ℓ : ℕ) (u : List Γ) (κ : Fin K) : (parts ℓ u κ).length ≤ ℓ := by
  simp [parts]

end Cat

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {K : ℕ} (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ)




section Party

variable {T} {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {R C : Option S → Fin (K + K) → List Γ}

open Classical in
theorem partyW_block (κ : Fin K) : partyW mu T q x (Fin.castAdd K κ) R C =
    if ∀ b, R none b = [] then blockW mu T (q κ.castSucc) (q κ.succ) (vec R C) else 0 := by
  rw [partyW, Fin.addCases_left]

open Classical in
theorem partyW_input (κ : Fin K) : partyW mu T q x (Fin.natAdd K κ) R C =
    if (∀ s b, R (some s) b = []) ∧ (∀ s b, C s b = []) ∧ cat (R none) = x κ then 1 else 0 := by
  rw [partyW, Fin.addCases_right]

variable {mu}




end Party


noncomputable def segW (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (X : Option S → Fin (K + K) → Fin (K + K) → List Γ) : F :=
  ∏ p, partyW mu T q x p (fun s b => X s p b) (fun s b => X s b p)


noncomputable def segs (Γ S : Type) [Fintype Γ] [Fintype S] [DecidableEq S] (K T : ℕ) :
    Finset (Option S → Fin (K + K) → Fin (K + K) → List Γ) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Fintype.piFinset fun _ => wordsLe Γ T



variable {mu T}






end Nc.Cut
end
/- Source module Nc.Cut.Codes. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

section Codes

variable {F : Type*} [CommRing F] {I : Type*} [Fintype I] {A B : I → Type*}
  [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] {Zg Zh : Type*} [Fintype Zg] [DecidableEq Zg] [Fintype Zh]
  [DecidableEq Zh] (ca : (i : I) → A i → Zg) (cb : (i : I) → B i → Zh)

variable {ca cb} (hca : Function.Injective fun p : Σ i, A i => ca p.1 p.2)
  (hcb : Function.Injective fun p : Σ i, B i => cb p.1 p.2)

include hca hcb

end Codes

section Strings

variable {I : Type} {lam : ℕ} (lab : I → Fin lam → Bool)





variable {lab}








def codeWord (lab : I → Fin lam → Bool) (len : I → ℕ) (ub U : ℕ) {B : ℕ} (i : Fin B → I)
    (g : ∀ k, Fin (len (i k)) → Bool) : Fin U → UW ub := fun k => unitsOf ub (sideString lab len i g) k



end Strings

end Nc.Cut
end
/- Source module Nc.Cut.StartB. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset





variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {K U0 E U1 : ℕ} {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {ub : ℕ} {c : ℕ}
  {cb : Option Γ → Fin c → Bool}

end Nc.Cut
end
/- Source module Nc.G.Contract. -/
section
set_option linter.unusedSectionVars false

namespace Nc.G

open Finset

section Contract

variable {F : Type} [CommRing F] {Ro Cn ι : Type} [Fintype Ro] [DecidableEq Ro] [Fintype Cn] [DecidableEq Cn]
  [Fintype ι] {S : ι → Cn → Type} [∀ i ν, Fintype (S i ν)] {Z : Type} [Fintype Z] (c d : Cn → Ro)
  (code : (ν : Cn) → (i : ι) → S i ν → Z)

open Classical in

noncomputable def codeTab (p : Ro) (G : (i : ι) → ((ν : {ν // c ν = p ∨ d ν = p}) → S i ν) → F) (z : Cn → Z) : F :=
  ∑ i, ∑ g : (ν : {ν // c ν = p ∨ d ν = p}) → S i ν, if ∀ ν : {ν // c ν = p ∨ d ν = p}, code ν i (g ν) = z ν then G i g else 0




variable {c d code}



end Contract

section Pow

variable {F : Type} [CommRing F] (L : Law F)






end Pow

end Nc.G
end
/- Source module Nc.G.Move. -/
section
set_option linter.unusedSectionVars false

namespace Nc.G

open Finset Nc.Cut

variable {F : Type} [CommRing F] {A A' E U0 U1 ub : ℕ} {M : Sys F (A + A') E}

section Slots

variable {N : Type} [Fintype N] [DecidableEq N]
















end Slots

section Role




theorem role_ne_zero {x : Fin E} {p : (M.kind x).Ro} {t : ℕ} {ids : (M.kind x).SlAt p → List (Uid A U0 M.N U1)}
    {o : M.N → Fin U1} {y : Uid A U0 M.N U1 → UW ub} (h : role M x p t ids o y ≠ 0) :
    (∀ e, ∀ id ∈ ids e, y id ≠ none) ∧ ∃ (i : Fin (t * ub) → (M.kind x).I)
      (g : ∀ k, ∀ ν : (M.kind x).CnAt p, Fin ((M.kind x).len (i k) ν) → Bool),
      (∀ ν : (M.kind x).CnAt p, ChOk ⟨x, ν.1⟩ (o ⟨x, ν.1⟩).1
        (chString (M.kind x).lab (fun j => (M.kind x).len j ν) i fun k => g k ν) y) ∧
      ∏ k : Fin (t * ub), (M.kind x).tab p (i k) (fun e => (slotBits t (ids e) y).getD k false) (g k) ≠ 0 := by
  classical
  rw [role] at h
  split_ifs at h with hy
  swap
  · exact absurd rfl h
  obtain ⟨i, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨g, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at h with hc
  · exact ⟨hy, i, g, hc, h⟩
  · exact absurd rfl h

theorem ChOk.ne_none {N : Type} {ν : N} {J : ℕ} {str : List Bool} {y : Uid A U0 N U1 → UW ub} (h : ChOk ν J str y)
    {k : Fin U1} (hk : k.1 ≤ J) : y (.new ν k) ≠ none := by
  rw [h.2 k, Ne, unitsOf_eq_none, h.1]
  omega


theorem role_new_ne_none {x : Fin E} {p : (M.kind x).Ro} {t : ℕ} {ids : (M.kind x).SlAt p → List (Uid A U0 M.N U1)}
    {o : M.N → Fin U1} {y : Uid A U0 M.N U1 → UW ub} (h : role M x p t ids o y ≠ 0) {ν : (M.kind x).Cn}
    (hν : (M.kind x).c ν = p ∨ (M.kind x).d ν = p) {k : Fin U1} (hk : k ≤ o ⟨x, ν⟩) : y (.new ⟨x, ν⟩ k) ≠ none := by
  obtain ⟨-, i, g, hg, -⟩ := role_ne_zero h
  exact (hg ⟨ν, hν⟩).ne_none hk

end Role

section Law

variable (L : Law F)


def chCode (ub U1 B : ℕ) (ν : L.Cn) (i : Fin B → L.I) (g : (k : Fin B) → Fin (L.len (i k) ν) → Bool) : Fin U1 → UW ub :=
  fun k => unitsOf ub (chString L.lab (fun j => L.len j ν) i g) k




structure Law.Le (L : Law F) (m : ℕ) : Prop where
  len_le : ∀ i ν, L.len i ν ≤ m

variable {L}



open Classical in
variable (L) in

noncomputable def outTab (ub : ℕ) {U1 B : ℕ} (X : L.Ro → Fin B → L.Sl → Bool) (o : L.Cn → Fin U1) (p : L.Ro)
    (i : Fin B → L.I) (g : (ν : L.CnAt p) → (k : Fin B) → Fin (L.len (i k) ν) → Bool) : F :=
  if ∀ ν : L.CnAt p, ucount ub (chString L.lab (fun j => L.len j ν) i (g ν)) = (o ν).1 + 1 then
    ∏ k, L.tab p (i k) (fun e => X p k e) fun ν => g ν k else 0







end Law

section Identity




theorem new_mem_newUnits {x : Fin E} {o : M.N → Fin U1} {ν : M.N} {k : Fin U1} :
    (Uid.new ν k : Uid A U0 M.N U1) ∈ newUnits M x o ↔ ν.1 = x ∧ k ≤ o ν := by
  simp [newUnits]

theorem init_not_mem_newUnits {x : Fin E} {o : M.N → Fin U1} {a b : Fin A} {k : Fin U0} :
    (Uid.init a b k : Uid A U0 M.N U1) ∉ newUnits M x o := by
  simp [newUnits]




def upd (M : Sys F (A + A') E) (o : M.N → Fin U1) (x : Fin E) (oo : (M.kind x).Cn → Fin U1) : M.N → Fin U1 := fun ν =>
  if h : x = ν.1 then (h ▸ oo : (M.kind ν.1).Cn → Fin U1) ν.2 else o ν














end Identity

end Nc.G
end
/- Source module Nc.G.PlayThm. -/
section
set_option linter.unusedSectionVars false

namespace Nc.G

open Finset Nc.Cut

variable {F : Type} [CommRing F] {A A' E U0 U1 ub : ℕ} {M : Sys F (A + A') E}

theorem init_mem_seen0 {N : Type} [Fintype N] [DecidableEq N] {n : Fin A → Fin A → Fin (U0 + 1)} {a b : Fin A}
    {k : Fin U0} : (Uid.init a b k : Uid A U0 N U1) ∈ seen0 n ↔ k.1 < (n a b).1 := by
  simp [seen0]

theorem new_not_mem_seen0 {N : Type} [Fintype N] [DecidableEq N] {n : Fin A → Fin A → Fin (U0 + 1)} {ν : N}
    {k : Fin U1} : (Uid.new ν k : Uid A U0 N U1) ∉ seen0 n := by
  simp [seen0]

namespace Plan

variable {P : Plan M U0 U1} {n : Fin A → Fin A → Fin (U0 + 1)} {o o' : M.N → Fin U1}

theorem mem_seenAt {x : ℕ} {id : Uid A U0 M.N U1} : id ∈ seenAt n o x ↔
    id ∈ seen0 n ∨ ∃ x' : Fin E, x'.1 < x ∧ id ∈ newUnits M x' o := by
  simp [seenAt]

theorem new_mem_seenAt {x : ℕ} {ν : M.N} {k : Fin U1} :
    (Uid.new ν k : Uid A U0 M.N U1) ∈ seenAt n o x ↔ ν.1.1 < x ∧ k ≤ o ν := by
  rw [mem_seenAt]
  constructor
  · rintro (h | ⟨x', hx', h⟩)
    · exact absurd h new_not_mem_seen0
    · obtain ⟨rfl, h2⟩ := new_mem_newUnits.1 h
      exact ⟨hx', h2⟩
  · rintro ⟨h1, h2⟩
    exact Or.inr ⟨ν.1, h1, new_mem_newUnits.2 ⟨rfl, h2⟩⟩

theorem init_mem_seenAt {x : ℕ} {a b : Fin A} {k : Fin U0} :
    (Uid.init a b k : Uid A U0 M.N U1) ∈ seenAt n o x ↔ k.1 < (n a b).1 := by
  rw [mem_seenAt, init_mem_seen0]
  refine or_iff_left ?_
  rintro ⟨x', -, h⟩
  exact init_not_mem_newUnits h




theorem mem_used {x : ℕ} {id : Uid A U0 M.N U1} : id ∈ P.used n o x ↔ ∃ z : M.Z, z.1.1 < x ∧ id ∈ P.cons n o z := by
  simp [used]

theorem mem_cur {x : ℕ} {id : Uid A U0 M.N U1} : id ∈ P.cur n o x ↔ id ∈ seenAt n o x ∧
    ∀ z : M.Z, z.1.1 < x → id ∉ P.cons n o z := by
  rw [cur, Finset.mem_sdiff, mem_used]
  push Not
  exact Iff.rfl







end Plan

section Lemmas

variable {P : Plan M U0 U1} {cap : ℕ} {n : Fin A → Fin A → Fin (U0 + 1)} {o o' : M.N → Fin U1}














noncomputable def tabUpTo (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1)
    (init : Fin (A + A') → (Uid A U0 M.N U1 → UW ub) → F) (x : ℕ) (y : Fin (A + A') → Uid A U0 M.N U1 → UW ub) : F :=
  (∏ a, init a (y a)) * ∏ x' ∈ univ.filter (fun x' : Fin E => x'.1 < x), ∏ p, roleAt P n o ⟨x', p⟩ (y (M.part x' p))

variable {init : Fin (A + A') → (Uid A U0 M.N U1 → UW ub) → F}
















def outSet (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1) (x : Fin E) :
    Finset (Uid A U0 M.N U1) := univ.biUnion fun e : (M.kind x).Sl => P.cons n o ⟨x, e⟩





end Lemmas









end Nc.G
end
/- Source module Nc.G.Start. -/
section
set_option linter.unusedSectionVars false

namespace Nc.G

open Finset Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K U0 U1 : ℕ} {N : Type} [Fintype N] [DecidableEq N] {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {ub : ℕ} {c : ℕ}
  {cb : Option Γ → Fin c → Bool}


def InitOk (ub : ℕ) {c : ℕ} (cb : Option Γ → Fin c → Bool) {A : ℕ} (ρ : Option S → RowData A)
    (n : Fin A → Fin A → ℕ) (p : Fin A) (y : Uid A U0 N U1 → UW ub) (R C : Option S → Fin A → List Γ) : Prop :=
  (∀ s, RowOk (ρ s) (R s)) ∧ (∀ b, ucount ub (strOf cb fun s => R s b) = n p b ∧
      ∀ k : Fin U0, y (.init p b k) = unitsOf ub (strOf cb fun s => R s b) k) ∧
    (∀ b, ucount ub (strOf cb fun s => C s b) = n b p ∧
      ∀ k : Fin U0, y (.init b p k) = unitsOf ub (strOf cb fun s => C s b) k)

open Classical in
theorem tabInit_eq (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → ℕ) (p : Fin (K + K)) (y : Uid (K + K) U0 N U1 → UW ub) :
    tabInit mu T cb q x ρ n p y =
      ∑ R ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T,
      ∑ C ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T,
        if InitOk ub cb ρ n p y R C then partyW mu T q x p R C else 0 := by
  unfold tabInit
  exact Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun C _ => if_congr Iff.rfl rfl rfl


theorem tabInit_ne_none {np : N → Bool → Fin (K + K + A')} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
    {ρ : Option S → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {p : Fin (K + K)}
    {y : Uid (K + K) U0 N U1 → UW ub} (h : tabInit mu T cb q x ρ (fun a b => (n a b).1) p y ≠ 0) :
    ∀ id ∈ seen0 (N := N) (U1 := U1) n, Holds (hold0 np) (hold1 np) (Fin.castAdd A' p) id → y id ≠ none := by
  classical
  rw [tabInit_eq] at h
  obtain ⟨R, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨C, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at h with hc
  swap
  · exact absurd rfl h
  obtain ⟨-, h1, h2⟩ := hc
  intro id hid hh
  cases id with
  | new ν k => exact absurd hid new_not_mem_seen0
  | init a b k =>
    rw [init_mem_seen0] at hid
    rcases hh with hh | hh
    · have hh : p = a := Fin.castAdd_injective _ _ hh
      subst hh
      rw [(h1 b).2, Ne, unitsOf_eq_none, (h1 b).1]
      exact not_le.2 hid
    · have hh : p = b := Fin.castAdd_injective _ _ hh
      subst hh
      rw [(h2 a).2, Ne, unitsOf_eq_none, (h2 a).1]
      exact not_le.2 hid





noncomputable def sides (Γ S : Type) [Fintype Γ] [Fintype S] [DecidableEq S] (K T : ℕ) :
    Finset (Fin (K + K) → Option S → Fin (K + K) → List Γ) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Fintype.piFinset fun _ => wordsLe Γ T



open Classical in
theorem prod_tabInit (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → ℕ) (y : Fin (K + K) → Uid (K + K) U0 N U1 → UW ub) :
    (∏ p, tabInit mu T cb q x (fun s => ρ s p) n p (y p)) =
      ∑ R ∈ sides Γ S K T, ∑ C ∈ sides Γ S K T, if ∀ p, InitOk ub cb (fun s => ρ s p) n p (y p) (R p) (C p) then
        ∏ p, partyW mu T q x p (R p) (C p) else 0 := by
  simp only [tabInit_eq]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, true_imp_iff]





end Nc.G
end
/- Source module Nc.Cut.Exact. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Cut

open Finset

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A K U0 E U1 : ℕ}

section Groups

variable {AA UU W G : Type*} [Fintype AA] [DecidableEq AA] [Fintype UU] [DecidableEq UU]
  [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G]


theorem groupVal_ne_none {h0 h1 : UU → AA} {e : W} {Seen Cur : Finset UU} (hCur : Cur ⊆ Seen) {grp : AA → G}
    {φ : AA → (UU → W) → F} {g : G} {b : UU → W}
    (hφ : ∀ a y, φ a y ≠ 0 → ∀ id ∈ Seen, Holds h0 h1 a id → y id ≠ e)
    (h : groupVal h0 h1 e Seen Cur grp φ g b ≠ 0) {id : UU} (hid : id ∈ Cur)
    (hg : (grp (h0 id) = g ∧ grp (h1 id) ≠ g) ∨ (grp (h0 id) ≠ g ∧ grp (h1 id) = g)) : b id ≠ e := by
  classical
  rw [groupVal] at h
  obtain ⟨y, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at h with hc
  swap
  · exact absurd rfl h
  have h2 : ∀ a, grp a = g → φ a (y a) ≠ 0 := fun a ha h0 =>
    h (Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩) h0)
  rcases hg with ⟨g1, g2⟩ | ⟨g1, g2⟩
  · rw [← hc.fst id hid g1 g2]
    exact hφ _ _ (h2 _ g1) id (hCur hid) (Or.inl rfl)
  · rw [← hc.snd id hid g1 g2]
    exact hφ _ _ (h2 _ g2) id (hCur hid) (Or.inr rfl)

end Groups

end Nc.Cut
end
/- Source module Nc.G.Exact. -/
section
set_option linter.unusedSectionVars false

namespace Nc.G

open Finset Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A A' K E U0 U1 ub c : ℕ}

section Play

variable {M : Sys F (A + A') E} {P : Plan M U0 U1} {n : Fin A → Fin A → Fin (U0 + 1)} {o : M.N → Fin U1}


theorem partyTab_ne_none {init : (Uid A U0 M.N U1 → UW ub) → F} {a : Fin (A + A')} {y : Uid A U0 M.N U1 → UW ub}
    (hinit : init y ≠ 0 → ∀ id ∈ seen0 (N := M.N) (U1 := U1) n, Holds (hold0 M.np) (hold1 M.np) a id → y id ≠ none)
    (h : partyTab P n o init a y ≠ 0) {id : Uid A U0 M.N U1} (hid : id ∈ Plan.seenAt n o E)
    (ha : Holds (hold0 M.np) (hold1 M.np) a id) : y id ≠ none := by
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  cases id with
  | init b c k => exact hinit h1 _ (init_mem_seen0.2 (Plan.init_mem_seenAt.1 hid)) ha
  | new ν k =>
    obtain ⟨-, hk⟩ := Plan.new_mem_seenAt.1 hid
    obtain ⟨x, ν⟩ := ν
    have h3 : ∀ p, M.part x p = a → roleAt P n o ⟨x, p⟩ y ≠ 0 := by
      intro p hp h0
      refine h2 (Finset.prod_eq_zero (Finset.mem_univ (⟨x, p⟩ : M.R)) ?_)
      have : M.rp ⟨x, p⟩ = a := hp
      rw [if_pos this]
      exact h0
    rcases ha with ha | ha
    · have : a = M.part x ((M.kind x).c ν) := ha
      exact role_new_ne_none (h3 _ this.symm) (Or.inl rfl) hk
    · have : a = M.part x ((M.kind x).d ν) := ha
      exact role_new_ne_none (h3 _ this.symm) (Or.inr rfl) hk

end Play

section Exact

variable (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (cb : Option Γ → Fin c → Bool) {M : Sys F (K + K + A') E}


noncomputable def initAll (A' : ℕ) {N : Type} [Fintype N] [DecidableEq N] {U0 U1 ub : ℕ} (q : Fin (K + 1) → Q)
    (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (p : Fin (K + K + A')) : (Uid (K + K) U0 N U1 → UW ub) → F :=
  Fin.addCases (motive := fun _ => (Uid (K + K) U0 N U1 → UW ub) → F)
    (fun p => tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p) (fun _ _ => 1) p

variable {mu T cb}

theorem tabFinal_eq {P : Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
    {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
    {o : M.N → Fin U1} (p : Fin (K + K + A')) :
    (tabFinal mu T cb P q x ρ n o p : (Uid (K + K) U0 M.N U1 → UW ub) → F) =
      partyTab P n o (initAll mu T cb A' q x ρ n p) p := by
  refine Fin.addCases (fun p => ?_) (fun p => ?_) p
  · rw [tabFinal, initAll, Fin.addCases_left, Fin.addCases_left]
  · rw [tabFinal, initAll, Fin.addCases_right, Fin.addCases_right]

theorem initAll_ne_none {N : Type} [Fintype N] [DecidableEq N] {f : N → Bool → Fin (K + K + A')}
    {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {ρ : Option S → Fin (K + K) → RowData (K + K)}
    {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {p : Fin (K + K + A')} {y : Uid (K + K) U0 N U1 → UW ub}
    (h : initAll mu T cb A' q x ρ n p y ≠ 0) :
    ∀ id ∈ seen0 (N := N) (U1 := U1) n, Holds (hold0 f) (hold1 f) p id → y id ≠ none := by
  revert h
  refine Fin.addCases (fun p => ?_) (fun p => ?_) p
  · intro h
    rw [initAll, Fin.addCases_left] at h
    exact tabInit_ne_none h
  · intro _ id hid hh
    cases id with
    | new ν k => exact absurd hid new_not_mem_seen0
    | init a b k =>
      exfalso
      have hne : ∀ a : Fin (K + K), Fin.natAdd (K + K) p ≠ Fin.castAdd A' a := by
        intro a h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        omega
      rcases hh with hh | hh
      · exact hne a hh
      · exact hne b hh

theorem tabFinal_ne_none {P : Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
    {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
    {o : M.N → Fin U1} {p : Fin (K + K + A')} {y : Uid (K + K) U0 M.N U1 → UW ub}
    (h : tabFinal mu T cb P q x ρ n o p y ≠ 0) {id : Uid (K + K) U0 M.N U1} (hid : id ∈ Plan.seenAt n o E)
    (ha : Holds (hold0 M.np) (hold1 M.np) p id) : y id ≠ none := by
  rw [tabFinal_eq] at h
  exact partyTab_ne_none (fun h0 => initAll_ne_none h0) h hid ha


theorem grpVal_ne_none {G : Type} [Fintype G] [DecidableEq G] {P : Plan M U0 U1} {q : Fin (K + 1) → Q}
    {x : Fin K → List Γ} {ρ : Option S → Fin (K + K) → RowData (K + K)}
    {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {o : M.N → Fin U1} {grp : Fin (K + K + A') → G}
    {g : G} {b : Uid (K + K) U0 M.N U1 → UW ub} (h : grpVal mu T cb P q x ρ n o grp g b ≠ 0)
    {id : Uid (K + K) U0 M.N U1} (hid : id ∈ P.cur n o E)
    (hg : (grp (hold0 M.np id) = g ∧ grp (hold1 M.np id) ≠ g) ∨
      (grp (hold0 M.np id) ≠ g ∧ grp (hold1 M.np id) = g)) : b id ≠ none :=
  Cut.groupVal_ne_none (fun _ hi => (Plan.mem_cur.1 hi).1)
    (fun _ _ h0 _ hi ha => tabFinal_ne_none h0 hi ha) h hid hg

end Exact

end Nc.G
end
/- Source module Nc.Grp.GrpSteps. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Grp

open Finset Nc.G Nc.Cut

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K E U0 U1 ub c cap : ℕ} {Gr : Type} [DecidableEq Gr]


def isInit {A U0 : ℕ} {N : Type} {U1 : ℕ} : G.Uid A U0 N U1 → Bool
  | .init _ _ _ => true
  | .new _ _ => false


def isNewOf {M : Sys F (K + K + A') E} (x : Fin E) : G.Uid (K + K) U0 M.N U1 → Bool
  | .init _ _ _ => false
  | .new ν _ => decide (ν.1 = x)

section

variable (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (cb : Option Γ → Fin c → Bool)
  {M : Sys F (K + K + A') E} (P : G.Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
  (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
  (o : M.N → Fin U1) (grp : Fin (K + K + A') → Gr) (g : Gr)





def dom : Finset (Cell M U0 U1) := univ.filter fun c =>
  grp c.1 = g ∧ c.2 ∈ G.Plan.seenAt n o E ∧ Holds (G.hold0 M.np) (G.hold1 M.np) c.1 c.2


noncomputable def initV (ub : ℕ) (N : Type) (U0 U1 : ℕ) (R C : Option S → Fin (K + K) → List Γ) (p : Fin (K + K)) :
    G.Uid (K + K) U0 N U1 → UW ub
  | .init a b k => if a = p then unitsOf ub (strOf cb fun s => R s b) k else unitsOf ub (strOf cb fun s => C s a) k
  | .new _ _ => none


def InitC (ub U0 : ℕ) (n : Fin (K + K) → Fin (K + K) → ℕ) (ρ : Option S → RowData (K + K)) (p : Fin (K + K))
    (R C : Option S → Fin (K + K) → List Γ) : Prop :=
  (∀ s, RowOk (ρ s) (R s)) ∧ (∀ b, ucount ub (strOf cb fun s => R s b) = n p b) ∧
    (∀ b, ucount ub (strOf cb fun s => C s b) = n b p) ∧
    ∀ k : Fin U0, unitsOf ub (strOf cb fun s => R s p) k = unitsOf ub (strOf cb fun s => C s p) k

open Classical in

noncomputable def baseStep (ub : ℕ) (p : Fin (K + K)) : WStep F (Cell M U0 U1) (UW ub) where
  ι := (Option S → Fin (K + K) → List Γ) × (Option S → Fin (K + K) → List Γ)
  Om := (Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T) ×ˢ
    (Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T)
  wr := (dom n o grp g).filter fun c => c.1 = Fin.castAdd A' p ∧ isInit c.2 = true
  w RC _ := if InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s p) p RC.1 RC.2 then
    partyW mu T q x p RC.1 RC.2 else 0
  v RC _ c := initV cb ub M.N U0 U1 RC.1 RC.2 p c.2
  rd := ∅


abbrev Bk (L : Law F) (p : L.Ro) := Σ i : L.I, ∀ ν : L.CnAt p, Fin (L.len i ν) → Bool


def chS (L : Law F) (p : L.Ro) {B : ℕ} (f : Fin B → Bk L p) (ν : L.CnAt p) : List Bool :=
  chString L.lab (fun j => L.len j ν) (fun k => (f k).1) (fun k => (f k).2 ν)

open Classical in

noncomputable def roleV (ub : ℕ) {M : Sys F (K + K + A') E} (r : M.R) {B : ℕ} (f : Fin B → Bk (M.kind r.1) r.2) :
    G.Uid (K + K) U0 M.N U1 → UW ub
  | .init _ _ _ => none
  | .new ν k => if h : ∃ c : (M.kind r.1).CnAt r.2, (⟨r.1, c.1⟩ : M.N) = ν then
      unitsOf ub (chS (M.kind r.1) r.2 f h.choose) k else none

open Classical in

noncomputable def roleStep (ub : ℕ) (r : M.R) : WStep F (Cell M U0 U1) (UW ub) where
  ι := Fin (P.num n o r.1 * ub) → Bk (M.kind r.1) r.2
  Om := univ
  wr := (dom n o grp g).filter fun c => c.1 = M.rp r ∧ isNewOf r.1 c.2 = true
  w f σ := if (∀ e : (M.kind r.1).SlAt r.2, ∀ id ∈ P.ids n o ⟨r.1, e.1⟩, σ (M.rp r, id) ≠ none) ∧
      ∀ ν : (M.kind r.1).CnAt r.2, ucount ub (chS (M.kind r.1) r.2 f ν) = (o ⟨r.1, ν.1⟩).1 + 1 then
    ∏ k, (M.kind r.1).tab r.2 (f k).1 (fun e => (slotBits (P.num n o r.1) (P.ids n o ⟨r.1, e.1⟩)
      fun id => σ (M.rp r, id)).getD k false) (f k).2 else 0
  v f _ c := roleV ub r f c.2
  rd := univ.filter fun c => c.1 = M.rp r ∧ ∃ e : (M.kind r.1).SlAt r.2, c.2 ∈ P.ids n o ⟨r.1, e.1⟩











noncomputable def steps (ub : ℕ) : List (WStep F (Cell M U0 U1) (UW ub)) :=
  (baseList grp g).map (baseStep mu T cb q x ρ n o grp g ub) ++ (roleList grp g M).map (roleStep P n o grp g ub)

end

section facts

variable {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {cb : Option Γ → Fin c → Bool}
  {M : Sys F (K + K + A') E} {P : G.Plan M U0 U1} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}



theorem mem_baseList {p : Fin (K + K)} : p ∈ baseList (A' := A') grp g ↔ grp (Fin.castAdd A' p) = g := by
  simp [baseList]





theorem nodup_baseList : (baseList (A' := A') (K := K) grp g).Nodup := (List.nodup_finRange _).filter _

theorem pairwise_allRoles : (allRoles M).Pairwise fun r r' => r ≠ r' ∧ r.1 ≤ r'.1 := by
  unfold allRoles
  rw [List.pairwise_flatMap]
  refine ⟨fun x _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine (Finset.nodup_toList _).imp fun {p p'} h => ⟨fun h' => h ?_, le_rfl⟩
    exact eq_of_heq (Sigma.mk.inj h').2
  · refine (List.pairwise_lt_finRange E).imp fun {x x'} hx r hr r' hr' => ?_
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hr
    obtain ⟨p', -, rfl⟩ := List.mem_map.1 hr'
    exact ⟨fun h => hx.ne (Sigma.mk.inj h).1, hx.le⟩





















end facts

end Nc.Grp
end
/- Source module Nc.Dl.Tab. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut


inductive Nm (K E pS : ℕ) (S N Id : Type) where
  
  | zero
  
  | part (κ : Fin K)
  
  | q (a : Fin (K + 1))
  
  | flag (s : Option S) (p : Fin (K + K))
  
  | rd (s : Option S) (p : Fin (K + K))
  
  | row (s : Option S) (p : Fin (K + K))
  
  | kR (a b : Fin (K + K))
  
  | kC (a b : Fin (K + K))
  
  | dg (a : Fin (K + K))
  
  | dn (a b : Fin (K + K))
  
  | dO (ν : N)
  
  | ch (ν : N) (d : Bool)
  
  | slp (k : Fin pS)
  
  | num (x : Fin E)
  
  | cond (x : Option (Fin E))
  
  | cut (id : Id)
  
  | cont (id : Id)
  deriving DecidableEq

variable {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E}





structure Codes (S : Type) (M : Sys A (K + K + A') E) (U0 U1 D pS : ℕ) where
  
  nm : Nm K E pS S M.N (G.Uid (K + K) U0 M.N U1) → List Bool
  nm_inj : Function.Injective nm
  
  dc : Fin D → List Bool
  dc_inj : Function.Injective dc
  
  rc : RowData (K + K) → List Bool
  rc_inj : Function.Injective rc
  
  key : Grp.Cell M U0 U1 → List Bool
  
  dkey : Fin (K + K) × Fin U0 → List Bool

variable {P : G.Plan M U0 U1} {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm}

namespace Codes

variable (C : Codes S M U0 U1 D pS)


abbrev NmT (S : Type) (M : Sys A (K + K + A') E) (U0 U1 pS : ℕ) := Nm K E pS S M.N (G.Uid (K + K) U0 M.N U1)


def dt (d : Fin D) : Tree := ofBits (C.dc d)


noncomputable def un (x dst : NmT S M U0 U1 pS) (f : Fin D → Tree) : DStep :=
  .op (C.nm x) (C.nm .zero) (C.nm dst) (trieOf C.dc fun d => .cons (f d) .nil)


noncomputable def bin (x y dst : NmT S M U0 U1 pS) (f : Fin D → Fin D → Fin D) : DStep :=
  .op (C.nm x) (C.nm y) (C.nm dst) (trieOf C.dc fun d => trieOf C.dc fun d' => C.dt (f d d'))


def con (dst : NmT S M U0 U1 pS) (t : Tree) : DStep :=
  .op (C.nm .zero) (C.nm .zero) (C.nm dst) (.cons (.cons t .nil) .nil)

variable {C} {m : ℕ} {st : NmT S M U0 U1 pS → Tree}

theorem exec_un {x dst : NmT S M U0 U1 pS} {f : Fin D → Tree} {d : Fin D} (hz : st .zero = .nil) (hx : st x = C.dt d) :
    (C.un x dst f).exec m (byPath C.nm st) = [byPath C.nm (Function.update st dst (f d))] := by
  rw [un, exec_op C.nm_inj, hz, hx, dt, path_ofBits, tget_trieOf C.dc_inj]
  rfl

theorem exec_bin {x y dst : NmT S M U0 U1 pS} {f : Fin D → Fin D → Fin D} {d d' : Fin D} (hx : st x = C.dt d)
    (hy : st y = C.dt d') :
    (C.bin x y dst f).exec m (byPath C.nm st) = [byPath C.nm (Function.update st dst (C.dt (f d d')))] := by
  rw [bin, exec_op C.nm_inj, hx, hy, dt, dt, path_ofBits, path_ofBits, tget_trieOf C.dc_inj, tget_trieOf C.dc_inj]

theorem exec_con {dst : NmT S M U0 U1 pS} {t : Tree} (hz : st .zero = .nil) :
    (C.con dst t).exec m (byPath C.nm st) = [byPath C.nm (Function.update st dst t)] := by
  rw [con, exec_op C.nm_inj, hz]
  rfl

end Codes

end Nc.Dl
end
/- Source module Nc.Dl.Phases. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut

theorem sum_execAll_append {B : Type} [CommRing B] (m : ℕ) (a b : List DStep) (σ : List Bool → Tree)
    (Φ : (List Bool → Tree) → B) :
    ((execAll m (a ++ b) σ).map Φ).sum = ((execAll m a σ).map fun σ' => ((execAll m b σ').map Φ).sum).sum := by
  rw [execAll_append, sum_flatMap_map]


theorem sum_funs_univ {A : Type} [CommRing A] {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (opts : ι → List α) (hopts : ∀ i, (opts i).Nodup) (f0 : ι → α) (Φ : (ι → α) → A) :
    ((funs opts f0 (univ : Finset ι).toList).map Φ).sum = ∑ f : ι → α, if ∀ i, f i ∈ opts i then Φ f else 0 := by
  rw [sum_funs opts hopts _ (Finset.nodup_toList _)]
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  simp

variable {B : Type} [CommRing B] {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) {m : ℕ}

open Codes

section Generic

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]


noncomputable def pickS (opts : List α) (o : α → List (NmT S M U0 U1 pS × Tree)) : DStep :=
  .pick (C.nm .zero) (.cons (listT (opts.map fun a => optT C.nm (o a))) .nil)

theorem exec_pickS {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil) (opts : List α)
    (o : α → List (NmT S M U0 U1 pS × Tree)) :
    (pickS C opts o).exec m (byPath C.nm st) = opts.map fun a => byPath C.nm (upds st (o a)) := by
  rw [pickS, exec_pick C.nm_inj (opts := opts.map o), List.map_map]
  · rfl
  · rw [hz]
    simp [path, tget, Function.comp_def]

theorem upds_of_not {ν : Type} [DecidableEq ν] {st : ν → Tree} {o : List (ν × Tree)} {x : ν} (h : ∀ a ∈ o, a.1 ≠ x) :
    upds st o x = st x := by
  unfold upds
  induction o generalizing st with
  | nil => rfl
  | cons a o ih =>
    rw [List.foldl_cons, ih fun b hb => h b (List.mem_cons_of_mem _ hb),
      Function.update_of_ne (h a List.mem_cons_self).symm]


theorem phase_picks {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil) (opts : ι → List α)
    (hopts : ∀ i, (opts i).Nodup) (o : ι → α → List (NmT S M U0 U1 pS × Tree))
    (own : NmT S M U0 U1 pS → Option ι) (v : (ι → α) → NmT S M U0 U1 pS → Tree)
    (ho : ∀ (f : ι → α) i, ∀ a ∈ o i (f i), own a.1 = some i ∧ a.2 = v f a.1)
    (hall : ∀ (f : ι → α) i x, own x = some i → ∃ a ∈ o i (f i), a.1 = x) (hz' : own .zero = none) (f0 : ι → α)
    (Φ : (List Bool → Tree) → B) :
    ((execAll m ((univ : Finset ι).toList.map fun i => pickS C (opts i) (o i)) (byPath C.nm st)).map Φ).sum =
      ∑ f : ι → α, if ∀ i, f i ∈ opts i then
        Φ (byPath C.nm fun x => if (own x).isSome then v f x else st x) else 0 := by
  have hzero : ∀ (st : NmT S M U0 U1 pS → Tree) i a, st .zero = .nil → upds st (o i a) .zero = .nil := by
    intro st i a hst
    rw [upds_of_not, hst]
    intro b hb h0
    have := (ho (Function.update f0 i a) i b (by rw [Function.update_self]; exact hb)).1
    rw [h0, hz'] at this
    simp at this
  rw [execAll_choices (opts := opts) (L := byPath C.nm) (ov := fun i a st => upds st (o i a))
    (good := fun st => st .zero = .nil) (fun i st hst => exec_pickS C hst (opts i) (o i))
    (fun i st a _ hst => hzero st i a hst) (Finset.nodup_toList _) hz f0, sum_funs_univ opts hopts]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hf := foldl_upds (own := own) (o := fun i => o i (f i)) (v := v f) (ho f) (hall f) (univ : Finset ι).toList st
  rw [hf]
  congr 2
  congr 1
  funext x
  cases h : own x with
  | none => simp
  | some i => simp


theorem phase_det {st : NmT S M U0 U1 pS → Tree} {step : ι → DStep} (g : ι → NmT S M U0 U1 pS)
    (hg : Function.Injective g) (v : ι → Tree) (base : (NmT S M U0 U1 pS → Tree) → Prop) (hst0 : base st)
    (hstep : ∀ i st, base st → (step i).exec m (byPath C.nm st) = [byPath C.nm (Function.update st (g i) (v i))])
    (hbase : ∀ i st, base st → base (Function.update st (g i) (v i))) (s : List ι) (hall : ∀ i, i ∈ s) :
    execAll m (s.map step) (byPath C.nm st) = [byPath C.nm fun x =>
      open Classical in if h : ∃ i, g i = x then v h.choose else st x] := by
  classical
  rw [execAll_det (L := byPath C.nm) (ov := fun i st => Function.update st (g i) (v i)) (good := fun _ st => base st)
    (fun i _ st hst => ⟨hstep i st hst, hbase i st hst⟩) hst0]
  have hf := foldl_upds (own := fun x => if h : ∃ i, g i = x then some h.choose else none)
    (o := fun i => [(g i, v i)]) (v := fun x => if h : ∃ i, g i = x then v h.choose else .nil) (by
      intro i a ha
      rw [List.mem_singleton] at ha
      subst ha
      have h : ∃ j, g j = g i := ⟨i, rfl⟩
      rw [dif_pos h, dif_pos h, hg h.choose_spec]
      exact ⟨rfl, rfl⟩) (by
      intro i x hx
      by_cases h : ∃ i, g i = x
      · rw [dif_pos h] at hx
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        rw [← Option.some.inj hx]
        exact h.choose_spec
      · rw [dif_neg h] at hx
        simp at hx) s st
  have e : (s.foldl (fun st i => Function.update st (g i) (v i)) st) = s.foldl (fun st i => upds st [(g i, v i)]) st := rfl
  rw [e, hf]
  congr 2
  funext x
  by_cases h : ∃ i, g i = x
  · rw [dif_pos h, dif_pos h]
    simp [hall, h]
  · simp only [dif_neg h]

end Generic

end Nc.Dl
end
/- Source module Nc.Dl.Run. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

variable {B : Type} [CommRing B] {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) {m : ℕ}

section Values

variable (qn : Q → ℕ) (hU0 : U0 < D) (hU1 : U1 ≤ D)


def digN (n : Fin (U0 + 1)) : Fin D := ⟨n, lt_of_le_of_lt (Nat.le_of_lt_succ n.2) hU0⟩


def digO (j : Fin U1) : Fin D := ⟨j, lt_of_lt_of_le j.2 hU1⟩


def flagT (d : RowData (K + K)) : Tree := listT ((List.ofFn fun b => Grp.rowFlag d b).reverse.map num)


def kRT (a b : Fin (K + K)) (n : Fin (U0 + 1)) : Tree :=
  listT (((List.finRange U0).filter fun k => k.1 < n.1).map fun k => ofBits (C.key (Fin.castAdd A' a, .init a b k)))


def kCT (a b : Fin (K + K)) (n : Fin (U0 + 1)) : Tree :=
  listT (((List.finRange U0).filter fun k => k.1 < n.1).map fun k =>
    ofBits (if a = b then C.dkey (b, k) else C.key (Fin.castAdd A' b, .init a b k)))


def dgT (a : Fin (K + K)) (n : Fin (U0 + 1)) : Tree :=
  listT (((List.finRange U0).filter fun k => k.1 < n.1).map fun k =>
    (Grp.Ins.both (C.key (Fin.castAdd A' a, .init a a k)) (C.dkey (a, k))).tree)


def chT (ν : M.N) (d : Bool) (j : Fin U1) : Tree :=
  listT (((List.finRange U1).filter fun k => k ≤ j).map fun k => ofBits (C.key (M.np ν d, .new ν k)))

end Values

section Picks

variable (pt : Fin K → Tree) (qn : Q → ℕ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D)


def S0 : NmT S M U0 U1 pS → Tree
  | .part κ => pt κ
  | _ => .nil


def own1 : NmT S M U0 U1 pS → Option (Fin (K + 1))
  | .q a => some a
  | _ => none


def v1 (q : Fin (K + 1) → Q) : NmT S M U0 U1 pS → Tree
  | .q a => num (qn (q a))
  | _ => .nil


noncomputable def opts1 (a : Fin (K + 1)) : List Q :=
  if a = 0 then [i] else if a = Fin.last K then [e] else (univ : Finset Q).toList


noncomputable def steps1 : List DStep := (univ : Finset (Fin (K + 1))).toList.map fun a =>
  pickS C (opts1 i e a) fun q => [(.q a, num (qn q))]


def S1 (q : Fin (K + 1) → Q) : NmT S M U0 U1 pS → Tree := fun x =>
  if (own1 x).isSome then v1 qn q x else S0 pt x

theorem phase1 (hK : 0 < K) [Nonempty Q] (Φ : (List Bool → Tree) → B) :
    ((execAll m (steps1 C qn i e) (byPath C.nm (S0 pt))).map Φ).sum =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then Φ (byPath C.nm (S1 pt qn q)) else 0 := by
  classical
  rw [steps1, phase_picks C rfl (opts1 i e) (fun a => ?_) (fun a q => [(.q a, num (qn q))]) own1 (v1 qn)
    (fun f a b hb => ?_) (fun f a x hx => ?_) rfl (fun _ => Classical.arbitrary Q)]
  · refine Finset.sum_congr rfl fun q _ => ?_
    have h0 : (0 : Fin (K + 1)) ≠ Fin.last K := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have key : (∀ a, q a ∈ opts1 i e a) ↔ q 0 = i ∧ q (Fin.last K) = e := by
      constructor
      · intro h
        have h1 := h 0
        have h2 := h (Fin.last K)
        rw [opts1, if_pos rfl, List.mem_singleton] at h1
        rw [opts1, if_neg (Ne.symm h0), if_pos rfl, List.mem_singleton] at h2
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩ a
        unfold opts1
        split_ifs with ha ha'
        · rw [ha, h1]; exact List.mem_singleton_self _
        · rw [ha', h2]; exact List.mem_singleton_self _
        · simp
    by_cases hq : q 0 = i ∧ q (Fin.last K) = e
    · rw [if_pos hq, if_pos (key.2 hq)]
      rfl
    · rw [if_neg hq, if_neg fun h => hq (key.1 h)]
  · unfold opts1
    split_ifs
    · simp
    · simp
    · exact Finset.nodup_toList _
  · rw [List.mem_singleton] at hb
    subst hb
    exact ⟨rfl, rfl⟩
  · cases x <;> simp only [own1, reduceCtorEq, Option.some.injEq] at hx
    subst hx
    exact ⟨_, List.mem_singleton_self _, rfl⟩


def own2 : NmT S M U0 U1 pS → Option (Option S × Fin (K + K))
  | .flag s p => some (s, p)
  | .rd s p => some (s, p)
  | _ => none


def v2 (ρ : Option S × Fin (K + K) → RowData (K + K)) : NmT S M U0 U1 pS → Tree
  | .flag s p => flagT (ρ (s, p))
  | .rd s p => ofBits (C.rc (ρ (s, p)))
  | _ => .nil


noncomputable def steps2 : List DStep := (univ : Finset (Option S × Fin (K + K))).toList.map fun a =>
  pickS C (univ : Finset (RowData (K + K))).toList fun d => [(.flag a.1 a.2, flagT d), (.rd a.1 a.2, ofBits (C.rc d))]

theorem phase2 [Nonempty (RowData (K + K))] {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil)
    (Φ : (List Bool → Tree) → B) :
    ((execAll m (steps2 C) (byPath C.nm st)).map Φ).sum = ∑ ρ : Option S → Fin (K + K) → RowData (K + K),
      Φ (byPath C.nm fun x => if (own2 x).isSome then v2 C (fun a => ρ a.1 a.2) x else st x) := by
  classical
  rw [steps2, phase_picks C hz (fun _ => (univ : Finset (RowData (K + K))).toList) (fun _ => Finset.nodup_toList _)
    (fun a d => [(.flag a.1 a.2, flagT d), (.rd a.1 a.2, ofBits (C.rc d))]) own2 (v2 C)
    (fun f a b hb => ?_) (fun f a x hx => ?_) rfl (fun _ => Classical.arbitrary _)]
  · rw [← (Equiv.curry (Option S) (Fin (K + K)) (RowData (K + K))).sum_comp]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [if_pos]
    · rfl
    · intro a
      simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact ⟨rfl, rfl⟩
  · cases x <;> simp only [own2, reduceCtorEq, Option.some.injEq] at hx
    · subst hx
      exact ⟨_, List.mem_cons_self, rfl⟩
    · subst hx
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl⟩


def own3 : NmT S M U0 U1 pS → Option (Fin (K + K) × Fin (K + K))
  | .kR a b => some (a, b)
  | .kC a b => some (a, b)
  | .dn a b => some (a, b)
  | .dg a => some (a, a)
  | _ => none


def v3 (n : Fin (K + K) × Fin (K + K) → Fin (U0 + 1)) : NmT S M U0 U1 pS → Tree
  | .kR a b => kRT C a b (n (a, b))
  | .kC a b => kCT C a b (n (a, b))
  | .dn a b => C.dt (digN hU0 (n (a, b)))
  | .dg a => dgT C a (n (a, a))
  | _ => .nil


def o3 (a : Fin (K + K) × Fin (K + K)) (n : Fin (U0 + 1)) : List (NmT S M U0 U1 pS × Tree) :=
  (.kR a.1 a.2, kRT C a.1 a.2 n) :: (.kC a.1 a.2, kCT C a.1 a.2 n) :: (.dn a.1 a.2, C.dt (digN hU0 n)) ::
    if a.1 = a.2 then [(.dg a.1, dgT C a.1 n)] else []


noncomputable def steps3 : List DStep := (univ : Finset (Fin (K + K) × Fin (K + K))).toList.map fun a =>
  pickS C (univ : Finset (Fin (U0 + 1))).toList (o3 C hU0 a)

theorem phase3 {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil) (Φ : (List Bool → Tree) → B) :
    ((execAll m (steps3 C hU0) (byPath C.nm st)).map Φ).sum = ∑ n : NN K U0,
      Φ (byPath C.nm fun x => if (own3 x).isSome then v3 C hU0 (fun a => n a.1 a.2) x else st x) := by
  classical
  rw [steps3, phase_picks C hz (fun _ => (univ : Finset (Fin (U0 + 1))).toList) (fun _ => Finset.nodup_toList _)
    (o3 C hU0) own3 (v3 C hU0) (fun f a b hb => ?_) (fun f a x hx => ?_) rfl (fun _ => 0)]
  · rw [← (Equiv.curry (Fin (K + K)) (Fin (K + K)) (Fin (U0 + 1))).sum_comp]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [if_pos]
    · rfl
    · intro a
      simp
  · obtain ⟨a1, a2⟩ := a
    simp only [o3, List.mem_cons] at hb
    rcases hb with rfl | rfl | rfl | hb
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · split_ifs at hb with h
      · rw [List.mem_singleton] at hb
        subst hb
        have h : a1 = a2 := h
        subst h
        exact ⟨rfl, rfl⟩
      · simp at hb
  · cases x <;> simp only [own3, reduceCtorEq, Option.some.injEq] at hx
    · subst hx
      exact ⟨_, List.mem_cons_self, rfl⟩
    · subst hx
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
    · rename_i a0
      subst hx
      refine ⟨(.dg a0, dgT C a0 (f (a0, a0))), ?_, rfl⟩
      simp only [o3, if_true]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · subst hx
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩


def own4 : NmT S M U0 U1 pS → Option M.N
  | .dO ν => some ν
  | .ch ν _ => some ν
  | _ => none


def v4 (o : M.N → Fin U1) : NmT S M U0 U1 pS → Tree
  | .dO ν => C.dt (digO hU1 (o ν))
  | .ch ν d => chT C ν d (o ν)
  | _ => .nil


noncomputable def steps4 : List DStep := (univ : Finset M.N).toList.map fun ν =>
  pickS C (univ : Finset (Fin U1)).toList fun j =>
    [(.dO ν, C.dt (digO hU1 j)), (.ch ν false, chT C ν false j), (.ch ν true, chT C ν true j)]

theorem phase4 [Nonempty (Fin U1)] {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil) (Φ : (List Bool → Tree) → B) :
    ((execAll m (steps4 C hU1) (byPath C.nm st)).map Φ).sum = ∑ o : M.N → Fin U1,
      Φ (byPath C.nm fun x => if (own4 x).isSome then v4 C hU1 o x else st x) := by
  classical
  rw [steps4, phase_picks C hz (fun _ => (univ : Finset (Fin U1)).toList) (fun _ => Finset.nodup_toList _)
    (fun ν j => [(.dO ν, C.dt (digO hU1 j)), (.ch ν false, chT C ν false j), (.ch ν true, chT C ν true j)]) own4
    (v4 C hU1) (fun f a b hb => ?_) (fun f a x hx => ?_) rfl (fun _ => Classical.arbitrary _)]
  · refine Finset.sum_congr rfl fun f _ => ?_
    rw [if_pos]
    intro a
    simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  · cases x with
    | dO ν =>
      simp only [own4, Option.some.injEq] at hx
      subst hx
      exact ⟨_, List.mem_cons_self, rfl⟩
    | ch ν d =>
      simp only [own4, Option.some.injEq] at hx
      subst hx
      cases d
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), rfl⟩
    | _ => simp [own4] at hx

end Picks

section Rows


def vr (h : ℕ) (d : RowData (K + K)) : Prop :=
  if d.1 then d.2.1.1 = h ∧ d.2.2.1 = h else h ≤ d.2.1.1 ∧ d.2.1 ≤ d.2.2

theorem validRow_iff (ρ : Fin (K + K) → RowData (K + K)) (p : Fin (K + K)) : ValidRow ρ p ↔ vr (prevHi ρ p) (ρ p) :=
  Iff.rfl

open Classical in

noncomputable def rowStep (a : Option S × Fin (K + K)) : DStep :=
  if h : a.2.1 = 0 then .op (C.nm .zero) (C.nm (.rd a.1 a.2)) (C.nm (.row a.1 a.2))
    (.cons (trieOf C.rc fun d => bit (decide (vr 0 d))) .nil)
  else .op (C.nm (.rd a.1 ⟨a.2.1 - 1, by omega⟩)) (C.nm (.rd a.1 a.2)) (C.nm (.row a.1 a.2))
    (trieOf C.rc fun d' => trieOf C.rc fun d => bit (decide (vr d'.2.2.1 d)))


noncomputable def steps5 : List DStep := (univ : Finset (Option S × Fin (K + K))).toList.map (rowStep C)

open Classical in
theorem phase5 {st : NmT S M U0 U1 pS → Tree} {ρ : Option S → Fin (K + K) → RowData (K + K)} (hz : st .zero = .nil)
    (hρ : ∀ s p, st (.rd s p) = ofBits (C.rc (ρ s p))) :
    execAll m (steps5 C) (byPath C.nm st) = [byPath C.nm fun x =>
      if h : ∃ a : Option S × Fin (K + K), Nm.row a.1 a.2 = x then bit (decide (ValidRow (ρ h.choose.1) h.choose.2))
      else st x] := by
  refine phase_det C (fun a : Option S × Fin (K + K) => Nm.row a.1 a.2) (fun a b h => ?_)
    (fun a => bit (decide (ValidRow (ρ a.1) a.2)))
    (fun st => st .zero = .nil ∧ ∀ s p, st (.rd s p) = ofBits (C.rc (ρ s p))) ⟨hz, hρ⟩ (fun a st hst => ?_)
    (fun a st hst => ⟨?_, fun s p => ?_⟩) _ (fun a => Finset.mem_toList.2 (Finset.mem_univ a))
  · simp only [Nm.row.injEq] at h
    exact Prod.ext h.1 h.2
  · obtain ⟨hz, hr⟩ := hst
    unfold rowStep
    split_ifs with h
    · rw [exec_op C.nm_inj, hz, hr, path_ofBits]
      simp only [path, tget, hd_cons]
      rw [tget_trieOf C.rc_inj]
      have : prevHi (ρ a.1) a.2 = 0 := by rw [prevHi, dif_pos h]
      rw [validRow_iff, this]
    · rw [exec_op C.nm_inj, hr, hr, path_ofBits, path_ofBits, tget_trieOf C.rc_inj, tget_trieOf C.rc_inj]
      have : prevHi (ρ a.1) a.2 = (ρ a.1 ⟨a.2.1 - 1, by omega⟩).2.2.1 := by rw [prevHi, dif_neg h]
      rw [validRow_iff, this]
  · rw [Function.update_of_ne (by simp)]
    exact hst.1
  · rw [Function.update_of_ne (by simp)]
    exact hst.2 s p

end Rows

section Slp

variable (tab : SlpTab P grp D pS)


def coord : (Fin (K + K) × Fin (K + K)) ⊕ M.N → NmT S M U0 U1 pS
  | .inl a => .dn a.1 a.2
  | .inr ν => .dO ν

open Classical in

noncomputable def slpStep (k : Fin pS) : DStep :=
  if h : ∃ i, tab.fn k = tab.inp i then C.un (coord h.choose) (.slp k) C.dt
  else if h : ∃ c, tab.fn k = fun _ => c then C.con (.slp k) (C.dt h.choose)
  else if h : ∃ i j : Fin pS, i < k ∧ j < k ∧ ∃ φ : Fin D → Fin D → Fin D, ∀ x, tab.fn k x = φ (tab.fn i x) (tab.fn j x)
    then C.bin (.slp h.choose) (.slp h.choose_spec.choose) (.slp k) h.choose_spec.choose_spec.2.2.choose
  else C.con (.slp k) .nil


noncomputable def steps6 : List DStep := (List.finRange pS).map (slpStep C tab)

theorem exec_slpStep (x : NN K U0 × (M.N → Fin U1)) (k : Fin pS) {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil)
    (hc : ∀ i, st (coord i) = C.dt (tab.inp i x)) (hprev : ∀ j < k, st (.slp j) = C.dt (tab.fn j x)) :
    (slpStep C tab k).exec m (byPath C.nm st) = [byPath C.nm (Function.update st (.slp k) (C.dt (tab.fn k x)))] := by
  classical
  unfold slpStep
  split_ifs with h1 h2 h3
  · rw [exec_un hz (hc _)]
    have e := congrFun h1.choose_spec x
    exact congrArg (fun t => [byPath C.nm (Function.update st (Nm.slp k) (C.dt t))]) e.symm
  · rw [exec_con hz]
    have e := congrFun h2.choose_spec x
    exact congrArg (fun t => [byPath C.nm (Function.update st (Nm.slp k) (C.dt t))]) e.symm
  · obtain ⟨a1, a2, a3⟩ := h3.choose_spec.choose_spec
    rw [exec_bin (hprev _ a1) (hprev _ a2), ← a3.choose_spec x]
  · exfalso
    rcases tab.step k k.2 with h | h | ⟨i, hi, j, hj, φ, hφ⟩
    · exact h1 h
    · exact h2 h
    · exact h3 ⟨⟨i, hi.trans k.2⟩, ⟨j, hj.trans k.2⟩, hi, hj, φ, hφ⟩

theorem phase6 (x : NN K U0 × (M.N → Fin U1)) {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil)
    (hc : ∀ i, st (coord i) = C.dt (tab.inp i x)) :
    ∃ st' : NmT S M U0 U1 pS → Tree, execAll m (steps6 C tab) (byPath C.nm st) = [byPath C.nm st'] ∧
      (∀ k, st' (.slp k) = C.dt (tab.fn k x)) ∧ ∀ y, (∀ k, y ≠ .slp k) → st' y = st y := by
  -- the first k steps
  have key : ∀ k, k ≤ pS → ∃ st' : NmT S M U0 U1 pS → Tree,
      execAll m (((List.finRange pS).take k).map (slpStep C tab)) (byPath C.nm st) = [byPath C.nm st'] ∧
      (∀ j : Fin pS, j.1 < k → st' (.slp j) = C.dt (tab.fn j x)) ∧ ∀ y, (∀ k, y ≠ .slp k) → st' y = st y := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨st, rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨st', e1, e2, e3⟩ := ih (Nat.le_of_succ_le hk)
      have hlen : k < (List.finRange pS).length := by rw [List.length_finRange]; exact hk
      have e4 : (List.finRange pS).take (k + 1) = (List.finRange pS).take k ++ [⟨k, hk⟩] := by
        rw [List.take_succ_eq_append_getElem hlen, List.getElem_finRange]
        rfl
      refine ⟨Function.update st' (.slp ⟨k, hk⟩) (C.dt (tab.fn k x)), ?_, fun j hj => ?_, fun y hy => ?_⟩
      · rw [e4, List.map_append, execAll_append, e1, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons,
          List.map_nil, execAll, exec_slpStep C tab x ⟨k, hk⟩ (by rw [e3 _ (fun _ => by simp)]; exact hz)
          (fun i => by rw [e3 _ (fun _ => by cases i <;> simp [coord])]; exact hc i) (fun j hj => e2 j hj)]
        rfl
      · by_cases hjk : j.1 = k
        · have : j = ⟨k, hk⟩ := Fin.ext hjk
          subst this
          rw [Function.update_self]
        · rw [Function.update_of_ne (fun h => hjk (by simpa using congrArg (fun z => match z with | Nm.slp j => j.1 | _ => 0) h))]
          exact e2 j (by omega)
      · rw [Function.update_of_ne (hy _)]
        exact e3 y hy
  obtain ⟨st', e1, e2, e3⟩ := key pS le_rfl
  rw [List.take_of_length_le (by rw [List.length_finRange])] at e1
  exact ⟨st', e1, fun k => e2 k k.2, e3⟩

end Slp

end Nc.Dl
end
/- Source module Nc.Dl.Run2. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

variable {B : Type} [CommRing B] {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) {m : ℕ}

section Conv

variable (tab : SlpTab P grp D pS)


abbrev Ix7 (M : Sys A (K + K + A') E) (U0 U1 : ℕ) := Fin E ⊕ Option (Fin E) ⊕ G.Uid (K + K) U0 M.N U1


def nm7 : Ix7 M U0 U1 → NmT S M U0 U1 pS
  | .inl x => .num x
  | .inr (.inl c) => .cond c
  | .inr (.inr id) => .cut id

theorem nm7_inj : Function.Injective (nm7 : Ix7 M U0 U1 → NmT S M U0 U1 pS) := by
  rintro (x | c | id) (x' | c' | id') h <;> simp only [nm7, reduceCtorEq, Nm.num.injEq, Nm.cond.injEq, Nm.cut.injEq] at h <;>
    rw [h]


noncomputable def step7 : Ix7 M U0 U1 → DStep
  | .inl x => C.un (.slp (tab.knum x)) (.num x) fun d => num d
  | .inr (.inl c) => C.un (.slp (tab.kcond c)) (.cond c) fun d => bit (decide (d.1 = 1))
  | .inr (.inr id) => C.un (.slp (tab.kcut id)) (.cut id) fun d => bit (decide (d.1 = 1))


def v7 (x : NN K U0 × (M.N → Fin U1)) : Ix7 M U0 U1 → Tree
  | .inl y => num (tab.fn (tab.knum y) x)
  | .inr (.inl c) => bit (decide ((tab.fn (tab.kcond c) x : ℕ) = 1))
  | .inr (.inr id) => bit (decide ((tab.fn (tab.kcut id) x : ℕ) = 1))


noncomputable def steps7 : List DStep := (univ : Finset (Ix7 M U0 U1)).toList.map (step7 C tab)

open Classical in
theorem phase7 (x : NN K U0 × (M.N → Fin U1)) {st : NmT S M U0 U1 pS → Tree} (hz : st .zero = .nil)
    (hs : ∀ k, st (.slp k) = C.dt (tab.fn k x)) :
    execAll m (steps7 C tab) (byPath C.nm st) = [byPath C.nm fun y =>
      if h : ∃ a : Ix7 M U0 U1, nm7 a = y then v7 tab x h.choose else st y] := by
  refine phase_det C nm7 nm7_inj (v7 tab x)
    (fun st => st .zero = .nil ∧ ∀ k, st (.slp k) = C.dt (tab.fn k x)) ⟨hz, hs⟩ (fun a st hst => ?_)
    (fun a st hst => ⟨?_, fun k => ?_⟩) _ (fun a => Finset.mem_toList.2 (Finset.mem_univ a))
  · obtain ⟨hz, hs⟩ := hst
    rcases a with y | c | id
    · exact exec_un hz (hs _)
    · exact exec_un hz (hs _)
    · exact exec_un hz (hs _)
  · rw [Function.update_of_ne (by rcases a with y | c | id <;> simp [nm7])]
    exact hst.1
  · rw [Function.update_of_ne (by rcases a with y | c | id <;> simp [nm7])]
    exact hst.2 k

end Conv

section Checks


noncomputable def steps8 : List DStep :=
  (((univ : Finset (Option S × Fin (K + K))).toList.map fun a => C.nm (.row a.1 a.2)) ++
    ((univ : Finset (Option (Fin E))).toList.map fun c => C.nm (.cond c))).map DStep.check

theorem phase8_pos {st : NmT S M U0 U1 pS → Tree} (h1 : ∀ s p, st (.row s p) ≠ .nil) (h2 : ∀ c, st (.cond c) ≠ .nil) :
    execAll m (steps8 C) (byPath C.nm st) = [byPath C.nm st] := by
  refine execAll_checks_pos fun p hp => ?_
  rw [List.mem_append, List.mem_map, List.mem_map] at hp
  rcases hp with ⟨a, -, rfl⟩ | ⟨c, -, rfl⟩
  · rw [byPath_nm C.nm_inj]; exact h1 _ _
  · rw [byPath_nm C.nm_inj]; exact h2 _

theorem phase8_neg {st : NmT S M U0 U1 pS → Tree} (h : (∃ s p, st (.row s p) = .nil) ∨ ∃ c, st (.cond c) = .nil) :
    execAll m (steps8 C) (byPath C.nm st) = [] := by
  refine execAll_checks_neg ?_
  rcases h with ⟨s, p, h⟩ | ⟨c, h⟩
  · refine ⟨C.nm (.row s p), List.mem_append_left _ (List.mem_map.2 ⟨(s, p), Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩), ?_⟩
    rw [byPath_nm C.nm_inj]; exact h
  · refine ⟨C.nm (.cond c), List.mem_append_right _ (List.mem_map.2 ⟨c, Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩), ?_⟩
    rw [byPath_nm C.nm_inj]; exact h

end Checks

section Bits


def wOf (ub : ℕ) (u : List Bool) : UW ub := some fun j => u.reverse.getD j false

theorem length_allBits {n : ℕ} {u : List Bool} (h : u ∈ allBits n) : u.length = n := by
  induction n generalizing u with
  | zero => simp [allBits] at h; simp [h]
  | succ n ih =>
    simp only [allBits, List.mem_append, List.mem_map] at h
    rcases h with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;> simp [ih hv]

theorem mem_allBits {n : ℕ} {u : List Bool} (h : u.length = n) : u ∈ allBits n := by
  induction n generalizing u with
  | zero => simp [allBits, List.eq_nil_of_length_eq_zero h]
  | succ n ih =>
    cases u with
    | nil => simp at h
    | cons b u =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [allBits, List.mem_append, List.mem_map]
      cases b
      · exact Or.inr ⟨u, ih h, rfl⟩
      · exact Or.inl ⟨u, ih h, rfl⟩

theorem nodup_allBits (n : ℕ) : (allBits n).Nodup := by
  induction n with
  | zero => simp [allBits]
  | succ n ih =>
    rw [allBits, List.nodup_append]
    refine ⟨ih.map fun a b h => by simpa using h, ih.map fun a b h => by simpa using h, ?_⟩
    intro a ha b hb hab
    rw [List.mem_map] at ha hb
    obtain ⟨u, -, rfl⟩ := ha
    obtain ⟨u', -, rfl⟩ := hb
    simp at hab

theorem uwBits_wOf {u : List Bool} (h : u.length = ub) : uwBits (wOf ub u) = u.reverse := by
  unfold wOf uwBits
  apply List.ext_getElem
  · simp [h]
  · intro k h1 h2
    rw [List.getElem_ofFn, List.getD_eq_getElem _ _ h2]

theorem wOf_inj {u u' : List Bool} (h : u.length = ub) (h' : u'.length = ub) (e : wOf ub u = wOf ub u') : u = u' := by
  have := congrArg uwBits e
  rw [uwBits_wOf h, uwBits_wOf h'] at this
  exact List.reverse_injective this

theorem exists_wOf {w : UW ub} (h : w ≠ none) : ∃ u ∈ allBits ub, wOf ub u = w := by
  obtain ⟨v, rfl⟩ := Option.ne_none_iff_exists'.1 h
  refine ⟨(List.ofFn v).reverse, mem_allBits (by simp), ?_⟩
  unfold wOf
  congr 1
  funext j
  rw [List.reverse_reverse, List.getD_eq_getElem _ _ (by simp)]
  simp


def optsB (ub : ℕ) (c : Bool) : List (UW ub) := if c then (allBits ub).map (wOf ub) else [none]

theorem nodup_optsB (c : Bool) : (optsB ub c).Nodup := by
  unfold optsB
  cases c
  · simp
  · simp only [if_true]
    refine List.Nodup.map_on (fun u hu u' hu' h => ?_) (nodup_allBits ub)
    exact wOf_inj (length_allBits hu) (length_allBits hu') h

theorem mem_optsB {c : Bool} {w : UW ub} : w ∈ optsB ub c ↔ (w ≠ none ↔ c = true) := by
  unfold optsB
  cases c
  · simp
  · simp only [if_true, List.mem_map, iff_true]
    constructor
    · rintro ⟨u, -, rfl⟩
      exact Option.some_ne_none _
    · intro h
      exact exists_wOf h


noncomputable def steps9 : List DStep := (univ : Finset (G.Uid (K + K) U0 M.N U1)).toList.map fun id =>
  DStep.bits (C.nm (.cut id)) (C.nm (.cont id))


def ov9 (id : G.Uid (K + K) U0 M.N U1) (w : UW ub) (st : NmT S M U0 U1 pS → Tree) : NmT S M U0 U1 pS → Tree :=
  match w with
  | none => st
  | some v => Function.update st (.cont id) (ofBits (List.ofFn v))

theorem ov9_some (id : G.Uid (K + K) U0 M.N U1) (v : Fin ub → Bool) (st : NmT S M U0 U1 pS → Tree) :
    ov9 id (some v : UW ub) st = Function.update st (.cont id) (ofBits (List.ofFn v)) := rfl

theorem foldl_ov9 (b : G.Uid (K + K) U0 M.N U1 → UW ub) (s : List (G.Uid (K + K) U0 M.N U1))
    (st : NmT S M U0 U1 pS → Tree) :
    (∀ id ∈ s, ∀ v, b id = some v → (s.foldl (fun st id => ov9 id (b id) st) st) (.cont id) = ofBits (List.ofFn v)) ∧
    ∀ y, (∀ id, y ≠ .cont id) → (s.foldl (fun st id => ov9 id (b id) st) st) y = st y := by
  induction s using List.reverseRecOn generalizing st with
  | nil => exact ⟨fun id h => absurd h (by simp), fun _ _ => rfl⟩
  | append_singleton s id ih =>
    obtain ⟨h1, h2⟩ := ih st
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨fun id' hid' v hv => ?_, fun y hy => ?_⟩
    · by_cases h : id' = id
      · subst h
        rw [hv, ov9_some, Function.update_self]
      · have h3 : id' ∈ s := by
          rw [List.mem_append, List.mem_singleton] at hid'
          exact hid'.resolve_right h
        rw [← h1 id' h3 v hv]
        cases b id with
        | none => rfl
        | some w =>
          rw [ov9_some, Function.update_of_ne]
          intro h4
          exact h (by simpa using h4)
    · rw [← h2 y hy]
      cases b id with
      | none => rfl
      | some w => exact Function.update_of_ne (hy id) _ _

theorem phase9 {st : NmT S M U0 U1 pS → Tree} {cut : G.Uid (K + K) U0 M.N U1 → Bool}
    (hc : ∀ id, st (.cut id) = bit (cut id)) (Φ : (List Bool → Tree) → B) :
    ((execAll ub (steps9 C) (byPath C.nm st)).map Φ).sum = ∑ b : G.Uid (K + K) U0 M.N U1 → UW ub,
      if ∀ id, b id ≠ none ↔ cut id = true then
        Φ (byPath C.nm ((univ : Finset (G.Uid (K + K) U0 M.N U1)).toList.foldl (fun st id => ov9 id (b id) st) st))
      else 0 := by
  classical
  rw [steps9, execAll_choices (opts := fun id => optsB ub (cut id)) (L := byPath C.nm) (ov := ov9)
    (good := fun st => ∀ id, st (.cut id) = bit (cut id)) (fun id st hst => ?_) (fun id st w hw hst id' => ?_)
    (Finset.nodup_toList _) hc (fun _ => none), sum_funs_univ _ fun id => nodup_optsB (cut id)]
  · refine Finset.sum_congr rfl fun b _ => ?_
    have key : (∀ id, b id ∈ optsB ub (cut id)) ↔ ∀ id, b id ≠ none ↔ cut id = true := forall_congr' fun id => mem_optsB
    by_cases h : ∀ id, b id ≠ none ↔ cut id = true
    · rw [if_pos h, if_pos (key.2 h)]
    · rw [if_neg h, if_neg fun h' => h (key.1 h')]
  · rw [exec_bits C.nm_inj, hst]
    unfold optsB
    cases cut id
    · rfl
    · simp only [if_true, List.map_map]
      rw [if_neg (by simp [bit, one])]
      refine List.map_congr_left fun u hu => ?_
      have h1 := uwBits_wOf (length_allBits hu)
      simp only [Function.comp_apply, wOf, ov9]
      rw [wOf] at h1
      simp only [uwBits] at h1
      rw [h1]
  · rw [← hst id']
    cases w with
    | none => rfl
    | some v => exact Function.update_of_ne (show (Nm.cut id' : NmT S M U0 U1 pS) ≠ .cont id by simp) _ _

end Bits

end Nc.Dl
end
/- Source module Nc.Dl.Scr. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

section Lists


def listTm : List Tm → Tm
  | [] => .c .nil
  | t :: ts => .cons t (listTm ts)

theorem expand_listTm (σ : List Bool → Tree) (ts : List Tm) : (listTm ts).expand σ = listT (ts.map (Tm.expand σ)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [listTm, Tm.expand, ih, listT]


def catTm : List Tm → Tm
  | [] => .c .nil
  | t :: ts => .app t (catTm ts)

theorem expand_catTm (σ : List Bool → Tree) (ts : List Tm) :
    (catTm ts).expand σ = listT (ts.flatMap fun t => (t.expand σ).toList) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [catTm, Tm.expand, ih, toList_listT, List.flatMap_cons]


def ifTm (p : List Bool) (t : Tree) (a : Tm) : Tm := .ifeq p t a (.c .nil)

theorem expand_ifTm (σ : List Bool → Tree) (p : List Bool) (t : Tree) (a : Tm) :
    ((ifTm p t a).expand σ).toList = if σ p = t then (a.expand σ).toList else [] := by
  rw [ifTm, Tm.expand]
  split_ifs <;> rfl

theorem flatMap_if {α β : Type*} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → List β) :
    (l.flatMap fun a => if p a then f a else []) = (l.filter p).flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih]

end Lists

variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] {K A' E U0 U1 ub mm D pS c : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS)

section Templates

variable (tab : SlpTab P grp D pS) (tg : M.R → ℕ) (bT bub : List Bool) (gt : Fin mm → Tree) (d1 : Tree)


def gN (x : NmT S M U0 U1 pS) : Tm := .get (C.nm x)


noncomputable def bodyTm (p : Fin (K + K)) : Tm :=
  .cons (listTm ((univ : Finset (Option S)).toList.map fun s => gN C (.flag s p)))
    (.cons (listTm (List.ofFn fun b => gN C (.kR p b))) (listTm (List.ofFn fun b => gN C (.kC b p))))


noncomputable def baseTm (p : Fin (K + K)) : Tm :=
  Fin.addCases (motive := fun _ => Tm)
    (fun κ => .cons (.c (num 0)) (.cons (.cons (gN C (.q κ.castSucc)) (gN C (.q κ.succ))) (bodyTm C (Fin.castAdd K κ))))
    (fun κ => .cons (.c (num 1)) (.cons (gN C (.part κ)) (bodyTm C (Fin.natAdd K κ)))) p


noncomputable def basesTm (p : Fin (K + K)) : Tm := .cons (baseTm C p) (gN C (.dg p))


noncomputable def slotTm (z : M.Z) (a : Fin (K + K + A')) : Tm :=
  catTm ((G.allIds (K + K) U0 M.N U1).reverse.map fun id =>
    ifTm (C.nm (.slp (tab.kcons z id))) d1 (.c (listT [ofBits (C.key (a, id))])))


noncomputable def roleTm (r : M.R) : Tm :=
  .cons (.c (num (4 + tg r))) (.cons (gN C (.num r.1)) (.cons
    (listTm ((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map fun e => slotTm C tab d1 ⟨r.1, e.1⟩ (M.rp r)))
    (listTm ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      gN C (.ch ⟨r.1, ν.1⟩ (decide ((M.kind r.1).c ν.1 ≠ r.2)))))))


def oneTm (k : List Bool) (id : G.Uid (K + K) U0 M.N U1) : Tm :=
  listTm [.cons (.c (num 3)) (.cons (.c (ofBits k)) (gN C (.cont id)))]


noncomputable def endTm (g : Fin mm) (id : G.Uid (K + K) U0 M.N U1) : Tm :=
  ifTm (C.nm (.slp (tab.kcur id))) d1
    (.ifeq (C.nm (.slp (tab.kgrp (G.hold0 M.np id)))) (gt g)
      (.ifeq (C.nm (.slp (tab.kgrp (G.hold1 M.np id)))) (gt g)
        (.c (listT [(Grp.Ins.both (C.key (G.hold0 M.np id, id)) (C.key (G.hold1 M.np id, id))).tree]))
        (oneTm C (C.key (G.hold0 M.np id, id)) id))
      (ifTm (C.nm (.slp (tab.kgrp (G.hold1 M.np id)))) (gt g) (oneTm C (C.key (G.hold1 M.np id, id)) id)))


noncomputable def scriptTm (g : Fin mm) : Tm :=
  .cons (.c (.cons (ofBits bT) (ofBits bub))) (catTm (
    (List.finRange (K + K)).map (fun p =>
      ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)) ++
    (Grp.allRoles M).map (fun r => ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g) (listTm [roleTm C tab tg d1 r])) ++
    (G.allIds (K + K) U0 M.N U1).map (endTm C tab gt d1 g)))

end Templates


structure Final (C : Codes S M U0 U1 D pS) (tab : SlpTab P grp D pS) (qn : Q → ℕ) (pt : Fin K → Tree)
    (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1)
    (b : G.Uid (K + K) U0 M.N U1 → UW ub) (st : NmT S M U0 U1 pS → Tree) : Prop where
  part : ∀ κ, st (.part κ) = pt κ
  q : ∀ a, st (.q a) = num (qn (q a))
  flag : ∀ s p, st (.flag s p) = flagT (ρ s p)
  kR : ∀ a b, st (.kR a b) = kRT C a b (n a b)
  kC : ∀ a b, st (.kC a b) = kCT C a b (n a b)
  dg : ∀ a, st (.dg a) = dgT C a (n a a)
  ch : ∀ ν d, st (.ch ν d) = chT C ν d (o ν)
  slp : ∀ k, st (.slp k) = C.dt (tab.fn k (n, o))
  num : ∀ x, st (.num x) = NS1.Tree.num (P.num n o x)
  cont : ∀ id v, b id = some v → st (.cont id) = ofBits (List.ofFn v)

section Expand

variable {C} {tab : SlpTab P grp D pS} {qn : Q → ℕ} {pt : Fin K → Tree} {q : Fin (K + 1) → Q}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : NN K U0} {o : M.N → Fin U1}
  {b : G.Uid (K + K) U0 M.N U1 → UW ub} {st : NmT S M U0 U1 pS → Tree} {tg : M.R → ℕ} {bT bub : List Bool}
  {cb : Option Γ → Fin c → Bool} {x : Fin K → List Γ}

theorem expand_gN (y : NmT S M U0 U1 pS) : (gN C y).expand (byPath C.nm st) = st y := byPath_nm C.nm_inj st y

theorem dt_inj : Function.Injective C.dt := by
  intro d d' h
  apply C.dc_inj
  rw [← path_ofBits (C.dc d), ← path_ofBits (C.dc d')]
  exact congrArg Tree.path h

variable (h : Final C tab qn pt q ρ n o b st)

include h

theorem expand_bodyTm (p : Fin (K + K)) :
    (bodyTm C p).expand (byPath C.nm st) = (Grp.bodyOf ρ n C.key C.dkey p).tree := by
  simp only [bodyTm, Tm.expand, expand_listTm, List.map_map, Function.comp_def, expand_gN, Grp.Body.tree, Grp.bodyOf,
    Grp.keysT, List.map_ofFn]
  congr 1
  · congr 1
    exact List.map_congr_left fun s _ => h.flag s p
  · congr 1
    · congr 2
      funext b'
      rw [h.kR]
      rfl
    · congr 2
      funext b'
      rw [h.kC]
      rfl

theorem expand_baseTm (hpt : ∀ κ, pt κ = listT (((x κ).map fun a => ofBits (List.ofFn (cb (some a)))).reverse))
    (p : Fin (K + K)) : (basesTm C p).expand (byPath C.nm st) =
      listT ((Grp.baseIns qn cb q x ρ n C.key C.dkey p).map Grp.Ins.tree) := by
  rw [basesTm, Tm.expand, Grp.baseIns, List.map_cons, expand_gN, h.dg]
  show _ = Tree.cons _ _
  congr 1
  · refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
    · rw [baseTm, Fin.addCases_left, Fin.addCases_left]
      simp only [Tm.expand, expand_gN, h.q, expand_bodyTm h, Grp.Ins.tree]
    · rw [baseTm, Fin.addCases_right, Fin.addCases_right]
      simp only [Tm.expand, expand_gN, h.part, expand_bodyTm h, Grp.Ins.tree, hpt, List.map_reverse, List.map_map,
        Function.comp_def]
  · rw [dgT, List.map_map]
    rfl

theorem expand_slotTm {d1 : Tree} (hd1 : ∀ d : Fin D, C.dt d = d1 ↔ d.1 = 1) (z : M.Z) (a : Fin (K + K + A')) :
    (slotTm C tab d1 z a).expand (byPath C.nm st) =
      listT ((((P.ids n o z).map fun id => C.key (a, id)).reverse).map ofBits) := by
  classical
  rw [slotTm, expand_catTm, List.flatMap_map]
  congr 1
  have e : ∀ id, ((ifTm (C.nm (.slp (tab.kcons z id))) d1 (.c (listT [ofBits (C.key (a, id))]))).expand
      (byPath C.nm st)).toList = if id ∈ P.cons n o z then [ofBits (C.key (a, id))] else [] := by
    intro id
    rw [expand_ifTm, byPath_nm C.nm_inj, h.slp]
    refine if_congr ?_ rfl rfl
    rw [hd1, tab.hcons]
    split_ifs with hc <;> simp [hc]
  simp only [e]
  rw [flatMap_if, flatMap_single, G.Plan.ids, ← List.map_reverse, ← List.filter_reverse, List.map_map]
  rfl

theorem expand_roleTm {d1 : Tree} (hd1 : ∀ d : Fin D, C.dt d = d1 ↔ d.1 = 1) (r : M.R) :
    (roleTm C tab tg d1 r).expand (byPath C.nm st) = (Grp.roleIns P n o C.key tg r).tree := by
  simp only [roleTm, Tm.expand, expand_listTm, List.map_map, Function.comp_def, expand_gN, h.num, Grp.roleIns,
    Grp.Ins.tree, Grp.keysT]
  congr 3
  · congr 1
    exact List.map_congr_left fun e _ => expand_slotTm h hd1 _ _
  · congr 1
    refine List.map_congr_left fun ν _ => ?_
    rw [h.ch]
    have hp : M.np ⟨r.1, ν.1⟩ (decide ((M.kind r.1).c ν.1 ≠ r.2)) = M.rp r := by
      obtain ⟨x', p⟩ := r
      obtain ⟨ν, hν⟩ := ν
      simp only [Sys.np, Sys.nr, Law.cnEnd, Sys.rp]
      by_cases hc : (M.kind x').c ν = p
      · simp [hc]
      · have hd : (M.kind x').d ν = p := hν.resolve_left hc
        simp [hc, hd]
    rw [chT, hp]

theorem expand_endTm {d1 : Tree} {gt : Fin mm → Tree} (hd1 : ∀ d : Fin D, C.dt d = d1 ↔ d.1 = 1)
    (hgt : ∀ (d : Fin D) g, C.dt d = gt g ↔ d.1 = g.1)
    (hb : ∀ id ∈ P.cur n o E, grp n o (G.hold0 M.np id) ≠ grp n o (G.hold1 M.np id) → b id ≠ none) (g : Fin mm)
    (id : G.Uid (K + K) U0 M.N U1) : ((endTm C tab gt d1 g id).expand (byPath C.nm st)).toList =
      (if id ∈ P.cur n o E then
        ((if grp n o (G.hold0 M.np id) = g then
          if grp n o (G.hold1 M.np id) = g then some (Grp.Ins.both (C.key (G.hold0 M.np id, id)) (C.key (G.hold1 M.np id, id)))
          else some (.one (C.key (G.hold0 M.np id, id)) (uwBits (b id)))
        else if grp n o (G.hold1 M.np id) = g then some (.one (C.key (G.hold1 M.np id, id)) (uwBits (b id)))
        else none).map Grp.Ins.tree).toList else []) := by
  classical
  have hslp : ∀ k, byPath C.nm st (C.nm (.slp k)) = C.dt (tab.fn k (n, o)) := fun k => by
    rw [byPath_nm C.nm_inj, h.slp]
  have hg : ∀ p, (C.dt (tab.fn (tab.kgrp p) (n, o)) = gt g ↔ grp n o p = g) := by
    intro p
    rw [hgt, tab.hgrp]
    exact Fin.ext_iff.symm
  have hone : ∀ k, b id ≠ none → (oneTm C k id).expand (byPath C.nm st) = listT [(Grp.Ins.one k (uwBits (b id))).tree] := by
    intro k hbn
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hbn
    simp only [oneTm, expand_listTm, List.map_cons, List.map_nil, Tm.expand, expand_gN, h.cont id v hv, Grp.Ins.tree, hv,
      uwBits]
  rw [endTm, expand_ifTm, hslp]
  have hcur : C.dt (tab.fn (tab.kcur id) (n, o)) = d1 ↔ id ∈ P.cur n o E := by
    rw [hd1, tab.hcur]
    split_ifs with hc <;> simp [hc]
  by_cases hc : id ∈ P.cur n o E
  swap
  · rw [if_neg fun h' => hc (hcur.1 h'), if_neg hc]
  rw [if_pos (hcur.2 hc), if_pos hc]
  simp only [Tm.expand, hslp]
  by_cases h0 : grp n o (G.hold0 M.np id) = g
  · rw [if_pos ((hg _).2 h0), if_pos h0]
    by_cases h1 : grp n o (G.hold1 M.np id) = g
    · rw [if_pos ((hg _).2 h1), if_pos h1]
      rfl
    · rw [if_neg fun h' => h1 ((hg _).1 h'), if_neg h1, hone _ (hb id hc fun h' => h1 (h' ▸ h0))]
      simp
  · rw [if_neg fun h' => h0 ((hg _).1 h'), if_neg h0]
    rw [expand_ifTm, hslp]
    by_cases h1 : grp n o (G.hold1 M.np id) = g
    · rw [if_pos ((hg _).2 h1), if_pos h1, hone _ (hb id hc fun h' => h0 (h'.trans h1))]
      simp
    · rw [if_neg fun h' => h1 ((hg _).1 h'), if_neg h1]
      rfl


theorem expand_scriptTm {d1 : Tree} {gt : Fin mm → Tree} (hd1 : ∀ d : Fin D, C.dt d = d1 ↔ d.1 = 1)
    (hgt : ∀ (d : Fin D) g, C.dt d = gt g ↔ d.1 = g.1)
    (hpt : ∀ κ, pt κ = listT (((x κ).map fun a => ofBits (List.ofFn (cb (some a)))).reverse))
    (hb : ∀ id ∈ P.cur n o E, grp n o (G.hold0 M.np id) ≠ grp n o (G.hold1 M.np id) → b id ≠ none) (g : Fin mm) :
    (scriptTm C tab tg bT bub gt d1 g).expand (byPath C.nm st) =
      Grp.scriptT bT bub (Grp.script qn cb P q x ρ n o (grp n o) g C.key C.dkey tg b) := by
  classical
  have hslp : ∀ k, byPath C.nm st (C.nm (.slp k)) = C.dt (tab.fn k (n, o)) := fun k => by
    rw [byPath_nm C.nm_inj, h.slp]
  have hg : ∀ p, (C.dt (tab.fn (tab.kgrp p) (n, o)) = gt g ↔ grp n o p = g) := by
    intro p
    rw [hgt, tab.hgrp]
    exact Fin.ext_iff.symm
  rw [scriptTm, Tm.expand, Tm.expand, Grp.scriptT, expand_catTm]
  congr 2
  rw [Grp.script, List.flatMap_append, List.flatMap_append, List.map_append, List.map_append, List.flatMap_map,
    List.flatMap_map, List.flatMap_map]
  congr 1
  · congr 1
    · have e : ∀ p : Fin (K + K), ((ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)).expand
          (byPath C.nm st)).toList = if grp n o (Fin.castAdd A' p) = g then
          (Grp.baseIns qn cb q x ρ n C.key C.dkey p).map Grp.Ins.tree else [] := by
        intro p
        rw [expand_ifTm, hslp, expand_baseTm h hpt, toList_listT]
        exact if_congr (hg _) rfl rfl
      simp only [e]
      rw [flatMap_if, Grp.baseList, List.map_flatMap]
    · have e : ∀ r : M.R, ((ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g) (listTm [roleTm C tab tg d1 r])).expand
          (byPath C.nm st)).toList = if grp n o (M.rp r) = g then [(Grp.roleIns P n o C.key tg r).tree] else [] := by
        intro r
        rw [expand_ifTm, hslp, expand_listTm, toList_listT]
        refine if_congr (hg _) ?_ rfl
        simp [expand_roleTm h hd1]
      simp only [e]
      rw [flatMap_if, flatMap_single, Grp.roleList, List.map_map]
      rfl
  · simp only [expand_endTm h hd1 hgt hb]
    rw [Grp.endIns]
    generalize G.allIds (K + K) U0 M.N U1 = l
    induction l with
    | nil => rfl
    | cons id l ih =>
      rw [List.flatMap_cons, ih]
      by_cases hc : id ∈ P.cur n o E
      · simp only [hc, if_true, List.filter_cons_of_pos, decide_true, List.filterMap_cons]
        cases (if grp n o (G.hold0 M.np id) = g then
          if grp n o (G.hold1 M.np id) = g then some (Grp.Ins.both (C.key (G.hold0 M.np id, id)) (C.key (G.hold1 M.np id, id)))
          else some (.one (C.key (G.hold0 M.np id, id)) (uwBits (b id)))
        else if grp n o (G.hold1 M.np id) = g then some (.one (C.key (G.hold1 M.np id, id)) (uwBits (b id)))
        else none) <;> simp
      · simp [hc]

end Expand

end Nc.Dl
end
/- Source module Nc.Dl.Total. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

variable {B : Type} [CommRing B] {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) {m : ℕ}
  (tab : SlpTab P grp D pS) (pt : Fin K → Tree) (qn : Q → ℕ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D)


def S4 (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1) :
    NmT S M U0 U1 pS → Tree := fun x =>
  if (own4 x).isSome then v4 C hU1 o x else if (own3 x).isSome then v3 C hU0 (fun a => n a.1 a.2) x else
    if (own2 x).isSome then v2 C (fun a => ρ a.1 a.2) x else S1 pt qn q x


structure Mid (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1)
    (st : NmT S M U0 U1 pS → Tree) : Prop where
  part : ∀ κ, st (.part κ) = pt κ
  q : ∀ a, st (.q a) = num (qn (q a))
  flag : ∀ s p, st (.flag s p) = flagT (ρ s p)
  kR : ∀ a b, st (.kR a b) = kRT C a b (n a b)
  kC : ∀ a b, st (.kC a b) = kCT C a b (n a b)
  dg : ∀ a, st (.dg a) = dgT C a (n a a)
  ch : ∀ ν d, st (.ch ν d) = chT C ν d (o ν)
  slp : ∀ k, st (.slp k) = C.dt (tab.fn k (n, o))
  num : ∀ x, st (.num x) = NS1.Tree.num (P.num n o x)
  row : ∀ s p, st (.row s p) ≠ .nil ↔ ValidRow (ρ s) p
  good : ∀ x, st (.cond (some x)) ≠ .nil ↔ P.good n o x
  valid : st (.cond none) ≠ .nil ↔ tab.valid n
  cut : ∀ id, ∃ c : Bool, st (.cut id) = bit c ∧
    (c = true ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E))

theorem exists_mid (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0)
    (o : M.N → Fin U1) : ∃ st : NmT S M U0 U1 pS → Tree,
    execAll m (steps5 C ++ (steps6 C tab ++ steps7 C tab)) (byPath C.nm (S4 C pt qn hU0 hU1 q ρ n o)) =
      [byPath C.nm st] ∧ Mid C tab pt qn q ρ n o st := by
  classical
  obtain ⟨s4, hs4⟩ : ∃ s, s = S4 C pt qn hU0 hU1 q ρ n o := ⟨_, rfl⟩
  have z4 : s4 .zero = .nil := by rw [hs4]; rfl
  have r4 : ∀ s p, s4 (.rd s p) = ofBits (C.rc (ρ s p)) := fun s p => by rw [hs4]; rfl
  have h5 := phase5 C (m := m) z4 r4
  obtain ⟨s5, hs5⟩ : ∃ s : NmT S M U0 U1 pS → Tree, s = fun x =>
      if h : ∃ a : Option S × Fin (K + K), Nm.row a.1 a.2 = x then bit (decide (ValidRow (ρ h.choose.1) h.choose.2))
      else s4 x := ⟨_, rfl⟩
  rw [← hs5] at h5
  have k5 : ∀ y, (∀ s p, y ≠ .row s p) → s5 y = s4 y := by
    intro y hy
    rw [hs5]
    exact dif_neg fun ⟨a, ha⟩ => hy a.1 a.2 ha.symm
  have w5 : ∀ s p, s5 (.row s p) = bit (decide (ValidRow (ρ s) p)) := by
    intro s p
    have h : ∃ a : Option S × Fin (K + K), (Nm.row a.1 a.2 : NmT S M U0 U1 pS) = .row s p := ⟨(s, p), rfl⟩
    rw [hs5]
    simp only [dif_pos h]
    have hinj : ∀ (s s' : Option S) (p p' : Fin (K + K)), (Nm.row s p : NmT S M U0 U1 pS) = .row s' p' → s = s' ∧ p = p' :=
      fun s s' p p' h => by simpa using h
    obtain ⟨h1, h2⟩ := hinj _ _ _ _ h.choose_spec
    rw [h1, h2]
  have hc : ∀ c, s5 (coord c) = C.dt (tab.inp c (n, o)) := by
    intro c
    rw [k5 _ fun s p => by cases c <;> simp [coord]]
    rcases c with ⟨a, b⟩ | ν
    · rw [hs4]
      show C.dt (digN hU0 (n a b)) = _
      congr 1
      apply Fin.ext
      rw [tab.inpN]
      rfl
    · rw [hs4]
      show C.dt (digO hU1 (o ν)) = _
      congr 1
      apply Fin.ext
      rw [tab.inpO]
      rfl
  obtain ⟨s6, h6, w6, k6⟩ := phase6 C tab (m := m) (n, o) (by rw [k5 _ fun s p => by simp]; exact z4) hc
  have z6 : s6 .zero = .nil := by rw [k6 _ fun k => by simp, k5 _ fun s p => by simp]; exact z4
  have h7 := phase7 C tab (m := m) (n, o) z6 w6
  obtain ⟨s7, hs7⟩ : ∃ s : NmT S M U0 U1 pS → Tree, s = fun y =>
      if h : ∃ a : Ix7 M U0 U1, nm7 a = y then v7 tab (n, o) h.choose else s6 y := ⟨_, rfl⟩
  rw [← hs7] at h7
  have k7 : ∀ y, (∀ a, y ≠ nm7 a) → s7 y = s6 y := by
    intro y hy
    rw [hs7]
    exact dif_neg fun ⟨a, ha⟩ => hy a ha.symm
  have w7 : ∀ a, s7 (nm7 a) = v7 tab (n, o) a := by
    intro a
    have h : ∃ a' : Ix7 M U0 U1, (nm7 a' : NmT S M U0 U1 pS) = nm7 a := ⟨a, rfl⟩
    rw [hs7]
    simp only [dif_pos h]
    rw [nm7_inj h.choose_spec]
  have old : ∀ y, (∀ s p, y ≠ .row s p) → (∀ k, y ≠ .slp k) → (∀ a, y ≠ nm7 a) → s7 y = s4 y := fun y h1 h2 h3 => by
    rw [k7 y h3, k6 y h2, k5 y h1]
  refine ⟨s7, ?_, ?_⟩
  · rw [← hs4, execAll_append, h5, List.flatMap_cons, List.flatMap_nil, List.append_nil, execAll_append, h6,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, h7]
  · have n7 : ∀ y : NmT S M U0 U1 pS, (∀ x, y ≠ .num x) → (∀ x, y ≠ .cond x) → (∀ x, y ≠ .cut x) → ∀ a, y ≠ nm7 a := by
      rintro y h1 h2 h3 (x | c | id)
      · exact h1 x
      · exact h2 c
      · exact h3 id
    refine ⟨fun κ => ?_, fun a => ?_, fun s p => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun ν d => ?_, fun k => ?_,
      fun x => ?_, fun s p => ?_, fun x => ?_, ?_, fun id => ?_⟩
    · rw [old _ (by simp) (by simp) (n7 _ (by simp) (by simp) (by simp)), hs4]; rfl
    · rw [old _ (by simp) (by simp) (n7 _ (by simp) (by simp) (by simp)), hs4]; rfl
    · rw [old _ (by simp) (by simp) (n7 _ (by simp) (by simp) (by simp)), hs4]; rfl
    · rw [old _ (by simp) (by simp) (n7 _ (by simp) (by simp) (by simp)), hs4]; rfl
    · rw [old _ (by simp) (by simp) (n7 _ (by simp) (by simp) (by simp)), hs4]; rfl
    · rw [old _ (by simp) (by simp) (n7 _ (by simp) (by simp) (by simp)), hs4]; rfl
    · rw [old _ (by simp) (by simp) (n7 _ (by simp) (by simp) (by simp)), hs4]; rfl
    · rw [k7 _ (n7 _ (by simp) (by simp) (by simp)), w6]
    · have := w7 (.inl x)
      simp only [nm7, v7] at this
      rw [this, tab.hnum]
    · rw [k7 _ (n7 _ (by simp) (by simp) (by simp)), k6 _ (by simp), w5, bit_ne_nil, decide_eq_true_eq]
    · have := w7 (.inr (.inl (some x)))
      simp only [nm7, v7] at this
      rw [this, bit_ne_nil, decide_eq_true_eq, tab.hgood]
    · have := w7 (.inr (.inl none))
      simp only [nm7, v7] at this
      rw [this, bit_ne_nil, decide_eq_true_eq, tab.hvalid]
    · have := w7 (.inr (.inr id))
      simp only [nm7, v7] at this
      refine ⟨_, this, ?_⟩
      rw [decide_eq_true_eq, tab.hcut, cutUnits, Finset.mem_filter]
      split_ifs with h <;> simp [h]


noncomputable def allSteps (i e : Q) : List DStep :=
  steps1 C qn i e ++ (steps2 C ++ (steps3 C hU0 ++ (steps4 C hU1 ++ ((steps5 C ++ (steps6 C tab ++ steps7 C tab)) ++
    (steps8 C ++ steps9 C)))))

open Classical in

theorem sum_allSteps (hK : 0 < K) [Nonempty Q] [Nonempty (Fin U1)] : ∃ st : (Fin (K + 1) → Q) →
    (Option S → Fin (K + K) → RowData (K + K)) → NN K U0 → (M.N → Fin U1) →
    (G.Uid (K + K) U0 M.N U1 → UW ub) → NmT S M U0 U1 pS → Tree,
    (∀ q ρ n o b, Final C tab qn pt q ρ n o b (st q ρ n o b)) ∧ ∀ (B : Type) [CommRing B] (Φ : (List Bool → Tree) → B),
    ((execAll ub (allSteps C tab qn hU0 hU1 i e) (byPath C.nm (S0 pt))).map Φ).sum =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
          ∑ n : NN K U0, if tab.valid n then ∑ o : M.N → Fin U1, if ∀ x, P.good n o x then
            ∑ b : G.Uid (K + K) U0 M.N U1 → UW ub,
              if ∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E) then
                Φ (byPath C.nm (st q ρ n o b)) else 0
            else 0 else 0 else 0 else 0 := by
  have hmid := fun q ρ n o => exists_mid (m := ub) C tab pt qn hU0 hU1 q ρ n o
  choose s7 hs7 hm7 using hmid
  refine ⟨fun q ρ n o b => (univ : Finset (G.Uid (K + K) U0 M.N U1)).toList.foldl (fun st id => ov9 id (b id) st)
    (s7 q ρ n o), fun q ρ n o b => ?_, fun B _ Φ => ?_⟩
  · obtain ⟨f1, f2⟩ := foldl_ov9 b (univ : Finset (G.Uid (K + K) U0 M.N U1)).toList (s7 q ρ n o)
    have h := hm7 q ρ n o
    refine ⟨fun κ => ?_, fun a => ?_, fun s p => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun ν d => ?_, fun k => ?_,
      fun x => ?_, fun id v hv => f1 id (Finset.mem_toList.2 (Finset.mem_univ _)) v hv⟩
    · exact (f2 _ fun _ => by simp).trans (h.part κ)
    · exact (f2 _ fun _ => by simp).trans (h.q a)
    · exact (f2 _ fun _ => by simp).trans (h.flag s p)
    · exact (f2 _ fun _ => by simp).trans (h.kR a b)
    · exact (f2 _ fun _ => by simp).trans (h.kC a b)
    · exact (f2 _ fun _ => by simp).trans (h.dg a)
    · exact (f2 _ fun _ => by simp).trans (h.ch ν d)
    · exact (f2 _ fun _ => by simp).trans (h.slp k)
    · exact (f2 _ fun _ => by simp).trans (h.num x)
  · have hne : Nonempty (RowData (K + K)) := ⟨(false, ⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    rw [allSteps, sum_execAll_append, phase1 C pt qn i e hK fun σ' => _]
    refine Finset.sum_congr rfl fun q _ => if_congr Iff.rfl ?_ rfl
    rw [sum_execAll_append, phase2 C (by rfl) fun σ' => _]
    -- row data, numbers, outcomes
    have h4 : ∀ ρ, ((execAll ub (steps3 C hU0 ++ (steps4 C hU1 ++ ((steps5 C ++ (steps6 C tab ++ steps7 C tab)) ++
        (steps8 C ++ steps9 C)))) (byPath C.nm fun x => if (own2 x).isSome then v2 C (fun a => ρ a.1 a.2) x else
          S1 pt qn q x)).map Φ).sum = if ValidRows ρ then
          ∑ n : NN K U0, if tab.valid n then ∑ o : M.N → Fin U1, if ∀ x, P.good n o x then
            ∑ b : G.Uid (K + K) U0 M.N U1 → UW ub,
              if ∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E) then
                Φ (byPath C.nm ((univ : Finset (G.Uid (K + K) U0 M.N U1)).toList.foldl (fun st id => ov9 id (b id) st)
                  (s7 q ρ n o))) else 0
            else 0 else 0 else 0 := by
      intro ρ
      rw [sum_execAll_append, phase3 C hU0 (by rfl) fun σ' => _]
      have h5 : ∀ n : NN K U0, ((execAll ub (steps4 C hU1 ++ ((steps5 C ++ (steps6 C tab ++ steps7 C tab)) ++
          (steps8 C ++ steps9 C))) (byPath C.nm fun x => if (own3 x).isSome then v3 C hU0 (fun a => n a.1 a.2) x else
            if (own2 x).isSome then v2 C (fun a => ρ a.1 a.2) x else S1 pt qn q x)).map Φ).sum =
          ∑ o : M.N → Fin U1, if ValidRows ρ ∧ tab.valid n ∧ ∀ x, P.good n o x then
            ∑ b : G.Uid (K + K) U0 M.N U1 → UW ub,
              if ∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E) then
                Φ (byPath C.nm ((univ : Finset (G.Uid (K + K) U0 M.N U1)).toList.foldl (fun st id => ov9 id (b id) st)
                  (s7 q ρ n o))) else 0
            else 0 := by
        intro n
        rw [sum_execAll_append, phase4 C hU1 (by rfl) fun σ' => _]
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [sum_execAll_append]
        have e4 : (fun x : NmT S M U0 U1 pS => if (own4 x).isSome then v4 C hU1 o x else
            if (own3 x).isSome then v3 C hU0 (fun a => n a.1 a.2) x else
            if (own2 x).isSome then v2 C (fun a => ρ a.1 a.2) x else S1 pt qn q x) = S4 C pt qn hU0 hU1 q ρ n o := rfl
        rw [e4, hs7 q ρ n o, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, sum_execAll_append]
        have hm := hm7 q ρ n o
        by_cases hcond : ValidRows ρ ∧ tab.valid n ∧ ∀ x, P.good n o x
        · rw [if_pos hcond, phase8_pos C (fun s p => (hm.row s p).2 (hcond.1 s p)) (fun c => by
            cases c with
            | none => exact hm.valid.2 hcond.2.1
            | some x => exact (hm.good x).2 (hcond.2.2 x)), List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          choose cutb hcut1 hcut2 using hm.cut
          rw [phase9 C hcut1 Φ]
          refine Finset.sum_congr rfl fun b _ => if_congr (forall_congr' fun id => ?_) rfl rfl
          rw [hcut2]
        · rw [if_neg hcond, phase8_neg]
          · simp
          · by_contra hc
            push Not at hc
            refine hcond ⟨fun s p => (hm.row s p).1 (hc.1 s p), hm.valid.1 (hc.2 none), fun x => (hm.good x).1 (hc.2 (some x))⟩
      simp only [h5]
      by_cases hv : ValidRows ρ
      · rw [if_pos hv]
        refine Finset.sum_congr rfl fun n _ => ?_
        by_cases hvn : tab.valid n
        · rw [if_pos hvn]
          refine Finset.sum_congr rfl fun o _ => if_congr ?_ rfl rfl
          simp [hv, hvn]
        · rw [if_neg hvn]
          refine Finset.sum_eq_zero fun o _ => if_neg ?_
          rintro ⟨-, h, -⟩
          exact hvn h
      · rw [if_neg hv]
        refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun o _ => if_neg ?_
        rintro ⟨h, -⟩
        exact hv h
    exact Finset.sum_congr rfl fun ρ _ => h4 ρ

end Nc.Dl
end
/- Source module NS1.Parts. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}



def partStep : Fm := lett
  (.cons (app takeB.code (.cons (.quote takeB.code) (.cons (.hd (.tl (.tl .id))) (.cons (.quote .nil) (.tl (.tl (.tl .id)))))))
    .id)
  (.cons (setF (.hd (.tl .id)) (.hd (.hd .id)) (.hd (.tl (.tl .id)))) (.cons (.hd (.tl (.tl (.tl .id)))) (.tl (.hd .id))))


def partFun (m : ℕ) (x σ : Tree) : Tree :=
  .cons (tset x.path (listT (σ.tl.tl.toList.take m).reverse) σ.hd) (.cons σ.tl.hd (listT (σ.tl.tl.toList.drop m)))

theorem partStep_gives (x W : Tree) (w : List Bool) (l : List Tree) :
    Gives θ partStep (.cons x (.cons W (.cons (ofBits w) (listT l)))) (partFun (KT.val w) x (.cons W (.cons (ofBits w) (listT l))))
      (((l.take (KT.val w)).length + 1) * (60 * w.length + 100) + 60 * x.len + 100) := by
  have h1 := Gives.app (p := takeB.code) (Gives.cons (Gives.quote (θ := θ) takeB.code
    (.cons x (.cons W (.cons (ofBits w) (listT l))))) (Gives.cons (Gives.id _).tl.tl.hd
      (Gives.cons (Gives.quote (listT []) _) (Gives.id _).tl.tl.tl))) (by rw [Fm.ofTree_code]; exact takeB_gives w [] l)
  have h2 := Gives.cons h1 (Gives.id (θ := θ) (.cons x (.cons W (.cons (ofBits w) (listT l)))))
  rw [List.append_nil] at h2
  have h3 := setF_gives (Gives.id (θ := θ) (.cons (.cons (listT (l.take (KT.val w)).reverse) (listT (l.drop (KT.val w))))
    (.cons x (.cons W (.cons (ofBits w) (listT l)))))).tl.hd (Gives.id _).hd.hd (Gives.id _).tl.tl.hd
  have h4 := Gives.lett h2 (Gives.cons h3 (Gives.cons (Gives.id _).tl.tl.tl.hd (Gives.id _).hd.tl))
  have e : partFun (KT.val w) x (.cons W (.cons (ofBits w) (listT l))) =
      .cons (tset x.path (listT (l.take (KT.val w)).reverse) W) (.cons (ofBits w) (listT (l.drop (KT.val w)))) := by
    simp [partFun]
  rw [e]
  refine Gives.mono h4 ?_
  simp only [tl_cons, hd_cons]
  omega


def partsF (names : List (List Bool)) (n : List Bool) (l : Fm) : Fm :=
  .hd (foldF partStep (.cons (.quote .nil) (.cons (.quote (ofBits n)) l)) (.quote (listT (names.map ofBits))))


def partsT (m : ℕ) : List (List Bool) → Tree → List Tree → Tree
  | [], W, _ => W
  | p :: ps, W, l => partsT m ps (tset p (listT (l.take m).reverse) W) (l.drop m)

theorem foldl_partFun (m : ℕ) (names : List (List Bool)) (W nT : Tree) (l : List Tree) :
    ((names.map ofBits).foldl (fun σ x => partFun m x σ) (.cons W (.cons nT (listT l)))).hd = partsT m names W l := by
  induction names generalizing W l with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, List.foldl_cons, partsT]
    simp only [partFun, hd_cons, tl_cons, toList_listT, path_ofBits]
    exact ih _ _

theorem partsF_gives {lf : Fm} {x : Tree} {cl : ℕ} {l : List Tree} (hl : Gives θ lf x (listT l) cl)
    (names : List (List Bool)) (n : List Bool) (Ln : ℕ) (hn : ∀ p ∈ names, p.length ≤ Ln) :
    Gives θ (partsF names n lf) x (partsT (KT.val n) names .nil l)
      (cl + (l.length + names.length) * (60 * n.length + 100) + names.length * (60 * Ln + 130) + 40) := by
  -- the cost of the steps depends on the rest; we count with a potential
  have key : ∀ (ps : List (List Bool)) (W : Tree) (l : List Tree), (∀ p ∈ ps, p.length ≤ Ln) →
      Gives θ (foldB partStep) (.cons (foldB partStep).code (.cons (.cons W (.cons (ofBits n) (listT l)))
        (listT (ps.map ofBits)))) ((ps.map ofBits).foldl (fun σ x => partFun (KT.val n) x σ)
        (.cons W (.cons (ofBits n) (listT l)))) ((l.length + ps.length) * (60 * n.length + 100) + ps.length * (60 * Ln + 130) + 10) := by
    intro ps
    induction ps with
    | nil =>
      intro W l _
      exact (Gives.ite_false (Gives.id _).tl.tl (Gives.id _).tl.hd).mono (by omega)
    | cons p ps ih =>
      intro W l hps
      have hstep := partStep_gives (θ := θ) (ofBits p) W n l
      have e : partFun (KT.val n) (ofBits p) (.cons W (.cons (ofBits n) (listT l))) =
          .cons (tset p (listT (l.take (KT.val n)).reverse) W) (.cons (ofBits n) (listT (l.drop (KT.val n)))) := by
        simp [partFun]
      have e1 : Gives θ (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) partStep)
          (.cons (foldB partStep).code (.cons (.cons W (.cons (ofBits n) (listT l))) (listT ((p :: ps).map ofBits))))
          (partFun (KT.val n) (ofBits p) (.cons W (.cons (ofBits n) (listT l)))) _ :=
        Gives.lett (Gives.cons (Gives.id _).tl.tl.hd (Gives.id _).tl.hd) hstep
      have ih' : Gives θ (Fm.ofTree (foldB partStep).code) (.cons (foldB partStep).code
          (.cons (.cons (tset p (listT (l.take (KT.val n)).reverse) W) (.cons (ofBits n) (listT (l.drop (KT.val n)))))
          (listT (ps.map ofBits)))) ((ps.map ofBits).foldl (fun σ x => partFun (KT.val n) x σ)
          (.cons (tset p (listT (l.take (KT.val n)).reverse) W) (.cons (ofBits n) (listT (l.drop (KT.val n))))))
          (((l.drop (KT.val n)).length + ps.length) * (60 * n.length + 100) + ps.length * (60 * Ln + 130) + 10) := by
        rw [Fm.ofTree_code]
        exact ih _ _ fun q hq => hps q (List.mem_cons_of_mem _ hq)
      rw [e] at e1
      have r := Gives.run (Gives.id (θ := θ) (.cons (foldB partStep).code (.cons (.cons W (.cons (ofBits n) (listT l)))
        (listT ((p :: ps).map ofBits))))).hd (Gives.cons (Gives.id _).hd (Gives.cons e1 (Gives.id _).tl.tl.tl)) ih'
      rw [List.map_cons, List.foldl_cons, e]
      refine (Gives.ite_true (Gives.id _).tl.tl (by simp [listT]) r).mono ?_
      have hp := hps p List.mem_cons_self
      have hlen : (l.take (KT.val n)).length + (l.drop (KT.val n)).length = l.length := by
        rw [← List.length_append, List.take_append_drop]
      simp only [List.length_cons, len_ofBits]
      have e3 : (l.length + (ps.length + 1)) * (60 * n.length + 100) = ((l.take (KT.val n)).length + 1) * (60 * n.length + 100) +
          ((l.drop (KT.val n)).length + ps.length) * (60 * n.length + 100) := by
        rw [← hlen]
        ring
      have e4 : (ps.length + 1) * (60 * Ln + 130) = ps.length * (60 * Ln + 130) + (60 * Ln + 130) := by ring
      omega
  have h0 := Gives.cons (Gives.quote (θ := θ) .nil x) (Gives.cons (Gives.quote (ofBits n) x) hl)
  have h1 := Gives.app (p := (foldB partStep).code) (Gives.cons (Gives.quote (θ := θ) (foldB partStep).code x)
    (Gives.cons h0 (Gives.quote (listT (names.map ofBits)) x))) (by rw [Fm.ofTree_code]; exact key names .nil l hn)
  have h2 := Gives.hd h1
  rw [foldl_partFun] at h2
  exact h2.mono (by omega)

end NS1
end
/- Source module NS1.Compose. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}





def stepC (G : Tree) : Fm := lett (.cons (app G (.hd .id)) (.tl .id)) (appF (.hd .id) (.tl .id))


def compC (G G' : Tree) : Fm := lett (app G .id) (foldF (stepC G') (.quote .nil) .id)











end NS1
end
/- Source module Nc.Dl.DealThm. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

section Program

variable {A : Type} [CommRing A] {θ : List Bool → A}


def dealF (t0 t1 : Tree) (names : List (List Bool)) (nl nub : List Bool) (sts sts' : List DStep) (ts : List Tm) : Fm :=
  lett (dstepsF nub sts (partsF names nl (wordF t0 t1 .id))) (lett (dstepsF nub sts' .id) (tmsF ts .id))

theorem dealF_does (t0 t1 : Tree) (names : List (List Bool)) (nl nub : List Bool) (sts sts' : List DStep) (ts : List Tm)
    (z : Tree) {Ln : ℕ} (hn : ∀ p ∈ names, p.length ≤ Ln)
    {I : List DStep → (List Bool → Tree) → Prop} {c : DStep → ℕ} {ct c9 : ℕ}
    (hI : ∀ st sts' σ, I (st :: sts') σ → st.cost (KT.val nub) nub.length σ ≤ c st ∧
      ∀ σ' ∈ st.exec (KT.val nub) σ, I sts' σ')
    (hI0 : I sts (gets (partsT (KT.val nl) names .nil (wordT t0 t1 z))))
    (h9 : ∀ σ ∈ execAll (KT.val nub) sts (gets (partsT (KT.val nl) names .nil (wordT t0 t1 z))),
      (∃ I' : List DStep → (List Bool → Tree) → Prop, ∃ c' : DStep → ℕ,
        (∀ st sts'' σ, I' (st :: sts'') σ → st.cost (KT.val nub) nub.length σ ≤ c' st ∧
          ∀ σ' ∈ st.exec (KT.val nub) σ, I' sts'' σ') ∧ I' sts' σ ∧ (sts'.map fun st => c' st + 30).sum ≤ c9) ∧
      ∀ σ' ∈ execAll (KT.val nub) sts' σ, ∀ t ∈ ts, t.cost σ' ≤ ct) : ∃ Q : List (A × Tree),
    Does θ (dealF t0 t1 names nl nub sts sts' ts) z Q (60 * z.size + (z.size + names.length) * (60 * nl.length + 100) +
      names.length * (60 * Ln + 130) + (sts.map fun st => c st + 30).sum + c9 + ts.length * (ct + 60) + 300) ∧
    (∀ q ∈ Q, ∃ σ ∈ execAll (KT.val nub) (sts ++ sts') (gets (partsT (KT.val nl) names .nil (wordT t0 t1 z))),
      q.2 = listT (ts.map fun t => t.expand σ)) ∧
    wsum Q (pvs θ) = ((execAll (KT.val nub) (sts ++ sts') (gets (partsT (KT.val nl) names .nil (wordT t0 t1 z)))).map
      fun σ => (ts.map fun t => pv θ (t.expand σ)).prod).sum := by
  obtain ⟨σ0, hσ0⟩ : ∃ σ, σ = gets (partsT (KT.val nl) names .nil (wordT t0 t1 z)) := ⟨_, rfl⟩
  rw [← hσ0] at hI0 h9 ⊢
  have hw := partsF_gives (wordF_gives (t0 := t0) (t1 := t1) (Gives.id (θ := θ) z)) names nl Ln hn
  rw [length_wordT] at hw
  obtain ⟨Q1, d1, m1, s1⟩ := dstepsF_does (θ := θ) nub sts hw hI (by rw [← hσ0]; exact hI0)
  rw [← hσ0] at m1 s1
  -- the second part
  have h2 : ∀ W : Tree, ∃ Q : List (A × Tree), gets W ∈ execAll (KT.val nub) sts σ0 →
      Does θ (lett (dstepsF nub sts' .id) (tmsF ts .id)) W Q (c9 + ts.length * (ct + 60) + 150) ∧
      (∀ q ∈ Q, ∃ σ ∈ execAll (KT.val nub) sts' (gets W), q.2 = listT (ts.map fun t => t.expand σ)) ∧
      wsum Q (pvs θ) = ((execAll (KT.val nub) sts' (gets W)).map fun σ => (ts.map fun t => pv θ (t.expand σ)).prod).sum := by
    intro W
    by_cases hW : gets W ∈ execAll (KT.val nub) sts σ0
    swap
    · exact ⟨[], fun h => absurd h hW⟩
    obtain ⟨⟨I', c', hI', hI0', hc'⟩, ht⟩ := h9 _ hW
    obtain ⟨Q2, d2, m2, s2⟩ := dstepsF_does (θ := θ) nub sts' (Gives.id (θ := θ) W) hI' hI0'
    have d3 := Gives.after (G := tmsF ts .id) (f := fun W' => listT (ts.map fun t => t.expand (gets W'))) d2
      (d := 1 + ts.length * (ct + 60) + 30) fun q hq => tmsF_gives (Gives.id (θ := θ) q.2) fun t htt => ht _ (m2 q hq) t htt
    refine ⟨_, fun _ => ⟨d3.mono (by omega), ?_, ?_⟩⟩
    · intro q hq
      rw [List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      exact ⟨_, m2 q' hq', rfl⟩
    · rw [← s2]
      simp only [wsum, List.map_map, Function.comp_def, pvs, toList_listT]
  choose R hR using h2
  have d4 := d1.lett (G := lett (dstepsF nub sts' .id) (tmsF ts .id)) (R := R) (d := c9 + ts.length * (ct + 60) + 150)
    fun q hq => (hR q.2 (m1 q hq)).1
  refine ⟨_, d4.mono ?_, ?_, ?_⟩
  · omega
  · intro p hp
    obtain ⟨q, hq, r, hr, e, -⟩ := mem_bindW hp
    obtain ⟨σ, hσ, h⟩ := (hR q.2 (m1 q hq)).2.1 r hr
    refine ⟨σ, ?_, by rw [e, h]⟩
    rw [execAll_append, List.mem_flatMap]
    exact ⟨_, m1 q hq, hσ⟩
  · rw [wsum_bindW, wsum_congr (φ' := fun W => ((execAll (KT.val nub) sts' (gets W)).map
      fun σ => (ts.map fun t => pv θ (t.expand σ)).prod).sum) fun q hq => (hR q.2 (m1 q hq)).2.2, execAll_append,
      sum_flatMap_map]
    exact s1 fun σ => ((execAll (KT.val nub) sts' σ).map fun σ' => (ts.map fun t => pv θ (t.expand σ')).prod).sum

end Program

section Parts

variable {ν : Type} [DecidableEq ν] {nm : ν → List Bool} (hnm : Function.Injective nm)

include hnm


theorem gets_partsT (m : ℕ) (xs : List ν) (hxs : xs.Nodup) (W : Tree) (l : List Tree) (st : ν → Tree)
    (hW : gets W = byPath nm st) : ∃ st' : ν → Tree, gets (partsT m (xs.map nm) W l) = byPath nm st' ∧
      (∀ k (h : k < xs.length), st' xs[k] = listT ((l.drop (k * m)).take m).reverse) ∧ ∀ y, y ∉ xs → st' y = st y := by
  induction xs generalizing W l st with
  | nil => exact ⟨st, hW, fun k h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  | cons x xs ih =>
    rw [List.nodup_cons] at hxs
    rw [List.map_cons, partsT]
    obtain ⟨st', h1, h2, h3⟩ := ih hxs.2 (tset (nm x) (listT (l.take m).reverse) W) (l.drop m)
      (Function.update st x (listT (l.take m).reverse)) (by rw [gets_tset, hW, update_byPath hnm])
    refine ⟨st', h1, fun k h => ?_, fun y hy => ?_⟩
    · cases k with
      | zero =>
        rw [List.getElem_cons_zero, h3 x hxs.1, Function.update_self]
        simp
      | succ k =>
        rw [List.getElem_cons_succ, h2 k (by simpa using h), List.drop_drop]
        congr 4
        ring
    · rw [List.mem_cons, not_or] at hy
      rw [h3 y hy.2, Function.update_of_ne hy.1]

end Parts

end Nc.Dl
end
/- Source module Nc.Dl.Facts. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open Finset Nc.Cut Nc.G

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K U0 E U1 : ℕ} {mu : Letter S Unit Γ → Matrix Q Q F} {T : ℕ} {ub : ℕ} {c : ℕ}
  {cb : Option Γ → Fin c → Bool}














end Nc.Dl
end
/- Source module Nc.Dl.Cut. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

theorem length_wordG {Γ : Type} (b0 b1 : Γ) (z : Tree) : (wordG b0 b1 z).length = z.size := by
  induction z with
  | nil => rfl
  | cons a b iha ihb => simp only [wordG, List.length_cons, List.length_append, iha, ihb, Tree.size]

theorem wordT_eq {Γ : Type} (b0 b1 : Γ) (f : Γ → Tree) (z : Tree) : wordT (f b0) (f b1) z = (wordG b0 b1 z).map f := by
  induction z with
  | nil => rfl
  | cons a b iha ihb => simp only [wordT, wordG, iha, ihb, List.map_cons, List.map_append]

variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] {θ : List Bool → A} {K A' E U0 U1 ub mm D pS c T ℓ : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) (tab : SlpTab P grp D pS)
  (qn : Q → ℕ) (tg : M.R → ℕ) (bT bub nl nub : List Bool) (gt : Fin mm → Tree) (d1 gp : Tree) (cb : Option Γ → Fin c → Bool)
  (b0 b1 : Γ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D)


def lT (cb : Option Γ → Fin c → Bool) (a : Γ) : Tree := ofBits (List.ofFn (cb (some a)))


noncomputable def instTm (g : Fin mm) : Tm := .cons (.c gp) (scriptTm C tab tg bT bub gt d1 g)


noncomputable def steps18 : List DStep :=
  steps1 C qn i e ++ (steps2 C ++ (steps3 C hU0 ++ (steps4 C hU1 ++ ((steps5 C ++ (steps6 C tab ++ steps7 C tab)) ++
    steps8 C))))

theorem allSteps_eq : allSteps C tab qn hU0 hU1 i e = steps18 C tab qn i e hU0 hU1 ++ steps9 C := by
  simp only [allSteps, steps18, List.append_assoc]


noncomputable def dealProg : Fm :=
  dealF (lT cb b0) (lT cb b1) ((List.finRange K).map fun κ => C.nm (.part κ)) nl nub (steps18 C tab qn i e hU0 hU1)
    (steps9 C) ((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp))


def ptT (cb : Option Γ → Fin c → Bool) (x : Fin K → List Γ) (κ : Fin K) : Tree :=
  listT (((x κ).map fun a => ofBits (List.ofFn (cb (some a)))).reverse)

theorem gets_parts (hnl : KT.val nl = ℓ) (z : Tree) :
    gets (partsT (KT.val nl) ((List.finRange K).map fun κ => C.nm (.part κ)) .nil (wordT (lT cb b0) (lT cb b1) z)) =
      byPath C.nm (S0 (ptT cb (parts ℓ (wordG b0 b1 z)))) := by
  have h0 : gets .nil = byPath C.nm fun _ => .nil := by
    rw [gets_nil]
    funext p
    unfold byPath
    split_ifs <;> rfl
  obtain ⟨st', h1, h2, h3⟩ := gets_partsT C.nm_inj (KT.val nl) ((List.finRange K).map Nm.part)
    ((List.nodup_finRange K).map fun a b h => by simpa using h) .nil (wordT (lT cb b0) (lT cb b1) z) _ h0
  rw [List.map_map] at h1
  have e1 : (C.nm ∘ Nm.part) = fun κ : Fin K => C.nm (.part κ) := rfl
  rw [e1] at h1
  rw [h1]
  congr 1
  funext y
  by_cases hy : y ∈ (List.finRange K).map (Nm.part : Fin K → NmT S M U0 U1 pS)
  · rw [List.mem_map] at hy
    obtain ⟨κ, -, rfl⟩ := hy
    have hk : κ.1 < ((List.finRange K).map (Nm.part : Fin K → NmT S M U0 U1 pS)).length := by simp
    have := h2 κ.1 hk
    rw [List.getElem_map, List.getElem_finRange] at this
    have h4 : st' (.part κ) = listT ((((wordT (lT cb b0) (lT cb b1) z)).drop (κ.1 * KT.val nl)).take (KT.val nl)).reverse :=
      this
    rw [h4, wordT_eq b0 b1 (lT cb), hnl, ← List.map_drop, ← List.map_take]
    rfl
  · rw [h3 y hy]
    cases y with
    | part κ => exact absurd (List.mem_map.2 ⟨κ, List.mem_finRange κ, rfl⟩) hy
    | _ => rfl


theorem mem_execAll (hK : 0 < K) [Nonempty Q] [Nonempty (Fin U1)] {pt : Fin K → Tree} {σ : List Bool → Tree}
    (hσ : σ ∈ execAll ub (allSteps C tab qn hU0 hU1 i e) (byPath C.nm (S0 pt))) :
    ∃ (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1)
      (b : G.Uid (K + K) U0 M.N U1 → UW ub) (st : NmT S M U0 U1 pS → Tree), (q 0 = i ∧ q (Fin.last K) = e) ∧ ValidRows ρ ∧
      tab.valid n ∧ (∀ x, P.good n o x) ∧
      (∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)) ∧
      Final C tab qn pt q ρ n o b st ∧ σ = byPath C.nm st := by
  classical
  obtain ⟨st, hf, hs⟩ := sum_allSteps (ub := ub) C tab pt qn i e hU0 hU1 hK
  by_contra hno
  have h := hs ℤ fun σ' => if σ' = σ then 1 else 0
  have hz : ∀ (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1)
      (b : G.Uid (K + K) U0 M.N U1 → UW ub), (q 0 = i ∧ q (Fin.last K) = e) → ValidRows ρ → tab.valid n →
      (∀ x, P.good n o x) → (∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)) →
      byPath C.nm (st q ρ n o b) ≠ σ := fun q ρ n o b h1 h2 h3 h4 h5 h6 =>
    hno ⟨q, ρ, n, o, b, st q ρ n o b, h1, h2, h3, h4, h5, hf q ρ n o b, h6.symm⟩
  have hR : (∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
          ∑ n : NN K U0, if tab.valid n then ∑ o : M.N → Fin U1, if ∀ x, P.good n o x then
            ∑ b : G.Uid (K + K) U0 M.N U1 → UW ub,
              if ∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E) then
                (if byPath C.nm (st q ρ n o b) = σ then (1 : ℤ) else 0) else 0
            else 0 else 0 else 0 else 0) = 0 := by
    refine Finset.sum_eq_zero fun q _ => ?_
    split_ifs with h1
    swap
    · rfl
    refine Finset.sum_eq_zero fun ρ _ => ?_
    split_ifs with h2
    swap
    · rfl
    refine Finset.sum_eq_zero fun n _ => ?_
    split_ifs with h3
    swap
    · rfl
    refine Finset.sum_eq_zero fun o _ => ?_
    split_ifs with h4
    swap
    · rfl
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with h5 h6
    · exact absurd h6 (hz q ρ n o b h1 h2 h3 h4 h5)
    · rfl
    · rfl
  rw [hR] at h
  have hpos : (0 : ℤ) < ((execAll ub (allSteps C tab qn hU0 hU1 i e) (byPath C.nm (S0 pt))).map
      fun σ' => if σ' = σ then (1 : ℤ) else 0).sum := by
    refine lt_of_lt_of_le (b := (if σ = σ then (1 : ℤ) else 0)) (by simp) ?_
    refine List.single_le_sum (fun x hx => ?_) _ (List.mem_map.2 ⟨σ, hσ, rfl⟩)
    rw [List.mem_map] at hx
    obtain ⟨σ', -, rfl⟩ := hx
    split_ifs <;> norm_num
  omega

variable {mu : Letter S Unit Γ → Matrix Q Q A} {τ s τ' s' t : ℕ}

open Classical in

theorem deal_cut (hK : 0 < K) [Nonempty Q] [Nonempty (Fin U1)] (hnl : KT.val nl = ℓ) (hnub : KT.val nub = ub)
    (hd1 : ∀ d : Fin D, C.dt d = d1 ↔ d.1 = 1) (hgt : ∀ (d : Fin D) (g : Fin mm), C.dt d = gt g ↔ d.1 = g.1)
    -- the automaton
    (hU : ∀ z, z.size ≤ s → Plain θ τ z → runVal mu i e (K * T) (fun _ => wordG b0 b1 z) = pv θ z)
    -- the formula of the pieces
    (hval : ∀ z, z.size ≤ s → runVal mu i e (K * T) (fun _ => wordG b0 b1 z) =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
          ∑ n : NN K U0, if tab.valid n then
            ∑ o : M.N → Fin U1, if ∀ x, P.good n o x then
              ∑ b ∈ Common (none : UW ub) (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)),
                ∏ g, G.grpVal mu T cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g b
            else 0
          else 0
        else 0
      else 0)
    -- the program
    (hdoes : ∀ z, z.size ≤ s → ∃ Qs : List (A × Tree),
      Does θ (dealProg C tab qn tg bT bub nl nub gt d1 gp cb b0 b1 i e hU0 hU1) z Qs t ∧
      (∀ q ∈ Qs, ∃ σ ∈ execAll ub (allSteps C tab qn hU0 hU1 i e)
        (byPath C.nm (S0 (ptT cb (parts ℓ (wordG b0 b1 z))))),
        q.2 = listT (((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp)).map fun t => t.expand σ)) ∧
      wsum Qs (pvs θ) = ((execAll ub (allSteps C tab qn hU0 hU1 i e)
        (byPath C.nm (S0 (ptT cb (parts ℓ (wordG b0 b1 z)))))).map
        fun σ => (((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp)).map fun t => pv θ (t.expand σ)).prod).sum)
    -- the pieces
    (hpc : ∀ z, z.size ≤ s → ∀ (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0)
      (o : M.N → Fin U1) (b : G.Uid (K + K) U0 M.N U1 → UW ub) (g : Fin mm), ValidRows ρ → tab.valid n →
      (∀ x, P.good n o x) →
      (∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)) →
      (Tree.cons gp (Grp.scriptT bT bub (Grp.script qn cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g C.key C.dkey
        tg b))).size ≤ s' ∧
      Plain θ τ' (.cons gp (Grp.scriptT bT bub (Grp.script qn cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g C.key
        C.dkey tg b))) ∧
      pv θ (.cons gp (Grp.scriptT bT bub (Grp.script qn cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g C.key
        C.dkey tg b))) = G.grpVal mu T cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g b) :
    CutD θ τ s τ' s' mm t (dealProg C tab qn tg bT bub nl nub gt d1 gp cb b0 b1 i e hU0 hU1).code := by
  classical
  intro z hz
  obtain ⟨Qs, hD, hmem, hsum⟩ := hdoes z hz
  have hpt : ∀ κ : Fin K, ptT cb (parts ℓ (wordG b0 b1 z)) κ =
      listT (((parts ℓ (wordG b0 b1 z) κ).map fun a => ofBits (List.ofFn (cb (some a)))).reverse) := fun κ => rfl
  -- the instances at a final state
  have hinst : ∀ (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1)
      (b : G.Uid (K + K) U0 M.N U1 → UW ub) (st : NmT S M U0 U1 pS → Tree),
      (∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)) →
      Final C tab qn (ptT cb (parts ℓ (wordG b0 b1 z))) q ρ n o b st → ∀ g,
      (instTm C tab tg bT bub gt d1 gp g).expand (byPath C.nm st) = .cons gp (Grp.scriptT bT bub (Grp.script qn cb P q
        (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g C.key C.dkey tg b)) := by
    intro q ρ n o b st hb hst g
    rw [instTm, Tm.expand, Tm.expand, expand_scriptTm hst hd1 hgt hpt fun id hid hne =>
      (hb id).2 (Finset.mem_filter.2 ⟨hid, hne⟩)]
  have hpieces : ∀ q ∈ Qs, ∀ y ∈ q.2.toList, y.size ≤ s' ∧ Plain θ τ' y := by
    intro q hq y hy
    obtain ⟨σ, hσ, hq2⟩ := hmem q hq
    obtain ⟨q', ρ, n, o, b, st, h1, h2, h3, h4, h5, h6, rfl⟩ := mem_execAll C tab qn i e hU0 hU1 hK hσ
    rw [hq2, toList_listT, List.map_map, List.mem_map] at hy
    obtain ⟨g, -, rfl⟩ := hy
    simp only [Function.comp_apply]
    rw [hinst q' ρ n o b st h5 h6 g]
    have := hpc z hz q' ρ n o b g h2 h3 h4 h5
    exact ⟨this.1, this.2.1⟩
  refine ⟨Qs, by rw [Fm.ofTree_code]; exact hD, fun q hq => ⟨?_, fun y hy => (hpieces q hq y hy).1⟩, fun hpl =>
    ⟨fun q hq y hy => (hpieces q hq y hy).2, ?_⟩⟩
  · obtain ⟨σ, hσ, hq2⟩ := hmem q hq
    rw [hq2, toList_listT, List.length_map, List.length_map, List.length_finRange]
  · rw [hsum, ← hU z hz hpl, hval z hz]
    obtain ⟨st, hf, hs'⟩ := sum_allSteps (ub := ub) C tab (ptT cb (parts ℓ (wordG b0 b1 z))) qn i e hU0 hU1 hK
    rw [hs' A fun σ => _]
    refine Finset.sum_congr rfl fun q _ => if_congr Iff.rfl ?_ rfl
    refine Finset.sum_congr rfl fun ρ _ => ?_
    by_cases hρ : ValidRows ρ
    swap
    · rw [if_neg hρ, if_neg hρ]
    rw [if_pos hρ, if_pos hρ]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : tab.valid n
    swap
    · rw [if_neg hn, if_neg hn]
    rw [if_pos hn]
    rw [if_pos hn]
    refine Finset.sum_congr rfl fun o _ => ?_
    by_cases ho : ∀ x, P.good n o x
    swap
    · rw [if_neg ho, if_neg ho]
    rw [if_pos ho, if_pos ho]
    have hb : (∑ b ∈ Common (none : UW ub) (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)),
        ∏ g, G.grpVal mu T cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g b) =
        ∑ b : G.Uid (K + K) U0 M.N U1 → UW ub,
          if b ∈ Common (none : UW ub) (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)) then
          ∏ g, G.grpVal mu T cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g b else 0 := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [hb]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hbc : ∀ id, b id ≠ none ↔ id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)
    · rw [if_pos hbc, if_pos]
      · rw [List.map_map, Fin.prod_univ_def]
        congr 1
        refine List.map_congr_left fun g _ => ?_
        simp only [Function.comp_apply]
        rw [hinst q ρ n o b _ hbc (hf q ρ n o b) g]
        exact (hpc z hz q ρ n o b g hρ hn ho hbc).2.2.symm
      · rw [mem_common_iff]
        intro id hid
        by_contra hne
        exact hid ((hbc id).1 hne)
    · rw [if_neg hbc]
      split_ifs with hcm
      swap
      · rfl
      rw [mem_common_iff] at hcm
      push Not at hbc
      obtain ⟨id, hid⟩ := hbc
      rcases hid with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd (hcm id h2) h1
      · obtain ⟨hcur, hne⟩ := Finset.mem_filter.1 h2
        refine Finset.prod_eq_zero (Finset.mem_univ (grp n o (G.hold0 M.np id))) ?_
        by_contra hg
        exact grpVal_ne_none hg hcur (Or.inl ⟨rfl, Ne.symm hne⟩) h1

end Nc.Dl
end
/- Source module Nc.Dl.Bd1. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

section Reach

variable {m mb : ℕ}

end Reach

variable {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) {m mb : ℕ}

section Tries

theorem tget_mkTrie_mem (l : List (List Bool × Tree)) (p : List Bool) :
    tget p (mkTrie l) = .nil ∨ ∃ a ∈ l, a.1 = p ∧ tget p (mkTrie l) = a.2 := by
  induction l with
  | nil => left; exact tget_nil p
  | cons a l ih =>
    rw [mkTrie, List.foldr_cons, tget_tset]
    by_cases h : p = a.1
    · right
      exact ⟨a, List.mem_cons_self, h.symm, if_pos h⟩
    · rw [if_neg h]
      rw [mkTrie] at ih
      rcases ih with ih | ⟨b, hb, h1, h2⟩
      · exact Or.inl ih
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, h1, h2⟩

theorem tget_trieOf_cases {α : Type} [Fintype α] (code : α → List Bool) (f : α → Tree) (p : List Bool) :
    tget p (trieOf code f) = .nil ∨ ∃ a, tget p (trieOf code f) = f a := by
  rcases tget_mkTrie_mem ((Finset.univ : Finset α).toList.map fun a => (code a, f a)) p with h | ⟨a, ha, -, h⟩
  · exact Or.inl h
  · rw [List.mem_map] at ha
    obtain ⟨b, -, rfl⟩ := ha
    exact Or.inr ⟨b, h⟩

theorem tget_single (t : Tree) (p : List Bool) : tget p (.cons t .nil) = .nil ∨ tget p (.cons t .nil) = t := by
  cases p with
  | nil => exact Or.inr rfl
  | cons b p =>
    left
    cases b <;> exact tget_nil p

end Tries

section Readable


def Rdb : NmT S M U0 U1 pS → Prop
  | .zero => True
  | .rd _ _ => True
  | .dn _ _ => True
  | .dO _ => True
  | .slp _ => True
  | _ => False


def Short (Lc : ℕ) (σ : List Bool → Tree) : Prop := ∀ y : NmT S M U0 U1 pS, Rdb y → (σ (C.nm y)).len ≤ Lc


structure OkStep (Lc X : ℕ) (st : DStep) : Prop where
  keep : ∀ σ, Short C Lc σ → ∀ σ' ∈ st.exec m σ, Short C Lc σ'
  cost : ∀ σ, Short C Lc σ → st.cost m mb σ ≤ X

variable {C}

theorem Short.update {Lc : ℕ} {σ : List Bool → Tree} (h : Short C Lc σ) (y : NmT S M U0 U1 pS) {v : Tree}
    (hv : Rdb y → v.len ≤ Lc) : Short C Lc (Function.update σ (C.nm y) v) := by
  intro z hz
  by_cases hzy : z = y
  · subst hzy
    rw [Function.update_self]
    exact hv hz
  · rw [Function.update_of_ne fun h => hzy (C.nm_inj h)]
    exact h z hz

theorem Short.assign {Lc : ℕ} {σ : List Bool → Tree} (h : Short C Lc σ) {o : List (NmT S M U0 U1 pS × Tree)}
    (ho : ∀ a ∈ o, Rdb a.1 → a.2.len ≤ Lc) : Short C Lc (assignS σ (optT C.nm o)) := by
  unfold assignS optT
  rw [toList_listT]
  induction o generalizing σ with
  | nil => exact h
  | cons a o ih =>
    rw [List.map_cons, List.foldl_cons, hd_cons, tl_cons, path_ofBits]
    exact ih (h.update a.1 (ho a List.mem_cons_self)) fun b hb => ho b (List.mem_cons_of_mem _ hb)

variable {Lc : ℕ} (hnm : ∀ y, (C.nm y).length ≤ Lc)

include hnm


theorem okStep_pick {α : Type} (opts : List α) (o : α → List (NmT S M U0 U1 pS × Tree)) {X w : ℕ}
    (ho : ∀ a ∈ opts, ∀ b ∈ o a, Rdb b.1 → b.2.len ≤ Lc) (hX : opts.length ≤ X) (hw : ∀ a ∈ opts, (o a).length ≤ w) :
    OkStep (m := m) (mb := mb) C Lc (60 * Lc + 20 * X + X * (w * (60 * Lc + 80)) + 200) (pickS C opts o) := by
  have hlist : ∀ p : List Bool, (tget p (.cons (listT (opts.map fun a => optT C.nm (o a))) .nil)).toList = [] ∨
      (tget p (.cons (listT (opts.map fun a => optT C.nm (o a))) .nil)).toList = opts.map fun a => optT C.nm (o a) := by
    intro p
    rcases tget_single (listT (opts.map fun a => optT C.nm (o a))) p with h | h
    · left; rw [h]; rfl
    · right; rw [h, toList_listT]
  constructor
  · intro σ hσ σ' hσ'
    rw [pickS, DStep.exec, List.mem_map] at hσ'
    obtain ⟨t, ht, rfl⟩ := hσ'
    rcases hlist (σ (C.nm .zero)).path with h | h
    · rw [h] at ht
      simp at ht
    · rw [h, List.mem_map] at ht
      obtain ⟨a, ha, rfl⟩ := ht
      exact hσ.assign (ho a ha)
  · intro σ hσ
    have h1 := hnm .zero
    have h2 := hσ .zero trivial
    rw [pickS, DStep.cost]
    have hsum : ((opts.map fun a => optT C.nm (o a)).map fun t => (t.toList.map fun y => 60 * y.hd.len + 80).sum).sum ≤
        X * (w * (60 * Lc + 80)) := by
      rw [List.map_map]
      refine (List.sum_le_card_nsmul _ (w * (60 * Lc + 80)) ?_).trans ?_
      · intro n hn
        rw [List.mem_map] at hn
        obtain ⟨a, ha, rfl⟩ := hn
        simp only [Function.comp_apply, optT, toList_listT, List.map_map]
        refine (List.sum_le_card_nsmul _ (60 * Lc + 80) ?_).trans ?_
        · intro n hn
          rw [List.mem_map] at hn
          obtain ⟨b, hb, rfl⟩ := hn
          simp only [Function.comp_apply, hd_cons, len_ofBits]
          have := hnm b.1
          omega
        · rw [List.length_map, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (hw a ha)
      · rw [List.length_map, smul_eq_mul]
        exact Nat.mul_le_mul_right _ hX
    rcases hlist (σ (C.nm .zero)).path with h | h
    · rw [h]
      simp only [List.length_nil, List.map_nil, List.sum_nil]
      omega
    · rw [h]
      rw [List.length_map]
      have : 20 * opts.length ≤ 20 * X := Nat.mul_le_mul_left _ hX
      omega


theorem okStep_op {x y z : NmT S M U0 U1 pS} {φ : Tree} (hx : Rdb x) (hy : Rdb y)
    (hz : Rdb z → ∀ p q : List Bool, (tget q (tget p φ)).len ≤ Lc) :
    OkStep (m := m) (mb := mb) C Lc (180 * Lc + 200) (.op (C.nm x) (C.nm y) (C.nm z) φ) := by
  constructor
  · intro σ hσ σ' hσ'
    rw [DStep.exec, List.mem_singleton] at hσ'
    subst hσ'
    exact hσ.update z fun h => hz h _ _
  · intro σ hσ
    have h1 := hnm x
    have h2 := hnm y
    have h3 := hnm z
    have h4 := hσ x hx
    have h5 := hσ y hy
    rw [DStep.cost]
    omega


theorem okStep_check (x : NmT S M U0 U1 pS) :
    OkStep (m := m) (mb := mb) C Lc (30 * Lc + 100) (.check (C.nm x)) := by
  constructor
  · intro σ hσ σ' hσ'
    rw [DStep.exec] at hσ'
    split_ifs at hσ'
    · simp at hσ'
    · rw [List.mem_singleton] at hσ'
      subst hσ'
      exact hσ
  · intro σ _
    have := hnm x
    rw [DStep.cost]
    omega

end Readable

theorem OkStep.mono {C : Codes S M U0 U1 D pS} {Lc X X' : ℕ} {st : DStep} (h : OkStep (m := m) (mb := mb) C Lc X st)
    (hX : X ≤ X') : OkStep (m := m) (mb := mb) C Lc X' st := ⟨h.keep, fun σ hσ => (h.cost σ hσ).trans hX⟩


theorem okSteps_inv {C : Codes S M U0 U1 D pS} {Lc X : ℕ} {sts : List DStep}
    (h : ∀ st ∈ sts, OkStep (m := m) (mb := mb) C Lc X st) {σ0 : List Bool → Tree} (h0 : Short C Lc σ0) :
    ∃ I : List DStep → (List Bool → Tree) → Prop, (∀ st sts' σ, I (st :: sts') σ → st.cost m mb σ ≤ X ∧
      ∀ σ' ∈ st.exec m σ, I sts' σ') ∧ I sts σ0 := by
  refine ⟨fun rest σ => (∀ st ∈ rest, OkStep (m := m) (mb := mb) C Lc X st) ∧ Short C Lc σ, ?_, h, h0⟩
  rintro st sts' σ ⟨h1, h2⟩
  have hst := h1 st List.mem_cons_self
  exact ⟨hst.cost σ h2, fun σ' hσ' => ⟨fun s hs => h1 s (List.mem_cons_of_mem _ hs), hst.keep σ h2 σ' hσ'⟩⟩

section All

variable {C} (tab : SlpTab P grp D pS) (qn : Q → ℕ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D)


def stepB (Lc X : ℕ) : ℕ := 60 * Lc + 20 * X + X * (4 * (60 * Lc + 80)) + 180 * Lc + 200

theorem okSteps18 {Lc X : ℕ} (hnm : ∀ y, (C.nm y).length ≤ Lc) (hdc : ∀ d, (C.dc d).length ≤ Lc)
    (hrc : ∀ d, (C.rc d).length ≤ Lc) (hLc : 1 ≤ Lc) (hXQ : Fintype.card Q + 1 ≤ X)
    (hXr : Fintype.card (RowData (K + K)) ≤ X) (hXU : U0 + 1 ≤ X) (hXU1 : U1 ≤ X) :
    ∀ st ∈ steps18 C tab qn i e hU0 hU1, OkStep (m := m) (mb := mb) C Lc (stepB Lc X) st := by
  have hdt : ∀ d, (C.dt d).len ≤ Lc := fun d => by rw [dt, len_ofBits]; exact hdc d
  have hbit : ∀ b : Bool, (bit b).len ≤ Lc := fun b => by
    cases b
    · simp [bit, len]
    · simpa [bit, one, len] using hLc
  have hop : 180 * Lc + 200 ≤ stepB Lc X := by unfold stepB; omega
  have hck : 30 * Lc + 100 ≤ stepB Lc X := by unfold stepB; omega
  have hpk : ∀ w, w ≤ 4 → 60 * Lc + 20 * X + X * (w * (60 * Lc + 80)) + 200 ≤ stepB Lc X := by
    intro w hw
    have := Nat.mul_le_mul_left X (Nat.mul_le_mul_right (60 * Lc + 80) hw)
    unfold stepB
    omega
  have hun : ∀ (x dst : NmT S M U0 U1 pS) (f : Fin D → Tree), Rdb x → (Rdb dst → ∀ d, (f d).len ≤ Lc) →
      OkStep (m := m) (mb := mb) C Lc (stepB Lc X) (C.un x dst f) := by
    intro x dst f hx hf
    refine (okStep_op hnm (x := x) (y := .zero) (z := dst) hx trivial fun hd p q => ?_).mono hop
    rcases tget_trieOf_cases C.dc (fun d => Tree.cons (f d) .nil) p with h | ⟨d, h⟩
    · rw [h, tget_nil]; exact Nat.zero_le _
    · rw [h]
      rcases tget_single (f d) q with h' | h'
      · rw [h']; exact Nat.zero_le _
      · rw [h']; exact hf hd d
  have hcon : ∀ (dst : NmT S M U0 U1 pS) (t : Tree), (Rdb dst → t.len ≤ Lc) →
      OkStep (m := m) (mb := mb) C Lc (stepB Lc X) (C.con dst t) := by
    intro dst t ht
    refine (okStep_op hnm (x := .zero) (y := .zero) (z := dst) trivial trivial fun hd p q => ?_).mono hop
    rcases tget_single (.cons t .nil) p with h | h
    · rw [h, tget_nil]; exact Nat.zero_le _
    · rw [h]
      rcases tget_single t q with h' | h'
      · rw [h']; exact Nat.zero_le _
      · rw [h']; exact ht hd
  intro st hst
  simp only [steps18, List.mem_append] at hst
  rcases hst with h | h | h | h | (h | h | h) | h
  · -- states
    rw [steps1, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    refine (okStep_pick hnm _ _ (X := X) (w := 1) (fun q _ b hb hr => ?_) ?_ fun q _ => by simp).mono (hpk 1 (by norm_num))
    · rw [List.mem_singleton] at hb
      subst hb
      exact absurd hr (by simp [Rdb])
    · unfold opts1
      split_ifs
      · simp only [List.length_singleton]; omega
      · simp only [List.length_singleton]; omega
      · rw [Finset.length_toList, Finset.card_univ]; omega
  · rw [steps2, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    refine (okStep_pick hnm _ _ (X := X) (w := 2) (fun d _ b hb hr => ?_) ?_ fun d _ => by simp).mono (hpk 2 (by norm_num))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact absurd hr (by simp [Rdb])
      · simp only [len_ofBits]; exact hrc d
    · rw [Finset.length_toList, Finset.card_univ]; exact hXr
  · rw [steps3, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    refine (okStep_pick hnm _ _ (X := X) (w := 4) (fun d _ b hb hr => ?_) ?_ fun d _ => ?_).mono (hpk 4 le_rfl)
    · simp only [o3, List.mem_cons] at hb
      rcases hb with rfl | rfl | rfl | hb
      · exact absurd hr (by simp [Rdb])
      · exact absurd hr (by simp [Rdb])
      · exact hdt _
      · split_ifs at hb
        · rw [List.mem_singleton] at hb
          subst hb
          exact absurd hr (by simp [Rdb])
        · simp at hb
    · rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]; exact hXU
    · simp only [o3, List.length_cons]
      split_ifs <;> simp
  · rw [steps4, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    refine (okStep_pick hnm _ _ (X := X) (w := 3) (fun d _ b hb hr => ?_) ?_ fun d _ => by simp).mono (hpk 3 (by norm_num))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact hdt _
      · exact absurd hr (by simp [Rdb])
      · exact absurd hr (by simp [Rdb])
    · rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]; exact hXU1
  · rw [steps5, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    unfold rowStep
    split_ifs
    · exact (okStep_op hnm (x := .zero) (y := .rd _ _) trivial trivial fun hd => absurd hd (by simp [Rdb])).mono hop
    · exact (okStep_op hnm (x := .rd _ _) (y := .rd _ _) trivial trivial fun hd => absurd hd (by simp [Rdb])).mono hop
  · rw [steps6, List.mem_map] at h
    obtain ⟨k, -, rfl⟩ := h
    unfold slpStep
    split_ifs with h1 h2 h3
    · refine hun _ _ _ ?_ fun _ => hdt
      cases h1.choose <;> exact trivial
    · exact hcon _ _ fun _ => hdt _
    · refine (okStep_op hnm (x := .slp _) (y := .slp _) (z := .slp _) trivial trivial fun _ p q => ?_).mono hop
      rcases tget_trieOf_cases C.dc (fun d => trieOf C.dc fun d' => C.dt (h3.choose_spec.choose_spec.2.2.choose d d')) p with
        h | ⟨d, h⟩
      · rw [h, tget_nil]; exact Nat.zero_le _
      · rw [h]
        rcases tget_trieOf_cases C.dc (fun d' => C.dt (h3.choose_spec.choose_spec.2.2.choose d d')) q with h' | ⟨d', h'⟩
        · rw [h']; exact Nat.zero_le _
        · rw [h']; exact hdt _
    · exact hcon _ _ fun _ => Nat.zero_le _
  · rw [steps7, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    rcases a with y | c | id
    · exact hun _ _ _ trivial fun hd => absurd hd (by simp [Rdb])
    · exact hun _ _ _ trivial fun hd => absurd hd (by simp [Rdb])
    · exact hun _ _ _ trivial fun hd => absurd hd (by simp [Rdb])
  · rw [steps8, List.map_append, List.mem_append, List.map_map, List.map_map, List.mem_map, List.mem_map] at h
    rcases h with ⟨a, -, rfl⟩ | ⟨c, -, rfl⟩
    · exact (okStep_check hnm _).mono hck
    · exact (okStep_check hnm _).mono hck

end All

end Nc.Dl
end
/- Source module Nc.Dl.Bd2. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

variable {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) {m mb : ℕ}
  (tab : SlpTab P grp D pS) (pt : Fin K → Tree) (qn : Q → ℕ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D)

open Classical in

theorem sum_steps18 (hK : 0 < K) [Nonempty Q] [Nonempty (Fin U1)] : ∃ st : (Fin (K + 1) → Q) →
    (Option S → Fin (K + K) → RowData (K + K)) → NN K U0 → (M.N → Fin U1) → NmT S M U0 U1 pS → Tree,
    (∀ q ρ n o, Mid C tab pt qn q ρ n o (st q ρ n o)) ∧ ∀ (B : Type) [CommRing B] (Φ : (List Bool → Tree) → B),
    ((execAll m (steps18 C tab qn i e hU0 hU1) (byPath C.nm (S0 pt))).map Φ).sum =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), ∑ n : NN K U0, ∑ o : M.N → Fin U1,
          if ValidRows ρ ∧ tab.valid n ∧ ∀ x, P.good n o x then Φ (byPath C.nm (st q ρ n o)) else 0
        else 0 := by
  have hmid := fun q ρ n o => exists_mid (m := m) C tab pt qn hU0 hU1 q ρ n o
  choose s7 hs7 hm7 using hmid
  refine ⟨s7, hm7, fun B _ Φ => ?_⟩
  have hne : Nonempty (RowData (K + K)) := ⟨(false, ⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  rw [steps18, sum_execAll_append, phase1 C pt qn i e hK fun σ' => _]
  refine Finset.sum_congr rfl fun q _ => if_congr Iff.rfl ?_ rfl
  rw [sum_execAll_append, phase2 C (by rfl) fun σ' => _]
  have h4 : ∀ ρ, ((execAll m (steps3 C hU0 ++ (steps4 C hU1 ++ ((steps5 C ++ (steps6 C tab ++ steps7 C tab)) ++
      steps8 C))) (byPath C.nm fun x => if (own2 x).isSome then v2 C (fun a => ρ a.1 a.2) x else
        S1 pt qn q x)).map Φ).sum = ∑ n : NN K U0, ∑ o : M.N → Fin U1,
          if ValidRows ρ ∧ tab.valid n ∧ ∀ x, P.good n o x then Φ (byPath C.nm (s7 q ρ n o)) else 0 := by
    intro ρ
    rw [sum_execAll_append, phase3 C hU0 (by rfl) fun σ' => _]
    have h5 : ∀ n : NN K U0, ((execAll m (steps4 C hU1 ++ ((steps5 C ++ (steps6 C tab ++ steps7 C tab)) ++
        steps8 C)) (byPath C.nm fun x => if (own3 x).isSome then v3 C hU0 (fun a => n a.1 a.2) x else
          if (own2 x).isSome then v2 C (fun a => ρ a.1 a.2) x else S1 pt qn q x)).map Φ).sum =
        ∑ o : M.N → Fin U1, if ValidRows ρ ∧ tab.valid n ∧ ∀ x, P.good n o x then Φ (byPath C.nm (s7 q ρ n o)) else 0 := by
      intro n
      rw [sum_execAll_append, phase4 C hU1 (by rfl) fun σ' => _]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [sum_execAll_append]
      have e4 : (fun x : NmT S M U0 U1 pS => if (own4 x).isSome then v4 C hU1 o x else
          if (own3 x).isSome then v3 C hU0 (fun a => n a.1 a.2) x else
          if (own2 x).isSome then v2 C (fun a => ρ a.1 a.2) x else S1 pt qn q x) = S4 C pt qn hU0 hU1 q ρ n o := rfl
      rw [e4, hs7 q ρ n o, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hm := hm7 q ρ n o
      by_cases hcond : ValidRows ρ ∧ tab.valid n ∧ ∀ x, P.good n o x
      · rw [if_pos hcond, phase8_pos C (fun s p => (hm.row s p).2 (hcond.1 s p)) (fun c => by
          cases c with
          | none => exact hm.valid.2 hcond.2.1
          | some x => exact (hm.good x).2 (hcond.2.2 x)), List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      · rw [if_neg hcond, phase8_neg]
        · simp
        · by_contra hc
          push Not at hc
          refine hcond ⟨fun s p => (hm.row s p).1 (hc.1 s p), hm.valid.1 (hc.2 none), fun x => (hm.good x).1 (hc.2 (some x))⟩
    exact Finset.sum_congr rfl fun n _ => h5 n
  exact Finset.sum_congr rfl fun ρ _ => h4 ρ


theorem mem_steps18 (hK : 0 < K) [Nonempty Q] [Nonempty (Fin U1)] {σ : List Bool → Tree}
    (hσ : σ ∈ execAll m (steps18 C tab qn i e hU0 hU1) (byPath C.nm (S0 pt))) :
    ∃ (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1)
      (st : NmT S M U0 U1 pS → Tree), tab.valid n ∧ (∀ x, P.good n o x) ∧ Mid C tab pt qn q ρ n o st ∧
      σ = byPath C.nm st := by
  classical
  obtain ⟨st, hf, hs⟩ := sum_steps18 (m := m) C tab pt qn i e hU0 hU1 hK
  by_contra hno
  have h := hs ℤ fun σ' => if σ' = σ then 1 else 0
  have hR : (∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), ∑ n : NN K U0, ∑ o : M.N → Fin U1,
          if ValidRows ρ ∧ tab.valid n ∧ ∀ x, P.good n o x then
            (if byPath C.nm (st q ρ n o) = σ then (1 : ℤ) else 0) else 0
        else 0) = 0 := by
    refine Finset.sum_eq_zero fun q _ => ?_
    split_ifs
    swap
    · rfl
    refine Finset.sum_eq_zero fun ρ _ => Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun o _ => ?_
    split_ifs with h5 h6
    · exact absurd ⟨q, ρ, n, o, st q ρ n o, h5.2.1, h5.2.2, hf q ρ n o, h6.symm⟩ hno
    · rfl
    · rfl
  rw [hR] at h
  have hpos : (0 : ℤ) < ((execAll m (steps18 C tab qn i e hU0 hU1) (byPath C.nm (S0 pt))).map
      fun σ' => if σ' = σ then (1 : ℤ) else 0).sum := by
    refine lt_of_lt_of_le (b := (if σ = σ then (1 : ℤ) else 0)) (by simp) ?_
    refine List.single_le_sum (fun x hx => ?_) _ (List.mem_map.2 ⟨σ, hσ, rfl⟩)
    rw [List.mem_map] at hx
    obtain ⟨σ', -, rfl⟩ := hx
    split_ifs <;> norm_num
  omega

section Nine

variable {C} {Lc : ℕ} (hnm : ∀ y, (C.nm y).length ≤ Lc)

include hnm


theorem cost9 {q : Fin (K + 1) → Q} {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : NN K U0} {o : M.N → Fin U1}
    {st : NmT S M U0 U1 pS → Tree} (hst : Mid C tab pt qn q ρ n o st) :
    ∃ I' : List DStep → (List Bool → Tree) → Prop, ∃ c' : DStep → ℕ,
      (∀ s sts σ, I' (s :: sts) σ → s.cost m mb σ ≤ c' s ∧ ∀ σ' ∈ s.exec m σ, I' sts σ') ∧
      I' (steps9 C) (byPath C.nm st) ∧ ((steps9 C).map fun s => c' s + 30).sum ≤
        Fintype.card (G.Uid (K + K) U0 M.N U1) * (90 * Lc + 230) +
        (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)).card * ((m + 1) * (60 * mb + 100)) := by
  classical
  refine ⟨fun rest σ => (∀ s ∈ rest, ∃ id : G.Uid (K + K) U0 M.N U1, s = DStep.bits (C.nm (.cut id)) (C.nm (.cont id))) ∧
    ∀ id, σ (C.nm (.cut id)) = st (.cut id), fun s => s.cost m mb (byPath C.nm st), ?_, ⟨?_, fun id => ?_⟩, ?_⟩
  · rintro s sts σ ⟨h1, h2⟩
    obtain ⟨id, rfl⟩ := h1 s List.mem_cons_self
    refine ⟨?_, fun σ' hσ' => ⟨fun s hs => h1 s (List.mem_cons_of_mem _ hs), fun id' => ?_⟩⟩
    · simp only [DStep.cost, h2, byPath_nm C.nm_inj]
      exact le_rfl
    · simp only [DStep.exec] at hσ'
      split_ifs at hσ' with hc
      · rw [List.mem_singleton] at hσ'
        rw [hσ', h2]
      · rw [List.mem_map] at hσ'
        obtain ⟨u, -, rfl⟩ := hσ'
        rw [Function.update_of_ne fun h => by simpa using C.nm_inj h, h2]
  · intro s hs
    rw [steps9, List.mem_map] at hs
    obtain ⟨id, -, rfl⟩ := hs
    exact ⟨id, rfl⟩
  · rw [byPath_nm C.nm_inj]
  · rw [steps9, List.map_map]
    have h1 : (((univ : Finset (G.Uid (K + K) U0 M.N U1)).toList.map ((fun s : DStep => s.cost m mb (byPath C.nm st) + 30) ∘
        fun id => DStep.bits (C.nm (.cut id)) (C.nm (.cont id))))).sum =
        ∑ id : G.Uid (K + K) U0 M.N U1, ((DStep.bits (C.nm (.cut id)) (C.nm (.cont id))).cost m mb (byPath C.nm st) + 30) :=
      Finset.sum_map_toList _ _
    rw [h1]
    calc ∑ id : G.Uid (K + K) U0 M.N U1, ((DStep.bits (C.nm (.cut id)) (C.nm (.cont id))).cost m mb (byPath C.nm st) + 30)
        ≤ ∑ id : G.Uid (K + K) U0 M.N U1, ((90 * Lc + 230) + if id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o)
            (P.cur n o E) then (m + 1) * (60 * mb + 100) else 0) := by
          refine Finset.sum_le_sum fun id _ => ?_
          have a1 := hnm (.cut id)
          have a2 := hnm (.cont id)
          obtain ⟨cc, h1, h2⟩ := hst.cut id
          rw [DStep.cost, byPath_nm C.nm_inj, h1]
          by_cases hc : id ∈ cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)
          · rw [if_pos hc, if_neg (bit_ne_nil.2 (h2.2 hc))]
            omega
          · have : cc = false := by
              by_contra hcc
              exact hc (h2.1 (by simpa using hcc))
            rw [if_neg hc, this, if_pos (show bit false = .nil from rfl)]
            omega
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.card_univ, Finset.sum_ite_mem,
            Finset.univ_inter, Finset.sum_const, smul_eq_mul]

end Nine

end Nc.Dl
end
/- Source module Nc.Dl.Bd3. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

theorem cost_listTm (σ : List Bool → Tree) (ts : List Tm) :
    (listTm ts).cost σ = (ts.map fun t => t.cost σ + 100).sum + 20 := by
  induction ts with
  | nil => simp [listTm, Tm.cost]
  | cons t ts ih =>
    simp only [listTm, Tm.cost, ih, List.map_cons, List.sum_cons]
    omega

theorem cost_catTm (σ : List Bool → Tree) (ts : List Tm) :
    (catTm ts).cost σ = (ts.map fun t => t.cost σ + 62 * (t.expand σ).toList.length + 250).sum + 20 := by
  induction ts with
  | nil => simp [catTm, Tm.cost]
  | cons t ts ih =>
    simp only [catTm, Tm.cost, ih, List.map_cons, List.sum_cons]
    omega

theorem sum_map_le {α : Type*} (l : List α) (f : α → ℕ) {n b : ℕ} (h : ∀ a ∈ l, f a ≤ b) (hn : l.length ≤ n) :
    (l.map f).sum ≤ n * b := by
  refine (List.sum_le_card_nsmul _ b ?_).trans ?_
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact h a ha
  · rw [List.length_map, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hn

variable {A : Type} [CommRing A] {S Q : Type} [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K A' E U0 U1 ub mm D pS : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} {C : Codes S M U0 U1 D pS}
  {tab : SlpTab P grp D pS} {qn : Q → ℕ} {pt : Fin K → Tree} {q : Fin (K + 1) → Q}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : NN K U0} {o : M.N → Fin U1}
  {b : G.Uid (K + K) U0 M.N U1 → UW ub} {st : NmT S M U0 U1 pS → Tree} {tg : M.R → ℕ} {bT bub : List Bool}
  {gt : Fin mm → Tree} {d1 gp : Tree} {Lc X : ℕ}

section

variable (hst : Final C tab qn pt q ρ n o b st) (hnm : ∀ y, (C.nm y).length ≤ Lc) (hdc : ∀ d, (C.dc d).length ≤ Lc)

include hst hnm hdc

theorem cost_gN (y : NmT S M U0 U1 pS) (σ : List Bool → Tree) : (gN C y).cost σ ≤ 30 * Lc + 50 := by
  have := hnm y
  simp only [gN, Tm.cost]
  omega

theorem size_slp (k : Fin pS) : (byPath C.nm st (C.nm (.slp k))).size ≤ 4 * Lc + 1 := by
  rw [byPath_nm C.nm_inj, hst.slp, dt]
  have h1 := size_ofBits (C.dc (tab.fn k (n, o)))
  have h2 := hdc (tab.fn k (n, o))
  omega


theorem cost_ifeq (k : Fin pS) (t : Tree) (a c : Tm) : (Tm.ifeq (C.nm (.slp k)) t a c).cost (byPath C.nm st) ≤
    a.cost (byPath C.nm st) + c.cost (byPath C.nm st) + 270 * Lc + 260 := by
  have h1 := hnm (.slp k)
  have h2 := size_slp hst hnm hdc k
  simp only [Tm.cost]
  have h3 : (if byPath C.nm st (C.nm (.slp k)) = .nil then 0 else 0) = 0 := by split_ifs <;> rfl
  rw [h3]
  omega

theorem cost_ifTm (k : Fin pS) (t : Tree) (a : Tm) : (ifTm (C.nm (.slp k)) t a).cost (byPath C.nm st) ≤
    a.cost (byPath C.nm st) + 270 * Lc + 280 := by
  have := cost_ifeq hst hnm hdc k t a (.c .nil)
  have e : (Tm.c .nil).cost (byPath C.nm st) = 20 := rfl
  rw [ifTm]
  omega

variable (hS : Fintype.card (Option S) ≤ X) (hK2 : K + K ≤ X) (hId : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X)
  (hU0X : U0 + 1 ≤ X) (hSl : ∀ r : M.R, Fintype.card ((M.kind r.1).SlAt r.2) ≤ X)
  (hCn : ∀ r : M.R, Fintype.card ((M.kind r.1).CnAt r.2) ≤ X) (hR : Fintype.card M.R ≤ X)

include hS hK2

theorem cost_bodyTm (p : Fin (K + K)) :
    (bodyTm C p).cost (byPath C.nm st) ≤ 3 * (X * (30 * Lc + 150)) + 300 := by
  have h1 : ((listTm ((univ : Finset (Option S)).toList.map fun s => gN C (.flag s p)))).cost (byPath C.nm st) ≤
      X * (30 * Lc + 150) + 20 := by
    rw [cost_listTm, List.map_map]
    refine Nat.add_le_add_right (sum_map_le _ _ (fun s _ => ?_) ?_) _
    · have := cost_gN hst hnm hdc (.flag s p) (byPath C.nm st)
      simp only [Function.comp_apply]
      omega
    · rw [Finset.length_toList, Finset.card_univ]; exact hS
  have h2 : ∀ f : Fin (K + K) → NmT S M U0 U1 pS, (listTm (List.ofFn fun b => gN C (f b))).cost (byPath C.nm st) ≤
      X * (30 * Lc + 150) + 20 := by
    intro f
    rw [cost_listTm]
    refine Nat.add_le_add_right (sum_map_le _ _ (fun t ht => ?_) ?_) _
    · rw [List.mem_ofFn] at ht
      obtain ⟨b', rfl⟩ := ht
      have := cost_gN hst hnm hdc (f b') (byPath C.nm st)
      omega
    · rw [List.length_ofFn]; exact hK2
  have h3 := h2 fun b => .kR p b
  have h4 := h2 fun b => .kC b p
  simp only [bodyTm, Tm.cost]
  omega

theorem cost_basesTm (p : Fin (K + K)) :
    (basesTm C p).cost (byPath C.nm st) ≤ 3 * (X * (30 * Lc + 150)) + 90 * Lc + 1000 := by
  have h1 := cost_bodyTm hst hnm hdc hS hK2 p
  have h2 : (baseTm C p).cost (byPath C.nm st) ≤ 3 * (X * (30 * Lc + 150)) + 60 * Lc + 800 := by
    revert h1
    refine Fin.addCases (fun κ h1 => ?_) (fun κ h1 => ?_) p
    · rw [baseTm, Fin.addCases_left]
      have a1 := cost_gN hst hnm hdc (.q κ.castSucc) (byPath C.nm st)
      have a2 := cost_gN hst hnm hdc (.q κ.succ) (byPath C.nm st)
      simp only [Tm.cost]
      omega
    · rw [baseTm, Fin.addCases_right]
      have a1 := cost_gN hst hnm hdc (.part κ) (byPath C.nm st)
      simp only [Tm.cost]
      omega
  have h3 := cost_gN hst hnm hdc (.dg p) (byPath C.nm st)
  simp only [basesTm, Tm.cost]
  omega

include hId

theorem cost_slotTm (z : M.Z) (a : Fin (K + K + A')) :
    (slotTm C tab d1 z a).cost (byPath C.nm st) ≤ X * (270 * Lc + 700) + 20 := by
  rw [slotTm, cost_catTm, List.map_map]
  refine Nat.add_le_add_right (sum_map_le _ _ (fun id _ => ?_) ?_) _
  · have h1 := cost_ifTm hst hnm hdc (tab.kcons z id) d1 (.c (listT [ofBits (C.key (a, id))]))
    have e : (Tm.c (listT [ofBits (C.key (a, id))])).cost (byPath C.nm st) = 20 := rfl
    have h2 : ((ifTm (C.nm (.slp (tab.kcons z id))) d1 (.c (listT [ofBits (C.key (a, id))]))).expand
        (byPath C.nm st)).toList.length ≤ 1 := by
      rw [expand_ifTm]
      split_ifs
      · simp [Tm.expand]
      · simp
    simp only [Function.comp_apply]
    omega
  · rw [List.length_reverse, G.allIds, Finset.length_toList, Finset.card_univ]
    exact hId

include hSl hCn

theorem cost_roleTm (r : M.R) : (roleTm C tab tg d1 r).cost (byPath C.nm st) ≤
    X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 30 * Lc + 500 := by
  have h1 : (listTm ((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map fun e => slotTm C tab d1 ⟨r.1, e.1⟩ (M.rp r))).cost
      (byPath C.nm st) ≤ X * (X * (270 * Lc + 700) + 120) + 20 := by
    rw [cost_listTm, List.map_map]
    refine Nat.add_le_add_right (sum_map_le _ _ (fun e _ => ?_) ?_) _
    · have := cost_slotTm (d1 := d1) hst hnm hdc hS hK2 hId ⟨r.1, e.1⟩ (M.rp r)
      simp only [Function.comp_apply]
      omega
    · rw [Finset.length_toList, Finset.card_univ]; exact hSl r
  have h2 : (listTm ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      gN C (.ch ⟨r.1, ν.1⟩ (decide ((M.kind r.1).c ν.1 ≠ r.2))))).cost (byPath C.nm st) ≤ X * (30 * Lc + 150) + 20 := by
    rw [cost_listTm, List.map_map]
    refine Nat.add_le_add_right (sum_map_le _ _ (fun ν _ => ?_) ?_) _
    · have := cost_gN hst hnm hdc (.ch ⟨r.1, ν.1⟩ (decide ((M.kind r.1).c ν.1 ≠ r.2))) (byPath C.nm st)
      simp only [Function.comp_apply]
      omega
    · rw [Finset.length_toList, Finset.card_univ]; exact hCn r
  have h3 := cost_gN hst hnm hdc (.num r.1) (byPath C.nm st)
  simp only [roleTm, Tm.cost]
  omega

omit hSl hCn in
theorem cost_endTm (g : Fin mm) (id : G.Uid (K + K) U0 M.N U1) :
    (endTm C tab gt d1 g id).cost (byPath C.nm st) ≤ 2000 * Lc + 4000 ∧
    ((endTm C tab gt d1 g id).expand (byPath C.nm st)).toList.length ≤ 1 := by
  have hone : ∀ k, (oneTm C k id).cost (byPath C.nm st) ≤ 30 * Lc + 500 := by
    intro k
    have := cost_gN hst hnm hdc (.cont id) (byPath C.nm st)
    rw [oneTm, cost_listTm]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Tm.cost]
    omega
  have lone : ∀ k, ((oneTm C k id).expand (byPath C.nm st)).toList.length = 1 := by
    intro k
    rw [oneTm, expand_listTm, toList_listT]
    rfl
  constructor
  · have e : ∀ t : Tree, (Tm.c t).cost (byPath C.nm st) = 20 := fun _ => rfl
    have h1 := hone (C.key (G.hold0 M.np id, id))
    have h2 := hone (C.key (G.hold1 M.np id, id))
    have h3 := cost_ifTm hst hnm hdc (tab.kgrp (G.hold1 M.np id)) (gt g) (oneTm C (C.key (G.hold1 M.np id, id)) id)
    have h4 := cost_ifeq hst hnm hdc (tab.kgrp (G.hold1 M.np id)) (gt g)
      (.c (listT [(Grp.Ins.both (C.key (G.hold0 M.np id, id)) (C.key (G.hold1 M.np id, id))).tree]))
      (oneTm C (C.key (G.hold0 M.np id, id)) id)
    have h5 := cost_ifeq hst hnm hdc (tab.kgrp (G.hold0 M.np id)) (gt g)
      (.ifeq (C.nm (.slp (tab.kgrp (G.hold1 M.np id)))) (gt g)
        (.c (listT [(Grp.Ins.both (C.key (G.hold0 M.np id, id)) (C.key (G.hold1 M.np id, id))).tree]))
        (oneTm C (C.key (G.hold0 M.np id, id)) id))
      (ifTm (C.nm (.slp (tab.kgrp (G.hold1 M.np id)))) (gt g) (oneTm C (C.key (G.hold1 M.np id, id)) id))
    have h6 := cost_ifTm hst hnm hdc (tab.kcur id) d1 (.ifeq (C.nm (.slp (tab.kgrp (G.hold0 M.np id)))) (gt g)
      (.ifeq (C.nm (.slp (tab.kgrp (G.hold1 M.np id)))) (gt g)
        (.c (listT [(Grp.Ins.both (C.key (G.hold0 M.np id, id)) (C.key (G.hold1 M.np id, id))).tree]))
        (oneTm C (C.key (G.hold0 M.np id, id)) id))
      (ifTm (C.nm (.slp (tab.kgrp (G.hold1 M.np id)))) (gt g) (oneTm C (C.key (G.hold1 M.np id, id)) id)))
    rw [e] at h4
    rw [endTm]
    omega
  · rw [endTm, expand_ifTm]
    split_ifs
    · simp only [Tm.expand]
      split_ifs
      · simp
      · exact (lone _).le
      · rw [expand_ifTm]
        split_ifs
        · exact (lone _).le
        · simp
    · simp

include hSl hCn hU0X hR


theorem cost_instTm (g : Fin mm) :
    (instTm C tab tg bT bub gt d1 gp g).cost (byPath C.nm st) ≤
      X * (3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000) +
      X * (X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500) +
      X * (2000 * Lc + 5000) + 1000 := by
  have hbase : ∀ p : Fin (K + K), (ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)).cost
      (byPath C.nm st) + 62 * ((ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)).expand
      (byPath C.nm st)).toList.length + 250 ≤ 3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000 := by
    intro p
    have h1 := cost_ifTm hst hnm hdc (tab.kgrp (Fin.castAdd A' p)) (gt g) (basesTm C p)
    have h2 := cost_basesTm hst hnm hdc hS hK2 p
    have h3 : ((ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)).expand
        (byPath C.nm st)).toList.length ≤ X := by
      rw [expand_ifTm]
      split_ifs
      · simp only [basesTm, Tm.expand, expand_gN, hst.dg, dgT, NS1.Tree.toList, toList_listT, List.length_cons, List.length_map]
        have := List.length_filter_le (fun k : Fin U0 => decide (k.1 < (n p p).1)) (List.finRange U0)
        rw [List.length_finRange] at this
        omega
      · simp
    omega
  have hrole : ∀ r : M.R, (ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g) (listTm [roleTm C tab tg d1 r])).cost
      (byPath C.nm st) + 62 * ((ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g) (listTm [roleTm C tab tg d1 r])).expand
      (byPath C.nm st)).toList.length + 250 ≤
      X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500 := by
    intro r
    have h1 := cost_ifTm hst hnm hdc (tab.kgrp (M.rp r)) (gt g) (listTm [roleTm C tab tg d1 r])
    have h2 := cost_roleTm (tg := tg) (d1 := d1) hst hnm hdc hS hK2 hId hSl hCn r
    have h3 : (listTm [roleTm C tab tg d1 r]).cost (byPath C.nm st) = (roleTm C tab tg d1 r).cost (byPath C.nm st) + 120 := by
      rw [cost_listTm]
      simp
    have h4 : ((ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g) (listTm [roleTm C tab tg d1 r])).expand
        (byPath C.nm st)).toList.length ≤ 1 := by
      rw [expand_ifTm]
      split_ifs
      · rw [expand_listTm, toList_listT]
        simp
      · simp
    omega
  have hroles : (Grp.allRoles M).length ≤ X := by
    refine le_trans (le_of_eq ?_) hR
    rw [Grp.allRoles, List.length_flatMap]
    rw [Fintype.card_sigma]
    simp only [List.length_map, Finset.length_toList, Finset.card_univ]
    rw [← List.ofFn_eq_map, List.sum_ofFn]
  have h0 : ∀ l1 l2 l3 : List Tm, (catTm (l1 ++ l2 ++ l3)).cost (byPath C.nm st) =
      ((l1.map fun t => t.cost (byPath C.nm st) + 62 * (t.expand (byPath C.nm st)).toList.length + 250).sum +
      (l2.map fun t => t.cost (byPath C.nm st) + 62 * (t.expand (byPath C.nm st)).toList.length + 250).sum +
      (l3.map fun t => t.cost (byPath C.nm st) + 62 * (t.expand (byPath C.nm st)).toList.length + 250).sum) + 20 := by
    intro l1 l2 l3
    rw [cost_catTm, List.map_append, List.map_append, List.sum_append, List.sum_append]
  have h1 : (((List.finRange (K + K)).map fun p =>
      ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)).map fun t => t.cost (byPath C.nm st) +
      62 * (t.expand (byPath C.nm st)).toList.length + 250).sum ≤
      X * (3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000) := by
    rw [List.map_map]
    exact sum_map_le _ _ (fun p _ => hbase p) (by rw [List.length_finRange]; exact hK2)
  have h2 : (((Grp.allRoles M).map fun r => ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g)
      (listTm [roleTm C tab tg d1 r])).map fun t => t.cost (byPath C.nm st) +
      62 * (t.expand (byPath C.nm st)).toList.length + 250).sum ≤
      X * (X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500) := by
    rw [List.map_map]
    exact sum_map_le _ _ (fun r _ => hrole r) hroles
  have h3 : (((G.allIds (K + K) U0 M.N U1).map (endTm C tab gt d1 g)).map fun t => t.cost (byPath C.nm st) +
      62 * (t.expand (byPath C.nm st)).toList.length + 250).sum ≤ X * (2000 * Lc + 5000) := by
    rw [List.map_map]
    refine sum_map_le _ _ (fun id _ => ?_) ?_
    · obtain ⟨a1, a2⟩ := cost_endTm (gt := gt) (d1 := d1) hst hnm hdc hS hK2 hId g id
      simp only [Function.comp_apply]
      omega
    · rw [G.allIds, Finset.length_toList, Finset.card_univ]; exact hId
  simp only [instTm, scriptTm, Tm.cost, h0]
  omega

end

end Nc.Dl
end
/- Source module Nc.Dl.Code. -/
section
namespace Nc.Dl

open NS1 Finset


def bitsN (L n : ℕ) : List Bool := List.ofFn fun i : Fin L => n.testBit i

theorem length_bitsN (L n : ℕ) : (bitsN L n).length = L := by simp [bitsN]

theorem bitsN_inj {L n n' : ℕ} (hn : n < 2 ^ L) (hn' : n' < 2 ^ L) (h : bitsN L n = bitsN L n') : n = n' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < L
  · exact congrFun (List.ofFn_injective h) ⟨i, hi⟩
  · rw [Nat.testBit_lt_two_pow (hn.trans_le (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi))),
      Nat.testBit_lt_two_pow (hn'.trans_le (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi)))]


theorem exists_code (α : Type) [Fintype α] {L : ℕ} (h : Fintype.card α ≤ 2 ^ L) :
    ∃ code : α → List Bool, Function.Injective code ∧ ∀ a, (code a).length = L := by
  refine ⟨fun a => bitsN L (Fintype.equivFin α a), fun a b hab => ?_, fun a => length_bitsN _ _⟩
  have h1 := ((Fintype.equivFin α a).2).trans_le h
  have h2 := ((Fintype.equivFin α b).2).trans_le h
  have := bitsN_inj h1 h2 hab
  exact (Fintype.equivFin α).injective (Fin.ext this)


theorem val_bitsN (L n : ℕ) (hn : n < 2 ^ L) : KT.val (bitsN L n) = n := by
  induction L generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    subst this
    rfl
  | succ L ih =>
    have e : bitsN (L + 1) n = (n.testBit 0) :: bitsN L (n / 2) := by
      rw [bitsN, List.ofFn_succ]
      congr 1
      unfold bitsN
      congr 1
      funext i
      simp [Nat.testBit_succ]
    rw [e, KT.val, ih (n / 2) (by rw [pow_succ] at hn; omega), Nat.testBit_zero]
    have := Nat.div_add_mod n 2
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · simp [h]; omega
    · simp [h]; omega


def nmEquiv {K E pS : ℕ} {S N Id : Type} : (Unit ⊕ Fin K ⊕ Fin (K + 1) ⊕ (Option S × Fin (K + K)) ⊕ (Option S × Fin (K + K)) ⊕
    (Option S × Fin (K + K)) ⊕ (Fin (K + K) × Fin (K + K)) ⊕ (Fin (K + K) × Fin (K + K)) ⊕ Fin (K + K) ⊕
    (Fin (K + K) × Fin (K + K)) ⊕ N ⊕ (N × Bool) ⊕ Fin pS ⊕ Fin E ⊕ Option (Fin E) ⊕ Id ⊕ Id) ≃ Nm K E pS S N Id :=
    { toFun := fun x => match x with
        | .inl _ => .zero
        | .inr (.inl κ) => .part κ
        | .inr (.inr (.inl a)) => .q a
        | .inr (.inr (.inr (.inl a))) => .flag a.1 a.2
        | .inr (.inr (.inr (.inr (.inl a)))) => .rd a.1 a.2
        | .inr (.inr (.inr (.inr (.inr (.inl a))))) => .row a.1 a.2
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))) => .kR a.1 a.2
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))) => .kC a.1 a.2
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))))) => .dg a
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))))) => .dn a.1 a.2
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))))))) => .dO a
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))))))) => .ch a.1 a.2
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))))))))) => .slp a
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))))))))) => .num a
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))))))))))) => .cond a
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))))))))))) => .cut a
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr a))))))))))))))) => .cont a
      invFun := fun x => match x with
        | .zero => .inl ()
        | .part κ => .inr (.inl κ)
        | .q a => .inr (.inr (.inl a))
        | .flag s p => .inr (.inr (.inr (.inl (s, p))))
        | .rd s p => .inr (.inr (.inr (.inr (.inl (s, p)))))
        | .row s p => .inr (.inr (.inr (.inr (.inr (.inl (s, p))))))
        | .kR a b => .inr (.inr (.inr (.inr (.inr (.inr (.inl (a, b)))))))
        | .kC a b => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (a, b))))))))
        | .dg a => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))))
        | .dn a b => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (a, b))))))))))
        | .dO a => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))))))
        | .ch a d => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (a, d))))))))))))
        | .slp a => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))))))))
        | .num a => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))))))))))
        | .cond a => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))))))))))
        | .cut a => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))))))))))))
        | .cont a => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr a)))))))))))))))
      left_inv := fun x => by
        rcases x with a | a | a | a | a | a | a | a | a | a | a | a | a | a | a | a | a <;> rfl
      right_inv := fun x => by cases x <;> rfl }


instance Nm.instFintype {K E pS : ℕ} {S N Id : Type} [Fintype S] [Fintype N] [Fintype Id] : Fintype (Nm K E pS S N Id) :=
  Fintype.ofEquiv _ nmEquiv

end Nc.Dl
end
/- Source module Nc.Dl.Does. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] {θ : List Bool → A} {K A' E U0 U1 ub mm D pS c T ℓ : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} {C : Codes S M U0 U1 D pS} {tab : SlpTab P grp D pS}
  {qn : Q → ℕ} {tg : M.R → ℕ} {bT bub nl nub : List Bool} {gt : Fin mm → Tree} {d1 gp : Tree} {cb : Option Γ → Fin c → Bool}
  {b0 b1 : Γ} {i e : Q} {hU0 : U0 < D} {hU1 : U1 ≤ D} {Lc X : ℕ}


def tmB' (Lc X : ℕ) : ℕ := X * (3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000) +
  X * (X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500) + X * (2000 * Lc + 5000) + 1000



def dealB (Lc X K mm ub bd nS s : ℕ) : ℕ := 60 * s + (s + K) * (60 * Lc + 100) + K * (60 * Lc + 130) +
  nS * (stepB Lc X + 30) + (X * (90 * Lc + 230) + bd * ((ub + 1) * (60 * Lc + 100))) + mm * (tmB' Lc X + 60) + 300

theorem deal_does (hK : 0 < K) [Nonempty Q] [Nonempty (Fin U1)] (hnl : KT.val nl = ℓ) (hnub : KT.val nub = ub)
    (hnll : nl.length ≤ Lc) (hnubl : nub.length ≤ Lc)
    (hnm : ∀ y, (C.nm y).length ≤ Lc) (hdc : ∀ d, (C.dc d).length ≤ Lc)
    (hrc : ∀ d, (C.rc d).length ≤ Lc) (hLc : 1 ≤ Lc) (hXQ : Fintype.card Q + 1 ≤ X)
    (hXr : Fintype.card (RowData (K + K)) ≤ X) (hU0X : U0 + 1 ≤ X) (hXU1 : U1 ≤ X)
    (hS : Fintype.card (Option S) ≤ X) (hK2 : K + K ≤ X) (hId : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X)
    (hSl : ∀ r : M.R, Fintype.card ((M.kind r.1).SlAt r.2) ≤ X)
    (hCn : ∀ r : M.R, Fintype.card ((M.kind r.1).CnAt r.2) ≤ X) (hR : Fintype.card M.R ≤ X)
    {bd nS : ℕ} (hnS : (steps18 C tab qn i e hU0 hU1).length ≤ nS)
    (hbd : ∀ n o, tab.valid n → (∀ x, P.good n o x) →
      (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)).card ≤ bd) {s : ℕ} (z : Tree) (hz : z.size ≤ s) :
    ∃ Qs : List (A × Tree),
      Does θ (dealProg C tab qn tg bT bub nl nub gt d1 gp cb b0 b1 i e hU0 hU1) z Qs (dealB Lc X K mm ub bd nS s) ∧
      (∀ q ∈ Qs, ∃ σ ∈ execAll ub (allSteps C tab qn hU0 hU1 i e)
        (byPath C.nm (S0 (ptT cb (parts ℓ (wordG b0 b1 z))))),
        q.2 = listT (((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp)).map fun t => t.expand σ)) ∧
      wsum Qs (pvs θ) = ((execAll ub (allSteps C tab qn hU0 hU1 i e)
        (byPath C.nm (S0 (ptT cb (parts ℓ (wordG b0 b1 z)))))).map
        fun σ => (((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp)).map fun t => pv θ (t.expand σ)).prod).sum := by
  classical
  have hparts := gets_parts C nl cb b0 b1 hnl z
  obtain ⟨pt, hpt⟩ : ∃ pt, pt = ptT cb (parts (K := K) ℓ (wordG b0 b1 z)) := ⟨_, rfl⟩
  rw [← hpt] at hparts
  have hshort : Short C Lc (byPath C.nm (S0 pt)) := by
    intro y hy
    rw [byPath_nm C.nm_inj]
    cases y <;> simp_all [S0, Rdb, len]
  obtain ⟨I, hI, hI0⟩ := okSteps_inv (m := KT.val nub) (mb := nub.length)
    (okSteps18 tab qn i e hU0 hU1 hnm hdc hrc hLc hXQ hXr hU0X hXU1) hshort
  have h9 : ∀ σ ∈ execAll (KT.val nub) (steps18 C tab qn i e hU0 hU1) (byPath C.nm (S0 pt)),
      (∃ I' : List DStep → (List Bool → Tree) → Prop, ∃ c' : DStep → ℕ,
        (∀ st sts'' σ, I' (st :: sts'') σ → st.cost (KT.val nub) nub.length σ ≤ c' st ∧
          ∀ σ' ∈ st.exec (KT.val nub) σ, I' sts'' σ') ∧ I' (steps9 C) σ ∧
          ((steps9 C).map fun st => c' st + 30).sum ≤ X * (90 * Lc + 230) + bd * ((ub + 1) * (60 * Lc + 100))) ∧
      ∀ σ' ∈ execAll (KT.val nub) (steps9 C) σ, ∀ t ∈ (List.finRange mm).map (instTm C tab tg bT bub gt d1 gp),
        t.cost σ' ≤ tmB' Lc X := by
    intro σ hσ
    constructor
    · obtain ⟨q, ρ, n, o, st, hn, ho, hmid, rfl⟩ := mem_steps18 C tab pt qn i e hU0 hU1 hK hσ
      obtain ⟨I', c', h1, h2, h3⟩ := cost9 tab pt qn hnm (m := KT.val nub) (mb := nub.length) hmid
      refine ⟨I', c', h1, h2, h3.trans ?_⟩
      rw [hnub]
      have a1 := Nat.mul_le_mul_right (90 * Lc + 230) hId
      have a2 : (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)).card * ((ub + 1) * (60 * nub.length + 100)) ≤
          bd * ((ub + 1) * (60 * Lc + 100)) := Nat.mul_le_mul (hbd n o hn ho) (Nat.mul_le_mul_left _ (by omega))
      omega
    · intro σ' hσ' t ht
      rw [List.mem_map] at ht
      obtain ⟨g, -, rfl⟩ := ht
      have hmem : σ' ∈ execAll ub (allSteps C tab qn hU0 hU1 i e) (byPath C.nm (S0 pt)) := by
        rw [allSteps_eq, execAll_append, List.mem_flatMap]
        rw [hnub] at hσ hσ'
        exact ⟨σ, hσ, hσ'⟩
      obtain ⟨q, ρ, n, o, b, st, h1, h2, h3, h4, h5, hfin, rfl⟩ := mem_execAll C tab qn i e hU0 hU1 hK hmem
      exact cost_instTm hfin hnm hdc hS hK2 hId hU0X hSl hCn hR g
  have := dealF_does (θ := θ) (lT cb b0) (lT cb b1) ((List.finRange K).map fun κ => C.nm (.part κ)) nl nub
    (steps18 C tab qn i e hU0 hU1) (steps9 C) ((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp)) z (Ln := Lc)
    (fun p hp => by
      rw [List.mem_map] at hp
      obtain ⟨κ, -, rfl⟩ := hp
      exact hnm _) (c := fun _ => stepB Lc X) (ct := tmB' Lc X) (c9 := X * (90 * Lc + 230) + bd * ((ub + 1) * (60 * Lc + 100)))
    hI (by rw [hparts]; exact hI0) (by rw [hparts]; exact h9)
  obtain ⟨Qs, d1', m1, s1⟩ := this
  rw [hparts, hnub, ← allSteps_eq] at m1 s1
  rw [← hpt]
  refine ⟨Qs, d1'.mono ?_, m1, s1⟩
  rw [List.length_map, List.length_finRange, List.length_map, List.length_finRange, List.map_const', List.sum_replicate,
    smul_eq_mul]
  have a1 : (steps18 C tab qn i e hU0 hU1).length * (stepB Lc X + 30) ≤ nS * (stepB Lc X + 30) := Nat.mul_le_mul_right _ hnS
  have a2 : (z.size + K) * (60 * nl.length + 100) ≤ (s + K) * (60 * Lc + 100) := Nat.mul_le_mul (by omega) (by omega)
  unfold dealB
  omega


theorem length_steps18_le (hXQ : Fintype.card Q + 1 ≤ X) (hS : Fintype.card (Option S) ≤ X) (hK2 : K + K + 1 ≤ X)
    (hN : Fintype.card M.N ≤ X) (hpS : pS ≤ X) (hE : E + 1 ≤ X) (hId : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X) :
    (steps18 C tab qn i e hU0 hU1).length ≤ 4 * (X * X) + 10 * X := by
  have hm : Fintype.card (Option S) * (K + K) ≤ X * X := Nat.mul_le_mul hS (by omega)
  have hkk : (K + K) * (K + K) ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
  simp only [steps18, steps1, steps2, steps3, steps4, steps5, steps6, steps7, steps8, List.length_append, List.length_map,
    Finset.length_toList, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_sum, List.length_finRange]
  rw [Fintype.card_option (α := Fin E), Fintype.card_fin]
  omega

end Nc.Dl
end
/- Source module Nc.Dl.Num0. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl



structure CutNums (v K τ s k T ℓ ub lh X Lc m c ιb bd ev mm : ℕ) : Prop where
  v_pos : 1 ≤ v
  m_ge : 10000 ≤ m
  m_le : m ≤ v
  k_pos : 2 ≤ k
  kK : k ≤ K
  vK : v ^ 300 ≤ K
  KT : K * T ≤ τ * m
  ℓeq : ℓ = s / K + 1
  ub_pos : 1 ≤ ub
  ub_le : ub ≤ T + 1
  lhub : lh * ub ≤ m * T
  Lc_le : Lc + 1 ≤ m
  c_le : 4 * c + 8 ≤ m
  K_X : K ≤ X
  X_ge : 1 ≤ X
  ιb_le : ιb * k ≤ m * K
  ιbX : ιb ≤ X
  bd_le : bd * ub * v ^ 300 ≤ τ * m ^ 2
  ev_le : ev * ub * k ≤ τ * m ^ 2
  mm_le : mm ≤ k * m
  mmX : mm ≤ X
  small : X ^ 6 * m ^ 20 * v ^ 300 ≤ τ

namespace CutNums

variable {v K τ s k T ℓ ub lh X Lc m c ιb bd ev mm : ℕ} (h : CutNums v K τ s k T ℓ ub lh X Lc m c ιb bd ev mm)

include h

theorem m_pos : 1 ≤ m := le_trans (by norm_num) h.m_ge

theorem Xpow {a b : ℕ} (hab : a ≤ b) : X ^ a ≤ X ^ b := Nat.pow_le_pow_right h.X_ge hab

theorem mpow {a b : ℕ} (hab : a ≤ b) : m ^ a ≤ m ^ b := Nat.pow_le_pow_right h.m_pos hab


theorem X6 : X ^ 6 * m ^ 20 ≤ τ / v ^ 300 := by
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos h.v_pos)]
  exact h.small

theorem X6' : X ^ 6 * m ^ 20 ≤ τ / v ^ 256 :=
  h.X6.trans (Nat.div_le_div_left (Nat.pow_le_pow_right h.v_pos (by norm_num)) (Nat.pow_pos h.v_pos))

theorem X6t : X ^ 6 * m ^ 20 ≤ τ := h.X6.trans (Nat.div_le_self _ _)

theorem Xm_le {a b : ℕ} (ha : a ≤ 6) (hb : b ≤ 20) : X ^ a * m ^ b ≤ X ^ 6 * m ^ 20 :=
  Nat.mul_le_mul (h.Xpow ha) (h.mpow hb)


theorem bdub : bd * ub ≤ τ / v ^ 256 := by
  have hm := h.m_pos
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos h.v_pos)]
  have h1 : bd * ub * v ^ 300 ≤ τ * m ^ 5 := h.bd_le.trans (Nat.mul_le_mul_left _ (h.mpow (by norm_num)))
  have h2 : bd * ub * v ^ 256 * m ^ 5 ≤ τ * m ^ 5 := by
    calc bd * ub * v ^ 256 * m ^ 5 ≤ bd * ub * v ^ 256 * v ^ 5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h.m_le 5)
      _ = bd * ub * v ^ 261 := by rw [Nat.mul_assoc, ← pow_add]
      _ ≤ bd * ub * v ^ 300 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right h.v_pos (by norm_num))
      _ ≤ τ * m ^ 5 := h1
  exact Nat.le_of_mul_le_mul_right h2 (Nat.pow_pos hm)


theorem time {κ : ℕ} (hκ : κ ≤ m) : κ * (2 * (Lc + 1) * (T + ub + 2) + ιb * T + 1000 * (ev + ιb * lh) * (ub + Lc + 1) +
    X ^ 4 * 1000 * (Lc + 1)) ≤ τ * m ^ 10 / k := by
  have hm := h.m_pos
  have hk := h.k_pos
  rw [Nat.le_div_iff_mul_le (by omega)]
  have hXk : ∀ a b, a ≤ 5 → b ≤ 20 → X ^ a * m ^ b * k ≤ τ := by
    intro a b ha hb
    calc X ^ a * m ^ b * k ≤ X ^ a * m ^ b * X := Nat.mul_le_mul_left _ (h.kK.trans h.K_X)
      _ = X ^ (a + 1) * m ^ b := by rw [pow_succ]; ring
      _ ≤ X ^ 6 * m ^ 20 := h.Xm_le (by omega) hb
      _ ≤ τ := h.X6t
  have hTk : T * k ≤ τ * m := by
    calc T * k ≤ T * K := Nat.mul_le_mul_left _ h.kK
      _ = K * T := Nat.mul_comm _ _
      _ ≤ τ * m := h.KT
  have A1 : 2 * (Lc + 1) * (T + ub + 2) * k ≤ τ * m ^ 3 := by
    have e1 : k ≤ τ := by
      have := hXk 0 0 (by norm_num) (by norm_num)
      simpa using this
    calc 2 * (Lc + 1) * (T + ub + 2) * k ≤ 2 * m * (T + (T + 1) + 2) * k :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ h.Lc_le) (by have := h.ub_le; omega))
      _ = 2 * m * (2 * (T * k) + 3 * k) := by ring
      _ ≤ 2 * m * (2 * (τ * m) + 3 * (τ * m)) := Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hTk)
          (Nat.mul_le_mul_left _ (e1.trans (Nat.le_mul_of_pos_right _ hm))))
      _ = τ * m ^ 2 * 10 := by ring
      _ ≤ τ * m ^ 2 * m := Nat.mul_le_mul_left _ (le_trans (by norm_num) h.m_ge)
      _ = τ * m ^ 3 := by ring
  have A2 : ιb * T * k ≤ τ * m ^ 3 := by
    calc ιb * T * k = ιb * k * T := by ring
      _ ≤ m * K * T := Nat.mul_le_mul_right _ h.ιb_le
      _ = m * (K * T) := by ring
      _ ≤ m * (τ * m) := Nat.mul_le_mul_left _ h.KT
      _ = τ * m ^ 2 := by ring
      _ ≤ τ * m ^ 3 := Nat.mul_le_mul_left _ (h.mpow (by norm_num))
  have hu : ub + m ≤ ub * (m * 2) := by
    have h1 : ub ≤ ub * m := Nat.le_mul_of_pos_right _ hm
    have h2 : m ≤ ub * m := Nat.le_mul_of_pos_left _ h.ub_pos
    have e : ub * (m * 2) = ub * m + ub * m := by ring
    omega
  have hev : ev * k * (ub + m) ≤ τ * m ^ 6 := by
    calc ev * k * (ub + m) ≤ ev * k * (ub * (m * 2)) := Nat.mul_le_mul_left _ hu
      _ = ev * ub * k * (m * 2) := by ring
      _ ≤ τ * m ^ 2 * (m * m) := Nat.mul_le_mul h.ev_le (Nat.mul_le_mul_left _ (le_trans (by norm_num) h.m_ge))
      _ = τ * m ^ 4 := by ring
      _ ≤ τ * m ^ 6 := Nat.mul_le_mul_left _ (h.mpow (by norm_num))
  have hιb : ιb * lh * k * (ub + m) ≤ τ * m ^ 6 := by
    calc ιb * lh * k * (ub + m) ≤ ιb * lh * k * (ub * (m * 2)) := Nat.mul_le_mul_left _ hu
      _ = ιb * k * (lh * ub) * (m * 2) := by ring
      _ ≤ m * K * (m * T) * (m * m) :=
          Nat.mul_le_mul (Nat.mul_le_mul h.ιb_le h.lhub) (Nat.mul_le_mul_left _ (le_trans (by norm_num) h.m_ge))
      _ = m ^ 4 * (K * T) := by ring
      _ ≤ m ^ 4 * (τ * m) := Nat.mul_le_mul_left _ h.KT
      _ = τ * m ^ 5 := by ring
      _ ≤ τ * m ^ 6 := Nat.mul_le_mul_left _ (h.mpow (by norm_num))
  have A3 : 1000 * (ev + ιb * lh) * (ub + Lc + 1) * k ≤ τ * m ^ 7 := by
    have hL := h.Lc_le
    calc 1000 * (ev + ιb * lh) * (ub + Lc + 1) * k ≤ 1000 * (ev + ιb * lh) * (ub + m) * k :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = 1000 * (ev * k * (ub + m) + ιb * lh * k * (ub + m)) := by ring
      _ ≤ 1000 * (τ * m ^ 6 + τ * m ^ 6) := Nat.mul_le_mul_left _ (Nat.add_le_add hev hιb)
      _ = τ * m ^ 6 * 2000 := by ring
      _ ≤ τ * m ^ 6 * m := Nat.mul_le_mul_left _ (le_trans (by norm_num) h.m_ge)
      _ = τ * m ^ 7 := by ring
  have A4 : X ^ 4 * 1000 * (Lc + 1) * k ≤ τ := by
    calc X ^ 4 * 1000 * (Lc + 1) * k ≤ X ^ 4 * m * m * k :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ (le_trans (by norm_num) h.m_ge)) h.Lc_le)
      _ = X ^ 4 * m ^ 2 * k := by ring
      _ ≤ τ := hXk 4 2 (by norm_num) (by norm_num)
  calc κ * (2 * (Lc + 1) * (T + ub + 2) + ιb * T + 1000 * (ev + ιb * lh) * (ub + Lc + 1) + X ^ 4 * 1000 * (Lc + 1)) * k
      = κ * (2 * (Lc + 1) * (T + ub + 2) * k + ιb * T * k + 1000 * (ev + ιb * lh) * (ub + Lc + 1) * k +
        X ^ 4 * 1000 * (Lc + 1) * k) := by ring
    _ ≤ m * (τ * m ^ 3 + τ * m ^ 3 + τ * m ^ 7 + τ) := Nat.mul_le_mul hκ
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add A1 A2) A3) A4)
    _ ≤ m * (τ * m ^ 7 + τ * m ^ 7 + τ * m ^ 7 + τ * m ^ 7) := by
        refine Nat.mul_le_mul_left _ ?_
        have e1 : τ * m ^ 3 ≤ τ * m ^ 7 := Nat.mul_le_mul_left _ (h.mpow (by norm_num))
        have e2 : τ ≤ τ * m ^ 7 := Nat.le_mul_of_pos_right _ (Nat.pow_pos hm)
        omega
    _ = τ * m ^ 8 * 4 := by ring
    _ ≤ τ * m ^ 8 * m := Nat.mul_le_mul_left _ (le_trans (by norm_num) h.m_ge)
    _ = τ * m ^ 9 := by ring
    _ ≤ τ * m ^ 10 := Nat.mul_le_mul_left _ (h.mpow (by norm_num))


theorem size : X + 1 + (200 * X ^ 3 * Lc + ιb * ℓ * (4 * c + 2) + bd * (4 * ub)) ≤ (s / k + τ / v ^ 256) * m ^ 10 := by
  have hm := h.m_pos
  have hk := h.k_pos
  have B1 : ιb * ℓ ≤ m * (s / k) + m + X := by
    have h1 : ιb * (s / K) ≤ m * (s / k) + m := by
      have h2 : ιb * (s / K) * k ≤ m * s := by
        calc ιb * (s / K) * k = ιb * k * (s / K) := by ring
          _ ≤ m * K * (s / K) := Nat.mul_le_mul_right _ h.ιb_le
          _ = m * (K * (s / K)) := by ring
          _ ≤ m * s := Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)
      have h3 : s ≤ (s / k + 1) * k := by
        have := Nat.div_add_mod s k
        have h4 := Nat.mod_lt s (show 0 < k by omega)
        rw [add_mul, one_mul, Nat.mul_comm (s / k)]
        omega
      have h4 : ιb * (s / K) * k ≤ (m * (s / k) + m) * k := by
        calc ιb * (s / K) * k ≤ m * s := h2
          _ ≤ m * ((s / k + 1) * k) := Nat.mul_le_mul_left _ h3
          _ = (m * (s / k) + m) * k := by ring
      exact Nat.le_of_mul_le_mul_right h4 (by omega)
    have h2 := h.ιbX
    rw [h.ℓeq, Nat.mul_add, Nat.mul_one]
    omega
  have hX : 1 ≤ X := h.X_ge
  have S1 : X + 1 + 200 * X ^ 3 * Lc + (m + X) * m ≤ τ / v ^ 256 := by
    refine le_trans ?_ h.X6'
    have hL := h.Lc_le
    have e1 : X ≤ X ^ 3 * m ^ 2 := by
      calc X = X ^ 1 * 1 := by rw [pow_one, mul_one]
        _ ≤ X ^ 3 * m ^ 2 := Nat.mul_le_mul (h.Xpow (by norm_num)) (Nat.pow_pos hm)
    have e2 : 1 ≤ X ^ 3 * m ^ 2 := Nat.mul_pos (Nat.pow_pos hX) (Nat.pow_pos hm)
    have e3 : 200 * X ^ 3 * Lc ≤ X ^ 3 * m ^ 2 := by
      calc 200 * X ^ 3 * Lc ≤ m * X ^ 3 * m :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ (le_trans (by norm_num) h.m_ge)) (by omega)
        _ = X ^ 3 * m ^ 2 := by ring
    have e4 : m * m ≤ X ^ 3 * m ^ 2 := by
      calc m * m = 1 * m ^ 2 := by ring
        _ ≤ X ^ 3 * m ^ 2 := Nat.mul_le_mul_right _ (Nat.pow_pos hX)
    have e5 : X * m ≤ X ^ 3 * m ^ 2 := by
      calc X * m = X ^ 1 * m ^ 1 := by rw [pow_one, pow_one]
        _ ≤ X ^ 3 * m ^ 2 := Nat.mul_le_mul (h.Xpow (by norm_num)) (h.mpow (by norm_num))
    calc X + 1 + 200 * X ^ 3 * Lc + (m + X) * m = X + 1 + 200 * X ^ 3 * Lc + (m * m + X * m) := by ring
      _ ≤ X ^ 3 * m ^ 2 * 5 := by omega
      _ ≤ X ^ 3 * m ^ 2 * m := Nat.mul_le_mul_left _ (le_trans (by norm_num) h.m_ge)
      _ = X ^ 3 * m ^ 3 := by ring
      _ ≤ X ^ 6 * m ^ 20 := h.Xm_le (by norm_num) (by norm_num)
  have S2 : bd * (4 * ub) ≤ 4 * (τ / v ^ 256) := by
    have := h.bdub
    calc bd * (4 * ub) = 4 * (bd * ub) := by ring
      _ ≤ 4 * (τ / v ^ 256) := Nat.mul_le_mul_left _ this
  have S3 : ιb * ℓ * (4 * c + 2) ≤ m ^ 2 * (s / k) + (m + X) * m := by
    calc ιb * ℓ * (4 * c + 2) ≤ (m * (s / k) + m + X) * m := Nat.mul_le_mul B1 (by have := h.c_le; omega)
      _ = m ^ 2 * (s / k) + (m + X) * m := by ring
  have hm10 : m ^ 2 ≤ m ^ 10 := h.mpow (by norm_num)
  have h5 : 5 ≤ m ^ 10 := le_trans (le_trans (by norm_num) h.m_ge) (Nat.le_self_pow (by norm_num) m)
  calc X + 1 + (200 * X ^ 3 * Lc + ιb * ℓ * (4 * c + 2) + bd * (4 * ub)) ≤ m ^ 2 * (s / k) + 5 * (τ / v ^ 256) := by omega
    _ ≤ m ^ 10 * (s / k) + m ^ 10 * (τ / v ^ 256) := Nat.add_le_add (Nat.mul_le_mul_right _ hm10) (Nat.mul_le_mul_right _ h5)
    _ = (s / k + τ / v ^ 256) * m ^ 10 := by ring


theorem deal : dealB Lc X K mm ub (mm * bd) (4 * (X * X) + 10 * X) s ≤ (s + τ * k / v ^ 256) * m ^ 10 := by
  have hm := h.m_pos
  have hk := h.k_pos
  have hX : 1 ≤ X := h.X_ge
  have hL := h.Lc_le
  have hm1 := h.m_ge
  -- the units of the boundaries
  have D1 : mm * bd * ((ub + 1) * (60 * Lc + 100)) ≤ τ * k / v ^ 256 * m ^ 3 := by
    have h1 : mm * (bd * ub) ≤ m * (τ * k / v ^ 256) := by
      calc mm * (bd * ub) ≤ k * m * (τ / v ^ 256) := Nat.mul_le_mul h.mm_le h.bdub
        _ = m * (k * (τ / v ^ 256)) := by ring
        _ ≤ m * (τ * k / v ^ 256) := Nat.mul_le_mul_left _ (by
            rw [Nat.mul_comm τ k]
            exact Nat.mul_div_le_mul_div_assoc _ _ _)
    calc mm * bd * ((ub + 1) * (60 * Lc + 100)) ≤ mm * bd * ((ub + ub) * (100 * m)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.add_le_add_left h.ub_pos _) (by omega))
      _ = mm * (bd * ub) * (200 * m) := by ring
      _ ≤ m * (τ * k / v ^ 256) * (m * m) := Nat.mul_le_mul h1 (Nat.mul_le_mul_right _ (le_trans (by norm_num) hm1))
      _ = τ * k / v ^ 256 * m ^ 3 := by ring
  -- small things
  have D2 : (K * (60 * Lc + 100) + K * (60 * Lc + 130) + (4 * (X * X) + 10 * X) * (stepB Lc X + 30) + X * (90 * Lc + 230) +
      mm * (tmB' Lc X + 60) + 300) ≤ τ * k / v ^ 256 := by
    have hsm : X ^ 4 * m ^ 4 ≤ τ * k / v ^ 256 := by
      refine (h.Xm_le (by norm_num) (by norm_num)).trans (h.X6'.trans ?_)
      exact Nat.div_le_div_right (Nat.le_mul_of_pos_right _ (by omega))
    refine le_trans ?_ hsm
    have hK := h.K_X
    have x1 : X ≤ X ^ 4 := Nat.le_self_pow (by norm_num) X
    have x2 : X ^ 2 ≤ X ^ 4 := h.Xpow (by norm_num)
    have x3 : X ^ 3 ≤ X ^ 4 := h.Xpow (by norm_num)
    have L1 : 60 * Lc + 100 ≤ 100 * m := by omega
    have f1 : K * (60 * Lc + 100) ≤ X ^ 4 * (100 * m) := Nat.mul_le_mul (hK.trans x1) L1
    have f2 : K * (60 * Lc + 130) ≤ X ^ 4 * (130 * m) := Nat.mul_le_mul (hK.trans x1) (by omega)
    have st : stepB Lc X + 30 ≤ X * (1000 * m) := by
      have e1 : 60 * Lc ≤ X * (60 * m) := by
        calc 60 * Lc ≤ 1 * (60 * m) := by omega
          _ ≤ X * (60 * m) := Nat.mul_le_mul_right _ hX
      have e2 : 20 * X ≤ X * (20 * m) := by nlinarith
      have e3 : X * (4 * (60 * Lc + 80)) ≤ X * (320 * m) := Nat.mul_le_mul_left _ (by omega)
      have e4 : 180 * Lc ≤ X * (180 * m) := by
        calc 180 * Lc ≤ 1 * (180 * m) := by omega
          _ ≤ X * (180 * m) := Nat.mul_le_mul_right _ hX
      have e5 : 230 ≤ X * (230 * m) := by
        calc 230 ≤ 1 * (230 * m) := by omega
          _ ≤ X * (230 * m) := Nat.mul_le_mul_right _ hX
      have e6 : X * (1000 * m) = X * (60 * m) + X * (20 * m) + X * (320 * m) + X * (180 * m) + X * (230 * m) + X * (190 * m) := by
        ring
      unfold stepB
      omega
    have f3 : (4 * (X * X) + 10 * X) * (stepB Lc X + 30) ≤ X ^ 4 * (14000 * m) := by
      have e1 : 4 * (X * X) + 10 * X ≤ 14 * X ^ 2 := by nlinarith
      calc (4 * (X * X) + 10 * X) * (stepB Lc X + 30) ≤ 14 * X ^ 2 * (X * (1000 * m)) := Nat.mul_le_mul e1 st
        _ = X ^ 3 * (14000 * m) := by ring
        _ ≤ X ^ 4 * (14000 * m) := Nat.mul_le_mul_right _ x3
    have f4 : X * (90 * Lc + 230) ≤ X ^ 4 * (230 * m) := Nat.mul_le_mul x1 (by omega)
    have tb : tmB' Lc X + 60 ≤ X ^ 3 * (20000 * m) := by
      have y1 : X ^ 2 ≤ X ^ 3 := h.Xpow (by norm_num)
      have y2 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
      have y3 : 1 ≤ X ^ 3 := Nat.pow_pos hX
      have g1 : X * (3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000) ≤ X ^ 3 * (3000 * m) := by
        calc X * (3 * (X * (30 * Lc + 150)) + 360 * Lc + 62 * X + 2000)
            ≤ X * (3 * (X * (150 * m)) + X * (360 * m) + X * (62 * m) + X * (2000 * m)) := by
              refine Nat.mul_le_mul_left _ ?_
              have e1 : 3 * (X * (30 * Lc + 150)) ≤ 3 * (X * (150 * m)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
              have e2 : 360 * Lc ≤ X * (360 * m) := by
                calc 360 * Lc ≤ 1 * (360 * m) := by omega
                  _ ≤ X * (360 * m) := Nat.mul_le_mul_right _ hX
              have e3 : 62 * X ≤ X * (62 * m) := by nlinarith
              have e4 : 2000 ≤ X * (2000 * m) := by
                calc 2000 ≤ 1 * (2000 * m) := by omega
                  _ ≤ X * (2000 * m) := Nat.mul_le_mul_right _ hX
              omega
          _ = X ^ 2 * (2872 * m) := by ring
          _ ≤ X ^ 3 * (3000 * m) := Nat.mul_le_mul y1 (by omega)
      have g2 : X * (X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500) ≤ X ^ 3 * (4000 * m) := by
        calc X * (X * (X * (270 * Lc + 700) + 120) + X * (30 * Lc + 150) + 300 * Lc + 1500)
            ≤ X * (X * (X * (700 * m) + X * (120 * m)) + X * (X * (150 * m)) + X * (X * (300 * m)) + X * (X * (1500 * m))) := by
              refine Nat.mul_le_mul_left _ ?_
              have e0 : 1 ≤ X * X := Nat.mul_pos hX hX
              have e1 : X * (X * (270 * Lc + 700) + 120) ≤ X * (X * (700 * m) + X * (120 * m)) := by
                refine Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) ?_)
                calc 120 ≤ 1 * (120 * m) := by omega
                  _ ≤ X * (120 * m) := Nat.mul_le_mul_right _ hX
              have e2 : X * (30 * Lc + 150) ≤ X * (X * (150 * m)) := Nat.mul_le_mul_left _ (by
                calc 30 * Lc + 150 ≤ 1 * (150 * m) := by omega
                  _ ≤ X * (150 * m) := Nat.mul_le_mul_right _ hX)
              have e3 : 300 * Lc ≤ X * (X * (300 * m)) := by
                calc 300 * Lc ≤ 1 * (300 * m) := by omega
                  _ ≤ X * X * (300 * m) := Nat.mul_le_mul_right _ e0
                  _ = X * (X * (300 * m)) := by ring
              have e4 : 1500 ≤ X * (X * (1500 * m)) := by
                calc 1500 ≤ 1 * (1500 * m) := by omega
                  _ ≤ X * X * (1500 * m) := Nat.mul_le_mul_right _ e0
                  _ = X * (X * (1500 * m)) := by ring
              linarith
          _ = X ^ 3 * (2770 * m) := by ring
          _ ≤ X ^ 3 * (4000 * m) := Nat.mul_le_mul_left _ (by omega)
      have g3 : X * (2000 * Lc + 5000) ≤ X ^ 3 * (5000 * m) := Nat.mul_le_mul y2 (by omega)
      have g4 : 1060 ≤ X ^ 3 * (1060 * m) := by
        calc 1060 ≤ 1 * (1060 * m) := by omega
          _ ≤ X ^ 3 * (1060 * m) := Nat.mul_le_mul_right _ y3
      have g5 : X ^ 3 * (20000 * m) = X ^ 3 * (3000 * m) + X ^ 3 * (4000 * m) + X ^ 3 * (5000 * m) + X ^ 3 * (1060 * m) +
          X ^ 3 * (6940 * m) := by ring
      unfold tmB'
      linarith
    have f5 : mm * (tmB' Lc X + 60) ≤ X ^ 4 * (20000 * m) := by
      calc mm * (tmB' Lc X + 60) ≤ X * (X ^ 3 * (20000 * m)) := Nat.mul_le_mul h.mmX tb
        _ = X ^ 4 * (20000 * m) := by ring
    have f6 : 300 ≤ X ^ 4 * (300 * m) := by
      calc 300 ≤ 1 * (300 * m) := by omega
        _ ≤ X ^ 4 * (300 * m) := Nat.mul_le_mul_right _ (Nat.pow_pos hX)
    have f7 : X ^ 4 * (100 * m) + X ^ 4 * (130 * m) + X ^ 4 * (14000 * m) + X ^ 4 * (230 * m) + X ^ 4 * (20000 * m) +
        X ^ 4 * (300 * m) = X ^ 4 * (34760 * m) := by ring
    have f8 : X ^ 4 * (34760 * m) ≤ X ^ 4 * m ^ 4 := by
      refine Nat.mul_le_mul_left _ ?_
      calc 34760 * m ≤ m * m * m * m := by nlinarith [Nat.mul_le_mul hm1 hm1, Nat.mul_pos hm hm]
        _ = m ^ 4 := by ring
    omega
  have D3 : 60 * s + s * (60 * Lc + 100) ≤ s * (200 * m) := by
    calc 60 * s + s * (60 * Lc + 100) = s * (60 * Lc + 160) := by ring
      _ ≤ s * (200 * m) := Nat.mul_le_mul_left _ (by omega)
  have e10 : s * (200 * m) ≤ s * m ^ 10 := Nat.mul_le_mul_left _ (by
    calc 200 * m ≤ m * m := Nat.mul_le_mul_right _ (le_trans (by norm_num) hm1)
      _ = m ^ 2 := by ring
      _ ≤ m ^ 10 := h.mpow (by norm_num))
  have e11 : τ * k / v ^ 256 * m ^ 3 + τ * k / v ^ 256 ≤ τ * k / v ^ 256 * m ^ 10 := by
    calc τ * k / v ^ 256 * m ^ 3 + τ * k / v ^ 256 ≤ τ * k / v ^ 256 * m ^ 3 + τ * k / v ^ 256 * m ^ 3 :=
          Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (Nat.pow_pos hm)) _
      _ = τ * k / v ^ 256 * m ^ 3 * 2 := by ring
      _ ≤ τ * k / v ^ 256 * m ^ 3 * m := Nat.mul_le_mul_left _ (le_trans (by norm_num) hm1)
      _ = τ * k / v ^ 256 * m ^ 4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (h.mpow (by norm_num))
  have e12 : (s + K) * (60 * Lc + 100) = s * (60 * Lc + 100) + K * (60 * Lc + 100) := by ring
  have e13 : (s + τ * k / v ^ 256) * m ^ 10 = s * m ^ 10 + τ * k / v ^ 256 * m ^ 10 := by ring
  unfold dealB
  omega

end CutNums

end Nc.Dl
end
/- Source module Nc.Dl.SizeDeal. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

namespace Sz

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

theorem size_app (p : Tree) (e : Fm) : (app p e).code.size = p.size + e.code.size + 17 := by
  rw [app, size_run, size_quote]; ring

theorem size_lett (e b : Fm) : (lett e b).code.size = b.code.size + e.code.size + 17 := by
  rw [lett, size_run, size_quote]; ring

theorem size_foldF (step s l : Fm) : (foldF step s l).code.size ≤ 2 * step.code.size + s.code.size + l.code.size + 500 := by
  rw [foldF, size_app, size_cons, size_cons, size_quote, foldB, size_ite, size_run, size_cons, size_cons, size_lett,
    size_cons]
  simp only [size_hd, size_tl, size_id]
  omega

theorem size_mapF (step s l : Fm) : (mapF step s l).code.size ≤ 2 * step.code.size + s.code.size + l.code.size + 600 := by
  rw [mapF, size_app, size_cons, size_cons, size_quote, mapB, size_ite, size_cons, size_lett, size_cons, size_run,
    size_cons, size_cons]
  simp only [size_hd, size_tl, size_id, size_quote, Tree.size]
  omega

theorem size_listT (l : List Tree) : (listT l).size = (l.map Tree.size).sum + l.length + 1 := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [listT, Tree.size, ih, List.map_cons, List.sum_cons, List.length_cons]; ring

theorem sum_le {α : Type*} {l : List α} {f : α → ℕ} {n b : ℕ} (hl : l.length ≤ n) (hb : ∀ t ∈ l, f t ≤ b) :
    (l.map f).sum ≤ n * b := by
  have h : (l.map f).sum ≤ l.length * b := by
    clear hl
    induction l with
    | nil => simp
    | cons t l ih =>
      have h1 := hb t List.mem_cons_self
      have h2 := ih fun t ht => hb t (List.mem_cons_of_mem _ ht)
      rw [List.map_cons, List.sum_cons, List.length_cons, add_mul, one_mul]
      omega
  exact h.trans (Nat.mul_le_mul_right _ hl)

theorem size_listT_le {l : List Tree} {n b : ℕ} (hl : l.length ≤ n) (hb : ∀ t ∈ l, t.size ≤ b) :
    (listT l).size ≤ n * (b + 1) + 1 := by
  have h := sum_le hl hb
  rw [size_listT, mul_add, mul_one]
  omega

theorem size_c (t : Tree) : (Tm.c t).tree.size = t.size + 2 := by
  simp only [Tm.tree, Tree.size, size_num]; ring

theorem size_get (p : List Bool) : (Tm.get p).tree.size = (ofBits p).size + 4 := by
  simp only [Tm.tree, Tree.size, size_num]; ring

theorem size_tmCons (a b : Tm) : (Tm.cons a b).tree.size = a.tree.size + b.tree.size + 7 := by
  simp only [Tm.tree, Tree.size, size_num]; ring

theorem size_ifeq (p : List Bool) (t : Tree) (a b : Tm) :
    (Tm.ifeq p t a b).tree.size = (ofBits p).size + t.size + a.tree.size + b.tree.size + 11 := by
  simp only [Tm.tree, Tree.size, size_num]; ring

theorem size_tmApp (a b : Tm) : (Tm.app a b).tree.size = a.tree.size + b.tree.size + 11 := by
  simp only [Tm.tree, Tree.size, size_num]; ring

theorem size_ifTm (p : List Bool) (t : Tree) (a : Tm) :
    (ifTm p t a).tree.size = (ofBits p).size + t.size + a.tree.size + 14 := by
  rw [ifTm, size_ifeq, size_c]
  simp only [Tree.size]

theorem size_listTm (ts : List Tm) : (listTm ts).tree.size = (ts.map fun t => t.tree.size).sum + 7 * ts.length + 3 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [listTm, size_tmCons, ih, List.map_cons, List.sum_cons, List.length_cons]; ring

theorem size_listTm_le {ts : List Tm} {n b : ℕ} (hl : ts.length ≤ n) (hb : ∀ t ∈ ts, t.tree.size ≤ b) :
    (listTm ts).tree.size ≤ n * (b + 7) + 3 := by
  have h := sum_le hl hb
  rw [size_listTm, mul_add]
  omega

theorem size_catTm (ts : List Tm) : (catTm ts).tree.size = (ts.map fun t => t.tree.size).sum + 11 * ts.length + 3 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [catTm, size_tmApp, ih, List.map_cons, List.sum_cons, List.length_cons]; ring

theorem size_catTm_le {ts : List Tm} {n b : ℕ} (hl : ts.length ≤ n) (hb : ∀ t ∈ ts, t.tree.size ≤ b) :
    (catTm ts).tree.size ≤ n * (b + 11) + 3 := by
  have h := sum_le hl hb
  rw [size_catTm, mul_add]
  omega

theorem size_bits {w : List Bool} {L : ℕ} (h : w.length ≤ L) : (ofBits w).size ≤ 4 * L + 1 :=
  (size_ofBits w).trans (by omega)

theorem size_bit (b : Bool) : (bit b).size ≤ 3 := by cases b <;> simp [bit, one, Tree.size]

theorem size_pick (p : List Bool) (t : Tree) : (DStep.pick p t).tree.size = (ofBits p).size + t.size + 3 := by
  simp only [DStep.tree, Tree.size, size_num]; ring

theorem size_op (p q d : List Bool) (φ : Tree) : (DStep.op p q d φ).tree.size =
    (ofBits p).size + (ofBits q).size + (ofBits d).size + φ.size + 7 := by
  simp only [DStep.tree, Tree.size, size_num]; ring

theorem size_dbits (p d : List Bool) : (DStep.bits p d).tree.size = (ofBits p).size + (ofBits d).size + 7 := by
  simp only [DStep.tree, Tree.size, size_num]; ring

theorem size_check (p : List Bool) : (DStep.check p).tree.size = (ofBits p).size + 8 := by
  simp only [DStep.tree, Tree.size, size_num]; ring

end Sz

open Sz

section formulas


def dealC : ℕ := 4 * (dstepF []).code.size + 2 * partStep.code.size + 2 * (wordB .nil .nil).code.size +
  2 * (tmF (.tl .id) (.hd .id)).code.size + 5000

theorem size_dstepF (n : List Bool) : (dstepF n).code.size + 1 = (dstepF []).code.size + (ofBits n).size := by
  have h : ∀ n, (bitsF n).code.size = 2 * bitsB.code.size + (ofBits n).size + 22 := by
    intro n
    rw [bitsF, size_app, size_quote]
    simp only [Tree.size]
    ring
  simp only [dstepF, size_ite, size_lett, size_cons, h]
  have : (ofBits []).size = 1 := rfl
  rw [this]
  ring

theorem size_wordB (t0 t1 : Tree) : (wordB t0 t1).code.size + 2 = (wordB .nil .nil).code.size + t0.size + t1.size := by
  simp only [wordB, size_ite, size_cons, size_quote, Tree.size]
  ring


theorem size_dealF (t0 t1 : Tree) (names : List (List Bool)) (nl nub : List Bool) (sts sts' : List DStep) (ts : List Tm) :
    (dealF t0 t1 names nl nub sts sts' ts).code.size ≤ dealC + 4 * (ofBits nub).size + (ofBits nl).size +
      2 * t0.size + 2 * t1.size + (listT (names.map ofBits)).size + (listT (sts.map DStep.tree)).size +
      (listT (sts'.map DStep.tree)).size + (listT (ts.map Tm.tree)).size := by
  have h7 : (wordF t0 t1 .id).code.size = 2 * (wordB t0 t1).code.size + 49 := by
    rw [wordF, size_app, size_cons, size_cons, size_quote, size_quote, size_id]
    simp only [Tree.size]
    ring
  have h1 : (dstepsF nub sts (partsF names nl (wordF t0 t1 .id))).code.size ≤ 2 * (dstepF nub).code.size +
      (partsF names nl (wordF t0 t1 .id)).code.size + ((listT (sts.map DStep.tree)).size + 2) + 500 := by
    rw [dstepsF, ← size_quote]
    exact size_foldF _ _ _
  have h2 : (dstepsF nub sts' .id).code.size ≤ 2 * (dstepF nub).code.size + 5 +
      ((listT (sts'.map DStep.tree)).size + 2) + 500 := by
    rw [dstepsF, ← size_quote, ← size_id]
    exact size_foldF _ _ _
  have h3 : (tmsF ts .id).code.size ≤ 2 * (tmF (.tl .id) (.hd .id)).code.size + 5 +
      ((listT (ts.map Tm.tree)).size + 2) + 600 := by
    rw [tmsF, ← size_quote, ← size_id]
    exact size_mapF _ _ _
  have h4 : (partsF names nl (wordF t0 t1 .id)).code.size ≤ 2 * partStep.code.size +
      (1 + 2 + ((ofBits nl).size + 2 + (2 * (wordB t0 t1).code.size + 49) + 11) + 11) +
      ((listT (names.map ofBits)).size + 2) + 500 + 6 := by
    rw [partsF, size_hd, ← h7]
    have := size_foldF partStep (.cons (.quote .nil) (.cons (.quote (ofBits nl)) (wordF t0 t1 .id)))
      (.quote (listT (names.map ofBits)))
    rw [size_cons, size_cons, size_quote, size_quote, size_quote] at this
    simp only [Tree.size] at this
    exact Nat.add_le_add_right this 6
  have h5 := size_dstepF nub
  have h6 := size_wordB t0 t1
  have h8 : dealC = 4 * (dstepF []).code.size + 2 * partStep.code.size + 2 * (wordB .nil .nil).code.size +
    2 * (tmF (.tl .id) (.hd .id)).code.size + 5000 := rfl
  rw [dealF, size_lett, size_lett, h8]
  generalize (dstepsF nub sts (partsF names nl (wordF t0 t1 .id))).code.size = a1 at *
  generalize (dstepsF nub sts' .id).code.size = a2 at *
  generalize (tmsF ts .id).code.size = a3 at *
  generalize (partsF names nl (wordF t0 t1 .id)).code.size = a4 at *
  generalize (dstepF nub).code.size = a5 at *
  generalize (dstepF []).code.size = a6 at *
  generalize (wordB t0 t1).code.size = a7 at *
  generalize (wordB .nil .nil).code.size = a8 at *
  generalize (tmF (.tl .id) (.hd .id)).code.size = a9 at *
  generalize partStep.code.size = a10 at *
  omega

end formulas

variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] {K A' E U0 U1 mm D pS c : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) (tab : SlpTab P grp D pS)
  (qn : Q → ℕ) (tg : M.R → ℕ) (bT bub nl nub : List Bool) (gt : Fin mm → Tree) (d1 gp : Tree) (cb : Option Γ → Fin c → Bool)
  (b0 b1 : Γ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D)


structure SizeHyp (X Lc : ℕ) : Prop where
  hLc : 1 ≤ Lc
  nm : ∀ y, (C.nm y).length ≤ Lc
  dc : ∀ d, (C.dc d).length ≤ Lc
  rc : ∀ d, (C.rc d).length ≤ Lc
  key : ∀ y, (C.key y).length ≤ Lc
  dkey : ∀ y, (C.dkey y).length ≤ Lc
  hK1 : K + 1 ≤ X
  hK2 : K + K ≤ X
  hU0 : U0 + 1 ≤ X
  hU1 : U1 ≤ X
  hE : E + 1 ≤ X
  hD : D ≤ X
  hpS : pS ≤ X
  hN : Fintype.card M.N ≤ X
  hId : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X
  hS : Fintype.card (Option S) ≤ X
  hQ : Fintype.card Q + 1 ≤ X
  row : Fintype.card (RowData (K + K)) ≤ X
  hR : Fintype.card M.R ≤ X
  Sl : ∀ r : M.R, Fintype.card ((M.kind r.1).SlAt r.2) ≤ X
  Cn : ∀ r : M.R, Fintype.card ((M.kind r.1).CnAt r.2) ≤ X
  hqn : ∀ q, qn q ≤ X
  htg : ∀ r, tg r + 4 ≤ X

section sizes

variable {C} {qn} {tg} {X Lc : ℕ} (H : SizeHyp C qn tg X Lc)

include H

theorem SizeHyp.X1 : 1 ≤ X := (Nat.le_add_left 1 K).trans H.hK1

theorem SizeHyp.facts : X ≤ X * Lc ∧ Lc ≤ X * Lc ∧ X * Lc ≤ (X * Lc) ^ 2 ∧ 1 ≤ X * Lc ∧ X * (X * Lc) ≤ (X * Lc) ^ 2 := by
  have h1 := H.X1
  have h2 := H.hLc
  have h3 : 1 ≤ X * Lc := Nat.mul_le_mul h1 h2
  refine ⟨Nat.le_mul_of_pos_right _ h2, Nat.le_mul_of_pos_left _ h1, ?_, h3, ?_⟩
  · rw [pow_two]
    exact Nat.le_mul_of_pos_right _ h3
  · rw [pow_two]
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ h2)


theorem size_pickS {α : Type} {opts : List α} {o : α → List (NmT S M U0 U1 pS × Tree)} (hopts : opts.length ≤ X)
    (ho : ∀ a ∈ opts, (o a).length ≤ 4 ∧ ∀ b ∈ o a, b.2.size ≤ 19 * (X * Lc)) :
    (pickS C opts o).tree.size ≤ 120 * (X * Lc) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have h1 : ∀ t ∈ opts.map fun a => optT C.nm (o a), t.size ≤ 105 * (X * Lc) := by
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    obtain ⟨h2, h3⟩ := ho a ha
    refine (size_listT_le (n := 4) (b := 25 * (X * Lc)) (by rw [List.length_map]; exact h2) ?_).trans (by omega)
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨b, hb, rfl⟩ := ht
    have h4 := h3 b hb
    have h5 := size_bits (H.nm b.1)
    simp only [Tree.size]
    omega
  have h2 := size_listT_le (n := X) (b := 105 * (X * Lc)) (by rw [List.length_map]; exact hopts) h1
  have h3 := size_bits (H.nm .zero)
  rw [pickS, size_pick]
  simp only [Tree.size]
  have h4 : X * (105 * (X * Lc) + 1) = 105 * (X * (X * Lc)) + X := by ring
  omega

theorem size_dt (d : Fin D) : (C.dt d).size ≤ 4 * Lc + 1 := size_bits (H.dc d)

theorem size_opS (x y z : NmT S M U0 U1 pS) {φ : Tree} (hφ : φ.size ≤ 60 * (X * Lc) ^ 2) :
    (DStep.op (C.nm x) (C.nm y) (C.nm z) φ).tree.size ≤ 120 * (X * Lc) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have h1 := size_bits (H.nm x)
  have h2 := size_bits (H.nm y)
  have h3 := size_bits (H.nm z)
  rw [size_op]
  omega

theorem size_un (x z : NmT S M U0 U1 pS) {f : Fin D → Tree} (hf : ∀ d, (f d).size ≤ 5 * (X * Lc)) :
    (C.un x z f).tree.size ≤ 120 * (X * Lc) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  refine size_opS H _ _ _ ?_
  have h := size_trieOf_le (code := C.dc) (f := fun d => Tree.cons (f d) .nil) (L := Lc) (s := 7 * (X * Lc)) H.dc
    fun d => by
      have := hf d
      simp only [Tree.size]
      omega
  rw [Fintype.card_fin] at h
  have h2 := Nat.mul_le_mul_right (7 * (X * Lc) + 4 * Lc + 4) H.hD
  have h3 : X * (7 * (X * Lc) + 4 * Lc + 4) = 7 * (X * (X * Lc)) + 4 * (X * Lc) + 4 * X := by ring
  omega

theorem size_con (z : NmT S M U0 U1 pS) {t : Tree} (ht : t.size ≤ 5 * (X * Lc)) :
    (C.con z t).tree.size ≤ 120 * (X * Lc) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  refine size_opS H _ _ _ ?_
  simp only [Tree.size]
  omega

theorem size_trie2 {α : Type} [Fintype α] {code : α → List Bool} (hc : ∀ a, (code a).length ≤ Lc)
    (hα : Fintype.card α ≤ X) {f : α → α → Tree} (hf : ∀ a b, (f a b).size ≤ 4 * Lc + 1) :
    (trieOf code fun a => trieOf code fun b => f a b).size ≤ 50 * (X * Lc) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have h1 : ∀ a, (trieOf code fun b => f a b).size ≤ 13 * (X * Lc) + 1 := by
    intro a
    have h := size_trieOf_le (code := code) (f := fun b => f a b) (L := Lc) hc (hf a)
    have h2 := Nat.mul_le_mul_right (4 * Lc + 1 + 4 * Lc + 4) hα
    have h3 : X * (4 * Lc + 1 + 4 * Lc + 4) = 8 * (X * Lc) + 5 * X := by ring
    omega
  have h := size_trieOf_le (code := code) (f := fun a => trieOf code fun b => f a b) (L := Lc) hc h1
  have h2 := Nat.mul_le_mul_right (13 * (X * Lc) + 1 + 4 * Lc + 4) hα
  have h3 : X * (13 * (X * Lc) + 1 + 4 * Lc + 4) = 13 * (X * (X * Lc)) + 4 * (X * Lc) + 5 * X := by ring
  omega


theorem size_keysL {α : Type} {l : List α} {f : α → List Bool} (hl : l.length ≤ X) (hf : ∀ a, (f a).length ≤ Lc) :
    (listT (l.map fun a => ofBits (f a))).size ≤ 19 * (X * Lc) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  refine (size_listT_le (n := X) (b := 4 * Lc + 1) (by rw [List.length_map]; exact hl) ?_).trans ?_
  · intro t ht
    rw [List.mem_map] at ht
    obtain ⟨a, -, rfl⟩ := ht
    exact size_bits (hf a)
  · have : X * (4 * Lc + 1 + 1) = 4 * (X * Lc) + 2 * X := by ring
    omega

theorem length_filter_finRange {n : ℕ} (hn : n ≤ X) (p : Fin n → Bool) : ((List.finRange n).filter p).length ≤ X := by
  have := List.length_filter_le p (List.finRange n)
  rw [List.length_finRange] at this
  omega


theorem size_steps18 : ∀ st ∈ steps18 C tab qn i e hU0 hU1, st.tree.size ≤ 120 * (X * Lc) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have hX1 := H.X1
  have hLc := H.hLc
  have hUX : U0 ≤ X := (Nat.le_succ _).trans H.hU0
  have hdt : ∀ d, (C.dt d).size ≤ 5 * (X * Lc) := fun d => (size_dt H d).trans (by omega)
  have hbit : ∀ b : Bool, (bit b).size ≤ 5 * (X * Lc) := fun b => (size_bit b).trans (by omega)
  intro st hst
  simp only [steps18, List.mem_append] at hst
  rcases hst with h | h | h | h | (h | h | h) | h
  · rw [steps1, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    refine size_pickS H ?_ fun q _ => ⟨by simp, fun b hb => ?_⟩
    · have hQ := H.hQ
      unfold opts1
      split_ifs
      · simpa using hX1
      · simpa using hX1
      · rw [Finset.length_toList, Finset.card_univ]; omega
    · rw [List.mem_singleton] at hb
      subst hb
      have := H.hqn q
      simp only [size_num]
      omega
  · rw [steps2, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    refine size_pickS H (by rw [Finset.length_toList, Finset.card_univ]; exact H.row) fun d _ => ⟨by simp, fun b hb => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · simp only [flagT]
      refine (size_listT_le (n := X) (b := 5) (by simpa using H.hK2) ?_).trans (by omega)
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨k, hk, rfl⟩ := ht
      rw [List.mem_reverse, List.mem_ofFn] at hk
      obtain ⟨b, rfl⟩ := hk
      rw [size_num]
      unfold Grp.rowFlag
      split_ifs <;> omega
    · have := size_bits (H.rc d)
      simp only
      omega
  · rw [steps3, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    refine size_pickS H (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]; exact H.hU0) fun n _ => ⟨?_, ?_⟩
    · simp only [o3, List.length_cons]
      split_ifs <;> simp
    · intro b hb
      simp only [o3, List.mem_cons] at hb
      rcases hb with rfl | rfl | rfl | hb
      · exact size_keysL H (length_filter_finRange H hUX _) fun k => H.key _
      · refine size_keysL H (length_filter_finRange H hUX _) fun k => ?_
        split_ifs
        · exact H.dkey _
        · exact H.key _
      · have := hdt (digN hU0 n)
        simp only
        omega
      · split_ifs at hb
        · rw [List.mem_singleton] at hb
          subst hb
          simp only [dgT]
          refine (size_listT_le (n := X) (b := 8 * Lc + 9) (by
            rw [List.length_map]; exact length_filter_finRange H hUX _) ?_).trans ?_
          · intro t ht
            rw [List.mem_map] at ht
            obtain ⟨k, -, rfl⟩ := ht
            have k1 := size_bits (H.key (Fin.castAdd A' a.1, .init a.1 a.1 k))
            have k2 := size_bits (H.dkey (a.1, k))
            simp only [Grp.Ins.tree, Tree.size, size_num]
            omega
          · have : X * (8 * Lc + 9 + 1) = 8 * (X * Lc) + 10 * X := by ring
            omega
        · simp at hb
  · rw [steps4, List.mem_map] at h
    obtain ⟨ν, -, rfl⟩ := h
    refine size_pickS H (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]; exact H.hU1) fun j _ => ⟨by simp, ?_⟩
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · have := hdt (digO hU1 j)
      simp only
      omega
    · exact size_keysL H (length_filter_finRange H H.hU1 _) fun k => H.key _
    · exact size_keysL H (length_filter_finRange H H.hU1 _) fun k => H.key _
  · rw [steps5, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    have hb : ∀ b : Bool, (bit b).size ≤ 4 * Lc + 1 := fun b => (size_bit b).trans (by omega)
    unfold rowStep
    split_ifs
    · have hb3 : ∀ f : RowData (K + K) → Tree, (∀ d, (f d).size ≤ 3) →
          (Tree.cons (trieOf C.rc f) .nil).size ≤ 60 * (X * Lc) ^ 2 := by
        intro f hf
        have h := size_trieOf_le (code := C.rc) (f := f) (L := Lc) (s := 3) H.rc hf
        have h2 := Nat.mul_le_mul_right (3 + 4 * Lc + 4) H.row
        have h3 : X * (3 + 4 * Lc + 4) = 4 * (X * Lc) + 7 * X := by ring
        simp only [Tree.size]
        omega
      exact size_opS H _ _ _ (hb3 _ fun d => size_bit _)
    · refine size_opS H _ _ _ ((size_trie2 H H.rc H.row fun d' d => hb _).trans (by omega))
  · rw [steps6, List.mem_map] at h
    obtain ⟨k, -, rfl⟩ := h
    unfold slpStep
    split_ifs with h1 h2 h3
    · exact size_un H _ _ hdt
    · exact size_con H _ (hdt _)
    · refine size_opS H _ _ _ ((size_trie2 H H.dc (by rw [Fintype.card_fin]; exact H.hD) fun d d' => size_dt H _).trans
        (by omega))
    · refine size_con H _ ?_
      simp only [Tree.size]
      omega
  · rw [steps7, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    rcases a with y | c | id
    · refine size_un H _ _ fun d => ?_
      have h1 := H.hD
      have h2 := d.2
      rw [size_num]
      omega
    · exact size_un H _ _ fun d => hbit _
    · exact size_un H _ _ fun d => hbit _
  · rw [steps8, List.map_append, List.mem_append, List.map_map, List.map_map, List.mem_map, List.mem_map] at h
    rcases h with ⟨a, -, rfl⟩ | ⟨c, -, rfl⟩
    · have := size_bits (H.nm (.row a.1 a.2))
      simp only [Function.comp_apply, size_check]
      omega
    · have := size_bits (H.nm (.cond c))
      simp only [Function.comp_apply, size_check]
      omega

theorem length_steps18 : (steps18 C tab qn i e hU0 hU1).length ≤ 11 * X ^ 2 := by
  have hX1 := H.X1
  have hX2 : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) X
  have hK1 := H.hK1
  have hN := H.hN
  have hE := H.hE
  have hId := H.hId
  have hp := H.hpS
  have hSK : Fintype.card (Option S) * (K + K) ≤ X ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul H.hS H.hK2
  have hKK : (K + K) * (K + K) ≤ X ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul H.hK2 H.hK2
  have l2 : (univ : Finset (Option S × Fin (K + K))).toList.length = Fintype.card (Option S) * (K + K) := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have l3 : (univ : Finset (Fin (K + K) × Fin (K + K))).toList.length = (K + K) * (K + K) := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have l7 : (univ : Finset (Ix7 M U0 U1)).toList.length = E + (E + 1 + Fintype.card (G.Uid (K + K) U0 M.N U1)) := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_sum, Fintype.card_sum, Fintype.card_option, Fintype.card_fin]
  simp only [steps18, steps1, steps2, steps3, steps4, steps5, steps6, steps7, steps8, List.length_append, List.length_map,
    l2, l3, l7, List.length_finRange]
  simp only [Finset.length_toList, Finset.card_univ, Fintype.card_fin, Fintype.card_option] at hSK ⊢
  omega

theorem size_gN (y : NmT S M U0 U1 pS) : (gN C y).tree.size ≤ 4 * Lc + 5 := by
  have := size_bits (H.nm y)
  rw [gN, size_get]
  omega

theorem size_bodyTm (p : Fin (K + K)) : (bodyTm C p).tree.size ≤ 75 * (X * Lc) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have h : ∀ l : List Tm, l.length ≤ X → (∀ t ∈ l, t.tree.size ≤ 4 * Lc + 5) → (listTm l).tree.size ≤ 19 * (X * Lc) := by
    intro l hl hb
    refine (size_listTm_le hl hb).trans ?_
    have : X * (4 * Lc + 5 + 7) = 4 * (X * Lc) + 12 * X := by ring
    omega
  have h1 := h ((univ : Finset (Option S)).toList.map fun s => gN C (.flag s p)) (by
    rw [List.length_map, Finset.length_toList, Finset.card_univ]; exact H.hS) (by
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨s, -, rfl⟩ := ht
      exact size_gN H _)
  have h2 := h (List.ofFn fun b => gN C (.kR p b)) (by rw [List.length_ofFn]; exact H.hK2) (by
      intro t ht
      rw [List.mem_ofFn] at ht
      obtain ⟨s, rfl⟩ := ht
      exact size_gN H _)
  have h3 := h (List.ofFn fun b => gN C (.kC b p)) (by rw [List.length_ofFn]; exact H.hK2) (by
      intro t ht
      rw [List.mem_ofFn] at ht
      obtain ⟨s, rfl⟩ := ht
      exact size_gN H _)
  rw [bodyTm, size_tmCons, size_tmCons]
  omega

theorem size_baseTm (p : Fin (K + K)) : (baseTm C p).tree.size ≤ 120 * (X * Lc) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  unfold baseTm
  refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
  · rw [Fin.addCases_left, size_tmCons, size_tmCons, size_tmCons, size_c]
    have h1 := size_gN H (.q κ.castSucc)
    have h2 := size_gN H (.q κ.succ)
    have h3 := size_bodyTm H (Fin.castAdd K κ)
    rw [size_num]
    omega
  · rw [Fin.addCases_right, size_tmCons, size_tmCons, size_c]
    have h1 := size_gN H (.part κ)
    have h3 := size_bodyTm H (Fin.natAdd K κ)
    rw [size_num]
    omega

theorem size_basesTm (p : Fin (K + K)) : (basesTm C p).tree.size ≤ 140 * (X * Lc) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have h1 := size_baseTm H p
  have h2 := size_gN H (.dg p)
  rw [basesTm, size_tmCons]
  omega

theorem length_allIds : (G.allIds (K + K) U0 M.N U1).length ≤ X := by
  rw [G.allIds, Finset.length_toList, Finset.card_univ]
  exact H.hId

theorem length_allRoles : (Grp.allRoles M).length ≤ X := by
  refine le_trans (le_of_eq ?_) H.hR
  rw [Grp.allRoles, List.length_flatMap, Fintype.card_sigma]
  have : ∀ x : Fin E, ((univ : Finset (M.kind x).Ro).toList.map (Sigma.mk (β := fun x => (M.kind x).Ro) x)).length = Fintype.card (M.kind x).Ro := by
    intro x
    rw [List.length_map, Finset.length_toList, Finset.card_univ]
  simp only [this]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

variable {d1 : Tree} (hd1 : d1.size ≤ 4 * Lc + 1) {gt : Fin mm → Tree} (hgt : ∀ g, (gt g).size ≤ 4 * Lc + 1)

include hd1

theorem size_slotTm (z : M.Z) (a : Fin (K + K + A')) : (slotTm C tab d1 z a).tree.size ≤ 50 * (X * Lc) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  rw [slotTm]
  refine (size_catTm_le (n := X) (b := 12 * Lc + 21) (by
    rw [List.length_map, List.length_reverse]; exact length_allIds H) ?_).trans ?_
  · intro t ht
    rw [List.mem_map] at ht
    obtain ⟨id, -, rfl⟩ := ht
    have h1 := size_bits (H.nm (.slp (tab.kcons z id)))
    have h2 := size_bits (H.key (a, id))
    rw [size_ifTm, size_c]
    simp only [listT, Tree.size]
    omega
  · have : X * (12 * Lc + 21 + 11) = 12 * (X * Lc) + 32 * X := by ring
    omega

theorem size_roleTm (r : M.R) : (roleTm C tab tg d1 r).tree.size ≤ 120 * (X * Lc) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have h1 := size_listTm_le (ts := (univ : Finset ((M.kind r.1).SlAt r.2)).toList.map fun e =>
    slotTm C tab d1 ⟨r.1, e.1⟩ (M.rp r)) (n := X) (b := 50 * (X * Lc)) (by
      rw [List.length_map, Finset.length_toList, Finset.card_univ]; exact H.Sl r) (by
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨e, -, rfl⟩ := ht
      exact size_slotTm tab H hd1 _ _)
  have h2 := size_listTm_le (ts := (univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
    gN C (.ch ⟨r.1, ν.1⟩ (decide ((M.kind r.1).c ν.1 ≠ r.2)))) (n := X) (b := 4 * Lc + 5) (by
      rw [List.length_map, Finset.length_toList, Finset.card_univ]; exact H.Cn r) (by
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨e, -, rfl⟩ := ht
      exact size_gN H _)
  have h3 := size_gN H (.num r.1)
  have h4 := H.htg r
  rw [roleTm, size_tmCons, size_tmCons, size_tmCons, size_c, size_num]
  have e1 : X * (50 * (X * Lc) + 7) = 50 * (X * (X * Lc)) + 7 * X := by ring
  have e2 : X * (4 * Lc + 5 + 7) = 4 * (X * Lc) + 12 * X := by ring
  omega

omit hd1 in
theorem size_oneTm {k : List Bool} (hk : k.length ≤ Lc) (id : G.Uid (K + K) U0 M.N U1) :
    (oneTm C k id).tree.size ≤ 8 * Lc + 50 := by
  have h1 := size_bits hk
  have h2 := size_gN H (.cont id)
  rw [oneTm, size_listTm]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_singleton, size_tmCons, size_c, size_num]
  omega

include hgt

theorem size_endTm (g : Fin mm) (id : G.Uid (K + K) U0 M.N U1) :
    (endTm C tab gt d1 g id).tree.size ≤ 300 * (X * Lc) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have h1 := size_bits (H.nm (.slp (tab.kcur id)))
  have h2 := size_bits (H.nm (.slp (tab.kgrp (G.hold0 M.np id))))
  have h3 := size_bits (H.nm (.slp (tab.kgrp (G.hold1 M.np id))))
  have h4 := size_bits (H.key (G.hold0 M.np id, id))
  have h5 := size_bits (H.key (G.hold1 M.np id, id))
  have h6 := size_oneTm H (H.key (G.hold0 M.np id, id)) id
  have h7 := size_oneTm H (H.key (G.hold1 M.np id, id)) id
  have h8 := hgt g
  rw [endTm, size_ifTm, size_ifeq, size_ifeq, size_ifTm, size_c]
  simp only [listT, Grp.Ins.tree, Tree.size, size_num]
  omega

variable {bT bub : List Bool} (hbT : bT.length ≤ Lc) (hbub : bub.length ≤ Lc)

include hbT hbub

theorem size_scriptTm (g : Fin mm) : (scriptTm C tab tg bT bub gt d1 g).tree.size ≤ 720 * (X * Lc) ^ 3 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have f6 : (X * Lc) ^ 2 ≤ (X * Lc) ^ 3 := Nat.pow_le_pow_right f4 (by norm_num)
  have f7 : X * (X * Lc) ^ 2 ≤ (X * Lc) ^ 3 := by
    rw [pow_succ (X * Lc) 2, mul_comm]
    exact Nat.mul_le_mul_left _ f1
  have k1 := size_bits hbT
  have k2 := size_bits hbub
  have h1 := sum_le (l := (List.finRange (K + K)).map fun p =>
      ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)) (f := fun t => t.tree.size) (n := X)
      (b := 170 * (X * Lc)) (by rw [List.length_map, List.length_finRange]; exact H.hK2) (by
        intro t ht
        rw [List.mem_map] at ht
        obtain ⟨p, -, rfl⟩ := ht
        have a1 := size_bits (H.nm (.slp (tab.kgrp (Fin.castAdd A' p))))
        have a2 := size_basesTm H p
        have a3 := hgt g
        rw [size_ifTm]
        omega)
  have h2 := sum_le (l := (Grp.allRoles M).map fun r =>
      ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g) (listTm [roleTm C tab tg d1 r])) (f := fun t => t.tree.size) (n := X)
      (b := 160 * (X * Lc) ^ 2) (by rw [List.length_map]; exact length_allRoles H) (by
        intro t ht
        rw [List.mem_map] at ht
        obtain ⟨r, -, rfl⟩ := ht
        have a1 := size_bits (H.nm (.slp (tab.kgrp (M.rp r))))
        have a2 := size_roleTm tab H hd1 r
        have a3 := hgt g
        rw [size_ifTm, size_listTm]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_singleton]
        omega)
  have h3 := sum_le (l := (G.allIds (K + K) U0 M.N U1).map (endTm C tab gt d1 g)) (f := fun t => t.tree.size) (n := X)
      (b := 300 * (X * Lc)) (by rw [List.length_map]; exact length_allIds H) (by
        intro t ht
        rw [List.mem_map] at ht
        obtain ⟨id, -, rfl⟩ := ht
        exact size_endTm tab H hd1 hgt g id)
  have l1 : ((List.finRange (K + K)).map fun p =>
      ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)).length ≤ X := by
    rw [List.length_map, List.length_finRange]; exact H.hK2
  have l2 : ((Grp.allRoles M).map fun r =>
      ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g) (listTm [roleTm C tab tg d1 r])).length ≤ X := by
    rw [List.length_map]; exact length_allRoles H
  have l3 : ((G.allIds (K + K) U0 M.N U1).map (endTm C tab gt d1 g)).length ≤ X := by
    rw [List.length_map]; exact length_allIds H
  rw [scriptTm, size_tmCons, size_c, size_catTm, List.map_append, List.map_append, List.sum_append, List.sum_append,
    List.length_append, List.length_append]
  simp only [Tree.size]
  have e1 : X * (170 * (X * Lc)) = 170 * (X * (X * Lc)) := by ring
  have e2 : X * (160 * (X * Lc) ^ 2) = 160 * (X * (X * Lc) ^ 2) := by ring
  have e3 : X * (300 * (X * Lc)) = 300 * (X * (X * Lc)) := by ring
  omega

variable {gp : Tree} (hgp : gp.size ≤ X)

include hgp

theorem size_instTm (g : Fin mm) : (instTm C tab tg bT bub gt d1 gp g).tree.size ≤ 740 * (X * Lc) ^ 3 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have f6 : (X * Lc) ^ 2 ≤ (X * Lc) ^ 3 := Nat.pow_le_pow_right f4 (by norm_num)
  have h := size_scriptTm tab H hd1 hgt hbT hbub g
  rw [instTm, size_tmCons, size_c]
  omega

variable (hmm : mm ≤ X) {nl nub : List Bool} (hnl : nl.length ≤ Lc) (hnub : nub.length ≤ Lc) (hc : c ≤ X)

include hmm hnl hnub hc


theorem size_dealProg : (dealProg C tab qn tg bT bub nl nub gt d1 gp cb b0 b1 i e hU0 hU1).code.size ≤
    (dealC + 3000) * (X * Lc) ^ 4 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have f6 : (X * Lc) ^ 2 ≤ (X * Lc) ^ 4 := Nat.pow_le_pow_right f4 (by norm_num)
  have f7 : 1 ≤ (X * Lc) ^ 4 := Nat.one_le_pow _ _ f4
  have k1 := size_bits hnl
  have k2 := size_bits hnub
  have hlT : ∀ b : Γ, (lT cb b).size ≤ 4 * X + 1 := fun b => by
    have := size_ofBits (List.ofFn (cb (some b)))
    rw [List.length_ofFn] at this
    rw [lT]
    omega
  have t0 := hlT b0
  have t1 := hlT b1
  have s1 : (listT ((List.finRange K).map fun κ => ofBits (C.nm (.part κ)))).size ≤ 19 * (X * Lc) :=
    size_keysL H (f := fun κ => C.nm (.part κ)) (by
      rw [List.length_finRange]; have := H.hK1; omega) fun κ => H.nm _
  have s1' : (((List.finRange K).map fun κ => C.nm (.part κ)).map ofBits) =
      (List.finRange K).map fun κ => ofBits (C.nm (.part κ)) := by
    rw [List.map_map]
    rfl
  have s2 := size_listT_le (l := (steps18 C tab qn i e hU0 hU1).map DStep.tree) (n := 11 * X ^ 2)
    (b := 120 * (X * Lc) ^ 2) (by rw [List.length_map]; exact length_steps18 tab i e hU0 hU1 H) (by
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨st, hst, rfl⟩ := ht
      exact size_steps18 tab i e hU0 hU1 H st hst)
  have s3 := size_listT_le (l := (steps9 C).map DStep.tree) (n := X) (b := 8 * Lc + 9) (by
      rw [List.length_map, steps9, List.length_map, Finset.length_toList, Finset.card_univ]; exact H.hId) (by
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨st, hst, rfl⟩ := ht
      rw [steps9, List.mem_map] at hst
      obtain ⟨id, -, rfl⟩ := hst
      have a1 := size_bits (H.nm (.cut id))
      have a2 := size_bits (H.nm (.cont id))
      rw [size_dbits]
      omega)
  have s4 := size_listT_le (l := ((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp)).map Tm.tree) (n := X)
    (b := 740 * (X * Lc) ^ 3) (by rw [List.length_map, List.length_map, List.length_finRange]; exact hmm) (by
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨tm, htm, rfl⟩ := ht
      rw [List.mem_map] at htm
      obtain ⟨g, -, rfl⟩ := htm
      exact size_instTm tab H hd1 hgt hbT hbub hgp g)
  have h := size_dealF (lT cb b0) (lT cb b1) ((List.finRange K).map fun κ => C.nm (.part κ)) nl nub
    (steps18 C tab qn i e hU0 hU1) (steps9 C) ((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp))
  rw [s1'] at h
  rw [dealProg]
  have e1 : 11 * X ^ 2 * (120 * (X * Lc) ^ 2 + 1) ≤ 1331 * (X * Lc) ^ 4 := by
    have a1 : X ^ 2 ≤ (X * Lc) ^ 2 := Nat.pow_le_pow_left f1 2
    have a2 : 1 ≤ (X * Lc) ^ 2 := Nat.one_le_pow _ _ f4
    calc 11 * X ^ 2 * (120 * (X * Lc) ^ 2 + 1) ≤ 11 * (X * Lc) ^ 2 * (121 * (X * Lc) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ a1) (by omega)
      _ = 1331 * (X * Lc) ^ 4 := by ring
  have e2 : X * (8 * Lc + 9 + 1) = 8 * (X * Lc) + 10 * X := by ring
  have e3 : X * (740 * (X * Lc) ^ 3 + 1) ≤ 741 * (X * Lc) ^ 4 := by
    have a2 : 1 ≤ (X * Lc) ^ 3 := Nat.one_le_pow _ _ f4
    calc X * (740 * (X * Lc) ^ 3 + 1) ≤ (X * Lc) * (741 * (X * Lc) ^ 3) := Nat.mul_le_mul f1 (by omega)
      _ = 741 * (X * Lc) ^ 4 := by ring
  have e4 : dealC ≤ dealC * (X * Lc) ^ 4 := Nat.le_mul_of_pos_right _ f7
  have e5 : (dealC + 3000) * (X * Lc) ^ 4 = dealC * (X * Lc) ^ 4 + 3000 * (X * Lc) ^ 4 := by ring
  omega

end sizes

end Nc.Dl
end
/- Source module Nc.Dl.SizeScript. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Nc.Grp

theorem size_numT (k : ℕ) : (num k).size = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [num, Tree.size, ih]
    omega

theorem size_listT (l : List Tree) : (listT l).size = (l.map fun t => t.size + 1).sum + 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [listT, Tree.size, ih, List.map_cons, List.sum_cons]
    omega

theorem size_listT_le {l : List Tree} {s : ℕ} (h : ∀ t ∈ l, t.size ≤ s) :
    (listT l).size ≤ l.length * (s + 1) + 1 := by
  rw [size_listT]
  have := List.sum_le_card_nsmul (l.map fun t => t.size + 1) (s + 1) (by
    intro n hn
    rw [List.mem_map] at hn
    obtain ⟨t, ht, rfl⟩ := hn
    exact Nat.succ_le_succ (h t ht))
  rw [List.length_map, smul_eq_mul] at this
  omega

theorem size_listT_le' {l : List Tree} {s X : ℕ} (hl : l.length ≤ X) (h : ∀ t ∈ l, t.size ≤ s) :
    (listT l).size ≤ X * (s + 1) + 1 := by
  refine (size_listT_le h).trans ?_
  have := Nat.mul_le_mul_right (s + 1) hl
  omega

theorem size_keys {ks : List (List Bool)} {X Lc : ℕ} (hl : ks.length ≤ X) (h : ∀ k ∈ ks, k.length ≤ Lc) :
    (listT (ks.map ofBits)).size ≤ X * (4 * Lc + 2) + 1 := by
  refine size_listT_le' (s := 4 * Lc + 1) (by rw [List.length_map]; exact hl) ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  have h1 := size_ofBits k
  have h2 := h k hk
  omega

theorem size_keysT {l : List (List (List Bool))} {X Lc : ℕ} (hl : l.length ≤ X)
    (h : ∀ ks ∈ l, ks.length ≤ X ∧ ∀ k ∈ ks, k.length ≤ Lc) :
    (keysT l).size ≤ X * (X * (4 * Lc + 2) + 2) + 1 := by
  refine size_listT_le' (s := X * (4 * Lc + 2) + 1) (by rw [List.length_map]; exact hl) ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨ks, hks, rfl⟩ := ht
  exact size_keys (h ks hks).1 (h ks hks).2


theorem size_body {B : Body} {X Lc : ℕ} (h1 : B.flags.length ≤ X)
    (h2 : ∀ l ∈ B.flags, l.length ≤ X ∧ ∀ k ∈ l, k ≤ 2) (h3 : B.kR.length ≤ X)
    (h4 : ∀ ks ∈ B.kR, ks.length ≤ X ∧ ∀ k ∈ ks, k.length ≤ Lc) (h5 : B.kC.length ≤ X)
    (h6 : ∀ ks ∈ B.kC, ks.length ≤ X ∧ ∀ k ∈ ks, k.length ≤ Lc) :
    B.tree.size ≤ X * X * (8 * Lc + 10) + 6 * X + 5 := by
  have e1 : (listT (B.flags.map fun l => listT (l.map num))).size ≤ X * (X * 6 + 1 + 1) + 1 := by
    refine size_listT_le' (by rw [List.length_map]; exact h1) ?_
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨l, hl, rfl⟩ := ht
    refine size_listT_le' (s := 5) (by rw [List.length_map]; exact (h2 l hl).1) ?_
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    rw [size_numT]
    have := (h2 l hl).2 k hk
    omega
  have e2 := size_keysT h3 h4
  have e3 := size_keysT h5 h6
  simp only [Body.tree, Tree.size]
  have e4 : X * (X * (4 * Lc + 2) + 2) = X * X * (4 * Lc + 2) + 2 * X := by ring
  have e5 : X * (X * 6 + 1 + 1) = X * X * 6 + 2 * X := by ring
  have e6 : X * X * (8 * Lc + 10) = X * X * 6 + 2 * (X * X * (4 * Lc + 2)) := by ring
  omega

section script

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K E U0 U1 ub c : ℕ} {Gr : Type} [DecidableEq Gr]

variable {qn : Q → ℕ} {cb : Option Γ → Fin c → Bool} {M : Sys F (K + K + A') E} {P : G.Plan M U0 U1}
  {q : Fin (K + 1) → Q} {x : Fin K → List Γ} {ρ : Option S → Fin (K + K) → RowData (K + K)}
  {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}
  {key : Cell M U0 U1 → List Bool} {dkey : Fin (K + K) × Fin U0 → List Bool} {tg : M.R → ℕ} {X Lc : ℕ}

theorem rowFlag_le {A : ℕ} (d : RowData A) (b : Fin A) : rowFlag d b ≤ 2 := by
  unfold rowFlag
  split_ifs <;> omega

theorem size_bodyOf (hK : K + K ≤ X) (hU0 : U0 ≤ X) (hS : Fintype.card (Option S) ≤ X)
    (hkey : ∀ a, (key a).length ≤ Lc) (hdkey : ∀ a, (dkey a).length ≤ Lc) (p : Fin (K + K)) :
    (bodyOf ρ n key dkey p).tree.size ≤ X * X * (8 * Lc + 10) + 6 * X + 5 := by
  have hf : ∀ f : Fin U0 → Bool, ((List.finRange U0).filter f).length ≤ X := fun f => by
    refine (List.length_filter_le _ _).trans ?_
    rw [List.length_finRange]
    exact hU0
  refine size_body ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [bodyOf, List.length_map, Finset.length_toList, card_univ]
    exact hS
  · intro l hl
    simp only [bodyOf, List.mem_map] at hl
    obtain ⟨s, -, rfl⟩ := hl
    refine ⟨by simpa using hK, fun k hk => ?_⟩
    rw [List.mem_reverse, List.mem_ofFn] at hk
    obtain ⟨b, rfl⟩ := hk
    exact rowFlag_le _ _
  · simpa [bodyOf] using hK
  · intro ks hks
    simp only [bodyOf, List.mem_ofFn] at hks
    obtain ⟨b, rfl⟩ := hks
    refine ⟨by rw [List.length_map]; exact hf _, fun k hk => ?_⟩
    rw [List.mem_map] at hk
    obtain ⟨i, -, rfl⟩ := hk
    exact hkey _
  · simpa [bodyOf] using hK
  · intro ks hks
    simp only [bodyOf, List.mem_ofFn] at hks
    obtain ⟨b, rfl⟩ := hks
    refine ⟨by rw [List.length_map]; exact hf _, fun k hk => ?_⟩
    rw [List.mem_map] at hk
    obtain ⟨i, -, rfl⟩ := hk
    split_ifs
    · exact hdkey _
    · exact hkey _


def plen (x : Fin K → List Γ) (p : Fin (K + K)) : ℕ :=
  Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun κ => (x κ).length) p

theorem size_baseIns (hK : K + K ≤ X) (hU0 : U0 ≤ X) (hS : Fintype.card (Option S) ≤ X)
    (hkey : ∀ a, (key a).length ≤ Lc) (hdkey : ∀ a, (dkey a).length ≤ Lc) (hqn : ∀ a, qn a ≤ X)
    (p : Fin (K + K)) :
    (((baseIns qn cb q x ρ n key dkey p).map Ins.tree).map fun t => t.size + 1).sum ≤
      X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10) + plen x p * (4 * c + 2) := by
  have hboth : ((((List.finRange U0).filter fun k => k.1 < (n p p).1).map fun k =>
      (Ins.both (key (Fin.castAdd A' p, .init p p k)) (dkey (p, k))).tree.size + 1)).sum ≤ X * (8 * Lc + 10) := by
    refine (List.sum_le_card_nsmul _ (8 * Lc + 10) ?_).trans ?_
    · intro m hm
      rw [List.mem_map] at hm
      obtain ⟨k, -, rfl⟩ := hm
      have h1 := size_ofBits (key (Fin.castAdd A' p, .init p p k))
      have h2 := size_ofBits (dkey (p, k))
      have h3 := hkey (Fin.castAdd A' p, .init p p k)
      have h4 := hdkey (p, k)
      simp only [Ins.tree, Tree.size, size_numT]
      omega
    · rw [List.length_map, smul_eq_mul]
      refine Nat.mul_le_mul_right _ ((List.length_filter_le _ _).trans ?_)
      rw [List.length_finRange]
      exact hU0
  rw [baseIns, List.map_cons, List.map_cons, List.sum_cons, List.map_map, List.map_map]
  have hb := hboth
  have hsum : ((((List.finRange U0).filter fun k => k.1 < (n p p).1).map
      ((fun t : Tree => t.size + 1) ∘ Ins.tree ∘ fun k =>
        Ins.both (key (Fin.castAdd A' p, .init p p k)) (dkey (p, k))))).sum ≤ X * (8 * Lc + 10) := hb
  have hhead : (Fin.addCases (motive := fun _ => Ins)
      (fun κ => .block (qn (q κ.castSucc)) (qn (q κ.succ)) (bodyOf ρ n key dkey (Fin.castAdd K κ)))
      (fun κ => .input ((x κ).map fun a => List.ofFn (cb (some a))).reverse (bodyOf ρ n key dkey (Fin.natAdd K κ)))
        p).tree.size + 1 ≤ X * X * (8 * Lc + 10) + 10 * X + 12 + plen x p * (4 * c + 2) := by
    unfold plen
    refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
    · rw [Fin.addCases_left, Fin.addCases_left]
      have h1 := size_bodyOf (ρ := ρ) (n := n) hK hU0 hS hkey hdkey (Fin.castAdd K κ)
      have h2 := hqn (q κ.castSucc)
      have h3 := hqn (q κ.succ)
      simp only [Ins.tree, Tree.size, size_numT]
      omega
    · rw [Fin.addCases_right, Fin.addCases_right]
      have h1 := size_bodyOf (ρ := ρ) (n := n) hK hU0 hS hkey hdkey (Fin.natAdd K κ)
      have h2 : (listT ((((x κ).map fun a => List.ofFn (cb (some a))).reverse).map ofBits)).size ≤
          (x κ).length * (4 * c + 1 + 1) + 1 := by
        refine size_listT_le' (by simp) ?_
        intro t ht
        rw [List.mem_map] at ht
        obtain ⟨w, hw, rfl⟩ := ht
        rw [List.mem_reverse, List.mem_map] at hw
        obtain ⟨a, -, rfl⟩ := hw
        have := size_ofBits (List.ofFn (cb (some a)))
        rw [List.length_ofFn] at this
        exact this
      have e : (x κ).length * (4 * c + 1 + 1) = (x κ).length * (4 * c + 2) := by ring
      simp only [Ins.tree, Tree.size, size_numT]
      omega
  refine le_trans (Nat.add_le_add hhead hsum) ?_
  omega

theorem size_roleIns (hU : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X) (hU1 : U1 ≤ X)
    (hSl : ∀ y, Fintype.card (M.kind y).Sl ≤ X) (hCn : ∀ y, Fintype.card (M.kind y).Cn ≤ X)
    (hkey : ∀ a, (key a).length ≤ Lc) (htg : ∀ r, tg r ≤ X) (hnum : ∀ y, P.num n o y ≤ X) (r : M.R) :
    (roleIns P n o key tg r).tree.size ≤ X * X * (8 * Lc + 4) + 8 * X + 15 := by
  classical
  have h1 : (keysT ((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map fun e =>
      ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse)).size ≤
      X * (X * (4 * Lc + 2) + 2) + 1 := by
    refine size_keysT ?_ ?_
    · rw [List.length_map, Finset.length_toList, card_univ]
      exact (Fintype.card_subtype_le _).trans (hSl _)
    · intro ks hks
      rw [List.mem_map] at hks
      obtain ⟨e, -, rfl⟩ := hks
      refine ⟨?_, fun k hk => ?_⟩
      · rw [List.length_reverse, List.length_map, G.Plan.ids]
        refine (List.length_filter_le _ _).trans ?_
        rw [G.allIds, Finset.length_toList, card_univ]
        exact hU
      · rw [List.mem_reverse, List.mem_map] at hk
        obtain ⟨id, -, rfl⟩ := hk
        exact hkey _
  have h2 : (keysT ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k =>
        key (M.rp r, .new ⟨r.1, ν.1⟩ k))).size ≤ X * (X * (4 * Lc + 2) + 2) + 1 := by
    refine size_keysT ?_ ?_
    · rw [List.length_map, Finset.length_toList, card_univ]
      exact (Fintype.card_subtype_le _).trans (hCn _)
    · intro ks hks
      rw [List.mem_map] at hks
      obtain ⟨ν, -, rfl⟩ := hks
      refine ⟨?_, fun k hk => ?_⟩
      · rw [List.length_map]
        refine (List.length_filter_le _ _).trans ?_
        rw [List.length_finRange]
        exact hU1
      · rw [List.mem_map] at hk
        obtain ⟨i, -, rfl⟩ := hk
        exact hkey _
  have h3 := htg r
  have h4 := hnum r.1
  have e : X * (X * (4 * Lc + 2) + 2) = X * X * (4 * Lc + 2) + 2 * X := by ring
  have e' : X * X * (8 * Lc + 4) = 2 * (X * X * (4 * Lc + 2)) := by ring
  simp only [roleIns, Ins.tree, Tree.size, size_numT]
  omega


noncomputable def cutAt (P : G.Plan M U0 U1) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.N → Fin U1)
    (grp : Fin (K + K + A') → Gr) (g : Gr) : Finset (G.Uid (K + K) U0 M.N U1) :=
  open Classical in
  univ.filter fun id => id ∈ P.cur n o E ∧ grp (G.hold0 M.np id) ≠ grp (G.hold1 M.np id) ∧
    (grp (G.hold0 M.np id) = g ∨ grp (G.hold1 M.np id) = g)

theorem length_uwBits_le (w : UW ub) : (uwBits w).length ≤ ub := by
  cases w with
  | none => exact Nat.zero_le _
  | some v => simp [uwBits]

theorem size_endIns (hU : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X) (hkey : ∀ a, (key a).length ≤ Lc)
    (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    (((endIns P n o grp g key b).map Ins.tree).map fun t => t.size + 1).sum ≤
      X * (8 * Lc + 12) + (cutAt P n o grp g).card * (4 * ub) := by
  classical
  have key1 : ∀ l : List (G.Uid (K + K) U0 M.N U1),
      ((((l.filter fun id => id ∈ P.cur n o E).filterMap fun id =>
        if grp (G.hold0 M.np id) = g then
          if grp (G.hold1 M.np id) = g then some (Ins.both (key (G.hold0 M.np id, id)) (key (G.hold1 M.np id, id)))
          else some (.one (key (G.hold0 M.np id, id)) (uwBits (b id)))
        else if grp (G.hold1 M.np id) = g then some (.one (key (G.hold1 M.np id, id)) (uwBits (b id)))
        else none).map Ins.tree).map fun t => t.size + 1).sum ≤
      l.length * (8 * Lc + 12) + (l.map fun id => if id ∈ cutAt P n o grp g then 4 * ub else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons id l ih =>
      rw [List.length_cons, List.map_cons, List.sum_cons]
      have e0 : (l.length + 1) * (8 * Lc + 12) = l.length * (8 * Lc + 12) + (8 * Lc + 12) := by ring
      by_cases hc : id ∈ P.cur n o E
      · rw [List.filter_cons_of_pos (by simpa using hc), List.filterMap_cons]
        have k0 := hkey (G.hold0 M.np id, id)
        have k1 := hkey (G.hold1 M.np id, id)
        have s0 := size_ofBits (key (G.hold0 M.np id, id))
        have s1 := size_ofBits (key (G.hold1 M.np id, id))
        have sw := size_ofBits (uwBits (b id))
        have lw := length_uwBits_le (b id)
        by_cases h0 : grp (G.hold0 M.np id) = g
        · by_cases h1 : grp (G.hold1 M.np id) = g
          · simp only [h0, h1, if_true, List.map_cons, List.sum_cons, Ins.tree, Tree.size, size_numT]
            omega
          · have hcut : id ∈ cutAt P n o grp g := by
              refine mem_filter.2 ⟨mem_univ _, hc, ?_, Or.inl h0⟩
              rw [h0]
              exact fun h => h1 h.symm
            simp only [h0, h1, if_true, if_false, List.map_cons, List.sum_cons, Ins.tree, Tree.size, size_numT,
              if_pos hcut]
            omega
        · by_cases h1 : grp (G.hold1 M.np id) = g
          · have hcut : id ∈ cutAt P n o grp g := by
              refine mem_filter.2 ⟨mem_univ _, hc, ?_, Or.inr h1⟩
              rw [h1]
              exact h0
            simp only [h0, h1, if_true, if_false, List.map_cons, List.sum_cons, Ins.tree, Tree.size, size_numT,
              if_pos hcut]
            omega
          · simp only [h0, h1, if_false]
            omega
      · rw [List.filter_cons_of_neg (by simpa using hc)]
        omega
  have h1 := key1 (G.allIds (K + K) U0 M.N U1)
  have h2 : (G.allIds (K + K) U0 M.N U1).length ≤ X := by
    rw [G.allIds, Finset.length_toList, card_univ]
    exact hU
  have h3 : ((G.allIds (K + K) U0 M.N U1).map fun id => if id ∈ cutAt P n o grp g then 4 * ub else 0).sum =
      (cutAt P n o grp g).card * (4 * ub) := by
    rw [G.allIds, Finset.sum_map_toList, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]
  have h4 := Nat.mul_le_mul_right (8 * Lc + 12) h2
  rw [endIns]
  omega


theorem size_scriptT (hX : 1 ≤ X) (hLc : 1 ≤ Lc) (hK : K + K ≤ X) (hU0 : U0 ≤ X) (hU1 : U1 ≤ X)
    (hS : Fintype.card (Option S) ≤ X) (hU : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X)
    (hR : Fintype.card M.R ≤ X) (hSl : ∀ y, Fintype.card (M.kind y).Sl ≤ X)
    (hCn : ∀ y, Fintype.card (M.kind y).Cn ≤ X) (hkey : ∀ a, (key a).length ≤ Lc)
    (hdkey : ∀ a, (dkey a).length ≤ Lc) (hqn : ∀ a, qn a ≤ X) (htg : ∀ r, tg r ≤ X)
    (hnum : ∀ y, P.num n o y ≤ X) {bT bub : List Bool} (hbT : bT.length ≤ Lc) (hbub : bub.length ≤ Lc)
    (b : G.Uid (K + K) U0 M.N U1 → UW ub) :
    (scriptT bT bub (script qn cb P q x ρ n o grp g key dkey tg b)).size ≤ 200 * X ^ 3 * Lc +
      (∑ κ ∈ univ.filter (fun κ : Fin K => grp (Fin.castAdd A' (Fin.natAdd K κ)) = g), (x κ).length) * (4 * c + 2) +
      (cutAt P n o grp g).card * (4 * ub) := by
  classical
  -- base parties
  have h1 : ((((baseList (A' := A') grp g).flatMap (baseIns qn cb q x ρ n key dkey)).map Ins.tree).map
      fun t => t.size + 1).sum ≤ X * (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) +
      (∑ κ ∈ univ.filter (fun κ : Fin K => grp (Fin.castAdd A' (Fin.natAdd K κ)) = g), (x κ).length) * (4 * c + 2) := by
    have e1 : ∀ l : List (Fin (K + K)), (((l.flatMap (baseIns qn cb q x ρ n key dkey)).map Ins.tree).map
        fun t => t.size + 1).sum ≤ l.length * (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) +
        (l.map (plen x)).sum * (4 * c + 2) := by
      intro l
      induction l with
      | nil => simp
      | cons p l ih =>
        rw [List.flatMap_cons, List.map_append, List.map_append, List.sum_append, List.length_cons, List.map_cons,
          List.sum_cons]
        have h2 := size_baseIns (cb := cb) (q := q) (x := x) (ρ := ρ) (n := n) hK hU0 hS hkey hdkey hqn p
        have e2 : (l.length + 1) * (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) =
          l.length * (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) +
            (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) := by ring
        have e3 : (plen x p + (l.map (plen x)).sum) * (4 * c + 2) =
          plen x p * (4 * c + 2) + (l.map (plen x)).sum * (4 * c + 2) := by ring
        omega
    refine (e1 _).trans (Nat.add_le_add (Nat.mul_le_mul_right _ ?_) (Nat.mul_le_mul_right _ (le_of_eq ?_)))
    · rw [baseList]
      refine (List.length_filter_le _ _).trans ?_
      rw [List.length_finRange]
      exact hK
    · have e2 : ((baseList (A' := A') grp g).map (plen x)).sum =
          ∑ p ∈ univ.filter (fun p : Fin (K + K) => grp (Fin.castAdd A' p) = g), plen x p := by
        rw [← List.sum_toFinset _ nodup_baseList]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext p
        simp [mem_baseList]
      rw [e2, Finset.sum_filter, Fin.sum_univ_add, Finset.sum_filter]
      have e3 : ∀ κ : Fin K, plen x (Fin.castAdd K κ) = 0 := fun κ => Fin.addCases_left _
      have e4 : ∀ κ : Fin K, plen x (Fin.natAdd K κ) = (x κ).length := fun κ => Fin.addCases_right _
      simp only [e3, e4, ite_self, Finset.sum_const_zero, zero_add]
  -- roles
  have h2 : ((((roleList grp g M).map (roleIns P n o key tg)).map Ins.tree).map fun t => t.size + 1).sum ≤
      X * (X * X * (8 * Lc + 4) + 8 * X + 16) := by
    refine (List.sum_le_card_nsmul _ (X * X * (8 * Lc + 4) + 8 * X + 16) ?_).trans ?_
    · intro m hm
      rw [List.mem_map] at hm
      obtain ⟨t, ht, rfl⟩ := hm
      rw [List.mem_map] at ht
      obtain ⟨i, hi, rfl⟩ := ht
      rw [List.mem_map] at hi
      obtain ⟨r, -, rfl⟩ := hi
      have := size_roleIns (key := key) (tg := tg) (P := P) (n := n) (o := o) hU hU1 hSl hCn hkey htg hnum r
      omega
    · rw [List.length_map, List.length_map, List.length_map, smul_eq_mul]
      refine Nat.mul_le_mul_right _ ?_
      rw [roleList]
      refine (List.length_filter_le _ _).trans ?_
      have hnd : (allRoles M).Nodup := pairwise_allRoles.imp fun h => h.1
      rw [← List.toFinset_card_of_nodup hnd]
      exact (card_le_univ _).trans hR
  have h3 := size_endIns (P := P) (n := n) (o := o) (grp := grp) (g := g) (key := key) hU hkey b
  have hT := size_ofBits bT
  have hub := size_ofBits bub
  rw [scriptT, script]
  simp only [Tree.size]
  rw [size_listT, List.map_append, List.map_append, List.map_append, List.map_append, List.sum_append,
    List.sum_append]
  have f1 : X * (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) +
      X * (X * X * (8 * Lc + 4) + 8 * X + 16) + X * (8 * Lc + 12) + 8 * Lc + 6 ≤ 200 * X ^ 3 * Lc := by
    have g1 : X ≤ X ^ 3 * Lc := by
      calc X = X ^ 1 * 1 := by ring
        _ ≤ X ^ 3 * Lc := Nat.mul_le_mul (Nat.pow_le_pow_right hX (by omega)) hLc
    have g2 : X ^ 2 ≤ X ^ 3 * Lc := by
      calc X ^ 2 = X ^ 2 * 1 := by ring
        _ ≤ X ^ 3 * Lc := Nat.mul_le_mul (Nat.pow_le_pow_right hX (by omega)) hLc
    have g3 : X ^ 3 ≤ X ^ 3 * Lc := Nat.le_mul_of_pos_right _ hLc
    have g4 : X ^ 2 * Lc ≤ X ^ 3 * Lc := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hX (by omega))
    have g5 : X * Lc ≤ X ^ 3 * Lc := by
      calc X * Lc = X ^ 1 * Lc := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hX (by omega))
    have g6 : Lc ≤ X ^ 3 * Lc := Nat.le_mul_of_pos_left _ (by positivity)
    have g7 : 1 ≤ X ^ 3 * Lc := Nat.one_le_iff_ne_zero.2 (by positivity)
    have e : X * (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) +
      X * (X * X * (8 * Lc + 4) + 8 * X + 16) + X * (8 * Lc + 12) + 8 * Lc + 6 =
      16 * (X ^ 3 * Lc) + 14 * X ^ 3 + 28 * X ^ 2 + 8 * (X ^ 2 * Lc) + 40 * X + 8 * (X * Lc) + 8 * Lc + 6 := by ring
    rw [e, mul_assoc]
    omega
  omega

end script

end Nc.Dl
end
/- Source module Nc.Grp.PutDef. -/
section
namespace Nc.Grp

open NS1 NS1.Tree


def padTake (ub : ℕ) (r : List Bool) : List Bool := r.take ub ++ List.replicate (ub - r.length) false


def putL (ub : ℕ) : List (List Bool) → List Bool → Tree → List Tree
  | [], r, t => if r = [] then [t] else []
  | k :: ks, r, t => if r = [] then [] else putL ub ks (r.drop ub) (tset k (ofBits (padTake ub r)) t)


def putAll : List (List Bool) → (ℕ → List Bool) → Tree → Tree
  | [], _, t => t
  | k :: ks, u, t => putAll ks (fun i => u (i + 1)) (tset k (ofBits (u 0)) t)


def putsL (ub : ℕ) : List (List (List Bool)) → List (List Bool) → Tree → List Tree
  | [], _, t => [t]
  | ks :: kss, strs, t => (putL ub ks (strs.headD []) t).flatMap (putsL ub kss strs.tail)

end Nc.Grp
end
/- Source module Nc.Grp.Lang. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {α β γ : Type}


def bindL (l : List (A × α)) (f : α → List (A × β)) : List (A × β) :=
  l.flatMap fun p => (f p.2).map fun r => (p.1 * r.1, r.2)


def sumL (l : List (A × α)) (G : α → A) : A := (l.map fun p => p.1 * G p.2).sum

@[simp] theorem sumL_nil (G : α → A) : sumL ([] : List (A × α)) G = 0 := rfl

@[simp] theorem sumL_cons (p : A × α) (l : List (A × α)) (G : α → A) :
    sumL (p :: l) G = p.1 * G p.2 + sumL l G := by simp [sumL]



@[simp] theorem sumL_single (a : α) (G : α → A) : sumL [((1 : A), a)] G = G a := by simp [sumL]











theorem mem_bindL {l : List (A × α)} {f : α → List (A × β)} {p : A × β} (h : p ∈ bindL l f) :
    ∃ a ∈ l, ∃ r ∈ f a.2, p.2 = r.2 := by
  unfold bindL at h
  rw [List.mem_flatMap] at h
  obtain ⟨a, ha, h⟩ := h
  rw [List.mem_map] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨a, ha, r, hr, rfl⟩



































section Fold

variable {ε : Type}


def foldL (f : ε → β → List (A × β)) : List ε → β → List (A × β)
  | [], s => [(1, s)]
  | x :: xs, s => bindL (f x s) (foldL f xs)











end Fold

end Nc.Grp
end
/- Source module Nc.Grp.Trans. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

















def nthF : ℕ → Fm → Fm
  | 0, b => .hd b
  | k + 1, b => nthF k (.tl b)




def mkList : List Fm → Fm
  | [] => .quote .nil
  | f :: fs => .cons f (mkList fs)




def pushF : List Tree → Fm → Fm
  | [], b => b
  | t :: ts, b => .cons (.quote t) (pushF ts b)




def dispF : (m : ℕ) → (Fin m → Fm) → ((Fin m → Bool) → Fm) → Fm
  | 0, _, k => k Fin.elim0
  | m + 1, g, k => .ite (g 0) (dispF m (fun i => g i.succ) fun v => k (Fin.cons true v))
      (dispF m (fun i => g i.succ) fun v => k (Fin.cons false v))




def switchF (t : Fm) : List Fm → Fm
  | [] => .fail
  | f :: fs => .ite t (switchF (.tl t) fs) f



section transducer

variable {Λ : Type}


structure Opt (nC nO : ℕ) (Λ : Type) where
  
  wt : WE
  
  nxt : Fin nC
  
  push : Fin nO → List Λ

variable {nC nI nO : ℕ}


abbrev TSt (nC nI nO : ℕ) (Λ : Type) := Fin nC × (Fin nI → List Bool) × (Fin nO → List Λ)

variable (eL : Λ → Tree)


def encS (s : TSt nC nI nO Λ) : Tree :=
  .cons (num s.1) (.cons (listT (List.ofFn fun i => ofBits (s.2.1 i)))
    (listT (List.ofFn fun j => listT ((s.2.2 j).map eL))))


def Opt.app (o : Opt nC nO Λ) (s : TSt nC nI nO Λ) : TSt nC nI nO Λ :=
  (o.nxt, fun i => (s.2.1 i).tail, fun j => o.push j ++ s.2.2 j)

variable (θ) in

def stepL (tab : Fin nC → (Fin nI → Bool) → List (Opt nC nO Λ)) (s : TSt nC nI nO Λ) : List (A × TSt nC nI nO Λ) :=
  (tab s.1 fun i => (s.2.1 i).headD false).map fun o => (o.wt.val θ, o.app s)

variable {eL}





variable (eL)








variable (θ) in

def runL (tab : Fin nC → (Fin nI → Bool) → List (Opt nC nO Λ)) (k : ℕ) (s : TSt nC nI nO Λ) :
    List (A × TSt nC nI nO Λ) :=
  foldL (fun (_ : Unit) s => stepL θ tab s) (List.replicate k ()) s









end transducer

end Nc.Grp
end
/- Source module Nc.Grp.Seg. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}


def okFlag (f : ℕ) (tk : Bool) : Bool :=
  match f with
  | 0 => !tk
  | 1 => tk
  | _ => true



def segL (sep : List Bool) (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as : List (List Bool))
    (rest : List (List Bool)) (out : List (List Bool)) : List (List (List Bool)) :=
  (if okFlag f tk then
    match fs with
    | [] => if rest = [] then [cur :: out] else []
    | f' :: fs' => segL sep f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out)
  else []) ++
  match rest with
  | [] => []
  | a :: r => segL sep f true (a ++ cur) fs as r out
termination_by fs.length + rest.length


def segS (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool)) : Tree :=
  .cons (num f) (.cons (bit tk) (.cons (ofBits cur) (.cons (listT (fs.map num)) (.cons (listT (as.map ofBits))
    (.cons (listT (rest.map ofBits)) (listT (out.map ofBits)))))))


def sgF : Fm := .hd (.tl .id)

def sgTk : Fm := .hd (.tl (.tl .id))

def sgCur : Fm := .hd (.tl (.tl (.tl .id)))

def sgFs : Fm := .hd (.tl (.tl (.tl (.tl .id))))

def sgAs : Fm := .hd (.tl (.tl (.tl (.tl (.tl .id)))))

def sgRest : Fm := .hd (.tl (.tl (.tl (.tl (.tl (.tl .id))))))

def sgOut : Fm := .tl (.tl (.tl (.tl (.tl (.tl (.tl .id))))))





def segNext (sep : List Bool) : Fm := .cons (.hd .id) (.cons (.hd sgFs) (.cons (.quote .nil)
  (.cons (appF (.quote (ofBits sep)) (.hd sgAs)) (.cons (.tl sgFs) (.cons (.tl sgAs) (.cons sgRest
  (.cons sgCur sgOut)))))))


def segTake : Fm := .cons (.hd .id) (.cons sgF (.cons (.quote one) (.cons (appF (.hd sgRest) sgCur)
  (.cons sgFs (.cons sgAs (.cons (.tl sgRest) sgOut))))))


def segClose (sep : List Bool) : Fm := .ite sgFs (.run (.hd .id) (segNext sep)) (.ite sgRest .fail (.cons sgCur sgOut))


def segB (sep : List Bool) : Fm := .ite .guess
  (.ite sgF (.ite (.tl sgF) (segClose sep) (.ite sgTk (segClose sep) .fail)) (.ite sgTk .fail (segClose sep)))
  (.ite sgRest (.run (.hd .id) segTake) .fail)

section parts

variable {p : Tree} {f : ℕ} {tk : Bool} {cur : List Bool} {fs : List ℕ} {as rest out : List (List Bool)}















end parts






abbrev encL (l : List (List (List Bool))) : List (A × Tree) := l.map fun l => ((1 : A), listT (l.map ofBits))


def closeL (sep cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool)) : List (List (List Bool)) :=
  match fs with
  | [] => if rest = [] then [cur :: out] else []
  | f' :: fs' => segL sep f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out)


def takeL (sep : List Bool) (f : ℕ) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool)) :
    List (List (List Bool)) :=
  match rest with
  | [] => []
  | a :: r => segL sep f true (a ++ cur) fs as r out



section step

variable {sep : List Bool} {c d f : ℕ} {tk : Bool} {cur : List Bool} {fs : List ℕ} {as rest out : List (List Bool)}







end step





def segRow (sep : List Bool) (fl : List ℕ) (accs l : List (List Bool)) : List (List (List Bool)) :=
  match fl with
  | [] => []
  | f :: fs => segL sep f false (sep ++ accs.headD []) fs accs.tail l []

end Nc.Grp
end
/- Source module Nc.Grp.Put. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}


abbrev encT (l : List Tree) : List (A × Tree) := l.map fun t => ((1 : A), t)




def unitStep : Fm := .cons (.tl (.hd (.tl .id))) (.cons (.hd (.hd (.tl .id))) (.tl (.tl .id)))








def putStep : Fm := .ite (.hd (.tl (.tl .id)))
  (lett (.cons .id (foldF unitStep (.cons (.hd (.tl (.tl .id))) (.quote .nil)) (.hd (.tl .id))))
    (.cons (.hd (.tl (.hd .id))) (.cons (.hd (.tl .id))
      (setF (.hd (.hd .id)) (foldF .id (.quote (ofBits [])) (.tl (.tl .id))) (.tl (.tl (.tl (.hd .id))))))))
  .fail

variable (A) in

def putOne (ub : ℕ) (k : List Bool) (s : List Bool × Tree) : List (A × (List Bool × Tree)) :=
  if s.1 = [] then [] else [(1, (s.1.drop ub, tset k (ofBits (padTake ub s.1)) s.2))]

theorem length_padTake (ub : ℕ) (r : List Bool) : (padTake ub r).length = ub := by
  simp only [padTake, List.length_append, List.length_take, List.length_replicate]
  omega

theorem len_ofBits (w : List Bool) : (ofBits w).len = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ofBits, len, ih]




def putF : Fm := lett (foldF putStep (.cons (.hd .id) (.tl (.tl .id))) (.hd (.tl .id)))
  (.ite (.hd (.tl .id)) .fail (.tl (.tl .id)))






def putsStep : Fm := .cons (.hd (.tl .id)) (.cons (.tl (.hd (.tl (.tl .id))))
  (lett (.cons (.hd (.tl .id)) (.cons (.hd .id) (.cons (.hd (.hd (.tl (.tl .id)))) (.tl (.tl (.tl .id)))))) putF))


def putsF : Fm := lett (foldF putsStep (.cons (.hd .id) (.tl (.tl .id))) (.hd (.tl .id))) (.tl (.tl .id))





end Nc.Grp
end
/- Source module Nc.Grp.Role. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}


def streamStep : Fm := .ite (getF (.hd .id) (.hd (.tl .id)))
  (.cons (.hd (.tl .id)) (appF (getF (.hd .id) (.hd (.tl .id))) (.tl (.tl .id)))) .fail


def streamF : Fm := lett (foldF streamStep (.cons (.hd .id) (.quote .nil)) (.tl .id)) (.tl .id)


def streamsStep : Fm := .cons (.hd (.tl .id))
  (.cons (lett (.cons (.hd (.tl .id)) (.hd .id)) streamF) (.tl (.tl .id)))


def streamsF : Fm := lett (foldF streamsStep (.cons (.hd .id) (.quote .nil)) (.tl .id))
  (foldF .id (.quote .nil) (.tl .id))

section stream

variable {ub : ℕ} {ct : List Bool → List Bool} {t : Tree}













end stream

end Nc.Grp
end
/- Source module Nc.Grp.RoleProg. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

variable (θ) in
open Classical in

noncomputable def we (a : A) : WE := if h : ∃ e : WE, e.val θ = a then h.choose else .zero




noncomputable def slList (L : G.Law A) (p : L.Ro) : List (L.SlAt p) := (univ : Finset (L.SlAt p)).toList


noncomputable def cnList (L : G.Law A) (p : L.Ro) : List (L.CnAt p) := (univ : Finset (L.CnAt p)).toList


noncomputable def slIdx (L : G.Law A) (p : L.Ro) (e : L.SlAt p) : Fin (slList L p).length :=
  ⟨(slList L p).idxOf e, List.idxOf_lt_length_of_mem (Finset.mem_toList.2 (mem_univ e))⟩

variable (θ) in

noncomputable def roleTab (L : G.Law A) (p : L.Ro) (_ : Fin 1) (v : Fin (slList L p).length → Bool) :
    List (Opt 1 (cnList L p).length Bool) :=
  (univ : Finset (Bk L p)).toList.map fun z => ⟨we θ (L.tab p z.1 (fun e => v (slIdx L p e)) z.2), 0,
    fun j => (List.ofFn (L.lab z.1) ++ List.ofFn (z.2 ((cnList L p).get j))).reverse⟩


def yardF : Fm := .tl (foldF (.cons (.hd (.tl .id)) (appF (.hd (.tl .id)) (.tl (.tl .id)))) (.cons (.hd .id) (.quote .nil))
  (.hd (.tl (.tl .id))))





variable (θ) in

noncomputable def roleSem (L : G.Law A) (p : L.Ro) (ub : ℕ) (ct : List Bool → List Bool) (tt : ℕ)
    (slots keys : List (List (List Bool))) (t : Tree) : List (A × Tree) :=
  if ∀ es ∈ slots, ∀ k ∈ es, ct k ≠ [] then
    bindL (runL θ (roleTab θ L p) (tt * ub)
      (0, fun i => ((slots.map fun es => es.reverse.flatMap ct).getD i []), fun _ => [])) fun s =>
      encT (putsL ub keys (List.ofFn fun j => (s.2.2 j).reverse ++ [true]) t)
  else []


def roleEnd : Fm := lett (.cons (.hd (.hd .id)) (.cons (.tl (.tl (.tl (.tl (.hd .id)))))
  (.cons (mapF (foldF .id (.quote (ofBits [true])) (.tl .id)) (.quote .nil) (.tl (.tl (.tl .id))))
    (.hd (.tl (.hd .id)))))) putsF






end Nc.Grp
end
/- Source module Nc.Grp.Base. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

section seg


abbrev Item := List ℕ × List (List Bool)


def encI (it : Item) : Tree := .cons (listT (it.1.map num)) (listT (it.2.map ofBits))


def encA (l : List (List Bool)) : Tree := listT (l.map ofBits)

variable (A) in

def segOne (sep : List Bool) (it : Item) (accs : List (List Bool)) : List (A × List (List Bool)) :=
  (segRow sep it.1 accs it.2).map fun out => ((1 : A), out.reverse)






def segStepF (sep : List Bool) : Fm := .ite (.hd (.hd .id))
  (lett (app (segB sep).code (.cons (.quote (segB sep).code) (.cons (.hd (.hd (.hd .id))) (.cons (.quote .nil)
    (.cons (appF (.quote (ofBits sep)) (.hd (.tl .id))) (.cons (.tl (.hd (.hd .id))) (.cons (.tl (.tl .id))
      (.cons (.tl (.hd .id)) (.quote .nil))))))))) (foldF .id (.quote .nil) .id)) .fail



variable (A) in

def segsL (sep : List Bool) (items : List Item) (accs : List (List Bool)) : List (A × List (List Bool)) :=
  foldL (segOne A sep) items accs


def segsF (sep : List Bool) : Fm := foldF (segStepF sep) (.tl .id) (.hd .id)



end seg

end Nc.Grp
end
/- Source module Nc.Grp.BaseProg. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

section sim

variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}
  (mu : Letter S Unit Γ → Matrix Q Q A) (cb : Option Γ → Fin c → Bool)


noncomputable def tapes (S : Type) [Fintype S] [DecidableEq S] : List (Option S) := (univ : Finset (Option S)).toList


noncomputable abbrev nT (S : Type) [Fintype S] [DecidableEq S] : ℕ := (tapes S).length


def chOf : Ch S Unit → Option S × Bool
  | .tp s b => (some s, b)
  | .inp _ => (none, true)


noncomputable def outOf (j : Fin (nT S + nT S)) : Option S × Bool :=
  Fin.addCases (motive := fun _ => Option S × Bool) (fun i => ((tapes S).get i, false)) (fun i => ((tapes S).get i, true)) j


def code (a : Γ) : List Bool := List.ofFn (cb (some a))


noncomputable def pushOf (z : Letter S Unit Γ) (j : Fin (nT S + nT S)) : List (List Bool) :=
  match z with
  | none => []
  | some (ch, a) => if chOf ch = outOf j then [code cb a] else []




variable (θ) in

noncomputable def simTab (q : Fin (Fintype.card Q)) (_ : Fin 0 → Bool) :
    List (Opt (Fintype.card Q) (nT S + nT S) (List Bool)) :=
  (univ : Finset (Letter S Unit Γ × Q)).toList.map fun z => ⟨we θ (mu z.1 ((qn Q).symm q) z.2), qn Q z.2, pushOf cb z.1⟩


abbrev Outs (S : Type) [Fintype S] [DecidableEq S] := Fin (nT S + nT S) → List (List Bool)


noncomputable def encO (o : Outs S) : Tree := listT (List.ofFn fun j => listT ((o j).map ofBits))

variable (θ) in

noncomputable def simSem (T : ℕ) (q q' : Fin (Fintype.card Q)) : List (A × Outs S) :=
  bindL (runL θ (simTab θ mu cb) T (q, Fin.elim0, fun _ => [])) fun s => if s.1 = q' then [((1 : A), s.2.2)] else []



theorem size_num (k : ℕ) : (num k).size = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [num, size, ih]
    omega










noncomputable def inOuts (part : List (List Bool)) : Outs S := fun j => if outOf j = (none, false) then part else []




section pack


noncomputable def itemsR (flags : List (List ℕ)) (o : Outs S) : List Item :=
  List.ofFn fun i : Fin (nT S) => (flags.getD i.rev [], o (Fin.castAdd (nT S) i.rev))


noncomputable def itemsC (m : ℕ) (o : Outs S) : List Item :=
  List.ofFn fun i : Fin (nT S) => (List.replicate m 2, o (Fin.natAdd (nT S) i.rev))





end pack

end sim

end Nc.Grp
end
/- Source module Nc.Grp.Pack. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {S : Type} [Fintype S] [DecidableEq S]

variable (A) in

noncomputable def packSem (sep : List Bool) (ub : ℕ) (B : Body) (o : Outs S) (t : Tree) : List (A × Tree) :=
  bindL (segsL A sep (itemsR B.flags o) (List.replicate B.kR.length [true])) fun sR =>
    bindL (encT (A := A) (putsL ub B.kR sR.reverse t)) fun t1 =>
      bindL (segsL A sep (itemsC B.kR.length o) (List.replicate B.kR.length [true])) fun sC =>
        encT (putsL ub B.kC sC.reverse t1)




















end Nc.Grp
end
/- Source module Nc.Grp.GroupProg. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

section unary


def unF (b : Fm) : Fm := foldF (.ite (.hd .id) (.cons (.quote .nil) (appF (.tl .id) (.tl .id))) (appF (.tl .id) (.tl .id)))
  (.quote .nil) b







end unary

section group

variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}
  (mu : Letter S Unit Γ → Matrix Q Q A) (cb : Option Γ → Fin c → Bool) (kinds : List (Σ L : G.Law A, L.Ro))


def sepOf : List Bool := List.ofFn (cb none)

variable (θ) in

noncomputable def insSem (T ub : ℕ) : Ins → Tree → List (A × Tree)
  | .block q q' B, t => if h : q < Fintype.card Q ∧ q' < Fintype.card Q then
      bindL (simSem θ mu cb T ⟨q, h.1⟩ ⟨q', h.2⟩) fun o => packSem A (sepOf cb) ub B o t else []
  | .input part B, t => packSem A (sepOf cb) ub B (inOuts (S := S) part) t
  | .both k k', t => if tget k t = tget k' t then [(1, t)] else []
  | .one k w, t => if tget k t = ofBits w then [(1, t)] else []
  | .role j tt slots keys, t => match kinds[j]? with
    | some z => roleSem θ z.1 z.2 ub (fun k => (tget k t).path) tt slots keys t
    | none => []


def InsOk (S Q : Type) [Fintype S] [DecidableEq S] [Fintype Q] (c : ℕ) (kinds : List (Σ L : G.Law A, L.Ro)) : Ins → Prop
  | .block q q' _ => q < Fintype.card Q ∧ q' < Fintype.card Q
  | .input part _ => ∀ a ∈ part, a.length ≤ c
  | .both _ _ => True
  | .one _ _ => True
  | .role j _ slots _ => ∃ z, kinds[j]? = some z ∧ slots.length = (slList z.1 z.2).length








def TOk (ub : ℕ) (t : Tree) : Prop := ∀ k, ∃ w : List Bool, tget k t = ofBits w ∧ w.length ≤ ub

theorem TOk.path {ub : ℕ} {t : Tree} (h : TOk ub t) (k : List Bool) : tget k t = ofBits (tget k t).path ∧
    (tget k t).path.length ≤ ub := by
  obtain ⟨w, h1, h2⟩ := h k
  rw [h1, path_ofBits]
  exact ⟨rfl, h2⟩



theorem TOk.tset {ub : ℕ} {t : Tree} (h : TOk ub t) (k w : List Bool) (hw : w.length ≤ ub) :
    TOk ub (tset k (ofBits w) t) := by
  intro k'
  rw [tget_tset]
  split_ifs
  · exact ⟨w, rfl, hw⟩
  · exact h k'

theorem TOk.putL {ub : ℕ} {keys : List (List Bool)} {r : List Bool} {t : Tree} (h : TOk ub t) :
    ∀ t' ∈ putL ub keys r t, TOk ub t' := by
  induction keys generalizing r t with
  | nil =>
    intro t' ht'
    rw [Grp.putL] at ht'
    split_ifs at ht'
    · rw [List.mem_singleton] at ht'
      exact ht' ▸ h
    · simp at ht'
  | cons k ks ih =>
    intro t' ht'
    rw [Grp.putL] at ht'
    split_ifs at ht'
    · simp at ht'
    · exact ih (h.tset k _ (length_padTake _ _).le) t' ht'

theorem TOk.putsL {ub : ℕ} {kss : List (List (List Bool))} {strs : List (List Bool)} {t : Tree} (h : TOk ub t) :
    ∀ t' ∈ putsL ub kss strs t, TOk ub t' := by
  induction kss generalizing strs t with
  | nil =>
    intro t' ht'
    rw [Grp.putsL, List.mem_singleton] at ht'
    exact ht' ▸ h
  | cons ks kss ih =>
    intro t' ht'
    rw [Grp.putsL, List.mem_flatMap] at ht'
    obtain ⟨t1, h1, h2⟩ := ht'
    exact ih (h.putL t1 h1) t' h2

theorem mem_encT {l : List Tree} {q : A × Tree} (h : q ∈ encT (A := A) l) : q.2 ∈ l := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  exact ht

theorem TOk.pack {sep : List Bool} {ub : ℕ} {B : Body} {o : Outs S} {t : Tree} (h : TOk ub t) :
    ∀ q ∈ packSem A sep ub B o t, TOk ub q.2 := by
  intro q hq
  obtain ⟨a, -, r, hr, e1⟩ := mem_bindL hq
  obtain ⟨b, hb, r', hr', e2⟩ := mem_bindL hr
  obtain ⟨d, -, r'', hr'', e3⟩ := mem_bindL hr'
  rw [e1, e2, e3]
  exact (h.putsL _ (mem_encT hb)).putsL _ (mem_encT hr'')

theorem TOk.insSem {T ub : ℕ} {i : Ins} {t : Tree} (h : TOk ub t) :
    ∀ q ∈ insSem θ mu cb kinds T ub i t, TOk ub q.2 := by
  intro q hq
  cases i with
  | block q₁ q₂ B =>
    rw [Grp.insSem] at hq
    split_ifs at hq
    · obtain ⟨a, -, r, hr, e1⟩ := mem_bindL hq
      rw [e1]
      exact h.pack r hr
    · simp at hq
  | input part B => exact h.pack q hq
  | both k k' =>
    rw [Grp.insSem] at hq
    split_ifs at hq
    · rw [List.mem_singleton] at hq
      exact hq ▸ h
    · simp at hq
  | one k w =>
    rw [Grp.insSem] at hq
    split_ifs at hq
    · rw [List.mem_singleton] at hq
      exact hq ▸ h
    · simp at hq
  | role j tt slots keys =>
    rw [Grp.insSem] at hq
    split at hq
    · unfold roleSem at hq
      split_ifs at hq
      · obtain ⟨a, -, r, hr, e1⟩ := mem_bindL hq
        rw [e1]
        exact h.putsL _ (mem_encT hr)
      · simp at hq
    · simp at hq


def encG (T ub : ℕ) (t : Tree) : Tree := .cons (num T) (.cons (num ub) t)







variable (θ) in

noncomputable def scriptSem (T ub : ℕ) (l : List Ins) (t : Tree) : List (A × Tree) :=
  foldL (insSem (S := S) θ mu cb kinds T ub) l t




end group

end Nc.Grp
end
/- Source module Nc.Dl.Inst. -/
section
set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes








structure CodesLe {A : Type} [CommRing A] {S : Type} [Fintype S] {K A' E U0 U1 D pS : ℕ} {M : Sys A (K + K + A') E}
    (C : Codes S M U0 U1 D pS) (Lc : ℕ) : Prop where
  nm : ∀ y, (C.nm y).length ≤ Lc
  dc : ∀ d, (C.dc d).length ≤ Lc
  rc : ∀ d, (C.rc d).length ≤ Lc
  key : ∀ a, (C.key a).length ≤ Lc
  dkey : ∀ a, (C.dkey a).length ≤ Lc
  inj : Function.Injective (Sum.elim C.key C.dkey)

theorem exists_codes {A : Type} [CommRing A] {S : Type} [Fintype S] [DecidableEq S] {K A' E U0 U1 D pS : ℕ}
    {M : Sys A (K + K + A') E} {Lc : ℕ}
    (h1 : Fintype.card (Nm K E pS S M.N (G.Uid (K + K) U0 M.N U1)) ≤ 2 ^ Lc) (h2 : D ≤ 2 ^ Lc)
    (h3 : Fintype.card (RowData (K + K)) ≤ 2 ^ Lc)
    (h4 : Fintype.card (Grp.Cell M U0 U1 ⊕ Fin (K + K) × Fin U0) ≤ 2 ^ Lc) :
    ∃ C : Codes S M U0 U1 D pS, CodesLe C Lc := by
  obtain ⟨f1, i1, l1⟩ := exists_code _ h1
  obtain ⟨f2, i2, l2⟩ := exists_code (Fin D) (by rwa [Fintype.card_fin])
  obtain ⟨f3, i3, l3⟩ := exists_code _ h3
  obtain ⟨f4, i4, l4⟩ := exists_code _ h4
  refine ⟨⟨f1, i1, f2, i2, f3, i3, fun a => f4 (.inl a), fun a => f4 (.inr a)⟩, fun y => (l1 y).le, fun y => (l2 y).le,
    fun y => (l3 y).le, fun y => (l4 _).le, fun y => (l4 _).le, ?_⟩
  intro x y hxy
  apply i4
  cases x <;> cases y <;> exact hxy

variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] {θ : List Bool → A} {K A' E U0 U1 mm D pS c ℓ : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} {mu : Letter S Unit Γ → Matrix Q Q A}
  {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)} {qn : Q → ℕ} {GROUP : Fm} {κ : ℕ}


theorem card_cutUnits_le {n : NN K U0} {o : M.N → Fin U1} {bd : ℕ}
    (h : ∀ g, ((P.cur n o E).filter (Nc.Plus.OneIn (G.hold0 M.np) (G.hold1 M.np) (grp n o) g)).card ≤ bd) :
    (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)).card ≤ mm * bd := by
  classical
  have hsub : cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E) ⊆ (univ : Finset (Fin mm)).biUnion fun g =>
      (P.cur n o E).filter (Nc.Plus.OneIn (G.hold0 M.np) (G.hold1 M.np) (grp n o) g) := by
    intro id hid
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hid
    rw [Finset.mem_biUnion]
    exact ⟨grp n o (G.hold0 M.np id), Finset.mem_univ _, Finset.mem_filter.2 ⟨h1, Or.inl ⟨rfl, Ne.symm h2⟩⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine (Finset.sum_le_sum fun g _ => h g).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem card_cutAt_le {n : NN K U0} {o : M.N → Fin U1} {bd : ℕ} {g : Fin mm}
    (h : ((P.cur n o E).filter (Nc.Plus.OneIn (G.hold0 M.np) (G.hold1 M.np) (grp n o) g)).card ≤ bd) :
    (cutAt P n o (grp n o) g).card ≤ bd := by
  classical
  refine (Finset.card_le_card fun id hid => ?_).trans h
  unfold cutAt at hid
  obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hid
  refine Finset.mem_filter.2 ⟨h1, ?_⟩
  rcases h3 with h3 | h3
  · exact Or.inl ⟨h3, fun h4 => h2 (h3.trans h4.symm)⟩
  · exact Or.inr ⟨fun h4 => h2 (h4.trans h3.symm), h3⟩

open Classical in


theorem _root_.Paper.thm_onecut_program {i e : Q} {b0 b1 : Γ} {τ s cap bd ιb X Lc tB : ℕ} {tg : M.R → ℕ} {bT bub nub nl : List Bool}
    -- the automaton and GROUP
    (hK : 0 < K) [Nonempty Q] (hGR : GroupOK θ mu cb kinds qn GROUP κ)
    (hU : ∀ z, z.size ≤ s → Plain θ τ z → runVal mu i e (K * Grp.bval bT) (fun _ => wordG b0 b1 z) = pv θ z)
    (hkind : ∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩)
    -- the plan, the formula and the bounds of the pieces
    (tab : SlpTab P grp D pS) (hP : P.Ok cap) (hub : 0 < Grp.bval bub) (hnub : KT.val nub = Grp.bval bub)
    (hnl : KT.val nl = ℓ) (hU1p : 0 < U1) (hℓ : ℓ ≤ Grp.bval bT)
    (hval : ∀ z, z.size ≤ s → runVal mu i e (K * Grp.bval bT) (fun _ => wordG b0 b1 z) =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
          ∑ n : NN K U0, if tab.valid n then
            ∑ o : M.N → Fin U1, if ∀ x, P.good n o x then
              ∑ b ∈ Common (none : UW (Grp.bval bub)) (cutUnits (G.hold0 M.np) (G.hold1 M.np) (grp n o) (P.cur n o E)),
                ∏ g, G.grpVal mu (Grp.bval bT) cb P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g b
            else 0
          else 0
        else 0
      else 0)
    (hbdle : ∀ n o, tab.valid n → (∀ x, P.good n o x) → ∀ g,
      ((P.cur n o E).filter (Nc.Plus.OneIn (G.hold0 M.np) (G.hold1 M.np) (grp n o) g)).card ≤ bd)
    (hbase : ∀ n o, tab.valid n → (∀ x, P.good n o x) → ∀ g,
      (univ.filter fun p : Fin (K + K) => grp n o (Fin.castAdd A' p) = g).card ≤ ιb)
    (hnum : ∀ n o y, P.num n o y ≤ X)
    -- digits
    (hU0D : U0 < D) (hU1D : U1 ≤ D) (hD1 : 1 < D) (hmmD : mm ≤ D)
    -- sizes
    (C : Codes S M U0 U1 D pS) (hC : CodesLe C Lc) (hLc : 1 ≤ Lc) (hbT : bT.length ≤ Lc) (hbub : bub.length ≤ Lc)
    (hnubl : nub.length ≤ Lc) (hnll : nl.length ≤ Lc) (hK1 : K + K + 1 ≤ X) (hU0X : U0 + 1 ≤ X) (hU1X : U1 ≤ X) (hE : E + 1 ≤ X)
    (hDX : D ≤ X) (hpS : pS ≤ X) (hN : Fintype.card M.N ≤ X) (hId : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X)
    (hS : Fintype.card (Option S) ≤ X) (hQ : Fintype.card Q + 1 ≤ X) (hrow : Fintype.card (RowData (K + K)) ≤ X)
    (hR : Fintype.card M.R ≤ X) (hSl : ∀ y, Fintype.card (M.kind y).Sl ≤ X) (hCn : ∀ y, Fintype.card (M.kind y).Cn ≤ X)
    (hqn : ∀ q, qn q ≤ X) (htg : ∀ r, tg r + 4 ≤ X) (hgp : GROUP.code.size ≤ X) (hmm : mm ≤ X) (hcX : c ≤ X)
    -- time of GROUP
    (htB : ∀ (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0)
      (o : M.N → Fin U1) (b : G.Uid (K + K) U0 M.N U1 → UW (Grp.bval bub)) (g : Fin mm), (∀ κ, (x κ).length ≤ Grp.bval bT) →
      tab.valid n → (∀ x, P.good n o x) →
      grpT bT bub (Grp.script qn cb P q x ρ n o (grp n o) g C.key C.dkey tg b) ≤ tB) :
    ∃ G : Tree, G.size ≤ (dealC + 3000) * (X * Lc) ^ 4 ∧ CutD θ τ s (κ * tB)
      (X + 1 + (200 * X ^ 3 * Lc + ιb * ℓ * (4 * c + 2) + bd * (4 * Grp.bval bub))) mm
      (dealB Lc X K mm (Grp.bval bub) (mm * bd) (4 * (X * X) + 10 * X) s) G := by
  classical
  have : Nonempty (Fin U1) := ⟨⟨0, hU1p⟩⟩
  have hSlAt : ∀ r : M.R, Fintype.card ((M.kind r.1).SlAt r.2) ≤ X := fun r => (Fintype.card_subtype_le _).trans (hSl _)
  have hCnAt : ∀ r : M.R, Fintype.card ((M.kind r.1).CnAt r.2) ≤ X := fun r => (Fintype.card_subtype_le _).trans (hCn _)
  let gt : Fin mm → Tree := fun g => C.dt ⟨g, lt_of_lt_of_le g.2 hmmD⟩
  let d1 : Tree := C.dt ⟨1, hD1⟩
  have hd1 : ∀ d : Fin D, C.dt d = d1 ↔ d.1 = 1 := fun d => by
    rw [show d1 = C.dt ⟨1, hD1⟩ from rfl, dt_inj.eq_iff, Fin.ext_iff]
  have hgt : ∀ (d : Fin D) (g : Fin mm), C.dt d = gt g ↔ d.1 = g.1 := fun d g => by
    rw [show gt g = C.dt ⟨g, lt_of_lt_of_le g.2 hmmD⟩ from rfl, dt_inj.eq_iff, Fin.ext_iff]
  have hdts : ∀ d, (C.dt d).size ≤ 4 * Lc + 1 := fun d => by
    have h1 := size_ofBits (C.dc d)
    have h2 := hC.dc d
    rw [dt]
    omega
  have hH : SizeHyp C qn tg X Lc := by
    refine { hLc := hLc, nm := hC.nm, dc := hC.dc, rc := hC.rc, key := hC.key, dkey := hC.dkey, hK1 := by omega,
             hK2 := by omega, hU0 := hU0X, hU1 := hU1X, hE := hE, hD := hDX, hpS := hpS, hN := hN, hId := hId, hS := hS,
             hQ := hQ, row := hrow, hR := hR, Sl := ?_, Cn := ?_, hqn := hqn, htg := htg }
    · exact hSlAt
    · exact hCnAt
  refine ⟨(dealProg C tab qn tg bT bub nl nub gt d1 GROUP.code cb b0 b1 i e hU0D hU1D).code,
    size_dealProg (tab := tab) (H := hH) (hd1 := hdts _) (hgt := fun g => hdts _) (hbT := hbT) (hbub := hbub) (hgp := hgp)
      (hmm := hmm) (hnl := hnll) (hnub := hnubl) (hc := hcX) .., ?_⟩
  refine deal_cut C tab qn tg bT bub nl nub gt d1 GROUP.code cb b0 b1 i e hU0D hU1D hK hnl hnub hd1 hgt hU
    hval ?_ ?_
  · intro z hz
    exact deal_does hK hnl hnub hnll hnubl hC.nm hC.dc hC.rc hLc hQ hrow hU0X hU1X hS (by omega) hId hSlAt hCnAt hR
      (length_steps18_le hQ hS hK1 hN hpS hE hId) (fun n o hn ho => card_cutUnits_le (hbdle n o hn ho)) z hz
  · intro z hz q ρ n o b g hρ hn ho hb
    have hx : ∀ κ : Fin K, (parts ℓ (wordG b0 b1 z) κ).length ≤ Grp.bval bT := fun κ => (length_parts_le _ _ _).trans hℓ
    have hρ' : ∀ s p, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2 := by
      intro s p hf
      have := hρ s p
      rw [if_neg (by simp [hf])] at this
      exact this.2
    obtain ⟨h1, h2, h3⟩ := hGR P q (parts ℓ (wordG b0 b1 z)) ρ n o (grp n o) g C.key C.dkey tg bT bub b hC.inj hub hP hx hρ'
      hkind
    refine ⟨?_, ?_, h2⟩
    · have hsz := size_scriptT (qn := qn) (cb := cb) (P := P) (q := q) (x := parts ℓ (wordG b0 b1 z)) (ρ := ρ) (n := n)
        (o := o) (grp := grp n o) (g := g) (key := C.key) (dkey := C.dkey) (tg := tg) (X := X) (Lc := Lc) (by omega) hLc
        (by omega) (by omega) hU1X hS hId hR hSl hCn hC.key hC.dkey hqn (fun r => by have := htg r; omega) (hnum n o) hbT hbub b
      have hparts : (∑ κ ∈ univ.filter (fun κ : Fin K => grp n o (Fin.castAdd A' (Fin.natAdd K κ)) = g),
          (parts ℓ (wordG b0 b1 z) κ).length) ≤ ιb * ℓ := by
        refine (Finset.sum_le_card_nsmul _ _ ℓ fun κ _ => length_parts_le _ _ _).trans ?_
        rw [smul_eq_mul]
        refine Nat.mul_le_mul_right _ ?_
        refine le_trans ?_ (hbase n o hn ho g)
        refine Finset.card_le_card_of_injOn (Fin.natAdd K) ?_ ?_
        · intro κ hκ
          simpa using hκ
        · intro κ _ κ' _ h
          simpa using h
      have hcut := card_cutAt_le (hbdle n o hn ho g)
      have e1 := Nat.mul_le_mul_right (4 * c + 2) hparts
      have e2 := Nat.mul_le_mul_right (4 * Grp.bval bub) hcut
      simp only [Tree.size]
      omega
    · exact ⟨h1.1, fun r hr => ⟨(h1.2 r hr).1,
        (h1.2 r hr).2.trans (Nat.mul_le_mul_left κ (htB q _ ρ n o b g hx hn ho))⟩⟩

end Nc.Dl
end
/- Source module Nc.Dl.GrpCost. -/
section
namespace Nc.Dl
open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes
section Bits

theorem bval_append (l : List Bool) (b : Bool) : Grp.bval (l ++ [b]) = 2 * Grp.bval l + b.toNat := by
  simp [Grp.bval]

theorem bval_reverse (w : List Bool) : Grp.bval w.reverse = KT.val w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [List.reverse_cons, bval_append, ih, KT.val]
    cases b <;> simp <;> omega

theorem exists_bits (n : ℕ) {L : ℕ} (h : n < 2 ^ L) : (bitsN L n).length = L ∧ KT.val (bitsN L n) = n ∧
    (bitsN L n).reverse.length = L ∧ Grp.bval (bitsN L n).reverse = n :=
  ⟨length_bitsN L n, val_bitsN L n h, by rw [List.length_reverse, length_bitsN], by rw [bval_reverse, val_bitsN L n h]⟩

end Bits

section Cards

theorem card_uid_le {A0 U0 U1 : ℕ} {N : Type} [Fintype N] [DecidableEq N] :
    Fintype.card (G.Uid A0 U0 N U1) ≤ A0 * A0 * U0 + Fintype.card N * U1 := by
  let f : G.Uid A0 U0 N U1 → (Fin A0 × Fin A0 × Fin U0) ⊕ (N × Fin U1) := fun id => match id with
    | .init a b k => .inl (a, b, k)
    | .new ν k => .inr (ν, k)
  have hf : Function.Injective f := by
    intro x y h
    cases x <;> cases y <;> simp only [f, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq] at h
    · obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
    · obtain ⟨rfl, rfl⟩ := h
      rfl
  have h := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h
  calc _ ≤ _ := h
    _ = _ := by ring

theorem card_row (A0 : ℕ) : Fintype.card (RowData A0) = 2 * (A0 * A0) := by
  simp [RowData, Fintype.card_prod]

set_option maxHeartbeats 4000000 in
theorem card_nm {K E pS : ℕ} {S N Id : Type} [Fintype S] [Fintype N] [Fintype Id] {X : ℕ} (h1 : K + K + 1 ≤ X)
    (h2 : Fintype.card (Option S) ≤ X) (h3 : Fintype.card N ≤ X) (h4 : pS ≤ X) (h5 : E + 1 ≤ X) (h6 : Fintype.card Id ≤ X) :
    Fintype.card (Nm K E pS S N Id) ≤ 30 * (X * X) := by
  have hX : 1 ≤ X := by omega
  have e := Fintype.card_congr (nmEquiv (K := K) (E := E) (pS := pS) (S := S) (N := N) (Id := Id))
  rw [← e]
  have a1 : Fintype.card (Option S) * (K + K) ≤ X * X := Nat.mul_le_mul h2 (by omega)
  have a2 : (K + K) * (K + K) ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
  have a3 : X ≤ X * X := Nat.le_mul_of_pos_left _ hX
  have a4 : Fintype.card (Option (Fin E)) = E + 1 := by rw [Fintype.card_option, Fintype.card_fin]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit, Fintype.card_bool, a4]
  omega

end Cards

end Nc.Dl
end
/- Source module Paper.Postpone. -/
section
namespace Paper

open NS1
open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]



def postponed (p z : Tree) (e : Bt) : Tree := zq p z e










end Paper
end
/- Source module NS1.Scale. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]


def CutAt (θ : List Bool → A) (H v α : ℕ) : Prop :=
  ∀ τ s, v ^ H ≤ τ → τ ≤ v ^ (H * α) → s * v ^ 48 ≤ τ → ∃ G, CutProg θ H v τ s G

theorem CutHyp.at {H C₀ v₀ v α : ℕ} (h : CutHyp θ H C₀ v₀) (hv : v₀ ≤ v) (hl : lg v ^ (C₀ * α) ≤ v) : CutAt θ H v α :=
  fun τ s => h v hv α τ s hl




def cst : ℕ := WF.code.size + UF.code.size + 2000












end NS1
end
/- Source module NS1.Main. -/
section
set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

section Map

variable {R' : Type} [CommRing R'] [Algebra A R']

namespace KT


def map (f : R → R') : KT R → KT R'
  | none => none
  | leaf c => leaf (f c)
  | node l r => node (l.map f) (r.map f)





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


def consts : KT R → Set R
  | none => ∅
  | leaf c => {c}
  | node l r => l.consts ∪ r.consts





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



theorem le_lg_of_two_pow_le {n k : ℕ} (h : 2 ^ k ≤ n) : k + 1 ≤ lg n :=
  Nat.succ_le_succ (Nat.le_log_of_pow_le (by norm_num) h)

theorem two_pow_lg_le {n : ℕ} (hn : n ≠ 0) : 2 ^ (lg n - 1) ≤ n := by
  unfold lg
  rw [Nat.add_sub_cancel]
  exact Nat.pow_log_le_self 2 hn


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







def HasAcc (θ : List Bool → A) (R : Type) [CommRing R] [Algebra A R] (H v s : ℕ) : Prop :=
  ∃ (K : KT R) (B : ℕ) (D : Tree), IsAccT θ H v (v ^ (H - 16)) K B D ∧ K.nds ≤ s ∧ D.size ≤ s ∧
    K.ht ≤ lg (max (v ^ H) s) ^ 2 ∧ B ≤ lg (max (v ^ H) s) ^ 3

end NS1
end
/- Source module Paper.Cuts. -/
section
namespace NS1
variable {A : Type} [CommRing A] {θ : List Bool → A}
theorem Plain.mono {τ τ' : ℕ} {z : Tree} (h : Plain θ τ z) (hτ : τ ≤ τ') : Plain θ τ' z :=
  ⟨h.1, fun r hr => ⟨(h.2 r hr).1, (h.2 r hr).2.trans hτ⟩⟩

theorem CutD.mono {τ s τ' s' P t τ'' s'' P' t' : ℕ} {G : Tree} (h : CutD θ τ s τ' s' P t G) (h1 : τ' ≤ τ'')
    (h2 : s' ≤ s'') (h3 : P ≤ P') (h4 : t ≤ t') : CutD θ τ s τ'' s'' P' t' G := by
  intro z hz
  obtain ⟨Q, hD, hQ, hv⟩ := h z hz
  exact ⟨Q, hD.mono h4, fun q hq => ⟨(hQ q hq).1.trans h3, fun y hy => ((hQ q hq).2 y hy).trans h2⟩, fun hp =>
    ⟨fun q hq y hy => ((hv hp).1 q hq y hy).mono h1, (hv hp).2⟩⟩

end NS1
namespace Paper
open NS1 Finset Nc.Vp Nc.Tow
open Nc.Tower (U ee)
open NS1.Tree
variable {A : Type} [CommRing A]
theorem exists_generates (A : Type) [CommRing A] [Algebra.FiniteType ℤ A] : ∃ θ : List Bool → A, Generates θ :=
  Nc.Dl.exists_theta A

theorem lg_mul_sq_le {τ v : ℕ} : lg (τ * v ^ 2) ≤ lg τ + 2 * lg v + 1 := by
  have h1 : τ * v ^ 2 < 2 ^ (lg τ + 2 * lg v) := by
    rw [pow_add, Nat.mul_comm 2, pow_mul]
    exact Nat.mul_lt_mul'' (lt_two_pow_lg τ) (Nat.pow_lt_pow_left (lt_two_pow_lg v) (by norm_num))
  unfold lg at h1 ⊢
  rcases Nat.eq_zero_or_pos (τ * v ^ 2) with h | h
  · rw [h, Nat.log_zero_right]
    omega
  · have := Nat.log_lt_of_lt_pow (by omega) h1
    omega

set_option maxHeartbeats 1200000 in
/-- **Paper: Theorem thm:onecut.** "There are constants a₀, C, v₀ such that for all v ≥ v₀, all τ ≥ v^a₀ with
4 lg τ ≤ (lg v)², all s ≤ τ and 2 ≤ k ≤ v^64, with Λ = (lg v)^C, a program of size at most v^a₀ cuts (τ,s) into
(τΛ/k, (s/k + τ/v^256)Λ) with at most kΛ pieces, in (s + τk/v^256)Λ steps." The laws and the generators θ are the
standing hypothesis "Fix the ring A and the laws". The proof takes the automaton from Proposition prop:universal and
the formula and the bounds of the pieces from Proposition prop:pieces, and puts the evaluator and the program G on
them. -/
theorem thm_onecut {θ : List Bool → A} (hθ : Generates θ) {h : ℕ} [NeZero h]
    (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (h : ℝ) / 4) :
    ∃ a₀ C v₀ : ℕ, ∀ v, v₀ ≤ v → ∀ τ s k, v ^ a₀ ≤ τ → 4 * lg τ ≤ lg v ^ 2 → s ≤ τ → 2 ≤ k → k ≤ v ^ 64 →
      ∃ G : Tree, G.size ≤ v ^ a₀ ∧ CutD θ τ s (τ * lg v ^ C / k) ((s / k + τ / v ^ 256) * lg v ^ C)
        (k * lg v ^ C) ((s + τ * k / v ^ 256) * lg v ^ C) G := by
  classical
  obtain ⟨S, Γ, Q, i1, i2, i3, i4, i5, i6, mu, i, e', b0, b1, CU, hCU⟩ := ValiantBorder.universalAutomaton θ hθ.1
  obtain ⟨a, e, he, hpieces⟩ := ValiantBorder.lawTapePieces VL h3 hgain
  obtain ⟨Cp, v₁, hP⟩ := hpieces Γ S Q mu
  obtain ⟨kinds, hkinds⟩ : ∃ l, l = Nc.Tow.kindList A ((univ : Finset VL.Di).toList.map VL.L) := ⟨_, rfl⟩
  rw [← hkinds] at hP
  -- one evaluator for each code of symbols
  choose GR κ hGR hGT using fun (c : Fin (Cp + 1)) (cb : Option Γ → Fin c.1 → Bool) =>
    ValiantBorder.weightedGroupEvaluator hθ mu cb kinds
  obtain ⟨Zg, hZg⟩ : ∃ Z, Z = ∑ c : Fin (Cp + 1), ∑ cb : Option Γ → Fin c.1 → Bool, ((GR c cb).code.size + κ c cb) :=
    ⟨_, rfl⟩
  obtain ⟨ml, hml⟩ : ∃ m, m = (kinds.map fun L : (Σ L : Nc.G.Law A, L.Ro) =>
      Fintype.card L.1.Ro + Fintype.card L.1.Sl + Fintype.card L.1.Cn).sum := ⟨_, rfl⟩
  obtain ⟨cq, hcq⟩ : ∃ cq, ∀ q, (Nc.Grp.qn Q q : ℕ) ≤ cq :=
    ⟨univ.sup fun q => (Nc.Grp.qn Q q : ℕ), fun q => Finset.le_sup (f := fun q => (Nc.Grp.qn Q q : ℕ)) (Finset.mem_univ q)⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b, b = 3 * Cp + 3 * e + a + 8 := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ : ∃ C, C = Cp + 10 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 20000 + Cp + Zg + ml + cq + Fintype.card S + Fintype.card Q + kinds.length + Nc.Dl.dealC +
      16 * (CU + 1) + 3 * b₁ + 4 * Cp + 8 := ⟨_, rfl⟩
  obtain ⟨n1, hn1⟩ := poly_lg 1 C1
  refine ⟨a + e + 6 * b₁ + 400, 10 * C1, 2 ^ (Z + 1) + v₁ + n1, fun v hv τ s k hτ hlτ hsτ hk hkv => ?_⟩
  -- logarithms
  obtain ⟨l, hl⟩ : ∃ l, l = lg v := ⟨_, rfl⟩
  have hlbig : Z + 1 < l := by
    rw [hl]; exact le_lg_of_two_pow_le (le_trans (by omega) hv)
  have hl1 : 1 ≤ l := by omega
  have hpow1 := Nat.one_le_two_pow (n := Z + 1)
  have hv0 : v ≠ 0 := by omega
  have hv1 : 1 ≤ v := by omega
  have hlv : l ≤ v := by
    rw [hl]
    unfold lg
    exact Nat.log_lt_self 2 hv0
  obtain ⟨m, hm⟩ : ∃ m, m = l ^ C1 := ⟨_, rfl⟩
  have hml' : ∀ p, p ≤ C1 → l ^ p ≤ m := fun p hp => hm ▸ Nat.pow_le_pow_right hl1 hp
  have hlm : l ≤ m := by
    have := hml' 1 (by omega)
    rwa [pow_one] at this
  have hmv : m ≤ v := by
    have := hn1 v (by omega)
    rw [one_mul, ← hl, ← hm] at this
    exact this
  have hm1 : 1 ≤ m := hl1.trans hlm
  have vpow : ∀ {p q}, p ≤ q → v ^ p ≤ v ^ q := fun h => Nat.pow_le_pow_right hv1 h
  have vpos : ∀ p, 0 < v ^ p := fun p => Nat.pow_pos (by omega)
  have vone : v ≤ v ^ 1 := (pow_one v).ge
  -- the number of blocks
  obtain ⟨K, hKv, hKv', hP⟩ := hP v (by omega)
  have hK0 : 0 < K := lt_of_lt_of_le (vpos e) hKv
  have hvK : v ^ 300 ≤ K := (vpow he).trans hKv
  have hKe : K ≤ v ^ (e + 1) := by
    calc K ≤ Cp * v ^ e := hKv'
      _ ≤ v * v ^ e := Nat.mul_le_mul_right _ (by omega)
      _ = v ^ (e + 1) := (pow_succ' v e).symm
  obtain ⟨X, hX⟩ : ∃ X, X = v ^ b₁ := ⟨_, rfl⟩
  have vX : ∀ p, p ≤ b₁ → v ^ p ≤ X := fun p hp => hX ▸ vpow hp
  have hX1 : 1 ≤ X := hX ▸ Nat.pow_pos hv1
  have hvX : v ≤ X := vone.trans (vX 1 (by omega))
  have hKX : K ≤ X := hKe.trans (vX _ (by omega))
  have hsmall : X ^ 6 * m ^ 20 * v ^ 300 ≤ τ := by
    calc X ^ 6 * m ^ 20 * v ^ 300 ≤ X ^ 6 * v ^ 20 * v ^ 300 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmv 20))
      _ = v ^ (b₁ * 6 + 20 + 300) := by rw [hX, ← pow_mul, ← pow_add, ← pow_add]
      _ ≤ v ^ (a + e + 6 * b₁ + 400) := vpow (by omega)
      _ ≤ τ := hτ
  have hXτ : X ≤ τ := by
    calc X = X ^ 1 * 1 * 1 := by ring
      _ ≤ X ^ 6 * m ^ 20 * v ^ 300 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_right hX1 (by norm_num))
          (Nat.pow_pos hm1)) (vpos 300)
      _ ≤ τ := hsmall
  have hτ1 : 1 ≤ τ := hX1.trans hXτ
  -- the steps: a plain instance is the value of the universal automaton in KT steps
  obtain ⟨tU, htU⟩ : ∃ t, t = (CU + 1) * (2 * τ + 2) * lg (2 * τ + 2) ^ 2 := ⟨_, rfl⟩
  have hl2 : lg τ + 3 ≤ 2 * l ^ 2 := by
    have : l ≤ l ^ 2 := Nat.le_self_pow (by norm_num) l
    rw [← hl] at hlτ
    omega
  have hlgτ : lg (2 * τ + 2) ≤ 2 * l ^ 2 := by
    have h1 : 2 * τ + 2 < 2 ^ (lg τ + 2) := by
      have := lt_two_pow_lg τ
      rw [pow_add]
      omega
    have h2 : Nat.log 2 (2 * τ + 2) < lg τ + 2 := Nat.log_lt_of_lt_pow (by omega) h1
    have e1 : lg (2 * τ + 2) = Nat.log 2 (2 * τ + 2) + 1 := rfl
    omega
  have htUle : tU ≤ τ * l ^ 5 := by
    calc tU ≤ (CU + 1) * (4 * τ) * (2 * l ^ 2) ^ 2 := by
          rw [htU]
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left hlgτ 2)
      _ = τ * (16 * (CU + 1) * l ^ 4) := by ring
      _ ≤ τ * (l * l ^ 4) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = τ * l ^ 5 := by ring
  obtain ⟨T, hT⟩ : ∃ T, T = tU / K + 1 := ⟨_, rfl⟩
  have hKTge : tU ≤ K * T := by
    have h1 := Nat.div_add_mod tU K
    have h2 := Nat.mod_lt tU hK0
    rw [hT, Nat.mul_add, Nat.mul_one]
    omega
  have hKT : K * T ≤ τ * m := by
    calc K * T = K * (tU / K) + K := by rw [hT]; ring
      _ ≤ tU + τ := Nat.add_le_add (Nat.mul_div_le _ _) (hKX.trans hXτ)
      _ ≤ τ * l ^ 5 + τ * l ^ 5 := Nat.add_le_add htUle (Nat.le_mul_of_pos_right _ (Nat.pow_pos hl1))
      _ = τ * (2 * l ^ 5) := by ring
      _ ≤ τ * (l * l ^ 5) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = τ * l ^ 6 := by ring
      _ ≤ τ * m := Nat.mul_le_mul_left _ (hml' 6 (by omega))
  have hτtU : τ ≤ tU := by
    rw [htU]
    have h1 : 1 ≤ lg (2 * τ + 2) ^ 2 := Nat.pow_pos (by unfold lg; omega)
    calc τ ≤ 1 * (2 * τ + 2) * 1 := by omega
      _ ≤ (CU + 1) * (2 * τ + 2) * lg (2 * τ + 2) ^ 2 := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) h1
  have hTa : v ^ a ≤ T := by
    refine Nat.le_of_mul_le_mul_left (?_ : v ^ (e + 1) * v ^ a ≤ v ^ (e + 1) * T) (vpos _)
    calc v ^ (e + 1) * v ^ a = v ^ (e + 1 + a) := (pow_add _ _ _).symm
      _ ≤ v ^ (a + e + 6 * b₁ + 400) := vpow (by omega)
      _ ≤ K * T := hτ.trans (hτtU.trans hKTge)
      _ ≤ v ^ (e + 1) * T := Nat.mul_le_mul_right _ hKe
  obtain ⟨pc⟩ := hP T k hTa hk hkv
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = s / K + 1 := ⟨_, rfl⟩
  have hℓT : ℓ ≤ T := by
    rw [hℓ, hT]
    exact Nat.add_le_add_right (Nat.div_le_div_right (hsτ.trans hτtU)) 1
  have hsK : s ≤ K * ℓ := by
    have h1 := Nat.div_add_mod s K
    have h2 := Nat.mod_lt s hK0
    rw [hℓ, Nat.mul_add, Nat.mul_one]
    omega
  -- numbers below X
  obtain ⟨hD, hst, hA', hE, hU0, hU1⟩ := pc.steps_le
  have hCX : v ^ Cp + 1 ≤ X := by
    calc v ^ Cp + 1 ≤ v ^ Cp * v := by
          have : 1 ≤ v ^ Cp := vpos Cp
          have : v ^ Cp * 2 ≤ v ^ Cp * v := Nat.mul_le_mul_left _ (by omega)
          omega
      _ = v ^ (Cp + 1) := (pow_succ v Cp).symm
      _ ≤ X := vX _ (by omega)
  have h3K : 3 * K ≤ v * K := Nat.mul_le_mul_right _ (by omega)
  have hK2 : K + K + 1 ≤ X := by
    calc K + K + 1 ≤ v * K := by omega
      _ ≤ v * v ^ (e + 1) := Nat.mul_le_mul_left _ hKe
      _ = v ^ (e + 2) := (pow_succ' v (e + 1)).symm
      _ ≤ X := vX _ (by omega)
  have hcId : Fintype.card (Nc.G.Uid (K + K) pc.U0 pc.sys.N pc.U1) ≤ X := by
    refine Nc.Dl.card_uid_le.trans ?_
    have g1 : (K + K) * (K + K) * pc.U0 ≤ v ^ (b₁ - 1) := by
      calc (K + K) * (K + K) * pc.U0 ≤ (v * K) * (v * K) * v ^ Cp :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hU0
        _ ≤ (v * v ^ (e + 1)) * (v * v ^ (e + 1)) * v ^ Cp := by gcongr
        _ = v ^ (2 * e + 4 + Cp) := by ring
        _ ≤ _ := vpow (by omega)
    have g2 : Fintype.card pc.sys.N * pc.U1 ≤ v ^ (b₁ - 1) := by
      calc _ ≤ v ^ Cp * v ^ Cp := Nat.mul_le_mul pc.outcomes_le hU1
        _ = v ^ (Cp + Cp) := (pow_add _ _ _).symm
        _ ≤ _ := vpow (by omega)
    calc _ ≤ v ^ (b₁ - 1) + v ^ (b₁ - 1) := Nat.add_le_add g1 g2
      _ ≤ v * v ^ (b₁ - 1) := by rw [← Nat.two_mul]; exact Nat.mul_le_mul_right _ (by omega)
      _ = X := by rw [hX, ← pow_succ']; congr 1; omega
  have hkind : ∀ r : pc.sys.R, ∃ t : ℕ, kinds[t]? = some ⟨pc.sys.kind r.1, r.2⟩ := fun r =>
    List.mem_iff_getElem?.1 (pc.kinds_mem r)
  choose tg htg using hkind
  have hlaw : ∀ r : pc.sys.R, Fintype.card (pc.sys.kind r.1).Ro + Fintype.card (pc.sys.kind r.1).Sl +
      Fintype.card (pc.sys.kind r.1).Cn ≤ ml := fun r => by
    rw [hml]
    exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨_, pc.kinds_mem r, rfl⟩)
  have hrole : ∀ x, Fintype.card (pc.sys.kind x).Ro = 0 → Fintype.card (pc.sys.kind x).Sl = 0 ∧
      Fintype.card (pc.sys.kind x).Cn = 0 := fun x h0 => by
    have := Fintype.card_eq_zero_iff.1 h0
    exact ⟨Fintype.card_eq_zero_iff.2 ⟨fun z => this.false ((pc.sys.kind x).a z)⟩,
      Fintype.card_eq_zero_iff.2 ⟨fun z => this.false ((pc.sys.kind x).c z)⟩⟩
  have hlaw' : ∀ x, Fintype.card (pc.sys.kind x).Ro + Fintype.card (pc.sys.kind x).Sl +
      Fintype.card (pc.sys.kind x).Cn ≤ ml := fun x => by
    rcases Nat.eq_zero_or_pos (Fintype.card (pc.sys.kind x).Ro) with h0 | h0
    · obtain ⟨h1, h2⟩ := hrole x h0
      omega
    · exact hlaw ⟨x, (Fintype.card_pos_iff.1 h0).some⟩
  have hcR : Fintype.card pc.sys.R ≤ X := by
    calc Fintype.card pc.sys.R = ∑ x, Fintype.card (pc.sys.kind x).Ro := Fintype.card_sigma
      _ ≤ ∑ _x : Fin pc.E, ml := Finset.sum_le_sum fun x _ => le_trans (by omega) (hlaw' x)
      _ = pc.E * ml := by simp
      _ ≤ v ^ Cp * v := Nat.mul_le_mul hE (by omega)
      _ = v ^ (Cp + 1) := (pow_succ v Cp).symm
      _ ≤ X := vX _ (by omega)
  have hrow : Fintype.card (Nc.Cut.RowData (K + K)) ≤ X := by
    rw [Nc.Dl.card_row]
    calc 2 * ((K + K) * (K + K)) = 8 * (K * K) := by ring
      _ ≤ v * (v ^ (e + 1) * v ^ (e + 1)) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul hKe hKe)
      _ = v ^ (2 * e + 3) := by ring
      _ ≤ X := vX _ (by omega)
  have hSX : Fintype.card (Option S) ≤ X := by
    rw [Fintype.card_option]
    omega
  -- bits
  obtain ⟨Lc, hLc⟩ : ∃ L, L = lg (X ^ 3) + lg (τ * v ^ 2) + 1 := ⟨_, rfl⟩
  have hX3Lc : X ^ 3 ≤ 2 ^ Lc := (lt_two_pow_lg _).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hTLc : T < 2 ^ Lc := by
    refine lt_of_le_of_lt ?_ (lt_of_lt_of_le (lt_two_pow_lg (τ * v ^ 2)) (Nat.pow_le_pow_right (by norm_num) (by omega)))
    calc T ≤ K * T := Nat.le_mul_of_pos_left _ hK0
      _ ≤ τ * m := hKT
      _ ≤ τ * v ^ 2 := Nat.mul_le_mul_left _ (hmv.trans (Nat.le_self_pow (by norm_num) v))
  obtain ⟨t1, t2, t3, t4⟩ := Nc.Dl.exists_bits T (L := Lc) hTLc
  obtain ⟨u1, u2, u3, u4⟩ := Nc.Dl.exists_bits pc.ub (L := Lc) (lt_of_le_of_lt pc.unit_le.1 hTLc)
  obtain ⟨l1, l2, -, -⟩ := Nc.Dl.exists_bits ℓ (L := Lc) (lt_of_le_of_lt hℓT hTLc)
  have hLcm : Lc + 1 ≤ m := by
    have h1 : lg (X ^ 3) ≤ 3 * b₁ * l := by
      rw [hX, ← pow_mul, hl, Nat.mul_comm b₁ 3]
      exact lg_pow_le (by omega)
    have h2 := lg_mul_sq_le (τ := τ) (v := v)
    rw [← hl] at h2 hlτ
    calc Lc + 1 ≤ 3 * b₁ * l + (l ^ 2 + 2 * l + 3) := by omega
      _ ≤ l * l + (l * l + l * l + l * l) := by
          have : 3 * b₁ * l ≤ l * l := Nat.mul_le_mul_right _ (by omega)
          have : 2 * l ≤ l * l := Nat.mul_le_mul_right _ (by omega)
          have : 3 ≤ l * l := le_trans (by omega : 3 ≤ l) (Nat.le_mul_self l)
          rw [pow_two]
          omega
      _ = 4 * (l * l) := by ring
      _ ≤ l * (l * l) := Nat.mul_le_mul_right _ (by omega)
      _ = l ^ 3 := by ring
      _ ≤ m := hml' 3 (by omega)
  have hX30 : 60 ≤ X := by omega
  have hX32 : ∀ n, n ≤ 60 * (X * X) → n ≤ 2 ^ Lc := by
    intro n hn
    refine hn.trans (le_trans ?_ hX3Lc)
    calc 60 * (X * X) ≤ X * (X * X) := Nat.mul_le_mul_right _ hX30
      _ = X ^ 3 := by ring
  have hXX : X ≤ X * X := Nat.le_mul_of_pos_left _ hX1
  have hN := pc.outcomes_le
  obtain ⟨Cd, hCd⟩ := Nc.Dl.exists_codes (A' := pc.A') (E := pc.E) (U0 := pc.U0) (U1 := pc.U1) (D := pc.D)
    (pS := pc.steps) (S := S) (M := pc.sys) (Lc := Lc)
    (hX32 _ ((Nc.Dl.card_nm hK2 hSX (by omega) (by omega) (by omega) hcId).trans (by omega))) (hX32 _ (by omega))
    (hX32 _ (by omega)) (hX32 _ (by
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
      have g1 : (K + K + pc.A') * Fintype.card (Nc.G.Uid (K + K) pc.U0 pc.sys.N pc.U1) ≤ X * X :=
        Nat.mul_le_mul (by omega) hcId
      have g2 : (K + K) * pc.U0 ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
      omega))
  -- the bounds of the pieces, in units
  obtain ⟨L, hL⟩ : ∃ L, L = lg v ^ Cp := ⟨_, rfl⟩
  have hLm : L ≤ m := hL ▸ hl ▸ hml' Cp (by omega)
  obtain ⟨bd, hbd⟩ : ∃ b, b = K * T * L / (pc.ub * v ^ 300) := ⟨_, rfl⟩
  obtain ⟨ev, hev⟩ : ∃ b, b = K * T * L / (pc.ub * k) := ⟨_, rfl⟩
  obtain ⟨ιb, hιb⟩ : ∃ b, b = Cp * K / k := ⟨_, rfl⟩
  have hbits : ∀ d, K * T * L / (pc.ub * d) * pc.ub * d ≤ τ * m ^ 2 := fun d => by
    rw [Nat.mul_assoc _ pc.ub d]
    refine (Nat.div_mul_le_self _ _).trans ((Nat.mul_le_mul hKT hLm).trans (le_of_eq ?_))
    ring
  have hιK : ιb * k ≤ Cp * K := hιb ▸ Nat.div_mul_le_self _ _
  have hnums : Nc.Dl.CutNums v K τ s k T ℓ pc.ub pc.load X Lc m pc.c ιb bd ev pc.num :=
    { v_pos := hv1, m_ge := by omega, m_le := hmv, k_pos := hk, kK := hkv.trans ((vpow (by norm_num)).trans hvK),
      vK := hvK, KT := hKT, ℓeq := hℓ, ub_pos := pc.ub_pos, ub_le := pc.unit_le.1.trans (Nat.le_succ T),
      lhub := by
        refine pc.unit_le.2.trans ?_
        rw [← hL, Nat.mul_comm]
        exact Nat.mul_le_mul_right _ hLm
      Lc_le := hLcm, c_le := by have := pc.c_le; omega, K_X := hKX, X_ge := hX1,
      ιb_le := hιK.trans (Nat.mul_le_mul_right _ (by omega)),
      ιbX := by
        calc ιb ≤ Cp * K := hιb ▸ Nat.div_le_self _ _
          _ ≤ v * v ^ (e + 1) := Nat.mul_le_mul (by omega) hKe
          _ = v ^ (e + 2) := (pow_succ' v (e + 1)).symm
          _ ≤ X := vX _ (by omega)
      bd_le := hbd ▸ hbits _, ev_le := hev ▸ hbits _,
      mm_le := by
        refine pc.num_le.trans ?_
        rw [← hL]
        exact Nat.mul_le_mul_left _ hLm
      mmX := by have := pc.digits.2.2.1; omega
      small := hsmall }
  have hubk : 0 < pc.ub * k := Nat.mul_pos pc.ub_pos (by omega)
  have hbdle : ∀ n o, pc.tab.valid n → (∀ x, pc.plan.good n o x) → ∀ g,
      ((pc.plan.cur n o pc.E).filter (Nc.Plus.OneIn (Nc.G.hold0 pc.sys.np) (Nc.G.hold1 pc.sys.np) (pc.grp n o) g)).card ≤
        bd := fun n o hn hg g => by
    rw [hbd, Nat.le_div_iff_mul_le (Nat.mul_pos pc.ub_pos (vpos 300)), ← Nat.mul_assoc, hL]
    exact pc.cut_le n o ((pc.tab_valid n).1 hn) hg g
  have hevle : ∀ n o, pc.tab.valid n → (∀ x, pc.plan.good n o x) → ∀ g,
      Nc.Dl.evG pc.grp n o g + Nc.Dl.pdG pc.plan pc.grp n o g ≤ ev := fun n o hn hg g => by
    rw [hev, Nat.le_div_iff_mul_le hubk, ← Nat.mul_assoc, hL]
    exact pc.all_le n o ((pc.tab_valid n).1 hn) hg g
  have hbase : ∀ n o, pc.tab.valid n → (∀ x, pc.plan.good n o x) → ∀ g,
      (univ.filter fun p : Fin (K + K) => pc.grp n o (Fin.castAdd pc.A' p) = g).card ≤ ιb := fun n o hn hg g => by
    rw [hιb, Nat.le_div_iff_mul_le (by omega)]
    exact pc.blocks_le n o ((pc.tab_valid n).1 hn) hg g
  have hnum : ∀ n o y, pc.plan.num n o y ≤ X := fun n o y => by
    have h1 := pc.tab.hnum y (n, o)
    have h2 := (pc.tab.fn (pc.tab.knum y) (n, o)).2
    simp only at h1
    omega
  -- the evaluator of this code
  obtain ⟨ci, hci⟩ : ∃ ci : Fin (Cp + 1), ci.1 = pc.c := ⟨⟨pc.c, Nat.lt_succ_of_le pc.c_le⟩, rfl⟩
  obtain ⟨cb, hcb⟩ : ∃ cb : Option Γ → Fin ci.1 → Bool, cb = fun z j => pc.cb z (Fin.cast hci j) := ⟨_, rfl⟩
  obtain ⟨GROUP, κ', hG, hGtime, hsize⟩ : ∃ (GROUP : Fm) (κ' : ℕ),
      Nc.Dl.GroupOK θ mu pc.cb kinds (fun z => (Nc.Grp.qn Q z : ℕ)) GROUP κ' ∧
      Nc.Dl.GrpTimeOK (S := S) A pc.cb (fun z => (Nc.Grp.qn Q z : ℕ)) ∧ GROUP.code.size + κ' ≤ Zg := by
    obtain ⟨cn, hcn⟩ := ci
    simp only at hci
    subst hci
    refine ⟨GR ⟨pc.c, hcn⟩ pc.cb, κ ⟨pc.c, hcn⟩ pc.cb, hGR ⟨pc.c, hcn⟩ pc.cb, hGT ⟨pc.c, hcn⟩ pc.cb, ?_⟩
    rw [hZg]
    exact le_trans (Finset.single_le_sum (f := fun cb => (GR ⟨pc.c, hcn⟩ cb).code.size + κ ⟨pc.c, hcn⟩ cb)
      (fun _ _ => Nat.zero_le _) (mem_univ pc.cb))
      (Finset.single_le_sum (f := fun c : Fin (Cp + 1) => ∑ cb : Option Γ → Fin c.1 → Bool,
        ((GR c cb).code.size + κ c cb)) (fun _ _ => Nat.zero_le _) (mem_univ (⟨pc.c, hcn⟩ : Fin (Cp + 1))))
  -- the program G
  have : Nonempty Q := ⟨i⟩
  obtain ⟨G, hGs, hcut⟩ := thm_onecut_program (θ := θ) (mu := mu) (i := i) (e := e') (b0 := b0) (b1 := b1) (τ := τ) (s := s)
    (X := X) (Lc := Lc) (bT := (Nc.Dl.bitsN Lc T).reverse) (bub := (Nc.Dl.bitsN Lc pc.ub).reverse)
    (nub := Nc.Dl.bitsN Lc pc.ub) (nl := Nc.Dl.bitsN Lc ℓ) (ℓ := ℓ) (cb := pc.cb) (bd := bd) (ιb := ιb)
    (tB := 2 * (Lc + 1) * (T + pc.ub + 2) + ιb * T + 1000 * (ev + ιb * pc.load) * (pc.ub + Lc + 1) +
      X ^ 4 * 1000 * (Lc + 1))
    hK0 hG (fun z hz hpl => by
      rw [t4]
      refine hCU τ z (K * T) hpl (le_trans ?_ hKTge)
      rw [htU]
      exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (Nat.pow_le_pow_left (lg_mono (by omega)) 2))
    htg pc.tab pc.ok (by rw [u4]; exact pc.ub_pos) (by rw [u2, u4]) l2 pc.U1_pos (by rw [t4]; exact hℓT)
    (fun z hz => by
      rw [t4, u4]
      rw [pc.value i e' (fun _ => Nc.Dl.wordG b0 b1 z) ℓ hℓT (by rw [Nc.Dl.length_wordG]; exact hz.trans hsK)]
      refine Finset.sum_congr rfl fun q _ => if_congr Iff.rfl ?_ rfl
      refine Finset.sum_congr rfl fun ρ _ => if_congr Iff.rfl ?_ rfl
      exact Finset.sum_congr rfl fun n _ => if_congr (pc.tab_valid n).symm rfl rfl)
    hbdle hbase hnum pc.digits.1 pc.digits.2.1 pc.digits.2.2.2 pc.digits.2.2.1 Cd hCd (by omega)
    t3.le u3.le u1.le l1.le hK2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hcId hSX (by omega) hrow hcR
    (fun y => le_trans (by have := hlaw' y; omega : Fintype.card (pc.sys.kind y).Sl ≤ ml) (by omega))
    (fun y => le_trans (by have := hlaw' y; omega : Fintype.card (pc.sys.kind y).Cn ≤ ml) (by omega))
    (fun q => (hcq q).trans (by omega)) (fun r => by
      have h1 := htg r
      have h2 : tg r < kinds.length := by
        by_contra hlt
        rw [List.getElem?_eq_none (not_lt.1 hlt)] at h1
        simp at h1
      omega) (by omega) hnums.mmX (by have := pc.c_le; omega) (fun q x ρ n o b g hx hn ho => by
        have := hGtime pc.plan pc.ok q x ρ n o (pc.grp n o) g Cd.key Cd.dkey tg (Nc.Dl.bitsN Lc T).reverse
          (Nc.Dl.bitsN Lc pc.ub).reverse b (Lc := Lc) (X := X) (ιb := ιb) (lh := pc.load) (ev := ev) hx hCd.key hCd.dkey
          t3.le u3.le hSX hK2 hcR hcId (fun y => by have := hlaw' y; omega) (fun y => by have := hlaw' y; omega)
          (hbase n o hn ho g) hnums.ιbX (fun p _ => (pc.tab_valid n).1 hn p) (hevle n o hn ho g)
        refine this.trans (le_of_eq ?_)
        rw [t4, u4])
  have hm10 : lg v ^ (10 * C1) = m ^ 10 := by rw [← hl, hm, ← pow_mul, Nat.mul_comm]
  refine ⟨G, ?_, ?_⟩
  · calc G.size ≤ (Nc.Dl.dealC + 3000) * (X * Lc) ^ 4 := hGs
      _ ≤ v * (X * v) ^ 4 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) 4)
      _ = v ^ ((b₁ + 1) * 4 + 1) := by rw [hX, ← pow_succ, ← pow_mul, ← pow_succ']
      _ ≤ v ^ (a + e + 6 * b₁ + 400) := vpow (by omega)
  · rw [hm10]
    rw [u4] at hcut
    refine hcut.mono (hnums.time (by omega)) hnums.size
      (hnums.mm_le.trans (Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) m))) hnums.deal

end Paper
end

theorem solution {A : Type} [CommRing A] [Algebra.FiniteType ℤ A] {h : ℕ} [NeZero h]
    (VL : Nc.Tow.VLaws A (Nc.Vp.cNear (h := h)) (Nc.Vp.dNear (h := h)) 1 (2 ^ Nc.Tower.ee h))
    (h3 : 3 ≤ h) (hgain : 1 + 8 * VL.C₁ ≤ (h : ℝ) / 4) :
    ∃ θ : List Bool → A, (Function.support θ).Finite ∧ NS1.LocalCuts θ := by
  obtain ⟨θ,hθ⟩ := Paper.exists_generates A
  exact ⟨θ,hθ.1,Paper.thm_onecut hθ VL h3 hgain⟩

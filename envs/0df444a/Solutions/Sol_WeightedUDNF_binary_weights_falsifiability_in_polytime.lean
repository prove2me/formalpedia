-- Prove2me | solution 1 for WeightedUDNF.binary_weights_falsifiability_in_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-10-20T00:09:30.864151+00:00
-- url     : https://prove2.me/submissions/9f86c96a-4087-462d-bd30-a6aec4c95e55

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Convert
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.GCongr
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_WeightedUDNF
import Mathlib.Data.List.GetD

/- Weighted falsifiability of unambiguous DNFs: a uniform polynomial-time TM2.
The StackCode compiler and Gaussian algebra below are adapted from openai/math
commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a, licensed Apache-2.0.
Original source: https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Computability
License: https://www.apache.org/licenses/LICENSE-2.0
-/


/- OAI.Computability.MatchingCount.FiniteStack -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode

abbrev Store (r : ℕ) := Fin r → List Bool

inductive Instr (r : ℕ) (L : Type)
  | go : L → Instr r L
  | push : Fin r → Bool → L → Instr r L
  | pop : Fin r → L → Instr r L
  | branch : Fin r → L → L → L → Instr r L

namespace Instr
variable {r : ℕ} {L L' : Type}

def map (f : L → L') : Instr r L → Instr r L'
  | .go q => .go (f q)
  | .push k b q => .push k b (f q)
  | .pop k q => .pop k (f q)
  | .branch k e z o => .branch k (f e) (f z) (f o)

def eval : Instr r L → Store r → L × Store r
  | .go q,s => (q,s)
  | .push k b q,s => (q,Function.update s k (b::s k))
  | .pop k q,s => (q,Function.update s k (s k).tail)
  | .branch k e z o,s => ((s k).head?.elim e (fun b => if b then o else z),s)

@[simp] theorem eval_map (f : L → L') (i : Instr r L) (s : Store r) :
    (i.map f).eval s = (f (i.eval s).1,(i.eval s).2) := by
  cases i <;> simp only [map,eval]
  rename_i k e z o
  cases h : (s k).head? with
  | none => rfl
  | some b => cases b <;> rfl

abbrev Stmt (r : ℕ) (L : Type) := Turing.TM2.Stmt (fun _ : Fin r => Bool) L (Option Bool)

def target (q : Option L) : Stmt r L :=
  .load (fun _ => none) (q.elim .halt (fun l => .goto (fun _ => l)))

def translate : Instr r (Option L) → Stmt r L
  | .go q => target q
  | .push k b q => .push k (fun _ => b) (target q)
  | .pop k q => .pop k (fun _ _ => none) (target q)
  | .branch k e z o => .peek k (fun _ h => h)
      (.branch Option.isNone (target e) (.branch (fun h => h.getD false) (target o) (target z)))

@[simp] theorem target_step (q : Option L) (v : Option Bool) (s : Store r) :
    Turing.TM2.stepAux (target q) v s = ⟨q,none,s⟩ := by cases q <;> rfl

@[simp] theorem translate_step (i : Instr r (Option L)) (v : Option Bool) (s : Store r) :
    Turing.TM2.stepAux i.translate v s = ⟨(i.eval s).1,none,(i.eval s).2⟩ := by
  cases i with
  | go q => exact target_step q v s
  | push k b q => simp only [translate,Turing.TM2.stepAux,target_step,eval]
  | pop k q => simp only [translate,Turing.TM2.stepAux,target_step,eval]
  | branch k e z o =>
    simp only [translate,Turing.TM2.stepAux,target_step,eval]
    cases h : (s k).head? with
    | none => rfl
    | some b => cases b <;> rfl
end Instr

structure Block (r : ℕ) where
  Label : Type
  finite : Fintype Label
  entry : Label
  code : Label → Instr r (Option Label)

attribute [instance] Block.finite

inductive Steps {r : ℕ} {L : Type} (code : L → Instr r (Option L)) :
    Option L → Store r → Option L → Store r → ℕ → Prop
  | refl (q s) : Steps code q s q s 0
  | next (q s q' s' t)
      (rest : Steps code ((code q).eval s).1 ((code q).eval s).2 q' s' t) :
      Steps code (some q) s q' s' (t+1)

namespace Steps
variable {r : ℕ} {L L' : Type} {code : L → Instr r (Option L)}

theorem trans {q s q' s' q'' s'' t u}
    (h : Steps code q s q' s' t) (h' : Steps code q' s' q'' s'' u) :
    Steps code q s q'' s'' (t+u) := by
  induction h with
  | refl => simpa using h'
  | next q s q' s' t h ih => simpa [Nat.add_right_comm] using Steps.next q s _ _ _ (ih h')

theorem map (code' : L' → Instr r (Option L')) (f : L → L') (last : Option L')
    (hcode : ∀ l, code' (f l)=(code l).map (fun q => q.elim last (some ∘ f)))
    {q s q' s' t} (h : Steps code q s q' s' t) :
    Steps code' (q.elim last (some ∘ f)) s (q'.elim last (some ∘ f)) s' t := by
  induction h with
  | refl => exact .refl _ _
  | next q s q' s' t h ih =>
    apply Steps.next
    simpa only [hcode,Instr.eval_map] using ih

abbrev cfg (q : Option L) (s : Store r) :
    Turing.TM2.Cfg (fun _ : Fin r => Bool) L (Option Bool) := ⟨q,none,s⟩

theorem simulation {q s q' s' t} (h : Steps code q s q' s' t) :
    (fun o => o.bind (Turing.TM2.step (fun l => (code l).translate)))^[t]
      (some (cfg q s)) = some (cfg q' s') := by
  induction h with
  | refl => rfl
  | next q s q' s' t h ih =>
    rw [Function.iterate_succ_apply]
    simpa only [Option.bind_some,Turing.TM2.step,Instr.translate_step] using ih
end Steps

namespace Block
variable {r : ℕ}

def primitive (i : Instr r Unit) : Block r where
  Label := Unit
  finite := inferInstance
  entry := ()
  code _ := i.map (fun _ => none)

def seq (a b : Block r) : Block r where
  Label := a.Label ⊕ b.Label
  finite := inferInstance
  entry := .inl a.entry
  code := fun l => match l with
    | .inl q => (a.code q).map (fun t => t.elim (some (.inr b.entry)) (fun u => some (.inl u)))
    | .inr q => (b.code q).map (Option.map Sum.inr)

def cases (k : Fin r) (e z o : Block r) : Block r where
  Label := Unit ⊕ (e.Label ⊕ (z.Label ⊕ o.Label))
  finite := inferInstance
  entry := .inl ()
  code := fun l => match l with
    | .inl _ => .branch k (some (.inr (.inl e.entry)))
        (some (.inr (.inr (.inl z.entry)))) (some (.inr (.inr (.inr o.entry))))
    | .inr (.inl q) => (e.code q).map (Option.map (Sum.inr ∘ Sum.inl))
    | .inr (.inr (.inl q)) => (z.code q).map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inl))
    | .inr (.inr (.inr q)) => (o.code q).map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inr))

def loop (k : Fin r) (b : Block r) : Block r where
  Label := Unit ⊕ b.Label
  finite := inferInstance
  entry := .inl ()
  code := fun l => match l with
    | .inl _ => .branch k none (some (.inr b.entry)) (some (.inr b.entry))
    | .inr q => (b.code q).map (fun t => t.elim (some (.inl ())) (fun u => some (.inr u)))

abbrev Runs (b : Block r) (s s' : Store r) (t : ℕ) : Prop :=
  Steps b.code (some b.entry) s none s' t

theorem primitive_runs (i : Instr r Unit) (s : Store r) :
    (primitive i).Runs s (i.eval s).2 1 := by
  apply Steps.next
  simp only [primitive,Instr.eval_map]
  exact .refl _ _

theorem seq_runs (a b : Block r) {s s' s'' : Store r} {t u : ℕ}
    (ha : a.Runs s s' t) (hb : b.Runs s' s'' u) : (a.seq b).Runs s s'' (t+u) := by
  have h₁ := ha.map (a.seq b).code Sum.inl (some (Sum.inr b.entry)) (fun _ => rfl)
  have h₂ := hb.map (a.seq b).code Sum.inr none (by
    intro l
    change (b.code l).map _ = (b.code l).map _
    congr 1
    funext t
    cases t <;> rfl)
  exact h₁.trans h₂

def machine (b : Block r) (input output : Fin r) : Turing.FinTM2 where
  K := Fin r
  k₀ := input
  k₁ := output
  Γ _ := Bool
  Λ := b.Label
  main := b.entry
  σ := Option Bool
  initialState := none
  m l := (b.code l).translate

theorem machine_finite (b : Block r) (input output : Fin r) (k : (b.machine input output).K) :
    Finite ((b.machine input output).Γ k) := by
  change Finite Bool
  infer_instance

def machine_runs (b : Block r) (input output : Fin r) (s s' : List Bool) {t : ℕ}
    (h : b.Runs (Function.update (fun _ => []) input s)
      (Function.update (fun _ => []) output s') t) :
    Turing.TM2OutputsInTime (b.machine input output) s (some s') t := by
  refine ⟨⟨t,?_⟩,le_rfl⟩
  have hini : Turing.initList (b.machine input output) s =
      Steps.cfg (some b.entry) (Function.update (fun _ => []) input s) := by
    simp only [Turing.initList,machine,Steps.cfg]
    congr 1
    funext k
    by_cases hk : k=input
    · subst k; rfl
    · simp [Function.update,hk]
  have hout : Turing.haltList (b.machine input output) s' =
      Steps.cfg none (Function.update (fun _ => []) output s') := by
    simp only [Turing.haltList,machine,Steps.cfg]
    congr 1
    funext k
    by_cases hk : k=output
    · subst k; rfl
    · simp [Function.update,hk]
  change (fun o => o.bind (Turing.TM2.step (fun l => (b.code l).translate)))^[t]
    (some (Turing.initList (b.machine input output) s)) =
    some (Turing.haltList (b.machine input output) s')
  rw [hini,hout]
  exact h.simulation
end Block
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.StackMacros -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
namespace Block
variable {r : ℕ}

private theorem option_map_elim {α β : Type} (f : α → β) :
    Option.map f = fun q => q.elim none (some ∘ f) := by funext q; cases q <;> rfl

theorem cases_runs_empty (k : Fin r) (e z o : Block r) {s s' : Store r} {t : ℕ}
    (hs : s k=[]) (he : e.Runs s s' t) : (cases k e z o).Runs s s' (t+1) := by
  apply Steps.next
  have h := he.map (cases k e z o).code (Sum.inr ∘ Sum.inl) none (by
    intro l
    change (e.code l).map _ = (e.code l).map _
    rw [option_map_elim]; rfl)
  simpa only [cases,Instr.eval,hs,List.head?_nil,Option.elim_none,Option.elim_some,
    Function.comp_apply] using h

theorem cases_runs_false (k : Fin r) (e z o : Block r) {s s' : Store r} {t : ℕ}
    (hs : (s k).head?=some false) (hz : z.Runs s s' t) : (cases k e z o).Runs s s' (t+1) := by
  apply Steps.next
  have h := hz.map (cases k e z o).code (Sum.inr ∘ Sum.inr ∘ Sum.inl) none (by
    intro l
    change (z.code l).map _ = (z.code l).map _
    rw [option_map_elim]; rfl)
  simpa only [cases,Instr.eval,hs,Option.elim_none,Option.elim_some,
    Function.comp_apply,Bool.false_eq_true,ite_false] using h

theorem cases_runs_true (k : Fin r) (e z o : Block r) {s s' : Store r} {t : ℕ}
    (hs : (s k).head?=some true) (ho : o.Runs s s' t) : (cases k e z o).Runs s s' (t+1) := by
  apply Steps.next
  have h := ho.map (cases k e z o).code (Sum.inr ∘ Sum.inr ∘ Sum.inr) none (by
    intro l
    change (o.code l).map _ = (o.code l).map _
    rw [option_map_elim]; rfl)
  simpa only [cases,Instr.eval,hs,Option.elim_none,Option.elim_some,
    Function.comp_apply,ite_true] using h

theorem loop_runs_empty (k : Fin r) (b : Block r) (s : Store r) (hs : s k=[]) :
    (loop k b).Runs s s 1 := by
  apply Steps.next
  simp only [loop,Instr.eval,hs,List.head?_nil,Option.elim_none]
  exact .refl _ _

theorem loop_runs_step (k : Fin r) (b : Block r) {s s' s'' : Store r} {t u : ℕ}
    (hs : s k≠[]) (hb : b.Runs s s' t) (hl : (loop k b).Runs s' s'' u) :
    (loop k b).Runs s s'' (t+u+1) := by
  apply Steps.next
  have h := hb.map (loop k b).code Sum.inr (some (Sum.inl ())) (fun _ => rfl)
  have hh := h.trans hl
  cases he : s k with
  | nil => exact (hs he).elim
  | cons a l =>
    cases a <;> simpa only [loop,Instr.eval,he,List.head?_cons,Option.elim_none,
      Option.elim_some,Function.comp_apply,Bool.false_eq_true,ite_false,ite_true] using hh

def skip : Block r := primitive (.go ())
def push (k : Fin r) (b : Bool) : Block r := primitive (.push k b ())
def pop (k : Fin r) : Block r := primitive (.pop k ())

theorem skip_runs (s : Store r) : skip.Runs s s 1 := primitive_runs _ s

theorem push_runs (k : Fin r) (b : Bool) (s : Store r) :
    (push k b).Runs s (Function.update s k (b::s k)) 1 := primitive_runs _ s

theorem pop_runs (k : Fin r) (s : Store r) :
    (pop k).Runs s (Function.update s k (s k).tail) 1 := primitive_runs _ s

def clear (k : Fin r) : Block r := loop k (pop k)

theorem clear_runs (k : Fin r) (s : Store r) :
    (clear k).Runs s (Function.update s k []) (2*(s k).length+1) := by
  generalize hl : s k=l
  induction l generalizing s with
  | nil =>
    have he : Function.update s k []=s := by rw [←hl,Function.update_eq_self]
    rw [he]
    exact loop_runs_empty k (pop k) s hl
  | cons a l ih =>
    let s' := Function.update s k l
    have hi := ih s' (by simp [s'])
    have hp : (pop k).Runs s s' 1 := by simpa [s',hl] using pop_runs k s
    have hx := loop_runs_step k (pop k) (by simp [hl]) hp hi
    have ht : 1+(2*l.length+1)+1=2*(a::l).length+1 := by simp only [List.length_cons]; omega
    rw [ht] at hx
    simpa only [clear,s',Function.update_idem] using hx

def moveBody (src dst : Fin r) : Block r :=
  cases src skip ((pop src).seq (push dst false)) ((pop src).seq (push dst true))

def reverseInto (src dst : Fin r) : Block r := loop src (moveBody src dst)

theorem moveBody_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) (a : Bool) (l : List Bool)
    (hs : s src=a::l) :
    (moveBody src dst).Runs s (Function.update (Function.update s src l) dst (a::s dst)) 3 := by
  have hp : (pop src).Runs s (Function.update s src l) 1 := by
    simpa only [hs,List.tail_cons] using pop_runs src s
  have ht := push_runs dst a (Function.update s src l)
  rw [Function.update_of_ne hne.symm] at ht
  have hseq : ((pop src).seq (push dst a)).Runs s
      (Function.update (Function.update s src l) dst (a::s dst)) 2 := by
    exact seq_runs _ _ hp ht
  cases a with
  | false => exact cases_runs_false _ _ _ _ (by simp [hs]) hseq
  | true => exact cases_runs_true _ _ _ _ (by simp [hs]) hseq

theorem reverseInto_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) :
    (reverseInto src dst).Runs s
      (Function.update (Function.update s src []) dst ((s src).reverse++s dst))
      (4*(s src).length+1) := by
  generalize hl : s src=l
  induction l generalizing s with
  | nil =>
    have he : Function.update (Function.update s src []) dst ([].reverse++s dst)=s := by
      rw [←hl,Function.update_eq_self]
      simp [hl]
    rw [he]
    exact loop_runs_empty src (moveBody src dst) s hl
  | cons a l ih =>
    let s' := Function.update (Function.update s src l) dst (a::s dst)
    have hs' : s' src=l := by simp [s',hne]
    have hi := ih s' hs'
    have hm := moveBody_runs src dst hne s a l hl
    have hx := loop_runs_step src (moveBody src dst) (by simp [hl]) hm hi
    have he : Function.update (Function.update s' src []) dst (l.reverse++s' dst)=
        Function.update (Function.update s src []) dst ((a::l).reverse++s dst) := by
      funext k
      by_cases hk : k=dst
      · subst k; simp [List.reverse_cons,List.append_assoc,s']
      · by_cases hks : k=src
        · subst k; simp [hne,s']
        · simp [Function.update_of_ne,hk,hks,s']
    rw [he] at hx
    have ht : 3+(4*l.length+1)+1=4*(a::l).length+1 := by simp only [List.length_cons]; omega
    rw [ht] at hx
    exact hx

end Block
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.StackCopy -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode.Block
variable {r : ℕ}

def moveTwoBody (src dst aux : Fin r) : Block r :=
  cases src skip
    ((pop src).seq ((push dst false).seq (push aux false)))
    ((pop src).seq ((push dst true).seq (push aux true)))

def reverseIntoTwo (src dst aux : Fin r) : Block r := loop src (moveTwoBody src dst aux)

lemma moveTwoBody_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (a : Bool) (l : List Bool) (hs : s src=a::l) :
    (moveTwoBody src dst aux).Runs s
      (Function.update (Function.update (Function.update s src l) dst (a::s dst)) aux (a::s aux)) 4 := by
  have hp : (pop src).Runs s (Function.update s src l) 1 := by
    simpa only [hs,List.tail_cons] using pop_runs src s
  have hd := push_runs dst a (Function.update s src l)
  rw [Function.update_of_ne hsd.symm] at hd
  have ha := push_runs aux a (Function.update (Function.update s src l) dst (a::s dst))
  rw [Function.update_of_ne hda.symm,Function.update_of_ne hsa.symm] at ha
  have hseq : ((pop src).seq ((push dst a).seq (push aux a))).Runs s
      (Function.update (Function.update (Function.update s src l) dst (a::s dst)) aux (a::s aux)) 3 :=
    seq_runs _ _ hp (seq_runs _ _ hd ha)
  cases a with
  | false => exact cases_runs_false _ _ _ _ (by simp [hs]) hseq
  | true => exact cases_runs_true _ _ _ _ (by simp [hs]) hseq

lemma reverseIntoTwo_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) :
    (reverseIntoTwo src dst aux).Runs s
      (Function.update (Function.update (Function.update s src []) dst ((s src).reverse++s dst))
        aux ((s src).reverse++s aux)) (5*(s src).length+1) := by
  generalize hl : s src=l
  induction l generalizing s with
  | nil =>
    have he : Function.update (Function.update (Function.update s src []) dst ([].reverse++s dst))
        aux ([].reverse++s aux)=s := by
      rw [←hl,Function.update_eq_self]
      simp only [hl,List.reverse_nil,List.nil_append,Function.update_eq_self]
    rw [he]
    exact loop_runs_empty src (moveTwoBody src dst aux) s hl
  | cons a l ih =>
    let s' := Function.update (Function.update (Function.update s src l) dst (a::s dst)) aux (a::s aux)
    have hs' : s' src=l := by simp [s',hsd,hsa]
    have hi := ih s' hs'
    have hm := moveTwoBody_runs src dst aux hsd hsa hda s a l hl
    have hx := loop_runs_step src (moveTwoBody src dst aux) (by simp [hl]) hm hi
    have he : Function.update (Function.update (Function.update s' src []) dst (l.reverse++s' dst))
        aux (l.reverse++s' aux)=
        Function.update (Function.update (Function.update s src []) dst ((a::l).reverse++s dst))
          aux ((a::l).reverse++s aux) := by
      funext k
      by_cases hka : k=aux
      · subst k; simp [List.reverse_cons,List.append_assoc,s']
      · by_cases hkd : k=dst
        · subst k; simp [hda,List.reverse_cons,List.append_assoc,s']
        · by_cases hks : k=src
          · subst k; simp [hsd,hsa,s']
          · simp [Function.update_of_ne,hka,hkd,hks,s']
    rw [he] at hx
    have ht : 4+(5*l.length+1)+1=5*(a::l).length+1 := by simp only [List.length_cons]; omega
    rw [ht] at hx
    exact hx

def copy (src dst aux : Fin r) : Block r :=
  (clear dst).seq ((reverseInto src aux).seq (reverseIntoTwo aux src dst))

lemma copy_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (ha : s aux=[]) :
    (copy src dst aux).Runs s (Function.update s dst (s src))
      (2*(s dst).length+9*(s src).length+3) := by
  let s₁ := Function.update s dst []
  let s₂ := Function.update (Function.update s₁ src []) aux ((s₁ src).reverse++s₁ aux)
  have h₁ := clear_runs dst s
  have h₂ := reverseInto_runs src aux hsa s₁
  have h₃ := reverseIntoTwo_runs aux src dst hsa.symm hda.symm hsd s₂
  have he : Function.update
      (Function.update (Function.update s₂ aux []) src ((s₂ aux).reverse++s₂ src))
        dst ((s₂ aux).reverse++s₂ dst)=Function.update s dst (s src) := by
    funext k
    by_cases hkd : k=dst
    · subst k; simp [s₂,s₁,hsd,hsa,hda,hsd.symm,hda.symm,ha]
    · by_cases hks : k=src
      · subst k; simp [s₂,s₁,hsd,hsa,hda,hsd.symm,hda.symm,ha]
      · by_cases hka : k=aux
        · subst k; simp [s₂,s₁,hsd,hsa,hda,ha,Ne.symm]
        · simp [s₂,s₁,Function.update_of_ne,hkd,hks,hka]
  rw [he] at h₃
  have hh := seq_runs (clear dst) _ h₁ (seq_runs _ _ h₂ h₃)
  change (copy src dst aux).Runs s (Function.update s dst (s src)) _ at hh
  have hlen₁ : (s₁ src).length=(s src).length := by simp [s₁,hsd]
  have hlen₂ : (s₂ aux).length=(s src).length := by simp [s₂,s₁,hsd,hda.symm,ha]
  rw [hlen₁,hlen₂] at hh
  have ht : (2*(s dst).length+1)+(4*(s src).length+1+(5*(s src).length+1))=
      2*(s dst).length+9*(s src).length+3 := by omega
  rw [ht] at hh
  exact hh

end BinaryMatching.StackCode.Block
end

end OAI

/- OAI.Computability.MatchingCount.StackEmbed -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode

noncomputable def liftStore {r R : ℕ} (f : Fin r → Fin R) (s : Store r) (base : Store R) : Store R :=
  fun k => if h : ∃ i,f i=k then s h.choose else base k

lemma liftStore_at {r R : ℕ} (f : Fin r → Fin R) (hf : Function.Injective f)
    (s : Store r) (base : Store R) (i : Fin r) : liftStore f s base (f i)=s i := by
  classical
  unfold liftStore
  have h : ∃ j,f j=f i := ⟨i,rfl⟩
  rw [dif_pos h]
  rw [hf h.choose_spec]

lemma liftStore_outside {r R : ℕ} (f : Fin r → Fin R) (s : Store r) (base : Store R)
    (k : Fin R) (hk : ∀ i,f i≠k) : liftStore f s base k=base k := by
  classical
  exact dif_neg (by simpa only [not_exists] using hk)

lemma liftStore_update {r R : ℕ} (f : Fin r → Fin R) (hf : Function.Injective f)
    (s : Store r) (base : Store R) (i : Fin r) (v : List Bool) :
    liftStore f (Function.update s i v) base=Function.update (liftStore f s base) (f i) v := by
  classical
  funext k
  by_cases hk : ∃ j,f j=k
  · obtain ⟨j,rfl⟩ := hk
    rw [liftStore_at f hf]
    by_cases hji : j=i
    · subst j; simp
    · rw [Function.update_of_ne hji,Function.update_of_ne (fun h => hji (hf h)),liftStore_at f hf]
  · have ho : ∀ j,f j≠k := by simpa only [not_exists] using hk
    rw [liftStore_outside f _ base k ho,Function.update_of_ne (ho i).symm,
      liftStore_outside f _ base k ho]

lemma liftStore_eq {r R : ℕ} (f : Fin r → Fin R) (s : Store r) (base : Store R)
    (h : ∀ i,base (f i)=s i) : liftStore f s base=base := by
  classical
  funext k
  unfold liftStore
  split_ifs with hk
  · rw [←h, hk.choose_spec]
  · rfl

namespace Instr
variable {r R : ℕ} {L : Type}

def rename (f : Fin r → Fin R) : Instr r L → Instr R L
  | .go q => .go q
  | .push k b q => .push (f k) b q
  | .pop k q => .pop (f k) q
  | .branch k e z o => .branch (f k) e z o

lemma eval_rename (f : Fin r → Fin R) (hf : Function.Injective f) (i : Instr r L)
    (s : Store r) (base : Store R) :
    (i.rename f).eval (liftStore f s base)=((i.eval s).1,liftStore f (i.eval s).2 base) := by
  cases i with
  | go q => rfl
  | push k b q => simp only [rename,eval,liftStore_at f hf,liftStore_update f hf]
  | pop k q => simp only [rename,eval,liftStore_at f hf,liftStore_update f hf]
  | branch k e z o => simp only [rename,eval,liftStore_at f hf]
end Instr

namespace Steps
variable {r R : ℕ} {L : Type} {code : L → Instr r (Option L)}

lemma rename (f : Fin r → Fin R) (hf : Function.Injective f) (base : Store R)
    {q s q' s' t} (h : Steps code q s q' s' t) :
    Steps (fun l => (code l).rename f) q (liftStore f s base) q' (liftStore f s' base) t := by
  induction h with
  | refl => exact .refl _ _
  | next q s q' s' t h ih =>
    apply Steps.next
    simpa only [Instr.eval_rename f hf] using ih
end Steps

namespace Block
variable {r R : ℕ}

def rename (b : Block r) (f : Fin r → Fin R) : Block R where
  Label := b.Label
  finite := b.finite
  entry := b.entry
  code l := (b.code l).rename f

lemma rename_runs (b : Block r) (f : Fin r → Fin R) (hf : Function.Injective f)
    (base : Store R) {s s' : Store r} {t : ℕ} (h : b.Runs s s' t) :
    (b.rename f).Runs (liftStore f s base) (liftStore f s' base) t := h.rename f hf base

end Block
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.StackRoutine -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Finset Polynomial

lemma polynomial_eval_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  simp only [Polynomial.eval_eq_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i)

def volume {r : ℕ} (s : Store r) : ℕ := ∑ i,(s i).length

lemma volume_update {r : ℕ} (s : Store r) (k : Fin r) (v : List Bool) :
    volume (Function.update s k v)+(s k).length=volume s+v.length := by
  classical
  simp only [volume]
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ k),
    ←Finset.sum_erase_add (Finset.univ) (fun i => (s i).length) (Finset.mem_univ k)]
  simp only [Function.update_self]
  have he : ∑ i∈Finset.univ.erase k,(Function.update s k v i).length =
      ∑ i∈Finset.univ.erase k,(s i).length := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [he]
  omega

lemma volume_instruction {r : ℕ} {L : Type} (i : Instr r L) (s : Store r) :
    volume (i.eval s).2≤volume s+1 := by
  cases i with
  | go q => exact Nat.le_succ _
  | push k b q =>
    have h := volume_update s k (b::s k)
    simp only [Instr.eval,List.length_cons] at *
    omega
  | pop k q =>
    have h := volume_update s k (s k).tail
    have hh : (s k).tail.length≤(s k).length := by simp
    simp only [Instr.eval] at *
    omega
  | branch k e z o => exact Nat.le_succ _

lemma Steps.volume_bound {r : ℕ} {L : Type} {code : L → Instr r (Option L)}
    {q s q' s' t} (h : Steps code q s q' s' t) : volume s'≤volume s+t := by
  induction h with
  | refl => exact le_rfl
  | next q s q' s' t h ih =>
    have he := volume_instruction (code q) s
    omega

lemma volume_single {r : ℕ} (k : Fin r) (s : List Bool) :
    volume (Function.update (fun _ => []) k s)=s.length := by
  classical
  unfold volume
  rw [Finset.sum_eq_single k]
  · simp
  · intro i hi hik
    simp [Function.update_of_ne hik]
  · simp

structure Routine {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  scratch : ℕ
  block : Block (scratch+1)
  time : Polynomial ℕ
  correct : ∀ a, ∃ t≤time.eval (ea a).length,
    block.Runs (Function.update (fun _ => []) 0 (ea a))
      (Function.update (fun _ => []) 0 (eb (f a))) t

namespace Routine
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
  {ec : γ → List Bool} {f : α → β} {g : β → γ}

lemma length_bound (p : Routine ea eb f) (a : α) :
    (eb (f a)).length≤(ea a).length+p.time.eval (ea a).length := by
  obtain ⟨t,ht,h⟩ := p.correct a
  have hv := h.volume_bound
  simp only [volume_single] at hv
  omega

private def embedding (r s : ℕ) : Fin (r+1) → Fin (r+s+1) :=
  Fin.castLE (by omega)

private lemma embedding_injective (r s : ℕ) : Function.Injective (embedding r s) := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin (r+s+1) => x.val) h)

private lemma embedding_zero (r s : ℕ) : embedding r s 0=0 := rfl

lemma lift_initial {r R : ℕ} (hR : 0<R) (f : Fin (r+1) → Fin R) (hf : Function.Injective f)
    (hz : f 0=⟨0,hR⟩) (v : List Bool) :
    liftStore f (Function.update (fun _ => []) 0 v) (fun _ => [])=
      Function.update (fun _ => []) ⟨0,hR⟩ v := by
  rw [liftStore_update f hf,hz]
  congr 1
  exact liftStore_eq f _ _ (fun _ => rfl)

noncomputable def comp (p : Routine ea eb f) (q : Routine eb ec g) : Routine ea ec (g ∘ f) where
  scratch := p.scratch+q.scratch
  block := (p.block.rename (embedding p.scratch q.scratch)).seq
    (q.block.rename (fun i => ⟨i.val,by have := i.isLt; omega⟩))
  time := p.time+q.time.comp (X+p.time)
  correct a := by
    obtain ⟨t,ht,hp⟩ := p.correct a
    obtain ⟨u,hu,hq⟩ := q.correct (f a)
    let f₁ := embedding p.scratch q.scratch
    let f₂ : Fin (q.scratch+1) → Fin (p.scratch+q.scratch+1) :=
      fun i => ⟨i.val,by have := i.isLt; omega⟩
    have hf₁ : Function.Injective f₁ := embedding_injective _ _
    have hf₂ : Function.Injective f₂ := by
      intro i j h
      exact Fin.ext (congrArg (fun x : Fin (p.scratch+q.scratch+1) => x.val) h)
    have hm₁ := p.block.rename_runs f₁ hf₁ (fun _ => []) hp
    have hm₂ := q.block.rename_runs f₂ hf₂ (fun _ => []) hq
    rw [lift_initial (by omega) f₁ hf₁ rfl,lift_initial (by omega) f₁ hf₁ rfl] at hm₁
    rw [lift_initial (by omega) f₂ hf₂ rfl,lift_initial (by omega) f₂ hf₂ rfl] at hm₂
    refine ⟨t+u,?_,Block.seq_runs _ _ hm₁ hm₂⟩
    simp only [Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_X]
    exact Nat.add_le_add ht (hu.trans (polynomial_eval_mono q.time (p.length_bound a)))

noncomputable def machine (p : Routine ea eb f) : Turing.TM2ComputableInPolyTime ea eb f where
  tm := p.block.machine 0 0
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := p.time
  outputsFun a := by
    let t := (p.correct a).choose
    have ht := (p.correct a).choose_spec.1
    have h := (p.correct a).choose_spec.2
    have hm := p.block.machine_runs 0 0 (ea a) (eb (f a)) h
    change Turing.TM2OutputsInTime (p.block.machine 0 0) (List.map id (ea a))
      (some (List.map id (eb (f a)))) (p.time.eval (ea a).length)
    rw [List.map_id_fun,List.map_id_fun]
    exact ⟨hm.toEvalsTo,hm.steps_le_m.trans ht⟩

lemma machine_alphabets_finite (p : Routine ea eb f) (k : p.machine.tm.K) :
    Finite (p.machine.tm.Γ k) := by
  change Finite Bool
  infer_instance

end Routine
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.StackPair -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode

def pairBits : List Bool → List Bool → List Bool
  | [],y => true::y
  | b::x,y => false::b::pairBits x y

@[simp] lemma pairBits_length (x y : List Bool) : (pairBits x y).length=2*x.length+y.length+1 := by
  induction x with
  | nil => simp [pairBits]
  | cons b x ih => simp only [pairBits,List.length_cons,ih]; omega

namespace Block
variable {r : ℕ}

def tagBody (src dst : Fin r) : Block r :=
  cases src skip ((pop src).seq ((push dst false).seq (push dst false)))
    ((pop src).seq ((push dst true).seq (push dst false)))

def tagAll (src dst : Fin r) : Block r := loop src (tagBody src dst)

lemma tagBody_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) (b : Bool) (l : List Bool)
    (hs : s src=b::l) :
    (tagBody src dst).Runs s (Function.update (Function.update s src l) dst (false::b::s dst)) 4 := by
  have hp : (pop src).Runs s (Function.update s src l) 1 := by
    simpa only [hs,List.tail_cons] using pop_runs src s
  have hb := push_runs dst b (Function.update s src l)
  rw [Function.update_of_ne hne.symm] at hb
  have hf := push_runs dst false (Function.update (Function.update s src l) dst (b::s dst))
  simp only [Function.update_self,Function.update_idem] at hf
  have hx := seq_runs _ _ hp (seq_runs _ _ hb hf)
  cases b with
  | false => exact cases_runs_false _ _ _ _ (by simp [hs]) hx
  | true => exact cases_runs_true _ _ _ _ (by simp [hs]) hx

lemma pairBits_eq (x y : List Bool) :
    pairBits x y=x.flatMap (fun b => [false,b])++true::y := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [pairBits,ih]

lemma tagAll_runs (src dst : Fin r) (hne : src≠dst) (x y : List Bool) (s : Store r)
    (hs : s src=x.reverse) (hd : s dst=y) :
    (tagAll src dst).Runs s
      (Function.update (Function.update s src []) dst (x.flatMap (fun b => [false,b])++y))
      (5*x.length+1) := by
  induction x using List.reverseRecOn generalizing y s with
  | nil =>
    have he : Function.update (Function.update s src []) dst
        ([].flatMap (fun b => [false,b])++y)=s := by
      simp only [List.reverse_nil] at hs
      simp only [List.flatMap_nil,List.nil_append]
      rw [←hs,Function.update_eq_self,←hd,Function.update_eq_self]
    rw [he]
    apply loop_runs_empty
    simpa using hs
  | append_singleton x b ih =>
    have hs' : s src=b::x.reverse := by simpa using hs
    let s' := Function.update (Function.update s src x.reverse) dst (false::b::s dst)
    have hm := tagBody_runs src dst hne s b x.reverse hs'
    have hi := ih (false::b::y) s' (by simp [s',hne]) (by simp [s',hd])
    have hx := loop_runs_step src (tagBody src dst) (by simp [hs']) hm hi
    have he : Function.update (Function.update s' src []) dst
        (x.flatMap (fun b => [false,b])++false::b::y)=
        Function.update (Function.update s src []) dst
          ((x++[b]).flatMap (fun b => [false,b])++y) := by
      funext k
      by_cases hk : k=dst
      · subst k; simp [List.flatMap_append,List.append_assoc]
      · by_cases hks : k=src
        · subst k; simp [s',hne]
        · simp [s',Function.update_of_ne,hk,hks]
    rw [he] at hx
    have ht : 4+(5*x.length+1)+1=5*(x++[b]).length+1 := by simp; omega
    rw [ht] at hx
    exact hx

def pairInto (src dst aux : Fin r) : Block r :=
  (reverseInto src aux).seq ((push dst true).seq (tagAll aux dst))

lemma pairInto_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (ha : s aux=[]) :
    (pairInto src dst aux).Runs s
      (Function.update (Function.update s src []) dst (pairBits (s src) (s dst)))
      (9*(s src).length+3) := by
  let s₁ := Function.update (Function.update s src []) aux ((s src).reverse++s aux)
  let s₂ := Function.update s₁ dst (true::s₁ dst)
  have h₁ := reverseInto_runs src aux hsa s
  have h₂ := push_runs dst true s₁
  have h₃ := tagAll_runs aux dst hda.symm (s src) (true::s dst) s₂
    (by simp [s₂,s₁,hda.symm,ha]) (by simp [s₂,s₁,hda,hsd.symm])
  rw [←pairBits_eq] at h₃
  have he : Function.update (Function.update s₂ aux []) dst (pairBits (s src) (s dst))=
      Function.update (Function.update s src []) dst (pairBits (s src) (s dst)) := by
    funext k
    by_cases hkd : k=dst
    · subst k; simp
    · by_cases hks : k=src
      · subst k; simp [s₂,s₁,hsd,hsa]
      · by_cases hka : k=aux
        · subst k; simp [s₂,s₁,ha,hda.symm,hsa.symm]
        · simp [s₂,s₁,Function.update_of_ne,hkd,hks,hka]
  rw [he] at h₃
  have hx := seq_runs _ _ h₁ (seq_runs _ _ h₂ h₃)
  have ht : (4*(s src).length+1)+(1+(5*(s src).length+1))=9*(s src).length+3 := by omega
  rw [ht] at hx
  exact hx

def moveInto (src dst aux : Fin r) : Block r :=
  (reverseInto src aux).seq (reverseInto aux dst)

lemma moveInto_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (hd : s dst=[]) (ha : s aux=[]) :
    (moveInto src dst aux).Runs s
      (Function.update (Function.update s src []) dst (s src)) (8*(s src).length+2) := by
  let s' := Function.update (Function.update s src []) aux ((s src).reverse++s aux)
  have h₁ := reverseInto_runs src aux hsa s
  have h₂ := reverseInto_runs aux dst hda.symm s'
  have he : Function.update (Function.update s' aux []) dst ((s' aux).reverse++s' dst)=
      Function.update (Function.update s src []) dst (s src) := by
    funext k
    by_cases hkd : k=dst
    · subst k; simp [s',ha,hd,hda,hsd.symm]
    · by_cases hks : k=src
      · subst k; simp [s',hsd,hsa]
      · by_cases hka : k=aux
        · subst k; simp [ha,hda.symm,hsa.symm]
        · simp [s',Function.update_of_ne,hkd,hks,hka]
  rw [he] at h₂
  have hh := seq_runs _ _ h₁ h₂
  have hl : (s' aux).length=(s src).length := by simp [s',ha]
  rw [hl] at hh
  have ht : (4*(s src).length+1)+(4*(s src).length+1)=8*(s src).length+2 := by omega
  rw [ht] at hh
  exact hh

def decodeRev (src dst : Fin r) : Block r where
  Label := Fin 7
  finite := inferInstance
  entry := 0
  code k := match k.val with
    | 0 => .branch src none (some 1) (some 6)
    | 1 => .pop src (some 2)
    | 2 => .branch src none (some 3) (some 4)
    | 3 => .push dst false (some 5)
    | 4 => .push dst true (some 5)
    | 5 => .pop src (some 0)
    | _ => .pop src none

lemma decodeRev_runs (src dst : Fin r) (hne : src≠dst) (x y : List Bool) (s : Store r)
    (hs : s src=pairBits x y) :
    (decodeRev src dst).Runs s
      (Function.update (Function.update s src y) dst (x.reverse++s dst)) (5*x.length+2) := by
  induction x generalizing s with
  | nil =>
    have hx : s src=true::y := hs
    have he : Function.update (Function.update s src y) dst ([].reverse++s dst)=
        Function.update s src y := by
      simp only [List.reverse_nil,List.nil_append]
      rw [←Function.update_of_ne hne.symm y s,Function.update_eq_self]
    rw [he]
    apply Steps.next
    simp [decodeRev,Instr.eval,hx]
    apply Steps.next
    simp [Instr.eval,hx]
    exact .refl _ _
  | cons b x ih =>
    let s' := Function.update (Function.update s dst (b::s dst)) src (pairBits x y)
    have hs' : s' src=pairBits x y := by simp [s']
    have hi := ih s' hs'
    have he : Function.update (Function.update s' src y) dst (x.reverse++s' dst)=
        Function.update (Function.update s src y) dst ((b::x).reverse++s dst) := by
      funext k
      by_cases hkd : k=dst
      · subst k; simp [s',hne.symm,List.reverse_cons,List.append_assoc]
      · by_cases hks : k=src
        · subst k; simp [s',hne]
        · simp [s',Function.update_of_ne,hkd,hks]
    rw [he] at hi
    have ht : 5*(b::x).length+2=(5*x.length+2)+1+1+1+1+1 := by simp; omega
    rw [ht]
    apply Steps.next
    simp [decodeRev,Instr.eval,hs,pairBits]
    apply Steps.next
    simp [Instr.eval,hs,pairBits]
    cases b <;>
      (apply Steps.next
       simp [Instr.eval]
       apply Steps.next
       simp [Instr.eval,hne.symm]
       apply Steps.next
       simp [Instr.eval,hne]
       convert hi using 1; simp [s',Function.update_comm hne,Function.update_idem,Block.Runs,decodeRev])

end Block
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.StackFrame -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode

lemma lift_clean {r R : ℕ} (f : Fin (r+1) → Fin R) (hf : Function.Injective f)
    (s : Store R) (hs : ∀ i : Fin (r+1), i≠0 → s (f i)=[]) (v : List Bool) :
    liftStore f (Function.update (fun _ => []) 0 v) s=Function.update s (f 0) v := by
  classical
  funext k
  by_cases hk : ∃ i,f i=k
  · obtain ⟨i,rfl⟩ := hk
    rw [liftStore_at f hf]
    by_cases hi : i=0
    · subst i; simp
    · rw [Function.update_of_ne hi,Function.update_of_ne (fun h => hi (hf h)),hs i hi]
  · rw [liftStore_outside f _ _ k (by simpa only [not_exists] using hk),
      Function.update_of_ne (fun h => hk ⟨0,h.symm⟩)]

namespace Routine
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

lemma run_at (p : Routine ea eb f) {R : ℕ} (ι : Fin (p.scratch+1) → Fin R)
    (hι : Function.Injective ι) (s : Store R) (a : α)
    (hinput : s (ι 0)=ea a) (hclean : ∀ i, i≠0 → s (ι i)=[]) :
    ∃ t ≤ p.time.eval (ea a).length,
      (p.block.rename ι).Runs s (Function.update s (ι 0) (eb (f a))) t := by
  obtain ⟨t,ht,h⟩ := p.correct a
  have hh := p.block.rename_runs ι hι s h
  rw [lift_clean ι hι s hclean,lift_clean ι hι s hclean,
    ←hinput,Function.update_eq_self] at hh
  exact ⟨t,ht,hh⟩

noncomputable def reindex {α' β' : Type} (p : Routine ea eb f) (ea' : α' → List Bool)
    (eb' : β' → List Bool) (f' : α' → β') (u : α' → α)
    (hin : ∀ a,ea (u a)=ea' a) (hout : ∀ a,eb (f (u a))=eb' (f' a)) :
    Routine ea' eb' f' where
  scratch := p.scratch
  block := p.block
  time := p.time
  correct a := by simpa only [hin,hout] using p.correct (u a)

noncomputable def identity (ea : α → List Bool) : Routine ea ea id where
  scratch := 0
  block := Block.skip
  time := 1
  correct a := ⟨1,by simp,Block.skip_runs _⟩

end Routine
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.PairRoutine -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

namespace PairRegisters

def left (p q : ℕ) (i : Fin (p+1)) : Fin (p+q+3) := ⟨i.val,by have := i.isLt; omega⟩
def right (p q : ℕ) (i : Fin (q+1)) : Fin (p+q+3) := ⟨p+1+i.val,by have := i.isLt; omega⟩
def aux (p q : ℕ) : Fin (p+q+3) := ⟨p+q+2,by omega⟩

@[simp] lemma left_zero (p q : ℕ) : left p q 0=0 := rfl
lemma left_inj (p q : ℕ) : Function.Injective (left p q) := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (p+q+3) => k.val) h)
lemma right_inj (p q : ℕ) : Function.Injective (right p q) := by
  intro i j h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [right] at hh
  exact Fin.ext (by omega)
@[simp] lemma left_ne_right (p q : ℕ) (i : Fin (p+1)) (j : Fin (q+1)) : left p q i≠right p q j := by
  intro h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [left,right] at hh
  have := i.isLt
  omega
@[simp] lemma left_ne_aux (p q : ℕ) (i : Fin (p+1)) : left p q i≠aux p q := by
  intro h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [left,aux] at hh
  have := i.isLt
  omega
@[simp] lemma right_ne_aux (p q : ℕ) (i : Fin (q+1)) : right p q i≠aux p q := by
  intro h
  have hh := congrArg (fun k : Fin (p+q+3) => k.val) h
  simp only [right,aux] at hh
  have := i.isLt
  omega
@[simp] lemma zero_ne_right (p q : ℕ) (j : Fin (q+1)) : (0:Fin (p+q+3))≠right p q j :=
  left_ne_right p q 0 j
@[simp] lemma zero_ne_aux (p q : ℕ) : (0:Fin (p+q+3))≠aux p q := left_ne_aux p q 0

end PairRegisters

namespace Routine
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
  {ec : γ → List Bool} {f : α → β} {g : α → γ}

noncomputable def pair (p : Routine ea eb f) (q : Routine ea ec g) :
    Routine ea (fun z : β×γ => pairBits (eb z.1) (ec z.2)) (fun a => (f a,g a)) where
  scratch := p.scratch+q.scratch+2
  block :=
    let fst := (0:Fin (p.scratch+q.scratch+3))
    let snd := PairRegisters.right p.scratch q.scratch 0
    let aux := PairRegisters.aux p.scratch q.scratch
    (Block.copy fst snd aux).seq
      ((p.block.rename (PairRegisters.left p.scratch q.scratch)).seq
        ((q.block.rename (PairRegisters.right p.scratch q.scratch)).seq
          ((Block.pairInto fst snd aux).seq (Block.moveInto snd fst aux))))
  time := 100*(X+p.time+q.time+1)
  correct a := by
    let R := p.scratch+q.scratch+3
    let d := PairRegisters.right p.scratch q.scratch 0
    let aux := PairRegisters.aux p.scratch q.scratch
    have h0d : (0:Fin R)≠d := PairRegisters.zero_ne_right _ _ _
    have h0a : (0:Fin R)≠aux := PairRegisters.zero_ne_aux _ _
    have hda : d≠aux := PairRegisters.right_ne_aux _ _ _
    let s₀ : Store R := Function.update (fun _ => []) 0 (ea a)
    let s₁ := Function.update s₀ d (ea a)
    let s₂ := Function.update s₁ 0 (eb (f a))
    let s₃ := Function.update s₂ d (ec (g a))
    let s₄ := Function.update (Function.update s₃ 0 []) d (pairBits (eb (f a)) (ec (g a)))
    have hc : (Block.copy 0 d aux).Runs s₀ s₁ (9*(ea a).length+3) := by
      simpa [s₀,s₁,h0d.symm] using Block.copy_runs 0 d aux h0d h0a hda s₀
        (by simp [s₀,h0a.symm])
    obtain ⟨t,ht,hp⟩ := p.run_at (PairRegisters.left p.scratch q.scratch)
      (PairRegisters.left_inj _ _) s₁ a (by simp [s₁,s₀,h0d]) (by
        intro i hi
        have hne : PairRegisters.left p.scratch q.scratch i≠0 := by
          simpa only [←PairRegisters.left_zero p.scratch q.scratch] using
            (fun h => hi (PairRegisters.left_inj _ _ h))
        simp [s₁,s₀,d,PairRegisters.left_ne_right,hne])
    obtain ⟨u,hu,hq⟩ := q.run_at (PairRegisters.right p.scratch q.scratch)
      (PairRegisters.right_inj _ _) s₂ a (by
        change s₂ d=ea a
        simp [s₂,s₁,h0d.symm]) (by
        intro i hi
        have hne : PairRegisters.right p.scratch q.scratch i≠d :=
          fun h => hi (PairRegisters.right_inj _ _ h)
        have hn0 : PairRegisters.right p.scratch q.scratch i≠0 :=
          (PairRegisters.zero_ne_right _ _ _).symm
        simp [s₂,s₁,s₀,Function.update_of_ne,hne,hn0])
    change (p.block.rename (PairRegisters.left _ _)).Runs s₁ s₂ t at hp
    change (q.block.rename (PairRegisters.right _ _)).Runs s₂ s₃ u at hq
    have h₃ : (Block.pairInto 0 d aux).Runs s₃ s₄ (9*(eb (f a)).length+3) := by
      simpa [s₄,s₃,s₂,h0d] using Block.pairInto_runs 0 d aux h0d h0a hda s₃
        (by simp [s₃,s₂,s₁,s₀,h0a.symm,hda.symm])
    have h₄ := Block.moveInto_runs d 0 aux h0d.symm hda h0a s₄
      (by simp [s₄,h0d]) (by simp [s₄,s₃,s₂,s₁,s₀,h0a.symm,hda.symm])
    have hf : Function.update (Function.update s₄ d []) 0 (s₄ d)=
        Function.update (fun _ => []) 0 (pairBits (eb (f a)) (ec (g a))) := by
      funext k
      by_cases hk : k=0
      · subst k; simp [s₄]
      · by_cases hkd : k=d
        · subst k; simp [h0d.symm]
        · simp [s₄,s₃,s₂,s₁,s₀,Function.update_of_ne,hk,hkd]
    rw [hf] at h₄
    have hlen : (s₄ d).length=(pairBits (eb (f a)) (ec (g a))).length := by simp [s₄]
    rw [hlen] at h₄
    have hrun := Block.seq_runs _ _ hc (Block.seq_runs _ _ hp
      (Block.seq_runs _ _ hq (Block.seq_runs _ _ h₃ h₄)))
    refine ⟨_,?_,hrun⟩
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one,pairBits_length]
    have hf := p.length_bound a
    have hg := q.length_bound a
    omega

end Routine
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.ProjectionRoutine -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Routine
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool)

noncomputable def first :
    Routine (fun z : α×β => pairBits (ea z.1) (eb z.2)) ea Prod.fst where
  scratch := 1
  block := (Block.decodeRev 0 1).seq ((Block.clear 0).seq (Block.reverseInto 1 0))
  time := 10*X+10
  correct a := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (pairBits (ea a.1) (eb a.2))
    let s₁ := Function.update (Function.update s₀ 0 (eb a.2)) 1 (ea a.1).reverse
    let s₂ := Function.update s₁ 0 []
    have h₁ : (Block.decodeRev 0 1).Runs s₀ s₁ (5*(ea a.1).length+2) := by
      simpa [s₁,s₀] using Block.decodeRev_runs (0:Fin 2) 1 (by decide) (ea a.1) (eb a.2)
        s₀ (by simp [s₀])
    have h₂ : (Block.clear 0).Runs s₁ s₂ (2*(eb a.2).length+1) := by
      simpa [s₁] using Block.clear_runs (0:Fin 2) s₁
    have h₃ := Block.reverseInto_runs (1:Fin 2) 0 (by decide) s₂
    have he : Function.update (Function.update s₂ 1 []) 0 ((s₂ 1).reverse++s₂ 0)=
        Function.update (fun _ => []) 0 (ea a.1) := by
      funext k
      fin_cases k <;> simp [s₂,s₁,s₀]
    rw [he] at h₃
    have hl : (s₂ 1).length=(ea a.1).length := by simp [s₂,s₁]
    rw [hl] at h₃
    refine ⟨_,?_,Block.seq_runs _ _ h₁ (Block.seq_runs _ _ h₂ h₃)⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,pairBits_length]
    omega

noncomputable def second :
    Routine (fun z : α×β => pairBits (ea z.1) (eb z.2)) eb Prod.snd where
  scratch := 1
  block := (Block.decodeRev 0 1).seq (Block.clear 1)
  time := 10*X+10
  correct a := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (pairBits (ea a.1) (eb a.2))
    let s₁ := Function.update (Function.update s₀ 0 (eb a.2)) 1 (ea a.1).reverse
    have h₁ : (Block.decodeRev 0 1).Runs s₀ s₁ (5*(ea a.1).length+2) := by
      simpa [s₁,s₀] using Block.decodeRev_runs (0:Fin 2) 1 (by decide) (ea a.1) (eb a.2)
        s₀ (by simp [s₀])
    have h₂ := Block.clear_runs (1:Fin 2) s₁
    have he : Function.update s₁ 1 []=Function.update (fun _ => []) 0 (eb a.2) := by
      funext k
      fin_cases k <;> simp [s₁,s₀]
    rw [he] at h₂
    have hl : (s₁ 1).length=(ea a.1).length := by simp [s₁]
    rw [hl] at h₂
    refine ⟨_,?_,Block.seq_runs _ _ h₁ h₂⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,pairBits_length]
    omega

end Routine
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.SelectRoutine -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Block
variable {r : ℕ}
def dropTwo (k : Fin r) : Block r := (pop k).seq (pop k)
lemma dropTwo_runs (k : Fin r) (s : Store r) (a b : Bool) (l : List Bool)
    (hs : s k=a::b::l) :
    (dropTwo k).Runs s (Function.update s k l) 2 := by
  have h₁ := pop_runs k s
  have h₂ := pop_runs k (Function.update s k (s k).tail)
  have h := seq_runs _ _ h₁ h₂
  simpa [dropTwo,hs,Function.update_idem] using h

def emit (k : Fin r) : List Bool → Block r
  | [] => skip
  | b::l => (emit k l).seq (push k b)
lemma emit_runs (k : Fin r) (x : List Bool) (s : Store r) :
    (emit k x).Runs s (Function.update s k (x++s k)) (x.length+1) := by
  induction x with
  | nil => simpa [emit] using skip_runs s
  | cons b x ih =>
    have h := seq_runs _ _ ih (push_runs k b (Function.update s k (x++s k)))
    simpa [emit,Function.update_idem,Nat.add_assoc] using h
end Block
namespace Routine
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
  {f g : α → β}

noncomputable def constant (ea : α → List Bool) (eb : β → List Bool) (b : β) :
    Routine ea eb (fun _ => b) where
  scratch := 0
  block := (Block.clear 0).seq (Block.emit 0 (eb b))
  time := 2*X+C ((eb b).length+2)
  correct a := by
    have h := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1)
      (Function.update (fun _ => []) 0 (ea a)))
      (Block.emit_runs (0:Fin 1) (eb b)
        (Function.update (Function.update (fun _ => []) 0 (ea a)) 0 []))
    refine ⟨2*(ea a).length+1+((eb b).length+1),?_,?_⟩
    · simpa only [eval_add,eval_mul,eval_ofNat,eval_X,eval_C,Function.update_self]
        using (show 2*(ea a).length+1+((eb b).length+1)≤2*(ea a).length+((eb b).length+2) by omega)
    · simpa only [Function.update_idem,Function.update_self,List.append_nil] using h

noncomputable def select (p : Routine ea eb f) (q : Routine ea eb g) :
    Routine (fun z : Bool×α => pairBits [z.1] (ea z.2)) eb
      (fun z => if z.1 then g z.2 else f z.2) where
  scratch := p.scratch+q.scratch
  block :=
    let ι : Fin (p.scratch+1) → Fin (p.scratch+q.scratch+1) :=
      fun i => ⟨i.val,by have := i.isLt; omega⟩
    let κ : Fin (q.scratch+1) → Fin (p.scratch+q.scratch+1) :=
      fun i => ⟨i.val,by have := i.isLt; omega⟩
    (Block.pop 0).seq (Block.cases 0 Block.skip
      ((Block.dropTwo 0).seq (p.block.rename ι))
      ((Block.dropTwo 0).seq (q.block.rename κ)))
  time := p.time+q.time+4
  correct z := by
    let R := p.scratch+q.scratch+1
    let ι : Fin (p.scratch+1) → Fin R := fun i => ⟨i.val,by have := i.isLt; omega⟩
    let κ : Fin (q.scratch+1) → Fin R := fun i => ⟨i.val,by have := i.isLt; omega⟩
    have hι : Function.Injective ι := fun i j h => Fin.ext (congrArg (fun k : Fin R => k.val) h)
    have hκ : Function.Injective κ := fun i j h => Fin.ext (congrArg (fun k : Fin R => k.val) h)
    let s₀ : Store R := Function.update (fun _ => []) 0 (pairBits [z.1] (ea z.2))
    let s₁ : Store R := Function.update (fun _ => []) 0 (z.1::true::ea z.2)
    let s₂ : Store R := Function.update (fun _ => []) 0 (ea z.2)
    have hp : (Block.pop 0).Runs s₀ s₁ 1 := by
      simpa [s₀,s₁,pairBits,Function.update_idem] using Block.pop_runs (0:Fin R) s₀
    have hd : (Block.dropTwo 0).Runs s₁ s₂ 2 := by
      simpa [s₁,s₂,Function.update_idem] using Block.dropTwo_runs (0:Fin R) s₁ z.1 true
        (ea z.2) (by simp [s₁])
    have hp₀ := p.run_at ι hι s₂ z.2 (by simp [s₂,ι]) (by
      intro i hi
      have hk : ι i≠0 := fun h => hi (hι h)
      simp [s₂,Function.update_of_ne hk])
    have hq₀ := q.run_at κ hκ s₂ z.2 (by simp [s₂,κ]) (by
      intro i hi
      have hk : κ i≠0 := fun h => hi (hκ h)
      simp [s₂,Function.update_of_ne hk])
    have hlen : (ea z.2).length≤(pairBits [z.1] (ea z.2)).length := by
      simp only [pairBits_length,List.length_singleton]
      omega
    have ht₁ := polynomial_eval_mono p.time hlen
    have ht₂ := polynomial_eval_mono q.time hlen
    rcases z with ⟨b,a⟩
    cases b with
    | false =>
      obtain ⟨t,ht,hr⟩ := hp₀
      have hx := Block.cases_runs_false (0:Fin R) Block.skip
        ((Block.dropTwo 0).seq (p.block.rename ι)) ((Block.dropTwo 0).seq (q.block.rename κ))
        (by simp [s₁]) (Block.seq_runs _ _ hd hr)
      refine ⟨1+(2+t+1),?_,?_⟩
      · simp only [eval_add,eval_ofNat]
        dsimp only at ht₁ ht₂ ht
        omega
      · simpa [s₂,ι,Function.update_idem] using Block.seq_runs _ _ hp hx
    | true =>
      obtain ⟨t,ht,hr⟩ := hq₀
      have hx := Block.cases_runs_true (0:Fin R) Block.skip
        ((Block.dropTwo 0).seq (p.block.rename ι)) ((Block.dropTwo 0).seq (q.block.rename κ))
        (by simp [s₁]) (Block.seq_runs _ _ hd hr)
      refine ⟨1+(2+t+1),?_,?_⟩
      · simp only [eval_add,eval_ofNat]
        dsimp only at ht₁ ht₂ ht
        omega
      · simpa [s₂,κ,Function.update_idem] using Block.seq_runs _ _ hp hx

end Routine
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.IterateRoutine -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

def unary (n : ℕ) : List Bool := List.replicate n true
@[simp] lemma unary_length (n : ℕ) : (unary n).length=n := by simp [unary]
@[simp] lemma unary_reverse (n : ℕ) : (unary n).reverse=unary n := by simp [unary]
@[simp] lemma unary_zero : unary 0=[] := rfl
@[simp] lemma unary_succ (n : ℕ) : unary (n+1)=true::unary n := by simp [unary,List.replicate_succ]

namespace Routine
variable {α : Type} {ea : α → List Bool} {f : α → α}

lemma iterate_runs_at (p : Routine ea ea f) {R : ℕ}
    (ι : Fin (p.scratch+1) → Fin R) (hι : Function.Injective ι)
    (counter : Fin R) (hc : ∀ i,ι i≠counter) (B n : ℕ) (a : α) (s : Store R)
    (hin : s (ι 0)=ea a) (hclean : ∀ i,i≠0 → s (ι i)=[]) (hcount : s counter=unary n)
    (hb : ∀ j≤n,(ea (f^[j] a)).length≤B) :
    ∃ t≤n*(p.time.eval B+2)+1,
      (Block.loop counter ((Block.pop counter).seq (p.block.rename ι))).Runs s
        (Function.update (Function.update s counter []) (ι 0) (ea (f^[n] a))) t := by
  induction n generalizing a s with
  | zero =>
    have he : Function.update (Function.update s counter []) (ι 0) (ea (f^[0] a))=s := by
      simp only [Function.iterate_zero, id_eq]
      have hc0 : s counter=[] := hcount
      rw [←hin,←hc0,Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact ⟨1,by simp,Block.loop_runs_empty _ _ _ (by simpa using hcount)⟩
  | succ n ih =>
    let s₁ := Function.update s counter (unary n)
    let s₂ := Function.update s₁ (ι 0) (ea (f a))
    have hp : (Block.pop counter).Runs s s₁ 1 := by
      simpa [s₁,hcount] using Block.pop_runs counter s
    obtain ⟨t,ht,hp₀⟩ := p.run_at ι hι s₁ a (by simpa [s₁,hc] using hin) (by
      intro i hi
      simpa [s₁,hc] using hclean i hi)
    change (p.block.rename ι).Runs s₁ s₂ t at hp₀
    obtain ⟨u,hu,hi⟩ := ih (f a) s₂ (by simp [s₂]) (by
      intro i hi
      have hne : ι i≠ι 0 := fun h => hi (hι h)
      simp [s₂,s₁,Function.update_of_ne hne,hc,hclean i hi])
      (by simp [s₂,s₁,(hc 0).symm]) (by
        intro j hj
        simpa only [Function.iterate_succ_apply] using hb (j+1) (by omega))
    have he : Function.update (Function.update s₂ counter []) (ι 0) (ea (f^[n] (f a)))=
        Function.update (Function.update s counter []) (ι 0) (ea (f^[n+1] a)) := by
      funext k
      by_cases hk : k=ι 0
      · subst k; simp [Function.iterate_succ_apply]
      · by_cases hkc : k=counter
        · subst k; simp [(hc 0).symm]
        · simp [s₂,s₁,Function.update_of_ne,hk,hkc]
    rw [he] at hi
    have hh := Block.loop_runs_step counter ((Block.pop counter).seq (p.block.rename ι))
      (by simp [hcount]) (Block.seq_runs _ _ hp hp₀) hi
    refine ⟨_,?_,hh⟩
    have ht' : t≤p.time.eval B := ht.trans (polynomial_eval_mono p.time (by simpa using hb 0 (by omega)))
    nlinarith

noncomputable def boundedIterate {δ : Type} (p : Routine ea ea f)
    (count : δ → ℕ) (initial : δ → α) (P : Polynomial ℕ)
    (hbound : ∀ d j,j≤count d → (ea (f^[j] (initial d))).length≤
      P.eval (pairBits (unary (count d)) (ea (initial d))).length) :
    Routine (fun d => pairBits (unary (count d)) (ea (initial d))) ea
      (fun d => f^[count d] (initial d)) where
  scratch := p.scratch+1
  block :=
    let ι : Fin (p.scratch+1) → Fin (p.scratch+2) := fun i => ⟨i.val,by omega⟩
    let c : Fin (p.scratch+2) := ⟨p.scratch+1,by omega⟩
    (Block.decodeRev 0 c).seq (Block.loop c ((Block.pop c).seq (p.block.rename ι)))
  time := X*(p.time.comp P+7)+3
  correct d := by
    let R := p.scratch+2
    let ι : Fin (p.scratch+1) → Fin R := fun i => ⟨i.val,by omega⟩
    let c : Fin R := ⟨p.scratch+1,by omega⟩
    have hι : Function.Injective ι := fun i j h => Fin.ext (congrArg (fun k : Fin R => k.val) h)
    have hc : ∀ i,ι i≠c := by
      intro i h
      have hh := congrArg (fun k : Fin R => k.val) h
      have hi := i.isLt
      simp only [ι,c] at hh
      omega
    have h0c : (0:Fin R)≠c := hc 0
    let e := pairBits (unary (count d)) (ea (initial d))
    let s₀ : Store R := Function.update (fun _ => []) 0 e
    let s₁ : Store R := Function.update (Function.update s₀ 0 (ea (initial d))) c (unary (count d))
    have hd : (Block.decodeRev 0 c).Runs s₀ s₁ (5*count d+2) := by
      simpa [s₁,s₀,h0c.symm] using Block.decodeRev_runs (0:Fin R) c h0c
        (unary (count d)) (ea (initial d)) s₀ (by simp [s₀,e])
    obtain ⟨t,ht,hi⟩ := p.iterate_runs_at ι hι c hc (P.eval e.length) (count d) (initial d) s₁
      (by change s₁ 0=_; simp [s₁,h0c]) (by
        intro i hi
        have hne : ι i≠0 := fun h => hi (hι h)
        simp [s₁,s₀,Function.update_of_ne,hne,hc])
      (by simp [s₁]) (hbound d)
    have he : Function.update (Function.update s₁ c []) (ι 0) (ea (f^[count d] (initial d)))=
        Function.update (fun _ => []) 0 (ea (f^[count d] (initial d))) := by
      funext k
      change Function.update (Function.update s₁ c []) 0 _ k=_
      by_cases hk : k=0
      · subst k; simp
      · by_cases hkc : k=c
        · subst k; simp [h0c.symm]
        · simp [s₁,s₀,Function.update_of_ne,hk,hkc]
    rw [he] at hi
    refine ⟨_,?_,Block.seq_runs _ _ hd hi⟩
    simp only [eval_add,eval_mul,eval_X,eval_comp,eval_ofNat]
    change 5*count d+2+t≤e.length*(p.time.eval (P.eval e.length)+7)+3
    have hn : count d≤e.length := by simp [e,pairBits_length]; omega
    have hmul := Nat.mul_le_mul_right (p.time.eval (P.eval e.length)+7) hn
    nlinarith

end Routine
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.RawRoutine -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Routine

noncomputable def append : Routine (fun z : List Bool×List Bool => pairBits z.1 z.2) id
    (fun z => z.1++z.2) where
  scratch := 1
  block := (Block.decodeRev 0 1).seq (Block.reverseInto 1 0)
  time := 10*X+10
  correct z := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (pairBits z.1 z.2)
    let s₁ := Function.update (Function.update s₀ 0 z.2) 1 z.1.reverse
    have h₁ : (Block.decodeRev 0 1).Runs s₀ s₁ (5*z.1.length+2) := by
      simpa [s₁,s₀] using Block.decodeRev_runs (0:Fin 2) 1 (by decide) z.1 z.2
        s₀ (by simp [s₀])
    have h₂ := Block.reverseInto_runs (1:Fin 2) 0 (by decide) s₁
    have he : Function.update (Function.update s₁ 1 []) 0 ((s₁ 1).reverse++s₁ 0)=
        Function.update (fun _ => []) 0 (z.1++z.2) := by
      funext k
      fin_cases k <;> simp [s₁,s₀]
    rw [he] at h₂
    have hl : (s₁ 1).length=z.1.length := by simp [s₁]
    rw [hl] at h₂
    refine ⟨_,?_,Block.seq_runs _ _ h₁ h₂⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,pairBits_length]
    omega

noncomputable def pushBit (b : Bool) : Routine (id : List Bool → List Bool) id (List.cons b) where
  scratch := 0
  block := Block.push 0 b
  time := 1
  correct x := by
    refine ⟨1,by simp,?_⟩
    simpa [Function.update_idem] using Block.push_runs (0:Fin 1) b (Function.update (fun _ => []) 0 x)

noncomputable def tail : Routine (id : List Bool → List Bool) id List.tail where
  scratch := 0
  block := Block.pop 0
  time := 1
  correct x := by
    refine ⟨1,by simp,?_⟩
    simpa [Function.update_idem] using Block.pop_runs (0:Fin 1) (Function.update (fun _ => []) 0 x)

noncomputable def isEmpty : Routine (id : List Bool → List Bool) (fun b : Bool => [b]) List.isEmpty where
  scratch := 0
  block := Block.cases 0 (Block.push 0 true)
    ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false))
  time := 2*X+3
  correct x := by
    let s : Store 1 := Function.update (fun _ => []) 0 x
    have hfalse := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1) s)
      (Block.push_runs (0:Fin 1) false (Function.update s 0 []))
    have htrue := Block.push_runs (0:Fin 1) true s
    cases x with
    | nil =>
      have hh := Block.cases_runs_empty (0:Fin 1) (Block.push 0 true)
        ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false)) (by simp [s]) htrue
      refine ⟨2,by simp,?_⟩
      simpa [s,Function.update_idem] using hh
    | cons b l =>
      cases b with
      | false =>
        have hh := Block.cases_runs_false (0:Fin 1) (Block.push 0 true)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false))
          (by simp [s]) hfalse
        refine ⟨2*(l.length+1)+3,?_,?_⟩
        · simp
        · simpa [s,Function.update_idem,Nat.add_assoc] using hh
      | true =>
        have hh := Block.cases_runs_true (0:Fin 1) (Block.push 0 true)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 false))
          (by simp [s]) hfalse
        refine ⟨2*(l.length+1)+3,?_,?_⟩
        · simp
        · simpa [s,Function.update_idem,Nat.add_assoc] using hh

end Routine
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.LengthRoutine -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Block
variable {r : ℕ}
def lengthInto (src dst : Fin r) : Block r := loop src ((pop src).seq (push dst true))
lemma lengthInto_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) :
    (lengthInto src dst).Runs s
      (Function.update (Function.update s src []) dst (unary (s src).length++s dst))
      (3*(s src).length+1) := by
  generalize hl : s src=l
  induction l generalizing s with
  | nil =>
    have he : Function.update (Function.update s src []) dst (unary 0++s dst)=s := by
      simp only [unary_zero,List.nil_append]
      rw [←hl,Function.update_eq_self,Function.update_eq_self]
    change (lengthInto src dst).Runs s
      (Function.update (Function.update s src []) dst (unary 0++s dst)) 1
    rw [he]
    exact loop_runs_empty src _ s hl
  | cons b l ih =>
    let s' := Function.update (Function.update s src l) dst (true::s dst)
    have hp : (pop src).Runs s (Function.update s src l) 1 := by
      simpa [hl] using pop_runs src s
    have ht : (push dst true).Runs (Function.update s src l) s' 1 := by
      simpa [s',hne.symm] using push_runs dst true (Function.update s src l)
    have hi := ih s' (by simp [s',hne])
    have he : Function.update (Function.update s' src []) dst (unary l.length++s' dst)=
        Function.update (Function.update s src []) dst (unary (b::l).length++s dst) := by
      funext k
      by_cases hk : k=dst
      · subst k
        simp only [Function.update_self,s',List.length_cons,unary]
        simp only [List.replicate_succ',List.append_assoc,List.singleton_append]
      · by_cases hks : k=src
        · subst k; simp [s',hne]
        · simp [s',Function.update_of_ne,hk,hks]
    rw [he] at hi
    have h := loop_runs_step src ((pop src).seq (push dst true)) (by simp [hl])
      (seq_runs _ _ hp ht) hi
    have heq : 2+(3*l.length+1)+1=3*(b::l).length+1 := by simp; omega
    rw [heq] at h
    exact h
end Block
namespace Routine
variable {α : Type}
noncomputable def codeLength (ea : α → List Bool) : Routine ea unary (fun a => (ea a).length) where
  scratch := 1
  block := (Block.lengthInto 0 1).seq (Block.reverseInto 1 0)
  time := 7*X+2
  correct a := by
    let s₀ : Store 2 := Function.update (fun _ => []) 0 (ea a)
    let s₁ := Function.update (Function.update s₀ 0 []) 1 (unary (ea a).length)
    have h₁ : (Block.lengthInto 0 1).Runs s₀ s₁ (3*(ea a).length+1) := by
      simpa [s₀,s₁] using Block.lengthInto_runs (0:Fin 2) 1 (by decide) s₀
    have h₂ := Block.reverseInto_runs (1:Fin 2) 0 (by decide) s₁
    have he : Function.update (Function.update s₁ 1 []) 0 ((s₁ 1).reverse++s₁ 0)=
        Function.update (fun _ => []) 0 (unary (ea a).length) := by
      funext k
      fin_cases k <;> simp [s₁,s₀]
    rw [he] at h₂
    have hl : (s₁ 1).length=(ea a).length := by simp [s₁]
    rw [hl] at h₂
    refine ⟨_,?_,Block.seq_runs _ _ h₁ h₂⟩
    simp only [eval_add,eval_mul,eval_ofNat,eval_X]
    omega
end Routine
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.PolyCoding -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
class Coding (α : Type) where
  encode : α → List Bool
export Coding (encode)
instance : Coding ℕ := ⟨unary⟩
instance : Coding Bool := ⟨fun b => [b]⟩
instance : Coding Unit := ⟨fun _ => []⟩
instance {α β : Type} [Coding α] [Coding β] : Coding (α×β) :=
  ⟨fun z => pairBits (encode z.1) (encode z.2)⟩

def listCode {α : Type} (ea : α → List Bool) : List α → List Bool
  | [] => []
  | a::l => pairBits (ea a) (listCode ea l)
instance {α : Type} [Coding α] : Coding (List α) := ⟨listCode encode⟩

@[simp] lemma encode_nat (n : ℕ) : encode n=unary n := rfl
@[simp] lemma encode_bool (b : Bool) : encode b=[b] := rfl
@[simp] lemma encode_pair {α β : Type} [Coding α] [Coding β] (a : α) (b : β) :
    encode (a,b)=pairBits (encode a) (encode b) := rfl
@[simp] lemma encode_prod {α β : Type} [Coding α] [Coding β] (z : α×β) :
    encode z=pairBits (encode z.1) (encode z.2) := rfl

@[simp] lemma code_nil {α : Type} [Coding α] : encode ([]:List α)=[] := rfl
@[simp] lemma code_cons {α : Type} [Coding α] (a : α) (l : List α) :
    encode (a::l)=pairBits (encode a) (encode l) := rfl

lemma pairBits_append (x y z : List Bool) : pairBits x (y++z)=pairBits x y++z := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa only [pairBits,List.cons_append,Function.comp_apply] using congrArg (List.cons false ∘ List.cons b) ih

lemma code_append {α : Type} [Coding α] (l m : List α) : encode (l++m)=encode l++encode m := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.cons_append,code_cons,ih,pairBits_append]

lemma list_length_le_code {α : Type} [Coding α] (l : List α) : l.length≤(encode l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.length_cons,code_cons,pairBits_length]; omega

@[fun_prop] def Poly {α β : Type} [Coding α] [Coding β] (f : α → β) : Prop :=
  Nonempty (Routine encode encode f)

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
noncomputable def routine {f : α → β} (h : Poly f) : Routine encode encode f := Classical.choice h

@[fun_prop] theorem identity : Poly (fun a : α => a) := ⟨Routine.identity encode⟩
@[fun_prop] theorem constant (b : β) : Poly (fun _ : α => b) := ⟨Routine.constant encode encode b⟩
@[fun_prop] theorem comp (f : β → γ) (g : α → β) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => f (g a)) := ⟨hg.routine.comp hf.routine⟩
@[fun_prop] theorem pair (f : α → β) (g : α → γ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => (f a,g a)) := ⟨hf.routine.pair hg.routine⟩
@[fun_prop] theorem first (f : α → β×γ) (hf : Poly f) : Poly (fun a => (f a).1) :=
  ⟨hf.routine.comp (Routine.first encode encode)⟩
@[fun_prop] theorem second (f : α → β×γ) (hf : Poly f) : Poly (fun a => (f a).2) :=
  ⟨hf.routine.comp (Routine.second encode encode)⟩

@[fun_prop] theorem cond (b : α → Bool) (f g : α → β) (hb : Poly b) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => if b a then g a else f a) := by
  let p := (hb.routine.pair (Routine.identity encode)).comp (hf.routine.select hg.routine)
  exact ⟨p⟩

@[fun_prop] theorem codeLength : Poly (fun a : α => (encode a).length) := ⟨Routine.codeLength encode⟩

theorem boundedIterate (f : α → α) (hf : Poly f) (P : Polynomial ℕ)
    (h : ∀ (z : ℕ×α) j,j≤z.1 → (encode (f^[j] z.2)).length≤P.eval (encode z).length) :
    Poly (fun z : ℕ×α => f^[z.1] z.2) :=
  ⟨hf.routine.boundedIterate Prod.fst Prod.snd P h⟩

theorem congr {f g : α → β} (hf : Poly f) (h : ∀ a,f a=g a) : Poly g := by
  have he : f=g := funext h
  rwa [←he]

end Poly
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.ListRoutine -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Routine
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
  {f : α×List α → β}

noncomputable def listCases (b : β)
    (p : Routine (fun z : α×List α => pairBits (ea z.1) (listCode ea z.2)) eb f) :
    Routine (listCode ea) eb (fun l => match l with | [] => b | a::l => f (a,l)) where
  scratch := p.scratch
  block := Block.cases 0 (Block.emit 0 (eb b)) p.block p.block
  time := p.time+C ((eb b).length+2)
  correct l := by
    let s : Store (p.scratch+1) := Function.update (fun _ => []) 0 (listCode ea l)
    cases l with
    | nil =>
      have he := Block.emit_runs (0:Fin (p.scratch+1)) (eb b) s
      have hh := Block.cases_runs_empty (0:Fin (p.scratch+1)) (Block.emit 0 (eb b))
        p.block p.block (by simp [s,listCode]) he
      refine ⟨(eb b).length+1+1,?_,?_⟩
      · simp only [eval_add,eval_C]
        omega
      · simpa [s,listCode,Function.update_idem] using hh
    | cons a l =>
      obtain ⟨t,ht,hp⟩ := p.correct (a,l)
      change p.block.Runs s (Function.update (fun _ => []) 0 (eb (f (a,l)))) t at hp
      refine ⟨t+1,?_,?_⟩
      · simp only [eval_add,eval_C,listCode] at *
        omega
      · cases ha : ea a with
        | nil => exact Block.cases_runs_true _ _ _ _ (by simp [listCode,ha,pairBits]) hp
        | cons x xs => exact Block.cases_runs_false _ _ _ _ (by simp [listCode,ha,pairBits]) hp
end Routine
namespace Poly
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem listCases (b : β) (f : α×List α → β) (hf : Poly f) :
    Poly (fun l => match l with | [] => b | a::l => f (a,l)) :=
  ⟨Routine.listCases encode encode b hf.routine⟩

@[fun_prop] theorem listCons : Poly (fun z : α×List α => z.1::z.2) := by
  refine ⟨(Routine.identity (encode : α×List α → List Bool)).reindex encode encode
    (fun z : α×List α => z.1::z.2) id (fun _ => rfl) (fun _ => rfl)⟩

@[fun_prop] theorem listTail : Poly (List.tail : List α → List α) := by
  exact listCases [] Prod.snd (by fun_prop)

@[fun_prop] theorem listHeadD (a : α) : Poly (fun l : List α => l.headD a) := by
  exact (listCases a Prod.fst (by fun_prop)).congr (fun l => by cases l <;> rfl)

@[fun_prop] theorem listIsEmpty : Poly (List.isEmpty : List α → Bool) := by
  exact listCases true (fun _ : α×List α => false) (by fun_prop)

@[fun_prop] theorem listAppend : Poly (fun z : List α×List α => z.1++z.2) := by
  refine ⟨Routine.append.reindex encode encode (fun z : List α×List α => z.1++z.2)
    (fun z => (encode z.1,encode z.2)) (fun _ => rfl) ?_⟩
  intro z
  exact (code_append z.1 z.2).symm

end Poly
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.UnaryArithmetic -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Poly

@[fun_prop] theorem natSucc : Poly (fun n : ℕ => n+1) := by
  refine ⟨(Routine.pushBit true).reindex encode encode (fun n : ℕ => n+1) unary
    (fun _ => rfl) ?_⟩
  intro n
  simp

@[fun_prop] theorem natPred : Poly (Nat.pred : ℕ → ℕ) := by
  refine ⟨Routine.tail.reindex encode encode Nat.pred unary (fun _ => rfl) ?_⟩
  intro n
  cases n <;> simp

@[fun_prop] theorem natZeroTest : Poly (fun n : ℕ => decide (n=0)) := by
  refine ⟨Routine.isEmpty.reindex encode encode (fun n : ℕ => decide (n=0)) unary
    (fun _ => rfl) ?_⟩
  intro n
  cases n <;> simp

@[fun_prop] theorem natAdd : Poly (fun z : ℕ×ℕ => z.1+z.2) := by
  refine ⟨Routine.append.reindex encode encode (fun z : ℕ×ℕ => z.1+z.2)
    (fun z => (unary z.1,unary z.2)) (fun _ => rfl) ?_⟩
  intro z
  simp only [id_eq,encode_nat,unary,List.replicate_add]

@[fun_prop] theorem natSub : Poly (fun z : ℕ×ℕ => z.1-z.2) := by
  have hp : Poly (fun z : ℕ×ℕ => Nat.pred^[z.1] z.2) :=
    boundedIterate Nat.pred natPred X (by
      intro z j hj
      simp only [Nat.pred_iterate,encode_nat,unary_length,encode_prod,pairBits_length,eval_X]
      omega)
  have h : Poly (fun z : ℕ×ℕ => Nat.pred^[z.2] z.1) := by fun_prop
  exact h.congr (fun z => Nat.pred_iterate z.1 z.2)

@[fun_prop] theorem boolNot : Poly (Bool.not : Bool → Bool) := by
  have h : Poly (fun b : Bool => if b then false else true) := by fun_prop
  exact h.congr (fun b => by cases b <;> rfl)

@[fun_prop] theorem boolAnd : Poly (fun z : Bool×Bool => z.1 && z.2) := by
  have h : Poly (fun z : Bool×Bool => if z.1 then z.2 else false) := by fun_prop
  exact h.congr (fun z => by cases z.1 <;> rfl)

@[fun_prop] theorem boolOr : Poly (fun z : Bool×Bool => z.1 || z.2) := by
  have h : Poly (fun z : Bool×Bool => if z.1 then true else z.2) := by fun_prop
  exact h.congr (fun z => by cases z.1 <;> rfl)

@[fun_prop] theorem natLE : Poly (fun z : ℕ×ℕ => decide (z.1≤z.2)) := by
  have h : Poly (fun z : ℕ×ℕ => decide (z.1-z.2=0)) := comp _ _ natZeroTest natSub
  exact h.congr (fun z => by simp [Nat.sub_eq_zero_iff_le])

@[fun_prop] theorem natLT : Poly (fun z : ℕ×ℕ => decide (z.1<z.2)) := by
  have hle : Poly (fun z : ℕ×ℕ => decide (z.2≤z.1)) := comp _ (fun z : ℕ×ℕ => (z.2,z.1)) natLE (by fun_prop)
  have h : Poly (fun z : ℕ×ℕ => !(decide (z.2≤z.1))) := comp _ _ boolNot hle
  exact h.congr (fun z => by simp [←decide_not])

@[fun_prop] theorem natEQ : Poly (fun z : ℕ×ℕ => decide (z.1=z.2)) := by
  have hle : Poly (fun z : ℕ×ℕ => decide (z.2≤z.1)) := comp _ (fun z : ℕ×ℕ => (z.2,z.1)) natLE (by fun_prop)
  have h : Poly (fun z : ℕ×ℕ => decide (z.1≤z.2) && decide (z.2≤z.1)) :=
    comp _ _ boolAnd (pair _ _ natLE hle)
  exact h.congr (fun z => by simp [le_antisymm_iff])

private def addStep (z : ℕ×ℕ) : ℕ×ℕ := (z.1,z.2+z.1)
private lemma addStep_iterate (n : ℕ) (z : ℕ×ℕ) : addStep^[n] z=(z.1,z.2+n*z.1) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply',ih,addStep,Nat.add_mul,Nat.add_assoc]

@[fun_prop] theorem natMul : Poly (fun z : ℕ×ℕ => z.1*z.2) := by
  have hs : Poly addStep := by unfold addStep; fun_prop
  have hi : Poly (fun z : ℕ×(ℕ×ℕ) => addStep^[z.1] z.2) :=
    boundedIterate addStep hs ((X+1)^2) (by
      intro z j hj
      simp only [addStep_iterate,encode_prod,encode_nat,unary_length,pairBits_length,
        eval_pow,eval_add,eval_X,eval_one]
      have hh : j*z.2.1≤z.1*z.2.1 := Nat.mul_le_mul_right _ hj
      nlinarith [sq_nonneg (z.1:ℤ),sq_nonneg (z.2.1:ℤ)])
  have h : Poly (fun z : ℕ×ℕ => (addStep^[z.2] (z.1,0)).2) := by fun_prop
  exact h.congr (fun z => by simp [addStep_iterate,Nat.mul_comm])

@[fun_prop] theorem natMin : Poly (fun z : ℕ×ℕ => min z.1 z.2) := by
  have h : Poly (fun z : ℕ×ℕ => if decide (z.1≤z.2) then z.1 else z.2) := by fun_prop
  exact h.congr (fun z => by simp [min_def])

@[fun_prop] theorem natMax : Poly (fun z : ℕ×ℕ => max z.1 z.2) := by
  have h : Poly (fun z : ℕ×ℕ => if decide (z.1≤z.2) then z.2 else z.1) := by fun_prop
  exact h.congr (fun z => by simp [max_def])

variable {α : Type} [Coding α]
@[fun_prop] theorem natLe_apply (f g : α → ℕ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a≤g a)) := comp _ _ natLE (pair _ _ hf hg)
@[fun_prop] theorem natLt_apply (f g : α → ℕ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a<g a)) := comp _ _ natLT (pair _ _ hf hg)
@[fun_prop] theorem natEq_apply (f g : α → ℕ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a=g a)) := comp _ _ natEQ (pair _ _ hf hg)
@[fun_prop] theorem natPow (k : ℕ) : Poly (fun n : ℕ => n^k) := by
  induction k with
  | zero => simpa only [pow_zero] using (constant (α := ℕ) (1:ℕ))
  | succ k ih =>
    have h : Poly (fun n : ℕ => n^k*n) := comp _ _ natMul (pair _ _ ih identity)
    exact h.congr (fun n => (pow_succ n k).symm)
end Poly
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.FoldRoutine -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma code_drop_le {α : Type} [Coding α] (l : List α) (n : ℕ) :
    (encode (l.drop n)).length≤(encode l).length := by
  have h := congrArg (fun xs => (encode xs).length) (List.take_append_drop n l)
  rw [code_append,List.length_append] at h
  omega

def foldStep {α β : Type} (a₀ : α) (f : β×α → β) (z : List α×β) : List α×β :=
  if z.1.isEmpty then z else (z.1.tail,f (z.2,z.1.headD a₀))

lemma foldStep_iterate {α β : Type} (a₀ : α) (f : β×α → β) (n : ℕ) (z : List α×β) :
    (foldStep a₀ f)^[n] z=(z.1.drop n,(z.1.take n).foldl (fun b a => f (b,a)) z.2) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rcases z with ⟨l,b⟩
    cases l with
    | nil => simp [Function.iterate_succ_apply,foldStep,ih]
    | cons a l => simp [Function.iterate_succ_apply,foldStep,ih]

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

theorem listFold (a₀ : α) (f : β×α → β) (hf : Poly f) (P : Polynomial ℕ)
    (hb : ∀ (z : List α×β) k,
      (encode ((z.1.take k).foldl (fun b a => f (b,a)) z.2)).length≤P.eval (encode z).length) :
    Poly (fun z : List α×β => z.1.foldl (fun b a => f (b,a)) z.2) := by
  have hs : Poly (foldStep a₀ f) := by unfold foldStep; fun_prop
  have hi : Poly (fun z : ℕ×(List α×β) => (foldStep a₀ f)^[z.1] z.2) :=
    boundedIterate (foldStep a₀ f) hs (X+P) (by
      intro z j hj
      rw [foldStep_iterate]
      have hl := code_drop_le z.2.1 j
      have hn : (encode z.2).length≤(encode z).length := by
        simp only [encode_prod,pairBits_length]
        omega
      have hacc := (hb z.2 j).trans (polynomial_eval_mono P hn)
      simp only [encode_prod,pairBits_length,eval_add,eval_X] at *
      omega)
  have h : Poly (fun z : List α×β => ((foldStep a₀ f)^[(encode z.1).length] z).2) :=
    second _ (comp _ (fun z : List α×β => ((encode z.1).length,z)) hi
      (pair _ _ (comp _ Prod.fst codeLength (first _ identity)) identity))
  exact h.congr (fun z => by
    rw [foldStep_iterate]
    simp only [List.take_of_length_le (list_length_le_code z.1)])

omit [Coding α] in
private lemma count_fold (l : List α) (b : ℕ) :
    l.foldl (fun b _ => b+1) b=b+l.length := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih,Nat.add_comm,Nat.add_left_comm]

@[fun_prop] theorem listLength [Inhabited α] : Poly (List.length : List α → ℕ) := by
  have hf : Poly (fun z : ℕ×α => z.1+1) := by fun_prop
  have hfold := listFold (default:α) (fun z : ℕ×α => z.1+1) hf X (by
    intro z k
    rw [count_fold]
    have hk : (z.1.take k).length≤z.1.length := by simp only [List.length_take]; exact Nat.min_le_right _ _
    have hl := list_length_le_code z.1
    simp only [encode_nat,unary_length,encode_prod,pairBits_length,eval_X]
    omega)
  have hh : Poly (fun l : List α => l.foldl (fun b _ => b+1) 0) :=
    comp _ (fun l : List α => (l,0)) hfold (by fun_prop)
  exact hh.congr (fun l => by simp)

end Poly
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.MapRoutine -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma element_code_le {α : Type} [Coding α] (l : List α) (a : α) (ha : a∈l) :
    (encode a).length≤(encode l).length := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.mem_cons] at ha
    simp only [code_cons,pairBits_length]
    rcases ha with rfl | ha
    · omega
    · have hh := ih ha; omega

lemma list_code_bound {α : Type} [Coding α] (l : List α) (M : ℕ)
    (hb : ∀ a∈l,(encode a).length≤M) : (encode l).length≤l.length*(2*M+1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hb a (by simp)
    have hl := ih (fun a ha => hb a (List.mem_cons_of_mem _ ha))
    simp only [code_cons,pairBits_length,List.length_cons]
    nlinarith

lemma code_reverse_length {α : Type} [Coding α] (l : List α) :
    (encode l.reverse).length=(encode l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.reverse_cons,code_append,pairBits_length,ih]; omega

lemma append_map_fold {α β : Type} (f : α → β) (l : List α) (b : List β) :
    l.foldl (fun b a => b++[f a]) b=b++l.map f := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih,List.append_assoc]

lemma append_fold {α : Type} (l : List (List α)) (b : List α) :
    l.foldl (fun b a => b++a) b=b++l.flatten := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [ih,List.append_assoc]

lemma code_flatten_le {α : Type} [Coding α] (l : List (List α)) :
    (encode l.flatten).length≤(encode l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatten_cons,code_append,List.length_append,code_cons,pairBits_length]; omega

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem listMap [Inhabited α] (f : α → β) (hf : Poly f) : Poly (List.map f) := by
  let p := hf.routine.time
  have hs : Poly (fun z : List β×α => z.1++[f z.2]) := by fun_prop
  have hfold := listFold (default:α) (fun z : List β×α => z.1++[f z.2]) hs
    (X+X*(2*(X+p)+1)) (by
      intro z k
      rw [append_map_fold,code_append,List.length_append]
      let N := (encode z).length
      have help : ∀ a∈z.1.take k,(encode a).length≤N := by
        intro a ha
        have hh := element_code_le z.1 a (List.mem_of_mem_take ha)
        simp only [N,encode_prod,pairBits_length]
        omega
      have hb : ∀ b∈(z.1.take k).map f,(encode b).length≤N+p.eval N := by
        intro b hb
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
        have ht := hf.routine.length_bound a
        have hh := help a ha
        have hm := polynomial_eval_mono p hh
        exact ht.trans (Nat.add_le_add hh hm)
      have hmap := list_code_bound ((z.1.take k).map f) (N+p.eval N) hb
      have ht : (z.1.take k).length≤N := (show (z.1.take k).length≤z.1.length by simp only [List.length_take]; exact Nat.min_le_right _ _).trans
        ((list_length_le_code z.1).trans (by simp only [N,encode_prod,pairBits_length]; omega))
      have hmul := Nat.mul_le_mul_right (2*(N+p.eval N)+1) ht
      simp only [List.length_map] at hmap
      have hb₀ : (encode z.2).length≤N := by simp only [N,encode_prod,pairBits_length]; omega
      simp only [eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
      change (encode z.2).length+(encode ((z.1.take k).map f)).length≤N+N*(2*(N+p.eval N)+1)
      omega)
  have hh : Poly (fun l : List α => l.foldl (fun b a => b++[f a]) []) :=
    comp _ (fun l : List α => (l,[])) hfold (by fun_prop)
  exact hh.congr (fun l => by rw [append_map_fold,List.nil_append])

@[fun_prop] theorem listFlatten : Poly (List.flatten : List (List α) → List α) := by
  have hs : Poly (fun z : List α×List α => z.1++z.2) := by fun_prop
  have hfold := listFold ([]:List α) (fun z : List α×List α => z.1++z.2) hs X (by
    intro z k
    rw [append_fold,code_append,List.length_append]
    have h₁ := code_flatten_le (z.1.take k)
    have h₂ : (encode (z.1.take k)).length≤(encode z.1).length := by
      have hh := congrArg (fun l => (encode l).length) (List.take_append_drop k z.1)
      rw [code_append,List.length_append] at hh
      omega
    simp only [eval_X,encode_prod,pairBits_length]
    omega)
  have hh : Poly (fun l : List (List α) => l.foldl (fun b a => b++a) []) :=
    comp _ (fun l : List (List α) => (l,[])) hfold (by fun_prop)
  exact hh.congr (fun l => by simp [append_fold])

@[fun_prop] theorem listFlatMap [Inhabited α] (f : α → List β) (hf : Poly f) :
    Poly (List.flatMap f) := by
  have hm := listMap f hf
  have hl : Poly (List.flatten : List (List β) → List β) := listFlatten
  have hh : Poly (fun l : List α => (l.map f).flatten) := comp _ _ hl hm
  exact hh

@[fun_prop] theorem listFilter [Inhabited α] (f : α → Bool) (hf : Poly f) :
    Poly (List.filter f) := by
  have hs : Poly (fun a => if f a then [a] else []) := by fun_prop
  have hh := listFlatMap (fun a => if f a then [a] else []) hs
  exact hh.congr (fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.filter_cons,ih]; split <;> simp_all)

end Poly
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.SequenceRoutine -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma code_take_le {α : Type} [Coding α] (l : List α) (n : ℕ) :
    (encode (l.take n)).length≤(encode l).length := by
  have h := congrArg (fun xs => (encode xs).length) (List.take_append_drop n l)
  rw [code_append,List.length_append] at h
  omega

lemma code_replicate {α : Type} [Coding α] (a : α) (n : ℕ) :
    (encode (List.replicate n a)).length=n*(2*(encode a).length+1) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ,code_cons,pairBits_length,ih]; nlinarith

def dupStep {α : Type} (z : α×List α) : α×List α := (z.1,z.1::z.2)
lemma dupStep_iterate {α : Type} (n : ℕ) (z : α×List α) :
    dupStep^[n] z=(z.1,List.replicate n z.1++z.2) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply',ih,dupStep,List.replicate_succ]

lemma code_zip_bound {α β : Type} [Coding α] [Coding β] (l : List α) (m : List β) :
    (encode (l.zip m)).length≤2*(encode l).length+(encode m).length := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    cases m with
    | nil => simp
    | cons b m =>
      have h := ih m
      simp only [List.zip_cons_cons,code_cons,encode_prod,pairBits_length]
      omega

def zipStep {α β : Type} [Inhabited α] [Inhabited β]
    (z : List α×(List β×List (α×β))) : List α×(List β×List (α×β)) :=
  (z.1.tail,z.2.1.tail,if z.1.isEmpty || z.2.1.isEmpty then z.2.2
    else z.2.2++[(z.1.headD default,z.2.1.headD default)])

lemma zipStep_iterate {α β : Type} [Inhabited α] [Inhabited β]
    (n : ℕ) (z : List α×(List β×List (α×β))) :
    zipStep^[n] z=(z.1.drop n,z.2.1.drop n,
      z.2.2++(z.1.take n).zip (z.2.1.take n)) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rcases z with ⟨l,m,o⟩
    cases l <;> cases m <;>
      simp [Function.iterate_succ_apply,zipStep,ih,List.append_assoc]

lemma zip_take_right_of_ge {α β : Type} (l : List α) (m : List β) (n : ℕ)
    (hn : l.length≤n) : l.zip (m.take n)=l.zip m := by
  induction l generalizing m n with
  | nil => simp
  | cons a l ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      cases m with
      | nil => simp
      | cons b m => simp only [List.take_succ_cons,List.zip_cons_cons,ih m n (by simpa using hn)]

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem listReplicate : Poly (fun z : ℕ×α => List.replicate z.1 z.2) := by
  have hs : Poly (dupStep : α×List α → α×List α) := by unfold dupStep; fun_prop
  have hi : Poly (fun z : ℕ×(α×List α) => dupStep^[z.1] z.2) :=
    boundedIterate dupStep hs ((X+1)^2) (by
      intro z j hj
      rw [dupStep_iterate]
      simp only [encode_prod,pairBits_length,code_append,List.length_append,code_replicate,
        encode_nat,unary_length,eval_pow,eval_add,eval_X,eval_one]
      have hm := Nat.mul_le_mul_right (2*(encode z.2.1).length+1) hj
      nlinarith)
  have h : Poly (fun z : ℕ×α => (dupStep^[z.1] (z.2,[])).2) :=
    second _ (comp _ (fun z : ℕ×α => (z.1,(z.2,[]))) hi (by fun_prop))
  exact h.congr (fun z => by simp [dupStep_iterate])

@[fun_prop] theorem listZip [Inhabited α] [Inhabited β] :
    Poly (fun z : List α×List β => z.1.zip z.2) := by
  have hs : Poly (zipStep : List α×(List β×List (α×β)) → _) := by unfold zipStep; fun_prop
  have hi : Poly (fun z : ℕ×(List α×(List β×List (α×β))) => zipStep^[z.1] z.2) :=
    boundedIterate zipStep hs (2*X) (by
      intro z j hj
      rw [zipStep_iterate]
      have h₁ := code_drop_le z.2.1 j
      have h₂ := code_drop_le z.2.2.1 j
      have h₃ := code_take_le z.2.1 j
      have h₄ := code_take_le z.2.2.1 j
      have h₅ := code_zip_bound (z.2.1.take j) (z.2.2.1.take j)
      simp only [encode_prod,pairBits_length,code_append,List.length_append,encode_nat,unary_length,
        eval_mul,eval_ofNat,eval_X]
      omega)
  have h : Poly (fun z : List α×List β => (zipStep^[(encode z.1).length] (z.1,z.2,[])).2.2) := by
    apply second
    apply second
    apply comp _ (fun z : List α×List β => ((encode z.1).length,(z.1,z.2,[]))) hi
    apply pair
    · exact comp _ Prod.fst codeLength (first _ identity)
    · fun_prop
  exact h.congr (fun z => by
    rw [zipStep_iterate]
    simp only [List.nil_append,List.take_of_length_le (list_length_le_code z.1)]
    exact zip_take_right_of_ge z.1 z.2 _ (list_length_le_code z.1))

@[fun_prop] theorem listMapParam [Inhabited α] [Inhabited γ]
    (f : γ×α → β) (hf : Poly f) : Poly (fun z : γ×List α => z.2.map (fun a => f (z.1,a))) := by
  have hm : Poly (List.map f) := listMap f hf
  have h : Poly (fun z : γ×List α => (List.zip (List.replicate z.2.length z.1) z.2).map f) := by fun_prop
  exact h.congr (fun z => by
    have hz : List.zip (List.replicate z.2.length z.1) z.2=z.2.map (fun a => (z.1,a)) := by
      induction z.2 with
      | nil => rfl
      | cons a l ih => simpa only [List.length_cons,List.replicate_succ,List.zip_cons_cons,List.map_cons] using congrArg (List.cons (z.1,a)) ih
    simp [hz,List.map_map,Function.comp_def])

end Poly
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.OrbitRoutine -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Poly
variable {α β γ δ : Type} [Coding α] [Coding β] [Coding γ] [Coding δ]

theorem reindex {f : α → β} (hf : Poly f) (g : γ → δ) (i : γ → α)
    (hin : ∀ x,encode x=encode (i x))
    (hout : ∀ x,encode (f (i x))=encode (g x)) : Poly g :=
  ⟨hf.routine.reindex encode encode g i (fun x => (hin x).symm) hout⟩

theorem iterateFrom (step : α → α) (hs : Poly step) (count : β → ℕ) (initial : β → α)
    (hc : Poly count) (hi : Poly initial) (P : Polynomial ℕ)
    (hb : ∀ b j,j≤count b → (encode (step^[j] (initial b))).length≤
      P.eval (encode (count b,initial b)).length) :
    Poly (fun b => step^[count b] (initial b)) := by
  let paired := (pair count initial hc hi).routine
  let setup : Routine encode (fun b => encode (count b,initial b)) (id : β → β) :=
    paired.reindex encode (fun b => encode (count b,initial b)) id id
      (fun _ => rfl) (fun _ => rfl)
  exact ⟨setup.comp (hs.routine.boundedIterate count initial P hb)⟩

end Poly
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.SumRoutine -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode

instance {α : Type} [Coding α] : Coding (Option α) := ⟨fun x => encode x.toList⟩
instance {α β : Type} [Coding α] [Coding β] : Coding (Sum α β) :=
  ⟨fun x => match x with | .inl a => encode ([a],([]:List β)) | .inr b => encode (([]:List α),[b])⟩

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem some : Poly (Option.some : α → Option α) := by
  have h : Poly (fun a : α => [a]) := by fun_prop
  exact h.reindex Option.some id (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem optionToList : Poly (Option.toList : Option α → List α) :=
  identity.reindex Option.toList Option.toList (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem optionGetD (a : α) : Poly (fun x : Option α => x.getD a) := by
  have h : Poly (fun x : Option α => x.toList.headD a) := comp _ _ (listHeadD a) optionToList
  exact h.congr (fun x => by cases x <;> rfl)

@[fun_prop] theorem optionIsSome : Poly (Option.isSome : Option α → Bool) := by
  have h : Poly (fun x : Option α => !x.toList.isEmpty) := by fun_prop
  exact h.congr (fun x => by cases x <;> rfl)

@[fun_prop] theorem optionMap [Inhabited α] (f : α → β) (hf : Poly f) :
    Poly (Option.map f) := by
  have h : Poly (fun x : Option α => x.toList.map f) := by fun_prop
  exact h.reindex (Option.map f) id (fun _ => rfl) (fun x => by cases x <;> rfl)

@[fun_prop] theorem optionElim [Inhabited α] (b : β) (f : α → β) (hf : Poly f) :
    Poly (fun x : Option α => x.elim b f) := by
  have h : Poly (fun x : Option α => if x.isSome then f (x.getD default) else b) := by fun_prop
  exact h.congr (fun x => by cases x <;> rfl)

@[fun_prop] theorem sumInl : Poly (Sum.inl : α → Sum α β) := by
  have h : Poly (fun a : α => ([a],([]:List β))) := by fun_prop
  exact h.reindex Sum.inl id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem sumInr : Poly (Sum.inr : β → Sum α β) := by
  have h : Poly (fun b : β => (([]:List α),[b])) := by fun_prop
  exact h.reindex Sum.inr id (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem sumCases [Inhabited α] [Inhabited β]
    (f : α → γ) (g : β → γ) (hf : Poly f) (hg : Poly g) :
    Poly (Sum.elim f g) := by
  let repr : Sum α β → List α×List β :=
    fun x => match x with | .inl a => ([a],[]) | .inr b => ([],[b])
  have h : Poly (fun z : List α×List β => if z.1.isEmpty then g (z.2.headD default)
      else f (z.1.headD default)) := by fun_prop
  exact h.reindex (Sum.elim f g) repr (fun x => by cases x <;> rfl)
    (fun x => by cases x <;> rfl)

end Poly
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.UnaryDivision -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma bounded_stops {α : Type} (f : α → α) (active : α → Bool) (rank : α → ℕ)
    (hfix : ∀ a,active a=false → f a=a)
    (hdec : ∀ a,active a=true → rank (f a)+1≤rank a) :
    ∀ n a,rank a≤n → active (f^[n] a)=false := by
  intro n
  induction n with
  | zero =>
    intro a ha
    cases h : active a with
    | false => simpa using h
    | true => have hh := hdec a h; omega
  | succ n ih =>
    intro a ha
    cases h : active a with
    | false => rw [Function.iterate_fixed (hfix a h)]; exact h
    | true =>
      rw [Function.iterate_succ_apply]
      apply ih
      have hh := hdec a h
      omega

def divActive (z : ℕ×(ℕ×ℕ)) : Bool := decide (0<z.1) && decide (z.1≤z.2.1)
def divStep (z : ℕ×(ℕ×ℕ)) : ℕ×(ℕ×ℕ) :=
  if divActive z then (z.1,(z.2.1-z.1,z.2.2+1)) else z

lemma divStep_spec (z : ℕ×(ℕ×ℕ)) :
    (divStep z).1=z.1 ∧ (divStep z).2.1≤z.2.1 ∧ (divStep z).2.2≤z.2.2+1 ∧
      (divStep z).2.1+z.1*(divStep z).2.2=z.2.1+z.1*z.2.2 := by
  unfold divStep
  split_ifs with h
  · have hz : 0<z.1 ∧ z.1≤z.2.1 := by simpa [divActive] using h
    have he := Nat.sub_add_cancel hz.2
    dsimp only
    refine ⟨rfl,Nat.sub_le _ _,le_rfl,?_⟩
    nlinarith
  · simp

lemma divIterate_spec (n : ℕ) (z : ℕ×(ℕ×ℕ)) :
    (divStep^[n] z).1=z.1 ∧ (divStep^[n] z).2.1≤z.2.1 ∧ (divStep^[n] z).2.2≤z.2.2+n ∧
      (divStep^[n] z).2.1+z.1*(divStep^[n] z).2.2=z.2.1+z.1*z.2.2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h₁,h₂,h₃,h₄⟩ := divStep_spec (divStep^[n] z)
    rw [ih.1] at h₁ h₄
    exact ⟨h₁,h₂.trans ih.2.1,by omega,h₄.trans ih.2.2.2⟩

lemma divIterate_stops (n m : ℕ) : divActive (divStep^[n] (m,n,0))=false := by
  apply bounded_stops divStep divActive (fun z => z.2.1)
    (fun z hz => by simp [divStep,hz]) (fun z hz => ?_) n (m,n,0) le_rfl
  have hh : 0<z.1 ∧ z.1≤z.2.1 := by simpa [divActive] using hz
  simp only [divStep,hz,ite_true]
  omega

lemma divIterate_result (n m : ℕ) : (divStep^[n] (m,n,0)).2=(n%m,n/m) := by
  obtain ⟨hm,_,_,hh⟩ := divIterate_spec n (m,n,0)
  have hs := divIterate_stops n m
  by_cases hm0 : m=0
  · subst m
    have hf : divStep (0,n,0)=(0,n,0) := by simp [divStep,divActive]
    rw [Function.iterate_fixed hf]
    simp
  · have hr : (divStep^[n] (m,n,0) ).2.1 < m := by
      have hpos : 0 < m := Nat.pos_of_ne_zero hm0
      simpa [divActive,hm,hpos] using hs
    simp only [Nat.mul_zero,Nat.add_zero] at hh
    have hq : n/m=(divStep^[n] (m,n,0)).2.2 := by
      apply Nat.div_eq_of_lt_le
      · nlinarith
      · nlinarith
    apply Prod.ext
    · have hn := Nat.mod_add_div n m
      rw [hq] at hn
      omega
    · exact hq.symm

namespace Poly
@[fun_prop] theorem natDivMod : Poly (fun z : ℕ×ℕ => (z.1%z.2,z.1/z.2)) := by
  have hs : Poly divStep := by unfold divStep divActive; fun_prop
  have hi : Poly (fun z : ℕ×(ℕ×(ℕ×ℕ)) => divStep^[z.1] z.2) :=
    boundedIterate divStep hs X (by
      intro z j hj
      obtain ⟨h₁,h₂,h₃,_⟩ := divIterate_spec j z.2
      simp only [encode_prod,pairBits_length,encode_nat,unary_length,eval_X,h₁]
      omega)
  have hh : Poly (fun z : ℕ×ℕ => (divStep^[z.1] (z.2,z.1,0)).2) := by fun_prop
  exact hh.congr (fun z => divIterate_result z.1 z.2)

@[fun_prop] theorem natDiv : Poly (fun z : ℕ×ℕ => z.1/z.2) := by
  have h : Poly (fun z : ℕ×ℕ => (z.1%z.2,z.1/z.2).2) := second _ natDivMod
  exact h
@[fun_prop] theorem natMod : Poly (fun z : ℕ×ℕ => z.1%z.2) := by
  have h : Poly (fun z : ℕ×ℕ => (z.1%z.2,z.1/z.2).1) := first _ natDivMod
  exact h
end Poly
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.IntegerRoutine -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

def intParts (z : ℤ) : Bool×ℕ := (decide (z<0),z.natAbs)
def fromParts (p : Bool×ℕ) : ℤ := if p.1 then -(p.2:ℤ) else p.2
instance : Coding ℤ := ⟨fun z => encode (intParts z)⟩
@[simp] lemma encode_int (z : ℤ) : encode z=encode (intParts z) := rfl
lemma fromParts_parts (z : ℤ) : fromParts (intParts z)=z := by
  simp only [fromParts,intParts,decide_eq_true_eq]
  split_ifs with h
  · exact (Int.eq_neg_natAbs_of_nonpos (le_of_lt h)).symm
  · exact Int.natAbs_of_nonneg (le_of_not_gt h)

lemma intParts_nat (n : ℕ) : intParts (n:ℤ)=(false,n) := by
  have h : ¬ (n:ℤ)<0 := by omega
  simp [intParts,h]
lemma intParts_fromParts (p : Bool×ℕ) :
    intParts (fromParts p)=(p.1 && !(decide (p.2=0)),p.2) := by
  rcases p with ⟨b,n⟩
  cases b with
  | false => simp [fromParts,intParts_nat]
  | true =>
    by_cases hn : n=0
    · subst n; simp [intParts,fromParts]
    · simp [intParts,fromParts,Nat.pos_iff_ne_zero,hn]

namespace Poly
@[fun_prop] theorem intParts_poly : Poly intParts := by
  exact ⟨(Routine.identity (encode : Bool×ℕ → List Bool)).reindex encode encode intParts intParts
    (fun _ => rfl) (fun _ => rfl)⟩

@[fun_prop] theorem natCastInt : Poly (Int.ofNat : ℕ → ℤ) := by
  have h : Poly (fun n : ℕ => (false,n)) := by fun_prop
  refine ⟨h.routine.reindex encode encode Int.ofNat id (fun _ => rfl) ?_⟩
  intro n
  change encode (false,n)=encode (intParts (n:ℤ))
  rw [intParts_nat]

@[fun_prop] theorem natToInt : Poly (fun n : ℕ => (n:ℤ)) := natCastInt

@[fun_prop] theorem fromParts_poly : Poly fromParts := by
  have h : Poly (fun p : Bool×ℕ => (p.1 && !(decide (p.2=0)),p.2)) := by
    apply pair
    · exact comp _ _ boolAnd (pair _ _ (by fun_prop) (comp _ _ boolNot (comp _ _ natZeroTest (by fun_prop))))
    · fun_prop
  refine ⟨h.routine.reindex encode encode fromParts id (fun _ => rfl) ?_⟩
  intro p
  simp only [id_eq,encode_int,intParts_fromParts]

@[fun_prop] theorem intNatAbs : Poly (Int.natAbs : ℤ → ℕ) := by
  have h : Poly (fun z : ℤ => (intParts z).2) := second _ intParts_poly
  exact h

@[fun_prop] theorem intSign : Poly (fun z : ℤ => decide (z<0)) := by
  have h : Poly (fun z : ℤ => (intParts z).1) := first _ intParts_poly
  exact h

@[fun_prop] theorem intNeg : Poly (fun z : ℤ => -z) := by
  have h : Poly (fun z : ℤ => fromParts (!(intParts z).1,(intParts z).2)) := by fun_prop
  exact h.congr (fun z => by cases z <;> simp [intParts,fromParts])

def addParts (p : (Bool×ℕ)×(Bool×ℕ)) : ℤ :=
  if p.1.1 then
    if p.2.1 then fromParts (true,p.1.2+p.2.2)
    else if decide (p.2.2≤p.1.2) then fromParts (true,p.1.2-p.2.2)
    else fromParts (false,p.2.2-p.1.2)
  else if p.2.1 then
    if decide (p.1.2≤p.2.2) then fromParts (true,p.2.2-p.1.2)
    else fromParts (false,p.1.2-p.2.2)
  else fromParts (false,p.1.2+p.2.2)

lemma addParts_eq (p q : Bool×ℕ) : addParts (p,q)=fromParts p+fromParts q := by
  rcases p with ⟨b,n⟩; rcases q with ⟨c,m⟩
  cases b <;> cases c <;> simp only [addParts,fromParts,Bool.false_eq_true,ite_false,ite_true,
    decide_eq_true_eq]
  · omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · omega

@[fun_prop] theorem intAdd : Poly (fun z : ℤ×ℤ => z.1+z.2) := by
  have ha : Poly addParts := by unfold addParts; fun_prop
  have h : Poly (fun z : ℤ×ℤ => addParts (intParts z.1,intParts z.2)) := by fun_prop
  exact h.congr (fun z => by rw [addParts_eq,fromParts_parts,fromParts_parts])

@[fun_prop] theorem intSub : Poly (fun z : ℤ×ℤ => z.1-z.2) := by
  have h : Poly (fun z : ℤ×ℤ => z.1+ -z.2) := by fun_prop
  exact h.congr (fun z => sub_eq_add_neg _ _)

@[fun_prop] theorem intMul : Poly (fun z : ℤ×ℤ => z.1*z.2) := by
  have hm : Poly (fun p : (Bool×ℕ)×(Bool×ℕ) => fromParts
      (if p.1.1 then !p.2.1 else p.2.1,p.1.2*p.2.2)) := by fun_prop
  have hp : Poly (fun z : ℤ×ℤ => (intParts z.1,intParts z.2)) :=
    pair _ _ (comp _ Prod.fst intParts_poly (first _ identity))
      (comp _ Prod.snd intParts_poly (second _ identity))
  have h := comp _ _ hm hp
  have he (p q : Bool×ℕ) :
      fromParts (if p.1 then !q.1 else q.1,p.2*q.2)=fromParts p*fromParts q := by
    rcases p with ⟨b,n⟩; rcases q with ⟨c,m⟩
    cases b <;> cases c <;> simp [fromParts]
  exact h.congr (fun z => by dsimp only; rw [he,fromParts_parts,fromParts_parts])

@[fun_prop] theorem intLE : Poly (fun z : ℤ×ℤ => decide (z.1≤z.2)) := by
  have h : Poly (fun z : ℤ×ℤ => !(decide (z.2-z.1<0))) := by
    exact comp _ _ boolNot (comp _ _ intSign (comp _ (fun z : ℤ×ℤ => (z.2,z.1)) intSub (by fun_prop)))
  exact h.congr (fun z => by simp [←decide_not,sub_neg])

@[fun_prop] theorem intLT : Poly (fun z : ℤ×ℤ => decide (z.1<z.2)) := by
  have h : Poly (fun z : ℤ×ℤ => decide (z.1-z.2<0)) := comp _ _ intSign intSub
  exact h.congr (fun z => by simp [sub_neg])

@[fun_prop] theorem intEQ : Poly (fun z : ℤ×ℤ => decide (z.1=z.2)) := by
  have h : Poly (fun z : ℤ×ℤ => decide ((z.1-z.2).natAbs=0)) :=
    comp _ _ natZeroTest (comp _ _ intNatAbs intSub)
  exact h.congr (fun z => by simp [sub_eq_zero])

@[fun_prop] theorem intMin : Poly (fun z : ℤ×ℤ => min z.1 z.2) := by
  have h : Poly (fun z : ℤ×ℤ => if decide (z.1≤z.2) then z.1 else z.2) := by fun_prop
  exact h.congr (fun z => by simp [min_def])
@[fun_prop] theorem intMax : Poly (fun z : ℤ×ℤ => max z.1 z.2) := by
  have h : Poly (fun z : ℤ×ℤ => if decide (z.1≤z.2) then z.2 else z.1) := by fun_prop
  exact h.congr (fun z => by simp [max_def])
@[fun_prop] theorem intToNat : Poly (Int.toNat : ℤ → ℕ) := by
  have h : Poly (fun z : ℤ => if (intParts z).1 then 0 else (intParts z).2) := by fun_prop
  exact h.congr (fun z => by cases z <;> simp [intParts])
variable {α : Type} [Coding α]
@[fun_prop] theorem intLt_apply (f g : α → ℤ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a<g a)) := comp _ _ intLT (pair _ _ hf hg)
@[fun_prop] theorem intLe_apply (f g : α → ℤ) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => decide (f a≤g a)) := comp _ _ intLE (pair _ _ hf hg)
end Poly
end BinaryMatching.StackCode
end

end OAI

/- OAI.Computability.MatchingCount.ListNumeric -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. Imports narrowed for standalone reuse. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma code_option_none {α : Type} [Coding α] : encode (none:Option α)=[] := rfl
lemma code_option_some {α : Type} [Coding α] (a : α) :
    (encode (some a)).length=2*(encode a).length+1 := by
  change (encode ([a]:List α)).length=_
  simp

lemma fold_code_additive {α β : Type} [Coding α] [Coding β]
    (f : β×α → β) (C : ℕ)
    (hf : ∀ z,(encode (f z)).length≤(encode z.1).length+C*(2*(encode z.2).length+1))
    (l : List α) (b : β) :
    (encode (l.foldl (fun b a => f (b,a)) b)).length≤
      (encode b).length+C*(encode l).length := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    have h := hf (b,a)
    have hi := ih (f (b,a))
    simp only [List.foldl_cons,code_cons,pairBits_length]
    nlinarith

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

theorem listFoldAdd [Inhabited α] (f : β×α → β) (hf : Poly f) (C : ℕ)
    (hb : ∀ z,(encode (f z)).length≤(encode z.1).length+C*(2*(encode z.2).length+1)) :
    Poly (fun z : List α×β => z.1.foldl (fun b a => f (b,a)) z.2) := by
  apply listFold default f hf ((Polynomial.C C+1)*X)
  intro z k
  have hh := fold_code_additive f C hb (z.1.take k) z.2
  have ht := code_take_le z.1 k
  have hm := Nat.mul_le_mul_left C ht
  simp only [encode_prod,pairBits_length,eval_mul,eval_add,eval_C,eval_one,eval_X]
  nlinarith

@[fun_prop] theorem listDrop : Poly (fun z : ℕ×List α => z.2.drop z.1) := by
  have hi := boundedIterate (List.tail:List α → List α) listTail X (by
    intro z j hj
    have he : ∀ (k : ℕ) (l : List α),List.tail^[k] l=l.drop k := by
      intro k l
      induction k with
      | zero => simp
      | succ k ih => simp [Function.iterate_succ_apply',ih,List.tail_drop]
    rw [he]
    have hh := code_drop_le z.2 j
    simp only [encode_prod,pairBits_length,eval_X]
    omega)
  apply hi.congr
  intro z
  induction z.1 generalizing z with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply',ih,List.tail_drop]

@[fun_prop] theorem listGetD (a : α) : Poly (fun z : List α×ℕ => z.1[z.2]?.getD a) := by
  have h : Poly (fun z : List α×ℕ => (z.1.drop z.2).headD a) := by fun_prop
  exact h.congr (fun z => by simp only [List.headD_eq_head?_getD,List.head?_drop])

@[fun_prop] theorem listNatSum : Poly (List.sum : List ℕ → ℕ) := by
  have hfold := listFoldAdd (fun z : ℕ×ℕ => z.1+z.2) natAdd 1 (by
    intro z; simp only [encode_nat,unary_length]; omega)
  have h : Poly (fun l : List ℕ => l.foldl (·+·) 0) := comp _ (fun l : List ℕ => (l,0)) hfold (by fun_prop)
  exact h.congr (fun l => by simp [List.sum_eq_foldl])

@[fun_prop] theorem listIntSum : Poly (List.sum : List ℤ → ℤ) := by
  have hfold := listFoldAdd (fun z : ℤ×ℤ => z.1+z.2) intAdd 1 (by
    intro z
    have h := Int.natAbs_add_le z.1 z.2
    simp only [encode_int,encode_prod,pairBits_length,intParts,encode_bool,List.length_singleton,
      encode_nat,unary_length]
    omega)
  have h : Poly (fun l : List ℤ => l.foldl (·+·) 0) := comp _ (fun l : List ℤ => (l,0)) hfold (by fun_prop)
  exact h.congr (fun l => by simp [List.sum_eq_foldl])

end Poly

def rangeStep (z : ℕ×List ℕ) : ℕ×List ℕ := (z.1+1,z.2++[z.1])
lemma rangeStep_iterate (k : ℕ) (z : ℕ×List ℕ) :
    rangeStep^[k] z=(z.1+k,z.2++List.range' z.1 k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [Function.iterate_succ_apply',ih,rangeStep,List.range'_concat,List.append_assoc,Nat.add_assoc]

namespace Poly
@[fun_prop] theorem listRange : Poly List.range := by
  have hs : Poly rangeStep := by unfold rangeStep; fun_prop
  have hi : Poly (fun z : ℕ×(ℕ×List ℕ) => rangeStep^[z.1] z.2) :=
    boundedIterate rangeStep hs (8*(X+1)^2) (by
      intro z j hj
      rw [rangeStep_iterate]
      have hb := list_code_bound (List.range' z.2.1 j) (z.2.1+j) (by
        intro a ha
        obtain ⟨i,hi,he⟩ := List.mem_range'.mp ha
        simp only [encode_nat,unary_length]
        omega)
      simp only [List.length_range'] at hb
      simp only [encode_prod,pairBits_length,encode_nat,unary_length,code_append,List.length_append,
        eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
      nlinarith [Nat.mul_le_mul hj hj, Nat.mul_le_mul_right z.2.1 hj])
  have h : Poly (fun n : ℕ => (rangeStep^[n] (0,[])).2) := by fun_prop
  exact h.congr (fun n => by simp [rangeStep_iterate,List.range_eq_range'])
end Poly
end BinaryMatching.StackCode
end

end OAI

/- BinaryWeights -/
set_option autoImplicit false
namespace WeightedUDNF.BinaryWeights
open OAI.BinaryMatching.StackCode
open Polynomial

/-- Little-endian words, permitting leading zeroes. -/
def value : List Bool → Nat
  | [] => 0
  | b :: xs => (if b then 1 else 0) + 2 * value xs

/-- Adapted from openai/math RationalHitting/StackWords.lean, Apache-2.0. -/
def increment : List Bool → List Bool
  | [] => [true]
  | false :: xs => true :: xs
  | true :: xs => false :: increment xs

@[simp] theorem increment_value (xs : List Bool) : value (increment xs) = value xs + 1 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [increment, value, ih] <;> omega

theorem increment_length (xs : List Bool) : (increment xs).length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [increment]
  | cons b xs ih => cases b <;> simp [increment] <;> omega

@[simp] theorem code_bits_length (xs : List Bool) : (encode xs).length = 3 * xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [code_cons, pairBits_length, encode_bool,
      List.length_singleton, List.length_cons, List.length_nil, ih]; omega

@[fun_prop] theorem reverse_poly : Poly (List.reverse : List Bool → List Bool) := by
  have hf : Poly (fun z : List Bool × Bool => z.2 :: z.1) := by fun_prop
  have hfold := Poly.listFoldAdd (fun z : List Bool × Bool => z.2 :: z.1) hf 1 (by
    intro z
    simp only [code_cons, pairBits_length, encode_bool, List.length_singleton]
    omega)
  have h : Poly (fun xs : List Bool => xs.foldl (fun acc b => b :: acc) []) :=
    Poly.comp _ (fun xs : List Bool => (xs, [])) hfold (by fun_prop)
  exact h.congr (fun xs => by simp)

def incStep (z : (List Bool × List Bool) × Bool) : List Bool × List Bool :=
  (z.2 :: z.1.1, if z.2 then false :: z.1.2 else true :: z.1.1)

@[fun_prop] theorem incStep_poly : Poly incStep := by unfold incStep; fun_prop

theorem incFold_bound (xs : List Bool) (z : List Bool × List Bool) :
    let r := xs.foldl (fun acc b => incStep (acc, b)) z
    max r.1.length r.2.length ≤ max z.1.length z.2.length + xs.length := by
  induction xs generalizing z with
  | nil => simp
  | cons b xs ih =>
    have hi := ih (incStep (z, b))
    have hs : max (incStep (z, b)).1.length (incStep (z, b)).2.length ≤
        max z.1.length z.2.length + 1 := by
      cases b <;> simp [incStep] <;> omega
    simp only [List.foldl_cons, List.length_cons]
    exact hi.trans (by omega)

@[fun_prop] theorem incFold_poly :
    Poly (fun z : List Bool × (List Bool × List Bool) =>
      z.1.foldl (fun acc b => incStep (acc, b)) z.2) := by
  apply Poly.listFold false incStep incStep_poly (10 * (X + 1))
  intro z k
  have h := incFold_bound (z.1.take k) z.2
  have ht : (z.1.take k).length ≤ z.1.length := by simp
  dsimp only at h
  simp only [encode_prod, pairBits_length, code_bits_length,
    eval_mul, eval_ofNat, eval_add, eval_X, eval_one] at *
  omega

theorem incFold_spec (xs : List Bool) :
    xs.reverse.foldl (fun acc b => incStep (acc, b)) ([], [true]) = (xs, increment xs) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    cases b <;> rfl

@[fun_prop] theorem increment_poly : Poly increment := by
  have h : Poly (fun xs : List Bool =>
      (xs.reverse.foldl (fun acc b => incStep (acc, b)) ([], [true])).2) := by
    apply Poly.second
    exact Poly.comp _ (fun xs : List Bool => (xs.reverse, ([], [true]))) incFold_poly (by fun_prop)
  exact h.congr (fun xs => congrArg Prod.snd (incFold_spec xs))

/-- Adapted from openai/math RationalHitting/BinaryAddition.lean, Apache-2.0. -/
def add : List Bool → List Bool → List Bool
  | a, [] => a
  | a, false :: b => a.headD false :: add a.tail b
  | a, true :: b => (increment a).headD false :: add (increment a).tail b

theorem value_head_tail (a : List Bool) :
    value a = (if a.headD false then 1 else 0) + 2 * value a.tail := by
  cases a <;> rfl

@[simp] theorem add_value (a b : List Bool) : value (add a b) = value a + value b := by
  induction b generalizing a with
  | nil => simp [add, value]
  | cons x b ih =>
    cases x with
    | false =>
      simp only [add, value, Bool.false_eq_true, ↓reduceIte, zero_add, ih]
      rw [value_head_tail a]
      omega
    | true =>
      simp only [add, value, ↓reduceIte, ih]
      have hh := value_head_tail (increment a)
      rw [increment_value] at hh
      omega

theorem increment_tail_length (a : List Bool) : (increment a).tail.length ≤ a.length := by
  have h := increment_length a
  simp only [List.length_tail]
  omega

theorem add_length (a b : List Bool) : (add a b).length ≤ a.length + b.length := by
  induction b generalizing a with
  | nil => simp [add]
  | cons x b ih =>
    cases x with
    | false =>
      have h := ih a.tail
      simp only [add, List.length_cons]
      have ht : a.tail.length ≤ a.length := by simp
      omega
    | true =>
      have h := ih (increment a).tail
      have ht := increment_tail_length a
      simp only [add, List.length_cons]
      omega

def addStep (z : (List Bool × List Bool) × Bool) : List Bool × List Bool :=
  let a := if z.2 then increment z.1.1 else z.1.1
  (a.tail, z.1.2 ++ [a.headD false])

@[fun_prop] theorem addStep_poly : Poly addStep := by
  unfold addStep
  fun_prop

@[fun_prop] theorem addFold_poly :
    Poly (fun z : List Bool × (List Bool × List Bool) =>
      z.1.foldl (fun acc b => addStep (acc, b)) z.2) := by
  apply Poly.listFoldAdd addStep addStep_poly 1
  intro z
  rcases z with ⟨⟨a, out⟩, b⟩
  have hi := increment_tail_length a
  have ht : a.tail.length ≤ a.length := by simp
  cases b <;>
    simp only [addStep, Bool.false_eq_true, ↓reduceIte, encode_prod, pairBits_length,
      code_bits_length, List.length_append, List.length_singleton, encode_bool] <;> omega

theorem addFold_spec (a out b : List Bool) :
    let r := b.foldl (fun acc x => addStep (acc, x)) (a, out)
    r.2 ++ r.1 = out ++ add a b := by
  induction b generalizing a out with
  | nil => rfl
  | cons x b ih =>
    cases x <;> simp only [List.foldl_cons, addStep, Bool.false_eq_true, ↓reduceIte]
    · simpa [add, addStep, List.append_assoc] using ih a.tail (out ++ [a.headD false])
    · simpa [add, addStep, List.append_assoc] using ih (increment a).tail (out ++ [(increment a).headD false])

@[fun_prop] theorem add_poly : Poly (fun z : List Bool × List Bool => add z.1 z.2) := by
  have hp : Poly (fun z : List Bool × List Bool =>
      z.2.foldl (fun acc b => addStep (acc, b)) (z.1, [])) :=
    Poly.comp _ (fun z : List Bool × List Bool => (z.2, (z.1, []))) addFold_poly (by fun_prop)
  have hh : Poly (fun z : List Bool × List Bool =>
      let r := z.2.foldl (fun acc b => addStep (acc, b)) (z.1, [])
      r.2 ++ r.1) := by fun_prop
  exact hh.congr (fun z => by simpa using addFold_spec z.1 [] z.2)

def compareStep (z : List Bool × List Bool × Bool) : List Bool × List Bool × Bool :=
  (z.1.tail, z.2.1.tail,
    if z.1.headD false then (if z.2.1.headD false then z.2.2 else false)
    else (if z.2.1.headD false then true else z.2.2))

@[fun_prop] theorem compareStep_poly : Poly compareStep := by unfold compareStep; fun_prop

theorem compareStep_size (z : List Bool × List Bool × Bool) :
    (encode (compareStep z)).length ≤ (encode z).length := by
  have ha : z.1.tail.length ≤ z.1.length := by simp
  have hb : z.2.1.tail.length ≤ z.2.1.length := by simp
  simp only [compareStep, encode_prod, pairBits_length, code_bits_length,
    encode_bool, List.length_singleton]
  omega

theorem compareIterate_size (n : Nat) (z : List Bool × List Bool × Bool) :
    (encode (compareStep^[n] z)).length ≤ (encode z).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (compareStep_size _).trans ih

@[fun_prop] theorem compareIterate_poly :
    Poly (fun z : Nat × (List Bool × List Bool × Bool) => compareStep^[z.1] z.2) := by
  apply Poly.boundedIterate compareStep compareStep_poly X
  intro z j hj
  have h := compareIterate_size j z.2
  simp only [encode_prod, pairBits_length, eval_X] at *
  omega

theorem compareIterate_correct (n : Nat) (a b : List Bool) (c : Bool)
    (ha : a.length ≤ n) (hb : b.length ≤ n) :
    (compareStep^[n] (a,b,c)).2.2 = true ↔ value a + (if c then 0 else 1) ≤ value b := by
  induction n generalizing a b c with
  | zero =>
    have he : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hf : b = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst a; subst b
    cases c <;> simp [value]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (compareStep^[n] (a.tail, b.tail,
      if a.headD false then (if b.headD false then c else false)
      else (if b.headD false then true else c))).2.2 = true ↔ _
    rw [ih _ _ _ (by simp only [List.length_tail]; omega)
      (by simp only [List.length_tail]; omega)]
    have hv₁ := value_head_tail a
    have hv₂ := value_head_tail b
    cases he : a.headD false <;> cases hf : b.headD false <;> cases c <;>
      simp only [he, hf, Bool.false_eq_true, ↓reduceIte] at * <;> omega

def le (a b : List Bool) : Bool :=
  (compareStep^[max a.length b.length] (a,b,true)).2.2

theorem le_correct (a b : List Bool) : le a b = true ↔ value a ≤ value b := by
  simpa only [le, ↓reduceIte, Nat.add_zero] using
    compareIterate_correct (max a.length b.length) a b true (Nat.le_max_left _ _) (Nat.le_max_right _ _)

@[fun_prop] theorem le_poly : Poly (fun z : List Bool × List Bool => le z.1 z.2) := by
  unfold le
  apply Poly.second
  apply Poly.second
  exact Poly.comp _ (fun z : List Bool × List Bool => (max z.1.length z.2.length, (z.1,z.2,true)))
    compareIterate_poly (by fun_prop)

end WeightedUDNF.BinaryWeights

/- PolyLists -/
set_option autoImplicit false
namespace WeightedUDNF.PolyLists
open OAI.BinaryMatching.StackCode
open Polynomial
variable {α : Type} [Coding α] [Inhabited α]

@[fun_prop] theorem reverse_poly : Poly (List.reverse : List α → List α) := by
  have hf : Poly (fun z : List α × α => z.2 :: z.1) := by fun_prop
  have hfold := Poly.listFoldAdd (fun z : List α × α => z.2 :: z.1) hf 1 (by
    intro z; simp only [code_cons, pairBits_length]; omega)
  have h : Poly (fun xs : List α => xs.foldl (fun acc b => b :: acc) []) :=
    Poly.comp _ (fun xs : List α => (xs, [])) hfold (by fun_prop)
  exact h.congr (fun xs => by simp)

@[fun_prop] theorem take_poly : Poly (fun z : Nat × List α => z.2.take z.1) := by
  have h : Poly (fun z : Nat × List α => (z.2.reverse.drop (z.2.length-z.1)).reverse) := by
    fun_prop
  exact h.congr (fun z => by simp [List.drop_reverse]; omega)

def prefixCount (xs : List Bool) : Nat := xs.foldr (fun b n => if b then n+1 else 0) 0

@[fun_prop] theorem prefixCount_poly : Poly prefixCount := by
  have hfold := Poly.listFoldAdd (fun z : Nat × Bool => if z.2 then z.1+1 else 0)
    (by fun_prop) 1 (by intro z; cases z.2 <;> simp [encode_nat, unary_length])
  have h : Poly (fun xs : List Bool => xs.reverse.foldl (fun n b => if b then n+1 else 0) 0) :=
    Poly.comp _ (fun xs : List Bool => (xs.reverse,0)) hfold (by fun_prop)
  exact h.congr (fun xs => by simp only [prefixCount, List.foldl_reverse])

theorem prefixCount_eq (xs : List Bool) : prefixCount xs = (xs.takeWhile id).length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [prefixCount, List.foldr_cons] at * <;> omega

@[fun_prop] theorem takeWhileParam_poly (p : α × α → Bool) (hp : Poly p) :
    Poly (fun z : α × List α => z.2.takeWhile (fun a => p (z.1,a))) := by
  have hm := Poly.listMapParam p hp
  have h : Poly (fun z : α × List α =>
      z.2.take (prefixCount (z.2.map (fun a => p (z.1,a))))) :=
    Poly.comp _ (fun z : α × List α => (prefixCount (z.2.map (fun a => p (z.1,a))), z.2))
      take_poly (Poly.pair _ _ (Poly.comp _ _ prefixCount_poly hm) (by fun_prop))
  exact h.congr (fun z => by
    rw [prefixCount_eq, List.takeWhile_map, List.length_map]
    change z.2.take (z.2.takeWhile (fun a => p (z.1,a))).length = _
    have he := congrArg (List.take (z.2.takeWhile (fun a => p (z.1,a))).length)
      (List.takeWhile_append_dropWhile (p := fun a => p (z.1,a)) (l := z.2))
    simpa only [List.take_left] using he.symm)

@[fun_prop] theorem dropWhileParam_poly (p : α × α → Bool) (hp : Poly p) :
    Poly (fun z : α × List α => z.2.dropWhile (fun a => p (z.1,a))) := by
  have ht := takeWhileParam_poly p hp
  have h : Poly (fun z : α × List α => z.2.drop (z.2.takeWhile (fun a => p (z.1,a))).length) :=
    Poly.comp _ (fun z : α × List α => ((z.2.takeWhile (fun a => p (z.1,a))).length,z.2))
      Poly.listDrop (Poly.pair _ _ (Poly.comp _ _ Poly.listLength ht) (by fun_prop))
  exact h.congr (fun z => by
    have he := congrArg (List.drop (z.2.takeWhile (fun a => p (z.1,a))).length)
      (List.takeWhile_append_dropWhile (p := fun a => p (z.1,a)) (l := z.2))
    simpa only [List.drop_left] using he.symm)

@[fun_prop] theorem orderedInsert_poly (p : α × α → Bool) (hp : Poly p) :
    Poly (fun z : α × List α => List.orderedInsert (fun a b => p (a,b) = true) z.1 z.2) := by
  have hn : Poly (fun z : α × α => !(p z)) := by fun_prop
  have ht := takeWhileParam_poly (fun z => !(p z)) hn
  have hd := dropWhileParam_poly (fun z => !(p z)) hn
  have h : Poly (fun z : α × List α =>
      z.2.takeWhile (fun a => !(p (z.1,a))) ++ z.1 :: z.2.dropWhile (fun a => !(p (z.1,a)))) := by
    apply Poly.comp _ (fun z : α × List α =>
      (z.2.takeWhile (fun a => !(p (z.1,a))),z.1 :: z.2.dropWhile (fun a => !(p (z.1,a))))) Poly.listAppend
    exact Poly.pair _ _ ht (Poly.comp _ (fun z : α × List α =>
      (z.1,z.2.dropWhile (fun a => !(p (z.1,a))))) Poly.listCons (Poly.pair _ _ (by fun_prop) hd))
  exact h.congr (fun z => by simp [List.orderedInsert_eq_take_drop])

theorem code_perm {xs ys : List α} (h : xs.Perm ys) : (encode xs).length = (encode ys).length := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [code_cons, pairBits_length, ih]
  | swap a b xs => simp only [code_cons, pairBits_length]; omega
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

@[fun_prop] theorem insertionSort_poly (p : α × α → Bool) (hp : Poly p) :
    Poly (List.insertionSort (fun a b => p (a,b) = true)) := by
  have hi := orderedInsert_poly p hp
  have hf : Poly (fun z : List α × α => List.orderedInsert (fun a b => p (a,b) = true) z.2 z.1) :=
    Poly.comp _ (fun z : List α × α => (z.2,z.1)) hi (by fun_prop)
  have hfold := Poly.listFoldAdd _ hf 1 (by
    intro z
    have he := code_perm (List.perm_orderedInsert (fun a b => p (a,b) = true) z.2 z.1)
    simp only [he, code_cons, pairBits_length]; omega)
  have h : Poly (fun xs : List α => xs.reverse.foldl
      (fun acc a => List.orderedInsert (fun a b => p (a,b) = true) a acc) []) :=
    Poly.comp _ (fun xs : List α => (xs.reverse,[])) hfold (by fun_prop)
  exact h.congr (fun xs => by simp only [List.insertionSort, List.foldl_reverse])

end WeightedUDNF.PolyLists

/- GF2Gaussian -/
set_option autoImplicit false
/- Adapted from openai/math, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Source: lean/OAI/ModelTheory/Choiceless/. Apache-2.0.
Changes: standalone imports; Gaussian scalar changed from ZMod 2 to ZMod 2;
query-specific definitions omitted. See SOURCE-NOTES.txt and LICENSE-openai-math. -/
set_option autoImplicit true

namespace OAI.CPTSeparation
abbrev Scalar := ZMod 2
end OAI.CPTSeparation


namespace OAI

namespace CPTSeparation.Gaussian

abbrev Scalar := ZMod 2

structure Row (n : ℕ) where
  coeff : Fin n → Scalar
  rhs : Scalar

namespace Row

def satisfies {n} (r : Row n) (v : Fin n → Scalar) : Prop :=
  (∑ i, r.coeff i * v i) = r.rhs

def tail {n} (r : Row (n+1)) : Row n := ⟨fun i => r.coeff i.succ,r.rhs⟩

def reduce {n} (p r : Row (n+1)) : Row n :=
  ⟨fun i => r.coeff i.succ - (r.coeff 0 / p.coeff 0)*p.coeff i.succ,
    r.rhs - (r.coeff 0 / p.coeff 0)*p.rhs⟩

lemma satisfies_cons {n} (r : Row (n+1)) (x : Scalar) (v : Fin n → Scalar) :
    r.satisfies (Fin.cons x v) ↔
      r.coeff 0*x + (∑ i, r.coeff i.succ * v i) = r.rhs := by
  simp [satisfies,Fin.sum_univ_succ]

lemma tail_iff {n} (r : Row (n+1)) (h : r.coeff 0 = 0) (x : Scalar) (v : Fin n → Scalar) :
    r.satisfies (Fin.cons x v) ↔ r.tail.satisfies v := by
  rw [satisfies_cons,h]
  simp [satisfies,tail]

lemma pivot_solution {n} (p : Row (n+1)) (hp : p.coeff 0 ≠ 0) (v : Fin n → Scalar) :
    p.satisfies (Fin.cons ((p.rhs - ∑ i, p.coeff i.succ * v i)/p.coeff 0) v) := by
  rw [satisfies_cons]
  field_simp
  ring

lemma reduce_iff {n} (p r : Row (n+1)) (hp : p.coeff 0 ≠ 0)
    (x : Scalar) (v : Fin n → Scalar) (hpx : p.satisfies (Fin.cons x v)) :
    r.satisfies (Fin.cons x v) ↔ (p.reduce r).satisfies v := by
  rw [satisfies_cons] at hpx ⊢
  simp only [satisfies,reduce,sub_mul,Finset.sum_sub_distrib,
    mul_assoc,← Finset.mul_sum]
  have h : (r.coeff 0 / p.coeff 0)*p.coeff 0 = r.coeff 0 := div_mul_cancel₀ _ hp
  have heq : r.coeff 0*x + ∑ i, r.coeff i.succ*v i - r.rhs =
      (∑ i, r.coeff i.succ*v i) - (r.coeff 0/p.coeff 0)*(∑ i, p.coeff i.succ*v i) -
        (r.rhs-(r.coeff 0/p.coeff 0)*p.rhs) := by
    rw [← hpx]
    linear_combination -(x*h)
  exact (sub_eq_zero.symm.trans (iff_of_eq (congrArg (fun z => z = 0) heq))).trans sub_eq_zero

end Row

def Solvable {n} (rows : List (Row n)) : Prop := ∃ v, ∀ r ∈ rows, r.satisfies v

def pivot {n} (rows : List (Row (n+1))) : Option (Row (n+1)) :=
  rows.find? (fun r => r.coeff 0 != 0)

def solve : {n : ℕ} → List (Row n) → Bool
  | 0, rows => rows.all (fun r => r.rhs == 0)
  | _+1, rows => match pivot rows with
    | none => solve (rows.map Row.tail)
    | some p => solve (rows.map (Row.reduce p))

lemma pivot_some {n} {rows : List (Row (n+1))} {p : Row (n+1)} (h : pivot rows = some p) :
    p ∈ rows ∧ p.coeff 0 ≠ 0 := by
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

lemma pivot_none {n} {rows : List (Row (n+1))} (h : pivot rows = none) :
    ∀ r ∈ rows, r.coeff 0 = 0 := by
  simpa [pivot,List.find?_eq_none] using h

lemma solvable_tail {n} {rows : List (Row (n+1))} (h : pivot rows = none) :
    Solvable rows ↔ Solvable (rows.map Row.tail) := by
  have hz := pivot_none h
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨fun i => v i.succ,?_⟩
    intro r hr
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    have hv' : Fin.cons (v 0) (fun i => v i.succ) = v := by ext i; cases i using Fin.cases <;> rfl
    exact (Row.tail_iff s (hz s hs) (v 0) _).mp (hv' ▸ hv s hs)
  · rintro ⟨v,hv⟩
    refine ⟨Fin.cons 0 v,?_⟩
    intro r hr
    exact (Row.tail_iff r (hz r hr) 0 v).mpr (hv _ (List.mem_map_of_mem hr))

lemma solvable_reduce {n} {rows : List (Row (n+1))} {p : Row (n+1)}
    (h : pivot rows = some p) : Solvable rows ↔ Solvable (rows.map (Row.reduce p)) := by
  obtain ⟨hpm,hp⟩ := pivot_some h
  constructor
  · rintro ⟨v,hv⟩
    have hv' : Fin.cons (v 0) (fun i => v i.succ) = v := by ext i; cases i using Fin.cases <;> rfl
    refine ⟨fun i => v i.succ,?_⟩
    intro r hr
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    exact (Row.reduce_iff p s hp (v 0) _ (hv' ▸ hv p hpm)).mp (hv' ▸ hv s hs)
  · rintro ⟨v,hv⟩
    let x := (p.rhs - ∑ i, p.coeff i.succ * v i)/p.coeff 0
    refine ⟨Fin.cons x v,?_⟩
    intro r hr
    exact (Row.reduce_iff p r hp x v (Row.pivot_solution p hp v)).mpr
      (hv _ (List.mem_map_of_mem hr))

theorem solve_correct {n} (rows : List (Row n)) : solve rows = true ↔ Solvable rows := by
  induction n with
  | zero =>
    simp only [solve,List.all_eq_true,beq_iff_eq]
    constructor
    · intro h
      exact ⟨Fin.elim0,fun r hr => by simpa [Row.satisfies] using (h r hr).symm⟩
    · rintro ⟨v,hv⟩ r hr
      simpa [Row.satisfies] using (hv r hr).symm
  | succ n ih =>
    cases hp : pivot rows with
    | none => simpa only [solve,hp] using (ih (rows.map Row.tail)).trans (solvable_tail hp).symm
    | some p => simpa only [solve,hp] using (ih (rows.map (Row.reduce p))).trans (solvable_reduce hp).symm

end CPTSeparation.Gaussian

namespace CPTSeparation.SerialGaussian

structure Row (n : ℕ) where
  coeff : List Scalar
  length_eq : coeff.length = n
  rhs : Scalar

def Row.decode {n} (r : Row n) : Gaussian.Row n :=
  ⟨fun i => r.coeff[i.val]'(by rw [r.length_eq]; exact i.isLt),r.rhs⟩

def Row.encode {n} (r : Gaussian.Row n) : Row n :=
  ⟨List.ofFn r.coeff,by simp,r.rhs⟩

def Row.head {n} (r : Row (n+1)) : Scalar := r.coeff.headD 0

def Row.tail {n} (r : Row (n+1)) : Row n :=
  ⟨r.coeff.tail,by simp [r.length_eq],r.rhs⟩

def Row.reduce {n} (p r : Row (n+1)) : Row n :=
  let c := r.head / p.head
  ⟨List.zipWith (fun x y => x-c*y) r.coeff.tail p.coeff.tail,
    by simp [r.length_eq,p.length_eq],r.rhs-c*p.rhs⟩

def pivot {n} (rows : List (Row (n+1))) : Option (Row (n+1)) :=
  rows.find? (fun r => r.head != 0)

def solve : {n : ℕ} → List (Row n) → Bool
  | 0,rows => rows.all (fun r => r.rhs == 0)
  | _+1,rows => match pivot rows with
    | none => solve (rows.map Row.tail)
    | some p => solve (rows.map (Row.reduce p))

@[simp] theorem Row.decode_encode {n} (r : Gaussian.Row n) : (Row.encode r).decode = r := by
  cases r
  simp only [Row.encode,Row.decode,List.getElem_ofFn]

@[simp] theorem Row.head_decode {n} (r : Row (n+1)) : r.head = r.decode.coeff 0 := by
  rcases r with ⟨l,h,b⟩
  cases l with
  | nil => simp at h
  | cons a l => rfl

@[simp] theorem Row.decode_tail {n} (r : Row (n+1)) : r.tail.decode = r.decode.tail := by
  apply congrArg₂ Gaussian.Row.mk
  · funext i
    simp [Row.decode,Row.tail]
  · rfl

@[simp] theorem Row.decode_reduce {n} (p r : Row (n+1)) :
    (p.reduce r).decode = p.decode.reduce r.decode := by
  apply congrArg₂ Gaussian.Row.mk
  · funext i
    simp [Row.decode,Row.reduce,List.getElem_zipWith,Row.head_decode]
  · simp [Row.decode,Row.reduce,Row.head_decode]

@[simp] theorem pivot_decode {n} (rows : List (Row (n+1))) :
    Gaussian.pivot (rows.map Row.decode) = (pivot rows).map Row.decode := by
  simp only [Gaussian.pivot,pivot,List.find?_map]
  congr 2
  funext r
  simp []

theorem solve_decode {n} (rows : List (Row n)) :
    solve rows = Gaussian.solve (rows.map Row.decode) := by
  induction n with
  | zero => simp [solve,Gaussian.solve,Row.decode,Function.comp_def]
  | succ n ih =>
    cases hp : pivot rows with
    | none => simp [solve,Gaussian.solve,pivot_decode,hp,ih,List.map_map,Function.comp_def]
    | some p => simp [solve,Gaussian.solve,pivot_decode,hp,ih,List.map_map,Function.comp_def]

def payload {n} (rows : List (Row n)) : List (Option Scalar) :=
  rows.flatMap (fun r => r.coeff.map some ++ [some r.rhs,none])

theorem payload_length {n} (rows : List (Row n)) :
    (payload rows).length = rows.length*(n+2) := by
  induction rows with
  | nil => simp [payload]
  | cons r rs ih =>
    simp only [payload,List.flatMap_cons,List.length_append,List.length_map,
      r.length_eq,List.length_cons,List.length_nil] at *
    rw [Nat.add_mul]
    omega

theorem reduce_payload_size {n} (p : Row (n+1)) (rows : List (Row (n+1))) :
    (payload (rows.map (Row.reduce p))).length ≤ (payload rows).length := by
  simp only [payload_length,List.length_map]
  gcongr
  omega

theorem tail_payload_size {n} (rows : List (Row (n+1))) :
    (payload (rows.map Row.tail)).length ≤ (payload rows).length := by
  simp only [payload_length,List.length_map]
  gcongr
  omega

end CPTSeparation.SerialGaussian
end OAI

/- GF2Span -/
set_option autoImplicit false
/-! Connect the adapted executable GF(2) solver to span membership. -/
namespace WeightedUDNF.GF2Span
open OAI.CPTSeparation

abbrev Vec (d : Nat) := Fin d → Scalar

/-- One equation per coordinate, with one unknown per candidate generator. -/
def rows {d k : Nat} (vs : Fin k → Vec d) (v : Vec d) :
    List (SerialGaussian.Row k) :=
  List.ofFn fun j : Fin d =>
    SerialGaussian.Row.encode ⟨fun i => vs i j, v j⟩

def test {d k : Nat} (vs : Fin k → Vec d) (v : Vec d) : Bool :=
  SerialGaussian.solve (rows vs v)

theorem test_correct {d k : Nat} (vs : Fin k → Vec d) (v : Vec d) :
    test vs v = true ↔ v ∈ Submodule.span Scalar (Set.range vs) := by
  rw [test, SerialGaussian.solve_decode, Gaussian.solve_correct,
    Submodule.mem_span_range_iff_exists_fun]
  unfold Gaussian.Solvable
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    funext j
    have hr : SerialGaussian.Row.encode (⟨fun i => vs i j, v j⟩ : Gaussian.Row k)
        ∈ rows vs v := List.mem_ofFn.mpr ⟨j, rfl⟩
    have h := hc _ (List.mem_map.mpr ⟨_, hr, rfl⟩)
    simpa [SerialGaussian.Row.decode_encode, Gaussian.Row.satisfies,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
    have h := congrFun hc j
    simpa [SerialGaussian.Row.decode_encode, Gaussian.Row.satisfies,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h


end WeightedUDNF.GF2Span

/- PolyGaussian -/
set_option autoImplicit false
namespace WeightedUDNF.PolyGaussian
open OAI.BinaryMatching.StackCode
open OAI.CPTSeparation
open Polynomial

theorem scalar_cases (x : Scalar) : x = 0 ∨ x = 1 := by
  change Fin 2 at x
  rcases x with ⟨v, hv⟩
  have h : v = 0 ∨ v = 1 := by omega
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

instance : Coding Scalar := ⟨fun x => [decide (x = 1)]⟩

def fromBool (b : Bool) : Scalar := if b then 1 else 0

def toBool (x : Scalar) : Bool := decide (x = 1)

@[simp] theorem code_scalar_length (x : Scalar) : (encode x).length = 1 := rfl

@[simp] theorem fromBool_toBool (x : Scalar) : fromBool (toBool x) = x := by
  rcases scalar_cases x with h | h <;> simp [h, fromBool, toBool]

@[simp] theorem toBool_fromBool (b : Bool) : toBool (fromBool b) = b := by
  cases b <;> decide

@[fun_prop] theorem toBool_poly : Poly toBool := by
  exact ⟨(Routine.identity (fun b : Bool => [b])).reindex encode encode toBool toBool
    (fun _ => rfl) (fun _ => rfl)⟩

@[fun_prop] theorem fromBool_poly : Poly fromBool := by
  refine ⟨(Routine.identity (fun b : Bool => [b])).reindex encode encode fromBool id
    (fun _ => rfl) ?_⟩
  intro b
  change [b] = [toBool (fromBool b)]
  simp

@[fun_prop] theorem scalar_mul_poly : Poly (fun z : Scalar × Scalar => z.1 * z.2) := by
  have h : Poly (fun z : Scalar × Scalar => fromBool (toBool z.1 && toBool z.2)) := by fun_prop
  exact h.congr (fun z => by rcases z with ⟨a,b⟩; fin_cases a <;> fin_cases b <;> decide)

@[fun_prop] theorem scalar_sub_poly : Poly (fun z : Scalar × Scalar => z.1 - z.2) := by
  have h : Poly (fun z : Scalar × Scalar =>
      fromBool (if toBool z.1 then !(toBool z.2) else toBool z.2)) := by fun_prop
  exact h.congr (fun z => by rcases z with ⟨a,b⟩; fin_cases a <;> fin_cases b <;> decide)

@[fun_prop] theorem scalar_div_poly : Poly (fun z : Scalar × Scalar => z.1 / z.2) :=
  scalar_mul_poly.congr (fun z => by
    have h := scalar_cases z.2
    rcases h with h | h <;> simp [h])

@[fun_prop] theorem scalar_ne_zero_poly : Poly (fun x : Scalar => decide (x ≠ 0)) :=
  toBool_poly.congr (fun x => by fin_cases x <;> decide)

abbrev Row := List Scalar × Scalar

def reduceNonzero (z : Row × Row) : Row :=
  let c := z.2.1.headD 0 / z.1.1.headD 0
  ((z.2.1.tail.zip z.1.1.tail).map (fun xy => xy.1 - c * xy.2), z.2.2 - c * z.1.2)

@[fun_prop] theorem reduceNonzero_poly : Poly reduceNonzero := by
  have hm : Poly (fun z : Scalar × List (Scalar × Scalar) =>
      z.2.map (fun xy => xy.1 - z.1 * xy.2)) :=
    Poly.listMapParam (fun z : Scalar × (Scalar × Scalar) => z.2.1 - z.1 * z.2.2) (by fun_prop)
  have hc : Poly (fun z : Row × Row => z.2.1.headD 0 / z.1.1.headD 0) := by fun_prop
  unfold reduceNonzero
  apply Poly.pair
  · exact Poly.comp _ (fun z : Row × Row =>
      (z.2.1.headD 0 / z.1.1.headD 0, z.2.1.tail.zip z.1.1.tail)) hm (by fun_prop)
  · fun_prop

def reduce (z : Row × Row) : Row :=
  if toBool (z.1.1.headD 0) then reduceNonzero z else (z.2.1.tail, z.2.2)

@[fun_prop] theorem reduce_poly : Poly reduce := by
  unfold reduce
  fun_prop

def pivot (rs : List Row) : Row :=
  (rs.filter (fun r => decide (r.1.headD 0 ≠ 0))).headD ([], 0)

@[fun_prop] theorem pivot_poly : Poly pivot := by
  have hf : Poly (fun r : Row => decide (r.1.headD 0 ≠ 0)) :=
    Poly.comp _ (fun r : Row => r.1.headD 0) scalar_ne_zero_poly (by fun_prop)
  unfold pivot
  exact Poly.comp _ _ (Poly.listHeadD ([], (0 : Scalar))) (Poly.listFilter _ hf)

def step (rs : List Row) : List Row := rs.map (fun r => reduce (pivot rs, r))

@[fun_prop] theorem step_poly : Poly step := by
  have hm : Poly (fun z : Row × List Row => z.2.map (fun r => reduce (z.1, r))) :=
    Poly.listMapParam reduce reduce_poly
  exact Poly.comp _ (fun rs : List Row => (pivot rs, rs)) hm (by fun_prop)

@[simp] theorem code_scalars_length (xs : List Scalar) : (encode xs).length = 3 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [code_cons, pairBits_length, code_scalar_length,
      List.length_cons, ih]; omega

@[simp] theorem code_row_length (r : Row) : (encode r).length = 6 * r.1.length + 2 := by
  simp [encode_prod, pairBits_length]
  omega

theorem reduce_code_length (p r : Row) : (encode (reduce (p,r))).length ≤ (encode r).length := by
  simp [reduce, reduceNonzero, List.length_zip, List.length_tail]
  split <;> simp_all

theorem step_code_length (rs : List Row) : (encode (step rs)).length ≤ (encode rs).length := by
  have h (p : Row) : ∀ rs : List Row,
      (encode (rs.map (fun r => reduce (p,r)))).length ≤ (encode rs).length := by
    intro rs
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      have hr := reduce_code_length p r
      simp only [List.map_cons, code_cons, pairBits_length]
      omega
  exact h (pivot rs) rs

theorem iterate_code_length (n : Nat) (rs : List Row) :
    (encode (step^[n] rs)).length ≤ (encode rs).length := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply']; exact (step_code_length _).trans ih

@[fun_prop] theorem iterate_poly : Poly (fun z : Nat × List Row => step^[z.1] z.2) := by
  apply Poly.boundedIterate step step_poly X
  intro z j hj
  have h := iterate_code_length j z.2
  simp only [encode_prod, pairBits_length, eval_X] at *
  omega

def serial {n : Nat} (r : SerialGaussian.Row n) : Row := (r.coeff, r.rhs)

theorem pivot_serial {n : Nat} (rs : List (SerialGaussian.Row (n+1))) :
    pivot (rs.map serial) = ((SerialGaussian.pivot rs).map serial).getD ([],0) := by
  simp only [pivot, List.headD_eq_head?_getD, List.head?_filter, List.find?_map,
    SerialGaussian.pivot]
  congr 3
  funext r
  simp only [Function.comp_apply, serial, ← List.headD_eq_head?_getD]
  change decide (r.head ≠ 0) = (r.head != 0)
  rcases scalar_cases r.head with h | h <;> rw [h] <;> decide

theorem reduce_serial {n : Nat} (p r : SerialGaussian.Row (n+1)) (hp : p.head ≠ 0) :
    reduce (serial p, serial r) = serial (p.reduce r) := by
  have hb : toBool p.head = true := by
    rcases scalar_cases p.head with h | h
    · exact (hp h).elim
    · unfold toBool; rw [h]; decide
  change toBool (p.coeff.headD 0) = true at hb
  simp only [reduce, serial, hb, ↓reduceIte, reduceNonzero, SerialGaussian.Row.reduce,
    SerialGaussian.Row.head]
  congr 1
  exact List.map_uncurry_zip_eq_zipWith (f := fun x y => x - r.coeff.headD 0 / p.coeff.headD 0 * y)

def finalCheck (rs : List Row) : Bool :=
  (rs.filter (fun r => toBool r.2)).isEmpty

@[fun_prop] theorem finalCheck_poly : Poly finalCheck := by
  unfold finalCheck
  exact Poly.comp _ _ Poly.listIsEmpty (Poly.listFilter _ (by fun_prop))

def solve (z : Nat × List Row) : Bool := finalCheck (step^[z.1] z.2)

@[fun_prop] theorem solve_poly : Poly solve := by
  unfold solve
  exact Poly.comp _ _ finalCheck_poly iterate_poly

theorem solve_serial {n : Nat} (rs : List (SerialGaussian.Row n)) :
    solve (n, rs.map serial) = SerialGaussian.solve rs := by
  induction n with
  | zero =>
    simp only [solve, Function.iterate_zero_apply, finalCheck, SerialGaussian.solve]
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      rcases scalar_cases r.rhs with h | h <;> simp [serial, toBool, h] at *
      exact ih
  | succ n ih =>
    change finalCheck (step^[n+1] (rs.map serial)) = _
    rw [Function.iterate_succ_apply]
    cases hp : SerialGaussian.pivot rs with
    | none =>
      have hs : step (rs.map serial) = (rs.map SerialGaussian.Row.tail).map serial := by
        simp [step, pivot_serial, hp, reduce, toBool, serial, SerialGaussian.Row.tail]
      rw [hs]
      exact (ih _).trans (by simp [SerialGaussian.solve, hp])
    | some p =>
      have hp' : p.head ≠ 0 := by
        have h := List.find?_some hp
        simpa using h
      have hs : step (rs.map serial) = (rs.map (SerialGaussian.Row.reduce p)).map serial := by
        simp only [step, pivot_serial, hp, Option.map_some, Option.getD_some, List.map_map]
        apply List.map_congr_left
        intro r hr
        exact reduce_serial p r hp'
      rw [hs]
      exact (ih _).trans (by simp [SerialGaussian.solve, hp])

def matrixRow (z : (List (List Scalar) × List Scalar) × Nat) : Row :=
  (z.1.1.map (fun v => v[z.2]?.getD 0), z.1.2[z.2]?.getD 0)

@[fun_prop] theorem matrixRow_poly : Poly matrixRow := by
  have hm : Poly (fun z : Nat × List (List Scalar) => z.2.map (fun v => v[z.1]?.getD 0)) :=
    Poly.listMapParam (fun z : Nat × List Scalar => z.2[z.1]?.getD 0)
      (Poly.comp _ (fun z : Nat × List Scalar => (z.2,z.1)) (Poly.listGetD 0) (by fun_prop))
  unfold matrixRow
  apply Poly.pair
  · exact Poly.comp _ (fun z : (List (List Scalar) × List Scalar) × Nat => (z.2,z.1.1)) hm (by fun_prop)
  · exact Poly.comp _ (fun z : (List (List Scalar) × List Scalar) × Nat => (z.1.2,z.2))
      (Poly.listGetD 0) (by fun_prop)

def matrix (z : List (List Scalar) × List Scalar) : List Row :=
  (List.range z.2.length).map (fun i => matrixRow (z,i))

@[fun_prop] theorem matrix_poly : Poly matrix :=
  Poly.comp _ (fun z : List (List Scalar) × List Scalar => (z,List.range z.2.length))
    (Poly.listMapParam matrixRow matrixRow_poly) (by fun_prop)

def spanTest (z : List (List Scalar) × List Scalar) : Bool := solve (z.1.length, matrix z)

@[fun_prop] theorem spanTest_poly : Poly spanTest := by
  unfold spanTest
  exact Poly.comp _ _ solve_poly (by fun_prop)

theorem matrix_ofFn {d k : Nat} (vs : Fin k → GF2Span.Vec d) (v : GF2Span.Vec d) :
    matrix ((List.ofFn vs).map List.ofFn, List.ofFn v) = (GF2Span.rows vs v).map serial := by
  apply List.ext_getElem
  · simp [matrix, GF2Span.rows]
  · intro i hi hj
    simp [matrix, GF2Span.rows] at hi
    simp [matrix, matrixRow, GF2Span.rows, serial, SerialGaussian.Row.encode, hi]
    funext j
    simp [Function.comp_def, hi]

theorem spanTest_ofFn {d k : Nat} (vs : Fin k → GF2Span.Vec d) (v : GF2Span.Vec d) :
    spanTest ((List.ofFn vs).map List.ofFn, List.ofFn v) = GF2Span.test vs v := by
  simp only [spanTest, List.length_map, List.length_ofFn, matrix_ofFn]
  exact solve_serial _

end WeightedUDNF.PolyGaussian

/- WeightedBasis -/
set_option autoImplicit false
/-!
Internal formalization of weighted representative compression.
This file does not prove the Prove2Me polynomial-time Turing-machine target.
Span membership is classical here; refinement to executable GF(2) elimination
and to a polynomial-time machine has not yet been formalized.
-/

set_option autoImplicit false

namespace WeightedBasis

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A nonzero linear observation of a span is nonzero on a generator. -/
theorem exists_nonzero_of_mem_span (s : Set V) (v : V)
    (hv : v ∈ Submodule.span K s) (f : V →ₗ[K] K) (hf : f v ≠ 0) :
    ∃ u ∈ s, f u ≠ 0 := by
  by_contra h
  have hs : s ⊆ LinearMap.ker f := by
    intro u hu
    change f u = 0
    by_contra hfu
    exact h ⟨u, hu, hfu⟩
  have hspan : Submodule.span K s ≤ LinearMap.ker f :=
    Submodule.span_le.mpr hs
  exact hf (hspan hv)

/-- Vectors attached to representatives of at least the requested weight. -/
def heavy (xs : List (Nat × V)) (w : Nat) : Set V :=
  {v | ∃ e ∈ xs, w ≤ e.1 ∧ e.2 = v}

/-- Every candidate is represented by retained candidates of no smaller weight. -/
def Represents (xs ys : List (Nat × V)) : Prop :=
  ∀ e ∈ xs, e.2 ∈ Submodule.span K (heavy ys e.1)

omit [AddCommGroup V] in
theorem heavy_mono {xs ys : List (Nat × V)} {a b : Nat}
    (hxy : ∀ e ∈ xs, e ∈ ys) (hab : a ≤ b) : heavy xs b ⊆ heavy ys a := by
  rintro v ⟨e, he, hbe, rfl⟩
  exact ⟨e, hxy e he, hab.trans hbe, rfl⟩

theorem Represents.refl (xs : List (Nat × V)) : Represents (K := K) xs xs := by
  intro e he
  exact Submodule.subset_span ⟨e, he, le_rfl, rfl⟩

theorem Represents.trans {xs ys zs : List (Nat × V)}
    (hxy : Represents (K := K) xs ys) (hyz : Represents (K := K) ys zs) :
    Represents (K := K) xs zs := by
  intro e he
  have hs : Submodule.span K (heavy ys e.1) ≤ Submodule.span K (heavy zs e.1) := by
    apply Submodule.span_le.mpr
    rintro v ⟨d, hd, hed, rfl⟩
    exact Submodule.span_mono (heavy_mono (fun _ h => h) hed) (hyz d hd)
  exact hs (hxy e he)

/-- Representation preserves the best weight for every linear completion test. -/
theorem Represents.preserves_completion {xs ys : List (Nat × V)}
    (hxy : Represents (K := K) xs ys) (f : V →ₗ[K] K)
    {e : Nat × V} (he : e ∈ xs) (hf : f e.2 ≠ 0) :
    ∃ d ∈ ys, e.1 ≤ d.1 ∧ f d.2 ≠ 0 := by
  obtain ⟨v, ⟨d, hd, hweight, rfl⟩, hfv⟩ :=
    exists_nonzero_of_mem_span _ _ (hxy e he) f hf
  exact ⟨d, hd, hweight, hfv⟩

def extend (f : V →ₗ[K] V) (cost : Nat) (e : Nat × V) : Nat × V :=
  (e.1 + cost, f e.2)

/-- Applying one fixed transition and adding its cost preserves representation. -/
theorem Represents.map_extend {xs ys : List (Nat × V)}
    (hxy : Represents (K := K) xs ys) (f : V →ₗ[K] V) (cost : Nat) :
    Represents (K := K) (xs.map (extend f cost)) (ys.map (extend f cost)) := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  have hv := Submodule.apply_mem_span_image_of_mem_span f (hxy a ha)
  apply Submodule.span_mono ?_ hv
  rintro v ⟨u, ⟨b, hb, hab, rfl⟩, rfl⟩
  exact ⟨extend f cost b, List.mem_map.mpr ⟨b, hb, rfl⟩,
    Nat.add_le_add_right hab cost, rfl⟩

theorem Represents.append {xs ys us vs : List (Nat × V)}
    (hxy : Represents (K := K) xs ys) (huv : Represents (K := K) us vs) :
    Represents (K := K) (xs ++ us) (ys ++ vs) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact Submodule.span_mono
      (heavy_mono (fun _ h => List.mem_append_left _ h) le_rfl) (hxy e he)
  · exact Submodule.span_mono
      (heavy_mono (fun _ h => List.mem_append_right _ h) le_rfl) (huv e he)

/-- Span of all representative vectors (scores are ignored here). -/
def vectors (xs : List (Nat × V)) : Set V := {v | ∃ e ∈ xs, e.2 = v}

noncomputable def compress : List (Nat × V) → List (Nat × V)
  | [] => []
  | a :: xs => by
      classical
      exact if a.2 ∈ Submodule.span K (vectors (compress xs))
        then compress xs else a :: compress xs

theorem compress_subset (xs : List (Nat × V)) :
    ∀ e ∈ compress (K := K) xs, e ∈ xs := by
  classical
  induction xs with
  | nil => simp [compress]
  | cons a xs ih =>
    intro e he
    simp only [compress] at he
    split_ifs at he with h
    · exact List.mem_cons_of_mem _ (ih e he)
    · rcases List.mem_cons.mp he with rfl | he
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih e he)

/-- Process a list sorted by increasing weight from its tail, hence heaviest first. -/
theorem compress_represents (xs : List (Nat × V))
    (hsorted : xs.Pairwise (fun a b => a.1 ≤ b.1)) :
    Represents (K := K) xs (compress (K := K) xs) := by
  classical
  induction xs with
  | nil => simp [Represents]
  | cons a xs ih =>
    obtain ⟨ha, hs⟩ := List.pairwise_cons.mp hsorted
    have ht := ih hs
    intro e he
    simp only [compress]
    split_ifs with h
    · rcases List.mem_cons.mp he with rfl | he
      · apply Submodule.span_mono ?_ h
        rintro v ⟨d, hd, rfl⟩
        exact ⟨d, hd, ha d (compress_subset xs d hd), rfl⟩
      · exact ht e he
    · rcases List.mem_cons.mp he with rfl | he
      · exact Submodule.subset_span ⟨e, List.mem_cons_self, le_rfl, rfl⟩
      · exact Submodule.span_mono
          (heavy_mono (fun _ h => List.mem_cons_of_mem _ h) le_rfl) (ht e he)

omit [AddCommGroup V] in
theorem vectors_cons (a : Nat × V) (xs : List (Nat × V)) :
    vectors (a :: xs) = insert a.2 (vectors xs) := by
  ext v
  simp only [vectors, Set.mem_ofPred_eq, Set.mem_insert_iff, List.mem_cons]
  constructor
  · rintro ⟨e, rfl | he, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e, he, rfl⟩
  · rintro (rfl | ⟨e, he, rfl⟩)
    · exact ⟨a, Or.inl rfl, rfl⟩
    · exact ⟨e, Or.inr he, rfl⟩

/-- The retained vectors are linearly independent. -/
theorem compress_independent (xs : List (Nat × V)) :
    LinearIndepOn K id (vectors (compress (K := K) xs)) := by
  classical
  induction xs with
  | nil => simp [compress, vectors]
  | cons a xs ih =>
    simp only [compress]
    split_ifs with h
    · exact ih
    · rw [vectors_cons]
      exact (linearIndepOn_id_insert (fun ha => h (Submodule.subset_span ha))).mpr ⟨ih, h⟩

theorem compress_nodup_vectors (xs : List (Nat × V)) :
    ((compress (K := K) xs).map Prod.snd).Nodup := by
  classical
  induction xs with
  | nil => simp [compress]
  | cons a xs ih =>
    simp only [compress]
    split_ifs with h
    · exact ih
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro ha
      obtain ⟨e, he, heq⟩ := List.mem_map.mp ha
      exact h (Submodule.subset_span ⟨e, he, heq⟩)

theorem compress_length_le [Module.Finite K V] (xs : List (Nat × V)) :
    (compress (K := K) xs).length ≤ Module.finrank K V := by
  classical
  have hset : (↑((compress (K := K) xs).map Prod.snd).toFinset : Set V) =
      vectors (compress (K := K) xs) := by
    ext v
    simp [vectors]
  have hi : LinearIndependent K
      (fun v : (((compress (K := K) xs).map Prod.snd).toFinset : Set V) => (v : V)) := by
    change LinearIndepOn K id _
    rw [hset]
    exact compress_independent xs
  have hc := hi.finset_card_le_finrank
  rw [List.toFinset_card_of_nodup (compress_nodup_vectors xs), List.length_map] at hc
  exact hc

def sortByWeight (xs : List (Nat × V)) : List (Nat × V) :=
  xs.insertionSort (fun a b => a.1 ≤ b.1)

omit [AddCommGroup V] in
theorem sortByWeight_sorted (xs : List (Nat × V)) :
    (sortByWeight xs).Pairwise (fun a b => a.1 ≤ b.1) := by
  letI : Std.Total (fun a b : Nat × V => a.1 ≤ b.1) := ⟨fun a b => Nat.le_total _ _⟩
  letI : IsTrans (Nat × V) (fun a b => a.1 ≤ b.1) := ⟨fun _ _ _ h1 h2 => h1.trans h2⟩
  exact List.pairwise_insertionSort _ xs

omit [AddCommGroup V] in
theorem mem_sortByWeight (e : Nat × V) (xs : List (Nat × V)) :
    e ∈ sortByWeight xs ↔ e ∈ xs := List.mem_insertionSort _

noncomputable def reduce (xs : List (Nat × V)) : List (Nat × V) :=
  compress (K := K) (sortByWeight xs)

theorem reduce_represents (xs : List (Nat × V)) :
    Represents (K := K) xs (reduce (K := K) xs) := by
  intro e he
  exact compress_represents _ (sortByWeight_sorted xs) e ((mem_sortByWeight e xs).mpr he)

theorem reduce_subset (xs : List (Nat × V)) : ∀ e ∈ reduce (K := K) xs, e ∈ xs := by
  intro e he
  exact (mem_sortByWeight e xs).mp (compress_subset _ e he)

theorem reduce_length_le [Module.Finite K V] (xs : List (Nat × V)) :
    (reduce (K := K) xs).length ≤ Module.finrank K V := compress_length_le _

def branches (f₀ f₁ : V →ₗ[K] V) (cost : Nat) (xs : List (Nat × V)) : List (Nat × V) :=
  xs.map (extend f₀ 0) ++ xs.map (extend f₁ cost)

def allStates (v : V) (f₀ f₁ : Nat → V →ₗ[K] V) (cost : Nat → Nat) :
    Nat → List (Nat × V)
  | 0 => [(0, v)]
  | i + 1 => branches (f₀ i) (f₁ i) (cost i) (allStates v f₀ f₁ cost i)

noncomputable def retained (v : V) (f₀ f₁ : Nat → V →ₗ[K] V) (cost : Nat → Nat) :
    Nat → List (Nat × V)
  | 0 => [(0, v)]
  | i + 1 => reduce (K := K) (branches (f₀ i) (f₁ i) (cost i) (retained v f₀ f₁ cost i))

theorem retained_represents (v : V) (f₀ f₁ : Nat → V →ₗ[K] V) (cost : Nat → Nat)
    (i : Nat) : Represents (K := K) (allStates v f₀ f₁ cost i) (retained v f₀ f₁ cost i) := by
  induction i with
  | zero => exact Represents.refl _
  | succ i ih =>
    exact ((ih.map_extend (f₀ i) 0).append (ih.map_extend (f₁ i) (cost i))).trans
      (reduce_represents _)

theorem branches_subset {xs ys : List (Nat × V)}
    (h : ∀ e ∈ xs, e ∈ ys) (f₀ f₁ : V →ₗ[K] V) (cost : Nat) :
    ∀ e ∈ branches f₀ f₁ cost xs, e ∈ branches f₀ f₁ cost ys := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact List.mem_append_left _ (List.mem_map.mpr ⟨a, h a ha, rfl⟩)
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact List.mem_append_right _ (List.mem_map.mpr ⟨a, h a ha, rfl⟩)

theorem retained_subset (v : V) (f₀ f₁ : Nat → V →ₗ[K] V) (cost : Nat → Nat)
    (i : Nat) : ∀ e ∈ retained v f₀ f₁ cost i, e ∈ allStates v f₀ f₁ cost i := by
  induction i with
  | zero => exact fun _ h => h
  | succ i ih =>
    intro e he
    exact branches_subset ih (f₀ i) (f₁ i) (cost i) e (reduce_subset _ e he)

/-- Exact threshold decision equivalence for the abstract compression algorithm. -/
theorem threshold_iff (v : V) (f₀ f₁ : Nat → V →ₗ[K] V) (cost : Nat → Nat)
    (i threshold : Nat) (terminal : V →ₗ[K] K) :
    (∃ e ∈ allStates v f₀ f₁ cost i, threshold ≤ e.1 ∧ terminal e.2 ≠ 0) ↔
    (∃ e ∈ retained v f₀ f₁ cost i, threshold ≤ e.1 ∧ terminal e.2 ≠ 0) := by
  constructor
  · rintro ⟨e, he, hweight, hterminal⟩
    obtain ⟨d, hd, hde, htd⟩ :=
      (retained_represents v f₀ f₁ cost i).preserves_completion terminal he hterminal
    exact ⟨d, hd, hweight.trans hde, htd⟩
  · rintro ⟨e, he, hweight, hterminal⟩
    exact ⟨e, retained_subset v f₀ f₁ cost i e he, hweight, hterminal⟩

theorem retained_length_succ_le [Module.Finite K V] (v : V)
    (f₀ f₁ : Nat → V →ₗ[K] V) (cost : Nat → Nat) (i : Nat) :
    (retained v f₀ f₁ cost (i + 1)).length ≤ Module.finrank K V := reduce_length_le _

end WeightedBasis

/- ExecutableWeightedBasis -/
set_option autoImplicit false
namespace WeightedUDNF.ExecutableBasis
open OAI.CPTSeparation
open GF2Span

variable {d : Nat}

def spanTest (xs : List (Nat × Vec d)) (v : Vec d) : Bool :=
  GF2Span.test (fun i : Fin xs.length => (xs.get i).2) v

theorem spanTest_correct (xs : List (Nat × Vec d)) (v : Vec d) :
    spanTest xs v = true ↔ v ∈ Submodule.span Scalar (WeightedBasis.vectors xs) := by
  rw [spanTest, GF2Span.test_correct]
  have he : Set.range (fun i : Fin xs.length => (xs.get i).2) = WeightedBasis.vectors xs := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨xs.get i, List.get_mem _ _, rfl⟩
    · rintro ⟨e, he, rfl⟩
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
      exact ⟨i, congrArg Prod.snd hi⟩
  rw [he]

/-- Executable refinement of weighted greedy basis compression. -/
def compress : List (Nat × Vec d) → List (Nat × Vec d)
  | [] => []
  | a :: xs =>
    let ys := compress xs
    if spanTest ys a.2 then ys else a :: ys

theorem compress_eq (xs : List (Nat × Vec d)) :
    compress xs = WeightedBasis.compress (K := Scalar) xs := by
  classical
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [compress, ih, WeightedBasis.compress]
    simp only [spanTest_correct]

def reduce (xs : List (Nat × Vec d)) : List (Nat × Vec d) :=
  compress (WeightedBasis.sortByWeight xs)

theorem reduce_eq (xs : List (Nat × Vec d)) :
    reduce xs = WeightedBasis.reduce (K := Scalar) xs := compress_eq _

theorem reduce_represents (xs : List (Nat × Vec d)) :
    WeightedBasis.Represents (K := Scalar) xs (reduce xs) := by
  rw [reduce_eq]
  exact WeightedBasis.reduce_represents xs

theorem reduce_length_le (xs : List (Nat × Vec d)) : (reduce xs).length ≤ d := by
  rw [reduce_eq]
  simpa [Vec] using WeightedBasis.reduce_length_le (K := Scalar) xs

def retained (v : Vec d) (f₀ f₁ : Nat → Vec d →ₗ[Scalar] Vec d)
    (cost : Nat → Nat) : Nat → List (Nat × Vec d)
  | 0 => [(0, v)]
  | i + 1 => reduce (WeightedBasis.branches (f₀ i) (f₁ i) (cost i)
      (retained v f₀ f₁ cost i))

theorem retained_eq (v : Vec d) (f₀ f₁ : Nat → Vec d →ₗ[Scalar] Vec d)
    (cost : Nat → Nat) (i : Nat) :
    retained v f₀ f₁ cost i = WeightedBasis.retained v f₀ f₁ cost i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [retained, WeightedBasis.retained, ih, reduce_eq]

theorem threshold_iff (v : Vec d) (f₀ f₁ : Nat → Vec d →ₗ[Scalar] Vec d)
    (cost : Nat → Nat) (i threshold : Nat) (terminal : Vec d →ₗ[Scalar] Scalar) :
    (∃ e ∈ WeightedBasis.allStates v f₀ f₁ cost i,
      threshold ≤ e.1 ∧ terminal e.2 ≠ 0) ↔
    (∃ e ∈ retained v f₀ f₁ cost i, threshold ≤ e.1 ∧ terminal e.2 ≠ 0) := by
  rw [retained_eq]
  exact WeightedBasis.threshold_iff v f₀ f₁ cost i threshold terminal

end WeightedUDNF.ExecutableBasis

/- PolyBasis -/
set_option autoImplicit false
namespace WeightedUDNF.PolyBasis
open OAI.BinaryMatching.StackCode OAI.CPTSeparation
open Polynomial
abbrev Entry := List Bool × List Scalar

def compare (z : Entry × Entry) : Bool := BinaryWeights.le z.1.1 z.2.1
@[fun_prop] theorem compare_poly : Poly compare := by
  unfold compare
  exact Poly.comp _ (fun z : Entry × Entry => (z.1.1,z.2.1)) BinaryWeights.le_poly (by fun_prop)

def sort (xs : List Entry) : List Entry := xs.insertionSort (fun a b => compare (a,b) = true)
@[fun_prop] theorem sort_poly : Poly sort := PolyLists.insertionSort_poly compare compare_poly

def test (z : List Entry × Entry) : Bool := PolyGaussian.spanTest (z.1.map Prod.snd,z.2.2)
@[fun_prop] theorem test_poly : Poly test := by
  unfold test
  exact Poly.comp _ (fun z : List Entry × Entry => (z.1.map Prod.snd,z.2.2))
    PolyGaussian.spanTest_poly (by fun_prop)

def compressStep (z : List Entry × Entry) : List Entry := if test z then z.1 else z.2 :: z.1
@[fun_prop] theorem compressStep_poly : Poly compressStep := by unfold compressStep; fun_prop

def compress : List Entry → List Entry
  | [] => []
  | a :: xs => compressStep (compress xs,a)

@[fun_prop] theorem compress_poly : Poly compress := by
  have hf := Poly.listFoldAdd compressStep compressStep_poly 1 (by
    intro z; unfold compressStep; split <;> simp only [code_cons,pairBits_length,Nat.one_mul] <;> omega)
  have h : Poly (fun xs : List Entry => xs.reverse.foldl (fun acc a => compressStep (acc,a)) []) :=
    Poly.comp _ (fun xs : List Entry => (xs.reverse,[])) hf (by fun_prop)
  apply h.congr
  intro xs
  simp only [List.foldl_reverse]
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons, compress, ih]

def reduce (xs : List Entry) : List Entry := compress (sort xs)
@[fun_prop] theorem reduce_poly : Poly reduce := by unfold reduce; fun_prop

def vector (d : Nat) (xs : List Scalar) : GF2Span.Vec d := fun i => xs[i.val]?.getD 0

def decode (d : Nat) (e : Entry) : Nat × GF2Span.Vec d := (BinaryWeights.value e.1,vector d e.2)

def WellFormed (d : Nat) (xs : List Entry) : Prop := ∀ e ∈ xs, e.2.length = d

theorem vector_roundtrip {d : Nat} (xs : List Scalar) (h : xs.length = d) :
    List.ofFn (vector d xs) = xs := by
  subst d
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [vector, hj]

theorem test_correct {d : Nat} (xs : List Entry) (e : Entry)
    (hx : WellFormed d xs) (he : e.2.length = d) :
    test (xs,e) = ExecutableBasis.spanTest (xs.map (decode d)) (decode d e).2 := by
  have hm : (List.ofFn (fun i : Fin (xs.map (decode d)).length =>
      ((xs.map (decode d)).get i).2)).map List.ofFn = xs.map Prod.snd := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.length_map] at hj
      simp [decode, vector_roundtrip _ (hx _ (List.getElem_mem hj)), hj]
  have h := PolyGaussian.spanTest_ofFn
    (fun i : Fin (xs.map (decode d)).length => ((xs.map (decode d)).get i).2) (decode d e).2
  rw [hm, show List.ofFn (decode d e).2 = e.2 from vector_roundtrip _ he] at h
  exact h

theorem compress_subset (xs : List Entry) : ∀ e ∈ compress xs, e ∈ xs := by
  induction xs with
  | nil => simp [compress]
  | cons a xs ih =>
    intro e he
    simp only [compress,compressStep] at he
    split at he
    · exact List.mem_cons_of_mem _ (ih e he)
    · rcases List.mem_cons.mp he with rfl | he
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih e he)

theorem compress_decode {d : Nat} (xs : List Entry) (hx : WellFormed d xs) :
    (compress xs).map (decode d) = ExecutableBasis.compress (xs.map (decode d)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ht : WellFormed d xs := fun e he => hx e (List.mem_cons_of_mem _ he)
    have ha := hx a List.mem_cons_self
    have hc : WellFormed d (compress xs) := fun e he => ht e (compress_subset xs e he)
    simp only [compress,compressStep, test_correct _ _ hc ha, List.map_cons,
      ExecutableBasis.compress, ih ht]
    split <;> simp_all

theorem sort_decode (d : Nat) (xs : List Entry) :
    (sort xs).map (decode d) = WeightedBasis.sortByWeight (xs.map (decode d)) := by
  apply List.map_insertionSort
  intro a ha b hb
  exact BinaryWeights.le_correct _ _

theorem sort_wellFormed {d : Nat} {xs : List Entry} (h : WellFormed d xs) : WellFormed d (sort xs) := by
  intro e he
  exact h e ((List.mem_insertionSort _).mp he)

theorem reduce_decode {d : Nat} (xs : List Entry) (hx : WellFormed d xs) :
    (reduce xs).map (decode d) = ExecutableBasis.reduce (xs.map (decode d)) := by
  rw [reduce, compress_decode _ (sort_wellFormed hx), sort_decode]
  rfl

theorem reduce_length {d : Nat} (xs : List Entry) (hx : WellFormed d xs) : (reduce xs).length ≤ d := by
  have h := ExecutableBasis.reduce_length_le (xs.map (decode d))
  rw [← reduce_decode xs hx,List.length_map] at h
  exact h

theorem reduce_subset (xs : List Entry) : ∀ e ∈ reduce xs, e ∈ xs := by
  intro e he
  exact (List.mem_insertionSort _).mp (compress_subset _ e he)

theorem reduce_wellFormed {d : Nat} {xs : List Entry} (h : WellFormed d xs) : WellFormed d (reduce xs) :=
  fun e he => h e (reduce_subset xs e he)

theorem compress_code_length (xs : List Entry) : (encode (compress xs)).length ≤ (encode xs).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [compress,compressStep]
    split <;> simp only [code_cons,pairBits_length] <;> omega

theorem reduce_code_length (xs : List Entry) : (encode (reduce xs)).length ≤ (encode xs).length := by
  have h := compress_code_length (sort xs)
  have he := PolyLists.code_perm (List.perm_insertionSort (fun a b => compare (a,b)=true) xs)
  exact h.trans_eq he

end WeightedUDNF.PolyBasis

/- OAI.Computability.MatchingCount.RawBitsBridge -/
set_option autoImplicit false
/- Adapted from openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Apache-2.0; see LICENSE-openai-math. -/
set_option autoImplicit true

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

structure Bits where
  data : List Bool
  deriving Inhabited
instance : Coding Bits := ⟨Bits.data⟩
@[simp] lemma encode_Bits (b : Bits) : encode b=b.data := rfl

namespace Routine
noncomputable def headBool : Routine (id : List Bool → List Bool) (fun b : Bool => [b])
    (fun l => l.headD false) where
  scratch := 0
  block := Block.cases 0 (Block.push 0 false)
    ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
  time := 2*X+3
  correct l := by
    let s : Store 1 := Function.update (fun _ => []) 0 l
    have hfalse := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1) s)
      (Block.push_runs (0:Fin 1) false (Function.update s 0 []))
    have htrue := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1) s)
      (Block.push_runs (0:Fin 1) true (Function.update s 0 []))
    cases l with
    | nil =>
      have hh := Block.cases_runs_empty (0:Fin 1) (Block.push 0 false)
        ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
        (by simp [s]) (Block.push_runs (0:Fin 1) false s)
      exact ⟨2,by simp,by simpa [s,Function.update_idem] using hh⟩
    | cons b l =>
      cases b with
      | false =>
        have hh := Block.cases_runs_false (0:Fin 1) (Block.push 0 false)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
          (by simp [s]) hfalse
        exact ⟨2*(l.length+1)+3,by simp,by simpa [s,Function.update_idem,Nat.add_assoc] using hh⟩
      | true =>
        have hh := Block.cases_runs_true (0:Fin 1) (Block.push 0 false)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
          (by simp [s]) htrue
        exact ⟨2*(l.length+1)+3,by simp,by simpa [s,Function.update_idem,Nat.add_assoc] using hh⟩
end Routine

namespace Poly
@[fun_prop] theorem bitsTail : Poly (fun b : Bits => Bits.mk b.data.tail) :=
  ⟨Routine.tail.reindex encode encode _ Bits.data (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsEmpty : Poly (fun b : Bits => b.data.isEmpty) :=
  ⟨Routine.isEmpty.reindex encode encode _ Bits.data (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsHead : Poly (fun b : Bits => b.data.headD false) :=
  ⟨Routine.headBool.reindex encode encode _ Bits.data (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsLength : Poly (fun b : Bits => b.data.length) := Poly.codeLength
@[fun_prop] theorem bitsAppend : Poly (fun z : Bits×Bits => Bits.mk (z.1.data++z.2.data)) :=
  ⟨Routine.append.reindex encode encode _ (fun z : Bits×Bits => (z.1.data,z.2.data)) (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsSingleton : Poly (fun b : Bool => Bits.mk [b]) :=
  ⟨(Routine.identity (fun b : Bool => [b])).reindex encode encode _ id (fun _ => rfl) (fun _ => rfl)⟩
end Poly

def encodeBitsStep (z : Bits×List Bool) : Bits×List Bool :=
  if z.1.data.isEmpty then z else (⟨z.1.data.tail⟩,z.2++[z.1.data.headD false])
lemma encodeBitsStep_iterate (j : ℕ) (b : Bits) (acc : List Bool) :
    encodeBitsStep^[j] (b,acc)=(⟨b.data.drop j⟩,acc++b.data.take j) := by
  induction j generalizing b acc with
  | zero => simp
  | succ j ih =>
    cases b with | mk l =>
    cases l with
    | nil => simp [Function.iterate_succ_apply,encodeBitsStep,ih]
    | cons a l => simp [Function.iterate_succ_apply,encodeBitsStep,ih,List.append_assoc]

namespace Poly
@[fun_prop] theorem bitsDecode : Poly (fun b : Bits => b.data) := by
  have ht : Poly (fun z : Bits×List Bool => Bits.mk z.1.data.tail) :=
    Poly.comp _ Prod.fst bitsTail (by fun_prop)
  have hh : Poly (fun z : Bits×List Bool => z.1.data.headD false) :=
    Poly.comp _ Prod.fst bitsHead (by fun_prop)
  have hs : Poly encodeBitsStep := by
    exact Poly.cond _ _ _ (Poly.comp _ Prod.fst bitsEmpty (by fun_prop))
      (Poly.pair _ _ ht (by fun_prop)) Poly.identity
  have hi := Poly.boundedIterate encodeBitsStep hs (5*X+1) (by
    intro z j hj
    rw [show z.2=(z.2.1,z.2.2) from rfl,encodeBitsStep_iterate]
    simp only [encode_prod,pairBits_length,encode_Bits,code_append,List.length_append,WeightedUDNF.BinaryWeights.code_bits_length,
      List.length_drop,List.length_take,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,encode_nat,unary_length]
    omega)
  have h := Poly.second _ (Poly.comp _ (fun b : Bits => (b.data.length,(b,([]:List Bool)))) hi (by fun_prop))
  exact h.congr (fun b => by rw [encodeBitsStep_iterate]; simp)

private lemma bits_fold (l acc : List Bool) :
    l.foldl (fun b a => Bits.mk (b.data++[a])) (Bits.mk acc)=Bits.mk (acc++l) := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih => simp [ih,List.append_assoc]

@[fun_prop] theorem bitsEncode : Poly (fun l : List Bool => Bits.mk l) := by
  have hf : Poly (fun z : Bits×Bool => Bits.mk (z.1.data++[z.2])) := by
    exact Poly.comp _ (fun z : Bits×Bool => (z.1,Bits.mk [z.2])) bitsAppend (Poly.pair _ _ (by fun_prop) (Poly.comp _ Prod.snd bitsSingleton (by fun_prop)))
  have hfold := Poly.listFold false _ hf X (by
    intro z k
    rw [show z.2=Bits.mk z.2.data from rfl,bits_fold]
    have hl := list_length_le_code z.1
    simp only [encode_Bits,List.length_append,List.length_take,eval_X,encode_prod,pairBits_length]
    omega)
  have h := Poly.comp _ (fun l : List Bool => (l,Bits.mk [])) hfold (by fun_prop)
  exact h.congr (fun l => by rw [bits_fold]; rfl)
end Poly
end BinaryMatching.StackCode
end

end OAI

/- PolyParser -/
set_option autoImplicit false
namespace WeightedUDNF.PolyParser
open OAI.BinaryMatching.StackCode Polynomial

def capStep (z : (ℕ×ℕ)×Bool) : ℕ×ℕ := (z.1.1,min z.1.1 (2*z.1.2+if z.2 then 1 else 0))
lemma capStep_fold (b : ℕ) (l : List Bool) (a : ℕ) :
    l.foldr (fun c z => capStep (z,c)) (b,min b a)=(b,min b (l.foldr Nat.bit a)) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.foldr_cons,ih]
    apply Prod.ext
    · rfl
    · cases c <;> simp [capStep,List.foldr_cons,Nat.bit] <;> omega

def boundedValue (b : ℕ) (l : List Bool) : ℕ := (l.reverse.foldl (fun z c => capStep (z,c)) (b,0)).2
lemma boundedValue_eq (b : ℕ) (l : List Bool) : boundedValue b l=min b (BinaryWeights.value l) := by
  unfold boundedValue
  rw [List.foldl_reverse,show (b,0)=(b,min b 0) by simp,capStep_fold]
  congr 1
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [Nat.bit, BinaryWeights.value, ih] <;> omega
lemma capStep_fold_bound (l : List Bool) (z : ℕ×ℕ) :
    (l.foldl (fun z c => capStep (z,c)) z).1=z.1 ∧
    (l.foldl (fun z c => capStep (z,c)) z).2≤ max z.1 z.2 := by
  induction l generalizing z with
  | nil => exact ⟨rfl,Nat.le_max_right _ _⟩
  | cons c l ih =>
    obtain ⟨h₁,h₂⟩ := ih (capStep (z,c))
    refine ⟨h₁,?_⟩
    have hh : (capStep (z,c)).2≤z.1 := min_le_left _ _
    exact h₂.trans (max_le (by exact Nat.le_max_left _ _) (hh.trans (Nat.le_max_left _ _)))
@[fun_prop] theorem boundedValue_poly : Poly (fun z : ℕ×List Bool => boundedValue z.1 z.2) := by
  have hs : Poly capStep := by unfold capStep; fun_prop
  have hf := Poly.listFold false capStep hs (4*X+2) (by
    intro z k
    obtain ⟨h₁,h₂⟩ := capStep_fold_bound (z.1.take k) z.2
    simp only [encode_prod,pairBits_length,encode_nat,unary_length,h₁,eval_add,eval_mul,eval_ofNat,eval_X]
    omega)
  unfold boundedValue
  exact Poly.second _ (Poly.comp _ (fun z : ℕ×List Bool => (z.2.reverse,(z.1,0))) hf (by fun_prop))

def block (xs : List Bool) : List Bool × List Bool :=
  let n := PolyLists.prefixCount xs
  let rest := xs.drop (n+1)
  (rest.take n, rest.drop n)

@[fun_prop] theorem block_poly : Poly block := by unfold block; fun_prop

theorem block_length (xs : List Bool) : (block xs).2.length ≤ xs.length := by
  simp only [block,List.length_drop]
  omega

theorem prefix_delimited (n : Nat) (xs : List Bool) :
    PolyLists.prefixCount (List.replicate n true ++ false :: xs) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change PolyLists.prefixCount (List.replicate n true ++ false :: xs) + 1 = n+1
    rw [ih]

theorem block_encode (n : Nat) (rest : List Bool) :
    block (natBlock n ++ rest) = (Computability.encodeNat n,rest) := by
  have hu (k : Nat) : Computability.unaryEncodeNat k = List.replicate k true := by
    induction k with
    | zero => rfl
    | succ k ih => simp [Computability.unaryEncodeNat, List.replicate_succ, ih]
  unfold block natBlock unaryLengthBlock
  rw [hu]
  rw [List.append_assoc,List.append_assoc,List.cons_append,List.nil_append,prefix_delimited]
  simp [List.drop_append, List.drop_replicate, Nat.add_sub_cancel_left, Nat.add_assoc]

theorem value_encode (n : Nat) : BinaryWeights.value (Computability.encodeNat n) = n := by
  unfold Computability.encodeNat
  generalize hn : (n : Num) = x
  have hx : (x : Nat) = n := by rw [← hn]; simp
  rw [← hx]
  clear hn hx n
  cases x with
  | zero => rfl
  | pos p =>
    induction p with
    | one => rfl
    | bit0 p ih =>
      simp [Computability.encodeNum] at ih
      simp [Computability.encodeNum,Computability.encodePosNum,BinaryWeights.value]
      omega
    | bit1 p ih =>
      simp [Computability.encodeNum] at ih
      simp [Computability.encodeNum,Computability.encodePosNum,BinaryWeights.value]
      omega

section Many
variable {α : Type} [Coding α] [Inhabited α]

def manyStep (f : List Bool → α × List Bool) (z : List Bool × List α) : List Bool × List α :=
  ((f z.1).2,z.2 ++ [(f z.1).1])

@[fun_prop] theorem manyStep_poly (f : List Bool → α × List Bool) (hf : Poly f) : Poly (manyStep f) := by
  unfold manyStep
  fun_prop

theorem manyStep_bound (f : List Bool → α × List Bool) (P : Polynomial Nat)
    (hr : ∀ xs, (encode (f xs).2).length ≤ (encode xs).length)
    (he : ∀ xs, (encode (f xs).1).length ≤ P.eval (encode xs).length)
    (n : Nat) (z : List Bool × List α) :
    (encode ((manyStep f)^[n] z).1).length ≤ (encode z.1).length ∧
    (encode ((manyStep f)^[n] z).2).length ≤
      (encode z.2).length + n * (2 * P.eval (encode z.1).length + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h1 := hr ((manyStep f)^[n] z).1
    have h2 := (he ((manyStep f)^[n] z).1).trans (polynomial_eval_mono P ih.1)
    constructor
    · exact h1.trans ih.1
    · simp only [manyStep,code_append,List.length_append,code_cons,pairBits_length,code_nil,List.length_nil]
      nlinarith [ih.2]

@[fun_prop] theorem manyIterate_poly (f : List Bool → α × List Bool) (hf : Poly f)
    (hr : ∀ xs, (f xs).2.length ≤ xs.length) :
    Poly (fun z : Nat × (List Bool × List α) => (manyStep f)^[z.1] z.2) := by
  let P := X + hf.routine.time
  have he : ∀ xs, (encode (f xs).1).length ≤ P.eval (encode xs).length := by
    intro xs
    have hh := hf.routine.length_bound xs
    simp only [P,eval_add,eval_X,encode_prod,pairBits_length] at *
    omega
  have hrest : ∀ xs, (encode (f xs).2).length ≤ (encode xs).length := by
    intro xs
    simpa only [BinaryWeights.code_bits_length] using Nat.mul_le_mul_left 3 (hr xs)
  apply Poly.boundedIterate (manyStep f) (manyStep_poly f hf) (4*X+1+X*(2*P+1))
  intro z j hj
  obtain ⟨h1,h2⟩ := manyStep_bound f P hrest he j z.2
  have hn : (encode z.2.1).length ≤ (encode z).length := by
    simp only [encode_prod,pairBits_length]; omega
  have hm := polynomial_eval_mono P hn
  have hc : j ≤ (encode z).length := by
    simp only [encode_prod,pairBits_length,encode_nat,unary_length]; omega
  have ha : (encode z.2.2).length ≤ (encode z).length := by
    simp only [encode_prod,pairBits_length]; omega
  have hm2 := Nat.mul_le_mul hc (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hm) 1)
  change P.eval (encode z.2.1).length ≤ P.eval (encode z).length at hm
  change j * (2 * P.eval (encode z.2.1).length + 1) ≤
    (encode z).length * (2 * P.eval (encode z).length + 1) at hm2
  simp only [eval_add,eval_mul,eval_X,eval_one,eval_ofNat]
  rw [encode_prod,pairBits_length]
  change 2 * (encode ((manyStep f)^[j] z.2).1).length +
    (encode ((manyStep f)^[j] z.2).2).length + 1 ≤
    4 * (encode z).length + 1 + (encode z).length * (2 * P.eval (encode z).length + 1)
  omega

def many (f : List Bool → α × List Bool) (n : Nat) (xs : List Bool) : List α × List Bool :=
  let z := (manyStep f)^[n] (xs,[])
  (z.2,z.1)

@[fun_prop] theorem many_poly (f : List Bool → α × List Bool) (hf : Poly f)
    (hr : ∀ xs, (f xs).2.length ≤ xs.length) : Poly (fun z : Nat × List Bool => many f z.1 z.2) := by
  have hi := manyIterate_poly f hf hr
  unfold many
  exact Poly.comp (fun z : List Bool × List α => (z.2,z.1))
    (fun z : Nat × List Bool => (manyStep f)^[z.1] (z.2,[])) (by fun_prop)
    (Poly.comp _ (fun z : Nat × List Bool => (z.1,(z.2,[]))) hi (by fun_prop))

theorem many_rest_length (f : List Bool → α × List Bool)
    (hr : ∀ xs, (f xs).2.length ≤ xs.length) (n : Nat) (xs : List Bool) :
    (many f n xs).2.length ≤ xs.length := by
  have h : ∀ n (z : List Bool × List α), ((manyStep f)^[n] z).1.length ≤ z.1.length := by
    intro n z
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply']; exact (hr _).trans ih
  exact h n (xs,[])

theorem many_encoded {β : Type} (f : List Bool → α × List Bool) (enc : β → List Bool)
    (rep : β → α) (hf : ∀ a rest, f (enc a ++ rest) = (rep a,rest))
    (xs : List β) (rest : List Bool) : many f xs.length (xs.flatMap enc ++ rest) = (xs.map rep,rest) := by
  have h (acc : List α) : (manyStep f)^[xs.length] (xs.flatMap enc ++ rest,acc) =
      (rest,acc ++ xs.map rep) := by
    induction xs generalizing acc with
    | nil => simp
    | cons a xs ih =>
      simp only [List.length_cons,Function.iterate_succ_apply,List.flatMap_cons,List.append_assoc]
      simp only [manyStep,hf]
      rw [ih]
      simp [List.append_assoc]
  unfold many
  rw [h]
  simp

def list (f : List Bool → α × List Bool) (xs : List Bool) : List α × List Bool :=
  let z := block xs
  many f (boundedValue z.2.length z.1) z.2

@[fun_prop] theorem list_poly (f : List Bool → α × List Bool) (hf : Poly f)
    (hr : ∀ xs, (f xs).2.length ≤ xs.length) : Poly (list f) := by
  unfold list
  exact Poly.comp _ (fun xs : List Bool => (boundedValue (block xs).2.length (block xs).1,(block xs).2))
    (many_poly f hf hr) (by fun_prop)

theorem list_rest_length (f : List Bool → α × List Bool)
    (hr : ∀ xs, (f xs).2.length ≤ xs.length) (xs : List Bool) : (list f xs).2.length ≤ xs.length :=
  (many_rest_length f hr _ _).trans (block_length xs)

theorem list_encoded {β : Type} (f : List Bool → α × List Bool) (enc : β → List Bool)
    (rep : β → α) (hf : ∀ a rest, f (enc a ++ rest) = (rep a,rest))
    (hlen : ∀ a, 1 ≤ (enc a).length) (xs : List β) (rest : List Bool) :
    list f (natBlock xs.length ++ xs.flatMap enc ++ rest) = (xs.map rep,rest) := by
  have hl : xs.length ≤ (xs.flatMap enc ++ rest).length := by
    have h : xs.length ≤ (xs.flatMap enc).length := by
      induction xs with
      | nil => simp
      | cons a xs ih => have ha := hlen a; simp only [List.flatMap_cons,List.length_append,List.length_cons]; omega
    simp only [List.length_append]; omega
  unfold list
  rw [List.append_assoc,block_encode]
  simp only [boundedValue_eq,value_encode,Nat.min_eq_right hl]
  exact many_encoded f enc rep hf xs rest
end Many

abbrev RawLiteral := Bool × List Bool
abbrev RawInput := List (List RawLiteral) × (List (List Bool) × List Bool)

def literal (xs : List Bool) : RawLiteral × List Bool :=
  ((xs.headD false,(block xs.tail).1),(block xs.tail).2)
@[fun_prop] theorem literal_poly : Poly literal := by unfold literal; fun_prop

theorem literal_length (xs : List Bool) : (literal xs).2.length ≤ xs.length :=
  (block_length xs.tail).trans (by simp)

def term := list literal
@[fun_prop] theorem term_poly : Poly term := list_poly literal literal_poly literal_length

theorem term_length (xs : List Bool) : (term xs).2.length ≤ xs.length :=
  list_rest_length literal literal_length xs

def terms := list term
@[fun_prop] theorem terms_poly : Poly terms := list_poly term term_poly term_length

def weights := list block
@[fun_prop] theorem weights_poly : Poly weights := list_poly block block_poly block_length

def parse (xs : List Bool) : RawInput :=
  let ts := terms (block xs).2
  let ws := weights ts.2
  (ts.1,(ws.1,(block ws.2).1))
@[fun_prop] theorem parse_poly : Poly parse := by unfold parse; fun_prop

def literalRep (l : Literal) : RawLiteral := (l.1,Computability.encodeNat l.2)
def inputRep (input : Input) : RawInput :=
  (input.terms.map (List.map literalRep),
    (input.weights.map Computability.encodeNat,Computability.encodeNat input.threshold))

theorem literal_encoded (l : Literal) (rest : List Bool) :
    literal (encodeLiteral l ++ rest) = (literalRep l,rest) := by
  simp [literal,encodeLiteral,block_encode,literalRep]

theorem natBlock_nonempty (n : Nat) : 1 ≤ (natBlock n).length := by
  simp only [natBlock,unaryLengthBlock,List.length_append,List.length_singleton]
  omega

theorem term_encoded (t : List Literal) (rest : List Bool) :
    term (encodeTerm t ++ rest) = (t.map literalRep,rest) := by
  exact list_encoded literal encodeLiteral literalRep literal_encoded
    (by intro l; simp [encodeLiteral]) t rest

theorem terms_encoded (ts : List (List Literal)) (rest : List Bool) :
    terms (encodeTerms ts ++ rest) = (ts.map (List.map literalRep),rest) := by
  exact list_encoded term encodeTerm (List.map literalRep) term_encoded
    (by intro t; have h := natBlock_nonempty t.length; simp only [encodeTerm,List.length_append]; omega) ts rest

theorem weights_encoded (ws : List Nat) (rest : List Bool) :
    weights (encodeNatList ws ++ rest) = (ws.map Computability.encodeNat,rest) :=
  list_encoded block natBlock Computability.encodeNat block_encode natBlock_nonempty ws rest

@[simp] theorem block_self (n : Nat) : block (natBlock n) = (Computability.encodeNat n,[]) := by
  simpa using block_encode n []

theorem parse_encoded (input : Input) : parse (encodeInput input) = inputRep input := by
  simp [parse,encodeInput,List.append_assoc,block_encode,terms_encoded,weights_encoded,inputRep]

end WeightedUDNF.PolyParser

/- UDNFSemantics -/
set_option autoImplicit false
namespace WeightedUDNF.Formal
open OAI.CPTSeparation

/-- Compatibility of a term with the bits fixed so far. -/
def compatible (term : List Literal) (bits : List Bool) : Bool :=
  term.all fun l => match bits[l.2]? with
    | none => true
    | some b => l.1 == b

def acceptsBit (term : List Literal) (i : Nat) (b : Bool) : Bool :=
  term.all fun l => if l.2 = i then l.1 == b else true

def bitScalar (b : Bool) : Scalar := if b then 1 else 0

@[simp] theorem bitScalar_and (a b : Bool) :
    bitScalar (a && b) = bitScalar a * bitScalar b := by
  cases a <;> cases b <;> simp [bitScalar]

theorem compatible_append (term : List Literal) (bits : List Bool) (b : Bool) :
    compatible term (bits ++ [b]) = (compatible term bits && acceptsBit term bits.length b) := by
  have hp (l : Literal) :
      (match (bits ++ [b])[l.2]? with | none => true | some v => l.1 == v) =
      ((match bits[l.2]? with | none => true | some v => l.1 == v) &&
        (if l.2 = bits.length then l.1 == b else true)) := by
    by_cases h : l.2 < bits.length
    · simp [List.getElem?_append, h, Nat.ne_of_lt h]
    · have hh : bits[l.2]? = none := List.getElem?_eq_none (by omega)
      by_cases he : l.2 = bits.length
      · simp [he]
      · have hd : l.2 - bits.length ≠ 0 := by omega
        simp [List.getElem?_append, h, he, hd]
  induction term with
  | nil => rfl
  | cons l ls ih =>
    simpa only [compatible, acceptsBit, List.all_cons, hp, Bool.and_assoc,
      Bool.and_left_comm, Bool.and_comm] using congrArg
        (fun x => ((match bits[l.2]? with | none => true | some v => l.1 == v) &&
          (if l.2 = bits.length then l.1 == b else true)) && x) ih

def state (input : Input) (bits : List Bool) : GF2Span.Vec (input.terms.length + 1) :=
  Fin.cases 1 (fun j => bitScalar (compatible (input.terms.get j) bits))

def mask (input : Input) (i : Nat) (b : Bool) : GF2Span.Vec (input.terms.length + 1) :=
  Fin.cases 1 (fun j => bitScalar (acceptsBit (input.terms.get j) i b))

def transition (input : Input) (i : Nat) (b : Bool) :
    GF2Span.Vec (input.terms.length + 1) →ₗ[Scalar] GF2Span.Vec (input.terms.length + 1) where
  toFun v := fun j => mask input i b j * v j
  map_add' := by intros; ext j; exact mul_add _ _ _
  map_smul' := by intros; ext j; simp [mul_left_comm]

theorem state_append (input : Input) (bits : List Bool) (b : Bool) :
    state input (bits ++ [b]) = transition input bits.length b (state input bits) := by
  funext j
  cases j using Fin.cases with
  | zero => simp [state, transition, mask]
  | succ j => simp [state, transition, mask, compatible_append, mul_comm]

theorem compatible_full (input : Input) (hr : literalsInRange input)
    (a : Fin input.variableCount → Bool) (term : List Literal) (ht : term ∈ input.terms) :
    compatible term (List.ofFn a) = termSatisfied input.variableCount a term := by
  unfold compatible termSatisfied
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  apply forall_congr'
  intro l
  apply forall_congr'
  intro hl
  have h := hr term ht l hl
  simp only [List.getElem?_ofFn, h, dif_pos, literalSatisfied]
  cases l.1 <;> cases a ⟨l.2, h⟩ <;> rfl

theorem sum_indicators {α : Type} (xs : List α) (f : α → Bool)
    (h : xs.Pairwise (fun a b => ¬ (f a = true ∧ f b = true))) :
    (xs.map (fun a => bitScalar (f a))).sum = bitScalar (xs.any f) := by
  induction xs with
  | nil => simp [bitScalar]
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
    by_cases hf : f a = true
    · have hz : ∀ b ∈ xs, f b = false := by
        intro b hb
        cases hfb : f b with
        | false => rfl
        | true => exact False.elim (ha b hb ⟨hf, hfb⟩)
      have hmap : xs.map (fun b => bitScalar (f b)) = xs.map (fun _ => (0 : Scalar)) := by
        apply List.map_congr_left
        intro b hb
        simp [hz b hb, bitScalar]
      rw [List.map_cons, List.sum_cons, hmap]
      simp [hf, bitScalar]
    · have hf' : f a = false := Bool.eq_false_iff.mpr hf
      simpa [hf', bitScalar] using ih ht

def terminal (input : Input) : GF2Span.Vec (input.terms.length + 1) →ₗ[Scalar] Scalar :=
  LinearMap.proj 0 - ∑ j : Fin input.terms.length, LinearMap.proj j.succ

theorem terminal_full (input : Input) (hr : literalsInRange input)
    (hu : pairwiseUnambiguous input) (a : Fin input.variableCount → Bool) :
    terminal input (state input (List.ofFn a)) ≠ 0 ↔ dnfSatisfied input a = false := by
  have hp : input.terms.Pairwise (fun l r =>
      ¬ (termSatisfied input.variableCount a l = true ∧ termSatisfied input.variableCount a r = true)) :=
    hu.imp (fun h hab => h ⟨a, hab⟩)
  have hs := sum_indicators input.terms (termSatisfied input.variableCount a) hp
  have hc : (∑ j : Fin input.terms.length,
      bitScalar (compatible (input.terms.get j) (List.ofFn a))) =
      (input.terms.map (fun t => bitScalar (termSatisfied input.variableCount a t))).sum := by
    calc
      _ = ∑ j : Fin input.terms.length,
          bitScalar (termSatisfied input.variableCount a (input.terms.get j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [compatible_full input hr a _ (List.get_mem _ _)]
      _ = _ := by
        rw [← List.sum_ofFn]
        congr 1
        simpa only [List.get_eq_getElem] using
          List.ofFn_getElem_eq_map input.terms
            (fun t => bitScalar (termSatisfied input.variableCount a t))

  simp only [terminal, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.proj_apply,
    state, Fin.cases_zero, Fin.cases_succ]
  rw [hc, hs]
  unfold dnfSatisfied
  cases input.terms.any (termSatisfied input.variableCount a) <;> simp [bitScalar]

def score (input : Input) (bits : List Bool) : Nat :=
  ((List.range bits.length).map (fun i =>
    if bits.getD i false then input.weights.getD i 0 else 0)).sum

theorem score_append (input : Input) (bits : List Bool) (b : Bool) :
    score input (bits ++ [b]) = score input bits +
      (if b then input.weights.getD bits.length 0 else 0) := by
  unfold score
  simp only [List.length_append, List.length_singleton, List.range_succ,
    List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  congr 1
  · apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have h : i < bits.length := List.mem_range.mp hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, h]
  · simp [List.getD_eq_getElem?_getD]

theorem score_full (input : Input) (a : Fin input.variableCount → Bool) :
    score input (List.ofFn a) = assignmentWeight input a := by
  unfold score assignmentWeight
  simp only [List.length_ofFn, List.sum_eq_foldl, List.foldl_map]
  congr 1
  funext total i
  by_cases h : i < input.variableCount <;>
    simp [List.getD_eq_getElem?_getD, h]

def entry (input : Input) (bits : List Bool) : Nat × GF2Span.Vec (input.terms.length + 1) :=
  (score input bits, state input bits)

def all (input : Input) (i : Nat) : List (Nat × GF2Span.Vec (input.terms.length + 1)) :=
  WeightedBasis.allStates (state input [])
    (fun i => transition input i false) (fun i => transition input i true)
    (fun i => input.weights.getD i 0) i

theorem all_sound (input : Input) (i : Nat) (e : Nat × GF2Span.Vec (input.terms.length + 1))
    (he : e ∈ all input i) : ∃ bits, bits.length = i ∧ e = entry input bits := by
  induction i generalizing e with
  | zero =>
    simp only [all, WeightedBasis.allStates, List.mem_singleton] at he
    exact ⟨[], rfl, he⟩
  | succ i ih =>
    change e ∈ WeightedBasis.branches _ _ _ (all input i) at he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      obtain ⟨bits, hl, rfl⟩ := ih a ha
      refine ⟨bits ++ [false], by simp [hl], ?_⟩
      simp [entry, score_append, state_append, WeightedBasis.extend, hl]
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      obtain ⟨bits, hl, rfl⟩ := ih a ha
      refine ⟨bits ++ [true], by simp [hl], ?_⟩
      simp [entry, score_append, state_append, WeightedBasis.extend, hl]

theorem all_complete (input : Input) (bits : List Bool) : entry input bits ∈ all input bits.length := by
  induction bits using List.reverseRecOn with
  | nil => simp [entry, score, all, WeightedBasis.allStates]
  | append_singleton bits b ih =>
    simp only [List.length_append, List.length_singleton, all, WeightedBasis.allStates]
    change entry input (bits ++ [b]) ∈ WeightedBasis.branches _ _ _ (all input bits.length)
    cases b with
    | false =>
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨entry input bits, ih, ?_⟩
      simp [entry, WeightedBasis.extend, score_append, state_append]
    | true =>
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨entry input bits, ih, ?_⟩
      simp [entry, WeightedBasis.extend, score_append, state_append]

def candidates (input : Input) :=
  ExecutableBasis.retained (state input [])
    (fun i => transition input i false) (fun i => transition input i true)
    (fun i => input.weights.getD i 0) input.variableCount

def solve (input : Input) : Bool :=
  (candidates input).any fun e =>
    decide (input.threshold ≤ e.1) && decide (terminal input e.2 ≠ 0)

theorem solve_correct (input : Input) (hv : validInput input) : solve input = decision input := by
  classical
  obtain ⟨_, _, _, hr, _, hu⟩ := hv
  apply Bool.eq_iff_iff.mpr
  have hd : decision input = true ↔ hasFalsifyingAssignment input := by
    simp only [decision, decide_eq_true_eq]
  rw [hd]
  simp only [solve, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  unfold hasFalsifyingAssignment
  change (∃ e ∈ candidates input, input.threshold ≤ e.1 ∧ terminal input e.2 ≠ 0) ↔ _
  unfold candidates
  rw [← ExecutableBasis.threshold_iff]
  change (∃ e ∈ all input input.variableCount,
    input.threshold ≤ e.1 ∧ terminal input e.2 ≠ 0) ↔ _
  constructor
  · rintro ⟨e, he, hw, ht⟩
    obtain ⟨bits, hl, rfl⟩ := all_sound input _ e he
    let a : Fin input.variableCount → Bool := fun j => bits[j.val]'(by omega)
    have hb : List.ofFn a = bits := by
      apply List.ext_getElem
      · simp [hl]
      · intro i hi hi'
        simp [a]
    refine ⟨a, ?_, ?_⟩
    · apply (terminal_full input hr hu a).mp
      simpa [hb, entry] using ht
    · simpa [← score_full input a, hb, entry] using hw
  · rintro ⟨a, ha, hw⟩
    refine ⟨entry input (List.ofFn a), ?_, ?_, ?_⟩
    · simpa using all_complete input (List.ofFn a)
    · simpa [entry, score_full] using hw
    · exact (terminal_full input hr hu a).mpr ha

/-- Reject an invalid oversized variable declaration before iterating. -/
def guardedSolve (input : Input) : Bool :=
  if input.variableCount = input.weights.length then solve input else false

theorem guardedSolve_correct (input : Input) (hv : validInput input) :
    guardedSolve input = decision input := by
  rw [guardedSolve, if_pos hv.1.symm]
  exact solve_correct input hv

end WeightedUDNF.Formal

/- PolySolver -/
set_option autoImplicit false
namespace WeightedUDNF.PolySolver
open OAI.BinaryMatching.StackCode OAI.CPTSeparation
open Polynomial PolyParser PolyBasis
abbrev Terms := List (List RawLiteral)

def literalOK (z : (Nat × Bool) × RawLiteral) : Bool :=
  if boundedValue (z.1.1+1) z.2.2 = z.1.1 then z.2.1 == z.1.2 else true
@[fun_prop] theorem literalOK_poly : Poly literalOK := by
  unfold literalOK
  have he : Poly (fun z : (Nat × Bool) × RawLiteral =>
    decide (boundedValue (z.1.1+1) z.2.2 = z.1.1)) := by fun_prop
  have hb : Poly (fun z : (Nat × Bool) × RawLiteral => z.2.1 == z.1.2) := by
    have h : Poly (fun z : (Nat × Bool) × RawLiteral =>
      if z.2.1 then z.1.2 else !z.1.2) := by fun_prop
    exact h.congr (by intro z; cases z.2.1 <;> cases z.1.2 <;> rfl)
  have h : Poly (fun z : (Nat × Bool) × RawLiteral =>
      if decide (boundedValue (z.1.1+1) z.2.2 = z.1.1) then z.2.1 == z.1.2 else true) := by
    exact Poly.cond _ _ _ he (by fun_prop) hb
  exact h.congr (fun _ => by simp)

def termOK (z : (Nat × Bool) × List RawLiteral) : Bool :=
  (z.2.map (fun l => literalOK (z.1,l))).all id

@[fun_prop] theorem all_poly : Poly (fun xs : List Bool => xs.all id) := by
  have h : Poly (fun xs : List Bool => (xs.filter Bool.not).isEmpty) := by fun_prop
  exact h.congr (by intro xs; induction xs with
    | nil => rfl
    | cons b xs ih => cases b <;> simp_all)

@[fun_prop] theorem termOK_poly : Poly termOK := by
  unfold termOK
  exact Poly.comp _ _ all_poly (Poly.listMapParam literalOK literalOK_poly)

def mask (z : (Nat × Bool) × Terms) : List Scalar :=
  1 :: z.2.map (fun t => PolyGaussian.fromBool (termOK (z.1,t)))
@[fun_prop] theorem mask_poly : Poly mask := by
  have hm := Poly.listMapParam (fun z : (Nat × Bool) × List RawLiteral => PolyGaussian.fromBool (termOK z))
    (by fun_prop)
  exact Poly.comp (fun xs : List Scalar => 1::xs) _ (by fun_prop) hm

def act (z : List Scalar × List Scalar) : List Scalar :=
  (z.1.zip z.2).map (fun xy => xy.1 * xy.2)
@[fun_prop] theorem act_poly : Poly act := by unfold act; fun_prop

def extend (z : (List Bool × List Scalar) × Entry) : Entry :=
  (BinaryWeights.add z.2.1 z.1.1, act (z.1.2,z.2.2))
@[fun_prop] theorem extend_poly : Poly extend := by
  unfold extend
  apply Poly.pair
  · exact Poly.comp _ (fun z : (List Bool × List Scalar) × Entry => (z.2.1,z.1.1)) BinaryWeights.add_poly (by fun_prop)
  · fun_prop

def branches (ts : Terms) (i : Nat) (w : List Bool) (cs : List Entry) : List Entry :=
  cs.map (fun e => (e.1,act (mask ((i,false),ts),e.2))) ++
    cs.map (fun e => extend ((w,mask ((i,true),ts)),e))

@[fun_prop] theorem branches_poly : Poly (fun z : (Terms × Nat) × (List Bool × List Entry) =>
    branches z.1.1 z.1.2 z.2.1 z.2.2) := by
  have h0 := Poly.listMapParam (fun z : List Scalar × Entry => (z.2.1,act (z.1,z.2.2))) (by fun_prop)
  have h1 := Poly.listMapParam extend extend_poly
  unfold branches
  apply Poly.comp _ (fun z : (Terms × Nat) × (List Bool × List Entry) =>
    (z.2.2.map (fun e => (e.1,act (mask ((z.1.2,false),z.1.1),e.2))),
      z.2.2.map (fun e => extend ((z.2.1,mask ((z.1.2,true),z.1.1)),e)))) Poly.listAppend
  apply Poly.pair
  · exact Poly.comp _ (fun z : (Terms × Nat) × (List Bool × List Entry) =>
      (mask ((z.1.2,false),z.1.1),z.2.2)) h0 (by fun_prop)
  · exact Poly.comp _ (fun z : (Terms × Nat) × (List Bool × List Entry) =>
      ((z.2.1,mask ((z.1.2,true),z.1.1)),z.2.2)) h1 (by fun_prop)

abbrev State := (Terms × Nat) × (Nat × List Entry)

def step (z : State × List Bool) : State :=
  let cs := PolyBasis.reduce (branches z.1.1.1 z.1.2.1 z.2 z.1.2.2)
  (z.1.1,(z.1.2.1+1,if (encode cs).length ≤ z.1.1.2 then cs else []))

@[fun_prop] theorem step_poly : Poly step := by
  have hb : Poly (fun z : State × List Bool => branches z.1.1.1 z.1.2.1 z.2 z.1.2.2) :=
    Poly.comp _ (fun z : State × List Bool => ((z.1.1.1,z.1.2.1),(z.2,z.1.2.2))) branches_poly (by fun_prop)
  have hc : Poly (fun z : State × List Bool => PolyBasis.reduce (branches z.1.1.1 z.1.2.1 z.2 z.1.2.2)) := by fun_prop
  have hl : Poly (fun z : State × List Bool =>
    (encode (PolyBasis.reduce (branches z.1.1.1 z.1.2.1 z.2 z.1.2.2))).length) :=
    Poly.comp (fun cs : List Entry => (encode cs).length)
      (fun z : State × List Bool => PolyBasis.reduce (branches z.1.1.1 z.1.2.1 z.2 z.1.2.2)) Poly.codeLength hc
  have hp : Poly (fun z : State × List Bool =>
    decide ((encode (PolyBasis.reduce (branches z.1.1.1 z.1.2.1 z.2 z.1.2.2))).length ≤ z.1.1.2)) :=
    Poly.comp _ _ Poly.natLE (Poly.pair _ _ hl (by fun_prop))
  unfold step
  have hh : Poly (fun z : State × List Bool =>
    if decide ((encode (PolyBasis.reduce (branches z.1.1.1 z.1.2.1 z.2 z.1.2.2))).length ≤ z.1.1.2)
    then PolyBasis.reduce (branches z.1.1.1 z.1.2.1 z.2 z.1.2.2) else []) :=
    Poly.cond _ _ _ hp (by fun_prop) hc
  have he : Poly (fun z : State × List Bool =>
    if (encode (PolyBasis.reduce (branches z.1.1.1 z.1.2.1 z.2 z.1.2.2))).length ≤ z.1.1.2
    then PolyBasis.reduce (branches z.1.1.1 z.1.2.1 z.2 z.1.2.2) else []) := hh.congr (fun _ => by simp)
  exact Poly.pair _ _ (by fun_prop) (Poly.pair _ _ (by fun_prop) he)

theorem step_size (z : State × List Bool) : (step z).1 = z.1.1 ∧
    (step z).2.1 = z.1.2.1+1 ∧ (encode (step z).2.2).length ≤ z.1.1.2 := by
  refine ⟨rfl,rfl,?_⟩
  simp only [step]
  split <;> simp_all

theorem fold_size (ws : List (List Bool)) (s : State) :
    let r := ws.foldl (fun s w => step (s,w)) s
    r.1 = s.1 ∧ r.2.1 = s.2.1 + ws.length ∧
      (encode r.2.2).length ≤ max (encode s.2.2).length s.1.2 := by
  induction ws generalizing s with
  | nil => simp
  | cons w ws ih =>
    have hs := step_size (s,w)
    have hi := ih (step (s,w))
    simp only [List.foldl_cons,List.length_cons]
    refine ⟨hi.1.trans hs.1,?_,?_⟩
    · rw [hi.2.1,hs.2.1]; simp only; omega
    · exact hi.2.2.trans (max_le (hs.2.2.trans (Nat.le_max_right _ _))
        (by rw [hs.1]; exact Nat.le_max_right _ _))

@[fun_prop] theorem fold_poly : Poly (fun z : List (List Bool) × State => z.1.foldl (fun s w => step (s,w)) z.2) := by
  apply Poly.listFold [] step step_poly (4*X+4)
  intro z k
  obtain ⟨h1,h2,h3⟩ := fold_size (z.1.take k) z.2
  have hl0 : (z.1.take k).length ≤ z.1.length := by simp
  have hl := hl0.trans (list_length_le_code z.1)
  simp only [encode_prod,pairBits_length,encode_nat,unary_length,eval_add,eval_mul,eval_ofNat,eval_X] at *
  rw [h1,h2]
  omega

def limit (input : RawInput) : Nat := 40 * ((encode input).length+1)^3

def initial (input : RawInput) : State :=
  ((input.1,limit input),(0,[([],List.replicate (input.1.length+1) 1)]))
@[fun_prop] theorem initial_poly : Poly initial := by unfold initial limit; fun_prop

def candidates (input : RawInput) : List Entry :=
  (input.2.1.foldl (fun s w => step (s,w)) (initial input)).2.2
@[fun_prop] theorem candidates_poly : Poly candidates := by
  unfold candidates
  exact Poly.comp (fun s : State => s.2.2) _ (by fun_prop)
    (Poly.comp _ (fun input : RawInput => (input.2.1,initial input)) fold_poly (by fun_prop))

def terminal (v : List Scalar) : Scalar := v.headD 0 - v.tail.foldl (·+·) 0

@[fun_prop] theorem scalar_add_poly : Poly (fun z : Scalar × Scalar => z.1 + z.2) :=
  PolyGaussian.scalar_sub_poly.congr (fun z => by
    rcases PolyGaussian.scalar_cases z.1 with h1|h1 <;>
    rcases PolyGaussian.scalar_cases z.2 with h2|h2 <;> rw [h1,h2] <;> decide)

@[fun_prop] theorem terminal_poly : Poly terminal := by
  have hf := Poly.listFoldAdd (fun z : Scalar × Scalar => z.1+z.2) scalar_add_poly 0 (by intro z; simp)
  have hs : Poly (fun xs : List Scalar => xs.tail.foldl (·+·) 0) :=
    Poly.comp _ (fun xs : List Scalar => (xs.tail,0)) hf (by fun_prop)
  unfold terminal
  exact Poly.comp _ (fun xs : List Scalar => (xs.headD 0,xs.tail.foldl (·+·) 0))
    PolyGaussian.scalar_sub_poly (Poly.pair _ _ (by fun_prop) hs)

def answer (input : RawInput) : Bool :=
  (candidates input).any (fun e => BinaryWeights.le input.2.2 e.1 && PolyGaussian.toBool (terminal e.2))

@[fun_prop] theorem answer_poly : Poly answer := by
  have hp : Poly (fun z : List Bool × Entry => BinaryWeights.le z.1 z.2.1 && PolyGaussian.toBool (terminal z.2.2)) := by
    have hl := Poly.comp _ (fun z : List Bool × Entry => (z.1,z.2.1)) BinaryWeights.le_poly (by fun_prop)
    fun_prop
  have hm := Poly.listMapParam _ hp
  have h : Poly (fun input : RawInput => !((candidates input).map
      (fun e => !(BinaryWeights.le input.2.2 e.1 && PolyGaussian.toBool (terminal e.2)))).all id) := by
    have hn := Poly.listMapParam (fun z : List Bool × Entry =>
      !(BinaryWeights.le z.1 z.2.1 && PolyGaussian.toBool (terminal z.2.2))) (by fun_prop)
    exact Poly.comp Bool.not _ (by fun_prop) (Poly.comp _ _ all_poly
      (Poly.comp _ (fun input : RawInput => (input.2.2,candidates input)) hn (by fun_prop)))
  exact h.congr (fun input => by simp [answer,List.any_eq_not_all_not])

end WeightedUDNF.PolySolver

/- SolverBounds -/
set_option autoImplicit false
namespace WeightedUDNF.PolySolver
open OAI.BinaryMatching.StackCode OAI.CPTSeparation
open PolyParser PolyBasis

def retained (input : RawInput) : Nat → List Entry
  | 0 => [([],List.replicate (input.1.length+1) 1)]
  | i+1 => PolyBasis.reduce (branches input.1 i (input.2.1[i]?.getD []) (retained input i))

theorem mask_length (ts : Terms) (i : Nat) (b : Bool) : (mask ((i,b),ts)).length = ts.length+1 := by
  simp [mask]

theorem branches_shape (ts : Terms) (i : Nat) (w : List Bool) (cs : List Entry)
    (B : Nat) (hc : ∀ e ∈ cs, e.2.length = ts.length+1 ∧ e.1.length ≤ B) :
    ∀ e ∈ branches ts i w cs, e.2.length = ts.length+1 ∧ e.1.length ≤ B+w.length := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    have h := hc a ha
    constructor
    · simp [act,mask_length,h.1]
    · exact h.2.trans (Nat.le_add_right _ _)
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    have h := hc a ha
    constructor
    · simp [extend,act,mask_length,h.1]
    · exact (BinaryWeights.add_length a.1 w).trans (Nat.add_le_add_right h.2 _)

theorem rawInput_sizes (input : RawInput) :
    input.1.length ≤ (encode input).length ∧
    input.2.1.length ≤ (encode input).length ∧
    ∀ i : Nat, (input.2.1[i]?.getD []).length ≤ (encode input).length := by
  have ht := list_length_le_code input.1
  have hw := list_length_le_code input.2.1
  refine ⟨?_,?_,?_⟩
  · simp only [encode_prod,pairBits_length]; omega
  · simp only [encode_prod,pairBits_length]; omega
  · intro i
    by_cases hi : i < input.2.1.length
    · rw [List.getElem?_eq_getElem hi,Option.getD_some]
      have he := element_code_le input.2.1 input.2.1[i] (List.getElem_mem hi)
      have hl := list_length_le_code input.2.1[i]
      simp only [encode_prod,pairBits_length]
      omega
    · simp [List.getElem?_eq_none (by omega : input.2.1.length ≤ i)]

theorem retained_shape (input : RawInput) (i : Nat) :
    ∀ e ∈ retained input i, e.2.length = input.1.length+1 ∧ e.1.length ≤ i*(encode input).length := by
  induction i with
  | zero => simp [retained]
  | succ i ih =>
    intro e he
    have h := branches_shape input.1 i (input.2.1[i]?.getD []) (retained input i)
      (i*(encode input).length) ih e (reduce_subset _ e he)
    exact ⟨h.1,h.2.trans (by have hw := (rawInput_sizes input).2.2 i; nlinarith)⟩

theorem retained_length (input : RawInput) (i : Nat) : (retained input i).length ≤ input.1.length+1 := by
  cases i with
  | zero => simp [retained]
  | succ i =>
    exact reduce_length _ (fun e he =>
      (branches_shape input.1 i _ _ _ (retained_shape input i) e he).1)

theorem retained_code_bound (input : RawInput) (i : Nat) (hi : i ≤ input.2.1.length) :
    (encode (retained input i)).length ≤ limit input := by
  let N := (encode input).length
  let d := input.1.length+1
  have hs := rawInput_sizes input
  have hn : i ≤ N := hi.trans hs.2.1
  have hd : d ≤ N+1 := Nat.add_le_add_right hs.1 1
  have he : ∀ e ∈ retained input i, (encode e).length ≤ 6*(N*N)+3*d+1 := by
    intro e he
    have h := retained_shape input i e he
    have hb : e.1.length ≤ N*N := h.2.trans (Nat.mul_le_mul_right N hn)
    simp only [encode_prod,pairBits_length,BinaryWeights.code_bits_length,PolyGaussian.code_scalars_length,h.1]
    dsimp [d]
    omega
  have hcode := list_code_bound (retained input i) _ he
  have hlen := retained_length input i
  have hm := Nat.mul_le_mul hlen (by omega : 2*(6*(N*N)+3*d+1)+1 ≤ 12*(N*N)+6*d+3)
  have hm2 := Nat.mul_le_mul hd (by omega : 12*(N*N)+6*d+3 ≤ 12*(N*N)+6*(N+1)+3)
  change (encode (retained input i)).length ≤ 40*(N+1)^3
  nlinarith

theorem fold_take_retained (input : RawInput) (i : Nat) (hi : i ≤ input.2.1.length) :
    (input.2.1.take i).foldl (fun s w => step (s,w)) (initial input) =
      ((input.1,limit input),(i,retained input i)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hil : i < input.2.1.length := by omega
    rw [List.take_succ_eq_append_getElem hil,List.foldl_append,ih (by omega)]
    simp only [List.foldl_cons,List.foldl_nil,step]
    have hb := retained_code_bound input (i+1) hi
    simp only [retained,List.getElem?_eq_getElem hil,Option.getD_some] at hb ⊢
    rw [if_pos hb]

theorem candidates_eq (input : RawInput) : candidates input = retained input input.2.1.length := by
  have h := fold_take_retained input input.2.1.length (by rfl)
  simp only [List.take_length] at h
  exact congrArg (fun s : State => s.2.2) h

end WeightedUDNF.PolySolver

/- SolverCorrect -/
set_option autoImplicit false
namespace WeightedUDNF.PolySolver
open OAI.BinaryMatching.StackCode OAI.CPTSeparation
open PolyParser PolyBasis

theorem literalOK_encoded (l : Literal) (i : Nat) (b : Bool) :
    literalOK ((i,b),literalRep l) = if l.2 = i then l.1 == b else true := by
  simp only [literalOK,literalRep,boundedValue_eq,value_encode]
  have h : min (i+1) l.2 = i ↔ l.2 = i := by omega
  simp only [h]

theorem termOK_encoded (t : List Literal) (i : Nat) (b : Bool) :
    termOK ((i,b),t.map literalRep) = Formal.acceptsBit t i b := by
  simp only [termOK,List.map_map,List.all_map,Function.comp_def,literalOK_encoded,Formal.acceptsBit]
  rfl

theorem mask_encoded (input : Input) (i : Nat) (b : Bool) :
    mask ((i,b),(inputRep input).1) = List.ofFn (Formal.mask input i b) := by
  rw [List.ofFn_succ]
  simp only [mask,inputRep,List.map_map,Function.comp_def,termOK_encoded,Formal.mask,
    Fin.cases_zero,Fin.cases_succ,Formal.bitScalar,PolyGaussian.fromBool]
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp

theorem act_ofFn {d : Nat} (f v : GF2Span.Vec d) :
    act (List.ofFn f,List.ofFn v) = List.ofFn (fun i => f i * v i) := by
  apply List.ext_getElem
  · simp [act]
  · intro i hi hj
    simp [act]

theorem vector_ofFn {d : Nat} (v : GF2Span.Vec d) : vector d (List.ofFn v) = v := by
  funext i
  simp [vector]

theorem act_encoded (input : Input) (i : Nat) (b : Bool) (v : List Scalar)
    (hv : v.length = input.terms.length+1) :
    vector (input.terms.length+1) (act (mask ((i,b),(inputRep input).1),v)) =
      Formal.transition input i b (vector (input.terms.length+1) v) := by
  rw [mask_encoded]
  have ha : act (List.ofFn (Formal.mask input i b),v) =
      List.ofFn (fun j => Formal.mask input i b j * vector (input.terms.length+1) v j) := by
    conv_lhs => arg 1; arg 2; rw [← vector_roundtrip v hv]
    exact act_ofFn _ _
  rw [ha,vector_ofFn]
  rfl

theorem weight_encoded (input : Input) (i : Nat) :
    BinaryWeights.value ((inputRep input).2.1[i]?.getD []) = input.weights.getD i 0 := by
  by_cases h : i < input.weights.length
  · simp [inputRep,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,value_encode,h]
  · have h' : input.weights.length ≤ i := by omega
    simp [inputRep,List.getD_eq_getElem?_getD,List.getElem?_eq_none h',h,BinaryWeights.value]

theorem branches_decode (input : Input) (i : Nat) (cs : List Entry)
    (hc : WellFormed (input.terms.length+1) cs) :
    (branches (inputRep input).1 i ((inputRep input).2.1[i]?.getD []) cs).map
      (decode (input.terms.length+1)) =
    WeightedBasis.branches (Formal.transition input i false) (Formal.transition input i true)
      (input.weights.getD i 0) (cs.map (decode (input.terms.length+1))) := by
  simp only [branches,WeightedBasis.branches,List.map_append,List.map_map,Function.comp_def]
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro e he
    simp only [decode,WeightedBasis.extend,Nat.add_zero]
    exact congrArg (fun v => (BinaryWeights.value e.1,v)) (act_encoded input i false e.2 (hc e he))
  · apply List.map_congr_left
    intro e he
    simp only [extend,decode,WeightedBasis.extend,BinaryWeights.add_value,weight_encoded]
    exact congrArg (fun v => (BinaryWeights.value e.1 + input.weights.getD i 0,v))
      (act_encoded input i true e.2 (hc e he))

theorem retained_decode (input : Input) (i : Nat) :
    (retained (inputRep input) i).map (decode (input.terms.length+1)) =
    ExecutableBasis.retained (Formal.state input [])
      (fun i => Formal.transition input i false) (fun i => Formal.transition input i true)
      (fun i => input.weights.getD i 0) i := by
  induction i with
  | zero =>
    simp only [retained,ExecutableBasis.retained,List.map_cons,List.map_nil,decode,BinaryWeights.value]
    congr 2
    funext j
    cases j using Fin.cases with
    | zero => simp [inputRep,vector,Formal.state]
    | succ j => simp [inputRep,vector,Formal.state,Formal.compatible,Formal.bitScalar]
  | succ i ih =>
    have hc : WellFormed (input.terms.length+1) (retained (inputRep input) i) := by
      intro e he
      simpa [inputRep] using (retained_shape (inputRep input) i e he).1
    have hb : WellFormed (input.terms.length+1)
        (branches (inputRep input).1 i ((inputRep input).2.1[i]?.getD []) (retained (inputRep input) i)) := by
      intro e he
      simpa [inputRep] using
        (branches_shape _ _ _ _ _ (retained_shape (inputRep input) i) e he).1
    rw [retained,reduce_decode _ hb,branches_decode input i _ hc,ih]
    rfl

theorem candidates_decode (input : Input) (hv : validInput input) :
    (candidates (inputRep input)).map (decode (input.terms.length+1)) = Formal.candidates input := by
  rw [candidates_eq]
  have hlen : (inputRep input).2.1.length = input.variableCount := by
    simpa [inputRep] using hv.1
  rw [hlen,retained_decode]
  rfl

theorem terminal_encoded (input : Input) (v : List Scalar) (hv : v.length = input.terms.length+1) :
    terminal v = Formal.terminal input (vector (input.terms.length+1) v) := by
  have h (w : GF2Span.Vec (input.terms.length+1)) :
      terminal (List.ofFn w) = Formal.terminal input w := by
    rw [terminal,List.ofFn_succ]
    simp [Formal.terminal]
    rw [← List.sum_eq_foldl,List.sum_ofFn]
  have he := h (vector (input.terms.length+1) v)
  rw [vector_roundtrip v hv] at he
  exact he

theorem answer_correct (input : Input) (hv : validInput input) : answer (inputRep input) = decision input := by
  rw [← Formal.solve_correct input hv]
  unfold Formal.solve
  rw [← candidates_decode input hv,List.any_map]
  unfold answer
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  apply exists_congr
  intro e
  apply and_congr_right
  intro he
  have hc : e.2.length = input.terms.length+1 := by
    rw [candidates_eq] at he
    simpa [inputRep] using (retained_shape (inputRep input) _ e he).1
  simp only [Bool.and_eq_true,BinaryWeights.le_correct,inputRep,value_encode,decode,
    decide_eq_true_eq,Function.comp_apply]
  rw [terminal_encoded input e.2 hc]
  have ht := PolyGaussian.scalar_cases (Formal.terminal input (vector (input.terms.length+1) e.2))
  rcases ht with ht | ht <;> simp [ht,PolyGaussian.toBool]
  exact decide_eq_true_iff.symm

end WeightedUDNF.PolySolver

/- FullTheorem -/
set_option autoImplicit false
namespace WeightedUDNF.Full
open OAI.BinaryMatching.StackCode

def decisionFn (input : Input) : Bool := PolySolver.answer (PolyParser.inputRep input)

def wordFn (b : Bits) : Bool := PolySolver.answer (PolyParser.parse b.data)

 theorem wordFn_poly : Poly wordFn := by
  unfold wordFn
  exact Poly.comp _ _ PolySolver.answer_poly (Poly.comp _ _ PolyParser.parse_poly Poly.bitsDecode)

noncomputable def machine : Turing.TM2ComputableInPolyTime encodeInput
    Computability.encodingBoolBool.encode decisionFn :=
  (wordFn_poly.routine.reindex encodeInput Computability.encodingBoolBool.encode decisionFn
    (fun input => Bits.mk (encodeInput input)) (fun _ => rfl)
    (fun input => by simp [wordFn,decisionFn,PolyParser.parse_encoded]; rfl)).machine

end WeightedUDNF.Full

theorem solution :
    ∃ f : WeightedUDNF.Input → Bool,
      ∃ machine : Turing.TM2ComputableInPolyTime WeightedUDNF.encodeInput
        Computability.encodingBoolBool.encode f,
        ∀ input, WeightedUDNF.validInput input → f input = WeightedUDNF.decision input := by
  exact ⟨WeightedUDNF.Full.decisionFn,WeightedUDNF.Full.machine,WeightedUDNF.PolySolver.answer_correct⟩

/-
Third-party license for the adapted openai/math code above.
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

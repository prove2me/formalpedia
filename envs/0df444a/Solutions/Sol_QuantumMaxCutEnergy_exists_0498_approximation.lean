-- Prove2me | solution 1 for QuantumMaxCutEnergy.exists_0498_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T00:38:41.920942+00:00
-- url     : https://prove2.me/submissions/8fa134a9-a099-4153-8e53-fdcd1e8d040f

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

-- Local source: runtime-reuse/QMCUpstreamRuntime.lean

/-! Concrete finite Boolean-stack polynomial-time arithmetic framework.
Extracted from OpenAI math, source revision 4eaee87548250b2682affda7d05d947c05554bae, Apache-2.0.
Unrelated Gaussian/LP declarations omitted. Deprecated conditional lemma names ported to Lean4.33.1.
No axioms or proof gaps added. -/

-- Source module: OAI.Combinatorics.KMedian.Binary.BooleanMachine

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Turing StateTransition Function Finset

structure Machine where
  K : Type
  [decK : DecidableEq K]
  [finK : Fintype K]
  input : K
  output : K
  Label : Type
  [finLabel : Fintype Label]
  main : Label
  State : Type
  [finState : Fintype State]
  initial : State
  code : Label → TM2.Stmt (fun _ : K => Bool) Label State

attribute [instance] Machine.decK Machine.finK Machine.finLabel Machine.finState

namespace Machine

def tm (M : Machine) : FinTM2 where
  K := M.K
  k₀ := M.input
  k₁ := M.output
  Γ _ := Bool
  Λ := M.Label
  main := M.main
  σ := M.State
  initialState := M.initial
  m := M.code

instance allWorkFinite (M : Machine) (k : M.tm.K) : Fintype (M.tm.Γ k) :=
  inferInstanceAs (Fintype Bool)

abbrev Cfg (M : Machine) := TM2.Cfg (fun _ : M.K => Bool) M.Label M.State

def initialCfg (M : Machine) (s : List Bool) : M.Cfg :=
  ⟨some M.main, M.initial, fun k => if k=M.input then s else []⟩

def finalCfg (M : Machine) (s : List Bool) : M.Cfg :=
  ⟨none, M.initial, fun k => if k=M.output then s else []⟩

@[simp] theorem init_eq (M : Machine) (s : List Bool) :
    initList M.tm s=M.initialCfg s := by
  rfl

@[simp] theorem halt_eq (M : Machine) (s : List Bool) :
    haltList M.tm s=M.finalCfg s := by
  rfl

abbrev step (M : Machine) : M.Cfg → Option M.Cfg := TM2.step M.code

end Machine

theorem cfg_ext {K L S : Type} {a b : TM2.Cfg (fun _ : K => Bool) L S}
    (hl : a.l=b.l) (hv : a.var=b.var) (hs : a.stk=b.stk) : a=b := by
  cases a
  cases b
  cases hl
  cases hv
  cases hs
  rfl

inductive Trace {α : Type*} (f : α → Option α) : ℕ → α → α → Prop
  | refl (a : α) : Trace f 0 a a
  | cons {n : ℕ} {a b c : α} : f a=some b → Trace f n b c → Trace f (n+1) a c

namespace Trace
variable {α β : Type*} {f : α → Option α}

theorem trans {n m : ℕ} {a b c : α} (h : Trace f n a b) (g : Trace f m b c) :
    Trace f (n+m) a c := by
  induction h with
  | refl => simpa using g
  | cons hs ht ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cons hs (ih g)

theorem map {g : β → Option β} (e : α → β)
    (he : ∀ a b, f a=some b → g (e a)=some (e b))
    {n : ℕ} {a b : α} (h : Trace f n a b) : Trace g n (e a) (e b) := by
  induction h with
  | refl => exact refl _
  | cons hs _ ih => exact cons (he _ _ hs) ih

theorem iterate_eq {n : ℕ} {a b : α} (h : Trace f n a b) :
    (flip bind f)^[n] (some a)=some b := by
  induction h with
  | refl => rfl
  | cons hs ht ih =>
      rw [Function.iterate_succ_apply,show (flip bind f) (some _)=_ from hs]
      exact ih

theorem of_iterate {n : ℕ} {a b : α}
    (h : (flip bind f)^[n] (some a)=some b) : Trace f n a b := by
  induction n generalizing a with
  | zero =>
      have hab : a=b := Option.some.inj h
      subst b
      exact refl a
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      cases hc : f a with
      | none =>
          have hz : ∀ t : ℕ, (flip bind f)^[t] (none : Option α)=none := by
            intro t
            induction t with
            | zero => rfl
            | succ t iht =>
                rw [Function.iterate_succ_apply]
                exact iht
          change (flip bind f)^[n] (f a)=some b at h
          rw [hc,hz] at h
          contradiction
      | some c =>
          have hh : (flip bind f)^[n] (some c)=some b := by
            change (flip bind f)^[n] (f a)=some b at h
            rwa [hc] at h
          exact cons hc (ih hh)

def inTime {n : ℕ} {a b : α} (h : Trace f n a b) :
    EvalsToInTime f a (some b) n := ⟨⟨n,h.iterate_eq⟩,le_rfl⟩

theorem of_inTime {n : ℕ} {a b : α} (h : EvalsToInTime f a (some b) n) :
    Trace f h.steps a b := of_iterate h.evals_in_steps

end Trace

namespace Machine
variable {K L S : Type} [DecidableEq K]

def pushes : TM2.Stmt (fun _ : K => Bool) L S → ℕ
  | .push _ _ q => 1+pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

def volume [Fintype K] (s : K → List Bool) : ℕ := ∑ k, (s k).length

variable [Fintype K]

theorem volume_update (s : K → List Bool) (k : K) (v : List Bool) :
    volume (update s k v)+(s k).length=volume s+v.length := by
  classical
  unfold volume
  have he : (fun j => (update s k v j).length)=update (fun j => (s j).length) k v.length := by
    funext j
    simp only [update_apply]
    split <;> rfl
  rw [he,Finset.sum_update_of_mem (mem_univ k)]
  have hh := Finset.sum_erase_add (univ : Finset K) (fun j => (s j).length) (mem_univ k)
  simp only [Finset.sdiff_singleton_eq_erase]
  omega

theorem stepAux_volume (q : TM2.Stmt (fun _ : K => Bool) L S)
    (v : S) (s : K → List Bool) :
    volume (TM2.stepAux q v s).stk ≤ volume s+pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have h := ih v (update s k (g v::s k))
      have hv := volume_update s k (g v::s k)
      simp only [List.length_cons] at hv
      simpa only [TM2.stepAux,pushes,Nat.add_assoc] using (by omega :
        volume (TM2.stepAux q v (update s k (g v::s k))).stk≤volume s+(1+pushes q))
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have h := ih (g v (s k).head?) (update s k (s k).tail)
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      simp only [TM2.stepAux,pushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simpa only [TM2.stepAux,hg,Bool.false_eq_true,Bool.cond_false,pushes] using
          (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simpa only [TM2.stepAux,hg,Bool.cond_true,pushes] using
          (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto g => simp only [TM2.stepAux,pushes,Nat.add_zero,le_refl]
  | halt => simp only [TM2.stepAux,pushes,Nat.add_zero,le_refl]

def growth (M : Machine) : ℕ := ∑ l, pushes (M.code l)

theorem step_volume (M : Machine) (a b : M.Cfg) (h : M.step a=some b) :
    volume b.stk ≤ volume a.stk+M.growth := by
  rcases a with ⟨l,v,s⟩
  cases l with
  | none => cases h
  | some l =>
      have hb : b=TM2.stepAux (M.code l) v s := (Option.some.inj h).symm
      rw [hb]
      exact (stepAux_volume _ _ _).trans (Nat.add_le_add_left
        (show pushes (M.code l) ≤ M.growth from
          single_le_sum (f:=fun x => pushes (M.code x)) (fun _ _ => Nat.zero_le _) (mem_univ l)) _)

theorem trace_volume (M : Machine) {n : ℕ} {a b : M.Cfg}
    (h : Trace M.step n a b) : volume b.stk ≤ volume a.stk+n*M.growth := by
  induction h with
  | refl => simp
  | @cons n a b c hab hbc ih =>
      have hs := M.step_volume a b hab
      calc
        _ ≤ volume b.stk+n*M.growth := ih
        _ ≤ volume a.stk+(n+1)*M.growth := by rw [Nat.add_mul]; omega

@[simp] theorem initial_volume (M : Machine) (s : List Bool) :
    volume (M.initialCfg s).stk=s.length := by
  classical
  simp only [initialCfg,volume,apply_ite List.length,List.length_nil]
  simp

@[simp] theorem final_volume (M : Machine) (s : List Bool) :
    volume (M.finalCfg s).stk=s.length := by
  classical
  simp only [finalCfg,volume,apply_ite List.length,List.length_nil]
  simp

theorem output_length (M : Machine) {s t : List Bool} {n : ℕ}
    (h : TM2OutputsInTime M.tm s (some t) n) : t.length ≤ s.length+n*M.growth := by
  have ht : Trace M.step h.steps (M.initialCfg s) (M.finalCfg t) :=
    Trace.of_iterate h.evals_in_steps
  have hv := M.trace_volume ht
  simp only [initial_volume,final_volume] at hv
  exact hv.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end Machine
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BooleanEmbedding

namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Turing Function

structure Embedding (K L S K' L' S' : Type) [DecidableEq K] [DecidableEq K'] where
  key : K → K'
  read : S' → S
  write : S' → S → S'
  state : S → S'
  read_state : ∀ v, read (state v)=v
  write_state : ∀ v w, write (state v) w=state w
  stack : (K → List Bool) → K' → List Bool
  stack_key : ∀ s k, stack s (key k)=s k
  stack_update : ∀ s k x, stack (update s k x)=update (stack s) (key k) x
  label : L → L'
  halted : Option L'
  stop : TM2.Stmt (fun _ : K' => Bool) L' S'
  stop_spec : ∀ v s, TM2.stepAux stop (state v) (stack s)=⟨halted,state v,stack s⟩

namespace Embedding
variable {K L S K' L' S' : Type} [DecidableEq K] [DecidableEq K']
variable (E : Embedding K L S K' L' S')

def stmt : TM2.Stmt (fun _ : K => Bool) L S → TM2.Stmt (fun _ : K' => Bool) L' S'
  | .push k f q => .push (E.key k) (fun v => f (E.read v)) (stmt q)
  | .peek k f q => .peek (E.key k) (fun v x => E.write v (f (E.read v) x)) (stmt q)
  | .pop k f q => .pop (E.key k) (fun v x => E.write v (f (E.read v) x)) (stmt q)
  | .load f q => .load (fun v => E.write v (f (E.read v))) (stmt q)
  | .branch f q r => .branch (fun v => f (E.read v)) (stmt q) (stmt r)
  | .goto f => .goto (fun v => E.label (f (E.read v)))
  | .halt => E.stop

def cfg (a : TM2.Cfg (fun _ : K => Bool) L S) : TM2.Cfg (fun _ : K' => Bool) L' S' :=
  ⟨a.l.elim E.halted (fun l => some (E.label l)),E.state a.var,E.stack a.stk⟩

theorem stepAux_stmt (q : TM2.Stmt (fun _ : K => Bool) L S) (v : S) (s : K → List Bool) :
    TM2.stepAux (E.stmt q) (E.state v) (E.stack s)=E.cfg (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih =>
      simp only [stmt,TM2.stepAux,E.read_state,E.stack_key,← E.stack_update]
      exact ih _ _
  | peek k f q ih =>
      simp only [stmt,TM2.stepAux,E.read_state,E.stack_key,E.write_state]
      exact ih _ _
  | pop k f q ih =>
      simp only [stmt,TM2.stepAux,E.read_state,E.stack_key,E.write_state,← E.stack_update]
      exact ih _ _
  | load f q ih =>
      simp only [stmt,TM2.stepAux,E.read_state,E.write_state]
      exact ih _ _
  | branch f q r ihq ihr =>
      cases h : f v <;> simp only [stmt,TM2.stepAux,E.read_state,h,Bool.cond_false,Bool.cond_true]
      · exact ihr _ _
      · exact ihq _ _
  | goto f => simp only [stmt,TM2.stepAux,E.read_state,cfg,Option.elim_some]
  | halt => exact E.stop_spec v s

theorem step_cfg (m : L → TM2.Stmt (fun _ : K => Bool) L S)
    (m' : L' → TM2.Stmt (fun _ : K' => Bool) L' S')
    (hm : ∀ l, m' (E.label l)=E.stmt (m l))
    (a b : TM2.Cfg (fun _ : K => Bool) L S) (h : TM2.step m a=some b) :
    TM2.step m' (E.cfg a)=some (E.cfg b) := by
  rcases a with ⟨l,v,s⟩
  cases l with
  | none => cases h
  | some l =>
      have hb : b=TM2.stepAux (m l) v s := (Option.some.inj h).symm
      subst b
      simp only [cfg,Option.elim_some,TM2.step,hm]
      exact congrArg some (E.stepAux_stmt (m l) v s)

theorem trace (m : L → TM2.Stmt (fun _ : K => Bool) L S)
    (m' : L' → TM2.Stmt (fun _ : K' => Bool) L' S')
    (hm : ∀ l, m' (E.label l)=E.stmt (m l))
    {n : ℕ} {a b : TM2.Cfg (fun _ : K => Bool) L S} (h : Trace (TM2.step m) n a b) :
    Trace (TM2.step m') n (E.cfg a) (E.cfg b) :=
  h.map E.cfg (E.step_cfg m m' hm)

end Embedding
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BooleanComposition

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open Turing Function

namespace Compose
variable (M N : Machine)

abbrev Key := M.K ⊕ (Unit ⊕ N.K)
abbrev Label := M.Label ⊕ (Bool ⊕ N.Label)
abbrev State := M.State × N.State × Option Bool

abbrev phaseLabel (b : Bool) : Label M N := .inr (.inl b)
abbrev auxiliary : Key M N := .inr (.inl ())

def left : Embedding M.K M.Label M.State (Key M N) (Label M N) (State M N) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,N.initial,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim s (fun _ => [])
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j
    · simp only [update_apply,Sum.elim_inl,Sum.inl.injEq]
    · simp only [update_apply,Sum.elim_inr,Sum.inr_ne_inl,ite_false]
  label := Sum.inl
  halted := some (phaseLabel M N false)
  stop := .goto (fun _ => phaseLabel M N false)
  stop_spec _ _ := rfl

def right : Embedding N.K N.Label N.State (Key M N) (Label M N) (State M N) where
  key k := .inr (.inr k)
  read v := v.2.1
  write v x := (v.1,x,v.2.2)
  state v := (M.initial,v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim (fun _ => []) (Sum.elim (fun _ => []) s)
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j
    · simp only [update_apply,Sum.elim_inl,Sum.inl_ne_inr,ite_false]
    · rcases j with j | j <;> simp only [update_apply,Sum.elim_inl,Sum.elim_inr,Sum.inr.injEq,Sum.inl_ne_inr,ite_false]
  label l := .inr (.inr l)
  halted := none
  stop := .halt
  stop_spec _ _ := rfl

def source (b : Bool) : Key M N := if b then auxiliary M N else .inl M.output

def target (b : Bool) : Key M N := if b then .inr (.inr N.input) else auxiliary M N

 theorem source_ne_target (b : Bool) : source M N b ≠ target M N b := by
  cases b <;> simp [source,target,auxiliary]

def following (b : Bool) : Label M N :=
  if b then .inr (.inr N.main) else phaseLabel M N true

def clean (v : State M N) : State M N := (v.1,v.2.1,none)

def transfer (b : Bool) : TM2.Stmt (fun _ : Key M N => Bool) (Label M N) (State M N) :=
  .pop (source M N b) (fun v c => (v.1,v.2.1,c))
    (.branch (fun v => v.2.2.isSome)
      (.push (target M N b) (fun v => v.2.2.getD false)
        (.load (clean M N) (.goto (fun _ => phaseLabel M N b))))
      (.load (clean M N) (.goto (fun _ => following M N b))))

def code : Label M N → TM2.Stmt (fun _ : Key M N => Bool) (Label M N) (State M N)
  | .inl l => (left M N).stmt (M.code l)
  | .inr (.inl b) => transfer M N b
  | .inr (.inr l) => (right M N).stmt (N.code l)

abbrev machine : Machine where
  K := Key M N
  input := .inl M.input
  output := .inr (.inr N.output)
  Label := Label M N
  main := .inl M.main
  State := State M N
  initial := (M.initial,N.initial,none)
  code := code M N

 theorem code_left (l : M.Label) : (machine M N).code ((left M N).label l)=
    (left M N).stmt (M.code l) := rfl

 theorem code_right (l : N.Label) : (machine M N).code ((right M N).label l)=
    (right M N).stmt (N.code l) := rfl

 theorem initial_left (s : List Bool) : (left M N).cfg (M.initialCfg s)=
    (machine M N).initialCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Embedding.cfg,left,Machine.initialCfg,machine]

 theorem final_right (s : List Bool) : (right M N).cfg (N.finalCfg s)=
    (machine M N).finalCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,right,Machine.finalCfg,machine]
  · rcases k with k | k <;> simp [Embedding.cfg,right,Machine.finalCfg,machine]

end Compose

def twoStacks {K : Type} [DecidableEq K] (a b : K) (xs ys : List Bool) (k : K) : List Bool :=
  if k=a then xs else if k=b then ys else []

@[simp] theorem twoStacks_source {K : Type} [DecidableEq K] (a b : K) (xs ys : List Bool) :
    twoStacks a b xs ys a=xs := by simp [twoStacks]

@[simp] theorem twoStacks_target {K : Type} [DecidableEq K] {a b : K} (h : a≠b)
    (xs ys : List Bool) : twoStacks a b xs ys b=ys := by simp [twoStacks,h.symm]

 theorem twoStacks_move {K : Type} [DecidableEq K] {a b : K} (h : a≠b)
    (x : Bool) (xs ys : List Bool) :
    update (update (twoStacks a b (x::xs) ys) a xs) b (x::ys)=twoStacks a b xs (x::ys) := by
  funext k
  by_cases ha : k=a
  · subst k; simp [h,twoStacks]
  · by_cases hb : k=b
    · subst k; simp [h.symm,twoStacks]
    · simp [ha,hb,twoStacks]

 theorem twoStacks_pop_empty {K : Type} [DecidableEq K] (a b : K) (ys : List Bool) :
    update (twoStacks a b [] ys) a []=twoStacks a b [] ys := by
  funext k
  by_cases h : k=a <;> simp [twoStacks,h]

namespace Compose
variable (M N : Machine)

def transferCfg (b : Bool) (xs ys : List Bool) : (machine M N).Cfg :=
  ⟨some (phaseLabel M N b), (M.initial,N.initial,none),
    twoStacks (source M N b) (target M N b) xs ys⟩

 theorem transfer_cons (b x : Bool) (xs ys : List Bool) :
    (machine M N).step (transferCfg M N b (x::xs) ys)=
      some (transferCfg M N b xs (x::ys)) := by
  change some (TM2.stepAux (transfer M N b) (M.initial,N.initial,none)
    (twoStacks (source M N b) (target M N b) (x::xs) ys))=some (transferCfg M N b xs (x::ys))
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some,clean]
  rw [update_of_ne (Ne.symm (source_ne_target M N b)),twoStacks_target (source_ne_target M N b)]
  rw [twoStacks_move (source_ne_target M N b)]
  rfl

 theorem transfer_run (b : Bool) (xs ys : List Bool) :
    Trace (machine M N).step xs.length (transferCfg M N b xs ys)
      (transferCfg M N b [] (xs.reverse++ys)) := by
  induction xs generalizing ys with
  | nil => exact Trace.refl _
  | cons x xs ih =>
      have h := Trace.cons (transfer_cons M N b x xs ys) (ih (x::ys))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem transfer_empty (b : Bool) (ys : List Bool) :
    (machine M N).step (transferCfg M N b [] ys)=
      some ⟨some (following M N b),(M.initial,N.initial,none),
        twoStacks (source M N b) (target M N b) [] ys⟩ := by
  change some (TM2.stepAux (transfer M N b) (M.initial,N.initial,none)
    (twoStacks (source M N b) (target M N b) [] ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,clean,twoStacks_pop_empty]

 theorem left_final_transfer (xs : List Bool) :
    (left M N).cfg (M.finalCfg xs)=transferCfg M N false xs [] := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,left,Machine.finalCfg,transferCfg,twoStacks,source,target,auxiliary,Sum.inl.injEq,Sum.inl_ne_inr]
  · rcases k with k | k <;>
      simp [Embedding.cfg,left,Machine.finalCfg,transferCfg,twoStacks,source,target,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_change (ys : List Bool) :
    (machine M N).step (transferCfg M N false [] ys)=some (transferCfg M N true ys []) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [transferCfg,source,target,twoStacks,auxiliary,Sum.inl.injEq,Sum.inl_ne_inr]
  · rcases k with k | k <;> simp [transferCfg,source,target,twoStacks,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_end (ys : List Bool) :
    (machine M N).step (transferCfg M N true [] ys)=some ((right M N).cfg (N.initialCfg ys)) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,right,Machine.initialCfg,source,target,twoStacks,auxiliary,Sum.inl_ne_inr]
  · rcases k with k | k <;>
      simp [Embedding.cfg,right,Machine.initialCfg,source,target,twoStacks,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_full (xs : List Bool) :
    Trace (machine M N).step (2*xs.length+2)
      ((left M N).cfg (M.finalCfg xs)) ((right M N).cfg (N.initialCfg xs)) := by
  rw [left_final_transfer]
  have h₁ := transfer_run M N false xs []
  simp only [List.append_nil] at h₁
  have h₂ := Trace.cons (transfer_change M N xs.reverse) (transfer_run M N true xs.reverse [])
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h₂
  have h₃ := Trace.cons (transfer_end M N xs) (Trace.refl _)
  have hh := (h₁.trans h₂).trans h₃
  simpa only [show xs.length+(xs.length+1)+(0+1)=2*xs.length+2 by omega] using hh

 theorem run {s t u : List Bool} {n m : ℕ}
    (hM : Trace M.step n (M.initialCfg s) (M.finalCfg t))
    (hN : Trace N.step m (N.initialCfg t) (N.finalCfg u)) :
    Trace (machine M N).step (n+2*t.length+2+m)
      ((machine M N).initialCfg s) ((machine M N).finalCfg u) := by
  have h₁ := (left M N).trace M.code (machine M N).code (code_left M N) hM
  have h₂ := (right M N).trace N.code (machine M N).code (code_right M N) hN
  rw [initial_left] at h₁
  rw [final_right] at h₂
  have hh := (h₁.trans (transfer_full M N t)).trans h₂
  simpa only [Machine.step,machine,Nat.add_assoc] using hh

end Compose
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BooleanPolynomial

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Polynomial

 theorem polynomial_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n x =>
      simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left x (Nat.pow_le_pow_left h n)

structure PolyProgram {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  machine : Machine
  time : Polynomial ℕ
  outputs : ∀ a, TM2OutputsInTime machine.tm (ea a) (some (eb (f a))) (time.eval (ea a).length)

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
variable {f : α → β} {g : β → γ}

def stock (P : PolyProgram ea eb f) : TM2ComputableInPolyTime ea eb f where
  tm := P.machine.tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := P.time
  outputsFun a := by
    have h := P.outputs a
    dsimp only [Machine.tm,Equiv.refl] at h ⊢
    simpa only [List.map_id] using h

 theorem finite_work (P : PolyProgram ea eb f) (k : P.stock.tm.K) : Finite (P.stock.tm.Γ k) :=
  inferInstanceAs (Finite Bool)

 noncomputable def sizeBound (P : PolyProgram ea eb f) : Polynomial ℕ :=
  X+P.time*C P.machine.growth

 theorem length_bound (P : PolyProgram ea eb f) (a : α) :
    (eb (f a)).length ≤ P.sizeBound.eval (ea a).length := by
  simpa only [sizeBound,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    using P.machine.output_length (P.outputs a)

 noncomputable def compTime (P : PolyProgram ea eb f) (Q : PolyProgram eb ec g) : Polynomial ℕ :=
  P.time+2*P.sizeBound+2+Q.time.comp P.sizeBound

 noncomputable def comp (P : PolyProgram ea eb f) (Q : PolyProgram eb ec g) : PolyProgram ea ec (g ∘ f) where
  machine := Compose.machine P.machine Q.machine
  time := P.compTime Q
  outputs a := by
    let hP := P.outputs a
    let hQ := Q.outputs (f a)
    have tP : Trace P.machine.step hP.steps (P.machine.initialCfg (ea a))
        (P.machine.finalCfg (eb (f a))) := Trace.of_iterate hP.evals_in_steps
    have tQ : Trace Q.machine.step hQ.steps (Q.machine.initialCfg (eb (f a)))
        (Q.machine.finalCfg (ec (g (f a)))) := Trace.of_iterate hQ.evals_in_steps
    have h := Compose.run P.machine Q.machine tP tQ
    refine ⟨⟨_,h.iterate_eq⟩,?_⟩
    have hl := P.length_bound a
    have hqp := (hQ.steps_le_m).trans (polynomial_eval_mono Q.time hl)
    have hpp := hP.steps_le_m
    simp only [compTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_comp]
    omega

 def congr (P : PolyProgram ea eb f) (f' : α → β) (h : ∀ a, f a=f' a) : PolyProgram ea eb f' where
  machine := P.machine
  time := P.time
  outputs a := by rw [← h a]; exact P.outputs a

end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BooleanTransducer

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Function Polynomial Finset

structure Transducer where
  Q : Type
  [finiteQ : Fintype Q]
  initial : Q
  next : Q → Bool → Q × List Bool
  finish : Q → List Bool
attribute [instance] Transducer.finiteQ

namespace Transducer
variable (T : Transducer)

def run : T.Q → List Bool → List Bool
  | q, [] => T.finish q
  | q, b::xs => (T.next q b).2 ++ run (T.next q b).1 xs

def width : ℕ := max (univ.sup (fun q => (T.finish q).length))
  (univ.sup (fun x : T.Q × Bool => (T.next x.1 x.2).2.length))

 theorem finish_length (q : T.Q) : (T.finish q).length ≤ T.width :=
  (le_sup (f:=fun q => (T.finish q).length) (mem_univ q)).trans (Nat.le_max_left _ _)

 theorem next_length (q : T.Q) (b : Bool) : (T.next q b).2.length ≤ T.width :=
  (le_sup (f:=fun x : T.Q × Bool => (T.next x.1 x.2).2.length) (mem_univ (q,b))).trans (Nat.le_max_right _ _)

 theorem run_length (q : T.Q) (xs : List Bool) : (T.run q xs).length ≤ T.width*(xs.length+1) := by
  induction xs generalizing q with
  | nil => simpa only [run,List.length_nil,zero_add,mul_one] using T.finish_length q
  | cons b xs ih =>
      have hn := T.next_length q b
      have ht := ih (T.next q b).1
      simp only [run,List.length_append,List.length_cons]
      rw [show xs.length+1+1=(xs.length+1)+1 by rfl,Nat.mul_add,mul_one]
      omega

inductive Key | input | buffer | output deriving DecidableEq
instance : Fintype Key := ⟨{Key.input,Key.buffer,Key.output},by
  intro k
  cases k <;> simp⟩
open Key
abbrev Label := T.Q ⊕ Unit
abbrev State := Option Bool

def emit : List Bool → TM2.Stmt (fun _ : Key => Bool) (Label T) State →
    TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | [], q => q
  | b::bs, q => .push buffer (fun _ => b) (emit bs q)

 theorem emit_step (bits : List Bool) (q : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (s : Key → List Bool) :
    TM2.stepAux (emit T bits q) v s=
      TM2.stepAux q v (update s buffer (bits.reverse++s buffer)) := by
  induction bits generalizing s with
  | nil => simp only [emit,List.reverse_nil,List.nil_append,update_eq_self]
  | cons b bs ih =>
      simp only [emit,TM2.stepAux,ih,update_self,update_idem,List.reverse_cons]
      simp only [List.append_assoc,List.singleton_append]

def transfer : TM2.Stmt (fun _ : Key => Bool) (Label T) State :=
  .pop buffer (fun _ b => b)
    (.branch Option.isSome
      (.push output (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => .inr ()))))
      (.load (fun _ => none) .halt))

def code : Label T → TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | .inl q => .pop input (fun _ b => b)
      (.branch Option.isSome
        (.branch (fun b => b.getD false)
          (.load (fun _ => none) (emit T (T.next q true).2 (.goto (fun _ => .inl (T.next q true).1))))
          (.load (fun _ => none) (emit T (T.next q false).2 (.goto (fun _ => .inl (T.next q false).1)))))
        (.load (fun _ => none) (emit T (T.finish q) (.goto (fun _ => .inr ())))))
  | .inr _ => transfer T

abbrev machine : Machine where
  K := Key
  input := input
  output := output
  Label := Label T
  main := .inl T.initial
  State := State
  initial := none
  code := code T

def store (xs ys zs : List Bool) : Key → List Bool
  | input => xs
  | buffer => ys
  | output => zs

 theorem stacks_update_input (xs ys zs ts : List Bool) :
    update (store xs ys zs) input ts=store ts ys zs := by
  funext k
  cases k <;> simp [store]

 theorem stacks_update_buffer (xs ys zs ts : List Bool) :
    update (store xs ys zs) buffer ts=store xs ts zs := by
  funext k
  cases k <;> simp [store]

 theorem stacks_update_output (xs ys zs ts : List Bool) :
    update (store xs ys zs) output ts=store xs ys ts := by
  funext k
  cases k <;> simp [store]

def readCfg (q : T.Q) (xs ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inl q),none,store xs ys []⟩

def transferCfg (ys zs : List Bool) : (machine T).Cfg :=
  ⟨some (.inr ()),none,store [] ys zs⟩

 theorem read_cons (q : T.Q) (b : Bool) (xs ys : List Bool) :
    (machine T).step (T.readCfg q (b::xs) ys)=
      some (T.readCfg (T.next q b).1 xs ((T.next q b).2.reverse++ys)) := by
  cases b <;>
    simp [readCfg,TM2.step,code,TM2.stepAux,store,List.head?,List.tail,
      emit_step,stacks_update_input,stacks_update_buffer]

 theorem read_nil (q : T.Q) (ys : List Bool) :
    (machine T).step (T.readCfg q [] ys)=some (T.transferCfg ((T.finish q).reverse++ys) []) := by
  simp [readCfg,transferCfg,TM2.step,code,TM2.stepAux,store,List.head?,List.tail,
    emit_step,stacks_update_input,stacks_update_buffer]

 theorem read_run (q : T.Q) (xs ys : List Bool) :
    Trace (machine T).step (xs.length+1) (T.readCfg q xs ys)
      (T.transferCfg ((T.run q xs).reverse++ys) []) := by
  induction xs generalizing q ys with
  | nil => exact Trace.cons (T.read_nil q ys) (Trace.refl _)
  | cons b xs ih =>
      have h := Trace.cons (T.read_cons q b xs ys) (ih (T.next q b).1 ((T.next q b).2.reverse++ys))
      simpa only [run,List.reverse_append,List.append_assoc,List.length_cons] using h

 theorem transfer_cons (b : Bool) (ys zs : List Bool) :
    (machine T).step (T.transferCfg (b::ys) zs)=some (T.transferCfg ys (b::zs)) := by
  simp [transferCfg,TM2.step,code,transfer,TM2.stepAux,store,List.head?,List.tail,
    stacks_update_buffer,stacks_update_output]

 theorem transfer_nil (zs : List Bool) :
    (machine T).step (T.transferCfg [] zs)=some ((machine T).finalCfg zs) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [Machine.finalCfg,code,transfer,TM2.stepAux,store]

 theorem transfer_run (ys zs : List Bool) :
    Trace (machine T).step (ys.length+1) (T.transferCfg ys zs)
      ((machine T).finalCfg (ys.reverse++zs)) := by
  induction ys generalizing zs with
  | nil => exact Trace.cons (T.transfer_nil zs) (Trace.refl _)
  | cons b ys ih =>
      have h := Trace.cons (T.transfer_cons b ys zs) (ih (b::zs))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem run_trace (xs : List Bool) :
    Trace (machine T).step (xs.length+(T.run T.initial xs).length+2)
      ((machine T).initialCfg xs) ((machine T).finalCfg (T.run T.initial xs)) := by
  have hi : (machine T).initialCfg xs=T.readCfg T.initial xs [] := by
    apply cfg_ext <;> try rfl
    funext k
    cases k <;> simp [Machine.initialCfg,readCfg,store]
  rw [hi]
  have hr := T.read_run T.initial xs []
  simp only [List.append_nil] at hr
  have h := hr.trans (T.transfer_run (T.run T.initial xs).reverse [])
  simpa only [List.append_nil,List.length_reverse,List.reverse_reverse,
    show xs.length+1+((T.run T.initial xs).length+1)=xs.length+(T.run T.initial xs).length+2 by omega] using h

noncomputable def program : PolyProgram id id (T.run T.initial) where
  machine := machine T
  time := C (T.width+1)*X+C (T.width+2)
  outputs xs := by
    refine ⟨⟨_,(T.run_trace xs).iterate_eq⟩,?_⟩
    have hl := T.run_length T.initial xs
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,id_eq]
    nlinarith

end Transducer
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BooleanEncoding

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

def quote : List Bool → List Bool
  | [] => [false]
  | b::bs => true::b::quote bs

@[simp] theorem quote_length (bs : List Bool) : (quote bs).length=2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [quote,List.length_cons,ih]; omega

def encodePair {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (x : α × β) : List Bool :=
  quote (ea x.1)++eb x.2

@[simp] theorem encodePair_length {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (x : α × β) :
    (encodePair ea eb x).length=2*(ea x.1).length+1+(eb x.2).length := by
  simp only [encodePair,List.length_append,quote_length]

namespace WordTransducer

def quoting : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[true,b])
  finish _ := [false]

 theorem quoting_run (xs : List Bool) : quoting.run () xs=quote xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [Transducer.run,quoting,List.cons_append,List.nil_append,quote] using congrArg (fun l => true::b::l) ih

def projecting (tail : Bool) : Transducer where
  Q := Option Bool
  initial := none
  next q b := match q with
    | none => (some (!b),[])
    | some false => (none,if tail then [] else [b])
    | some true => (some true,if tail then [b] else [])
  finish _ := []

 theorem projecting_done (tail : Bool) (xs : List Bool) :
    (projecting tail).run (some true) xs=if tail then xs else [] := by
  induction xs with
  | nil => cases tail <;> rfl
  | cons b xs ih =>
      change (if tail then [b] else [])++(projecting tail).run (some true) xs=_
      rw [ih]
      cases tail <;> simp

 theorem projecting_pair (tail : Bool) (xs ys : List Bool) :
    (projecting tail).run none (quote xs++ys)=if tail then ys else xs := by
  induction xs with
  | nil => exact projecting_done tail ys
  | cons b xs ih =>
      change (if tail then [] else [b])++(projecting tail).run none (quote xs++ys)=_
      rw [ih]
      cases tail <;> simp

end WordTransducer

namespace PolyProgram

 def of_word {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    {g : List Bool → List Bool} (P : PolyProgram id id g)
    (h : ∀ a, g (ea a)=eb (f a)) : PolyProgram ea eb f where
  machine := P.machine
  time := P.time
  outputs a := by simpa only [id_eq,h a] using P.outputs (ea a)

 noncomputable def quote : PolyProgram id id Binary.quote :=
  WordTransducer.quoting.program.congr _ WordTransducer.quoting_run

 noncomputable def fst {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) ea Prod.fst :=
  (WordTransducer.projecting false).program.of_word (fun _ => by
    simpa only [encodePair,Bool.false_eq_true,ite_false,WordTransducer.projecting] using WordTransducer.projecting_pair false _ _)

 noncomputable def snd {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) eb Prod.snd :=
  (WordTransducer.projecting true).program.of_word (fun _ => by
    simpa only [encodePair,ite_true,WordTransducer.projecting] using WordTransducer.projecting_pair true _ _)

end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BooleanThread

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace Thread
variable (M : Machine)
abbrev Key := M.K ⊕ Bool
abbrev Label := M.Label ⊕ Fin 4
abbrev State := M.State × Option Bool
abbrev source : Key M := .inr false
abbrev buffer : Key M := .inr true
abbrev reading : Label M := .inr 0
abbrev loading : Label M := .inr 1
abbrev emitting : Label M := .inr 2
abbrev draining : Label M := .inr 3

def store (s : M.K → List Bool) (xs ys : List Bool) : Key M → List Bool :=
  fun k => match k with
  | .inl k => s k
  | .inr false => xs
  | .inr true => ys

@[simp] theorem store_local (s : M.K → List Bool) (xs ys : List Bool) (k : M.K) :
    store M s xs ys (.inl k)=s k := rfl
@[simp] theorem store_source (s : M.K → List Bool) (xs ys : List Bool) :
    store M s xs ys (source M)=xs := rfl
@[simp] theorem store_buffer (s : M.K → List Bool) (xs ys : List Bool) :
    store M s xs ys (buffer M)=ys := rfl

def slot (k : M.K) (xs : List Bool) : M.K → List Bool := fun j => if j=k then xs else []

 theorem slot_nil (k : M.K) : slot M k []=fun _ => [] := by funext j; simp [slot]
 theorem slot_self (k : M.K) (xs : List Bool) : slot M k xs k=xs := by simp [slot]
 theorem slot_update (k : M.K) (xs ys : List Bool) : update (slot M k xs) k ys=slot M k ys := by
  funext j
  by_cases h : j=k <;> simp [slot,h]

 theorem store_update_local (s : M.K → List Bool) (xs ys : List Bool) (k : M.K) (w : List Bool) :
    update (store M s xs ys) (.inl k) w=store M (update s k w) xs ys := by
  funext j
  rcases j with j | j
  · simp [store,update_apply]
  · cases j <;> simp [store]
 theorem store_update_source (s : M.K → List Bool) (xs ys w : List Bool) :
    update (store M s xs ys) (source M) w=store M s w ys := by
  funext j
  rcases j with j | j <;> try cases j
  all_goals simp [store]
 theorem store_update_buffer (s : M.K → List Bool) (xs ys w : List Bool) :
    update (store M s xs ys) (buffer M) w=store M s xs w := by
  funext j
  rcases j with j | j <;> try cases j
  all_goals simp [store]

def body (tail : List Bool) : Embedding M.K M.Label M.State (Key M) (Label M) (State M) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := store M s tail []
  stack_key _ _ := rfl
  stack_update s k x := (store_update_local M s tail [] k x).symm
  label := Sum.inl
  halted := some (emitting M)
  stop := .goto (fun _ => emitting M)
  stop_spec _ _ := rfl

 theorem body_stmt (tail : List Bool) (s : TM2.Stmt (fun _ : M.K => Bool) M.Label M.State) :
    (body M tail).stmt s=(body M []).stmt s := by
  induction s <;> simp_all [Embedding.stmt,body]

def clean (v : State M) : State M := (v.1,none)

def readCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (source M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.getD false)
      (.pop (source M) (fun v b => (v.1,b))
        (.push (buffer M) (fun v => v.2.getD false)
          (.load (clean M) (.goto (fun _ => reading M)))))
      (.load (clean M) (.goto (fun _ => loading M))))

def loadCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (buffer M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (.inl M.input) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => loading M))))
      (.load (clean M) (.goto (fun _ => .inl M.main))))

def emitCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (.inl M.output) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (buffer M) (fun _ => true) (.push (buffer M) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => emitting M)))))
      (.push (buffer M) (fun _ => false)
        (.load (clean M) (.goto (fun _ => draining M)))))

def drainCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (buffer M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (source M) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => draining M))))
      (.load (clean M) .halt))

def code : Label M → TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M)
  | .inl l => (body M []).stmt (M.code l)
  | .inr i => if i=0 then readCode M else if i=1 then loadCode M else if i=2 then emitCode M else drainCode M

abbrev machine : Machine where
  K := Key M
  input := source M
  output := source M
  Label := Label M
  main := reading M
  State := State M
  initial := (M.initial,none)
  code := code M

 theorem code_body (tail : List Bool) (l : M.Label) :
    (machine M).code ((body M tail).label l)=(body M tail).stmt (M.code l) := (body_stmt M tail _).symm

def readCfg (xs tail buf : List Bool) : (machine M).Cfg :=
  ⟨some (reading M),(M.initial,none),store M (fun _ => []) (quote xs++tail) buf⟩

def loadCfg (tail buf xs : List Bool) : (machine M).Cfg :=
  ⟨some (loading M),(M.initial,none),store M (slot M M.input xs) tail buf⟩

def emitCfg (tail xs buf : List Bool) : (machine M).Cfg :=
  ⟨some (emitting M),(M.initial,none),store M (slot M M.output xs) tail buf⟩

def drainCfg (tail buf : List Bool) : (machine M).Cfg :=
  ⟨some (draining M),(M.initial,none),store M (fun _ => []) tail buf⟩

 theorem read_cons (b : Bool) (xs tail buf : List Bool) :
    (machine M).step (readCfg M (b::xs) tail buf)=some (readCfg M xs tail (b::buf)) := by
  simp [readCfg,TM2.step,code,readCode,TM2.stepAux,quote,clean,
    store_update_source,store_update_buffer]

 theorem read_nil (tail buf : List Bool) :
    (machine M).step (readCfg M [] tail buf)=some (loadCfg M tail buf []) := by
  simp [readCfg,loadCfg,TM2.step,code,readCode,TM2.stepAux,quote,clean,
    store_update_source,slot_nil]

 theorem read_run (xs tail buf : List Bool) :
    Trace (machine M).step (xs.length+1) (readCfg M xs tail buf) (loadCfg M tail (xs.reverse++buf) []) := by
  induction xs generalizing buf with
  | nil => exact Trace.cons (read_nil M tail buf) (Trace.refl _)
  | cons b xs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (read_cons M b xs tail buf) (ih (b::buf))

 theorem load_cons (b : Bool) (tail buf xs : List Bool) :
    (machine M).step (loadCfg M tail (b::buf) xs)=some (loadCfg M tail buf (b::xs)) := by
  simp [loadCfg,TM2.step,code,loadCode,TM2.stepAux,clean,
    store_update_buffer,store_update_local,slot_update,slot_self]

 theorem load_nil (tail xs : List Bool) :
    (machine M).step (loadCfg M tail [] xs)=some ((body M tail).cfg (M.initialCfg xs)) := by
  simp [loadCfg,Embedding.cfg,body,Machine.initialCfg,TM2.step,code,loadCode,TM2.stepAux,
    clean,store_update_buffer,slot]
  rfl

 theorem load_run (tail buf xs : List Bool) :
    Trace (machine M).step (buf.length+1) (loadCfg M tail buf xs)
      ((body M tail).cfg (M.initialCfg (buf.reverse++xs))) := by
  induction buf generalizing xs with
  | nil => exact Trace.cons (load_nil M tail xs) (Trace.refl _)
  | cons b bs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (load_cons M b tail bs xs) (ih (b::xs))

 theorem emit_cons (b : Bool) (tail xs buf : List Bool) :
    (machine M).step (emitCfg M tail (b::xs) buf)=some (emitCfg M tail xs (b::true::buf)) := by
  simp [emitCfg,TM2.step,code,emitCode,TM2.stepAux,clean,
    store_update_local,store_update_buffer,slot_update,slot_self]

 theorem emit_nil (tail buf : List Bool) :
    (machine M).step (emitCfg M tail [] buf)=some (drainCfg M tail (false::buf)) := by
  simp [emitCfg,drainCfg,TM2.step,code,emitCode,TM2.stepAux,clean,
    store_update_local,store_update_buffer,slot_nil]

 theorem emit_run (tail xs buf : List Bool) :
    Trace (machine M).step (xs.length+1) (emitCfg M tail xs buf)
      (drainCfg M tail ((quote xs).reverse++buf)) := by
  induction xs generalizing buf with
  | nil => exact Trace.cons (emit_nil M tail buf) (Trace.refl _)
  | cons b xs ih =>
      simpa only [List.length_cons,quote,List.reverse_cons,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
        Trace.cons (emit_cons M b tail xs buf) (ih (b::true::buf))

 theorem drain_cons (b : Bool) (tail buf : List Bool) :
    (machine M).step (drainCfg M tail (b::buf))=some (drainCfg M (b::tail) buf) := by
  simp [drainCfg,TM2.step,code,drainCode,TM2.stepAux,clean,
    store_update_source,store_update_buffer]

 theorem drain_nil (tail : List Bool) :
    (machine M).step (drainCfg M tail [])=some ((machine M).finalCfg tail) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    rcases k with k | k <;> try cases k
    all_goals simp [Machine.finalCfg,code,drainCode,TM2.stepAux,clean]

 theorem drain_run (tail buf : List Bool) :
    Trace (machine M).step (buf.length+1) (drainCfg M tail buf) ((machine M).finalCfg (buf.reverse++tail)) := by
  induction buf generalizing tail with
  | nil => exact Trace.cons (drain_nil M tail) (Trace.refl _)
  | cons b bs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (drain_cons M b tail bs) (ih (b::tail))

 theorem body_final (tail xs : List Bool) : (body M tail).cfg (M.finalCfg xs)=emitCfg M tail xs [] := rfl

 theorem run {xs zs : List Bool} {n : ℕ} (tail : List Bool)
    (h : Trace M.step n (M.initialCfg xs) (M.finalCfg zs)) :
    Trace (machine M).step (2*xs.length+3*zs.length+5+n)
      ((machine M).initialCfg (quote xs++tail)) ((machine M).finalCfg (quote zs++tail)) := by
  have hi : (machine M).initialCfg (quote xs++tail)=readCfg M xs tail [] := by
    apply cfg_ext <;> try rfl
    funext k
    rcases k with k | k <;> try cases k
    all_goals simp [Machine.initialCfg,readCfg,store]
  rw [hi]
  have ha := read_run M xs tail []
  simp only [List.append_nil] at ha
  have hb := load_run M tail xs.reverse []
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hb
  have hc := (body M tail).trace M.code (machine M).code (code_body M tail) h
  rw [body_final] at hc
  have hd := emit_run M tail zs []
  simp only [List.append_nil] at hd
  have he := drain_run M tail (quote zs).reverse
  simp only [List.reverse_reverse,List.length_reverse,quote_length] at he
  have hx := (((ha.trans hb).trans hc).trans hd).trans he
  convert hx using 1
  omega

end Thread

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {f : α → β}

 noncomputable def thread (P : PolyProgram ea eb f) (ec : γ → List Bool) :
    PolyProgram (encodePair ea ec) (encodePair eb ec) (fun x => (f x.1,x.2)) where
  machine := Thread.machine P.machine
  time := 2*X+3*P.sizeBound+5+P.time
  outputs x := by
    have hp := P.outputs x.1
    have h := Thread.run P.machine (ec x.2) (Trace.of_iterate hp.evals_in_steps)
    refine ⟨⟨_,h.iterate_eq⟩,?_⟩
    have hn : (ea x.1).length≤(encodePair ea ec x).length := by simp only [encodePair_length]; omega
    have hl := (P.length_bound x.1).trans (polynomial_eval_mono P.sizeBound hn)
    have ht := hp.steps_le_m.trans (polynomial_eval_mono P.time hn)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega

end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BooleanParallelTransducer

namespace OAI


                                                 
section
namespace MetricKMedian.Binary
open Turing Function Polynomial Finset

structure ParallelTransducer where
  Q : Type
  [finiteQ : Fintype Q]
  initial : Q
  next : Q → Bool → Q × (List Bool × List Bool)
  finish : Q → List Bool × List Bool
attribute [instance] ParallelTransducer.finiteQ

namespace ParallelTransducer
variable (T : ParallelTransducer)

def run : T.Q → List Bool → List Bool × List Bool
  | q, [] => T.finish q
  | q, b::xs =>
    let v := T.next q b
    let z := run v.1 xs
    (v.2.1++z.1,v.2.2++z.2)

def width : ℕ := max (univ.sup (fun q => (T.finish q).1.length+(T.finish q).2.length))
  (univ.sup (fun x : T.Q × Bool => (T.next x.1 x.2).2.1.length+(T.next x.1 x.2).2.2.length))

 theorem finish_length (q : T.Q) : (T.finish q).1.length+(T.finish q).2.length≤T.width :=
  (le_sup (f:=fun q => (T.finish q).1.length+(T.finish q).2.length) (mem_univ q)).trans (Nat.le_max_left _ _)

 theorem next_length (q : T.Q) (b : Bool) :
    (T.next q b).2.1.length+(T.next q b).2.2.length≤T.width :=
  (le_sup (f:=fun x : T.Q × Bool => (T.next x.1 x.2).2.1.length+(T.next x.1 x.2).2.2.length)
    (mem_univ (q,b))).trans (Nat.le_max_right _ _)

 theorem run_length (q : T.Q) (xs : List Bool) :
    (T.run q xs).1.length+(T.run q xs).2.length≤T.width*(xs.length+1) := by
  induction xs generalizing q with
  | nil => simpa only [run,List.length_nil,zero_add,mul_one] using T.finish_length q
  | cons b xs ih =>
      have hn := T.next_length q b
      have ht := ih (T.next q b).1
      simp only [run,List.length_append,List.length_cons]
      rw [show xs.length+1+1=(xs.length+1)+1 by rfl,Nat.mul_add,mul_one]
      omega

abbrev Key := Fin 4
abbrev input : Key := 0
abbrev left : Key := 1
abbrev right : Key := 2
abbrev output : Key := 3
abbrev Label := T.Q ⊕ Bool
abbrev State := Option Bool

def store (xs ls rs ys : List Bool) : Key → List Bool :=
  fun k => if k=input then xs else if k=left then ls else if k=right then rs else ys

 theorem store_update_input (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) input zs=store zs ls rs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_left (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) left zs=store xs zs rs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_right (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) right zs=store xs ls zs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_output (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) output zs=store xs ls rs zs := by
  funext k
  fin_cases k <;> simp [store,input,left,right,output]

def emit (k : Key) : List Bool → TM2.Stmt (fun _ : Key => Bool) (Label T) State →
    TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | [], s => s
  | b::bs, s => .push k (fun _ => b) (emit k bs s)

 theorem emit_step (k : Key) (bits : List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (stk : Key → List Bool) :
    TM2.stepAux (emit T k bits s) v stk=TM2.stepAux s v (update stk k (bits.reverse++stk k)) := by
  induction bits generalizing stk with
  | nil => simp only [emit,List.reverse_nil,List.nil_append,update_eq_self]
  | cons b bs ih =>
      simp only [emit,TM2.stepAux,ih,update_self,update_idem,List.reverse_cons,
        List.append_assoc,List.singleton_append]

def emitPair (p : List Bool × List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State) :=
  emit T left p.1 (emit T right p.2 s)

 theorem emitPair_step (p : List Bool × List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (xs ls rs ys : List Bool) :
    TM2.stepAux (emitPair T p s) v (store xs ls rs ys)=
      TM2.stepAux s v (store xs (p.1.reverse++ls) (p.2.reverse++rs) ys) := by
  simp [emitPair,emit_step,store,input,left,right,store_update_left,store_update_right]

def transfer (phase : Bool) : TM2.Stmt (fun _ : Key => Bool) (Label T) State :=
  .pop (if phase then left else right) (fun _ b => b)
    (.branch Option.isSome
      (.push output (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => .inr phase))))
      (.load (fun _ => none) (if phase then .halt else .goto (fun _ => .inr true))))

def code : Label T → TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | .inl q => .pop input (fun _ b => b)
      (.branch Option.isSome
        (.branch (fun b => b.getD false)
          (.load (fun _ => none) (emitPair T (T.next q true).2 (.goto (fun _ => .inl (T.next q true).1))))
          (.load (fun _ => none) (emitPair T (T.next q false).2 (.goto (fun _ => .inl (T.next q false).1)))))
        (.load (fun _ => none) (emitPair T (T.finish q) (.goto (fun _ => .inr false)))))
  | .inr b => transfer T b

abbrev machine : Machine where
  K := Key
  input := input
  output := output
  Label := Label T
  main := .inl T.initial
  State := State
  initial := none
  code := code T

def readCfg (q : T.Q) (xs ls rs : List Bool) : (machine T).Cfg :=
  ⟨some (.inl q),none,store xs ls rs []⟩
def rightCfg (ls rs ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inr false),none,store [] ls rs ys⟩
def leftCfg (ls ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inr true),none,store [] ls [] ys⟩

 theorem read_cons (q : T.Q) (b : Bool) (xs ls rs : List Bool) :
    (machine T).step (T.readCfg q (b::xs) ls rs)=
      some (T.readCfg (T.next q b).1 xs ((T.next q b).2.1.reverse++ls) ((T.next q b).2.2.reverse++rs)) := by
  cases b <;> simp [readCfg,TM2.step,code,TM2.stepAux,store,input,emitPair_step,store_update_input]

 theorem read_nil (q : T.Q) (ls rs : List Bool) :
    (machine T).step (T.readCfg q [] ls rs)=
      some (T.rightCfg ((T.finish q).1.reverse++ls) ((T.finish q).2.reverse++rs) []) := by
  simp [readCfg,rightCfg,TM2.step,code,TM2.stepAux,store,input,emitPair_step,store_update_input]

 theorem read_run (q : T.Q) (xs ls rs : List Bool) :
    Trace (machine T).step (xs.length+1) (T.readCfg q xs ls rs)
      (T.rightCfg ((T.run q xs).1.reverse++ls) ((T.run q xs).2.reverse++rs) []) := by
  induction xs generalizing q ls rs with
  | nil => exact Trace.cons (T.read_nil q ls rs) (Trace.refl _)
  | cons b xs ih =>
      simpa only [run,List.length_cons,List.reverse_append,List.append_assoc] using
        Trace.cons (T.read_cons q b xs ls rs)
          (ih (T.next q b).1 ((T.next q b).2.1.reverse++ls) ((T.next q b).2.2.reverse++rs))

 theorem right_cons (b : Bool) (ls rs ys : List Bool) :
    (machine T).step (T.rightCfg ls (b::rs) ys)=some (T.rightCfg ls rs (b::ys)) := by
  simp [rightCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_right,store_update_output]

 theorem right_nil (ls ys : List Bool) :
    (machine T).step (T.rightCfg ls [] ys)=some (T.leftCfg ls ys) := by
  simp [rightCfg,leftCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_right]

 theorem right_run (ls rs ys : List Bool) :
    Trace (machine T).step (rs.length+1) (T.rightCfg ls rs ys) (T.leftCfg ls (rs.reverse++ys)) := by
  induction rs generalizing ys with
  | nil => exact Trace.cons (T.right_nil ls ys) (Trace.refl _)
  | cons b rs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (T.right_cons b ls rs ys) (ih (b::ys))

 theorem left_cons (b : Bool) (ls ys : List Bool) :
    (machine T).step (T.leftCfg (b::ls) ys)=some (T.leftCfg ls (b::ys)) := by
  simp [leftCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_left,store_update_output]

 theorem left_nil (ys : List Bool) :
    (machine T).step (T.leftCfg [] ys)=some ((machine T).finalCfg ys) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    fin_cases k <;> simp [Machine.finalCfg,code,transfer,TM2.stepAux,store,input,left,right,output]

 theorem left_run (ls ys : List Bool) :
    Trace (machine T).step (ls.length+1) (T.leftCfg ls ys) ((machine T).finalCfg (ls.reverse++ys)) := by
  induction ls generalizing ys with
  | nil => exact Trace.cons (T.left_nil ys) (Trace.refl _)
  | cons b ls ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (T.left_cons b ls ys) (ih (b::ys))

 theorem run_trace (xs : List Bool) :
    Trace (machine T).step (xs.length+(T.run T.initial xs).1.length+(T.run T.initial xs).2.length+3)
      ((machine T).initialCfg xs)
      ((machine T).finalCfg ((T.run T.initial xs).1++(T.run T.initial xs).2)) := by
  have hi : (machine T).initialCfg xs=T.readCfg T.initial xs [] [] := by
    apply cfg_ext <;> try rfl
    funext k
    fin_cases k <;> simp [Machine.initialCfg,readCfg,store,input,left,right]
  rw [hi]
  have hr := T.read_run T.initial xs [] []
  simp only [List.append_nil] at hr
  have hs := T.right_run (T.run T.initial xs).1.reverse (T.run T.initial xs).2.reverse []
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hs
  have ht := T.left_run (T.run T.initial xs).1.reverse (T.run T.initial xs).2
  simp only [List.length_reverse,List.reverse_reverse] at ht
  have h := (hr.trans hs).trans ht
  convert h using 1
  omega

noncomputable def program : PolyProgram id id (fun xs => (T.run T.initial xs).1++(T.run T.initial xs).2) where
  machine := machine T
  time := C (T.width+1)*X+C (T.width+3)
  outputs xs := by
    refine ⟨⟨_,(T.run_trace xs).iterate_eq⟩,?_⟩
    have hl := T.run_length T.initial xs
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,id_eq]
    nlinarith

end ParallelTransducer
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BooleanProducts

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace WordTransducer

def identity : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[b])
  finish _ := []

 theorem identity_run (xs : List Bool) : identity.run () xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::identity.run () xs=b::xs; rw [ih]

def constant (s : List Bool) : Transducer where
  Q := Unit
  initial := ()
  next _ _ := ((),[])
  finish _ := s

 theorem constant_run (s xs : List Bool) : (constant s).run () xs=s := by
  induction xs with
  | nil => rfl
  | cons b xs ih => exact ih

def duplicate : ParallelTransducer where
  Q := Unit
  initial := ()
  next _ b := ((),([true,b],[b]))
  finish _ := ([false],[])

 theorem duplicate_run (xs : List Bool) : duplicate.run () xs=(quote xs,xs) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change (true::b::(duplicate.run () xs).1,b::(duplicate.run () xs).2)=_
      rw [ih]
      rfl

def exchange : ParallelTransducer where
  Q := Option Bool
  initial := none
  next q b := match q with
    | none => (some (!b),([],[]))
    | some false => (none,([],[b]))
    | some true => (some true,([true,b],[]))
  finish _ := ([false],[])

 theorem exchange_done (xs : List Bool) : exchange.run (some true) xs=(quote xs,[]) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change (true::b::(exchange.run (some true) xs).1,(exchange.run (some true) xs).2)=_
      rw [ih]
      rfl

 theorem exchange_run (xs ys : List Bool) : exchange.run none (quote xs++ys)=(quote ys,xs) := by
  induction xs with
  | nil => exact exchange_done ys
  | cons b xs ih =>
      change ((exchange.run none (quote xs++ys)).1,b::(exchange.run none (quote xs++ys)).2)=_
      rw [ih]

end WordTransducer

namespace PolyProgram
variable {α β γ δ : Type}
variable {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {ed : δ → List Bool}
variable {f : α → β} {g : γ → δ}

noncomputable def identity (ea : α → List Bool) : PolyProgram ea ea _root_.id :=
  WordTransducer.identity.program.of_word (fun a => by
    simpa only [WordTransducer.identity,id_eq] using WordTransducer.identity_run (ea a))

noncomputable def constant (ea : α → List Bool) (eb : β → List Bool) (b : β) :
    PolyProgram ea eb (fun _ => b) :=
  (WordTransducer.constant (eb b)).program.of_word (fun a => by
    simpa only [WordTransducer.constant] using WordTransducer.constant_run (eb b) (ea a))

noncomputable def duplicate (ea : α → List Bool) : PolyProgram ea (encodePair ea ea) (fun a => (a,a)) :=
  WordTransducer.duplicate.program.of_word (fun a => by
    have h := congrArg (fun p : List Bool × List Bool => p.1++p.2) (WordTransducer.duplicate_run (ea a))
    simpa only [WordTransducer.duplicate,encodePair] using h)

noncomputable def exchange (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) (encodePair eb ea) Prod.swap :=
  WordTransducer.exchange.program.of_word (fun x => by
    have h := congrArg (fun p : List Bool × List Bool => p.1++p.2) (WordTransducer.exchange_run (ea x.1) (eb x.2))
    simpa only [WordTransducer.exchange,encodePair,Prod.swap] using h)

noncomputable def second (P : PolyProgram ea eb f) (ec : γ → List Bool) :
    PolyProgram (encodePair ec ea) (encodePair ec eb) (fun x => (x.1,f x.2)) :=
  (((exchange ec ea).comp (P.thread ec)).comp (exchange eb ec)).congr _ (fun _ => rfl)

noncomputable def product (P : PolyProgram ea eb f) (Q : PolyProgram ec ed g) :
    PolyProgram (encodePair ea ec) (encodePair eb ed) (fun x => (f x.1,g x.2)) :=
  ((P.thread ec).comp (Q.second eb)).congr _ (fun _ => rfl)

noncomputable def fanout {h : α → γ} (P : PolyProgram ea eb f) (Q : PolyProgram ea ec h) :
    PolyProgram ea (encodePair eb ec) (fun a => (f a,h a)) :=
  ((duplicate ea).comp (P.product Q)).congr _ (fun _ => rfl)

end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BooleanLoop

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace Loop
variable (M : Machine)
abbrev Key := M.K ⊕ Unit
abbrev Label := M.Label ⊕ Option Bool
abbrev State := M.State × Option Bool
abbrev auxiliary : Key M := .inr ()
abbrev check : Label M := .inr none
abbrev phase (b : Bool) : Label M := .inr (some b)

def body : Embedding M.K M.Label M.State (Key M) (Label M) (State M) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim s (fun _ => [])
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j <;>
      simp only [update_apply,Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr_ne_inl,ite_false]
  label := Sum.inl
  halted := some (check M)
  stop := .goto (fun _ => check M)
  stop_spec _ _ := rfl

def source (b : Bool) : Key M := if b then auxiliary M else .inl M.output

def target (b : Bool) : Key M := if b then .inl M.input else auxiliary M

 theorem source_ne_target (b : Bool) : source M b ≠ target M b := by
  cases b <;> simp [source,target,auxiliary]

def following (b : Bool) : Label M := if b then .inl M.main else phase M true

def clean (v : State M) : State M := (v.1,none)

def transfer (b : Bool) : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (source M b) (fun v c => (v.1,c))
    (.branch (fun v => v.2.isSome)
      (.push (target M b) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => phase M b))))
      (.load (clean M) (.goto (fun _ => following M b))))

def checkCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (.inl M.output) (fun v c => (v.1,c))
    (.branch (fun v => v.2.getD false)
      (.load (clean M) (.goto (fun _ => phase M false)))
      (.load (clean M) .halt))

def code : Label M → TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M)
  | .inl l => (body M).stmt (M.code l)
  | .inr none => checkCode M
  | .inr (some b) => transfer M b

abbrev machine : Machine where
  K := Key M
  input := .inl M.input
  output := .inl M.output
  Label := Label M
  main := .inl M.main
  State := State M
  initial := (M.initial,none)
  code := code M

 theorem code_body (l : M.Label) : (machine M).code ((body M).label l)=
    (body M).stmt (M.code l) := rfl

 theorem initial_body (s : List Bool) : (body M).cfg (M.initialCfg s)=
    (machine M).initialCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Embedding.cfg,body,Machine.initialCfg]

def transferCfg (b : Bool) (xs ys : List Bool) : (machine M).Cfg :=
  ⟨some (phase M b),(M.initial,none),twoStacks (source M b) (target M b) xs ys⟩

 theorem transfer_cons (b x : Bool) (xs ys : List Bool) :
    (machine M).step (transferCfg M b (x::xs) ys)=some (transferCfg M b xs (x::ys)) := by
  change some (TM2.stepAux (transfer M b) (M.initial,none)
    (twoStacks (source M b) (target M b) (x::xs) ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some,clean]
  rw [update_of_ne (Ne.symm (source_ne_target M b)),twoStacks_target (source_ne_target M b)]
  rw [twoStacks_move (source_ne_target M b)]
  rfl

 theorem transfer_run (b : Bool) (xs ys : List Bool) :
    Trace (machine M).step xs.length (transferCfg M b xs ys)
      (transferCfg M b [] (xs.reverse++ys)) := by
  induction xs generalizing ys with
  | nil => exact Trace.refl _
  | cons x xs ih =>
      have h := Trace.cons (transfer_cons M b x xs ys) (ih (x::ys))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem transfer_empty (b : Bool) (ys : List Bool) :
    (machine M).step (transferCfg M b [] ys)=
      some ⟨some (following M b),(M.initial,none),twoStacks (source M b) (target M b) [] ys⟩ := by
  change some (TM2.stepAux (transfer M b) (M.initial,none)
    (twoStacks (source M b) (target M b) [] ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,clean,twoStacks_pop_empty]

 theorem transfer_change (ys : List Bool) :
    (machine M).step (transferCfg M false [] ys)=some (transferCfg M true ys []) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [transferCfg,source,target,twoStacks,auxiliary]

 theorem transfer_end (ys : List Bool) :
    (machine M).step (transferCfg M true [] ys)=some ((machine M).initialCfg ys) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Machine.initialCfg,source,target,twoStacks,auxiliary]

 theorem transfer_full (xs : List Bool) :
    Trace (machine M).step (2*xs.length+2) (transferCfg M false xs []) ((machine M).initialCfg xs) := by
  have h₁ := transfer_run M false xs []
  simp only [List.append_nil] at h₁
  have h₂ := Trace.cons (transfer_change M xs.reverse) (transfer_run M true xs.reverse [])
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h₂
  have h₃ := Trace.cons (transfer_end M xs) (Trace.refl _)
  have hh := (h₁.trans h₂).trans h₃
  simpa only [show xs.length+(xs.length+1)+(0+1)=2*xs.length+2 by omega] using hh

def checkCfg (xs : List Bool) : (machine M).Cfg :=
  ⟨some (check M),(M.initial,none),fun k => if k=Sum.inl M.output then xs else []⟩

 theorem body_final (xs : List Bool) : (body M).cfg (M.finalCfg xs)=checkCfg M xs := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [body,Embedding.cfg,Machine.finalCfg,checkCfg]

 theorem check_step (b : Bool) (xs : List Bool) :
    (machine M).step (checkCfg M (b::xs))=
      some ⟨if b then some (phase M false) else none,(M.initial,none),
        fun k => if k=Sum.inl M.output then xs else []⟩ := by
  change some (TM2.stepAux (checkCode M) (M.initial,none)
    (fun k => if k=Sum.inl M.output then b::xs else []))=_
  simp only [checkCode,TM2.stepAux,List.head?_cons,List.tail_cons,
    Option.getD_some,clean,ite_true]
  cases b <;> simp only [Bool.cond_false,Bool.cond_true,Bool.false_eq_true,ite_false,ite_true]
  all_goals
    apply congrArg some
    apply cfg_ext <;> try rfl
    funext k
    by_cases h : k=Sum.inl M.output <;> simp [h]

 theorem check_false (xs : List Bool) :
    (machine M).step ((body M).cfg (M.finalCfg (false::xs)))=some ((machine M).finalCfg xs) := by
  rw [body_final,check_step]
  rfl

 theorem check_true (xs : List Bool) :
    (machine M).step ((body M).cfg (M.finalCfg (true::xs)))=some (transferCfg M false xs []) := by
  rw [body_final,check_step]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [transferCfg,twoStacks,source,target,auxiliary]

 theorem stop {s t : List Bool} {n : ℕ}
    (hM : Trace M.step n (M.initialCfg s) (M.finalCfg (false::t))) :
    Trace (machine M).step (n+1) ((machine M).initialCfg s) ((machine M).finalCfg t) := by
  have h := (body M).trace M.code (machine M).code (code_body M) hM
  rw [initial_body] at h
  exact h.trans (Trace.cons (check_false M t) (Trace.refl _))

 theorem next {s t u : List Bool} {n m : ℕ}
    (hM : Trace M.step n (M.initialCfg s) (M.finalCfg (true::t)))
    (hR : Trace (machine M).step m ((machine M).initialCfg t) ((machine M).finalCfg u)) :
    Trace (machine M).step (n+2*t.length+3+m) ((machine M).initialCfg s) ((machine M).finalCfg u) := by
  have h := (body M).trace M.code (machine M).code (code_body M) hM
  rw [initial_body] at h
  have hg := Trace.cons (check_true M t) (transfer_full M t)
  have hh := (h.trans hg).trans hR
  simpa only [Nat.add_assoc,show 2*t.length+2+1=2*t.length+3 by omega] using hh

end Loop

def encodeLoop {α β : Type} (ea : α → List Bool) (eb : β → List Bool) : β ⊕ α → List Bool
  | .inl b => false::eb b
  | .inr a => true::ea a

inductive BoundedRun {α β : Type} (ea : α → List Bool) (f : α → β ⊕ α) (S : ℕ) :
    ℕ → α → β → Prop
  | stop {a b} : (ea a).length ≤ S → f a=.inl b → BoundedRun ea f S 1 a b
  | step {a a' b n} : (ea a).length ≤ S → f a=.inr a' →
      BoundedRun ea f S n a' b → BoundedRun ea f S (n+1) a b

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {f : α → β ⊕ α}

noncomputable def passTime (P : PolyProgram ea (encodeLoop ea eb) f) (S : ℕ) : ℕ :=
  P.time.eval S+2*P.sizeBound.eval S+3

 theorem run_loop (P : PolyProgram ea (encodeLoop ea eb) f) {S n : ℕ} {a : α} {b : β}
    (h : BoundedRun ea f S n a b) :
    ∃ t ≤ n*P.passTime S, Trace (Loop.machine P.machine).step t
      ((Loop.machine P.machine).initialCfg (ea a)) ((Loop.machine P.machine).finalCfg (eb b)) := by
  induction h with
  | @stop a b ha hab =>
      have hp := P.outputs a
      have ht : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
          (P.machine.finalCfg (false::eb b)) := by
        have hh : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
            (P.machine.finalCfg (encodeLoop ea eb (f a))) := Trace.of_iterate hp.evals_in_steps
        simpa only [hab,encodeLoop] using hh
      refine ⟨hp.steps+1,?_,Loop.stop P.machine ht⟩
      have htime := hp.steps_le_m.trans (polynomial_eval_mono P.time ha)
      simp only [passTime,one_mul]
      omega
  | @step a a' b n ha haa' h ih =>
      obtain ⟨t,ht,htrace⟩ := ih
      have hp := P.outputs a
      have hb : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
          (P.machine.finalCfg (true::ea a')) := by
        have hh : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
            (P.machine.finalCfg (encodeLoop ea eb (f a))) := Trace.of_iterate hp.evals_in_steps
        simpa only [haa',encodeLoop] using hh
      refine ⟨hp.steps+2*(ea a').length+3+t,?_,Loop.next P.machine hb htrace⟩
      have htime := hp.steps_le_m.trans (polynomial_eval_mono P.time ha)
      have hl := (P.length_bound a).trans (polynomial_eval_mono P.sizeBound ha)
      simp only [haa',encodeLoop,List.length_cons] at hl
      dsimp only [passTime] at ht ⊢
      rw [Nat.add_mul]
      omega

noncomputable def loop (P : PolyProgram ea (encodeLoop ea eb) f) (g : α → β)
    (iterations sizes : Polynomial ℕ)
    (h : ∀ a, ∃ n ≤ iterations.eval (ea a).length,
      BoundedRun ea f (sizes.eval (ea a).length) n a (g a)) : PolyProgram ea eb g where
  machine := Loop.machine P.machine
  time := iterations*(P.time.comp sizes+2*P.sizeBound.comp sizes+3)
  outputs a := Classical.choice (show Nonempty _ from by
    obtain ⟨n,hn,hrun⟩ := h a
    obtain ⟨t,ht,htrace⟩ := P.run_loop hrun
    refine ⟨⟨⟨t,htrace.iterate_eq⟩,?_⟩⟩
    refine ht.trans ?_
    simpa only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_comp,
      Polynomial.eval_ofNat,passTime] using Nat.mul_le_mul_right (P.passTime (sizes.eval (ea a).length)) hn)

end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BooleanListPrimitives

namespace OAI


                                             
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

def encodeBool (b : Bool) : List Bool := [b]

namespace WordTransducer

def emptyTest : Transducer where
  Q := Bool
  initial := true
  next _ _ := (false,[])
  finish b := [b]

 theorem emptyTest_run (q : Bool) (xs : List Bool) :
    emptyTest.run q xs=[q && xs.isEmpty] := by
  induction xs generalizing q with
  | nil => cases q <;> rfl
  | cons b xs ih =>
      change emptyTest.run false xs=_
      rw [ih]
      simp

def head : Transducer where
  Q := Option Bool
  initial := none
  next q b := (q.or (some b),[])
  finish q := [q.getD false]

 theorem head_run (q : Option Bool) (xs : List Bool) :
    head.run q xs=[(q.or xs.head?).getD false] := by
  induction xs generalizing q with
  | nil => cases q <;> rfl
  | cons b xs ih =>
      change head.run (q.or (some b)) xs=_
      rw [ih]
      cases q <;> rfl

def tail : Transducer where
  Q := Bool
  initial := true
  next q b := (false,if q then [] else [b])
  finish _ := []

 theorem tail_run_false (xs : List Bool) : tail.run false xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::tail.run false xs=b::xs; rw [ih]

 theorem tail_run (xs : List Bool) : tail.run true xs=xs.tail := by
  cases xs with
  | nil => rfl
  | cons b xs => exact tail_run_false xs

abbrev prepend : Transducer where
  Q := Fin 4
  initial := 0
  next q b := if q=0 then (1,[]) else if q=1 then (2,[b]) else if q=2 then (3,[]) else (3,[b])
  finish _ := []

 theorem prepend_done (xs : List Bool) : prepend.run 3 xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change b::prepend.run 3 xs=b::xs
      rw [ih]

 theorem prepend_run (b : Bool) (xs : List Bool) :
    prepend.run 0 (quote [b]++xs)=b::xs := by
  change b::prepend.run 3 xs=b::xs
  rw [prepend_done]

def prependWord (p : List Bool) : Transducer where
  Q := Bool
  initial := true
  next q b := (false,if q then p++[b] else [b])
  finish q := if q then p else []

 theorem prefix_done (p xs : List Bool) : (prependWord p).run false xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::(prependWord p).run false xs=b::xs; rw [ih]

 theorem prefix_run (p xs : List Bool) : (prependWord p).run true xs=p++xs := by
  cases xs with
  | nil => exact (List.append_nil p).symm
  | cons b xs =>
      change (p++[b])++(prependWord p).run false xs=p++b::xs
      rw [prefix_done,List.append_assoc,List.singleton_append]

def select : Transducer where
  Q := Fin 2 ⊕ (Bool × Option (Option Bool))
  initial := .inl 0
  next q b := match q with
    | .inl k => if k=0 then (.inl 1,[]) else (.inr (b,none),[])
    | .inr (keep,none) => (.inr (keep,some none),[])
    | .inr (keep,some none) => (.inr (keep,some (some (!b))),[])
    | .inr (keep,some (some false)) => (.inr (keep,some none),if keep then [] else [b])
    | .inr (keep,some (some true)) => (.inr (keep,some (some true)),if keep then [b] else [])
  finish _ := []

 theorem select_done (keep : Bool) (xs : List Bool) :
    select.run (.inr (keep,some (some true))) xs=if keep then xs else [] := by
  induction xs with
  | nil => cases keep <;> rfl
  | cons b xs ih =>
      change (if keep then [b] else [])++select.run (.inr (keep,some (some true))) xs=_
      rw [ih]
      cases keep <;> simp

 theorem select_pair (keep : Bool) (xs ys : List Bool) :
    select.run (.inr (keep,some none)) (quote xs++ys)=if keep then ys else xs := by
  induction xs with
  | nil => exact select_done keep ys
  | cons b xs ih =>
      change (if keep then [] else [b])++select.run (.inr (keep,some none)) (quote xs++ys)=_
      rw [ih]
      cases keep <;> simp

 theorem select_run (keep : Bool) (xs ys : List Bool) :
    select.run (.inl 0) (quote [keep]++quote xs++ys)=if keep then ys else xs := by
  exact select_pair keep xs ys

end WordTransducer

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

noncomputable def isEmpty : PolyProgram id encodeBool List.isEmpty :=
  WordTransducer.emptyTest.program.of_word (fun xs => by
    simpa only [WordTransducer.emptyTest,Bool.true_and,encodeBool,id_eq] using WordTransducer.emptyTest_run true xs)

noncomputable def head : PolyProgram id encodeBool (fun xs => xs.head?.getD false) :=
  WordTransducer.head.program.of_word (fun xs => by
    simpa only [WordTransducer.head,Option.or,encodeBool,id_eq] using WordTransducer.head_run none xs)

noncomputable def tail : PolyProgram id id List.tail :=
  WordTransducer.tail.program.of_word (fun xs => by
    simpa only [WordTransducer.tail,id_eq] using WordTransducer.tail_run xs)

noncomputable def cons : PolyProgram (encodePair encodeBool id) id (fun x => x.1::x.2) :=
  WordTransducer.prepend.program.of_word (fun x => by
    simpa only [WordTransducer.prepend,encodePair,encodeBool,id_eq] using WordTransducer.prepend_run x.1 x.2)

noncomputable def prependWord (p : List Bool) : PolyProgram id id (fun xs => p++xs) :=
  (WordTransducer.prependWord p).program.of_word (fun xs => by
    simpa only [WordTransducer.prependWord,id_eq] using WordTransducer.prefix_run p xs)

noncomputable def injectLeft (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram eb (encodeLoop ea eb) Sum.inl :=
  (prependWord [false]).of_word (fun _ => rfl)

noncomputable def injectRight (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram ea (encodeLoop ea eb) Sum.inr :=
  (prependWord [true]).of_word (fun _ => rfl)

noncomputable def select (eb : β → List Bool) :
    PolyProgram (encodePair encodeBool (encodePair eb eb)) eb
      (fun x => if x.1 then x.2.2 else x.2.1) :=
  WordTransducer.select.program.of_word (fun x => by
    simpa only [WordTransducer.select,encodePair,encodeBool,List.append_assoc,apply_ite] using
      WordTransducer.select_run x.1 (eb x.2.1) (eb x.2.2))

noncomputable def ite {p : α → Bool} {f g : α → β}
    (P : PolyProgram ea encodeBool p) (F : PolyProgram ea eb f) (G : PolyProgram ea eb g) :
    PolyProgram ea eb (fun a => if p a then g a else f a) :=
  ((P.fanout (F.fanout G)).comp (select eb)).congr _ (fun _ => rfl)

end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BooleanRecode

namespace OAI


                                     
section
namespace MetricKMedian.Binary.PolyProgram
variable {α β α' β' : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {ea' : α' → List Bool} {eb' : β' → List Bool} {f : α → β} {f' : α' → β'}

def recode (P : PolyProgram ea eb f) (i : α' → α)
    (hi : ∀ a, ea (i a)=ea' a) (ho : ∀ a, eb (f (i a))=eb' (f' a)) :
    PolyProgram ea' eb' f' where
  machine := P.machine
  time := P.time
  outputs a := by
    have h := P.outputs (i a)
    rwa [hi,ho] at h

end MetricKMedian.Binary.PolyProgram
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryLists

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Function Polynomial

 def encodeList {α : Type} (ea : α → List Bool) : List α → List Bool
  | [] => []
  | a::as => quote (ea a)++encodeList ea as

namespace EncodedList
variable {α : Type} (ea : α → List Bool)
 theorem nil : encodeList ea []=[] := rfl
 theorem cons (a : α) (as : List α) : encodeList ea (a::as)=quote (ea a)++encodeList ea as := rfl
 theorem cons_length (a : α) (as : List α) : (encodeList ea (a::as)).length=2*(ea a).length+1+(encodeList ea as).length := by
  simp only [encodeList,List.length_append,quote_length]
 theorem length_le (as : List α) : as.length ≤ (encodeList ea as).length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [cons_length,List.length_cons]; omega
 theorem isEmpty (as : List α) : (encodeList ea as).isEmpty=as.isEmpty := by
  cases as with
  | nil => rfl
  | cons a as =>
      have h := cons_length ea a as
      apply List.isEmpty_eq_false_iff.mpr
      intro hz
      simp only [hz,List.length_nil] at h
      omega
 theorem append (as bs : List α) : encodeList ea (as++bs)=encodeList ea as++encodeList ea bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append,encodeList,ih,List.append_assoc]
 theorem reverse_length (as : List α) : (encodeList ea as.reverse).length=(encodeList ea as).length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.reverse_cons,append,List.length_append,cons_length,nil,List.length_nil,ih]
      omega
 theorem member_length (as : List α) (a : α) (h : a∈as) : (ea a).length ≤ (encodeList ea as).length := by
  induction as with
  | nil => simp at h
  | cons b as ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl|h
      · rw [cons_length]; omega
      · have hh := ih h
        rw [cons_length]; omega
 theorem length_bound (as : List α) (L : ℕ) (h : ∀ a∈as, (ea a).length ≤ L) :
    (encodeList ea as).length ≤ as.length*(2*L+1) := by
  induction as with
  | nil => simp only [nil,List.length_nil,zero_mul,le_refl]
  | cons a as ih =>
      have ha := h a (by simp)
      have hh := ih (fun a ha => h a (by simp [ha]))
      rw [cons_length,List.length_cons]
      nlinarith
end EncodedList

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listIsEmpty : PolyProgram (encodeList ea) encodeBool List.isEmpty :=
  isEmpty.recode (encodeList ea) (fun _ => rfl) (fun as => by rw [EncodedList.isEmpty])

noncomputable def listUncons : PolyProgram (encodeList ea) (encodePair ea (encodeList ea))
    (fun as => (as.head?.getD a0,as.tail)) := by
  let raw : PolyProgram (encodeList ea) id (encodeList ea) := (identity id).recode (encodeList ea) (fun _ => rfl) (fun _ => rfl)
  let deflt := constant (encodeList ea) id (Binary.quote (ea a0))
  refine (ite (listIsEmpty ea) raw deflt).recode id (fun _ => rfl) ?_
  intro as
  cases as with
  | nil => simp [encodePair,encodeList]
  | cons a as => rfl
noncomputable def listHead : PolyProgram (encodeList ea) ea (fun as => as.head?.getD a0) :=
  ((listUncons ea a0).comp (fst ea (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listTail : PolyProgram (encodeList ea) (encodeList ea) List.tail :=
  ((listUncons ea a0).comp (snd ea (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listCons : PolyProgram (encodePair ea (encodeList ea)) (encodeList ea) (fun x => x.1::x.2) :=
  (identity id).recode (encodePair ea (encodeList ea)) (fun _ => rfl) (fun _ => rfl)
end PolyProgram

namespace ListReverse
variable {α : Type} (ea : α → List Bool) (a0 : α)
abbrev enc : List α × List α → List Bool := encodePair (encodeList ea) (encodeList ea)
 def body (s : List α × List α) : List α ⊕ (List α × List α) :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,s.1.head?.getD a0::s.2)
 def result (s : List α × List α) : List α := s.1.reverse++s.2

noncomputable def program : PolyProgram (enc ea) (encodeLoop (enc ea) (encodeList ea)) (body a0) := by
  let px := PolyProgram.fst (encodeList ea) (encodeList ea)
  let py := PolyProgram.snd (encodeList ea) (encodeList ea)
  let hd := px.comp (PolyProgram.listHead ea a0)
  let tl := px.comp (PolyProgram.listTail ea a0)
  let newLast := (hd.fanout py).comp (PolyProgram.listCons ea)
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight (enc ea) (encodeList ea))
  let done := py.comp (PolyProgram.injectLeft (enc ea) (encodeList ea))
  exact (PolyProgram.ite (px.comp (PolyProgram.listIsEmpty ea)) recur done).congr _ (fun _ => rfl)

 theorem run (as bs : List α) (S : ℕ) (h : 2*(encodeList ea as).length+1+(encodeList ea bs).length ≤ S) :
    BoundedRun (enc ea) (body a0) S (as.length+1) (as,bs) (as.reverse++bs) := by
  induction as generalizing bs with
  | nil =>
      apply BoundedRun.stop
      · simpa only [enc,encodePair_length] using h
      · rfl
  | cons a as ih =>
      have hs : 2*(encodeList ea as).length+1+(encodeList ea (a::bs)).length ≤ S := by
        simp only [EncodedList.cons_length] at h ⊢
        omega
      have hr := BoundedRun.step (ea:=enc ea) (f:=body a0)
        (a:=(a::as,bs)) (a':=(as,a::bs))
        (by simpa only [enc,encodePair_length] using h) rfl (ih (a::bs) hs)
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hr

noncomputable def loop : PolyProgram (enc ea) (encodeList ea) result :=
  (program ea a0).loop result (X+1) X (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · have h := EncodedList.length_le ea s.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]; omega
    · simpa only [eval_X,enc,encodePair_length,result] using run ea a0 s.1 s.2
        (2*(encodeList ea s.1).length+1+(encodeList ea s.2).length) le_rfl)
end ListReverse

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listReverse : PolyProgram (encodeList ea) (encodeList ea) List.reverse :=
  (((identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList ea) [])).comp (ListReverse.loop ea a0)).congr _
    (fun _ => List.append_nil _)
noncomputable def listAppend : PolyProgram (encodePair (encodeList ea) (encodeList ea)) (encodeList ea) (fun x => x.1++x.2) :=
  (((listReverse ea a0).thread (encodeList ea)).comp (ListReverse.loop ea a0)).congr _
    (fun _ => by simp only [Function.comp_apply,ListReverse.result,List.reverse_reverse])
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryListFold

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ListFold
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α)
variable (op : β × α → β)
abbrev enc : List α × β → List Bool := encodePair (encodeList ea) eb
 def body (s : List α × β) : β ⊕ (List α × β) :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,op (s.2,s.1.head?.getD a0))
 def result (s : List α × β) : β := s.1.foldl (fun b a => op (b,a)) s.2

noncomputable def program (P : PolyProgram (encodePair eb ea) eb op) :
    PolyProgram (enc ea eb) (encodeLoop (enc ea eb) eb) (body a0 op) := by
  let px := PolyProgram.fst (encodeList ea) eb
  let py := PolyProgram.snd (encodeList ea) eb
  let hd := px.comp (PolyProgram.listHead ea a0)
  let tl := px.comp (PolyProgram.listTail ea a0)
  let newLast := (py.fanout hd).comp P
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight (enc ea eb) eb)
  let done := py.comp (PolyProgram.injectLeft (enc ea eb) eb)
  exact (PolyProgram.ite (px.comp (PolyProgram.listIsEmpty ea)) recur done).congr _ (fun _ => rfl)

 theorem run (as : List α) (b : β) (S : ℕ)
    (h : ∀ pre suf, as=pre++suf → (enc ea eb (suf,pre.foldl (fun b a => op (b,a)) b)).length ≤ S) :
    BoundedRun (enc ea eb) (body a0 op) S (as.length+1) (as,b) (result op (as,b)) := by
  induction as generalizing b with
  | nil =>
      apply BoundedRun.stop
      · exact h [] [] rfl
      · rfl
  | cons a as ih =>
      have hs : ∀ pre suf, as=pre++suf →
          (enc ea eb (suf,pre.foldl (fun b a => op (b,a)) (op (b,a)))).length ≤ S := by
        intro pre suf he
        exact h (a::pre) suf (by simp only [List.cons_append,he])
      exact BoundedRun.step (h [] (a::as) rfl) rfl (ih (op (b,a)) hs)

noncomputable def loop (P : PolyProgram (encodePair eb ea) eb op) (B : Polynomial ℕ)
    (hB : ∀ (as : List α) (b : β) pre suf, as=pre++suf →
      (eb (pre.foldl (fun b a => op (b,a)) b)).length ≤ B.eval (enc ea eb (as,b)).length) :
    PolyProgram (enc ea eb) eb (result op) :=
  (program ea eb a0 op P).loop (result op) (X+1) (2*X+1+B) (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · have h := EncodedList.length_le ea s.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]; omega
    · apply run
      intro pre suf he
      have hh := hB s.1 s.2 pre suf he
      have hx : (encodeList ea suf).length ≤ (encodeList ea s.1).length := by
        rw [he,EncodedList.append,List.length_append]
        omega
      simp only [enc,encodePair_length] at hh ⊢
      simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
      omega)

 theorem linear_height (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1))
    (as : List α) (b : β) :
    (eb (as.foldl (fun b a => op (b,a)) b)).length ≤ (eb b).length+C*(encodeList ea as).length := by
  induction as generalizing b with
  | nil => simp only [List.foldl_nil,EncodedList.nil,List.length_nil,mul_zero,add_zero,le_refl]
  | cons a as ih =>
      have hh := ih (op (b,a))
      have ha := hop b a
      simp only [List.foldl_cons,EncodedList.cons_length]
      nlinarith

noncomputable def linearLoop (P : PolyProgram (encodePair eb ea) eb op) (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1)) :
    PolyProgram (enc ea eb) eb (result op) :=
  loop ea eb a0 op P ((Polynomial.C C+1)*X) (fun as b pre suf he => by
    have hh := linear_height ea eb op C hop pre b
    have hp : (encodeList ea pre).length ≤ (encodeList ea as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    simp only [eval_mul,eval_add,eval_C,eval_one,eval_X,enc,encodePair_length]
    nlinarith)
end ListFold

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {op : β × α → β}
noncomputable def listFold (P : PolyProgram (encodePair eb ea) eb op) (a0 : α) (B : Polynomial ℕ)
    (hB : ∀ (as : List α) (b : β) pre suf, as=pre++suf →
      (eb (pre.foldl (fun b a => op (b,a)) b)).length ≤ B.eval (encodePair (encodeList ea) eb (as,b)).length) :
    PolyProgram (encodePair (encodeList ea) eb) eb (fun x => x.1.foldl (fun b a => op (b,a)) x.2) :=
  ListFold.loop ea eb a0 op P B hB
noncomputable def listFoldLinear (P : PolyProgram (encodePair eb ea) eb op) (a0 : α) (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1)) :
    PolyProgram (encodePair (encodeList ea) eb) eb (fun x => x.1.foldl (fun b a => op (b,a)) x.2) :=
  ListFold.linearLoop ea eb a0 op P C hop
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BooleanReverse

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ReverseLoop
abbrev S := List Bool × List Bool
abbrev enc : S → List Bool := encodePair id id

def body (s : S) : List Bool ⊕ S :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,s.1.head?.getD false::s.2)

def result (s : S) : List Bool := s.1.reverse++s.2

noncomputable def program : PolyProgram enc (encodeLoop enc id) body := by
  let first := PolyProgram.fst id id
  let last := PolyProgram.snd id id
  let hd := first.comp PolyProgram.head
  let tl := first.comp PolyProgram.tail
  let newLast := (hd.fanout last).comp PolyProgram.cons
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight enc id)
  let done := last.comp (PolyProgram.injectLeft enc id)
  exact (PolyProgram.ite (first.comp PolyProgram.isEmpty) recur done).congr _ (fun _ => rfl)

 theorem run (xs ys : List Bool) (S : ℕ) (h : 2*xs.length+1+ys.length≤S) :
    BoundedRun enc body S (xs.length+1) (xs,ys) (xs.reverse++ys) := by
  induction xs generalizing ys with
  | nil =>
      apply BoundedRun.stop
      · simpa only [enc,encodePair_length,id_eq,List.length_nil,zero_mul,zero_add] using h
      · rfl
  | cons b xs ih =>
      have hs : 2*xs.length+1+(b::ys).length≤S := by simp only [List.length_cons] at h ⊢; omega
      have hr := BoundedRun.step (ea:=enc) (f:=body)
        (a:=(b::xs,ys)) (a':=(xs,b::ys))
        (by simpa only [enc,encodePair_length,id_eq] using h) rfl (ih (b::ys) hs)
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hr

noncomputable def loop : PolyProgram enc id result :=
  program.loop result (X+1) X (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc,encodePair_length,id_eq]; omega
    · simpa only [eval_X,enc,encodePair_length,id_eq,result] using run s.1 s.2 (2*s.1.length+1+s.2.length) le_rfl)

end ReverseLoop

namespace PolyProgram
noncomputable def reverse : PolyProgram id id List.reverse :=
  (((identity id).fanout (constant id id [])).comp ReverseLoop.loop).congr _
    (fun _ => List.append_nil _)
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryWords

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word

def value : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*value bs

@[simp] theorem value_nil : value []=0 := rfl
@[simp] theorem value_cons (b : Bool) (xs : List Bool) : value (b::xs)=b.toNat+2*value xs := rfl

 theorem value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih => rw [Nat.bits_append_bit n b hn,value_cons,ih,Nat.bit_val]; omega

 theorem value_zero (xs : List Bool) : value xs=0 ↔ ∀ b∈xs,b=false := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp only [value_cons,Nat.add_eq_zero_iff,Nat.mul_eq_zero,OfNat.ofNat_ne_zero,false_or,Bool.toNat_eq_zero,ih,List.forall_mem_cons]

 theorem bits_value (xs : List Bool) (h : xs.getLast?≠some false) : (value xs).bits=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      by_cases he : xs=[]
      · subst xs
        cases b
        · exact False.elim (h rfl)
        · rfl
      · have ht : xs.getLast?≠some false := by
          intro hh
          apply h
          simp only [List.getLast?_cons,hh,Option.getD_some]
        rw [value_cons,show b.toNat+2*value xs=Nat.bit b (value xs) by rw [Nat.bit_val]; omega]
        rw [Nat.bits_append_bit,ih ht]
        intro hzero
        exfalso
        have hh := value_zero xs |>.mp hzero
        have hl := List.getLast_mem he
        have hb := hh _ hl
        apply ht
        rw [List.getLast?_eq_some_getLast he,hb]

 theorem value_append (xs ys : List Bool) : value (xs++ys)=value xs+2^xs.length*value ys := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp only [List.cons_append,value_cons,ih,List.length_cons,pow_succ]; ring

 theorem value_reverse_drop (xs : List Bool) : value (xs.dropWhile Bool.not).reverse=value xs.reverse := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b
      · simp only [List.dropWhile_cons,Bool.not_false,ite_true,List.reverse_cons,value_append,
          value_cons,value_nil,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,zero_add]
        exact ih
      · simp

 theorem drop_head (xs : List Bool) : (xs.dropWhile Bool.not).head?≠some false := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp_all

 def normalize (xs : List Bool) : List Bool := (xs.reverse.dropWhile Bool.not).reverse

 theorem normalize_eq_bits (xs : List Bool) : normalize xs=(value xs).bits := by
  have hv : value (normalize xs)=value xs := by
    simpa only [normalize,List.reverse_reverse] using value_reverse_drop xs.reverse
  rw [← hv,bits_value]
  simp only [normalize,List.getLast?_reverse]
  exact drop_head _

end Word

namespace WordTransducer

def dropFalse : Transducer where
  Q := Bool
  initial := false
  next q b := (q || b,if q || b then [b] else [])
  finish _ := []

 theorem dropFalse_true (xs : List Bool) : dropFalse.run true xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::dropFalse.run true xs=b::xs; rw [ih]

 theorem dropFalse_run (xs : List Bool) : dropFalse.run false xs=xs.dropWhile Bool.not := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b
      · exact ih
      · exact congrArg (List.cons true) (dropFalse_true xs)

end WordTransducer

namespace PolyProgram
noncomputable def append : PolyProgram (encodePair id id) id (fun x : List Bool × List Bool => x.1++x.2) :=
  ((reverse.thread id).comp ReverseLoop.loop).congr _ (fun x => by
    simp only [Function.comp_apply,ReverseLoop.result,List.reverse_reverse])

noncomputable def dropFalse : PolyProgram id id (List.dropWhile Bool.not) :=
  WordTransducer.dropFalse.program.of_word (fun xs => by
    simpa only [WordTransducer.dropFalse,id_eq] using WordTransducer.dropFalse_run xs)

noncomputable def normalize : PolyProgram id id Word.normalize :=
  ((reverse.comp dropFalse).comp reverse).congr _ (fun _ => rfl)

noncomputable def toBits : PolyProgram id Nat.bits Word.value :=
  normalize.of_word (fun xs => Word.normalize_eq_bits xs)

end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryNatural

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word
 theorem normalize_length (xs : List Bool) : (normalize xs).length≤xs.length := by
  simpa only [normalize,List.length_reverse] using List.length_dropWhile_le Bool.not xs.reverse

 theorem bits_value_length (xs : List Bool) : (value xs).bits.length≤xs.length := by
  rw [← normalize_eq_bits]
  exact normalize_length xs
end Word

namespace NatBinary
 theorem zero_iff (n : ℕ) : n.bits=[] ↔ n=0 := by
  constructor
  · intro h
    have hv := Word.value_bits n
    rw [h,Word.value_nil] at hv
    exact hv.symm
  · rintro rfl; rfl

 theorem bit_length (b : Bool) (n : ℕ) : (Nat.bit b n).bits.length≤n.bits.length+1 := by
  have h := Word.bits_value_length (b::n.bits)
  simpa only [Word.value_cons,Word.value_bits,Nat.bit_val,Nat.add_comm,List.length_cons] using h

 theorem half_length (n : ℕ) : n.div2.bits.length=n.bits.length-1 := by
  rw [Nat.div2_bits_eq_tail,List.length_tail]

 theorem add_length (a b : ℕ) : (a+b).bits.length≤ max a.bits.length b.bits.length+1 := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have ha := (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (le_max_left a.size b.size))
  have hb := (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (le_max_right a.size b.size))
  rw [pow_succ]
  omega

 theorem mul_length (a b : ℕ) : (a*b).bits.length≤a.bits.length+b.bits.length := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  rw [pow_add]
  nlinarith

 theorem length_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h

 theorem half_lt_length {n : ℕ} (hn : n≠0) : n.div2.bits.length<n.bits.length := by
  rw [half_length]
  have hh : n.bits≠[] := fun h => hn ((zero_iff n).mp h)
  have hl : 0<n.bits.length := List.length_pos_iff.mpr hh
  omega
end NatBinary

namespace PolyProgram
noncomputable def natBit : PolyProgram (encodePair encodeBool Nat.bits) Nat.bits (fun x : Bool × ℕ => Nat.bit x.1 x.2) :=
  (cons.comp toBits).recode (fun x => (x.1,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.value_cons,Word.value_bits,Nat.bit_val,Nat.add_comm])

noncomputable def natHalf : PolyProgram Nat.bits Nat.bits Nat.div2 :=
  tail.recode Nat.bits (fun _ => rfl) (fun n => (Nat.div2_bits_eq_tail n).symm)

noncomputable def natOdd : PolyProgram Nat.bits encodeBool Nat.bodd :=
  head.recode Nat.bits (fun _ => rfl) (fun n => by
    rw [Nat.bodd_eq_bits_head]
    cases n.bits <;> rfl)

noncomputable def natZero : PolyProgram Nat.bits encodeBool (fun n => decide (n=0)) :=
  isEmpty.recode Nat.bits (fun _ => rfl) (fun n => by
    congr 1
    cases h : n.bits.isEmpty
    · have hn : n≠0 := by intro hn; subst n; contradiction
      exact (decide_eq_false hn).symm
    · have hn : n=0 := (NatBinary.zero_iff n).mp (List.isEmpty_iff.mp h)
      exact (decide_eq_true hn).symm)
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BooleanFinite

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Finset

namespace FiniteTransducer
variable {α β : Type} [Fintype α] (ea : α → List Bool) (eb : β → List Bool) (f : α → β)

noncomputable def prefixes : Finset (List Bool) :=
  univ.biUnion (fun a => (ea a).inits.toFinset)

 theorem mem_prefixes (a : α) (xs ys : List Bool) (h : xs++ys=ea a) : xs∈prefixes ea := by
  classical
  apply mem_biUnion.mpr
  refine ⟨a,mem_univ _,List.mem_toFinset.mpr ?_⟩
  exact (List.mem_inits _ _).mpr ⟨ys,h⟩

abbrev Q := Option {xs : List Bool // xs∈prefixes ea}

noncomputable def state (xs : List Bool) : Q ea :=
  if h : xs∈prefixes ea then some ⟨xs,h⟩ else none

noncomputable abbrev table : Transducer where
  Q := Q ea
  initial := state ea []
  next q b := (match q with | none => none | some xs => state ea (xs.val++[b]),[])
  finish q := match q with
    | none => []
    | some xs => if h : ∃ a, ea a=xs.val then eb (f (Classical.choose h)) else []

 theorem next_state (xs : List Bool) (b : Bool) (h : xs∈prefixes ea) :
    (table ea eb f).next (state ea xs) b=(state ea (xs++[b]),[]) := by
  simp only [table,state,dif_pos h]

 theorem finish_state (a : α) (hinj : Injective ea) :
    (table ea eb f).finish (state ea (ea a))=eb (f a) := by
  have hm := mem_prefixes ea a (ea a) [] (List.append_nil _)
  have hex : ∃ a', ea a'=ea a := ⟨a,rfl⟩
  simp only [state,dif_pos hm,dif_pos hex]
  have he := Classical.choose_spec hex
  rw [hinj he]

 theorem run_state (a : α) (hinj : Injective ea) (xs ys : List Bool) (h : xs++ys=ea a) :
    (table ea eb f).run (state ea xs) ys=eb (f a) := by
  induction ys generalizing xs with
  | nil =>
      have he : xs=ea a := by simpa only [List.append_nil] using h
      rw [he]
      exact finish_state ea eb f a hinj
  | cons b ys ih =>
      change ((table ea eb f).next (state ea xs) b).2 ++
        (table ea eb f).run ((table ea eb f).next (state ea xs) b).1 ys = _
      rw [next_state ea eb f xs b (mem_prefixes ea a xs (b::ys) h),List.nil_append]
      apply ih
      simpa only [List.append_assoc,List.singleton_append] using h

noncomputable def program (hinj : Injective ea) : PolyProgram ea eb f :=
  (table ea eb f).program.of_word (fun a =>
    run_state ea eb f a hinj [] (ea a) rfl)

end FiniteTransducer

 theorem encodeBool_injective : Injective encodeBool := by
  intro a b h
  simpa only [encodeBool,List.cons.injEq,true_and,and_true] using h

 theorem quote_injective : Injective quote := by
  intro xs ys h
  have hh := congrArg ((WordTransducer.projecting false).run none) h
  have hx := WordTransducer.projecting_pair false xs []
  have hy := WordTransducer.projecting_pair false ys []
  simp only [List.append_nil,Bool.false_eq_true,ite_false] at hx hy
  rwa [hx,hy] at hh

 theorem encodePair_injective {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    (ha : Injective ea) (hb : Injective eb) : Injective (encodePair ea eb) := by
  intro a b h
  have hx := congrArg ((WordTransducer.projecting false).run none) h
  have hy := congrArg ((WordTransducer.projecting true).run none) h
  simp only [encodePair,WordTransducer.projecting_pair,Bool.false_eq_true,ite_false,ite_true] at hx hy
  exact Prod.ext (ha hx) (hb hy)

namespace PolyProgram

noncomputable def boolFunction {α β : Type} [Fintype α] (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) (hinj : Injective ea) : PolyProgram ea eb f :=
  FiniteTransducer.program ea eb f hinj

noncomputable def boolNot : PolyProgram encodeBool encodeBool Bool.not :=
  boolFunction _ _ _ encodeBool_injective
noncomputable def boolAnd : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => x.1 && x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)
noncomputable def boolOr : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => x.1 || x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)

end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryAddition

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word

def sumBit (a b c : Bool) : Bool := xor (xor a b) c
 def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

 theorem fullAdder (a b c : Bool) :
    (sumBit a b c).toNat+2*(carryBit a b c).toNat=a.toNat+b.toNat+c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

 def add : List Bool → List Bool → Bool → List Bool
  | [],[],c => if c then [true] else []
  | a::xs,ys,c => sumBit a (ys.head?.getD false) c :: add xs ys.tail (carryBit a (ys.head?.getD false) c)
  | [],b::ys,c => sumBit false b c :: add [] ys (carryBit false b c)
termination_by xs ys _ => xs.length+ys.length

 theorem add_step (xs ys : List Bool) (c : Bool) (h : (xs.isEmpty && ys.isEmpty)=false) :
    add xs ys c=sumBit (xs.head?.getD false) (ys.head?.getD false) c ::
      add xs.tail ys.tail (carryBit (xs.head?.getD false) (ys.head?.getD false) c) := by
  cases xs <;> cases ys <;> simp_all only [List.isEmpty_nil,List.isEmpty_cons,Bool.true_and,Bool.false_and,
    Bool.true_eq_false,List.head?_cons,List.head?_nil,Option.getD_some,Option.getD_none,
    List.tail_nil,List.tail_cons,add]

 theorem value_add (xs ys : List Bool) (c : Bool) : value (add xs ys c)=value xs+value ys+c.toNat := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [add,value]
      | cons b ys ih =>
          rw [add,value_cons,ih]
          have h := fullAdder false b c
          simp only [value_nil,value_cons,Bool.toNat_false] at *
          omega
  | cons a xs ih =>
      rw [add,value_cons,ih]
      have h := fullAdder a (ys.head?.getD false) c
      cases ys with
      | nil => simp only [List.head?_nil,Option.getD_none,List.tail_nil,value_nil,value_cons,Bool.toNat_false] at *; omega
      | cons b ys => simp only [List.head?_cons,Option.getD_some,List.tail_cons,value_cons] at *; omega

end Word

namespace AdditionLoop
abbrev S := List Bool × (List Bool × (Bool × List Bool))
abbrev ec : Bool × List Bool → List Bool := encodePair encodeBool id
abbrev ey : List Bool × (Bool × List Bool) → List Bool := encodePair id ec
abbrev enc : S → List Bool := encodePair id ey
 def empty (s : S) : Bool := s.1.isEmpty && s.2.1.isEmpty
 def next (s : S) : S :=
  (s.1.tail,(s.2.1.tail,(Word.carryBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1,
    Word.sumBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1 :: s.2.2.2)))
 def finish (s : S) : List Bool := (if s.2.2.1 then true::s.2.2.2 else s.2.2.2).reverse
 def body (s : S) : List Bool ⊕ S := if empty s then .inl (finish s) else .inr (next s)
 def result (s : S) : List Bool := s.2.2.2.reverse++Word.add s.1 s.2.1 s.2.2.1

 theorem enc_length (s : S) : (enc s).length=2*s.1.length+2*s.2.1.length+s.2.2.2.length+5 := by
  simp only [enc,ey,ec,encodePair_length,encodeBool,id_eq,List.length_cons,List.length_nil]
  omega

noncomputable def program : PolyProgram enc (encodeLoop enc id) body := by
  let px := PolyProgram.fst id ey
  let pyz := PolyProgram.snd id ey
  let py := pyz.comp (PolyProgram.fst id ec)
  let pca := pyz.comp (PolyProgram.snd id ec)
  let pc := pca.comp (PolyProgram.fst encodeBool id)
  let pa := pca.comp (PolyProgram.snd encodeBool id)
  let bits := (px.comp PolyProgram.head).fanout ((py.comp PolyProgram.head).fanout pc)
  let binj := encodePair_injective encodeBool_injective (encodePair_injective encodeBool_injective encodeBool_injective)
  let sb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.sumBit v.1 v.2.1 v.2.2) binj)
  let cb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.carryBit v.1 v.2.1 v.2.2) binj)
  let na := (sb.fanout pa).comp PolyProgram.cons
  let pn := (px.comp PolyProgram.tail).fanout ((py.comp PolyProgram.tail).fanout (cb.fanout na))
  let pe := ((px.comp PolyProgram.isEmpty).fanout (py.comp PolyProgram.isEmpty)).comp PolyProgram.boolAnd
  let pf := (PolyProgram.ite pc pa ((PolyProgram.constant enc encodeBool true).fanout pa |>.comp PolyProgram.cons)).comp PolyProgram.reverse
  exact (PolyProgram.ite pe (pn.comp (PolyProgram.injectRight enc id))
    (pf.comp (PolyProgram.injectLeft enc id))).congr _ (fun _ => rfl)

 theorem shorten (s : S) (h : empty s=false) :
    s.1.tail.length+s.2.1.tail.length<s.1.length+s.2.1.length := by
  rcases s with ⟨xs,ys,c,acc⟩
  cases xs <;> cases ys <;> simp_all [empty]
  omega

 theorem next_result (s : S) (h : empty s=false) : result (next s)=result s := by
  simp only [result]
  rw [Word.add_step s.1 s.2.1 s.2.2.1 h]
  simp only [next,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem next_size (s : S) (h : empty s=false) : (enc (next s)).length≤(enc s).length := by
  have hs := shorten s h
  simp only [enc_length,next,List.length_cons]
  omega

 theorem run (L : ℕ) : ∀ (s : S) (S : ℕ), s.1.length+s.2.1.length=L → (enc s).length≤S →
    ∃ n≤L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL hs
      cases he : empty s with
      | true =>
          refine ⟨1,by omega,BoundedRun.stop hs ?_⟩
          rcases s with ⟨xs,ys,c,acc⟩
          have hz : xs=[] ∧ ys=[] := by simpa only [empty,Bool.and_eq_true,List.isEmpty_iff] using he
          rcases hz with ⟨rfl,rfl⟩
          cases c <;> simp [body,empty,finish,result,Word.add]
      | false =>
          have hl : (next s).1.length+(next s).2.1.length<L := by simpa only [next,hL] using shorten s he
          obtain ⟨n,hn,hr⟩ := ih _ hl (next s) S rfl ((next_size s he).trans hs)
          refine ⟨n+1,by omega,?_⟩
          rw [next_result s he] at hr
          exact BoundedRun.step hs (by simp only [body,he,Bool.false_eq_true,ite_false]) hr

noncomputable def loop : PolyProgram enc id result :=
  program.loop result (X+1) X (fun s => by
    obtain ⟨n,hn,hr⟩ := run (s.1.length+s.2.1.length) s (enc s).length rfl le_rfl
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc_length]; omega
    · simpa only [eval_X] using hr)

end AdditionLoop

namespace PolyProgram
noncomputable def addWords : PolyProgram (encodePair id id) id (fun x : List Bool × List Bool => Word.add x.1 x.2 false) := by
  let ex : List Bool × List Bool → List Bool := encodePair id id
  let init := (fst id id).fanout ((snd id id).fanout (constant ex AdditionLoop.ec (false,[])))
  exact (init.comp AdditionLoop.loop).congr _ (fun _ => rfl)

noncomputable def natAdd : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1+x.2) :=
  (addWords.comp toBits).recode (fun x => (x.1.bits,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.value_add,Word.value_bits,Bool.toNat_false,Nat.add_zero])
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinarySubtraction

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word
 def borrowBit (a b c : Bool) : Bool := ((!a) && b) || ((!a) && c) || (b && c)
 theorem fullSubtract (a b c : Bool) :
    a.toNat+2*(borrowBit a b c).toNat=b.toNat+c.toNat+(sumBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

 def sub : List Bool → List Bool → Bool → Bool × List Bool
  | [],[],c => (c,[])
  | a::xs,ys,c =>
      let t := sub xs ys.tail (borrowBit a (ys.head?.getD false) c)
      (t.1,sumBit a (ys.head?.getD false) c::t.2)
  | [],b::ys,c =>
      let t := sub [] ys (borrowBit false b c)
      (t.1,sumBit false b c::t.2)
termination_by xs ys _ => xs.length+ys.length

 theorem sub_step (xs ys : List Bool) (c : Bool) (h : (xs.isEmpty && ys.isEmpty)=false) :
    sub xs ys c=
      let t := sub xs.tail ys.tail (borrowBit (xs.head?.getD false) (ys.head?.getD false) c)
      (t.1,sumBit (xs.head?.getD false) (ys.head?.getD false) c::t.2) := by
  cases xs <;> cases ys <;> simp_all [sub]

 theorem value_lt (xs : List Bool) : value xs<2^xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
      have hb : b.toNat≤1 := by cases b <;> decide
      simp only [value_cons,List.length_cons,pow_succ]
      omega

 theorem value_sub (xs ys : List Bool) (c : Bool) :
    value (sub xs ys c).2+value ys+c.toNat=
      value xs+2^(sub xs ys c).2.length*(sub xs ys c).1.toNat := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => simp [sub,value]
      | cons b ys ih =>
          rw [sub]
          simp only [value_cons,value_nil,List.length_cons,pow_succ]
          have h := ih (borrowBit false b c)
          have hb := fullSubtract false b c
          simp only [value_nil,Bool.toNat_false] at h hb
          nlinarith
  | cons a xs ih =>
      rw [sub]
      simp only [value_cons,List.length_cons,pow_succ]
      have h := ih ys.tail (borrowBit a (ys.head?.getD false) c)
      have hb := fullSubtract a (ys.head?.getD false) c
      cases ys with
      | nil =>
          simp only [value_nil,List.head?_nil,Option.getD_none,List.tail_nil,Bool.toNat_false] at *
          nlinarith
      | cons b ys =>
          simp only [value_cons,List.head?_cons,Option.getD_some,List.tail_cons] at *
          nlinarith

 theorem sub_borrow (xs ys : List Bool) : (sub xs ys false).1=decide (value xs<value ys) := by
  have h := value_sub xs ys false
  have hl := value_lt (sub xs ys false).2
  cases he : (sub xs ys false).1
  · simp only [he,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at h
    have hn : ¬ value xs<value ys := by omega
    simp only [decide_eq_false hn]
  · simp only [he,Bool.toNat_true,Bool.toNat_false,Nat.mul_one,Nat.add_zero] at h
    have hn : value xs<value ys := by omega
    simp only [decide_eq_true hn]

 theorem sub_clamp (xs ys : List Bool) :
    value (if (sub xs ys false).1 then [] else (sub xs ys false).2)=value xs-value ys := by
  have h := value_sub xs ys false
  cases he : (sub xs ys false).1
  · simp only [he,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at h
    simp only [Bool.false_eq_true,ite_false]
    omega
  · have hl := sub_borrow xs ys
    rw [he] at hl
    have hn : value xs<value ys := of_decide_eq_true hl.symm
    simp only [ite_true,value_nil]
    omega
end Word

namespace SubtractionLoop
open AdditionLoop (S ec ey enc enc_length)
 def next (s : S) : S :=
  (s.1.tail,(s.2.1.tail,(Word.borrowBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1,
    Word.sumBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1 :: s.2.2.2)))
 def finish (s : S) : Bool × List Bool := (s.2.2.1,s.2.2.2.reverse)
 def body (s : S) : (Bool × List Bool) ⊕ S := if AdditionLoop.empty s then .inl (finish s) else .inr (next s)
 def result (s : S) : Bool × List Bool :=
  let t := Word.sub s.1 s.2.1 s.2.2.1
  (t.1,s.2.2.2.reverse++t.2)

noncomputable def program : PolyProgram enc (encodeLoop enc ec) body := by
  let px := PolyProgram.fst id ey
  let pyz := PolyProgram.snd id ey
  let py := pyz.comp (PolyProgram.fst id ec)
  let pca := pyz.comp (PolyProgram.snd id ec)
  let pc := pca.comp (PolyProgram.fst encodeBool id)
  let pa := pca.comp (PolyProgram.snd encodeBool id)
  let bits := (px.comp PolyProgram.head).fanout ((py.comp PolyProgram.head).fanout pc)
  let binj := encodePair_injective encodeBool_injective (encodePair_injective encodeBool_injective encodeBool_injective)
  let sb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.sumBit v.1 v.2.1 v.2.2) binj)
  let cb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.borrowBit v.1 v.2.1 v.2.2) binj)
  let na := (sb.fanout pa).comp PolyProgram.cons
  let pn := (px.comp PolyProgram.tail).fanout ((py.comp PolyProgram.tail).fanout (cb.fanout na))
  let pe := ((px.comp PolyProgram.isEmpty).fanout (py.comp PolyProgram.isEmpty)).comp PolyProgram.boolAnd
  let pf := pc.fanout (pa.comp PolyProgram.reverse)
  exact (PolyProgram.ite pe (pn.comp (PolyProgram.injectRight enc ec))
    (pf.comp (PolyProgram.injectLeft enc ec))).congr _ (fun _ => rfl)

 theorem next_result (s : S) (h : AdditionLoop.empty s=false) : result (next s)=result s := by
  simp only [result]
  rw [Word.sub_step s.1 s.2.1 s.2.2.1 h]
  simp only [next,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem next_size (s : S) (h : AdditionLoop.empty s=false) : (enc (next s)).length≤(enc s).length := by
  have hs := AdditionLoop.shorten s h
  simp only [enc_length,next,List.length_cons]
  omega

 theorem run (L : ℕ) : ∀ (s : S) (S : ℕ), s.1.length+s.2.1.length=L → (enc s).length≤S →
    ∃ n≤L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL hs
      cases he : AdditionLoop.empty s with
      | true =>
          refine ⟨1,by omega,BoundedRun.stop hs ?_⟩
          rcases s with ⟨xs,ys,c,acc⟩
          have hz : xs=[] ∧ ys=[] := by simpa only [AdditionLoop.empty,Bool.and_eq_true,List.isEmpty_iff] using he
          rcases hz with ⟨rfl,rfl⟩
          simp [body,AdditionLoop.empty,finish,result,Word.sub]
      | false =>
          have hl : (next s).1.length+(next s).2.1.length<L := by simpa only [next,hL] using AdditionLoop.shorten s he
          obtain ⟨n,hn,hr⟩ := ih _ hl (next s) S rfl ((next_size s he).trans hs)
          refine ⟨n+1,by omega,?_⟩
          rw [next_result s he] at hr
          exact BoundedRun.step hs (by simp only [body,he,Bool.false_eq_true,ite_false]) hr

noncomputable def loop : PolyProgram enc ec result :=
  program.loop result (X+1) X (fun s => by
    obtain ⟨n,hn,hr⟩ := run (s.1.length+s.2.1.length) s (enc s).length rfl le_rfl
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc_length]; omega
    · simpa only [eval_X] using hr)
end SubtractionLoop

namespace PolyProgram
noncomputable def subWords : PolyProgram (encodePair id id) AdditionLoop.ec (fun x : List Bool × List Bool => Word.sub x.1 x.2 false) := by
  let ex : List Bool × List Bool → List Bool := encodePair id id
  let init := (fst id id).fanout ((snd id id).fanout (constant ex AdditionLoop.ec (false,[])))
  exact (init.comp SubtractionLoop.loop).congr _ (fun _ => rfl)

noncomputable def natLT : PolyProgram (encodePair Nat.bits Nat.bits) encodeBool (fun x : ℕ × ℕ => decide (x.1<x.2)) :=
  (subWords.comp (fst encodeBool id)).recode (fun x => (x.1.bits,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.sub_borrow,Word.value_bits])

noncomputable def natSub : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1-x.2) := by
  let clamp := ite (fst encodeBool id) (snd encodeBool id) (constant AdditionLoop.ec id [])
  exact ((subWords.comp clamp).comp toBits).recode (fun x => (x.1.bits,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.sub_clamp,Word.value_bits])
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryDivision

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace DivisionLoop
 def qstep (b : Bool) (d q r : ℕ) : ℕ := Nat.bit (!decide (Nat.bit b r<d)) q
 def rstep (b : Bool) (d r : ℕ) : ℕ := if Nat.bit b r<d then Nat.bit b r else Nat.bit b r-d

 theorem step_total (b : Bool) (d q r : ℕ) :
    qstep b d q r*d+rstep b d r=2*(q*d+r)+b.toNat := by
  by_cases ht : Nat.bit b r<d
  · rw [qstep,rstep,if_pos ht,decide_eq_true ht]
    simp only [Bool.not_true,Nat.bit_val,Bool.toNat_false]
    ring
  · have hd : d≤Nat.bit b r := by omega
    have he := Nat.sub_add_cancel hd
    rw [qstep,rstep,if_neg ht,decide_eq_false ht]
    simp only [Bool.not_false,Nat.bit_val,Bool.toNat_true] at *
    nlinarith

 theorem step_remainder (b : Bool) (d r : ℕ) (_ : 0<d) (hr : r<d) : rstep b d r<d := by
  have hb : b.toNat≤1 := by cases b <;> decide
  unfold rstep
  split_ifs with ht
  · exact ht
  · simp only [Nat.bit_val] at *
    omega

 def eval : List Bool → ℕ → ℕ → ℕ → ℕ × ℕ
  | [],_,q,r => (q,r)
  | b::xs,d,q,r => eval xs d (qstep b d q r) (rstep b d r)

 theorem eval_spec (xs : List Bool) (d q r : ℕ) (hd : 0<d) (hr : r<d) :
    (eval xs d q r).2<d ∧
      (eval xs d q r).1*d+(eval xs d q r).2=2^xs.length*(q*d+r)+Word.value xs.reverse := by
  induction xs generalizing q r with
  | nil => exact ⟨hr,by simp [eval]⟩
  | cons b xs ih =>
      obtain ⟨hrem,heq⟩ := ih (qstep b d q r) (rstep b d r) (step_remainder b d r hd hr)
      refine ⟨hrem,?_⟩
      change (eval xs d (qstep b d q r) (rstep b d r)).1*d+
        (eval xs d (qstep b d q r) (rstep b d r)).2=_
      rw [heq,step_total]
      simp only [List.length_cons,List.reverse_cons,Word.value_append,Word.value_cons,Word.value_nil,
        Nat.mul_zero,Nat.add_zero,List.length_reverse,pow_succ]
      ring

abbrev S := List Bool × (ℕ × (ℕ × ℕ))
abbrev eqr : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
abbrev edqr : ℕ × (ℕ × ℕ) → List Bool := encodePair Nat.bits eqr
abbrev enc : S → List Bool := encodePair id edqr
 def next (s : S) : S :=
  (s.1.tail,(s.2.1,(qstep (s.1.head?.getD false) s.2.1 s.2.2.1 s.2.2.2,
    rstep (s.1.head?.getD false) s.2.1 s.2.2.2)))
 def body (s : S) : (ℕ × ℕ) ⊕ S := if s.1.isEmpty then .inl s.2.2 else .inr (next s)
 def result (s : S) : ℕ × ℕ := eval s.1 s.2.1 s.2.2.1 s.2.2.2
 def potential (s : S) : ℕ := s.1.length+max s.2.2.1.bits.length s.2.2.2.bits.length

 theorem enc_length (s : S) :
    (enc s).length=2*s.1.length+2*s.2.1.bits.length+2*s.2.2.1.bits.length+s.2.2.2.bits.length+3 := by
  simp only [enc,edqr,eqr,encodePair_length,id_eq]
  omega

 theorem total_le_length (s : S) : potential s+s.2.1.bits.length≤(enc s).length := by
  simp only [potential,enc_length]
  omega

 theorem length_le_total (s : S) : (enc s).length≤3*(potential s+s.2.1.bits.length)+3 := by
  simp only [potential,enc_length]
  omega

 theorem next_potential (s : S) (h : s.1.isEmpty=false) : potential (next s)≤potential s := by
  have hx : s.1.tail.length<s.1.length := by
    cases hh : s.1 with
    | nil => simp only [hh,List.isEmpty_nil] at h; contradiction
    | cons b xs => simp only [List.tail_cons,List.length_cons]; omega
  have hq := NatBinary.bit_length (!decide (Nat.bit (s.1.head?.getD false) s.2.2.2<s.2.1)) s.2.2.1
  have hr := NatBinary.bit_length (s.1.head?.getD false) s.2.2.2
  have hrle : rstep (s.1.head?.getD false) s.2.1 s.2.2.2≤Nat.bit (s.1.head?.getD false) s.2.2.2 := by
    unfold rstep
    split_ifs <;> omega
  have hrl := (NatBinary.length_mono hrle).trans hr
  simp only [potential,next,qstep]
  omega

 theorem next_result (s : S) (h : s.1.isEmpty=false) : result (next s)=result s := by
  rcases s with ⟨xs,d,q,r⟩
  cases xs with
  | nil => contradiction
  | cons b xs => rfl

noncomputable def program : PolyProgram enc (encodeLoop enc eqr) body := by
  let px := PolyProgram.fst id edqr
  let pdqr := PolyProgram.snd id edqr
  let pd := pdqr.comp (PolyProgram.fst Nat.bits eqr)
  let pqr := pdqr.comp (PolyProgram.snd Nat.bits eqr)
  let pq := pqr.comp (PolyProgram.fst Nat.bits Nat.bits)
  let pr := pqr.comp (PolyProgram.snd Nat.bits Nat.bits)
  let pb := px.comp PolyProgram.head
  let pt := (pb.fanout pr).comp PolyProgram.natBit
  let plt := (pt.fanout pd).comp PolyProgram.natLT
  let nq := ((plt.comp PolyProgram.boolNot).fanout pq).comp PolyProgram.natBit
  let nr := PolyProgram.ite plt ((pt.fanout pd).comp PolyProgram.natSub) pt
  let pn := (px.comp PolyProgram.tail).fanout (pd.fanout (nq.fanout nr))
  exact (PolyProgram.ite (px.comp PolyProgram.isEmpty)
    (pn.comp (PolyProgram.injectRight enc eqr))
    (pqr.comp (PolyProgram.injectLeft enc eqr))).congr _ (fun s => by
      simp only [Function.comp_apply,body,next,qstep,rstep,decide_eq_true_eq])

 theorem run (xs : List Bool) (d q r S : ℕ) (hs : 3*(potential (xs,d,q,r)+d.bits.length)+3≤S) :
    BoundedRun enc body S (xs.length+1) (xs,d,q,r) (result (xs,d,q,r)) := by
  induction xs generalizing q r with
  | nil =>
      exact BoundedRun.stop ((length_le_total ([],d,q,r)).trans hs) rfl
  | cons b xs ih =>
      let s : DivisionLoop.S := (b::xs,d,q,r)
      have hp := next_potential s rfl
      change 3*(potential s+d.bits.length)+3≤S at hs
      have hnext : 3*(potential (next s)+d.bits.length)+3≤S := by omega
      have hr := ih (qstep b d q r) (rstep b d r) hnext
      have hh : result (xs,d,qstep b d q r,rstep b d r)=result s := rfl
      rw [hh] at hr
      exact BoundedRun.step ((length_le_total s).trans hs) rfl hr

noncomputable def loop : PolyProgram enc eqr result :=
  program.loop result (X+1) (3*X+3) (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · simp only [Polynomial.eval_add,eval_X,eval_one,enc_length]; omega
    · have hs := total_le_length s
      simpa only [Polynomial.eval_add,eval_mul,eval_ofNat,eval_X] using
        run s.1 s.2.1 s.2.2.1 s.2.2.2 (3*(enc s).length+3) (by
          change 3*(potential s+s.2.1.bits.length)+3≤3*(enc s).length+3
          omega))
end DivisionLoop

namespace PolyProgram
noncomputable def natDivMod : PolyProgram (encodePair Nat.bits Nat.bits) (encodePair Nat.bits Nat.bits)
    (fun x : ℕ × ℕ => (x.1/x.2,x.1%x.2)) := by
  let ex : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
  let px := fst Nat.bits Nat.bits
  let pd := snd Nat.bits Nat.bits
  let rev : PolyProgram Nat.bits id (fun n => n.bits.reverse) := reverse.recode Nat.bits (fun _ => rfl) (fun _ => rfl)
  let init := (px.comp rev).fanout (pd.fanout (constant ex DivisionLoop.eqr (0,0)))
  let normal := init.comp DivisionLoop.loop
  let zeroCase := (constant ex Nat.bits 0).fanout px
  refine (ite (pd.comp natZero) normal zeroCase).congr _ ?_
  intro x
  change (if decide (x.2=0) then (0,x.1) else DivisionLoop.eval x.1.bits.reverse x.2 0 0)=_
  by_cases hd : x.2=0
  · simp only [hd,decide_true,ite_true,Nat.div_zero,Nat.mod_zero]
  · simp only [decide_eq_false hd,Bool.false_eq_true,ite_false]
    obtain ⟨hr,he⟩ := DivisionLoop.eval_spec x.1.bits.reverse x.2 0 0 (Nat.pos_of_ne_zero hd) (Nat.pos_of_ne_zero hd)
    simp only [zero_mul,zero_add,mul_zero,zero_add,List.reverse_reverse,Word.value_bits] at he
    have hp : x.1/x.2=(DivisionLoop.eval x.1.bits.reverse x.2 0 0).1 ∧
        x.1%x.2=(DivisionLoop.eval x.1.bits.reverse x.2 0 0).2 :=
      (Nat.div_mod_unique (Nat.pos_of_ne_zero hd)).mpr ⟨by
        simpa only [Nat.mul_comm,Nat.add_comm] using he,hr⟩
    exact Prod.ext hp.1.symm hp.2.symm

noncomputable def natDiv : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1/x.2) :=
  (natDivMod.comp (fst Nat.bits Nat.bits)).congr _ (fun _ => rfl)
noncomputable def natMod : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1%x.2) :=
  (natDivMod.comp (snd Nat.bits Nat.bits)).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryGCD

namespace OAI


                                 
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace NatBinary
 theorem mod_length_lt {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) : (a%b).bits.length < a.bits.length := by
  have ha : 0 < a := hb.trans_le hba
  by_cases hz : a%b=0
  · rw [hz,Nat.zero_bits,List.length_nil]
    apply List.length_pos_iff.mpr
    intro h
    have := (zero_iff a).mp h
    omega
  · have hr := Nat.mod_lt a hb
    have he := Nat.mod_add_div a b
    have hq : 1 ≤ a/b := (Nat.le_div_iff_mul_le hb).mpr (by simpa only [one_mul] using hba)
    have hm : b ≤ b*(a/b) := by nlinarith
    have hsmall : 2*(a%b) < a := by omega
    have hlen := length_mono hsmall.le
    have hbit : (2*(a%b)).bits.length=(a%b).bits.length+1 := by
      have hn : Nat.bit false (a%b) ≠ 0 := by
        simp only [Nat.bit_val,Bool.toNat_false,Nat.add_zero]
        omega
      simpa only [Nat.size_eq_bits_len,Nat.bit_val,Bool.toNat_false,Nat.add_zero,Nat.succ_eq_add_one]
        using Nat.size_bit hn
    omega
end NatBinary

namespace GCDLoop
abbrev S := ℕ × ℕ
abbrev enc : S → List Bool := encodePair Nat.bits Nat.bits
 def next (s : S) : S := (s.2,s.1%s.2)
 def body (s : S) : ℕ ⊕ S := if s.2=0 then .inl s.1 else .inr (next s)
 def result (s : S) : ℕ := s.1.gcd s.2
 def potential (s : S) : ℕ := s.1.bits.length+s.2.bits.length

 theorem enc_length (s : S) : (enc s).length=2*s.1.bits.length+1+s.2.bits.length := by
  exact encodePair_length _ _ _
 theorem length_le_potential (s : S) : (enc s).length ≤ 2*potential s+1 := by
  simp only [enc_length,potential]; omega
 theorem potential_le_length (s : S) : potential s ≤ (enc s).length := by
  simp only [enc_length,potential]; omega

 theorem next_result (s : S) : result (next s)=result s := by
  simp only [result,next]
  calc s.2.gcd (s.1%s.2)=(s.1%s.2).gcd s.2 := Nat.gcd_comm _ _
    _=s.2.gcd s.1 := (Nat.gcd_rec _ _).symm
    _=s.1.gcd s.2 := Nat.gcd_comm _ _

 theorem next_potential (s : S) : potential (next s) ≤ potential s := by
  have hm := NatBinary.length_mono (Nat.mod_le s.1 s.2)
  simp only [potential,next]
  omega

 theorem next_potential_lt (s : S) (ho : s.2 ≤ s.1) (hb : s.2 ≠ 0) : potential (next s) < potential s := by
  have h := NatBinary.mod_length_lt (Nat.pos_of_ne_zero hb) ho
  simp only [potential,next]
  omega

noncomputable def program : PolyProgram enc (encodeLoop enc Nat.bits) body := by
  let px := PolyProgram.fst Nat.bits Nat.bits
  let py := PolyProgram.snd Nat.bits Nat.bits
  let pn := py.fanout PolyProgram.natMod
  exact (PolyProgram.ite (py.comp PolyProgram.natZero)
    (pn.comp (PolyProgram.injectRight enc Nat.bits))
    (px.comp (PolyProgram.injectLeft enc Nat.bits))).congr _ (fun _ => by
      simp only [Function.comp_apply,body,next,decide_eq_true_eq])

 theorem run_ordered (L : ℕ) : ∀ (s : S) (S : ℕ), potential s=L →
    s.2 ≤ s.1 → 2*L+1 ≤ S → ∃ n ≤ L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL ho hs
      have hsize : (enc s).length ≤ S := (length_le_potential s).trans (by omega)
      by_cases hz : s.2=0
      · refine ⟨1,by omega,BoundedRun.stop hsize ?_⟩
        simp only [body,hz,ite_true,result,Nat.gcd_zero_right]
      · have hpot : potential (next s) < L := by simpa only [hL] using next_potential_lt s ho hz
        have horder : (next s).2 ≤ (next s).1 := (Nat.mod_lt s.1 (Nat.pos_of_ne_zero hz)).le
        obtain ⟨n,hn,hr⟩ := ih _ hpot (next s) S rfl horder (by omega)
        refine ⟨n+1,by omega,?_⟩
        rw [next_result] at hr
        exact BoundedRun.step hsize (by simp only [body,hz,ite_false]) hr

 theorem run (s : S) (S : ℕ) (hs : 2*potential s+1 ≤ S) :
    ∃ n ≤ potential s+2, BoundedRun enc body S n s (result s) := by
  by_cases ho : s.2 ≤ s.1
  · obtain ⟨n,hn,hr⟩ := run_ordered (potential s) s S rfl ho hs
    exact ⟨n,by omega,hr⟩
  · have hb : s.2 ≠ 0 := by omega
    have hn := next_potential s
    have horder : (next s).2 ≤ (next s).1 := (Nat.mod_lt s.1 (Nat.pos_of_ne_zero hb)).le
    obtain ⟨n,hbound,hr⟩ := run_ordered (potential (next s)) (next s) S rfl horder (by omega)
    refine ⟨n+1,by omega,?_⟩
    rw [next_result] at hr
    exact BoundedRun.step ((length_le_potential s).trans hs)
      (by simp only [body,hb,ite_false]) hr

noncomputable def loop : PolyProgram enc Nat.bits result :=
  program.loop result (X+2) (2*X+1) (fun s => by
    have hs := potential_le_length s
    obtain ⟨n,hn,hr⟩ := run s (2*(enc s).length+1) (by omega)
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_ofNat]; omega
    · simpa only [eval_add,eval_mul,eval_ofNat,eval_one,eval_X] using hr)
end GCDLoop

namespace PolyProgram
noncomputable def natGcd : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1.gcd x.2) :=
  GCDLoop.loop
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryMultiplication

namespace OAI


                                            
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace MultiplicationLoop
abbrev S := ℕ × (ℕ × ℕ)
abbrev ey : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
abbrev enc : S → List Bool := encodePair Nat.bits ey
 def next (s : S) : S := (s.1.div2,(Nat.bit false s.2.1,if s.1.bodd then s.2.2+s.2.1 else s.2.2))
 def body (s : S) : ℕ ⊕ S := if s.1=0 then .inl s.2.2 else .inr (next s)
 def result (s : S) : ℕ := s.1*s.2.1+s.2.2
 def potential (s : S) : ℕ := s.1.bits.length+max s.2.1.bits.length s.2.2.bits.length

 theorem enc_length (s : S) : (enc s).length=2*s.1.bits.length+2*s.2.1.bits.length+s.2.2.bits.length+2 := by
  simp only [enc,ey,encodePair_length]
  omega

 theorem potential_le_length (s : S) : potential s≤(enc s).length := by
  simp only [potential,enc_length]
  omega

 theorem length_le_potential (s : S) : (enc s).length≤3*potential s+2 := by
  simp only [potential,enc_length]
  omega

 theorem next_potential (s : S) (h : s.1≠0) : potential (next s)≤potential s := by
  have hx := NatBinary.half_lt_length h
  have hy := NatBinary.bit_length false s.2.1
  have ha := NatBinary.add_length s.2.2 s.2.1
  simp only [potential,next]
  cases s.1.bodd <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

 theorem next_result (s : S) : result (next s)=result s := by
  have h := Nat.bodd_add_div2 s.1
  simp only [result,next,Nat.bit_val,Bool.toNat_false,Nat.add_zero]
  cases he : s.1.bodd
  · simp only [he,Bool.toNat_false,zero_add] at h
    simp only [Bool.false_eq_true,ite_false]
    nlinarith only [congrArg (fun n => n*s.2.1) h]
  · simp only [he,Bool.toNat_true] at h
    simp only [ite_true]
    nlinarith only [congrArg (fun n => n*s.2.1) h]

noncomputable def program : PolyProgram enc (encodeLoop enc Nat.bits) body := by
  let px := PolyProgram.fst Nat.bits ey
  let pyz := PolyProgram.snd Nat.bits ey
  let py := pyz.comp (PolyProgram.fst Nat.bits Nat.bits)
  let pa := pyz.comp (PolyProgram.snd Nat.bits Nat.bits)
  let half := px.comp PolyProgram.natHalf
  let twice := ((PolyProgram.constant enc encodeBool false).fanout py).comp PolyProgram.natBit
  let acc := PolyProgram.ite (px.comp PolyProgram.natOdd) pa ((pa.fanout py).comp PolyProgram.natAdd)
  let pn := half.fanout (twice.fanout acc)
  exact (PolyProgram.ite (px.comp PolyProgram.natZero)
    (pn.comp (PolyProgram.injectRight enc Nat.bits))
    (pa.comp (PolyProgram.injectLeft enc Nat.bits))).congr _ (fun s => by
      simp only [Function.comp_apply,body,decide_eq_true_eq]
      rfl)

 theorem run (L : ℕ) : ∀ (s : S) (S : ℕ), s.1.bits.length=L → 3*potential s+2≤S →
    ∃ n≤L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL hs
      have hsize := (length_le_potential s).trans hs
      by_cases hz : s.1=0
      · refine ⟨1,by omega,BoundedRun.stop hsize ?_⟩
        simp only [body,hz,ite_true,result,zero_mul,zero_add]
      · have hl : (next s).1.bits.length<L := by simpa only [next,hL] using NatBinary.half_lt_length hz
        have hb : 3*potential (next s)+2≤S := by have := next_potential s hz; omega
        obtain ⟨n,hn,hr⟩ := ih _ hl (next s) S rfl hb
        refine ⟨n+1,by omega,?_⟩
        rw [next_result] at hr
        exact BoundedRun.step hsize (by simp only [body,hz,ite_false]) hr

noncomputable def loop : PolyProgram enc Nat.bits result :=
  program.loop result (X+1) (3*X+2) (fun s => by
    obtain ⟨n,hn,hr⟩ := run s.1.bits.length s (3*(enc s).length+2) rfl (by
      have := potential_le_length s; omega)
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc_length]; omega
    · simpa only [eval_add,eval_mul,eval_ofNat,eval_X] using hr)
end MultiplicationLoop

namespace PolyProgram
noncomputable def natMul : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1*x.2) := by
  let ex : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
  let init := (fst Nat.bits Nat.bits).fanout ((snd Nat.bits Nat.bits).fanout (constant ex Nat.bits 0))
  exact (init.comp MultiplicationLoop.loop).congr _ (fun x => by
    simp only [Function.comp_apply,MultiplicationLoop.result,Nat.add_zero])
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryInteger

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Signed
 def value (s : Bool) (n : ℕ) : ℤ := if s then -(n:ℤ) else n
 def sign (z : ℤ) : Bool := decide (z < 0)
 def parts (z : ℤ) : Bool × ℕ := (sign z,z.natAbs)
 def encode (z : ℤ) : List Bool := encodePair encodeBool Nat.bits (parts z)

 theorem abs_value (s : Bool) (n : ℕ) : (value s n).natAbs=n := by cases s <;> simp [value]
 theorem sign_value (s : Bool) (n : ℕ) : sign (value s n)=(s && !decide (n=0)) := by
  cases s <;> by_cases hn : n=0
  all_goals simp only [value,sign,Bool.false_eq_true,ite_false,ite_true]
  all_goals simp [hn, Nat.pos_of_ne_zero]

 theorem value_parts (z : ℤ) : value (sign z) z.natAbs=z := by
  unfold value sign
  split_ifs with h
  · exact (Int.eq_neg_natAbs_of_nonpos (le_of_lt (of_decide_eq_true h))).symm
  · exact Int.natAbs_of_nonneg (by simpa using h)

 theorem value_neg (s : Bool) (n : ℕ) : value (!s) n= -value s n := by
  cases s <;> simp [value]

 theorem value_mul (s t : Bool) (n m : ℕ) : value (xor s t) (n*m)=value s n*value t m := by
  cases s <;> cases t <;> simp [value]

 def add (s t : Bool) (n m : ℕ) : ℤ :=
  if s=t then value s (n+m) else if n < m then value t (m-n) else value s (n-m)

 theorem value_add (s t : Bool) (n m : ℕ) : add s t n m=value s n+value t m := by
  cases s <;> cases t <;> by_cases h : n < m <;> simp [add,value,h] <;> omega

 theorem value_div (s : Bool) (n d : ℕ) (h : d∣n) : value s (n/d)=value s n/(d:ℤ) := by
  have hd : (d:ℤ)∣(n:ℤ) := Int.natCast_dvd_natCast.mpr h
  cases s <;> simp only [value,Bool.false_eq_true,ite_false,ite_true,Int.neg_ediv_of_dvd hd,Int.ofNat_ediv_ofNat]
end Signed

namespace PolyProgram
abbrev signedParts : Bool × ℕ → List Bool := encodePair encodeBool Nat.bits

noncomputable def intFromParts : PolyProgram signedParts Signed.encode (fun x => Signed.value x.1 x.2) := by
  let ps := fst encodeBool Nat.bits
  let pn := snd encodeBool Nat.bits
  let s := (ps.fanout ((pn.comp natZero).comp boolNot)).comp boolAnd
  exact (s.fanout pn).recode id (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,id_eq,Signed.encode,Signed.parts,Signed.sign_value,Signed.abs_value])

noncomputable def intSign : PolyProgram Signed.encode encodeBool Signed.sign :=
  (fst encodeBool Nat.bits).recode Signed.parts (fun _ => rfl) (fun _ => rfl)
noncomputable def intAbs : PolyProgram Signed.encode Nat.bits Int.natAbs :=
  (snd encodeBool Nat.bits).recode Signed.parts (fun _ => rfl) (fun _ => rfl)

noncomputable def intNeg : PolyProgram Signed.encode Signed.encode Neg.neg :=
  (((intSign.comp boolNot).fanout intAbs).comp intFromParts).congr _ (fun z => by
    simp only [Function.comp_apply,Signed.value_neg,Signed.value_parts])

noncomputable def intOfNat : PolyProgram Nat.bits Signed.encode Nat.cast :=
  (((constant Nat.bits encodeBool false).fanout (identity Nat.bits)).comp intFromParts).congr _ (fun _ => rfl)

noncomputable def boolXor : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => xor x.1 x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)
noncomputable def boolEq : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => decide (x.1=x.2)) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)

noncomputable def intMul : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1*x.2) := by
  let px := fst Signed.encode Signed.encode
  let py := snd Signed.encode Signed.encode
  let s := ((px.comp intSign).fanout (py.comp intSign)).comp boolXor
  let n := ((px.comp intAbs).fanout (py.comp intAbs)).comp natMul
  exact ((s.fanout n).comp intFromParts).congr _ (fun x => by
    simp only [Function.comp_apply,Signed.value_mul,Signed.value_parts])

noncomputable def intAdd : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1+x.2) := by
  let px := fst Signed.encode Signed.encode
  let py := snd Signed.encode Signed.encode
  let sx := px.comp intSign
  let sy := py.comp intSign
  let nx := px.comp intAbs
  let ny := py.comp intAbs
  let plus := ((sx.fanout ((nx.fanout ny).comp natAdd)).comp intFromParts)
  let minusX := (sx.fanout ((nx.fanout ny).comp natSub)).comp intFromParts
  let minusY := (sy.fanout ((ny.fanout nx).comp natSub)).comp intFromParts
  let minus := ite ((nx.fanout ny).comp natLT) minusX minusY
  refine (ite ((sx.fanout sy).comp boolEq) minus plus).congr _ ?_
  intro x
  simpa only [Function.comp_apply, decide_eq_true_eq, Signed.add, Signed.value_parts]
    using Signed.value_add (Signed.sign x.1) (Signed.sign x.2) x.1.natAbs x.2.natAbs

noncomputable def intSub : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1-x.2) :=
  ((intNeg.second Signed.encode).comp intAdd).congr _ (fun x => (sub_eq_add_neg x.1 x.2).symm)
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryRational

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Ratio
 def parts (q : ℚ) : ℤ × ℕ := (q.num,q.den)
 def encode (q : ℚ) : List Bool := encodePair Signed.encode Nat.bits (parts q)
 def normalized (x : ℤ × ℕ) : ℤ × ℕ :=
  if x.2=0 then (0,1) else
    (Signed.value (Signed.sign x.1) (x.1.natAbs / x.2.gcd x.1.natAbs),x.2 / x.2.gcd x.1.natAbs)
 theorem normalized_eq (x : ℤ × ℕ) : normalized x=parts (mkRat x.1 x.2) := by
  simp only [normalized,parts,Rat.num_mkRat,Rat.den_mkRat]
  split_ifs with h
  · rfl
  · rw [Signed.value_div _ _ _ (Nat.gcd_dvd_right _ _),Signed.value_parts]

 theorem inv_eq (q : ℚ) : q⁻¹=mkRat (Signed.value (Signed.sign q.num) q.den) q.num.natAbs := by
  rw [Rat.mkRat_eq_div]
  calc
    q⁻¹ = ((q.num:ℚ)/q.den)⁻¹ := congrArg Inv.inv q.num_div_den.symm
    _ = (q.den:ℚ)/q.num := inv_div _ _
    _ = _ := by
      have hnum := Signed.value_parts q.num
      unfold Signed.value at hnum ⊢
      split_ifs with hn
      · rw [if_pos hn] at hnum
        have haZ : (q.num.natAbs:ℤ) = -q.num := by omega
        have ha : (q.num.natAbs:ℚ) = -(q.num:ℚ) := by simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun z : ℤ => (z:ℚ)) haZ
        rw [Int.cast_neg,Int.cast_natCast,ha,neg_div_neg_eq]
      · rw [if_neg hn] at hnum
        have ha : (q.num.natAbs:ℚ) = (q.num:ℚ) := by simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ)) hnum
        rw [Int.cast_natCast,ha]
end Ratio

namespace PolyProgram
noncomputable def intLT : PolyProgram (encodePair Signed.encode Signed.encode) encodeBool (fun x : ℤ × ℤ => decide (x.1 < x.2)) :=
  (intSub.comp intSign).congr _ (fun _ => by simp only [Function.comp_apply,Signed.sign,sub_neg])
noncomputable def intEQ : PolyProgram (encodePair Signed.encode Signed.encode) encodeBool (fun x : ℤ × ℤ => decide (x.1=x.2)) :=
  ((intSub.comp intAbs).comp natZero).congr _ (fun _ => by simp only [Function.comp_apply,Int.natAbs_eq_zero,sub_eq_zero])

noncomputable def mkRational : PolyProgram (encodePair Signed.encode Nat.bits) Ratio.encode (fun x => mkRat x.1 x.2) := by
  let pn := fst Signed.encode Nat.bits
  let pd := snd Signed.encode Nat.bits
  let pa := pn.comp intAbs
  let pg := (pd.fanout pa).comp natGcd
  let nm := (((pn.comp intSign).fanout ((pa.fanout pg).comp natDiv)).comp intFromParts)
  let dm := (pd.fanout pg).comp natDiv
  let normal := ite (pd.comp natZero) (nm.fanout dm)
    (constant (encodePair Signed.encode Nat.bits) (encodePair Signed.encode Nat.bits) (0,1))
  refine normal.recode id (fun _ => rfl) ?_
  intro x
  simp only [Function.comp_apply,id_eq,decide_eq_true_eq]
  change encodePair Signed.encode Nat.bits (Ratio.normalized x)=Ratio.encode (mkRat x.1 x.2)
  rw [Ratio.normalized_eq]
  rfl

noncomputable def ratNum : PolyProgram Ratio.encode Signed.encode Rat.num :=
  (fst Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)
noncomputable def ratDen : PolyProgram Ratio.encode Nat.bits Rat.den :=
  (snd Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)
noncomputable def ratNeg : PolyProgram Ratio.encode Ratio.encode Neg.neg := by
  refine (((ratNum.comp intNeg).fanout ratDen)).recode id (fun _ => rfl) ?_
  intro q
  simp only [Function.comp_apply,id_eq,Ratio.encode,Ratio.parts,Rat.num_neg_eq_neg_num,Rat.den_neg_eq_den]
noncomputable def ratOfInt : PolyProgram Signed.encode Ratio.encode Int.cast :=
  (((identity Signed.encode).fanout (constant Signed.encode Nat.bits 1)).comp mkRational).congr _ (fun z => by simp [Rat.mkRat_eq_div])
noncomputable def ratOfNat : PolyProgram Nat.bits Ratio.encode Nat.cast :=
  (intOfNat.comp ratOfInt).congr _ (fun n => by simp)
noncomputable def ratMul : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1*x.2) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let pn := ((px.comp ratNum).fanout (py.comp ratNum)).comp intMul
  let pd := ((px.comp ratDen).fanout (py.comp ratDen)).comp natMul
  exact ((pn.fanout pd).comp mkRational).congr _ (fun x => (Rat.mul_def' x.1 x.2).symm)
noncomputable def ratAdd : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1+x.2) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let pnx := ((px.comp ratNum).fanout ((py.comp ratDen).comp intOfNat)).comp intMul
  let pny := ((py.comp ratNum).fanout ((px.comp ratDen).comp intOfNat)).comp intMul
  let pn := (pnx.fanout pny).comp intAdd
  let pd := ((px.comp ratDen).fanout (py.comp ratDen)).comp natMul
  exact ((pn.fanout pd).comp mkRational).congr _ (fun x => (Rat.add_def' x.1 x.2).symm)
noncomputable def ratSub : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1-x.2) :=
  ((ratNeg.second Ratio.encode).comp ratAdd).congr _ (fun x => (sub_eq_add_neg x.1 x.2).symm)
noncomputable def ratInv : PolyProgram Ratio.encode Ratio.encode Inv.inv :=
  (((((ratNum.comp intSign).fanout ratDen).comp intFromParts).fanout (ratNum.comp intAbs)).comp mkRational).congr _ (fun q => (Ratio.inv_eq q).symm)
noncomputable def ratDiv : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1/x.2) :=
  ((ratInv.second Ratio.encode).comp ratMul).congr _ (fun x => (div_eq_mul_inv x.1 x.2).symm)
noncomputable def ratLT : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1 < x.2)) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let lhs := ((px.comp ratNum).fanout ((py.comp ratDen).comp intOfNat)).comp intMul
  let rhs := ((py.comp ratNum).fanout ((px.comp ratDen).comp intOfNat)).comp intMul
  refine ((lhs.fanout rhs).comp intLT).congr _ ?_
  intro x
  simp only [Function.comp_apply]
  simp only [← Rat.lt_iff]
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Compression.CircuitBitBound

-- Exact source lemma extracted from openai/math; unrelated Gaussian kernel declarations omitted.
namespace OAI.MetricKMedian.Gaussian

theorem ratio_num_den_bound (a b : ℤ) (hb : b ≠ 0) (H : ℤ)
    (ha : |a| ≤ H) (hbH : |b| ≤ H) :
    |((a:ℚ)/(b:ℚ)).num| ≤ H ∧ (((a:ℚ)/(b:ℚ)).den:ℤ) ≤ H := by
  let q := (a:ℚ)/(b:ℚ)
  obtain ⟨c,hcA,hcB⟩ := Rat.num_den_mk hb (q := q) (by exact (Rat.divInt_eq_div a b).symm)
  have hc : c ≠ 0 := by intro hz; rw [hz,zero_mul] at hcB; exact hb hcB
  have hc1 : (1:ℤ) ≤ |c| := by
    have ha := abs_pos.mpr hc
    omega
  have hnum : |q.num| ≤ |a| := by
    rw [hcA,abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (abs_nonneg q.num)
  have hden : (q.den:ℤ) ≤ |b| := by
    rw [hcB,abs_mul,abs_of_nonneg (by positivity : (0:ℤ) ≤ q.den)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (Int.natCast_nonneg q.den)
  exact ⟨hnum.trans ha,hden.trans hbH⟩

end OAI.MetricKMedian.Gaussian


-- Source module: OAI.Combinatorics.KMedian.Compression.RationalOperationHeight

namespace OAI


                                               
section
namespace MetricKMedian.Binary
open Finset

def HasHeight (q : ℚ) (L : ℕ) : Prop := |q.num| ≤ (2:ℤ)^L ∧ (q.den:ℤ) ≤ (2:ℤ)^L

namespace HasHeight
variable {q r : ℚ} {L M : ℕ}

 theorem mono (h : HasHeight q L) (hLM : L≤M) : HasHeight q M :=
  ⟨h.1.trans (pow_le_pow_right₀ (by norm_num) hLM),h.2.trans (pow_le_pow_right₀ (by norm_num) hLM)⟩

 theorem zero (L : ℕ) : HasHeight 0 L := by
  constructor
  · simp
  · simp only [Rat.den_zero,Int.natCast_one]
    exact one_le_pow₀ (by norm_num)

 theorem one (L : ℕ) : HasHeight 1 L := by
  constructor <;> simp only [Rat.num_one,Rat.den_one,abs_one,Int.natCast_one] <;>
    exact one_le_pow₀ (by norm_num)

 theorem neg (h : HasHeight q L) : HasHeight (-q) L := by
  simpa only [HasHeight,Rat.num_neg_eq_neg_num,Rat.den_neg_eq_den,abs_neg] using h

 theorem mul (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q*r) (L+M) := by
  have hdq : (q.den:ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hdr : (r.den:ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hh := Gaussian.ratio_num_den_bound (q.num*r.num) ((q.den:ℤ)*r.den) (mul_ne_zero hdq hdr)
    ((2:ℤ)^(L+M)) (by
      rw [abs_mul,pow_add]
      exact mul_le_mul hq.1 hr.1 (abs_nonneg _) (by positivity)) (by
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _),pow_add]
      exact mul_le_mul hq.2 hr.2 (by positivity) (by positivity))
  have he : ((q.num*r.num:ℤ):ℚ)/(((q.den:ℤ)*r.den:ℤ):ℚ)=q*r := by
    push_cast
    rw [mul_div_mul_comm,Rat.num_div_den,Rat.num_div_den]
  rwa [he] at hh

 theorem inv (hq : HasHeight q L) : HasHeight q⁻¹ L := by
  by_cases hq0 : q=0
  · rw [hq0,inv_zero]
    exact zero L
  have hqn : q.num ≠ 0 := by
    intro h
    apply hq0
    rw [← Rat.num_div_den q,h,Int.cast_zero,zero_div]
  have hh := Gaussian.ratio_num_den_bound (q.den:ℤ) q.num hqn ((2:ℤ)^L)
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using hq.2) hq.1
  have he : ((q.den:ℤ):ℚ)/(q.num:ℚ)=q⁻¹ := by
    conv_rhs => rw [← Rat.num_div_den q]
    simp only [inv_div,Int.cast_natCast]
  rwa [he] at hh

 theorem div (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q/r) (L+M) := by
  simpa only [div_eq_mul_inv] using hq.mul hr.inv

 theorem add (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q+r) (L+M+1) := by
  have hdq : (q.den:ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hdr : (r.den:ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hterm₁ : |q.num*(r.den:ℤ)| ≤ (2:ℤ)^(L+M) := by
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),pow_add]
    exact mul_le_mul hq.1 hr.2 (by positivity) (by positivity)
  have hterm₂ : |r.num*(q.den:ℤ)| ≤ (2:ℤ)^(L+M) := by
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),Nat.add_comm L M,pow_add]
    exact mul_le_mul hr.1 hq.2 (by positivity) (by positivity)
  have hh := Gaussian.ratio_num_den_bound (q.num*r.den+r.num*q.den) ((q.den:ℤ)*r.den)
    (mul_ne_zero hdq hdr) ((2:ℤ)^(L+M+1)) (by
      have hab := abs_add_le (q.num*(r.den:ℤ)) (r.num*(q.den:ℤ))
      rw [pow_succ]
      linarith) (by
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _)]
      have hb : (q.den:ℤ)*r.den ≤ (2:ℤ)^(L+M) := by
        rw [pow_add]
        exact mul_le_mul hq.2 hr.2 (by positivity) (by positivity)
      exact hb.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
  have he : ((q.num*r.den+r.num*q.den:ℤ):ℚ)/(((q.den:ℤ)*r.den:ℤ):ℚ)=q+r := by
    push_cast
    rw [add_div, mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr r.den_ne_zero),
      mul_comm (r.num:ℚ) (q.den:ℚ),mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr q.den_ne_zero),
      Rat.num_div_den,Rat.num_div_den]
  rwa [he] at hh

 theorem sub (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q-r) (L+M+1) := by
  simpa only [sub_eq_add_neg] using hq.add hr.neg

 theorem sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i∈s, HasHeight (f i) L) :
    HasHeight (∑ i∈s, f i) (s.card*(L+1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty,card_empty,zero_mul] using zero 0
  | @insert a s ha ih =>
      rw [sum_insert ha,card_insert_of_notMem ha]
      have hs := ih (fun i hi => h i (mem_insert_of_mem hi))
      have hh := (h a (mem_insert_self _ _)).add hs
      convert hh using 1
      ring

 theorem partialSum {n : ℕ} (f : Fin n → ℚ) (s : Finset (Fin n))
    (h : ∀ i, HasHeight (f i) L) : HasHeight (∑ i∈s, f i) (n*(L+1)) := by
  have hh := sum s f (fun i _ => h i)
  apply hh.mono
  exact Nat.mul_le_mul_right _ ((card_le_card (subset_univ s)).trans_eq (card_fin n))

end HasHeight
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryRationalHeight

namespace OAI


                                            
section
namespace MetricKMedian.Binary
open Polynomial
namespace NatBinary
 theorem length_le_height {n L : ℕ} (h : n ≤ 2^L) : n.bits.length ≤ L+1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hp : 0<2^L := pow_pos (by decide) _
  rw [pow_succ]
  omega
 theorem le_two_pow_length (n : ℕ) : n ≤ 2^n.bits.length := by
  simpa only [Nat.size_eq_bits_len] using (Nat.lt_size_self n).le
end NatBinary

namespace Signed
 theorem encode_length (z : ℤ) : (encode z).length=3+z.natAbs.bits.length := by
  simp only [encode,parts,encodePair_length,encodeBool,List.length_singleton]

 theorem encode_injective : Function.Injective encode := by
  intro a b h
  have hh := encodePair_injective encodeBool_injective (fun n m he => by
    have hg := congrArg Word.value he
    simpa only [Word.value_bits] using hg) h
  have hx := congrArg (fun x : Bool × ℕ => value x.1 x.2) hh
  simpa only [parts,value_parts] using hx
end Signed
namespace Ratio
 theorem encode_length (q : ℚ) : (encode q).length=7+2*q.num.natAbs.bits.length+q.den.bits.length := by
  simp only [encode,parts,encodePair_length,Signed.encode_length]
  omega
 theorem encode_injective : Function.Injective encode := by
  intro a b h
  have hh := encodePair_injective Signed.encode_injective (fun n m he => by
    have hg := congrArg Word.value he
    simpa only [Word.value_bits] using hg) h
  have hn := congrArg Prod.fst hh
  have hd := congrArg Prod.snd hh
  exact Rat.ext hn hd
 theorem height_length (q : ℚ) : HasHeight q (encode q).length := by
  have hn := NatBinary.le_two_pow_length q.num.natAbs
  have hd := NatBinary.le_two_pow_length q.den
  have hlen := encode_length q
  have hnb : q.num.natAbs.bits.length ≤ (encode q).length := by omega
  have hdb : q.den.bits.length ≤ (encode q).length := by omega
  have hN := hn.trans (Nat.pow_le_pow_right (by decide : 1≤2) hnb)
  have hD := hd.trans (Nat.pow_le_pow_right (by decide : 1≤2) hdb)
  constructor
  · simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using (Nat.cast_le (α:=ℤ)).mpr hN
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using (Nat.cast_le (α:=ℤ)).mpr hD
 theorem length_height {q : ℚ} {L : ℕ} (h : HasHeight q L) : (encode q).length ≤ 3*L+10 := by
  have hN : q.num.natAbs ≤ 2^L := (Nat.cast_le (α:=ℤ)).mp (by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using h.1)
  have hD : q.den ≤ 2^L := (Nat.cast_le (α:=ℤ)).mp (by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using h.2)
  have hnb := NatBinary.length_le_height hN
  have hdb := NatBinary.length_le_height hD
  rw [encode_length]
  omega
end Ratio
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryRationalFold

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace HasHeight
 theorem foldAdd (as : List ℚ) (b : ℚ) (L : ℕ) (hb : HasHeight b L) :
    HasHeight (as.foldl (·+·) b) (L+(encodeList Ratio.encode as).length) := by
  induction as generalizing b L with
  | nil => simpa only [List.foldl_nil,EncodedList.nil,List.length_nil,add_zero] using hb
  | cons a as ih =>
      have hh := ih (b+a) (L+(Ratio.encode a).length+1) (hb.add (Ratio.height_length a))
      simp only [List.foldl_cons,EncodedList.cons_length]
      exact hh.mono (by omega)
 theorem foldMul (as : List ℚ) (b : ℚ) (L : ℕ) (hb : HasHeight b L) :
    HasHeight (as.foldl (·*·) b) (L+(encodeList Ratio.encode as).length) := by
  induction as generalizing b L with
  | nil => simpa only [List.foldl_nil,EncodedList.nil,List.length_nil,add_zero] using hb
  | cons a as ih =>
      have hh := ih (b*a) (L+(Ratio.encode a).length) (hb.mul (Ratio.height_length a))
      simp only [List.foldl_cons,EncodedList.cons_length]
      exact hh.mono (by omega)
end HasHeight
namespace ListAlgorithms
 theorem foldAdd (as : List ℚ) (b : ℚ) : as.foldl (·+·) b=b+as.sum := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.sum_cons,add_assoc]
 theorem foldMul (as : List ℚ) (b : ℚ) : as.foldl (·*·) b=b*as.prod := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.prod_cons,mul_assoc]
end ListAlgorithms
namespace PolyProgram
noncomputable def ratFoldAdd : PolyProgram (encodePair (encodeList Ratio.encode) Ratio.encode)
    Ratio.encode (fun x : List ℚ × ℚ => x.1.foldl (·+·) x.2) :=
  ratAdd.listFold 0 (3*X+10) (fun as b pre suf he => by
    have hh := Ratio.length_height (HasHeight.foldAdd pre b (Ratio.encode b).length (Ratio.height_length b))
    have hp : (encodeList Ratio.encode pre).length ≤ (encodeList Ratio.encode as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    simp only [encodePair_length,eval_add,eval_mul,eval_ofNat,eval_X]
    omega)
noncomputable def ratFoldMul : PolyProgram (encodePair (encodeList Ratio.encode) Ratio.encode)
    Ratio.encode (fun x : List ℚ × ℚ => x.1.foldl (·*·) x.2) :=
  ratMul.listFold 0 (3*X+10) (fun as b pre suf he => by
    have hh := Ratio.length_height (HasHeight.foldMul pre b (Ratio.encode b).length (Ratio.height_length b))
    have hp : (encodeList Ratio.encode pre).length ≤ (encodeList Ratio.encode as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    simp only [encodePair_length,eval_add,eval_mul,eval_ofNat,eval_X]
    omega)
noncomputable def ratSum : PolyProgram (encodeList Ratio.encode) Ratio.encode List.sum := by
  refine (((identity (encodeList Ratio.encode)).fanout (constant (encodeList Ratio.encode) Ratio.encode 0)).comp ratFoldAdd).congr _ ?_
  intro as
  simp only [Function.comp_apply,id_eq]
  simpa only [zero_add] using ListAlgorithms.foldAdd as 0
noncomputable def ratProd : PolyProgram (encodeList Ratio.encode) Ratio.encode List.prod := by
  refine (((identity (encodeList Ratio.encode)).fanout (constant (encodeList Ratio.encode) Ratio.encode 1)).comp ratFoldMul).congr _ ?_
  intro as
  simp only [Function.comp_apply,id_eq]
  simpa only [one_mul] using ListAlgorithms.foldMul as 1
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryListMap

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ListAlgorithms
variable {α β : Type}
 theorem pushMap (f : α → β) (as : List α) (bs : List β) :
    as.foldl (fun bs a => f a::bs) bs=(as.map f).reverse++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      rw [List.foldl_cons,ih,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem pushFilter (f : α → Bool) (as bs : List α) :
    as.foldl (fun bs a => if f a then a::bs else bs) bs=(as.filter f).reverse++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons,List.filter_cons]
      cases f a <;> simp only [Bool.false_eq_true,ite_false,ite_true,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem count (as : List α) (n : ℕ) : as.foldl (fun n _ => n+1) n=n+as.length := by
  induction as generalizing n with
  | nil => rfl
  | cons a as ih => simp only [List.foldl_cons,ih,List.length_cons]; omega

 theorem all (p : α → Bool) (as : List α) (b : Bool) :
    as.foldl (fun b a => b && p a) b=(b && as.all p) := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.all_cons,Bool.and_assoc]

 theorem any (p : α → Bool) (as : List α) (b : Bool) :
    as.foldl (fun b a => b || p a) b=(b || as.any p) := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.any_cons,Bool.or_assoc]
end ListAlgorithms

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
noncomputable def listMap (P : PolyProgram ea eb f) (a0 : α) :
    PolyProgram (encodeList ea) (encodeList eb) (List.map f) := by
  let step : PolyProgram (encodePair (encodeList eb) ea) (encodeList eb) (fun x => f x.2::x.1) :=
    (((P.second (encodeList eb)).comp (exchange (encodeList eb) eb)).comp (listCons eb)).congr _ (fun _ => rfl)
  let fold := step.listFold a0 (X*(2*P.sizeBound+1)+X) (by
    intro as bs pre suf he
    simp only [ListAlgorithms.pushMap,EncodedList.append,List.length_append,EncodedList.reverse_length]
    let L := (encodePair (encodeList ea) (encodeList eb) (as,bs)).length
    have hpre : (encodeList ea pre).length ≤ (encodeList ea as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    have hlen : pre.length ≤ L := by
      have hp := EncodedList.length_le ea pre
      simp only [L,encodePair_length]; omega
    have hbs : (encodeList eb bs).length ≤ L := by simp only [L,encodePair_length]; omega
    have hh := EncodedList.length_bound eb (pre.map f) (P.sizeBound.eval L) (by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      apply (P.length_bound a).trans
      apply polynomial_eval_mono
      have hmem := EncodedList.member_length ea pre a ha
      simp only [L,encodePair_length]; omega)
    simp only [List.length_map] at hh
    simp only [eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
    change _ ≤ L*(2*P.sizeBound.eval L+1)+L
    nlinarith)
  let start := (identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList eb) [])
  exact ((start.comp fold).comp (listReverse eb (f a0))).congr _ (fun as => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.pushMap,List.append_nil,List.reverse_reverse])

noncomputable def listFilter {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) (encodeList ea) (List.filter p) := by
  let first := fst (encodeList ea) ea
  let test := (snd (encodeList ea) ea).comp P
  let push := (exchange (encodeList ea) ea).comp (listCons ea)
  let step : PolyProgram (encodePair (encodeList ea) ea) (encodeList ea) (fun x => if p x.2 then x.2::x.1 else x.1) :=
    (ite test first push).congr _ (fun _ => rfl)
  let fold := step.listFoldLinear a0 1 (by
    intro bs a
    simp only [one_mul]
    split_ifs
    · rw [EncodedList.cons_length]; omega
    · omega)
  exact ((((identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList ea) [])).comp fold).comp (listReverse ea a0)).congr _
    (fun as => by simp only [Function.comp_apply,id_eq,ListAlgorithms.pushFilter,List.append_nil,List.reverse_reverse])

noncomputable def listLength (ea : α → List Bool) (a0 : α) :
    PolyProgram (encodeList ea) Nat.bits List.length := by
  let step : PolyProgram (encodePair Nat.bits ea) Nat.bits (fun x : ℕ × α => x.1+1) :=
    (((fst Nat.bits ea).fanout (constant (encodePair Nat.bits ea) Nat.bits 1)).comp natAdd).congr _ (fun _ => rfl)
  let fold := step.listFoldLinear a0 2 (by
    intro n a
    have h := NatBinary.add_length n 1
    have hone : (1:ℕ).bits.length=1 := rfl
    rw [hone] at h
    dsimp only
    omega)
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) Nat.bits 0)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Nat.zero_add] using ListAlgorithms.count as 0)

noncomputable def listAll {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) encodeBool (fun as => as.all p) := by
  let step := (P.second encodeBool).comp boolAnd
  let fold := step.listFoldLinear a0 0 (by intro b a; simp only [encodeBool,List.length_singleton,zero_mul,add_zero,le_refl])
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) encodeBool true)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Bool.true_and] using ListAlgorithms.all p as true)

noncomputable def listAny {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) encodeBool (fun as => as.any p) := by
  let step := (P.second encodeBool).comp boolOr
  let fold := step.listFoldLinear a0 0 (by intro b a; simp only [encodeBool,List.length_singleton,zero_mul,add_zero,le_refl])
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) encodeBool false)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Bool.false_or] using ListAlgorithms.any p as false)
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryListContext

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListAlgorithms
variable {α β γ : Type}
 theorem pushMapWith (f : γ × α → β) (as : List α) (c : γ) (bs : List β) :
    as.foldl (fun x a => (x.1,f (x.1,a)::x.2)) (c,bs)=(c,(as.map (fun a => f (c,a))).reverse++bs) := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      simpa only [List.foldl_cons,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using ih (f (c,a)::bs)
 theorem pushMapWith_pair (f : γ × α → β) (as : List α) (x : γ × List β) :
    as.foldl (fun x a => (x.1,f (x.1,a)::x.2)) x=(x.1,(as.map (fun a => f (x.1,a))).reverse++x.2) := by
  cases x
  exact pushMapWith _ _ _ _
 theorem filterMapPair (p : γ × α → Bool) (c : γ) (as : List α) :
    (((as.map (fun a => (c,a))).filter p).map Prod.snd)=as.filter (fun a => p (c,a)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons,List.filter_cons]
      split <;> simp_all only [List.map_cons]
end ListAlgorithms

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
noncomputable def listMapWith {f : γ × α → β}
    (P : PolyProgram (encodePair ec ea) eb f) (a0 : α) (b0 : β) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList eb) (fun x => x.2.map (fun a => f (x.1,a))) := by
  let eacc := encodePair ec (encodeList eb)
  let acc := fst eacc ea
  let c := acc.comp (fst ec (encodeList eb))
  let bs := acc.comp (snd ec (encodeList eb))
  let a := snd eacc ea
  let nb := ((c.fanout a).comp P).fanout bs
  let step : PolyProgram (encodePair eacc ea) eacc (fun x : (γ × List β) × α => (x.1.1,f (x.1.1,x.2)::x.1.2)) :=
    (c.fanout (nb.comp (listCons eb))).congr _ (fun _ => rfl)
  let B : Polynomial ℕ := 3*X+X*(2*P.sizeBound.comp (3*X+1)+1)+1
  let fold := step.listFold a0 B (by
    intro as x pre suf he
    let L := (encodePair (encodeList ea) eacc (as,x)).length
    have hc : (ec x.1).length ≤ L := by simp only [L,eacc,encodePair_length]; omega
    have hb : (encodeList eb x.2).length ≤ L := by simp only [L,eacc,encodePair_length]; omega
    have hp : (encodeList ea pre).length ≤ L := by
      have hh : (encodeList ea pre).length ≤ (encodeList ea as).length := by rw [he,EncodedList.append,List.length_append]; omega
      simp only [L,encodePair_length]; omega
    have hplen : pre.length ≤ L := (EncodedList.length_le ea pre).trans hp
    have hout := EncodedList.length_bound eb (pre.map (fun a => f (x.1,a))) (P.sizeBound.eval (3*L+1)) (by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      apply (P.length_bound (x.1,a)).trans
      apply polynomial_eval_mono
      have hla := (EncodedList.member_length ea pre a ha).trans hp
      simp only [encodePair_length]
      omega)
    rw [List.length_map] at hout
    simp only [ListAlgorithms.pushMapWith_pair,eacc,encodePair_length,EncodedList.append,List.length_append,EncodedList.reverse_length]
    simp only [B,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,eval_comp]
    simp only [L,eacc,encodePair_length] at hc hb hplen hout
    nlinarith)
  let start := (snd ec (encodeList ea)).fanout ((fst ec (encodeList ea)).fanout (constant (encodePair ec (encodeList ea)) (encodeList eb) []))
  exact (((start.comp fold).comp (snd ec (encodeList eb))).comp (listReverse eb b0)).congr _ (fun x => by
    simp only [Function.comp_apply,ListAlgorithms.pushMapWith,List.append_nil,List.reverse_reverse])

noncomputable def listFilterWith {p : γ × α → Bool}
    (P : PolyProgram (encodePair ec ea) encodeBool p) (a0 : α) (c0 : γ) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList ea) (fun x => x.2.filter (fun a => p (x.1,a))) := by
  let attach := (identity (encodePair ec ea)).listMapWith a0 (c0,a0)
  let filt := listFilter P (c0,a0)
  let drop := (snd ec ea).listMap (c0,a0)
  exact ((attach.comp filt).comp drop).congr _ (fun x => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.filterMapPair])
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryListExtras

namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace WordTransducer

def listBits : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[true,b,false])
  finish _ := []
theorem listBits_run (xs : List Bool) : listBits.run () xs=encodeList encodeBool xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change [true,b,false]++listBits.run () xs=quote [b]++encodeList encodeBool xs
      rw [ih]
      rfl
end WordTransducer
namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
noncomputable def wordAsList : PolyProgram id (encodeList encodeBool) id :=
  WordTransducer.listBits.program.of_word (fun xs => WordTransducer.listBits_run xs)
noncomputable def natAsList : PolyProgram Nat.bits (encodeList encodeBool) Nat.bits :=
  wordAsList.recode Nat.bits (fun _ => rfl) (fun _ => rfl)
noncomputable def natSize : PolyProgram Nat.bits Nat.bits Nat.size :=
  (natAsList.comp (listLength encodeBool false)).congr _ (fun n => Nat.size_eq_bits_len n)
noncomputable def listFlatten (ea : α → List Bool) (a0 : α) :
    PolyProgram (encodeList (encodeList ea)) (encodeList ea) List.flatten := by
  let P := (listAppend ea a0).listFoldLinear [] 1 (by
    intro bs as
    simp only [EncodedList.append,List.length_append]
    omega)
  exact (((identity (encodeList (encodeList ea))).fanout (constant (encodeList (encodeList ea)) (encodeList ea) [])).comp P).congr _ (fun xs => by
    change xs.foldl (fun b a => b++a) []=xs.flatten
    have he (xs : List (List α)) (acc : List α) : xs.foldl (fun b a => b++a) acc=acc++xs.flatten := by
      induction xs generalizing acc with
      | nil => simp
      | cons y ys hi => simpa only [List.foldl_cons,List.flatten_cons,List.append_assoc] using hi (acc++y)
    simpa using he xs [])
noncomputable def listFlatMap {f : α → List β} (P : PolyProgram ea (encodeList eb) f) (a0 : α) (b0 : β) :
    PolyProgram (encodeList ea) (encodeList eb) (fun xs => xs.flatMap f) :=
  ((P.listMap a0).comp (listFlatten eb b0)).congr _ (fun xs => by rfl)
noncomputable def listFlatMapWith {f : γ × α → List β} (P : PolyProgram (encodePair ec ea) (encodeList eb) f) (a0 : α) (b0 : β) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList eb) (fun x => x.2.flatMap (fun a => f (x.1,a))) :=
  ((P.listMapWith a0 []).comp (listFlatten eb b0)).congr _ (fun x => by rfl)
noncomputable def listAllWith {p : γ × α → Bool} (P : PolyProgram (encodePair ec ea) encodeBool p) (a0 : α) :
    PolyProgram (encodePair ec (encodeList ea)) encodeBool (fun x => x.2.all (fun a => p (x.1,a))) :=
  ((P.listMapWith a0 false).comp (listAll (identity encodeBool) false)).congr _ (fun x => by simp only [Function.comp_apply,List.all_map,Function.id_comp])
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryListIndices

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListAlgorithms
variable {α : Type}
def indexStep (x : (ℕ × List ℕ) × α) : ℕ × List ℕ := (x.1.1+1,x.1.1::x.1.2)
 theorem pushIndices (xs : List α) (n : ℕ) (bs : List ℕ) :
    xs.foldl (fun b a => indexStep (b,a)) (n,bs)=
      (n+xs.length,(List.range' n xs.length).reverse++bs) := by
  induction xs generalizing n bs with
  | nil => simp
  | cons a xs ih =>
      change xs.foldl (fun b a => indexStep (b,a)) (n+1,n::bs)=_
      rw [ih]
      simp only [List.length_cons,List.range'_succ,List.reverse_cons,List.append_assoc,List.singleton_append]
      congr 1
      omega
 theorem index_partial_size (ea : α → List Bool) (xs : List α) (x : ℕ × List ℕ) (pre suf : List α)
    (he : xs=pre++suf) :
    (encodePair Nat.bits (encodeList Nat.bits) (pre.foldl (fun b a => indexStep (b,a)) x)).length ≤
      10*((encodePair (encodeList ea) (encodePair Nat.bits (encodeList Nat.bits)) (xs,x)).length+1)^2 := by
  let L := (encodePair (encodeList ea) (encodePair Nat.bits (encodeList Nat.bits)) (xs,x)).length
  have hp : pre.length ≤ L := by
    have hp : (encodeList ea pre).length ≤ (encodeList ea xs).length := by rw [he,EncodedList.append,List.length_append]; omega
    have hh := EncodedList.length_le ea pre
    simp only [L,encodePair_length]; omega
  have hn : x.1.bits.length ≤ L := by simp only [L,encodePair_length]; omega
  have hb : (encodeList Nat.bits x.2).length ≤ L := by simp only [L,encodePair_length]; omega
  have hl : pre.length.bits.length ≤ pre.length+1 := NatBinary.length_le_height (Nat.lt_two_pow_self.le)
  have hc := NatBinary.add_length x.1 pre.length
  have hi : ∀ q∈List.range' x.1 pre.length, q.bits.length ≤ 2*L+2 := by
    intro q hq
    have hq' : q ≤ x.1+pre.length := (List.mem_range'_1.mp hq).2.le
    have hh := (NatBinary.length_mono hq').trans hc
    omega
  have hr := EncodedList.length_bound Nat.bits (List.range' x.1 pre.length) (2*L+2) hi
  simp only [List.length_range'] at hr
  have hcount : (x.1+pre.length).bits.length ≤ 2*L+2 := by omega
  have hr' : (encodeList Nat.bits (List.range' x.1 pre.length)).length ≤ L*(4*L+5) := by
    calc
      _ ≤ pre.length*(2*(2*L+2)+1) := hr
      _ ≤ L*(2*(2*L+2)+1) := Nat.mul_le_mul_right _ hp
      _ = L*(4*L+5) := by ring
  change (encodePair Nat.bits (encodeList Nat.bits) (pre.foldl (fun b a => indexStep (b,a)) (x.1,x.2))).length ≤ _
  rw [pushIndices]
  simp only [encodePair_length,EncodedList.append,List.length_append,EncodedList.reverse_length]
  simp only [L,encodePair_length] at hcount hr' hb
  nlinarith

end ListAlgorithms
namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listIndices : PolyProgram (encodeList ea) (encodeList Nat.bits) (fun xs : List α => List.range xs.length) := by
  let eb := encodePair Nat.bits (encodeList Nat.bits)
  let acc := fst eb ea
  let n := acc.comp (fst Nat.bits (encodeList Nat.bits))
  let bs := acc.comp (snd Nat.bits (encodeList Nat.bits))
  let inc := (n.fanout (constant (encodePair eb ea) Nat.bits 1)).comp natAdd
  let push := (n.fanout bs).comp (listCons Nat.bits)
  let step : PolyProgram (encodePair eb ea) eb ListAlgorithms.indexStep :=
    (inc.fanout push).congr _ (fun _ => rfl)
  let fold := step.listFold a0 (10*(X+1)^2) (by
    intro xs x pre suf he
    simpa only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one] using ListAlgorithms.index_partial_size ea xs x pre suf he)
  let start := (identity (encodeList ea)).fanout (constant (encodeList ea) eb (0,[]))
  exact ((((start.comp fold).comp (snd Nat.bits (encodeList Nat.bits))).comp (listReverse Nat.bits 0))).congr _ (fun xs => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.pushIndices,List.append_nil,List.reverse_reverse,← List.range_eq_range'])
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryListIndex

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListSplit
variable {α : Type} (ea : α → List Bool) (a0 : α)
abbrev enc : List α × (ℕ × List α) → List Bool := encodePair (encodeList ea) (encodePair Nat.bits (encodeList ea))
abbrev out : List α × List α → List Bool := encodePair (encodeList ea) (encodeList ea)
def body (x : List α × (ℕ × List α)) : (List α × List α) ⊕ (List α × (ℕ × List α)) :=
  if x.1.isEmpty || decide (x.2.1=0) then .inl (x.2.2.reverse,x.1)
  else .inr (x.1.tail,(x.2.1-1,x.1.head?.getD a0::x.2.2))
def result (x : List α × (ℕ × List α)) : List α × List α := (x.2.2.reverse++x.1.take x.2.1,x.1.drop x.2.1)
noncomputable def program : PolyProgram (enc ea) (encodeLoop (enc ea) (out ea)) (body a0) := by
  let ls := PolyProgram.fst (encodeList ea) (encodePair Nat.bits (encodeList ea))
  let ns := PolyProgram.snd (encodeList ea) (encodePair Nat.bits (encodeList ea))
  let n := ns.comp (PolyProgram.fst Nat.bits (encodeList ea))
  let bs := ns.comp (PolyProgram.snd Nat.bits (encodeList ea))
  let zero := (((ls.comp (PolyProgram.listIsEmpty ea)).fanout (n.comp PolyProgram.natZero)).comp PolyProgram.boolOr)
  let done := (((bs.comp (PolyProgram.listReverse ea a0)).fanout ls).comp (PolyProgram.injectLeft (enc ea) (out ea)))
  let pred := ((n.fanout (PolyProgram.constant (enc ea) Nat.bits 1)).comp PolyProgram.natSub)
  let push := (((ls.comp (PolyProgram.listHead ea a0)).fanout bs).comp (PolyProgram.listCons ea))
  let cont := (((ls.comp (PolyProgram.listTail ea a0)).fanout (pred.fanout push)).comp (PolyProgram.injectRight (enc ea) (out ea)))
  exact (PolyProgram.ite zero cont done).congr _ (fun _ => rfl)

 theorem run (as bs : List α) (n S : ℕ) (hsize : (enc ea (as,(n,bs))).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea) (body a0) S t (as,(n,bs)) (result (as,(n,bs))) := by
  induction as generalizing n bs with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp only [body,result,List.isEmpty_nil,Bool.true_or,List.take_nil,List.drop_nil,List.append_nil]
      rfl
  | cons a as ih =>
      cases n with
      | zero =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp only [body,result,List.isEmpty_cons,decide_true,Bool.false_or,List.take_zero,List.drop_zero,List.append_nil]
          rfl
      | succ n =>
          have hn := NatBinary.length_mono (Nat.le_succ n)
          change n.bits.length ≤ (n+1).bits.length at hn
          have hs : (enc ea (as,(n,a::bs))).length ≤ S := by
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih (a::bs) n hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have hb : body a0 (a::as,(n+1,bs))=.inr (as,(n,a::bs)) := by simp [body]
          have he : result (as,(n,a::bs))=result (a::as,(n+1,bs)) := by
            simp only [result,List.reverse_cons,List.take_succ_cons,List.drop_succ_cons,List.append_assoc,List.singleton_append]
          rw [← he]
          exact BoundedRun.step hsize hb hr

noncomputable def loop : PolyProgram (enc ea) (out ea) result :=
  (program ea a0).loop result (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea a0 x.1 x.2.2 x.2.1 (enc ea x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListSplit

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listSplitAt : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodePair (encodeList ea) (encodeList ea)) (fun x : List α × ℕ => (x.1.take x.2,x.1.drop x.2)) := by
  let ls := fst (encodeList ea) Nat.bits
  let n := snd (encodeList ea) Nat.bits
  let start := ls.fanout (n.fanout (constant (encodePair (encodeList ea) Nat.bits) (encodeList ea) []))
  exact (start.comp (ListSplit.loop ea a0)).congr _ (fun x => by simp only [Function.comp_apply,ListSplit.result,List.reverse_nil,List.nil_append])
noncomputable def listTake : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.take x.2) :=
  ((listSplitAt ea a0).comp (fst (encodeList ea) (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listDrop : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.drop x.2) :=
  ((listSplitAt ea a0).comp (snd (encodeList ea) (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listGetD : PolyProgram (encodePair (encodeList ea) Nat.bits)
    ea (fun x : List α × ℕ => x.1[x.2]?.getD a0) := by
  exact ((listDrop ea a0).comp (listHead ea a0)).congr _ (fun x => by
    simp only [Function.comp_apply,List.head?_drop])
noncomputable def listEraseIdx : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.take x.2++(x.1.drop x.2).tail) :=
  (((listSplitAt ea a0).comp ((listTail ea a0).second (encodeList ea))).comp (listAppend ea a0)).congr _ (fun _ => rfl)
noncomputable def listInsertAt : PolyProgram (encodePair (encodePair (encodeList ea) Nat.bits) ea)
    (encodeList ea) (fun x : (List α × ℕ) × α => x.1.1.take x.1.2++x.2::x.1.1.drop x.1.2) := by
  let sp := (fst (encodePair (encodeList ea) Nat.bits) ea).comp (listSplitAt ea a0)
  let pre := sp.comp (fst (encodeList ea) (encodeList ea))
  let suf := sp.comp (snd (encodeList ea) (encodeList ea))
  let elem := snd (encodePair (encodeList ea) Nat.bits) ea
  exact ((pre.fanout ((elem.fanout suf).comp (listCons ea))).comp (listAppend ea a0)).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryListZip

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListZip
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α) (b0 : β)
abbrev enc : (List α × List β) × List (α × β) → List Bool :=
  encodePair (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
def body (x : (List α × List β) × List (α × β)) : List (α × β) ⊕ ((List α × List β) × List (α × β)) :=
  if x.1.1.isEmpty || x.1.2.isEmpty then .inl x.2.reverse
  else .inr ((x.1.1.tail,x.1.2.tail),(x.1.1.head?.getD a0,x.1.2.head?.getD b0)::x.2)
def result (x : (List α × List β) × List (α × β)) : List (α × β) := x.2.reverse++x.1.1.zip x.1.2
noncomputable def program : PolyProgram (enc ea eb) (encodeLoop (enc ea eb) (encodeList (encodePair ea eb))) (body a0 b0) := by
  let pair := PolyProgram.fst (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
  let as := pair.comp (PolyProgram.fst (encodeList ea) (encodeList eb))
  let bs := pair.comp (PolyProgram.snd (encodeList ea) (encodeList eb))
  let cs := PolyProgram.snd (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
  let test := (((as.comp (PolyProgram.listIsEmpty ea)).fanout (bs.comp (PolyProgram.listIsEmpty eb))).comp PolyProgram.boolOr)
  let done := ((cs.comp (PolyProgram.listReverse (encodePair ea eb) (a0,b0))).comp (PolyProgram.injectLeft (enc ea eb) (encodeList (encodePair ea eb))))
  let heads := (as.comp (PolyProgram.listHead ea a0)).fanout (bs.comp (PolyProgram.listHead eb b0))
  let tails := (as.comp (PolyProgram.listTail ea a0)).fanout (bs.comp (PolyProgram.listTail eb b0))
  let push := ((heads.fanout cs).comp (PolyProgram.listCons (encodePair ea eb)))
  let cont := ((tails.fanout push).comp (PolyProgram.injectRight (enc ea eb) (encodeList (encodePair ea eb))))
  exact (PolyProgram.ite test cont done).congr _ (fun _ => rfl)

 theorem run (as : List α) (bs : List β) (cs : List (α × β)) (S : ℕ)
    (hsize : (enc ea eb ((as,bs),cs)).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea eb) (body a0 b0) S t ((as,bs),cs) (result ((as,bs),cs)) := by
  induction as generalizing bs cs with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp [body,result]
  | cons a as ih =>
      cases bs with
      | nil =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp [body,result]
      | cons b bs =>
          have hs : (enc ea eb ((as,bs),(a,b)::cs)).length ≤ S := by
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih bs ((a,b)::cs) hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have he : result ((as,bs),(a,b)::cs)=result ((a::as,b::bs),cs) := by
            simp only [result,List.reverse_cons,List.zip_cons_cons,List.append_assoc,List.singleton_append]
          rw [← he]
          exact BoundedRun.step hsize (by simp [body]) hr

noncomputable def loop : PolyProgram (enc ea eb) (encodeList (encodePair ea eb)) result :=
  (program ea eb a0 b0).loop result (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea eb a0 b0 x.1.1 x.1.2 x.2 (enc ea eb x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListZip
namespace PolyProgram
variable {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α) (b0 : β)
noncomputable def listZip : PolyProgram (encodePair (encodeList ea) (encodeList eb))
    (encodeList (encodePair ea eb)) (fun x : List α × List β => x.1.zip x.2) := by
  let start := (identity (encodePair (encodeList ea) (encodeList eb))).fanout
    (constant (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb)) [])
  exact (start.comp (ListZip.loop ea eb a0 b0)).congr _ (fun _ => by simp only [Function.comp_apply,id_eq,ListZip.result,List.reverse_nil,List.nil_append])
noncomputable def listZipWith {ec : γ → List Bool} {f : α × β → γ}
    (P : PolyProgram (encodePair ea eb) ec f) :
    PolyProgram (encodePair (encodeList ea) (encodeList eb)) (encodeList ec) (fun x : List α × List β => (x.1.zip x.2).map f) :=
  ((listZip ea eb a0 b0).comp (P.listMap (a0,b0))).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryPredicates

namespace OAI


                                        
section
namespace MetricKMedian.Binary.PolyProgram
noncomputable def natLE : PolyProgram (encodePair Nat.bits Nat.bits) encodeBool (fun x : ℕ × ℕ => decide (x.1≤x.2)) :=
  (((exchange Nat.bits Nat.bits).comp natLT).comp boolNot).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [Function.comp_def,h,not_lt.mpr h]
    · simp [Function.comp_def,h,lt_of_not_ge h])
noncomputable def natEQ : PolyProgram (encodePair Nat.bits Nat.bits) encodeBool (fun x : ℕ × ℕ => decide (x.1=x.2)) :=
  ((natLE.fanout ((exchange Nat.bits Nat.bits).comp natLE)).comp boolAnd).congr _ (fun x => by
    by_cases h₁ : x.1≤x.2 <;> by_cases h₂ : x.2≤x.1 <;> simp [Function.comp_apply,Prod.swap,h₁,h₂,le_antisymm_iff])
noncomputable def ratZero : PolyProgram Ratio.encode encodeBool (fun q => decide (q=0)) :=
  ((ratNum.comp intAbs).comp natZero).congr _ (fun q => by
    simp only [Function.comp_apply,Int.natAbs_eq_zero,Rat.num_eq_zero])
noncomputable def ratNonzero : PolyProgram Ratio.encode encodeBool (fun q => decide (q≠0)) :=
  (ratZero.comp boolNot).congr _ (fun q => by simp)
noncomputable def ratEQ : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1=x.2)) :=
  (ratSub.comp ratZero).congr _ (fun q => by simp only [Function.comp_apply,sub_eq_zero])
noncomputable def ratLE : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1≤x.2)) :=
  (((exchange Ratio.encode Ratio.encode).comp ratLT).comp boolNot).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [Function.comp_def,h,not_lt.mpr h]
    · simp [Function.comp_def,h,lt_of_not_ge h])
end MetricKMedian.Binary.PolyProgram
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryListSelection

namespace OAI


                                           
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListFindIdx
variable {α : Type} (ea : α → List Bool) (a0 : α) (p : α → Bool)
abbrev enc : List α × ℕ → List Bool := encodePair (encodeList ea) Nat.bits
def body (x : List α × ℕ) : ℕ ⊕ (List α × ℕ) :=
  if x.1.isEmpty || p (x.1.head?.getD a0) then .inl x.2 else .inr (x.1.tail,x.2+1)
def result (x : List α × ℕ) : ℕ := x.2+x.1.findIdx p
noncomputable def program (P : PolyProgram ea encodeBool p) :
    PolyProgram (enc ea) (encodeLoop (enc ea) Nat.bits) (body a0 p) := by
  let ls := PolyProgram.fst (encodeList ea) Nat.bits
  let n := PolyProgram.snd (encodeList ea) Nat.bits
  let hd := (ls.comp (PolyProgram.listHead ea a0)).comp P
  let test := ((ls.comp (PolyProgram.listIsEmpty ea)).fanout hd).comp PolyProgram.boolOr
  let done := n.comp (PolyProgram.injectLeft (enc ea) Nat.bits)
  let inc := (n.fanout (PolyProgram.constant (enc ea) Nat.bits 1)).comp PolyProgram.natAdd
  let cont := (((ls.comp (PolyProgram.listTail ea a0)).fanout inc).comp (PolyProgram.injectRight (enc ea) Nat.bits))
  exact (PolyProgram.ite test cont done).congr _ (fun _ => rfl)
 theorem run (as : List α) (n S : ℕ) (hsize : (enc ea (as,n)).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea) (body a0 p) S t (as,n) (result p (as,n)) := by
  induction as generalizing n with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp [body,result]
  | cons a as ih =>
      cases hp : p a with
      | true =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp [body,result,hp,List.findIdx_cons]
      | false =>
          have hn := NatBinary.add_length n 1
          have hs : (enc ea (as,n+1)).length ≤ S := by
            have hone : (1:ℕ).bits.length=1 := rfl
            rw [hone] at hn
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih (n+1) hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have he : result p (as,n+1)=result p (a::as,n) := by simp [result,List.findIdx_cons,hp,Nat.add_comm,Nat.add_left_comm]
          rw [← he]
          exact BoundedRun.step hsize (by simp [body,hp]) hr
noncomputable def loop (P : PolyProgram ea encodeBool p) : PolyProgram (enc ea) Nat.bits (result p) :=
  (program ea a0 p P).loop (result p) (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea a0 p x.1 x.2 (enc ea x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListFindIdx
namespace ListAlgorithms
variable {α : Type}
 theorem foldChoice (p : α × α → Bool) (as : List α) (b : α) :
    as.foldl (fun b a => if p (b,a) then a else b) b=b ∨ as.foldl (fun b a => if p (b,a) then a else b) b∈as := by
  induction as generalizing b with
  | nil => exact Or.inl rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      cases hp : p (b,a)
      · simpa only [hp,Bool.false_eq_true,ite_false] using (ih b).imp_right (fun h => List.mem_cons_of_mem _ h)
      · simp only [ite_true]
        rcases ih a with he|hmem
        · exact Or.inr (by rw [he]; exact List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ hmem)
end ListAlgorithms
namespace PolyProgram
variable {α : Type} {ea : α → List Bool}
noncomputable def listFindIdx {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) Nat.bits (List.findIdx p) :=
  ((((identity (encodeList ea)).fanout (constant (encodeList ea) Nat.bits 0)).comp
    (ListFindIdx.loop ea a0 p P))).congr _ (fun _ => by simp only [Function.comp_apply,id_eq,ListFindIdx.result,Nat.zero_add])
noncomputable def listChoose {p : α × α → Bool} (P : PolyProgram (encodePair ea ea) encodeBool p) (a0 : α) :
    PolyProgram (encodePair (encodeList ea) ea) ea
      (fun x : List α × α => x.1.foldl (fun b a => if p (b,a) then a else b) x.2) := by
  let step : PolyProgram (encodePair ea ea) ea (fun x => if p x then x.2 else x.1) :=
    (ite P (fst ea ea) (snd ea ea)).congr _ (fun _ => rfl)
  exact step.listFold a0 X (fun as b pre suf he => by
    rcases ListAlgorithms.foldChoice p pre b with h|h
    · rw [h]
      simp only [eval_X,encodePair_length]; omega
    · have hp : (encodeList ea pre).length ≤ (encodeList ea as).length := by
        rw [he,EncodedList.append,List.length_append]; omega
      have hh := (EncodedList.member_length ea pre _ h).trans hp
      simp only [eval_X,encodePair_length]; omega)
end PolyProgram
end MetricKMedian.Binary
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryAutomatic

namespace OAI


                                       
section
namespace MetricKMedian.Binary.Automatic
open PolyProgram Function
class Coding (α : Type) where
  encode : α → List Bool
abbrev enc {α : Type} [Coding α] : α → List Bool := Coding.encode
instance : Coding ℕ := ⟨Nat.bits⟩
instance : Coding ℤ := ⟨Signed.encode⟩
instance : Coding ℚ := ⟨Ratio.encode⟩
instance : Coding Bool := ⟨encodeBool⟩
instance : Coding Unit := ⟨fun _ => []⟩
instance {α β : Type} [Coding α] [Coding β] : Coding (α × β) := ⟨encodePair enc enc⟩
instance {α : Type} [Coding α] : Coding (List α) := ⟨encodeList enc⟩

@[fun_prop] def Poly {α β : Type} [Coding α] [Coding β] (f : α → β) : Prop :=
  Nonempty (PolyProgram enc enc f)

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
noncomputable def program {f : α → β} (h : Poly f) : PolyProgram enc enc f := Classical.choice h

theorem of_program {f : α → β} (p : PolyProgram enc enc f) : Poly f := ⟨p⟩

@[fun_prop] theorem identity : Poly (id : α → α) := ⟨PolyProgram.identity enc⟩
@[fun_prop] theorem const (b : β) : Poly (fun _ : α => b) := ⟨PolyProgram.constant enc enc b⟩
@[fun_prop] theorem comp {f : β → γ} {g : α → β} (hf : Poly f) (hg : Poly g) : Poly (fun a => f (g a)) :=
  ⟨hg.program.comp hf.program⟩
@[fun_prop] theorem pair {f : α → β} {g : α → γ} (hf : Poly f) (hg : Poly g) : Poly (fun a => (f a,g a)) :=
  ⟨hf.program.fanout hg.program⟩
@[fun_prop] theorem fst : Poly (Prod.fst : α × β → α) := ⟨PolyProgram.fst enc enc⟩
@[fun_prop] theorem snd : Poly (Prod.snd : α × β → β) := ⟨PolyProgram.snd enc enc⟩
@[fun_prop] theorem ite {p : α → Bool} {f g : α → β} (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x then f x else g x) := ⟨(PolyProgram.ite hp.program hg.program hf.program).congr _ (fun _ => rfl)⟩

@[fun_prop] theorem list_map [Inhabited β] [Inhabited γ] {f : α → β → γ} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).map (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listMapWith default default)⟩

@[fun_prop] theorem rat_add : Poly (fun x : ℚ × ℚ => x.1+x.2) := ⟨ratAdd⟩
@[fun_prop] theorem rat_sub : Poly (fun x : ℚ × ℚ => x.1-x.2) := ⟨ratSub⟩
@[fun_prop] theorem rat_mul : Poly (fun x : ℚ × ℚ => x.1*x.2) := ⟨ratMul⟩
@[fun_prop] theorem rat_div : Poly (fun x : ℚ × ℚ => x.1/x.2) := ⟨ratDiv⟩
@[fun_prop] theorem rat_lt : Poly (fun x : ℚ × ℚ => decide (x.1<x.2)) := ⟨ratLT⟩
@[fun_prop] theorem rat_le : Poly (fun x : ℚ × ℚ => decide (x.1≤x.2)) := ⟨ratLE⟩
@[fun_prop] theorem rat_eq : Poly (fun x : ℚ × ℚ => decide (x.1=x.2)) := ⟨ratEQ⟩
@[fun_prop] theorem nat_add : Poly (fun x : ℕ × ℕ => x.1+x.2) := ⟨natAdd⟩
@[fun_prop] theorem nat_sub : Poly (fun x : ℕ × ℕ => x.1-x.2) := ⟨natSub⟩
@[fun_prop] theorem nat_mul : Poly (fun x : ℕ × ℕ => x.1*x.2) := ⟨natMul⟩
@[fun_prop] theorem nat_lt : Poly (fun x : ℕ × ℕ => decide (x.1<x.2)) := ⟨natLT⟩
@[fun_prop] theorem nat_le : Poly (fun x : ℕ × ℕ => decide (x.1≤x.2)) := ⟨natLE⟩
@[fun_prop] theorem nat_eq : Poly (fun x : ℕ × ℕ => decide (x.1=x.2)) := ⟨natEQ⟩
@[fun_prop] theorem bool_and : Poly (fun x : Bool × Bool => x.1 && x.2) := ⟨boolAnd⟩
@[fun_prop] theorem bool_or : Poly (fun x : Bool × Bool => x.1 || x.2) := ⟨boolOr⟩
@[fun_prop] theorem rat_neg : Poly (fun x : ℚ => -x) := ⟨ratNeg⟩
@[fun_prop] theorem bool_not : Poly (fun x : Bool => !x) := ⟨boolNot⟩
@[fun_prop] theorem rat_ofNat : Poly (fun x : ℕ => (x:ℚ)) := ⟨ratOfNat⟩
@[fun_prop] theorem rat_ofInt : Poly (fun x : ℤ => (x:ℚ)) := ⟨ratOfInt⟩

@[fun_prop] theorem list_length [Inhabited α] : Poly (List.length : List α → ℕ) := ⟨listLength enc default⟩
@[fun_prop] theorem list_indices [Inhabited α] : Poly (fun xs : List α => List.range xs.length) := ⟨listIndices enc default⟩
@[fun_prop] theorem list_getD (a0 : α) : Poly (fun x : List α × ℕ => x.1[x.2]?.getD a0) := ⟨listGetD enc a0⟩
@[fun_prop] theorem list_head (a0 : α) : Poly (fun xs : List α => xs.head?.getD a0) := ⟨listHead enc a0⟩
@[fun_prop] theorem list_tail [Inhabited α] : Poly (List.tail : List α → List α) := ⟨listTail enc default⟩
@[fun_prop] theorem list_empty : Poly (List.isEmpty : List α → Bool) := ⟨listIsEmpty enc⟩
@[fun_prop] theorem list_append [Inhabited α] : Poly (fun x : List α × List α => x.1++x.2) := ⟨listAppend enc default⟩
@[fun_prop] theorem list_cons : Poly (fun x : α × List α => x.1::x.2) := ⟨listCons enc⟩
@[fun_prop] theorem list_zip [Inhabited α] [Inhabited β] : Poly (fun x : List α × List β => x.1.zip x.2) := ⟨listZip enc enc default default⟩
@[fun_prop] theorem list_filter [Inhabited α] [Inhabited β] {f : α → β → Bool} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).filter (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listFilterWith default default)⟩
@[fun_prop] theorem list_findIdx [Inhabited β] {f : α → β → Bool} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).findIdx (f x)) := by
  let tests := ((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listMapWith default false)
  exact ⟨(tests.comp (listFindIdx (PolyProgram.identity encodeBool) false)).congr _ (fun _ => by
    simp only [Function.comp_def,List.findIdx_map,id_eq])⟩

@[fun_prop] theorem list_getD_comp (a0 : β) {xs : α → List β} {i : α → ℕ}
    (hx : Poly xs) (hi : Poly i) : Poly (fun x => (xs x)[i x]?.getD a0) :=
  comp (list_getD a0) (pair hx hi)
@[fun_prop] theorem list_head_comp (a0 : β) {xs : α → List β}
    (hx : Poly xs) : Poly (fun x => (xs x).head?.getD a0) := comp (list_head a0) hx

@[fun_prop] theorem rat_lt_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x<g x)) := comp rat_lt (pair hf hg)
@[fun_prop] theorem rat_le_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x≤g x)) := comp rat_le (pair hf hg)
@[fun_prop] theorem rat_eq_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x=g x)) := comp rat_eq (pair hf hg)
@[fun_prop] theorem nat_lt_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x<g x)) := comp nat_lt (pair hf hg)
@[fun_prop] theorem nat_le_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x≤g x)) := comp nat_le (pair hf hg)
@[fun_prop] theorem nat_eq_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x=g x)) := comp nat_eq (pair hf hg)
@[fun_prop] theorem ite_prop {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : Poly (fun x => decide (p x))) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x then f x else g x) := by
  exact ⟨(PolyProgram.ite hp.program hg.program hf.program).congr _ (fun _ => by simp only [decide_eq_true_eq])⟩

@[fun_prop] theorem list_flatMap [Inhabited β] [Inhabited γ] {f : α → β → List γ} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).flatMap (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listFlatMapWith default default)⟩

end Poly
end MetricKMedian.Binary.Automatic
end

end OAI


-- Source module: OAI.Combinatorics.KMedian.Binary.BinaryBooleanLists

namespace OAI


                                          
section
namespace MetricKMedian.Binary
namespace BooleanLists
def pack : Transducer where
  Q := Unit
  initial := ()
  next := fun _ b => ((),[true,b,false])
  finish := fun _ => []
 theorem pack_run (xs : List Bool) : pack.run () xs=encodeList encodeBool xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [Transducer.run,pack,encodeList,encodeBool,quote,List.append_assoc,List.nil_append] using congrArg (fun ys => [true,b,false]++ys) ih
inductive Phase | start | value | stop deriving DecidableEq
instance : Fintype Phase := ⟨{.start,.value,.stop},by intro p; cases p <;> simp⟩
def unpack : Transducer where
  Q := Phase
  initial := .start
  next := fun q b => match q with
    | .start => (.value,[])
    | .value => (.stop,[b])
    | .stop => (.start,[])
  finish := fun _ => []
 theorem unpack_run (xs : List Bool) : unpack.run .start (encodeList encodeBool xs)=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [encodeList,encodeBool,quote,List.cons_append,List.nil_append,Transducer.run,unpack,List.append_assoc,List.singleton_append] using congrArg (List.cons b) ih
noncomputable def packProgram : PolyProgram id (encodeList encodeBool) (id : List Bool → List Bool) :=
  pack.program.recode id (fun _ => rfl) (fun xs => pack_run xs)
noncomputable def unpackProgram : PolyProgram (encodeList encodeBool) id (id : List Bool → List Bool) :=
  unpack.program.recode (encodeList encodeBool) (fun _ => rfl) (fun xs => unpack_run xs)
noncomputable def valueProgram : PolyProgram (encodeList encodeBool) Nat.bits Word.value := unpackProgram.comp PolyProgram.toBits
 theorem length (xs : List Bool) : (encodeList encodeBool xs).length=3*xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [EncodedList.cons_length,encodeBool,List.length_cons,List.length_nil,ih]; omega
end BooleanLists
end MetricKMedian.Binary
end

end OAI



/-!
Reuses the concrete Boolean-stack polynomial-time machine framework from
OpenAI's metric k-median development (Apache-2.0).
Source: https://github.com/openai/math/tree/main/lean/OAI/Combinatorics/KMedian/Binary
-/

namespace QuantumMaxCutEnergy.RuntimeReuse

open OAI.MetricKMedian.Binary

def rationalHalfSum (weights : List ℚ) : ℚ := weights.sum / 2

noncomputable def rationalHalfSumProgram :
    PolyProgram (encodeList Ratio.encode) Ratio.encode rationalHalfSum :=
  (PolyProgram.ratSum.fanout
    (PolyProgram.constant (encodeList Ratio.encode) Ratio.encode 2)).comp
    PolyProgram.ratDiv

noncomputable def rationalHalfSumCertificate :
    Turing.TM2ComputableInPolyTime (encodeList Ratio.encode) Ratio.encode
      rationalHalfSum := rationalHalfSumProgram.stock


end QuantumMaxCutEnergy.RuntimeReuse




-- Local source: tm-design/EncodeBridge.lean

namespace QMCNumericRuntime

lemma encodePosNum_eq_bits (n : PosNum) :
    Computability.encodePosNum n = (n : ℕ).bits := by
  induction n with
  | one => rfl
  | bit0 n ih =>
      simp only [Computability.encodePosNum, PosNum.cast_bit0]
      rw [← two_mul, Nat.bit0_bits _ (PosNum.to_nat_pos n).ne']
      exact congrArg (List.cons false) ih
  | bit1 n ih =>
      simp only [Computability.encodePosNum, PosNum.cast_bit1]
      rw [← two_mul, Nat.bit1_bits]
      exact congrArg (List.cons true) ih

lemma encodeNum_eq_bits (n : Num) :
    Computability.encodeNum n = (n : ℕ).bits := by
  cases n with
  | zero => rfl
  | pos n => exact encodePosNum_eq_bits n

lemma encodeNat_eq_bits (n : ℕ) : Computability.encodeNat n = n.bits := by
  simpa only [Computability.encodeNat, Num.to_of_nat] using
    encodeNum_eq_bits (n : Num)

end QMCNumericRuntime




-- Local source: tm-design/WeightsList.lean

open scoped BigOperators
namespace QMCNumericRuntime
open QuantumMaxCutEnergy

def weightsList (G : Input) : List ℚ≥0 :=
  (List.finRange G.n).flatMap (fun i =>
    (List.finRange G.n).flatMap (fun j =>
      if hij : i < j then [G.weights ⟨(i, j), hij⟩] else []))

lemma sum_flatMap {α M : Type*} [AddMonoid M] (xs : List α) (f : α → List M) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  rw [List.flatMap_def, List.sum_flatten, List.map_map]
  rfl

lemma map_finRange_val (n : ℕ) :
    (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

lemma flatMap_singleton_length {α β : Type*} (xs : List α) (p : α → Prop)
    [DecidablePred p] (f : ∀ x, p x → β) :
    (xs.flatMap (fun x => if h : p x then [f x h] else [])).length =
      (xs.filter (fun x => decide (p x))).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : p a <;> simp [h, ih]

lemma sum_weightsList (G : Input) :
    (weightsList G).sum = ∑ e, G.weights e := by
  classical
  let f : Fin G.n × Fin G.n → ℚ≥0 := fun p =>
    if h : p.1 < p.2 then G.weights ⟨p, h⟩ else 0
  have hf : (∑ p, f p) = ∑ e, G.weights e := by
    apply Finset.sum_congr_set {p : Fin G.n × Fin G.n | p.1 < p.2} f G.weights
    · intro p hp
      change p.1 < p.2 at hp
      simp only [f, dif_pos hp]
    · intro p hp
      change ¬p.1 < p.2 at hp
      simp only [f, dif_neg hp]
  rw [weightsList, sum_flatMap]
  simp only [← Fin.sum_univ_def, sum_flatMap, apply_dite,
    List.sum_cons, List.sum_nil, add_zero]
  simpa only [Fintype.sum_prod_type, f] using hf

lemma encoding_weightsList (G : Input) :
    encodeInput G = List.replicate G.n true ++ [false] ++
      (weightsList G).flatMap (fun q => encodeNumber q.num ++ encodeNumber q.den) := by
  simp only [encodeInput, weightsList, List.flatMap_assoc]
  congr 1
  apply congrArg (fun f : Fin G.n → List Bool => (List.finRange G.n).flatMap f)
  funext i
  apply congrArg (fun f : Fin G.n → List Bool => (List.finRange G.n).flatMap f)
  funext j
  split_ifs <;> simp

lemma weightsList_length (G : Input) :
    (weightsList G).length =
      ((List.range G.n).flatMap (fun i =>
        (List.range G.n).filter (fun j => decide (i < j)))).length := by
  unfold weightsList
  rw [List.length_flatMap]
  simp_rw [flatMap_singleton_length]
  rw [List.length_flatMap]
  simp_rw [← map_finRange_val G.n]
  simp only [List.filter_map,
    List.length_map, List.map_map, Function.comp_def, Fin.lt_def]

end QMCNumericRuntime




-- Local source: input-parser/GraphParserSemantics.lean

/-!
The parsing operations below are adapted from the binary parser in
OpenAI's `OAI.Combinatorics.KMedian.Binary.NumericParserProgram` (Apache-2.0).
They are specialized to the campaign's actual input encoding, including
its unary graph order and its unsigned rational weights.
-/

namespace QMCNumericRuntime
open QuantumMaxCutEnergy

def bitValue : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bitValue bs

lemma bitValue_bits (n : ℕ) : bitValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn, bitValue, ih, Nat.bit_val]
      omega

def inputWidth (xs : List Bool) : ℕ := xs.findIdx Bool.not

def readNat (xs : List Bool) : ℕ × List Bool :=
  (bitValue ((xs.drop (inputWidth xs + 1)).take (inputWidth xs)),
    xs.drop (inputWidth xs + 1 + inputWidth xs))

lemma inputWidth_prefix (n : ℕ) (xs : List Bool) :
    inputWidth (List.replicate n true ++ false :: xs) = n := by
  induction n with
  | zero => simp [inputWidth, List.findIdx_cons]
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, inputWidth,
        List.findIdx_cons, Bool.not_true, Bool.cond_false]
      exact congrArg (fun k => k + 1) ih

lemma readNat_append (n : ℕ) (xs : List Bool) :
    readNat (encodeNumber n ++ xs) = (n, xs) := by
  have hb : Computability.encodeNat n = n.bits := encodeNat_eq_bits n
  have hw : inputWidth (encodeNumber n ++ xs) = n.bits.length := by
    simpa only [encodeNumber, hb, List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append] using
      inputWidth_prefix n.bits.length (n.bits ++ xs)
  unfold readNat
  rw [hw]
  have hd : (encodeNumber n ++ xs).drop (n.bits.length + 1) = n.bits ++ xs := by
    simp [encodeNumber, hb, List.drop_append, List.append_assoc]
  rw [hd]
  have ht : (encodeNumber n ++ xs).drop (n.bits.length + 1 + n.bits.length) = xs := by
    rw [← List.drop_drop, hd, List.drop_left]
  rw [ht]
  simp only [List.take_left, bitValue_bits]

lemma readNat_rest_length (xs : List Bool) : (readNat xs).2.length ≤ xs.length := by
  simp only [readNat, List.length_drop]
  omega

def readWeight (xs : List Bool) : ℚ × List Bool :=
  let a := readNat xs
  let b := readNat a.2
  (mkRat (a.1 : ℤ) b.1, b.2)

lemma readWeight_append (q : ℚ≥0) (xs : List Bool) :
    readWeight (encodeNumber q.num ++ encodeNumber q.den ++ xs) = ((q : ℚ), xs) := by
  simp only [readWeight, List.append_assoc, readNat_append]
  congr 1
  simpa only [NNRat.num_coe, NNRat.den_coe] using (q : ℚ).mkRat_num_den'

lemma readWeight_rest_length (xs : List Bool) : (readWeight xs).2.length ≤ xs.length :=
  (readNat_rest_length _).trans (readNat_rest_length _)

def encodeWeights (qs : List ℚ≥0) : List Bool :=
  qs.flatMap (fun q => encodeNumber q.num ++ encodeNumber q.den)

def parseStep (s : List Bool × List ℚ) (_ : ℕ) : List Bool × List ℚ :=
  let q := readWeight s.1
  (q.2, q.1 :: s.2)

lemma parseStep_fold_append (qs : List ℚ≥0) (slots : List ℕ)
    (hslots : slots.length = qs.length) (tail : List Bool) (acc : List ℚ) :
    slots.foldl parseStep (encodeWeights qs ++ tail, acc) =
      (tail, (qs.map (fun (q : ℚ≥0) => (q : ℚ))).reverse ++ acc) := by
  induction qs generalizing slots acc with
  | nil =>
      have hs : slots = [] := List.length_eq_zero_iff.mp hslots
      subst slots
      rfl
  | cons q qs ih =>
      cases slots with
      | nil => simp at hslots
      | cons slot slots =>
          have hl : slots.length = qs.length := by simpa using hslots
          have hprefix : encodeWeights (q :: qs) ++ tail =
              (encodeNumber q.num ++ encodeNumber q.den) ++ (encodeWeights qs ++ tail) := by
            simp only [encodeWeights, List.flatMap_cons, List.append_assoc]
          rw [List.foldl_cons, hprefix]
          simp only [parseStep, readWeight_append]
          rw [ih slots hl]
          simp [List.reverse_cons, List.append_assoc]

def parserVertices (xs : List Bool) : List ℕ :=
  (List.range xs.length).take (inputWidth xs)

def parserSlots (xs : List Bool) : List ℕ :=
  (parserVertices xs).flatMap (fun i =>
    (parserVertices xs).filter (fun j => decide (i < j)))

def parseWeights (xs : List Bool) : List ℚ :=
  ((parserSlots xs).foldl parseStep (xs.drop (inputWidth xs + 1), [])).2.reverse

lemma request_encoding (G : Input) (coins : List Bool) :
    encodeRequest (G, coins) =
      List.replicate G.n true ++ false :: (encodeWeights (weightsList G) ++ coins) := by
  simp only [encodeRequest, encoding_weightsList, encodeWeights, List.append_assoc,
    List.cons_append, List.nil_append]

lemma inputWidth_request (G : Input) (coins : List Bool) :
    inputWidth (encodeRequest (G, coins)) = G.n := by
  rw [request_encoding, inputWidth_prefix]

lemma parserVertices_request (G : Input) (coins : List Bool) :
    parserVertices (encodeRequest (G, coins)) = List.range G.n := by
  have hn : G.n ≤ (encodeRequest (G, coins)).length := by
    rw [request_encoding]
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega
  simp only [parserVertices, inputWidth_request, List.take_range, Nat.min_eq_left hn]

lemma parseWeights_request (G : Input) (coins : List Bool) :
    parseWeights (encodeRequest (G, coins)) =
      (weightsList G).map (fun (q : ℚ≥0) => (q : ℚ)) := by
  have htail : (encodeRequest (G, coins)).drop
      (inputWidth (encodeRequest (G, coins)) + 1) = encodeWeights (weightsList G) ++ coins := by
    rw [inputWidth_request, request_encoding]
    simp [List.drop_append]
  unfold parseWeights parserSlots
  rw [parserVertices_request, htail]
  rw [parseStep_fold_append (weightsList G) _ (weightsList_length G).symm coins []]
  simp only [List.append_nil, List.reverse_reverse]

lemma parseWeights_sum (G : Input) (coins : List Bool) :
    (parseWeights (encodeRequest (G, coins))).sum = ∑ e, (G.weights e : ℚ) := by
  rw [parseWeights_request]
  have h := congrArg (fun q : ℚ≥0 => (q : ℚ)) (sum_weightsList G)
  push_cast at h
  exact h

end QMCNumericRuntime




-- Local source: input-parser/GraphParserProgram.lean

namespace QMCNumericRuntime
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open Polynomial

lemma bitValue_eq_word (xs : List Bool) : bitValue xs = Word.value xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [bitValue, Word.value, ih]

@[fun_prop] theorem bitValue_poly : Poly bitValue := by
  have h : bitValue = Word.value := funext bitValue_eq_word
  rw [h]
  exact ⟨BooleanLists.valueProgram⟩

@[fun_prop] theorem parser_take_poly {α : Type} [Coding α] [Inhabited α] :
    Poly (fun x : List α × ℕ => x.1.take x.2) :=
  ⟨PolyProgram.listTake enc default⟩

@[fun_prop] theorem parser_drop_poly {α : Type} [Coding α] [Inhabited α] :
    Poly (fun x : List α × ℕ => x.1.drop x.2) :=
  ⟨PolyProgram.listDrop enc default⟩

@[fun_prop] theorem parser_reverse_poly {α : Type} [Coding α] [Inhabited α] :
    Poly (List.reverse : List α → List α) :=
  ⟨PolyProgram.listReverse enc default⟩

@[fun_prop] theorem inputWidth_poly : Poly inputWidth := by
  unfold inputWidth
  apply Poly.list_findIdx <;> fun_prop

@[fun_prop] theorem readNat_poly : Poly readNat := by
  unfold readNat
  have hd : Poly (fun xs : List Bool => xs.drop (inputWidth xs + 1)) :=
    Poly.comp (f := fun x : List Bool × ℕ => x.1.drop x.2) parser_drop_poly
      (g := fun xs : List Bool => (xs, inputWidth xs + 1)) (by fun_prop)
  have ht : Poly (fun xs : List Bool =>
      (xs.drop (inputWidth xs + 1)).take (inputWidth xs)) :=
    Poly.comp parser_take_poly (Poly.pair hd inputWidth_poly)
  exact Poly.pair (Poly.comp bitValue_poly ht)
    (Poly.comp (f := fun x : List Bool × ℕ => x.1.drop x.2) parser_drop_poly
      (g := fun xs : List Bool => (xs, inputWidth xs + 1 + inputWidth xs)) (by fun_prop))

@[fun_prop] theorem parser_signed_poly :
    Poly (fun x : Bool × ℕ => Signed.value x.1 x.2) := ⟨PolyProgram.intFromParts⟩

@[fun_prop] theorem parser_natInt_poly : Poly (fun n : ℕ => (n : ℤ)) := by
  have h : Poly (fun n : ℕ => Signed.value false n) := by fun_prop
  simpa only [Signed.value, Bool.false_eq_true, ↓reduceIte] using h

@[fun_prop] theorem parser_mkRat_poly :
    Poly (fun x : ℤ × ℕ => mkRat x.1 x.2) := ⟨PolyProgram.mkRational⟩

@[fun_prop] theorem readWeight_poly : Poly readWeight := by
  unfold readWeight
  fun_prop

noncomputable def readWeightProgram := readWeight_poly.program

noncomputable def readWeightBound : Polynomial ℕ :=
  readWeightProgram.sizeBound.comp (3 * X)

lemma booleanList_encoding_length (xs : List Bool) :
    (encodeList encodeBool xs).length = 3 * xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      simp only [EncodedList.cons_length, encodeBool,
        List.length_cons, List.length_nil, ih]
      omega

lemma readWeight_encoding_bound (xs : List Bool) :
    (Ratio.encode (readWeight xs).1).length ≤ readWeightBound.eval xs.length := by
  have h := readWeightProgram.length_bound xs
  change (encodePair Ratio.encode (encodeList encodeBool) (readWeight xs)).length ≤
    readWeightProgram.sizeBound.eval (encodeList encodeBool xs).length at h
  simp only [encodePair_length, booleanList_encoding_length] at h
  simp only [readWeightBound, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

abbrev ParserState := List Bool × List ℚ

def parserStateEncoding : ParserState → List Bool :=
  encodePair (encodeList encodeBool) (encodeList Ratio.encode)

lemma parserStateEncoding_length (s : ParserState) :
    (parserStateEncoding s).length =
      6 * s.1.length + 1 + (encodeList Ratio.encode s.2).length := by
  simp only [parserStateEncoding, encodePair_length, booleanList_encoding_length]
  omega

@[fun_prop] theorem parseStep_poly :
    Poly (fun x : ParserState × ℕ => parseStep x.1 x.2) := by
  unfold parseStep
  fun_prop

lemma parser_fold_bounds (slots : List ℕ) (xs : List Bool) (acc : List ℚ) :
    (slots.foldl parseStep (xs, acc)).1.length ≤ xs.length ∧
    (encodeList Ratio.encode (slots.foldl parseStep (xs, acc)).2).length ≤
      (encodeList Ratio.encode acc).length +
        slots.length * (2 * readWeightBound.eval xs.length + 1) := by
  induction slots generalizing xs acc with
  | nil => simp only [List.foldl_nil, List.length_nil, zero_mul, add_zero, le_refl, and_self]
  | cons slot slots ih =>
      have hr := readWeight_rest_length xs
      have hp := polynomial_eval_mono readWeightBound hr
      have hq := readWeight_encoding_bound xs
      have hi := ih (readWeight xs).2 ((readWeight xs).1 :: acc)
      constructor
      · simpa only [List.foldl_cons, parseStep] using hi.1.trans hr
      · have hm :
            slots.length * (2 * readWeightBound.eval (readWeight xs).2.length + 1) ≤
              slots.length * (2 * readWeightBound.eval xs.length + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        change (encodeList Ratio.encode
          (slots.foldl parseStep ((readWeight xs).2, (readWeight xs).1 :: acc)).2).length ≤ _
        calc
          _ ≤ (encodeList Ratio.encode ((readWeight xs).1 :: acc)).length +
              slots.length * (2 * readWeightBound.eval (readWeight xs).2.length + 1) := hi.2
          _ ≤ (encodeList Ratio.encode acc).length +
              (slot :: slots).length * (2 * readWeightBound.eval xs.length + 1) := by
            rw [EncodedList.cons_length, List.length_cons]
            nlinarith

noncomputable def parserFoldBound : Polynomial ℕ :=
  X + X * (2 * readWeightBound + 1)

lemma parser_fold_state_bound (as : List ℕ) (b : ParserState)
    (pre suf : List ℕ) (he : as = pre ++ suf) :
    (parserStateEncoding (pre.foldl parseStep b)).length ≤
      parserFoldBound.eval (encodePair (encodeList Nat.bits) parserStateEncoding (as, b)).length := by
  let N := (encodePair (encodeList Nat.bits) parserStateEncoding (as, b)).length
  have hb : (parserStateEncoding b).length ≤ N := by
    simp only [N, encodePair_length]
    omega
  have hx : b.1.length ≤ N := by
    rw [parserStateEncoding_length] at hb
    omega
  have hpre : pre.length ≤ N := by
    have hp : pre.length ≤ as.length := by rw [he, List.length_append]; omega
    have ha := EncodedList.length_le Nat.bits as
    have hc : (encodeList Nat.bits as).length ≤ N := by
      simp only [N, encodePair_length]
      omega
    omega
  have hfold :
      (pre.foldl parseStep b).1.length ≤ b.1.length ∧
        (encodeList Ratio.encode (pre.foldl parseStep b).2).length ≤
          (encodeList Ratio.encode b.2).length +
            pre.length * (2 * readWeightBound.eval b.1.length + 1) := by
    simpa only [Prod.eta] using parser_fold_bounds pre b.1 b.2
  have hgrowth : (parserStateEncoding (pre.foldl parseStep b)).length ≤
      (parserStateEncoding b).length +
        pre.length * (2 * readWeightBound.eval b.1.length + 1) := by
    rw [parserStateEncoding_length, parserStateEncoding_length]
    omega
  have hp := polynomial_eval_mono readWeightBound hx
  have hm : pre.length * (2 * readWeightBound.eval b.1.length + 1) ≤
      N * (2 * readWeightBound.eval N + 1) :=
    Nat.mul_le_mul hpre (by omega)
  change _ ≤ parserFoldBound.eval N
  simp only [parserFoldBound, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

noncomputable def parserFoldProgram :
    PolyProgram (encodePair (encodeList Nat.bits) parserStateEncoding) parserStateEncoding
      (fun x : List ℕ × ParserState => x.1.foldl parseStep x.2) :=
  parseStep_poly.program.listFold 0 parserFoldBound parser_fold_state_bound

@[fun_prop] theorem parserFold_poly :
    Poly (fun x : List ℕ × ParserState => x.1.foldl parseStep x.2) :=
  ⟨parserFoldProgram⟩

@[fun_prop] theorem parserVertices_poly : Poly parserVertices := by
  unfold parserVertices
  exact Poly.comp parser_take_poly (Poly.pair Poly.list_indices inputWidth_poly)

@[fun_prop] theorem parserSlots_poly : Poly parserSlots := by
  unfold parserSlots
  fun_prop

@[fun_prop] theorem parseWeights_poly : Poly parseWeights := by
  unfold parseWeights
  have hd : Poly (fun xs : List Bool => xs.drop (inputWidth xs + 1)) :=
    Poly.comp (f := fun x : List Bool × ℕ => x.1.drop x.2) parser_drop_poly
      (g := fun xs : List Bool => (xs, inputWidth xs + 1)) (by fun_prop)
  have hs : Poly (fun xs : List Bool => (parserSlots xs,
      (xs.drop (inputWidth xs + 1), ([] : List ℚ)))) :=
    Poly.pair parserSlots_poly (Poly.pair hd
      (OAI.MetricKMedian.Binary.Automatic.Poly.const
        (α := List Bool) (β := List ℚ) ([] : List ℚ)))
  have hf := Poly.comp parserFold_poly hs
  have ha := Poly.comp (Poly.snd (α := List Bool) (β := List ℚ)) hf
  exact
    (Poly.comp (f := fun qs : List ℚ => qs.reverse) parser_reverse_poly
      (g := fun xs : List Bool =>
        ((parserSlots xs).foldl parseStep (xs.drop (inputWidth xs + 1), [])).2) ha)

noncomputable def rawWeightsProgram :
    PolyProgram id (encodeList Ratio.encode) parseWeights :=
  BooleanLists.packProgram.comp parseWeights_poly.program

noncomputable def requestWeightsProgram :
    PolyProgram QuantumMaxCutEnergy.encodeRequest (encodeList Ratio.encode)
      (fun req : QuantumMaxCutEnergy.Input × List Bool =>
        (weightsList req.1).map (fun (q : ℚ≥0) => (q : ℚ))) :=
  rawWeightsProgram.recode QuantumMaxCutEnergy.encodeRequest
    (fun _ => rfl) (fun req => by rw [parseWeights_request])


end QMCNumericRuntime




-- Local source: input-parser/GraphEdgesProgram.lean

namespace QMCNumericRuntime
open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly

abbrev NumericEdge := (ℕ × ℕ) × ℚ

def graphEdgeList (n : ℕ) : List (Edge n) :=
  (List.finRange n).flatMap (fun i =>
    (List.finRange n).flatMap (fun j =>
      if hij : i < j then [⟨(i, j), hij⟩] else []))

def inputEdges (G : Input) : List NumericEdge :=
  (graphEdgeList G.n).map (fun e => ((e.val.1.val, e.val.2.val), (G.weights e : ℚ)))

def numericEdge (G : Input) (e : Edge G.n) : NumericEdge :=
  ((e.val.1.val, e.val.2.val), (G.weights e : ℚ))

lemma mem_graphEdgeList {n : ℕ} (e : Edge n) : e ∈ graphEdgeList n := by
  rcases e with ⟨⟨i, j⟩, hij⟩
  simp only [graphEdgeList, List.mem_flatMap]
  refine ⟨i, by simp, j, by simp, ?_⟩
  simp only [dif_pos hij, List.mem_singleton]

lemma numericEdge_injective (G : Input) : Function.Injective (numericEdge G) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun a : NumericEdge => a.1.1) h
  · apply Fin.ext
    exact congrArg (fun a : NumericEdge => a.1.2) h

lemma mem_inputEdges (G : Input) (a : NumericEdge) :
    a ∈ inputEdges G ↔ ∃ e : Edge G.n, numericEdge G e = a := by
  simp only [inputEdges, List.mem_map]
  constructor
  · rintro ⟨e, _, rfl⟩
    exact ⟨e, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e, mem_graphEdgeList e, rfl⟩

def endpointSlots (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap (fun i =>
    ((List.range n).filter (fun j => decide (i < j))).map (fun j => (i, j)))

lemma graphEdgeList_endpoints (n : ℕ) :
    (graphEdgeList n).map (fun e => (e.val.1.val, e.val.2.val)) = endpointSlots n := by
  unfold graphEdgeList endpointSlots
  simp_rw [← map_finRange_val n]
  simp only [List.map_flatMap, List.flatMap_map, List.filter_map, List.map_map,
    Function.comp_def, Fin.lt_def]
  congr 1
  funext i
  induction List.finRange n with
  | nil => rfl
  | cons j js ih =>
      by_cases hij : i < j <;> simp [hij] <;> simpa only [Fin.lt_def] using ih

lemma graphEdgeList_weights (G : Input) :
    (graphEdgeList G.n).map (fun e => G.weights e) = weightsList G := by
  unfold graphEdgeList weightsList
  simp only [List.map_flatMap]
  congr 1
  funext i
  congr 1
  funext j
  split_ifs <;> simp

lemma map_zip_map {α β γ : Type*} (xs : List α) (f : α → β) (g : α → γ) :
    (xs.map f).zip (xs.map g) = xs.map (fun x => (f x, g x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.zip_cons_cons, ih]

lemma inputEdges_zip (G : Input) :
    inputEdges G = (endpointSlots G.n).zip
      ((weightsList G).map (fun (q : ℚ≥0) => (q : ℚ))) := by
  rw [← graphEdgeList_endpoints, ← graphEdgeList_weights, List.map_map, map_zip_map]
  rfl

def parserPairs (xs : List Bool) : List (ℕ × ℕ) :=
  (parserVertices xs).flatMap (fun i =>
    ((parserVertices xs).filter (fun j => decide (i < j))).map (fun j => (i, j)))

def parseEdges (xs : List Bool) : List NumericEdge :=
  (parserPairs xs).zip (parseWeights xs)

lemma parserPairs_request (G : Input) (coins : List Bool) :
    parserPairs (encodeRequest (G, coins)) = endpointSlots G.n := by
  simp only [parserPairs, parserVertices_request, endpointSlots]

lemma parseEdges_request (G : Input) (coins : List Bool) :
    parseEdges (encodeRequest (G, coins)) = inputEdges G := by
  rw [parseEdges, parserPairs_request, parseWeights_request, inputEdges_zip]

@[fun_prop] theorem parserPairs_poly : Poly parserPairs := by
  unfold parserPairs
  fun_prop

@[fun_prop] theorem parseEdges_poly : Poly parseEdges := by
  unfold parseEdges
  exact Poly.comp Poly.list_zip (Poly.pair parserPairs_poly parseWeights_poly)

noncomputable def rawEdgesProgram :
    PolyProgram id (encodeList (encodePair (encodePair Nat.bits Nat.bits) Ratio.encode))
      parseEdges :=
  BooleanLists.packProgram.comp parseEdges_poly.program

noncomputable def requestEdgesProgram :
    PolyProgram encodeRequest
      (encodeList (encodePair (encodePair Nat.bits Nat.bits) Ratio.encode))
      (fun req : Input × List Bool => inputEdges req.1) :=
  rawEdgesProgram.recode encodeRequest
    (fun _ => rfl) (fun req => by rw [parseEdges_request])


end QMCNumericRuntime




-- Local source: input-parser/MatchingValueProgram.lean

namespace QMCNumericRuntime
open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly

def edgeWeightSum (xs : List NumericEdge) : ℚ := (xs.map Prod.snd).sum

def matchingEnergyFormula (p : List NumericEdge × List NumericEdge) : ℚ :=
  (edgeWeightSum p.1 + 3 * edgeWeightSum p.2) / 2

@[fun_prop] theorem rationalSum_poly : Poly (List.sum : List ℚ → ℚ) :=
  ⟨PolyProgram.ratSum⟩

@[fun_prop] theorem edgeWeightSum_poly : Poly edgeWeightSum := by
  unfold edgeWeightSum
  fun_prop

@[fun_prop] theorem matchingEnergyFormula_poly : Poly matchingEnergyFormula := by
  unfold matchingEnergyFormula
  fun_prop

noncomputable def matchingEnergyFormulaProgram :
    PolyProgram
      (encodePair
        (encodeList (encodePair (encodePair Nat.bits Nat.bits) Ratio.encode))
        (encodeList (encodePair (encodePair Nat.bits Nat.bits) Ratio.encode)))
      Ratio.encode matchingEnergyFormula := matchingEnergyFormula_poly.program

lemma inputEdges_weight_sum (G : Input) :
    edgeWeightSum (inputEdges G) = ∑ e, (G.weights e : ℚ) := by
  have h : (inputEdges G).map Prod.snd =
      (weightsList G).map (fun (q : ℚ≥0) => (q : ℚ)) := by
    rw [← graphEdgeList_weights]
    simp only [inputEdges, List.map_map]
    rfl
  rw [edgeWeightSum, h, ← parseWeights_request G []]
  exact parseWeights_sum G []

lemma edgeWeightSum_nonneg (xs : List NumericEdge)
    (h : ∀ e ∈ xs, 0 ≤ e.2) : 0 ≤ edgeWeightSum xs := by
  apply List.sum_nonneg
  intro q hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
  exact h e he

lemma matchingEnergyFormula_nonneg (xs ys : List NumericEdge)
    (hx : ∀ e ∈ xs, 0 ≤ e.2) (hy : ∀ e ∈ ys, 0 ≤ e.2) :
    0 ≤ matchingEnergyFormula (xs, ys) := by
  unfold matchingEnergyFormula
  exact div_nonneg (add_nonneg (edgeWeightSum_nonneg xs hx)
    (mul_nonneg (by norm_num) (edgeWeightSum_nonneg ys hy))) (by norm_num)


end QMCNumericRuntime




-- Local source: tm-design/FramingAdapter.lean

noncomputable section
open OAI.MetricKMedian.Binary
open Function Polynomial

namespace QMCNumericRuntime

/-- The self-delimiting numeric frame used by the campaign. -/
def frame (xs : List Bool) : List Bool :=
  List.replicate xs.length true ++ false :: xs

namespace Framing

def transducer : ParallelTransducer where
  Q := Unit
  initial := ()
  next _ b := ((), ([true], [b]))
  finish _ := ([false], [])

lemma run (xs : List Bool) :
    transducer.run () xs = (List.replicate xs.length true ++ [false], xs) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change (true :: (transducer.run () xs).1, b :: (transducer.run () xs).2) = _
      rw [ih]
      rfl

def program : PolyProgram id id frame :=
  transducer.program.congr _ (fun xs => by
    change (transducer.run () xs).1 ++ (transducer.run () xs).2 = frame xs
    rw [run]
    simp only [frame, List.append_assoc, List.singleton_append])

def numberProgram : PolyProgram Nat.bits id (fun n : ℕ => frame n.bits) :=
  program.of_word (fun _ => rfl)

end Framing

namespace AppendPair

abbrev transducer : Transducer where
  Q := Fin 3
  initial := 0
  next q b := if q = 0 then (if b then 1 else 2, [])
    else if q = 1 then (0, [b]) else (2, [b])
  finish _ := []

lemma run_tail (ys : List Bool) : transducer.run 2 ys = ys := by
  induction ys with
  | nil => rfl
  | cons b ys ih =>
      change b :: transducer.run 2 ys = b :: ys
      rw [ih]

lemma run_pair (xs ys : List Bool) :
    transducer.run 0 (quote xs ++ ys) = xs ++ ys := by
  induction xs with
  | nil => exact run_tail ys
  | cons b xs ih =>
      change b :: transducer.run 0 (quote xs ++ ys) = b :: (xs ++ ys)
      rw [ih]

def program : PolyProgram (encodePair id id) id (fun p : List Bool × List Bool => p.1 ++ p.2) :=
  transducer.program.of_word (fun p => by
    simpa only [encodePair, id_eq] using run_pair p.1 p.2)

end AppendPair

end QMCNumericRuntime

end


-- Local source: tm-design/OutputAdapter.lean

noncomputable section
open OAI.MetricKMedian.Binary
open Function Polynomial

namespace QMCNumericRuntime

/-- Converts a classical rational representation to two campaign numeric frames. -/
def rationalOutput : PolyProgram Ratio.encode id
    (fun q : ℚ => frame q.num.natAbs.bits ++ frame q.den.bits) := by
  let pn := (PolyProgram.ratNum.comp PolyProgram.intAbs).comp Framing.numberProgram
  let pd := PolyProgram.ratDen.comp Framing.numberProgram
  exact ((pn.fanout pd).comp AppendPair.program).congr _ (fun _ => rfl)

/-- No normalization is performed here: the upstream arithmetic already returns
canonical numerator/denominator, and this adapter only changes their framing. -/
def nnratOutputFrames : PolyProgram (fun q : ℚ≥0 => Ratio.encode (q : ℚ)) id
    (fun q : ℚ≥0 => frame q.num.bits ++ frame q.den.bits) :=
  rationalOutput.recode (fun q : ℚ≥0 => (q : ℚ)) (fun _ => rfl) (fun q => by
    simp only [NNRat.natAbs_num_coe, NNRat.den_coe])

/-- A genuine polynomial-time conversion into the campaign's exact output encoding. -/
def nnratOutput : PolyProgram (fun q : ℚ≥0 => Ratio.encode (q : ℚ))
    QuantumMaxCutEnergy.encodeValue (fun q => q) :=
  rationalOutput.recode (fun q : ℚ≥0 => (q : ℚ)) (fun _ => rfl) (fun q => by
    simp only [NNRat.natAbs_num_coe, NNRat.den_coe,
      QuantumMaxCutEnergy.encodeValue, QuantumMaxCutEnergy.encodeNumber,
      encodeNat_eq_bits, frame, id_eq, List.append_assoc, List.cons_append,
      List.nil_append])

end QMCNumericRuntime

end


-- Local source: AnalyticProof.lean

noncomputable section
open scoped BigOperators
namespace QuantumMaxCutEnergy

def totalWeight {n : ℕ} (w : Weights n) : ℝ := ∑ e, (w e : ℝ)

lemma normSq_sub_bound (z v : ℂ) :
    Complex.normSq (z - v) ≤ 2 * Complex.normSq z + 2 * Complex.normSq v := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (z.re + v.re), sq_nonneg (z.im + v.im)]

def swapBasis {n : ℕ} (a b : Fin n) : Basis n ≃ Basis n where
  toFun x := x ∘ Equiv.swap a b
  invFun x := x ∘ Equiv.swap a b
  left_inv x := by funext i; simp [Function.comp_def]
  right_inv x := by funext i; simp [Function.comp_def]

lemma squaredNorm_swap_sum {n : ℕ} (ψ : Wave n) (a b : Fin n) :
    (∑ x, Complex.normSq (ψ (x ∘ Equiv.swap a b))) = squaredNorm ψ := by
  exact (swapBasis a b).sum_comp (fun x => Complex.normSq (ψ x))

lemma energy_nonnegative {n : ℕ} (w : Weights n)
    (ψ : Wave n) : 0 ≤ energy w ψ := by
  apply Finset.sum_nonneg
  intro e _
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg (fun x _ => Complex.normSq_nonneg _)

lemma energy_upper_bound {n : ℕ} (w : Weights n)
    (ψ : Wave n) :
    energy w ψ ≤ 2 * totalWeight w * squaredNorm ψ := by
  have edge_bound (a b : Fin n) :
      (∑ x, Complex.normSq (ψ x - ψ (x ∘ Equiv.swap a b))) ≤ 4 * squaredNorm ψ := by
    calc
      _ ≤ ∑ x, (2 * Complex.normSq (ψ x) +
            2 * Complex.normSq (ψ (x ∘ Equiv.swap a b))) :=
        Finset.sum_le_sum (fun x _ => normSq_sub_bound _ _)
      _ = 4 * squaredNorm ψ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          squaredNorm_swap_sum]
        unfold squaredNorm
        ring
  calc
    energy w ψ ≤ ∑ e, (w e : ℝ) / 2 * (4 * squaredNorm ψ) := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left (edge_bound _ _) (by positivity)
    _ = ∑ e, (w e : ℝ) * (2 * squaredNorm ψ) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = 2 * totalWeight w * squaredNorm ψ := by
      rw [← Finset.sum_mul]
      unfold totalWeight
      ring

end QuantumMaxCutEnergy

namespace QuantumMaxCutEnergy.BaselineSemantic

def ket {n : ℕ} (b : Basis n) : Wave n := fun x => if x = b then 1 else 0

def cutWeight {n : ℕ} (w : Weights n) (b : Basis n) : ℝ :=
  ∑ e, if b e.val.1 = b e.val.2 then 0 else (w e : ℝ)

lemma squaredNorm_ket {n : ℕ} (b : Basis n) : squaredNorm (ket b) = 1 := by
  classical
  simp [squaredNorm, ket]

lemma sum_delta_difference {α : Type} [Fintype α] [DecidableEq α] (a b : α) :
    (∑ x, Complex.normSq
      ((if x = a then (1 : ℂ) else 0) - (if x = b then (1 : ℂ) else 0))) =
      if a = b then 0 else 2 := by
  classical
  by_cases h : a = b
  · subst b
    simp
  · have hp : ∀ x, Complex.normSq
        ((if x = a then (1 : ℂ) else 0) - (if x = b then (1 : ℂ) else 0)) =
        (if x = a then (1 : ℝ) else 0) + (if x = b then (1 : ℝ) else 0) := by
      intro x
      by_cases ha : x = a
      · subst x
        simp [h]
      · by_cases hb : x = b
        · subst x
          simp [Ne.symm h]
        · simp [ha, hb]
    simp_rw [hp]
    rw [Finset.sum_add_distrib]
    norm_num [h]

lemma ket_swap {n : ℕ} (b x : Basis n) (i j : Fin n) :
    ket b (x ∘ Equiv.swap i j) = ket (b ∘ Equiv.swap i j) x := by
  classical
  have h : (x ∘ Equiv.swap i j = b) ↔ (x = b ∘ Equiv.swap i j) := by
    constructor <;> intro h
    · have hh := congrArg (fun f => f ∘ Equiv.swap i j) h
      simpa only [Function.comp_def, Equiv.swap_apply_self] using hh
    · subst x
      funext k
      simp [Function.comp_def]
  simp only [ket, h]

lemma eq_swap_iff {n : ℕ} (b : Basis n) (i j : Fin n) :
    (b = b ∘ Equiv.swap i j) ↔ b i = b j := by
  constructor
  · intro h
    simpa using congrFun h i
  · intro h
    funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [Equiv.swap_apply_def]

lemma pairEnergy_ket {n : ℕ} (b : Basis n) (i j : Fin n) :
    (∑ x, Complex.normSq (ket b x - ket b (x ∘ Equiv.swap i j))) =
      if b i = b j then 0 else 2 := by
  simp_rw [ket_swap]
  change (∑ x, Complex.normSq
    ((if x = b then (1 : ℂ) else 0) -
      (if x = b ∘ Equiv.swap i j then (1 : ℂ) else 0))) = _
  rw [sum_delta_difference]
  simp only [eq_swap_iff]

lemma energy_ket {n : ℕ} (w : Weights n) (b : Basis n) :
    energy w (ket b) = cutWeight w b := by
  classical
  unfold energy cutWeight
  apply Finset.sum_congr rfl
  intro e _
  change (w e : ℝ) / 2 *
    (∑ x, Complex.normSq (ket b x - ket b (x ∘ Equiv.swap e.val.1 e.val.2))) = _
  rw [pairEnergy_ket]
  split_ifs <;> ring

def flipBit {n : ℕ} (i : Fin n) (b : Basis n) : Basis n :=
  Function.update b i (!(b i))

lemma flipBit_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flipBit i) := by
  intro b
  funext k
  by_cases hk : k = i
  · subst k
    simp [flipBit]
  · simp [flipBit, hk]

lemma uniform_cut_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (∑ b : Basis n, if b i = b j then (0 : ℝ) else 1) =
      (Fintype.card (Basis n) : ℝ) / 2 := by
  classical
  let f : Basis n → ℝ := fun b => if b i = b j then 0 else 1
  have hflip (b : Basis n) : f (flipBit i b) = 1 - f b := by
    simp only [f, flipBit, Function.update_self,
      Function.update_of_ne (Ne.symm hij)]
    cases hi : b i <;> cases hj : b j <;> norm_num
  have hs : (∑ b, f b) = ∑ b : Basis n, (1 - f b) := by
    calc
      (∑ b, f b) = ∑ b, f (flipBit i b) :=
        ((flipBit_involutive i).bijective.sum_comp f).symm
      _ = _ := by simp_rw [hflip]
  rw [Finset.sum_sub_distrib] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  change (∑ b, f b) = _
  linarith

lemma uniform_cut_sum {n : ℕ} (w : Weights n) :
    (∑ b : Basis n, cutWeight w b) =
      (Fintype.card (Basis n) : ℝ) / 2 * ∑ e, (w e : ℝ) := by
  classical
  unfold cutWeight
  rw [Finset.sum_comm]
  calc
    (∑ e, ∑ b : Basis n, if b e.val.1 = b e.val.2 then 0 else (w e : ℝ)) =
        ∑ e, (w e : ℝ) * ((Fintype.card (Basis n) : ℝ) / 2) := by
      apply Finset.sum_congr rfl
      intro e _
      have h := uniform_cut_pair e.val.1 e.val.2 (ne_of_lt e.property)
      rw [← h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> ring
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma uniform_basis_energy_sum {n : ℕ} (w : Weights n) :
    (∑ b : Basis n, energy w (ket b)) =
      (Fintype.card (Basis n) : ℝ) / 2 * ∑ e, (w e : ℝ) := by
  simp_rw [energy_ket]
  exact uniform_cut_sum w

def uniformBasisEnergy {n : ℕ} (w : Weights n) : ℝ :=
  (∑ b : Basis n, energy w (ket b)) /
    (Fintype.card (Basis n) : ℝ)

lemma uniformBasisEnergy_eq {n : ℕ} (w : Weights n) :
    uniformBasisEnergy w = (∑ e, (w e : ℝ)) / 2 := by
  have hcard : (Fintype.card (Basis n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniformBasisEnergy
  rw [uniform_basis_energy_sum]
  field_simp

lemma uniformBasis_quarter_of_upper {n : ℕ} (w : Weights n) (ψ : Wave n)
    (hψ : squaredNorm ψ = 1)
    (hupper : energy w ψ ≤
      2 * (∑ e, (w e : ℝ)) * squaredNorm ψ) :
    (1 / 4 : ℝ) * energy w ψ ≤
      uniformBasisEnergy w := by
  rw [uniformBasisEnergy_eq]
  rw [hψ] at hupper
  linarith

end QuantumMaxCutEnergy.BaselineSemantic

namespace QuantumMaxCutEnergy

open BaselineSemantic

lemma energy_values_nonempty (G : Input) :
    {v : ℝ | ∃ ψ : Wave G.n, squaredNorm ψ = 1 ∧ v = energy G.weights ψ}.Nonempty := by
  refine ⟨_, _, squaredNorm_ket (fun _ => false), rfl⟩

lemma energy_values_bddAbove (G : Input) :
    BddAbove {v : ℝ | ∃ ψ : Wave G.n, squaredNorm ψ = 1 ∧ v = energy G.weights ψ} := by
  refine ⟨2 * totalWeight G.weights, ?_⟩
  rintro v ⟨ψ, hψ, rfl⟩
  simpa [hψ] using energy_upper_bound G.weights ψ

lemma energy_le_optimum (G : Input) (ψ : Wave G.n) (hψ : squaredNorm ψ = 1) :
    energy G.weights ψ ≤ optimum G := by
  exact le_csSup (energy_values_bddAbove G) ⟨ψ, hψ, rfl⟩

lemma optimum_le_two_totalWeight (G : Input) :
    optimum G ≤ 2 * totalWeight G.weights := by
  apply csSup_le (energy_values_nonempty G)
  rintro v ⟨ψ, hψ, rfl⟩
  simpa [hψ] using energy_upper_bound G.weights ψ

lemma half_totalWeight_le_optimum (G : Input) :
    totalWeight G.weights / 2 ≤ optimum G := by
  have hcard : (0 : ℝ) < (Fintype.card (Basis G.n) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have havg : uniformBasisEnergy G.weights ≤ optimum G := by
    unfold uniformBasisEnergy
    apply (div_le_iff₀ hcard).2
    calc
      (∑ b : Basis G.n, energy G.weights (ket b)) ≤
          ∑ _b : Basis G.n, optimum G := by
        exact Finset.sum_le_sum (fun b _ => energy_le_optimum G (ket b) (squaredNorm_ket b))
      _ = optimum G * (Fintype.card (Basis G.n) : ℝ) := by
        simp [mul_comm]
  simpa [uniformBasisEnergy_eq, totalWeight] using havg

lemma quarter_optimum_le_half_totalWeight (G : Input) :
    (0.25 : ℝ) * optimum G ≤ totalWeight G.weights / 2 := by
  have h := optimum_le_two_totalWeight G
  linarith

def quarterValue (G : Input) : ℚ≥0 := (∑ e, G.weights e) / 2

lemma quarterValue_cast (G : Input) :
    (quarterValue G : ℝ) = totalWeight G.weights / 2 := by
  simp [quarterValue, totalWeight, NNRat.cast_sum]

def quarterEstimator : Algorithm where
  randomFactor := 0
  randomDegree := 0
  run G _ := quarterValue G

theorem quarterEstimator_ratio : ApproximationRatio quarterEstimator (0.25 : ℝ) := by
  intro G
  constructor
  · intro r
    simpa [quarterEstimator, quarterValue_cast] using half_totalWeight_le_optimum G
  · have hcard : (Fintype.card (Fin (randomBits quarterEstimator G) → Bool) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    change (0.25 : ℝ) * optimum G ≤
      (∑ _r : Fin (randomBits quarterEstimator G) → Bool, (quarterValue G : ℝ)) /
        (Fintype.card (Fin (randomBits quarterEstimator G) → Bool) : ℝ)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_div_cancel_left₀ _ hcard]
    simpa only [quarterValue_cast] using quarter_optimum_le_half_totalWeight G


end QuantumMaxCutEnergy


end


-- Local source: next-half/Antisymmetrizer.lean

noncomputable section
namespace QuantumMaxCutEnergy.Star

def swapWave {n : ℕ} (a b : Fin n) (ψ : Wave n) : Wave n :=
  fun x => ψ (x ∘ Equiv.swap a b)

def edgeAction {n : ℕ} (a b : Fin n) (ψ : Wave n) : Wave n :=
  ψ - swapWave a b ψ

lemma same_swap {α β : Type*} [DecidableEq α] (x : α → β) (a b : α)
    (h : x a = x b) : x ∘ Equiv.swap a b = x := by
  funext k
  by_cases hka : k = a <;> by_cases hkb : k = b <;>
    simp_all [Function.comp_apply, Equiv.swap_apply_def]

lemma cross_same_center {α β : Type*} [DecidableEq α] (x : α → β)
    (c i j : α) (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j)
    (h : x c = x i) :
    (x ∘ Equiv.swap c j) ∘ Equiv.swap c i = x ∘ Equiv.swap i j := by
  have hic : i ≠ c := hci.symm
  have hjc : j ≠ c := hcj.symm
  have hji : j ≠ i := hij.symm
  funext k
  by_cases hkc : k = c <;> by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [Function.comp_apply, Equiv.swap_apply_def]

lemma cross_same_leaves {α β : Type*} [DecidableEq α] (x : α → β)
    (c i j : α) (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j)
    (h : x i = x j) :
    (x ∘ Equiv.swap c i) ∘ Equiv.swap c j = x ∘ Equiv.swap c i := by
  have hic : i ≠ c := hci.symm
  have hjc : j ≠ c := hcj.symm
  have hji : j ≠ i := hij.symm
  funext k
  by_cases hkc : k = c <;> by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [Function.comp_apply, Equiv.swap_apply_def]

lemma bool_three_equal (a b c : Bool) : a = b ∨ a = c ∨ b = c := by
  cases a <;> cases b <;> cases c <;> simp

/-- The three-qubit antisymmetrizer vanishes because a Boolean basis string
has equal bits at two of the three positions. -/
lemma antisymmetrizer_pointwise {n : ℕ} (ψ : Wave n) (x : Basis n)
    (c i j : Fin n) (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j) :
    ψ x - swapWave c i ψ x - swapWave c j ψ x - swapWave i j ψ x +
      swapWave c i (swapWave c j ψ) x +
      swapWave c j (swapWave c i ψ) x = 0 := by
  rcases bool_three_equal (x c) (x i) (x j) with h | h | h
  · have hs := same_swap x c i h
    have ht := cross_same_center x c i j hci hcj hij h
    simp only [swapWave, hs, ht]
    ring
  · have hs := same_swap x c j h
    have ht := cross_same_center x c j i hcj hci hij.symm h
    have ht' : (x ∘ Equiv.swap c i) ∘ Equiv.swap c j = x ∘ Equiv.swap i j := by
      simpa only [Equiv.swap_comm j i] using ht
    simp only [swapWave, hs, ht']
    ring
  · have hs := same_swap x i j h
    have ht := cross_same_leaves x c i j hci hcj hij h
    have hu := cross_same_leaves x c j i hcj hci hij.symm h.symm
    simp only [swapWave, hs, ht, hu]
    ring

theorem antisymmetrizer {n : ℕ} (ψ : Wave n)
    (c i j : Fin n) (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j) :
    ψ - swapWave c i ψ - swapWave c j ψ - swapWave i j ψ +
      swapWave c i (swapWave c j ψ) +
      swapWave c j (swapWave c i ψ) = 0 := by
  funext x
  exact antisymmetrizer_pointwise ψ x c i j hci hcj hij

/-- In the QMC convention h=I-SWAP, products of two edges with a shared
center reduce to three edge operators. -/
theorem shared_center_anticommutator {n : ℕ} (ψ : Wave n)
    (c i j : Fin n) (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j) :
    edgeAction c i (edgeAction c j ψ) + edgeAction c j (edgeAction c i ψ) =
      edgeAction c i ψ + edgeAction c j ψ - edgeAction i j ψ := by
  funext x
  have h := antisymmetrizer_pointwise ψ x c i j hci hcj hij
  simp only [edgeAction, swapWave, Pi.add_apply, Pi.sub_apply] at h ⊢
  linear_combination h

end QuantumMaxCutEnergy.Star

end


-- Local source: next-half/RealInner.lean

noncomputable section
namespace QuantumMaxCutEnergy.Star

def swapBasis {n : ℕ} (a b : Fin n) : Basis n ≃ Basis n where
  toFun x := x ∘ Equiv.swap a b
  invFun x := x ∘ Equiv.swap a b
  left_inv x := by funext i; simp [Function.comp_def]
  right_inv x := by funext i; simp [Function.comp_def]

/-- The real part of the usual inner product, written as a finite real sum. -/
def realInner {n : ℕ} (ψ φ : Wave n) : ℝ :=
  ∑ x, ((ψ x).re * (φ x).re + (ψ x).im * (φ x).im)

def realScale {n : ℕ} (a : ℝ) (ψ : Wave n) : Wave n :=
  fun x => (a : ℂ) * ψ x

lemma realInner_comm {n : ℕ} (ψ φ : Wave n) :
    realInner ψ φ = realInner φ ψ := by
  unfold realInner
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma realInner_self {n : ℕ} (ψ : Wave n) :
    realInner ψ ψ = squaredNorm ψ := by
  unfold realInner squaredNorm
  apply Finset.sum_congr rfl
  intro x _
  simp [Complex.normSq_apply]

lemma realInner_nonneg {n : ℕ} (ψ : Wave n) : 0 ≤ realInner ψ ψ := by
  rw [realInner_self]
  exact Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _

@[simp] lemma realInner_zero_right {n : ℕ} (ψ : Wave n) : realInner ψ 0 = 0 := by
  simp [realInner]

lemma realInner_add_right {n : ℕ} (ψ φ χ : Wave n) :
    realInner ψ (φ + χ) = realInner ψ φ + realInner ψ χ := by
  unfold realInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Pi.add_apply, Complex.add_re, Complex.add_im]
  ring

lemma realInner_sub_right {n : ℕ} (ψ φ χ : Wave n) :
    realInner ψ (φ - χ) = realInner ψ φ - realInner ψ χ := by
  unfold realInner
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Pi.sub_apply, Complex.sub_re, Complex.sub_im]
  ring

lemma realInner_add_left {n : ℕ} (ψ φ χ : Wave n) :
    realInner (ψ + φ) χ = realInner ψ χ + realInner φ χ := by
  rw [realInner_comm, realInner_add_right]
  congr 1 <;> exact realInner_comm _ _

lemma realInner_sub_left {n : ℕ} (ψ φ χ : Wave n) :
    realInner (ψ - φ) χ = realInner ψ χ - realInner φ χ := by
  rw [realInner_comm, realInner_sub_right]
  congr 1 <;> exact realInner_comm _ _

lemma realInner_scale_right {n : ℕ} (a : ℝ) (ψ φ : Wave n) :
    realInner ψ (realScale a φ) = a * realInner ψ φ := by
  unfold realInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [realScale, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

lemma realInner_scale_left {n : ℕ} (a : ℝ) (ψ φ : Wave n) :
    realInner (realScale a ψ) φ = a * realInner ψ φ := by
  rw [realInner_comm, realInner_scale_right, realInner_comm φ ψ]

lemma realInner_sum_right {n : ℕ} {ι : Type*} (s : Finset ι)
    (ψ : Wave n) (φ : ι → Wave n) :
    realInner ψ (∑ i ∈ s, φ i) = ∑ i ∈ s, realInner ψ (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, realInner_add_right, ih]

lemma realInner_sum_left {n : ℕ} {ι : Type*} (s : Finset ι)
    (ψ : ι → Wave n) (φ : Wave n) :
    realInner (∑ i ∈ s, ψ i) φ = ∑ i ∈ s, realInner (ψ i) φ := by
  rw [realInner_comm, realInner_sum_right]
  apply Finset.sum_congr rfl
  intro i _
  exact realInner_comm _ _

lemma swapWave_twice {n : ℕ} (a b : Fin n) (ψ : Wave n) :
    swapWave a b (swapWave a b ψ) = ψ := by
  funext x
  simp [swapWave, Function.comp_def]

lemma swapWave_adjoint {n : ℕ} (a b : Fin n) (ψ φ : Wave n) :
    realInner (swapWave a b ψ) φ = realInner ψ (swapWave a b φ) := by
  unfold realInner
  have h := (swapBasis a b).sum_comp
    (fun x => (ψ x).re * (swapWave a b φ x).re +
      (ψ x).im * (swapWave a b φ x).im)
  simpa [swapBasis, swapWave, Function.comp_def] using h

lemma edgeAction_adjoint {n : ℕ} (a b : Fin n) (ψ φ : Wave n) :
    realInner (edgeAction a b ψ) φ = realInner ψ (edgeAction a b φ) := by
  simp only [edgeAction, realInner_sub_left, realInner_sub_right, swapWave_adjoint]

lemma edgeAction_twice {n : ℕ} (a b : Fin n) (ψ : Wave n) :
    edgeAction a b (edgeAction a b ψ) = realScale 2 (edgeAction a b ψ) := by
  funext x
  simp only [edgeAction, swapWave, Pi.sub_apply, realScale]
  have hs : (x ∘ Equiv.swap a b) ∘ Equiv.swap a b = x := by
    funext i
    simp [Function.comp_def]
  rw [hs]
  push_cast
  ring

def pairEnergy {n : ℕ} (a b : Fin n) (ψ : Wave n) : ℝ :=
  realInner ψ (edgeAction a b ψ)

lemma edgeAction_squaredNorm {n : ℕ} (a b : Fin n) (ψ : Wave n) :
    squaredNorm (edgeAction a b ψ) = 2 * pairEnergy a b ψ := by
  rw [← realInner_self, edgeAction_adjoint, edgeAction_twice,
    realInner_scale_right, pairEnergy]

lemma pairEnergy_nonneg {n : ℕ} (a b : Fin n) (ψ : Wave n) :
    0 ≤ pairEnergy a b ψ := by
  have h := realInner_nonneg (edgeAction a b ψ)
  rw [realInner_self, edgeAction_squaredNorm] at h
  linarith

lemma pairEnergy_eq {n : ℕ} (a b : Fin n) (ψ : Wave n) :
    pairEnergy a b ψ = (∑ x, Complex.normSq
      (ψ x - ψ (x ∘ Equiv.swap a b))) / 2 := by
  have h := edgeAction_squaredNorm a b ψ
  unfold squaredNorm edgeAction swapWave at h
  simp only [Pi.sub_apply] at h
  linarith

lemma shared_center_inner {n : ℕ} (ψ : Wave n) (c i j : Fin n)
    (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j) :
    2 * realInner (edgeAction c i ψ) (edgeAction c j ψ) =
      pairEnergy c i ψ + pairEnergy c j ψ - pairEnergy i j ψ := by
  have h := congrArg (realInner ψ)
    (shared_center_anticommutator ψ c i j hci hcj hij)
  simp only [realInner_add_right, realInner_sub_right] at h
  rw [← edgeAction_adjoint c i ψ (edgeAction c j ψ),
    ← edgeAction_adjoint c j ψ (edgeAction c i ψ)] at h
  have hc := realInner_comm (edgeAction c j ψ) (edgeAction c i ψ)
  unfold pairEnergy
  linarith

end QuantumMaxCutEnergy.Star

end


-- Local source: next-half/WeightedStar.lean

noncomputable section
namespace QuantumMaxCutEnergy.Star

lemma edge_inner_le {n : ℕ} (ψ : Wave n) (c i j : Fin n)
    (hci : c ≠ i) (hcj : c ≠ j) :
    realInner (edgeAction c i ψ) (edgeAction c j ψ) ≤
      (pairEnergy c i ψ + pairEnergy c j ψ) / 2 +
        if i = j then pairEnergy c i ψ else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [realInner_self, edgeAction_squaredNorm]
    simp only [ite_true]
    linarith
  · have h := shared_center_inner ψ c i j hci hcj hij
    have hp := pairEnergy_nonneg i j ψ
    rw [if_neg hij]
    linarith

/-- A finite algebra identity used to sum the two-edge estimate. -/
lemma weighted_pair_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w e : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j *
      ((e i + e j) / 2 + if i = j then e i else 0)) =
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * e i) +
        ∑ i ∈ s, w i * w i * e i := by
  have hrow (i : ι) (hi : i ∈ s) :
      (∑ j ∈ s, w i * w j *
        ((e i + e j) / 2 + if i = j then e i else 0)) =
        (w i * e i * (∑ j ∈ s, w j) +
          w i * (∑ j ∈ s, w j * e j)) / 2 + w i * w i * e i := by
    calc
      _ = (∑ j ∈ s, (w i * e i * w j + w i * (w j * e j)) / 2) +
          ∑ j ∈ s, if i = j then w i * w i * e i else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs with h
        · subst j
          ring
        · ring
      _ = _ := by
        rw [← Finset.sum_div, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
        simp [hi]
  calc
    _ = ∑ i ∈ s, ((w i * e i * (∑ j ∈ s, w j) +
        w i * (∑ j ∈ s, w j * e j)) / 2 + w i * w i * e i) := by
      apply Finset.sum_congr rfl
      exact hrow
    _ = _ := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul]
      ring

def starAction {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) : Wave n :=
  ∑ i ∈ s, realScale (w i) (edgeAction c i ψ)

def starEnergy {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) : ℝ :=
  ∑ i ∈ s, w i * pairEnergy c i ψ

lemma starEnergy_nonneg {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ starEnergy c s w ψ := by
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (pairEnergy_nonneg c i ψ)

lemma starAction_inner {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) :
    realInner ψ (starAction c s w ψ) = starEnergy c s w ψ := by
  unfold starAction starEnergy
  rw [realInner_sum_right]
  simp only [realInner_scale_right, pairEnergy]

lemma starAction_squaredNorm {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) :
    squaredNorm (starAction c s w ψ) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j *
        realInner (edgeAction c i ψ) (edgeAction c j ψ) := by
  rw [← realInner_self]
  unfold starAction
  rw [realInner_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [realInner_sum_right]
  apply Finset.sum_congr rfl
  intro j hj
  rw [realInner_scale_left, realInner_scale_right]
  ring

lemma starAction_norm_bound {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) (M : ℝ)
    (hc : c ∉ s) (hw : ∀ i ∈ s, 0 ≤ w i) (hM : ∀ i ∈ s, w i ≤ M) :
    squaredNorm (starAction c s w ψ) ≤
      ((∑ i ∈ s, w i) + M) * starEnergy c s w ψ := by
  classical
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j *
        ((pairEnergy c i ψ + pairEnergy c j ψ) / 2 +
          if i = j then pairEnergy c i ψ else 0) := by
      rw [starAction_squaredNorm]
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hw i hi) (hw j hj))
      apply edge_inner_le ψ c i j
      · exact fun h => hc (h ▸ hi)
      · exact fun h => hc (h ▸ hj)
    _ = (∑ i ∈ s, w i) * starEnergy c s w ψ +
        ∑ i ∈ s, w i * w i * pairEnergy c i ψ :=
      weighted_pair_sum s w (fun i => pairEnergy c i ψ)
    _ ≤ (∑ i ∈ s, w i) * starEnergy c s w ψ + M * starEnergy c s w ψ := by
      apply add_le_add_right
      unfold starEnergy
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [mul_nonneg (hw i hi) (pairEnergy_nonneg c i ψ),
        mul_le_mul_of_nonneg_right (hM i hi)
          (mul_nonneg (hw i hi) (pairEnergy_nonneg c i ψ))]
    _ = _ := by ring

lemma inner_sq_le_squaredNorm {n : ℕ} (ψ φ : Wave n) (hψ : squaredNorm ψ = 1) :
    realInner ψ φ ^ 2 ≤ squaredNorm φ := by
  have h := realInner_nonneg (φ - realScale (realInner ψ φ) ψ)
  simp only [realInner_sub_left, realInner_sub_right,
    realInner_scale_left, realInner_scale_right] at h
  rw [realInner_comm φ ψ, realInner_self ψ, hψ, realInner_self φ] at h
  nlinarith

/-- A nonnegative weighted QMC star has largest energy at most the total
incident weight plus an upper bound for its largest edge weight. -/
theorem weighted_star_upper_bound {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) (M : ℝ)
    (hc : c ∉ s) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hM0 : 0 ≤ M) (hM : ∀ i ∈ s, w i ≤ M) (hψ : squaredNorm ψ = 1) :
    starEnergy c s w ψ ≤ (∑ i ∈ s, w i) + M := by
  have hnorm := starAction_norm_bound c s w ψ M hc hw hM
  have hcs := inner_sq_le_squaredNorm ψ (starAction c s w ψ) hψ
  rw [starAction_inner] at hcs
  have hpos := starEnergy_nonneg c s w ψ hw
  have hwpos : 0 ≤ (∑ i ∈ s, w i) + M :=
    add_nonneg (Finset.sum_nonneg hw) hM0
  nlinarith

/-- The same star bound expressed directly in the campaign's energy convention. -/
theorem weighted_star_energy_upper_bound {n : ℕ} (c : Fin n) (s : Finset (Fin n))
    (w : Fin n → ℝ) (ψ : Wave n) (M : ℝ)
    (hc : c ∉ s) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hM0 : 0 ≤ M) (hM : ∀ i ∈ s, w i ≤ M) (hψ : squaredNorm ψ = 1) :
    (∑ i ∈ s, w i / 2 * (∑ x, Complex.normSq
      (ψ x - ψ (x ∘ Equiv.swap c i)))) ≤ (∑ i ∈ s, w i) + M := by
  convert weighted_star_upper_bound c s w ψ M hc hw hM0 hM hψ using 1
  unfold starEnergy
  apply Finset.sum_congr rfl
  intro i hi
  rw [pairEnergy_eq]
  ring

end QuantumMaxCutEnergy.Star

end


-- Local source: next-half/StarCover.lean

noncomputable section
namespace QuantumMaxCutEnergy.Star

lemma pairEnergy_comm {n : ℕ} (i j : Fin n) (ψ : Wave n) :
    pairEnergy i j ψ = pairEnergy j i ψ := by
  have hs : swapWave i j ψ = swapWave j i ψ := by
    funext x
    simp only [swapWave, Equiv.swap_comm i j]
  simp only [pairEnergy, edgeAction, hs]

@[simp] lemma pairEnergy_self {n : ℕ} (i : Fin n) (ψ : Wave n) :
    pairEnergy i i ψ = 0 := by
  have hs : swapWave i i ψ = ψ := by
    funext x
    simp [swapWave]
  simp [pairEnergy, edgeAction, hs]

lemma energy_eq_pairEnergy {n : ℕ} (w : Weights n) (ψ : Wave n) :
    energy w ψ = ∑ e, (w e : ℝ) * pairEnergy e.val.1 e.val.2 ψ := by
  unfold energy
  apply Finset.sum_congr rfl
  intro e he
  rw [pairEnergy_eq]
  ring

lemma sum_ordered_pairs {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, if i < j then f i j else 0) =
      ∑ e : Edge n, f e.val.1 e.val.2 := by
  classical
  let g : Fin n × Fin n → ℝ := fun p => if p.1 < p.2 then f p.1 p.2 else 0
  have hg : (∑ p, g p) = ∑ e : Edge n, f e.val.1 e.val.2 := by
    apply Finset.sum_congr_set {p : Fin n × Fin n | p.1 < p.2} g
      (fun e : Edge n => f e.val.1 e.val.2)
    · intro p hp
      change p.1 < p.2 at hp
      simp only [g, if_pos hp]
    · intro p hp
      change ¬p.1 < p.2 at hp
      simp only [g, if_neg hp]
  simpa only [Fintype.sum_prod_type, g] using hg

lemma sum_off_diagonal {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = ∑ e : Edge n,
      (f e.val.1 e.val.2 + f e.val.2 e.val.1) := by
  classical
  have hsplit : (∑ i, ∑ j, f i j) =
      (∑ i, ∑ j, if i < j then f i j else 0) +
        ∑ i, ∑ j, if j < i then f i j else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j
      simp [hdiag]
    · simp [h, not_lt_of_gt h]
  rw [hsplit]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  rw [sum_ordered_pairs, sum_ordered_pairs, ← Finset.sum_add_distrib]

lemma oriented_totalWeight {n : ℕ} (w : Weights n) (v : Fin n → Fin n → ℝ)
    (hdiag : ∀ i, v i i = 0)
    (hparts : ∀ e : Edge n, v e.val.1 e.val.2 + v e.val.2 e.val.1 = (w e : ℝ)) :
    (∑ c, ∑ i ∈ Finset.univ.erase c, v c i) = totalWeight w := by
  classical
  have hrow (c : Fin n) : (∑ i ∈ Finset.univ.erase c, v c i) = ∑ i, v c i :=
    Finset.sum_erase Finset.univ (hdiag c)
  simp only [hrow]
  rw [sum_off_diagonal v hdiag]
  exact Finset.sum_congr rfl fun e he => hparts e

lemma oriented_energy {n : ℕ} (w : Weights n) (v : Fin n → Fin n → ℝ)
    (hparts : ∀ e : Edge n, v e.val.1 e.val.2 + v e.val.2 e.val.1 = (w e : ℝ))
    (ψ : Wave n) :
    (∑ c, starEnergy c (Finset.univ.erase c) (v c) ψ) = energy w ψ := by
  classical
  unfold starEnergy
  have hrow (c : Fin n) :
      (∑ i ∈ Finset.univ.erase c, v c i * pairEnergy c i ψ) =
        ∑ i, v c i * pairEnergy c i ψ :=
    Finset.sum_erase Finset.univ (by simp)
  simp only [hrow]
  rw [sum_off_diagonal (fun i j => v i j * pairEnergy i j ψ) (by simp),
    energy_eq_pairEnergy]
  apply Finset.sum_congr rfl
  intro e he
  rw [pairEnergy_comm e.val.2 e.val.1 ψ, ← add_mul, hparts e]

/-- Any orientation of the edges into bounded weighted stars certifies an upper
bound on the full graph energy. -/
theorem energy_le_star_cover {n : ℕ} (w : Weights n)
    (v : Fin n → Fin n → ℝ) (M : Fin n → ℝ)
    (hdiag : ∀ i, v i i = 0)
    (hparts : ∀ e : Edge n, v e.val.1 e.val.2 + v e.val.2 e.val.1 = (w e : ℝ))
    (hv : ∀ c i, 0 ≤ v c i) (hM0 : ∀ c, 0 ≤ M c)
    (hM : ∀ c i, c ≠ i → v c i ≤ M c)
    (ψ : Wave n) (hψ : squaredNorm ψ = 1) :
    energy w ψ ≤ totalWeight w + ∑ c, M c := by
  classical
  rw [← oriented_energy w v hparts ψ]
  calc
    _ ≤ ∑ c, ((∑ i ∈ Finset.univ.erase c, v c i) + M c) := by
      apply Finset.sum_le_sum
      intro c hc
      apply weighted_star_upper_bound c (Finset.univ.erase c) (v c) ψ (M c)
      · simp
      · exact fun i hi => hv c i
      · exact hM0 c
      · intro i hi
        exact hM c i (Finset.ne_of_mem_erase hi).symm
      · exact hψ
    _ = _ := by rw [Finset.sum_add_distrib, oriented_totalWeight w v hdiag hparts]

theorem optimum_le_star_cover {n : ℕ} (w : Weights n)
    (v : Fin n → Fin n → ℝ) (M : Fin n → ℝ)
    (hdiag : ∀ i, v i i = 0)
    (hparts : ∀ e : Edge n, v e.val.1 e.val.2 + v e.val.2 e.val.1 = (w e : ℝ))
    (hv : ∀ c i, 0 ≤ v c i) (hM0 : ∀ c, 0 ≤ M c)
    (hM : ∀ c i, c ≠ i → v c i ≤ M c) :
    optimum ⟨n, w⟩ ≤ totalWeight w + ∑ c, M c := by
  apply csSup_le (energy_values_nonempty ⟨n, w⟩)
  intro b hb
  rcases hb with ⟨ψ, hψ, rfl⟩
  exact energy_le_star_cover w v M hdiag hparts hv hM0 hM ψ hψ

end QuantumMaxCutEnergy.Star

end


-- Local source: next-half/PriceCover.lean

noncomputable section
namespace QuantumMaxCutEnergy.Star

/-- Assign each edge to its endpoint with the larger price, resolving ties by
the vertex order. This definition is only a mathematical upper-bound witness. -/
def priceOrientation {n : ℕ} (w : Weights n) (p : Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  if hij : i < j then
    if p j ≤ p i then (w ⟨(i, j), hij⟩ : ℝ) else 0
  else if hji : j < i then
    if p j < p i then (w ⟨(j, i), hji⟩ : ℝ) else 0
  else 0

lemma priceOrientation_diag {n : ℕ} (w : Weights n) (p : Fin n → ℝ) (i : Fin n) :
    priceOrientation w p i i = 0 := by
  simp [priceOrientation]

lemma priceOrientation_parts {n : ℕ} (w : Weights n) (p : Fin n → ℝ) (e : Edge n) :
    priceOrientation w p e.val.1 e.val.2 + priceOrientation w p e.val.2 e.val.1 =
      (w e : ℝ) := by
  have hij := e.property
  have hji : ¬e.val.2 < e.val.1 := not_lt_of_gt hij
  have he : (⟨(e.val.1, e.val.2), hij⟩ : Edge n) = e := by
    cases e
    rfl
  by_cases hp : p e.val.2 ≤ p e.val.1
  · simp [priceOrientation, hij, hji, hp, not_lt.mpr hp, he]
  · simp [priceOrientation, hij, hji, hp, lt_of_not_ge hp, he]

lemma priceOrientation_nonneg {n : ℕ} (w : Weights n) (p : Fin n → ℝ) (i j : Fin n) :
    0 ≤ priceOrientation w p i j := by
  unfold priceOrientation
  split_ifs <;> positivity

lemma priceOrientation_le {n : ℕ} (w : Weights n) (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hcover : ∀ e : Edge n, (w e : ℝ) ≤ max (p e.val.1) (p e.val.2))
    (i j : Fin n) :
    priceOrientation w p i j ≤ p i := by
  unfold priceOrientation
  split_ifs with hij hprice hji hprice
  · simpa only [max_eq_left hprice] using hcover ⟨(i, j), hij⟩
  · exact hp i
  · simpa only [max_eq_right hprice.le] using hcover ⟨(j, i), hji⟩
  · exact hp i
  · exact hp i

/-- If every edge is bounded by the larger of its endpoint prices, the QMC
optimum is bounded by the total graph weight plus the sum of those prices. -/
theorem optimum_le_price_cover {n : ℕ} (w : Weights n) (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hcover : ∀ e : Edge n, (w e : ℝ) ≤ max (p e.val.1) (p e.val.2)) :
    optimum ⟨n, w⟩ ≤ totalWeight w + ∑ i, p i := by
  apply optimum_le_star_cover w (priceOrientation w p) p
  · exact priceOrientation_diag w p
  · exact priceOrientation_parts w p
  · exact priceOrientation_nonneg w p
  · exact hp
  · intro i j hij
    exact priceOrientation_le w p hp hcover i j

end QuantumMaxCutEnergy.Star

end


-- Local source: next-half/GreedyCover.lean

noncomputable section
namespace QuantumMaxCutEnergy.Star

def endpoints {n : ℕ} (e : Edge n) : Finset (Fin n) := {e.val.1, e.val.2}

def IsMatching {n : ℕ} (m : Finset (Edge n)) : Prop :=
  ∀ e ∈ m, ∀ f ∈ m, e ≠ f → Disjoint (endpoints e) (endpoints f)

def matchingPrice {n : ℕ} (w : Weights n) (m : Finset (Edge n)) (i : Fin n) : ℝ :=
  ∑ e ∈ m, if i ∈ endpoints e then (w e : ℝ) else 0

lemma matchingPrice_nonneg {n : ℕ} (w : Weights n) (m : Finset (Edge n)) (i : Fin n) :
    0 ≤ matchingPrice w m i := by
  apply Finset.sum_nonneg
  intro e he
  split_ifs <;> positivity

lemma matchingPrice_insert {n : ℕ} (w : Weights n) (m : Finset (Edge n))
    (e : Edge n) (he : e ∉ m) (i : Fin n) :
    matchingPrice w (insert e m) i =
      (if i ∈ endpoints e then (w e : ℝ) else 0) + matchingPrice w m i := by
  simp only [matchingPrice, Finset.sum_insert he]

lemma matchingPrice_mono_insert {n : ℕ} (w : Weights n) (m : Finset (Edge n))
    (e : Edge n) (he : e ∉ m) (i : Fin n) :
    matchingPrice w m i ≤ matchingPrice w (insert e m) i := by
  rw [matchingPrice_insert w m e he i]
  have h : 0 ≤ if i ∈ endpoints e then (w e : ℝ) else 0 := by
    split_ifs <;> positivity
  linarith

lemma matchingPrice_sum {n : ℕ} (w : Weights n) (m : Finset (Edge n)) :
    (∑ i, matchingPrice w m i) = 2 * ∑ e ∈ m, (w e : ℝ) := by
  classical
  unfold matchingPrice
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  calc
    _ = ∑ i, ((if i = e.val.1 then (w e : ℝ) else 0) +
        if i = e.val.2 then (w e : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [endpoints, Finset.mem_insert, Finset.mem_singleton]
      by_cases hi1 : i = e.val.1 <;> by_cases hi2 : i = e.val.2 <;>
        simp_all
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp [two_mul]

/-- Greedy selection of a maximum-weight remaining edge produces a matching
whose endpoint prices dominate every edge in the original finite set. -/
theorem exists_greedy_cover {n : ℕ} (w : Weights n) (E : Finset (Edge n)) :
    ∃ m : Finset (Edge n), m ⊆ E ∧ IsMatching m ∧
      ∀ f ∈ E, (w f : ℝ) ≤
        max (matchingPrice w m f.val.1) (matchingPrice w m f.val.2) := by
  classical
  induction E using Finset.strongInductionOn with
  | _ E ih =>
    by_cases hE : E.Nonempty
    · obtain ⟨e, he, hmax⟩ := E.exists_max_image (fun e => (w e : ℝ)) hE
      let R := E.filter (fun f => Disjoint (endpoints e) (endpoints f))
      have hRsub : R ⊆ E := Finset.filter_subset _ _
      have heR : e ∉ R := by
        intro h
        have hd := (Finset.mem_filter.mp h).2
        have hi : e.val.1 ∈ endpoints e := by simp [endpoints]
        exact Finset.disjoint_left.mp hd hi hi
      have hRlt : R ⊂ E := Finset.ssubset_iff_subset_ne.mpr ⟨hRsub, by
        intro h
        exact heR (h ▸ he)⟩
      obtain ⟨m, hm, hmatch, hcover⟩ := ih R hRlt
      have hem : e ∉ m := fun h => heR (hm h)
      refine ⟨insert e m, ?_, ?_, ?_⟩
      · exact Finset.insert_subset_iff.mpr ⟨he, fun f hf => hRsub (hm hf)⟩
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with hae | ham
        · subst a
          rcases Finset.mem_insert.mp hb with hbe | hbm
          · exact False.elim (hab hbe.symm)
          · exact (Finset.mem_filter.mp (hm hbm)).2
        · rcases Finset.mem_insert.mp hb with hbe | hbm
          · subst b
            exact (Finset.mem_filter.mp (hm ham)).2.symm
          · exact hmatch a ham b hbm hab
      · intro f hf
        by_cases hfR : f ∈ R
        · exact (hcover f hfR).trans (max_le_max
            (matchingPrice_mono_insert w m e hem f.val.1)
            (matchingPrice_mono_insert w m e hem f.val.2))
        · have hnot : ¬Disjoint (endpoints e) (endpoints f) := by
            intro h
            exact hfR (Finset.mem_filter.mpr ⟨hf, h⟩)
          obtain ⟨i, hie, hif⟩ := Finset.not_disjoint_iff.mp hnot
          have hp : (w e : ℝ) ≤ matchingPrice w (insert e m) i := by
            rw [matchingPrice_insert w m e hem i, if_pos hie]
            exact le_add_of_nonneg_right (matchingPrice_nonneg w m i)
          have hbound := (hmax f hf).trans hp
          simp only [endpoints, Finset.mem_insert, Finset.mem_singleton] at hif
          rcases hif with rfl | rfl
          · exact hbound.trans (le_max_left _ _)
          · exact hbound.trans (le_max_right _ _)
    · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · simp [IsMatching]
      · intro f hf
        exact False.elim (hE ⟨f, hf⟩)

theorem exists_matching_optimum_upper_bound {n : ℕ} (w : Weights n) :
    ∃ m : Finset (Edge n), IsMatching m ∧
      optimum ⟨n, w⟩ ≤ totalWeight w + 2 * ∑ e ∈ m, (w e : ℝ) := by
  classical
  obtain ⟨m, hm, hmatch, hcover⟩ := exists_greedy_cover w Finset.univ
  refine ⟨m, hmatch, ?_⟩
  have h := optimum_le_price_cover w (matchingPrice w m)
    (matchingPrice_nonneg w m) (fun e => hcover e (Finset.mem_univ e))
  rwa [matchingPrice_sum] at h

end QuantumMaxCutEnergy.Star

end


-- Local source: next-half/GreedyBridge.lean

noncomputable section
namespace QuantumMaxCutEnergy.Star

def remainingEdges {n : ℕ} (e : Edge n) (xs : List (Edge n)) : List (Edge n) :=
  xs.filter (fun f => decide (Disjoint (endpoints e) (endpoints f)))

/-- A trace records the actual choices of a greedy run. It permits any tie rule,
but every recorded choice must be maximum among the current residual edges. -/
inductive GreedyTrace {n : ℕ} (w : Weights n) : List (Edge n) → List (Edge n) → Prop
  | nil : GreedyTrace w [] []
  | cons (xs : List (Edge n)) (e : Edge n) (ys : List (Edge n))
      (he : e ∈ xs) (hmax : ∀ f ∈ xs, (w f : ℝ) ≤ (w e : ℝ))
      (tail : GreedyTrace w (remainingEdges e xs) ys) :
      GreedyTrace w xs (e :: ys)

lemma mem_remainingEdges {n : ℕ} (e f : Edge n) (xs : List (Edge n)) :
    f ∈ remainingEdges e xs ↔ f ∈ xs ∧ Disjoint (endpoints e) (endpoints f) := by
  simp [remainingEdges]

lemma not_mem_remainingEdges_self {n : ℕ} (e : Edge n) (xs : List (Edge n)) :
    e ∉ remainingEdges e xs := by
  intro h
  have hd := (mem_remainingEdges e e xs).mp h |>.2
  have hi : e.val.1 ∈ endpoints e := by simp [endpoints]
  exact Finset.disjoint_left.mp hd hi hi

theorem GreedyTrace.certificate {n : ℕ} {w : Weights n}
    {xs selected : List (Edge n)} (h : GreedyTrace w xs selected) :
    selected.Nodup ∧ selected.toFinset ⊆ xs.toFinset ∧
      IsMatching selected.toFinset ∧
      ∀ f ∈ xs, (w f : ℝ) ≤
        max (matchingPrice w selected.toFinset f.val.1)
          (matchingPrice w selected.toFinset f.val.2) := by
  classical
  induction h with
  | nil => simp [IsMatching]
  | cons xs e ys he hmax ht ih =>
    rcases ih with ⟨hnd, hsub, hmatching, hcover⟩
    have hes : e ∉ ys.toFinset := by
      intro h
      exact not_mem_remainingEdges_self e xs (by simpa using hsub h)
    have hsubmem {f : Edge n} (hf : f ∈ ys.toFinset) :
        f ∈ xs ∧ Disjoint (endpoints e) (endpoints f) := by
      exact (mem_remainingEdges e f xs).mp (by simpa using hsub hf)
    refine ⟨List.nodup_cons.mpr ⟨by simpa using hes, hnd⟩, ?_, ?_, ?_⟩
    · intro f hf
      simp only [List.toFinset_cons, Finset.mem_insert] at hf
      rcases hf with rfl | hf
      · simpa using he
      · simpa using (hsubmem hf).1
    · simp only [List.toFinset_cons]
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hae | ham
      · subst a
        rcases Finset.mem_insert.mp hb with hbe | hbm
        · exact False.elim (hab hbe.symm)
        · exact (hsubmem hbm).2
      · rcases Finset.mem_insert.mp hb with hbe | hbm
        · subst b
          exact (hsubmem ham).2.symm
        · exact hmatching a ham b hbm hab
    · intro f hf
      simp only [List.toFinset_cons]
      by_cases hfr : f ∈ remainingEdges e xs
      · exact (hcover f hfr).trans (max_le_max
          (matchingPrice_mono_insert w ys.toFinset e hes f.val.1)
          (matchingPrice_mono_insert w ys.toFinset e hes f.val.2))
      · have hnot : ¬Disjoint (endpoints e) (endpoints f) := by
          intro hd
          exact hfr ((mem_remainingEdges e f xs).mpr ⟨hf, hd⟩)
        obtain ⟨i, hie, hif⟩ := Finset.not_disjoint_iff.mp hnot
        have hp : (w e : ℝ) ≤ matchingPrice w (insert e ys.toFinset) i := by
          rw [matchingPrice_insert w ys.toFinset e hes i, if_pos hie]
          exact le_add_of_nonneg_right (matchingPrice_nonneg w ys.toFinset i)
        have hbound := (hmax f hf).trans hp
        simp only [endpoints, Finset.mem_insert, Finset.mem_singleton] at hif
        rcases hif with rfl | rfl
        · exact hbound.trans (le_max_left _ _)
        · exact hbound.trans (le_max_right _ _)

lemma sum_map_eq_sum_toFinset {α : Type*} [DecidableEq α]
    (xs : List α) (f : α → ℝ) (h : xs.Nodup) :
    (xs.map f).sum = ∑ a ∈ xs.toFinset, f a := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rcases List.nodup_cons.mp h with ⟨ha, hxs⟩
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
    rw [Finset.sum_insert (by simpa using ha), ih hxs]

/-- This theorem bounds the optimum using the weight of the exact list selected
by a certified greedy run, including its concrete tie decisions. -/
theorem GreedyTrace.optimum_upper {n : ℕ} {w : Weights n}
    {xs selected : List (Edge n)} (h : GreedyTrace w xs selected)
    (hcomplete : ∀ e : Edge n, e ∈ xs) :
    optimum ⟨n, w⟩ ≤ totalWeight w + 2 * (selected.map (fun e => (w e : ℝ))).sum := by
  have hc := h.certificate
  have hu := optimum_le_price_cover w (matchingPrice w selected.toFinset)
    (matchingPrice_nonneg w selected.toFinset) (fun e => hc.2.2.2 e (hcomplete e))
  rw [matchingPrice_sum] at hu
  rwa [sum_map_eq_sum_toFinset selected (fun e => (w e : ℝ)) hc.1]

lemma remainingEdges_length_lt {n : ℕ} (e : Edge n) (xs : List (Edge n))
    (he : e ∈ xs) : (remainingEdges e xs).length < xs.length := by
  apply List.length_filter_lt_length_iff_exists.mpr
  refine ⟨e, he, ?_⟩
  have hnot : ¬Disjoint (endpoints e) (endpoints e) := by
    intro h
    have hi : e.val.1 ∈ endpoints e := by simp [endpoints]
    exact Finset.disjoint_left.mp h hi hi
  simpa only [decide_eq_true_eq] using hnot

def greedyLoop {n : ℕ} (choose : List (Edge n) → Option (Edge n)) :
    ℕ → List (Edge n) → List (Edge n)
  | 0, _ => []
  | k + 1, xs => match choose xs with
    | none => []
    | some e => e :: greedyLoop choose k (remainingEdges e xs)

lemma greedyLoop_of_none {n : ℕ} (choose : List (Edge n) → Option (Edge n))
    (k : ℕ) (xs : List (Edge n)) (h : choose xs = none) :
    greedyLoop choose k xs = [] := by
  cases k <;> simp [greedyLoop, h]

theorem greedyLoop_trace {n : ℕ} (w : Weights n)
    (choose : List (Edge n) → Option (Edge n))
    (hnone : ∀ xs, choose xs = none → xs = [])
    (hchoose : ∀ xs e, choose xs = some e →
      e ∈ xs ∧ ∀ f ∈ xs, (w f : ℝ) ≤ (w e : ℝ))
    (k : ℕ) (xs : List (Edge n)) (hlen : xs.length ≤ k) :
    GreedyTrace w xs (greedyLoop choose k xs) := by
  induction k generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst xs
    exact GreedyTrace.nil
  | succ k ih =>
    cases hsel : choose xs with
    | none =>
      have hx := hnone xs hsel
      subst xs
      simpa [greedyLoop, hsel] using (GreedyTrace.nil (w := w))
    | some e =>
      obtain ⟨he, hmax⟩ := hchoose xs e hsel
      have hlt := remainingEdges_length_lt e xs he
      simp only [greedyLoop, hsel]
      exact GreedyTrace.cons xs e _ he hmax (ih _ (by omega))

def typedStep {n : ℕ} {γ : Type*} (choose : List (Edge n) → Option (Edge n))
    (s : List (Edge n) × List (Edge n)) (_ : γ) : List (Edge n) × List (Edge n) :=
  match choose s.1 with
  | none => s
  | some e => (remainingEdges e s.1, e :: s.2)

lemma typedStep_fold_output {n : ℕ} {γ : Type*}
    (choose : List (Edge n) → Option (Edge n)) (fuel : List γ)
    (xs acc : List (Edge n)) :
    (fuel.foldl (typedStep choose) (xs, acc)).2.reverse =
      acc.reverse ++ greedyLoop choose fuel.length xs := by
  induction fuel generalizing xs acc with
  | nil => simp [greedyLoop]
  | cons u fuel ih =>
    simp only [List.foldl_cons, List.length_cons]
    cases hsel : choose xs with
    | none =>
      simp only [typedStep, hsel]
      rw [ih]
      simp only [greedyLoop_of_none choose _ xs hsel, List.append_nil]
    | some e =>
      simp only [typedStep, hsel]
      rw [ih]
      simp [greedyLoop, hsel, List.append_assoc]

end QuantumMaxCutEnergy.Star

end


-- Local source: next-half/NumericGreedyBridge.lean

noncomputable section
namespace QuantumMaxCutEnergy.Star

abbrev RawEdge := (ℕ × ℕ) × ℚ

def edgeCode {n : ℕ} (w : Weights n) (e : Edge n) : RawEdge :=
  ((e.val.1.val, e.val.2.val), (w e : ℚ))

def rawDisjoint (b e : RawEdge) : Bool :=
  !(decide (e.1.1 = b.1.1)) && !(decide (e.1.1 = b.1.2)) &&
    !(decide (e.1.2 = b.1.1)) && !(decide (e.1.2 = b.1.2))

def rawRemaining (b : RawEdge) (xs : List RawEdge) : List RawEdge :=
  xs.filter (rawDisjoint b)

def rawStep (best : List RawEdge → RawEdge)
    (s : List RawEdge × List RawEdge) (_ : RawEdge) : List RawEdge × List RawEdge :=
  if s.1.isEmpty then s else
    let b := best s.1
    (rawRemaining b s.1, b :: s.2)

def rawMatching (best : List RawEdge → RawEdge) (xs : List RawEdge) : List RawEdge :=
  (xs.foldl (rawStep best) (xs, [])).2.reverse

lemma rawDisjoint_iff (b e : RawEdge) : rawDisjoint b e = true ↔
    e.1.1 ≠ b.1.1 ∧ e.1.1 ≠ b.1.2 ∧ e.1.2 ≠ b.1.1 ∧ e.1.2 ≠ b.1.2 := by
  simp [rawDisjoint, and_assoc]

variable (best : List RawEdge → RawEdge)
variable (hmem : ∀ xs : List RawEdge, xs ≠ [] → best xs ∈ xs)

def typedChoice {n : ℕ} (w : Weights n) (xs : List (Edge n)) (h : xs ≠ []) : Edge n :=
  Classical.choose (List.mem_map.mp
    (hmem (xs.map (edgeCode w)) (by simpa using h)))

lemma typedChoice_spec {n : ℕ} (w : Weights n) (xs : List (Edge n)) (h : xs ≠ []) :
    typedChoice best hmem w xs h ∈ xs ∧
      edgeCode w (typedChoice best hmem w xs h) = best (xs.map (edgeCode w)) := by
  exact Classical.choose_spec (List.mem_map.mp
    (hmem (xs.map (edgeCode w)) (by simpa using h)))

def codeSelector {n : ℕ} (w : Weights n) (xs : List (Edge n)) : Option (Edge n) :=
  if h : xs = [] then none else some (typedChoice best hmem w xs h)

lemma codeSelector_none {n : ℕ} (w : Weights n) (xs : List (Edge n))
    (h : codeSelector best hmem w xs = none) : xs = [] := by
  by_cases hx : xs = []
  · exact hx
  · simp [codeSelector, hx] at h

lemma codeSelector_spec {n : ℕ} (w : Weights n) (xs : List (Edge n)) (e : Edge n)
    (h : codeSelector best hmem w xs = some e) :
    e ∈ xs ∧ edgeCode w e = best (xs.map (edgeCode w)) := by
  by_cases hx : xs = []
  · simp [codeSelector, hx] at h
  · simp only [codeSelector, dif_neg hx, Option.some.injEq] at h
    subst e
    exact typedChoice_spec best hmem w xs hx

lemma codeSelector_max {n : ℕ} (w : Weights n)
    (hmax : ∀ xs : List RawEdge, ∀ e ∈ xs, e.2 ≤ (best xs).2)
    (xs : List (Edge n)) (e : Edge n)
    (h : codeSelector best hmem w xs = some e) :
    e ∈ xs ∧ ∀ f ∈ xs, (w f : ℝ) ≤ (w e : ℝ) := by
  have hs := codeSelector_spec best hmem w xs e h
  refine ⟨hs.1, ?_⟩
  intro f hf
  have hb := hmax (xs.map (edgeCode w)) (edgeCode w f)
    (List.mem_map.mpr ⟨f, hf, rfl⟩)
  rw [← hs.2] at hb
  change (w f : ℚ) ≤ (w e : ℚ) at hb
  exact_mod_cast hb

lemma rawDisjoint_edgeCode {n : ℕ} (w : Weights n) (e f : Edge n) :
    rawDisjoint (edgeCode w e) (edgeCode w f) =
      decide (Disjoint (endpoints e) (endpoints f)) := by
  apply Bool.eq_iff_iff.mpr
  rw [rawDisjoint_iff]
  simp [edgeCode, endpoints, Fin.ext_iff,
    ne_comm, and_left_comm, and_assoc]

lemma rawRemaining_map {n : ℕ} (w : Weights n) (e : Edge n) (xs : List (Edge n)) :
    rawRemaining (edgeCode w e) (xs.map (edgeCode w)) =
      (remainingEdges e xs).map (edgeCode w) := by
  simp only [rawRemaining, remainingEdges, List.filter_map]
  congr 1
  apply List.filter_congr
  intro f hf
  exact rawDisjoint_edgeCode w e f

def codeState {n : ℕ} (w : Weights n) (s : List (Edge n) × List (Edge n)) :
    List RawEdge × List RawEdge := (s.1.map (edgeCode w), s.2.map (edgeCode w))

lemma rawStep_codeState {n : ℕ} (w : Weights n)
    (s : List (Edge n) × List (Edge n)) (u : Edge n) :
    rawStep best (codeState w s) (edgeCode w u) =
      codeState w (typedStep (codeSelector best hmem w) s u) := by
  rcases s with ⟨xs, acc⟩
  by_cases hx : xs = []
  · subst xs
    simp [rawStep, codeState, typedStep, codeSelector]
  · have hs := typedChoice_spec best hmem w xs hx
    have hi : (xs.map (edgeCode w)).isEmpty = false := by
      cases xs with
      | nil => contradiction
      | cons x xs => rfl
    simp only [rawStep, codeState, hi, Bool.false_eq_true, if_false,
      typedStep, codeSelector, dif_neg hx]
    rw [← hs.2, rawRemaining_map]
    rfl

lemma rawFold_codeState {n : ℕ} (w : Weights n) (fuel : List (Edge n))
    (s : List (Edge n) × List (Edge n)) :
    (fuel.map (edgeCode w)).foldl (rawStep best) (codeState w s) =
      codeState w (fuel.foldl (typedStep (codeSelector best hmem w)) s) := by
  induction fuel generalizing s with
  | nil => rfl
  | cons u fuel ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [rawStep_codeState best hmem w s u, ih]

include hmem in
/-- The numeric implementation selects exactly the encoding of a typed greedy
trace, so its specific tie choices inherit the matching and price guarantees. -/
theorem rawMatching_has_trace {n : ℕ} (w : Weights n)
    (hmax : ∀ xs : List RawEdge, ∀ e ∈ xs, e.2 ≤ (best xs).2)
    (xs : List (Edge n)) :
    ∃ selected : List (Edge n), GreedyTrace w xs selected ∧
      rawMatching best (xs.map (edgeCode w)) = selected.map (edgeCode w) := by
  let choose := codeSelector best hmem w
  let selected := greedyLoop choose xs.length xs
  refine ⟨selected, ?_, ?_⟩
  · apply greedyLoop_trace w choose
    · exact codeSelector_none best hmem w
    · exact codeSelector_max best hmem w hmax
    · exact le_rfl
  · unfold rawMatching
    change ((xs.map (edgeCode w)).foldl (rawStep best) (codeState w (xs, []))).2.reverse = _
    rw [rawFold_codeState best hmem w xs (xs, [])]
    simp only [codeState]
    rw [← List.map_reverse, typedStep_fold_output]
    rfl

end QuantumMaxCutEnergy.Star

end


-- Local source: next-half/MatchingLowerWave.lean

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.Star

def pairAmplitude {n : ℕ} (e : Edge n) (x : Basis n) : ℂ :=
  if x e.val.1 = x e.val.2 then 0 else if x e.val.1 then -1 else 1

def matchingWave {n : ℕ} (m : Finset (Edge n)) : Wave n :=
  fun x => ∏ e ∈ m, pairAmplitude e x

lemma pairAmplitude_swap_self {n : ℕ} (e : Edge n) (x : Basis n) :
    pairAmplitude e (x ∘ Equiv.swap e.val.1 e.val.2) = -pairAmplitude e x := by
  simp only [pairAmplitude, Function.comp_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  cases h1 : x e.val.1 <;> cases h2 : x e.val.2 <;> norm_num

lemma pairAmplitude_swap_disjoint {n : ℕ} (e f : Edge n)
    (h : Disjoint (endpoints e) (endpoints f)) (x : Basis n) :
    pairAmplitude f (x ∘ Equiv.swap e.val.1 e.val.2) = pairAmplitude f x := by
  have hi1 : f.val.1 ≠ e.val.1 := by
    intro he
    exact Finset.disjoint_left.mp h
      (show f.val.1 ∈ endpoints e by simp [endpoints, ← he])
      (show f.val.1 ∈ endpoints f by simp [endpoints])
  have hi2 : f.val.1 ≠ e.val.2 := by
    intro he
    exact Finset.disjoint_left.mp h
      (show f.val.1 ∈ endpoints e by simp [endpoints, ← he])
      (show f.val.1 ∈ endpoints f by simp [endpoints])
  have hj1 : f.val.2 ≠ e.val.1 := by
    intro he
    exact Finset.disjoint_left.mp h
      (show f.val.2 ∈ endpoints e by simp [endpoints, ← he])
      (show f.val.2 ∈ endpoints f by simp [endpoints])
  have hj2 : f.val.2 ≠ e.val.2 := by
    intro he
    exact Finset.disjoint_left.mp h
      (show f.val.2 ∈ endpoints e by simp [endpoints, ← he])
      (show f.val.2 ∈ endpoints f by simp [endpoints])
  simp only [pairAmplitude, Function.comp_apply,
    Equiv.swap_apply_of_ne_of_ne hi1 hi2, Equiv.swap_apply_of_ne_of_ne hj1 hj2]

lemma matchingWave_swap {n : ℕ} (m : Finset (Edge n)) (hm : IsMatching m)
    (e : Edge n) (he : e ∈ m) (x : Basis n) :
    matchingWave m (x ∘ Equiv.swap e.val.1 e.val.2) = -matchingWave m x := by
  classical
  have hrest :
      (∏ f ∈ m.erase e, pairAmplitude f (x ∘ Equiv.swap e.val.1 e.val.2)) =
        ∏ f ∈ m.erase e, pairAmplitude f x := by
    apply Finset.prod_congr rfl
    intro f hf
    exact pairAmplitude_swap_disjoint e f
      (hm e he f (Finset.mem_erase.mp hf).2 (Ne.symm (Finset.mem_erase.mp hf).1)) x
  unfold matchingWave
  rw [← Finset.insert_erase he]
  rw [Finset.prod_insert (by simp : e ∉ m.erase e),
    Finset.prod_insert (by simp : e ∉ m.erase e), hrest, pairAmplitude_swap_self]
  ring

def matchingAssignment {n : ℕ} (m : Finset (Edge n)) : Basis n :=
  fun i => decide (i ∈ m.image (fun e => e.val.2))

lemma matchingAssignment_first {n : ℕ} (m : Finset (Edge n)) (hm : IsMatching m)
    (e : Edge n) (he : e ∈ m) : matchingAssignment m e.val.1 = false := by
  classical
  have hn : e.val.1 ∉ m.image (fun f => f.val.2) := by
    rintro h
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp h
    by_cases hEq : e = f
    · subst f
      exact (ne_of_lt e.property) hfe.symm
    · exact Finset.disjoint_left.mp (hm e he f hf hEq)
        (show e.val.1 ∈ endpoints e by simp [endpoints])
        (show e.val.1 ∈ endpoints f by simp [endpoints, hfe])
  simp [matchingAssignment, hn]

lemma matchingAssignment_second {n : ℕ} (m : Finset (Edge n))
    (e : Edge n) (he : e ∈ m) : matchingAssignment m e.val.2 = true := by
  classical
  simp [matchingAssignment, Finset.mem_image_of_mem (fun e : Edge n => e.val.2) he]

lemma matchingWave_nonzero {n : ℕ} (m : Finset (Edge n)) (hm : IsMatching m) :
    matchingWave m (matchingAssignment m) = 1 := by
  classical
  apply Finset.prod_eq_one
  intro e he
  simp [pairAmplitude, matchingAssignment_first m hm e he,
    matchingAssignment_second m e he]

lemma matchingWave_norm_pos {n : ℕ} (m : Finset (Edge n)) (hm : IsMatching m) :
    0 < squaredNorm (matchingWave m) := by
  classical
  have h : (1 : ℝ) ≤ squaredNorm (matchingWave m) := by
    calc
      1 = Complex.normSq (matchingWave m (matchingAssignment m)) := by
        rw [matchingWave_nonzero m hm]
        norm_num
      _ ≤ ∑ x, Complex.normSq (matchingWave m x) :=
        Finset.single_le_sum (fun x _ => Complex.normSq_nonneg _) (Finset.mem_univ _)
  linarith

lemma squaredNorm_realScale {n : ℕ} (a : ℝ) (ψ : Wave n) :
    squaredNorm (realScale a ψ) = a ^ 2 * squaredNorm ψ := by
  rw [← realInner_self, realInner_scale_left, realInner_scale_right, realInner_self]
  ring

def matchingState {n : ℕ} (m : Finset (Edge n)) : Wave n :=
  realScale (Real.sqrt (squaredNorm (matchingWave m)))⁻¹ (matchingWave m)

lemma matchingState_norm {n : ℕ} (m : Finset (Edge n)) (hm : IsMatching m) :
    squaredNorm (matchingState m) = 1 := by
  have hn := matchingWave_norm_pos m hm
  have hs : Real.sqrt (squaredNorm (matchingWave m)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hn)
  unfold matchingState
  rw [squaredNorm_realScale, inv_pow, Real.sq_sqrt hn.le]
  exact inv_mul_cancel₀ (ne_of_gt hn)

lemma matchingState_swap {n : ℕ} (m : Finset (Edge n)) (hm : IsMatching m)
    (e : Edge n) (he : e ∈ m) (x : Basis n) :
    matchingState m (x ∘ Equiv.swap e.val.1 e.val.2) = -matchingState m x := by
  simp only [matchingState, realScale, matchingWave_swap m hm e he]
  ring

lemma pairEnergy_of_antisymmetric {n : ℕ} (a b : Fin n) (ψ : Wave n)
    (hψ : squaredNorm ψ = 1)
    (hs : ∀ x, ψ (x ∘ Equiv.swap a b) = -ψ x) : pairEnergy a b ψ = 2 := by
  have he : edgeAction a b ψ = realScale 2 ψ := by
    funext x
    simp only [edgeAction, swapWave, Pi.sub_apply, realScale, hs]
    push_cast
    ring
  rw [pairEnergy, he, realInner_scale_right, realInner_self, hψ]
  norm_num

theorem matching_energy_lower {n : ℕ} (w : Weights n) (m : Finset (Edge n))
    (hm : IsMatching m) :
    2 * (∑ e ∈ m, (w e : ℝ)) ≤ optimum ⟨n, w⟩ := by
  classical
  have hp (e : Edge n) (he : e ∈ m) :
      pairEnergy e.val.1 e.val.2 (matchingState m) = 2 :=
    pairEnergy_of_antisymmetric _ _ _ (matchingState_norm m hm)
      (matchingState_swap m hm e he)
  have he : 2 * (∑ e ∈ m, (w e : ℝ)) ≤ energy w (matchingState m) := by
    rw [energy_eq_pairEnergy]
    calc
      _ = ∑ e ∈ m, (w e : ℝ) * pairEnergy e.val.1 e.val.2 (matchingState m) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        rw [hp e he]
        ring
      _ ≤ ∑ e, (w e : ℝ) * pairEnergy e.val.1 e.val.2 (matchingState m) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun e _ _ => mul_nonneg (by positivity) (pairEnergy_nonneg _ _ _))
  exact he.trans (energy_le_optimum ⟨n, w⟩ (matchingState m) (matchingState_norm m hm))


end QuantumMaxCutEnergy.Star

end


-- Local source: next-half/MatchingLowerStrong.lean

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.Star

lemma edgeAction_of_antisymmetric {n : ℕ} (a b : Fin n) (ψ : Wave n)
    (hs : ∀ x, ψ (x ∘ Equiv.swap a b) = -ψ x) :
    edgeAction a b ψ = realScale 2 ψ := by
  funext x
  simp only [edgeAction, swapWave, Pi.sub_apply, realScale, hs]
  push_cast
  ring

/-- A qubit in an antisymmetric pair has exactly one-half QMC interaction
with every third qubit. The proof uses only the shared-center identity. -/
lemma cross_pairEnergy_of_antisymmetric {n : ℕ} (a c b : Fin n)
    (hac : a ≠ c) (hab : a ≠ b) (hcb : c ≠ b) (ψ : Wave n)
    (hψ : squaredNorm ψ = 1)
    (hs : ∀ x, ψ (x ∘ Equiv.swap a c) = -ψ x) :
    pairEnergy a b ψ = 1 / 2 := by
  have hsr : ∀ x, ψ (x ∘ Equiv.swap c a) = -ψ x := by
    intro x
    simpa only [Equiv.swap_comm c a] using hs x
  have ha := edgeAction_of_antisymmetric a c ψ hs
  have hc := edgeAction_of_antisymmetric c a ψ hsr
  have hpa := pairEnergy_of_antisymmetric a c ψ hψ hs
  have hpc := pairEnergy_of_antisymmetric c a ψ hψ hsr
  have h1 := shared_center_inner ψ a c b hac hab hcb
  have h2 := shared_center_inner ψ c a b hac.symm hcb hab
  rw [ha, realInner_scale_left] at h1
  rw [hc, realInner_scale_left] at h2
  change 2 * (2 * pairEnergy a b ψ) =
    pairEnergy a c ψ + pairEnergy a b ψ - pairEnergy c b ψ at h1
  change 2 * (2 * pairEnergy c b ψ) =
    pairEnergy c a ψ + pairEnergy c b ψ - pairEnergy a b ψ at h2
  rw [hpa] at h1
  rw [hpc] at h2
  linarith

lemma edge_eq_of_coordinates {n : ℕ} (e f : Edge n)
    (h1 : e.val.1 = f.val.1) (h2 : e.val.2 = f.val.2) : e = f := by
  apply Subtype.ext
  exact Prod.ext h1 h2

lemma cross_pairEnergy_of_touching {n : ℕ} (e f : Edge n) (hne : e ≠ f)
    (htouch : ¬Disjoint (endpoints e) (endpoints f))
    (ψ : Wave n) (hψ : squaredNorm ψ = 1)
    (hs : ∀ x, ψ (x ∘ Equiv.swap e.val.1 e.val.2) = -ψ x) :
    pairEnergy f.val.1 f.val.2 ψ = 1 / 2 := by
  have hsr : ∀ x, ψ (x ∘ Equiv.swap e.val.2 e.val.1) = -ψ x := by
    intro x
    simpa only [Equiv.swap_comm e.val.2 e.val.1] using hs x
  have hen := ne_of_lt e.property
  have hfn := ne_of_lt f.property
  by_cases h11 : f.val.1 = e.val.1
  · have h22 : e.val.2 ≠ f.val.2 := by
      intro h
      exact hne (edge_eq_of_coordinates e f h11.symm h)
    simpa only [h11] using cross_pairEnergy_of_antisymmetric
      e.val.1 e.val.2 f.val.2 hen (by simpa only [h11] using hfn) h22 ψ hψ hs
  by_cases h12 : f.val.1 = e.val.2
  · have h21 : e.val.1 ≠ f.val.2 :=
      ne_of_lt (e.property.trans (by simpa only [h12] using f.property))
    simpa only [h12] using cross_pairEnergy_of_antisymmetric
      e.val.2 e.val.1 f.val.2 hen.symm (by simpa only [h12] using hfn) h21 ψ hψ hsr
  by_cases h21 : f.val.2 = e.val.1
  · have h12 : e.val.2 ≠ f.val.1 := by
      exact (ne_of_lt ((by simpa only [h21] using f.property : f.val.1 < e.val.1).trans
        e.property)).symm
    rw [pairEnergy_comm]
    simpa only [h21] using cross_pairEnergy_of_antisymmetric
      e.val.1 e.val.2 f.val.1 hen (by simpa only [h21] using hfn.symm) h12 ψ hψ hs
  have h22 : f.val.2 = e.val.2 := by
    obtain ⟨v, hve, hvf⟩ := Finset.not_disjoint_iff.mp htouch
    simp only [endpoints, Finset.mem_insert, Finset.mem_singleton] at hve hvf
    rcases hve with hve | hve <;> rcases hvf with hvf | hvf
    · exact False.elim (h11 (hvf.symm.trans hve))
    · exact False.elim (h21 (hvf.symm.trans hve))
    · exact False.elim (h12 (hvf.symm.trans hve))
    · exact hvf.symm.trans hve
  have h1 : e.val.1 ≠ f.val.1 := by
    intro h
    exact hne (edge_eq_of_coordinates e f h h22.symm)
  rw [pairEnergy_comm]
  simpa only [h22] using cross_pairEnergy_of_antisymmetric
    e.val.2 e.val.1 f.val.1 hen.symm (by simpa only [h22] using hfn.symm) h1 ψ hψ hsr

lemma matchingState_pair_of_touching {n : ℕ} (m : Finset (Edge n))
    (hm : IsMatching m) (f : Edge n) (hf : f ∉ m)
    (htouch : ∃ e ∈ m, ¬Disjoint (endpoints e) (endpoints f)) :
    pairEnergy f.val.1 f.val.2 (matchingState m) = 1 / 2 := by
  obtain ⟨e, he, hef⟩ := htouch
  have hne : e ≠ f := by
    intro h
    exact hf (h ▸ he)
  exact cross_pairEnergy_of_touching e f hne hef _ (matchingState_norm m hm)
    (matchingState_swap m hm e he)


end QuantumMaxCutEnergy.Star

end


-- Local source: next-half/MatchingExtension.lean

noncomputable section
namespace QuantumMaxCutEnergy.Star

lemma IsMatching.insert_disjoint {n : ℕ} {M : Finset (Edge n)} (hM : IsMatching M)
    (f : Edge n) (hd : ∀ e ∈ M, Disjoint (endpoints e) (endpoints f)) :
    IsMatching (insert f M) := by
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with haf | ham
  · subst a
    rcases Finset.mem_insert.mp hb with hbf | hbm
    · exact False.elim (hab hbf.symm)
    · exact (hd b hbm).symm
  · rcases Finset.mem_insert.mp hb with hbf | hbm
    · subst b
      exact hd a ham
    · exact hM a ham b hbm hab

/-- Every matching extends to a maximal matching of the complete vertex set.
No added edge needs positive graph weight. -/
theorem exists_maximal_matching_extension {n : ℕ} (m : Finset (Edge n))
    (hm : IsMatching m) :
    ∃ M : Finset (Edge n), m ⊆ M ∧ IsMatching M ∧
      ∀ f : Edge n, f ∉ M →
        ∃ e ∈ M, ¬Disjoint (endpoints e) (endpoints f) := by
  classical
  let C := (Finset.univ : Finset (Edge n)).powerset.filter
    (fun M => m ⊆ M ∧ IsMatching M)
  have hmC : m ∈ C := by simp [C, hm]
  obtain ⟨M, hMC, hmax⟩ := C.exists_max_image Finset.card ⟨m, hmC⟩
  have hM := (Finset.mem_filter.mp hMC).2
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro f hf
  by_contra h
  push Not at h
  have hmatch := hM.2.insert_disjoint f h
  have hsub : m ⊆ insert f M := hM.1.trans (Finset.subset_insert f M)
  have hiC : insert f M ∈ C := by simp [C, hsub, hmatch]
  have hcard := hmax (insert f M) hiC
  rw [Finset.card_insert_of_notMem hf] at hcard
  omega

end QuantumMaxCutEnergy.Star

end


-- Local source: next-half/MatchingLowerBound.lean

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.Star

lemma matchingState_energy {n : ℕ} (w : Weights n) (m : Finset (Edge n))
    (hm : IsMatching m)
    (hcover : ∀ f : Edge n, f ∉ m → ∃ e ∈ m, ¬Disjoint (endpoints e) (endpoints f)) :
    energy w (matchingState m) =
      (totalWeight w + 3 * (∑ e ∈ m, (w e : ℝ))) / 2 := by
  classical
  have hpair (e : Edge n) :
      pairEnergy e.val.1 e.val.2 (matchingState m) = if e ∈ m then 2 else 1 / 2 := by
    by_cases he : e ∈ m
    · rw [if_pos he]
      exact pairEnergy_of_antisymmetric _ _ _ (matchingState_norm m hm)
        (matchingState_swap m hm e he)
    · rw [if_neg he]
      exact matchingState_pair_of_touching m hm e he (hcover e he)
  rw [energy_eq_pairEnergy]
  simp_rw [hpair]
  have hsum : (∑ e : Edge n, if e ∈ m then (w e : ℝ) else 0) =
      ∑ e ∈ m, (w e : ℝ) := by
    simp
  calc
    (∑ e : Edge n, (w e : ℝ) * if e ∈ m then 2 else 1 / 2) =
        ∑ e : Edge n, ((w e : ℝ) / 2 +
          3 / 2 * (if e ∈ m then (w e : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, hsum]
      unfold totalWeight
      ring

/-- The matching lower estimate is a numerical bound on the unrestricted
optimum. The auxiliary normalized vector is only an analytic witness. -/
theorem matching_energy_strong_lower {n : ℕ} (w : Weights n) (m : Finset (Edge n))
    (hm : IsMatching m) :
    (totalWeight w + 3 * (∑ e ∈ m, (w e : ℝ))) / 2 ≤ optimum ⟨n, w⟩ := by
  classical
  obtain ⟨M, hsub, hM, hcover⟩ := exists_maximal_matching_extension m hm
  have hvalue := energy_le_optimum ⟨n, w⟩ (matchingState M) (matchingState_norm M hM)
  rw [matchingState_energy w M hM hcover] at hvalue
  have hsum : (∑ e ∈ m, (w e : ℝ)) ≤ ∑ e ∈ M, (w e : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => by positivity)
  linarith


end QuantumMaxCutEnergy.Star

end


-- Local source: greedy-runtime/GreedyRuntime.lean

noncomputable section

namespace QMCNumericRuntime.Greedy

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open Polynomial

abbrev NumericEdge := (ℕ × ℕ) × ℚ

def defaultEdge : NumericEdge := ((0, 0), 0)

def edgeEncoding : NumericEdge → List Bool :=
  encodePair (encodePair Nat.bits Nat.bits) Ratio.encode

def listEncoding : List NumericEdge → List Bool := encodeList edgeEncoding

def pick (a b : NumericEdge) : NumericEdge := if a.2 < b.2 then b else a

def best (xs : List NumericEdge) : NumericEdge :=
  xs.tail.foldl pick (xs.head?.getD defaultEdge)

def disjoint (b e : NumericEdge) : Bool :=
  !(decide (e.1.1 = b.1.1)) && !(decide (e.1.1 = b.1.2)) &&
    !(decide (e.1.2 = b.1.1)) && !(decide (e.1.2 = b.1.2))

def remaining (b : NumericEdge) (xs : List NumericEdge) : List NumericEdge :=
  xs.filter (disjoint b)

abbrev State := List NumericEdge × List NumericEdge

def stateEncoding : State → List Bool := encodePair listEncoding listEncoding

def step (s : State) (_ : NumericEdge) : State :=
  if s.1.isEmpty then s else
    let b := best s.1
    (remaining b s.1, b :: s.2)

def runState (xs : List NumericEdge) : State := xs.foldl step (xs, [])

def matching (xs : List NumericEdge) : List NumericEdge := (runState xs).2.reverse

lemma pick_eq_or (a b : NumericEdge) : pick a b = a ∨ pick a b = b := by
  unfold pick
  split_ifs <;> simp

lemma le_pick_left (a b : NumericEdge) : a.2 ≤ (pick a b).2 := by
  unfold pick
  split_ifs with h
  · exact h.le
  · exact le_rfl

lemma le_pick_right (a b : NumericEdge) : b.2 ≤ (pick a b).2 := by
  unfold pick
  split_ifs with h
  · exact le_rfl
  · exact le_of_not_gt h

lemma fold_pick_mem (xs : List NumericEdge) (a : NumericEdge) :
    xs.foldl pick a ∈ a :: xs := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp (ih (pick a b)) with he | hm
      · rw [he]
        rcases pick_eq_or a b with ha | hb
        · simp [ha]
        · simp [hb]
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)

lemma fold_pick_max (xs : List NumericEdge) (a : NumericEdge) :
    a.2 ≤ (xs.foldl pick a).2 ∧
      ∀ e ∈ xs, e.2 ≤ (xs.foldl pick a).2 := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
      have h := ih (pick a b)
      constructor
      · exact (le_pick_left a b).trans h.1
      · intro e he
        rcases List.mem_cons.mp he with he | hm
        · rw [he]
          exact (le_pick_right a b).trans h.1
        · exact h.2 e hm

theorem best_mem (xs : List NumericEdge) (hne : xs ≠ []) : best xs ∈ xs := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons a xs => simpa only [best, List.tail_cons, List.head?_cons, Option.getD_some]
      using fold_pick_mem xs a

theorem best_max (xs : List NumericEdge) (e : NumericEdge) (he : e ∈ xs) :
    e.2 ≤ (best xs).2 := by
  cases xs with
  | nil => simp at he
  | cons a xs =>
      simp only [best, List.tail_cons, List.head?_cons, Option.getD_some]
      rcases List.mem_cons.mp he with he | hm
      · rw [he]
        exact (fold_pick_max xs a).1
      · exact (fold_pick_max xs a).2 e hm

@[simp] lemma disjoint_self (e : NumericEdge) : disjoint e e = false := by
  simp [disjoint]

theorem disjoint_iff (b e : NumericEdge) : disjoint b e = true ↔
    e.1.1 ≠ b.1.1 ∧ e.1.1 ≠ b.1.2 ∧ e.1.2 ≠ b.1.1 ∧ e.1.2 ≠ b.1.2 := by
  simp [disjoint, and_assoc]

theorem mem_remaining (b e : NumericEdge) (xs : List NumericEdge) :
    e ∈ remaining b xs ↔ e ∈ xs ∧ disjoint b e = true := by
  simp [remaining]

theorem remaining_sublist (b : NumericEdge) (xs : List NumericEdge) :
    List.Sublist (remaining b xs) xs := List.filter_sublist

lemma remaining_length_lt (xs : List NumericEdge) (hne : xs ≠ []) :
    (remaining (best xs) xs).length < xs.length := by
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨best xs, best_mem xs hne, by simp⟩

lemma filter_encoding_bound (p : NumericEdge → Bool) (xs : List NumericEdge) :
    (listEncoding (xs.filter p)).length ≤ (listEncoding xs).length := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
      cases h : p e <;>
        simp [h, listEncoding, EncodedList.cons_length] at * <;> omega

lemma remaining_encoding_bound (b : NumericEdge) (xs : List NumericEdge) :
    (listEncoding (remaining b xs)).length ≤ (listEncoding xs).length :=
  filter_encoding_bound (disjoint b) xs

@[fun_prop] theorem pick_poly : Poly (fun x : NumericEdge × NumericEdge => pick x.1 x.2) := by
  unfold pick
  fun_prop

noncomputable def pickFoldProgram :
    PolyProgram (encodePair listEncoding edgeEncoding) edgeEncoding
      (fun x : List NumericEdge × NumericEdge => x.1.foldl pick x.2) :=
  pick_poly.program.listFoldLinear defaultEdge 1 (by
    intro b a
    change (edgeEncoding (pick b a)).length ≤
      (edgeEncoding b).length + 1 * (2 * (edgeEncoding a).length + 1)
    unfold pick
    split_ifs <;> omega)

@[fun_prop] theorem pickFold_poly :
    Poly (fun x : List NumericEdge × NumericEdge => x.1.foldl pick x.2) :=
  ⟨pickFoldProgram⟩

@[fun_prop] theorem best_poly : Poly best := by
  unfold best
  exact Poly.comp pickFold_poly (Poly.pair Poly.list_tail (Poly.list_head defaultEdge))

@[fun_prop] theorem disjoint_poly :
    Poly (fun x : NumericEdge × NumericEdge => disjoint x.1 x.2) := by
  unfold disjoint
  fun_prop

@[fun_prop] theorem remaining_poly :
    Poly (fun x : NumericEdge × List NumericEdge => remaining x.1 x.2) := by
  unfold remaining
  fun_prop

@[fun_prop] theorem step_poly :
    Poly (fun x : State × NumericEdge => step x.1 x.2) := by
  unfold step
  fun_prop

noncomputable def bestProgram : PolyProgram listEncoding edgeEncoding best := best_poly.program

noncomputable def bestBound : Polynomial ℕ := bestProgram.sizeBound

lemma best_encoding_bound (xs : List NumericEdge) :
    (edgeEncoding (best xs)).length ≤ bestBound.eval (listEncoding xs).length :=
  bestProgram.length_bound xs

lemma step_encoding_bounds (s : State) (e : NumericEdge) :
    (listEncoding (step s e).1).length ≤ (listEncoding s.1).length ∧
    (listEncoding (step s e).2).length ≤
      (listEncoding s.2).length + 2 * bestBound.eval (listEncoding s.1).length + 1 := by
  unfold step
  split_ifs
  · exact ⟨le_rfl, by omega⟩
  · constructor
    · exact remaining_encoding_bound _ _
    · have hb := best_encoding_bound s.1
      change (encodeList edgeEncoding (best s.1 :: s.2)).length ≤ _
      rw [EncodedList.cons_length]
      change (edgeEncoding (best s.1)).length ≤
        bestBound.eval (encodeList edgeEncoding s.1).length at hb
      change 2 * (edgeEncoding (best s.1)).length + 1 +
          (encodeList edgeEncoding s.2).length ≤
        (encodeList edgeEncoding s.2).length +
          2 * bestBound.eval (encodeList edgeEncoding s.1).length + 1
      omega

lemma fold_encoding_bounds (fuel : List NumericEdge) (remaining chosen : List NumericEdge) :
    (listEncoding (fuel.foldl step (remaining, chosen)).1).length ≤
        (listEncoding remaining).length ∧
    (listEncoding (fuel.foldl step (remaining, chosen)).2).length ≤
      (listEncoding chosen).length +
        fuel.length * (2 * bestBound.eval (listEncoding remaining).length + 1) := by
  induction fuel generalizing remaining chosen with
  | nil => simp only [List.foldl_nil, List.length_nil, zero_mul, add_zero, le_refl, and_self]
  | cons e fuel ih =>
      let s := step (remaining, chosen) e
      have hs := step_encoding_bounds (remaining, chosen) e
      have hi := ih s.1 s.2
      have hp := polynomial_eval_mono bestBound hs.1
      constructor
      · simpa only [List.foldl_cons, s] using hi.1.trans hs.1
      · have hm :
            fuel.length * (2 * bestBound.eval (listEncoding s.1).length + 1) ≤
              fuel.length * (2 * bestBound.eval (listEncoding remaining).length + 1) :=
          Nat.mul_le_mul_left _ (by simpa only [s] using
            (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hp) 1))
        change (listEncoding (fuel.foldl step (s.1, s.2)).2).length ≤ _
        simp only [List.length_cons]
        have hs' : (listEncoding s.2).length ≤
            (listEncoding chosen).length +
              2 * bestBound.eval (listEncoding remaining).length + 1 := hs.2
        nlinarith [hi.2]

lemma stateEncoding_length (s : State) :
    (stateEncoding s).length =
      2 * (listEncoding s.1).length + 1 + (listEncoding s.2).length := by
  simp only [stateEncoding, encodePair_length]

noncomputable def foldBound : Polynomial ℕ := X + X * (2 * bestBound + 1)

lemma fold_state_bound (as : List NumericEdge) (b : State)
    (pre suf : List NumericEdge) (he : as = pre ++ suf) :
    (stateEncoding (pre.foldl step b)).length ≤
      foldBound.eval (encodePair listEncoding stateEncoding (as, b)).length := by
  let N := (encodePair listEncoding stateEncoding (as, b)).length
  have hb : (stateEncoding b).length ≤ N := by
    simp only [N, encodePair_length]
    omega
  have hrem : (listEncoding b.1).length ≤ N := by
    rw [stateEncoding_length] at hb
    omega
  have hpre : pre.length ≤ N := by
    have hp : pre.length ≤ as.length := by rw [he, List.length_append]; omega
    have ha := EncodedList.length_le edgeEncoding as
    change as.length ≤ (listEncoding as).length at ha
    have hc : (listEncoding as).length ≤ N := by
      simp only [N, encodePair_length]
      omega
    omega
  have hf :
      (listEncoding (pre.foldl step b).1).length ≤ (listEncoding b.1).length ∧
      (listEncoding (pre.foldl step b).2).length ≤
        (listEncoding b.2).length +
          pre.length * (2 * bestBound.eval (listEncoding b.1).length + 1) := by
    simpa only [Prod.eta] using fold_encoding_bounds pre b.1 b.2
  have hgrowth : (stateEncoding (pre.foldl step b)).length ≤
      (stateEncoding b).length +
        pre.length * (2 * bestBound.eval (listEncoding b.1).length + 1) := by
    rw [stateEncoding_length, stateEncoding_length]
    omega
  have hp := polynomial_eval_mono bestBound hrem
  have hm : pre.length * (2 * bestBound.eval (listEncoding b.1).length + 1) ≤
      N * (2 * bestBound.eval N + 1) :=
    Nat.mul_le_mul hpre (by omega)
  change _ ≤ foldBound.eval N
  simp only [foldBound, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

noncomputable def foldProgram :
    PolyProgram (encodePair listEncoding stateEncoding) stateEncoding
      (fun x : List NumericEdge × State => x.1.foldl step x.2) :=
  step_poly.program.listFold defaultEdge foldBound fold_state_bound

@[fun_prop] theorem fold_poly :
    Poly (fun x : List NumericEdge × State => x.1.foldl step x.2) := ⟨foldProgram⟩

@[fun_prop] theorem runState_poly : Poly runState := by
  unfold runState
  have hs : Poly (fun xs : List NumericEdge => (xs, (xs, ([] : List NumericEdge)))) :=
    Poly.pair Poly.identity (Poly.pair Poly.identity
      (OAI.MetricKMedian.Binary.Automatic.Poly.const
        (α := List NumericEdge) (β := List NumericEdge) ([] : List NumericEdge)))
  exact Poly.comp fold_poly hs

@[fun_prop] theorem matching_reverse_poly :
    Poly (List.reverse : List NumericEdge → List NumericEdge) :=
  ⟨PolyProgram.listReverse edgeEncoding defaultEdge⟩

@[fun_prop] theorem matching_poly : Poly matching := by
  unfold matching
  fun_prop

noncomputable def matchingProgram : PolyProgram listEncoding listEncoding matching :=
  matching_poly.program

noncomputable def matchingCertificate :
    Turing.TM2ComputableInPolyTime listEncoding listEncoding matching := matchingProgram.stock


end QMCNumericRuntime.Greedy

end




-- Local source: next-half/GreedyGuarantees.lean

noncomputable section
namespace QMCNumericRuntime
open QuantumMaxCutEnergy
open QuantumMaxCutEnergy.Star

lemma matching_eq_rawMatching (xs : List NumericEdge) :
    Greedy.matching xs = rawMatching Greedy.best xs := rfl

theorem matching_has_typed_trace (G : Input) :
    ∃ selected : List (Edge G.n),
      GreedyTrace G.weights (graphEdgeList G.n) selected ∧
        Greedy.matching (inputEdges G) = selected.map (numericEdge G) := by
  obtain ⟨selected, htrace, hmap⟩ := rawMatching_has_trace Greedy.best Greedy.best_mem
    G.weights Greedy.best_max (graphEdgeList G.n)
  refine ⟨selected, htrace, ?_⟩
  exact hmap

theorem matching_nonneg (G : Input) :
    ∀ e ∈ Greedy.matching (inputEdges G), 0 ≤ e.2 := by
  obtain ⟨selected, htrace, hmap⟩ := matching_has_typed_trace G
  rw [hmap]
  intro e he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  change 0 ≤ (G.weights f : ℚ)
  positivity

lemma matching_weight_sum (G : Input) (selected : List (Edge G.n))
    (hmap : Greedy.matching (inputEdges G) = selected.map (numericEdge G)) :
    (((Greedy.matching (inputEdges G)).map Prod.snd).sum : ℚ) =
      (selected.map (fun e => (G.weights e : ℚ))).sum := by
  rw [hmap, List.map_map]
  rfl

lemma matching_weight_sum_real (G : Input) (selected : List (Edge G.n))
    (hmap : Greedy.matching (inputEdges G) = selected.map (numericEdge G)) :
    ((((Greedy.matching (inputEdges G)).map Prod.snd).sum : ℚ) : ℝ) =
      (selected.map (fun e => (G.weights e : ℝ))).sum := by
  rw [matching_weight_sum G selected hmap, Rat.cast_list_sum, List.map_map]
  congr 1

theorem matching_weight_nonneg (G : Input) :
    0 ≤ ((Greedy.matching (inputEdges G)).map Prod.snd).sum := by
  apply List.sum_nonneg
  intro q hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
  exact matching_nonneg G e he

theorem matching_optimum_upper (G : Input) :
    optimum G ≤ totalWeight G.weights +
      2 * ((((Greedy.matching (inputEdges G)).map Prod.snd).sum : ℚ) : ℝ) := by
  obtain ⟨selected, htrace, hmap⟩ := matching_has_typed_trace G
  rw [matching_weight_sum_real G selected hmap]
  exact htrace.optimum_upper mem_graphEdgeList

theorem matching_optimum_lower (G : Input) :
    (totalWeight G.weights +
      3 * ((((Greedy.matching (inputEdges G)).map Prod.snd).sum : ℚ) : ℝ)) / 2 ≤
      optimum G := by
  obtain ⟨selected, htrace, hmap⟩ := matching_has_typed_trace G
  have hc := htrace.certificate
  rw [matching_weight_sum_real G selected hmap,
    sum_map_eq_sum_toFinset selected (fun e => (G.weights e : ℝ)) hc.1]
  exact matching_energy_strong_lower G.weights selected.toFinset hc.2.2.1

end QMCNumericRuntime

end


-- Local source: ApproximationMonotonicity.lean

namespace QuantumMaxCutEnergy

theorem ApproximationRatio.mono {A : Algorithm} {α β : ℝ}
    (h : ApproximationRatio A β) (hab : α ≤ β) : ApproximationRatio A α := by
  intro G
  obtain ⟨hsound, hratio⟩ := h G
  have hopt : 0 ≤ optimum G := by
    have hzero := hsound (fun _ => false)
    exact (by positivity :
      0 ≤ (A.run G (List.ofFn (fun _ : Fin (randomBits A G) => false)) : ℝ)).trans hzero
  exact ⟨hsound, (mul_le_mul_of_nonneg_right hab hopt).trans hratio⟩


end QuantumMaxCutEnergy




-- Local source: NumericHalf.lean

noncomputable section
open scoped BigOperators

namespace QMCNumericRuntime
open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary

lemma inputEdges_nonneg (G : Input) : ∀ e ∈ inputEdges G, 0 ≤ e.2 := by
  intro a ha
  obtain ⟨e, rfl⟩ := (mem_inputEdges G a).mp ha
  change 0 ≤ (G.weights e : ℚ)
  positivity

/-- The algorithm returns this exact rational lower estimate of the energy. -/
def halfValue (G : Input) : ℚ≥0 :=
  ⟨matchingEnergyFormula (inputEdges G, Greedy.matching (inputEdges G)),
    matchingEnergyFormula_nonneg _ _ (inputEdges_nonneg G) (matching_nonneg G)⟩

lemma inputEdges_weight_sum_real (G : Input) :
    ((edgeWeightSum (inputEdges G) : ℚ) : ℝ) = totalWeight G.weights := by
  rw [inputEdges_weight_sum, Rat.cast_sum]
  simp [totalWeight]

lemma halfValue_cast (G : Input) :
    (halfValue G : ℝ) = (totalWeight G.weights +
      3 * (((Greedy.matching (inputEdges G)).map Prod.snd).sum : ℚ)) / 2 := by
  change ((matchingEnergyFormula (inputEdges G, Greedy.matching (inputEdges G)) : ℚ) : ℝ) = _
  simp only [matchingEnergyFormula, Rat.cast_div, Rat.cast_add, Rat.cast_mul,
    Rat.cast_ofNat]
  rw [inputEdges_weight_sum_real]
  rfl

theorem halfValue_bounds (G : Input) :
    (halfValue G : ℝ) ≤ optimum G ∧ (0.5 : ℝ) * optimum G ≤ (halfValue G : ℝ) := by
  rw [halfValue_cast]
  have hu := matching_optimum_upper G
  have hl := matching_optimum_lower G
  have hg : (0 : ℝ) ≤ (((Greedy.matching (inputEdges G)).map Prod.snd).sum : ℚ) := by
    exact_mod_cast matching_weight_nonneg G
  exact ⟨hl, by linarith⟩

def halfEstimator : Algorithm where
  randomFactor := 0
  randomDegree := 0
  run G _ := halfValue G

theorem halfEstimator_ratio : ApproximationRatio halfEstimator (0.5 : ℝ) := by
  intro G
  constructor
  · intro r
    exact (halfValue_bounds G).1
  · have hcard : (Fintype.card (Fin (randomBits halfEstimator G) → Bool) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    change (0.5 : ℝ) * optimum G ≤
      (∑ _r : Fin (randomBits halfEstimator G) → Bool, (halfValue G : ℝ)) /
        (Fintype.card (Fin (randomBits halfEstimator G) → Bool) : ℝ)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_div_cancel_left₀ _ hcard]
    exact (halfValue_bounds G).2

noncomputable def rationalHalfProgram :
    PolyProgram encodeRequest Ratio.encode
      (fun request : Input × List Bool => (halfValue request.1 : ℚ)) :=
  ((requestEdgesProgram.fanout (requestEdgesProgram.comp Greedy.matchingProgram)).comp
    matchingEnergyFormulaProgram).congr _ (fun _ => rfl)

noncomputable def nonnegativeHalfProgram :
    PolyProgram encodeRequest (fun q : ℚ≥0 => Ratio.encode (q : ℚ))
      (fun request : Input × List Bool => halfEstimator.run request.1 request.2) :=
  rationalHalfProgram.recode id (fun _ => rfl) (fun _ => rfl)

noncomputable def halfProgram :
    PolyProgram encodeRequest encodeValue
      (fun request : Input × List Bool => halfEstimator.run request.1 request.2) :=
  nonnegativeHalfProgram.comp nnratOutput

theorem halfEstimator_polynomialTime : PolynomialTime halfEstimator :=
  ⟨halfProgram.stock⟩

end QMCNumericRuntime

theorem solution :
    ∃ A : QuantumMaxCutEnergy.Algorithm,
      QuantumMaxCutEnergy.PolynomialTime A ∧
      QuantumMaxCutEnergy.ApproximationRatio A (0.498 : ℝ) := by
  exact ⟨QMCNumericRuntime.halfEstimator,
    QMCNumericRuntime.halfEstimator_polynomialTime,
    QuantumMaxCutEnergy.ApproximationRatio.mono
      QMCNumericRuntime.halfEstimator_ratio (by norm_num)⟩


end

#print axioms solution

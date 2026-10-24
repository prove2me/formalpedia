-- Prove2me | solution 1 for OAI.WLTime.OneTape.Symbolic.RAMWriter.correct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T21:51:41.714147+00:00
-- url     : https://prove2.me/submissions/436a3970-be4e-4b5b-b2ce-57a70e393285

import Mathlib
import Definitions.Def_WeisfeilerLeman
import Definitions.Def_OAIQWWLT000

section
-- module Solutions.OAIQW_WLTime.Turing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uJ

namespace WLTime

namespace OneTape
variable (M : OneTape)
open scoped Classical

variable {J : Type uJ}

theorem moveAt_line (d : Move) (h : ℤ) : moveAt lineShift d h = h+d.displacement := by
  cases d <;> simp [moveAt,lineShift,Move.displacement ]

theorem embed_step (C : M.Config ℤ) : M.embed (M.step lineShift C) = M.toTM.step (M.embed C) := by
  classical
  by_cases hh : C.state.val=1 ∨ C.state.val=2
  · have hc : M.step lineShift C=C := by
      cases C
      simp_all [step,action,moveAt,Function.update_eq_self]
    rw [hc]
    simp [TM.step,TM.halted,embed,hh]
  · simp only [TM.step,TM.halted,embed,hh,ite_false]
    simp only [step,action,hh,ite_false,toTM,moveAt_line]
    congr
    funext a z
    simp only [Function.update_apply]
    split <;> rename_i hz <;> simp only [hz,ite_true,ite_false]

theorem embed_run (w : List Bool) (t : ℕ) :
    M.embed (M.run lineShift (M.initial w) t)=M.toTM.run w t := by
  induction t with
  | zero => exact M.embed_initial w
  | succ t ih =>
    change M.embed ((M.step lineShift)^[t+1] (M.initial w)) = M.toTM.step^[t+1] (M.toTM.initial w)
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    rw [M.embed_step]
    exact congrArg M.toTM.step ih

end OneTape
end WLTime

namespace WLTime.TM
variable (M : TM)

theorem run_add (w : List Bool) (a b : ℕ) :
    M.run w (a+b)=M.step^[a] (M.run w b) :=
  Function.iterate_add_apply _ _ _ _

theorem step_frozen (C : M.Config) (h : M.halted C) : M.step C=C := by
  rw [step,ite_eq_left h]

theorem run_frozen (w : List Bool) {t u : ℕ} (hh : M.halted (M.run w t))
    (hu : t ≤ u) : M.run w u=M.run w t := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le hu
  rw [Nat.add_comm,M.run_add]
  exact Function.iterate_fixed (M.step_frozen _ hh) a

theorem time_halted (w : List Bool) (h : M.halts w) : M.halted (M.run w (M.time w)) := by
  simp only [time]
  split_ifs
  exact Nat.find_spec h

theorem time_le_of_halted (w : List Bool) {t : ℕ} (h : M.halted (M.run w t)) : M.time w ≤ t := by
  have hh : M.halts w := ⟨t,h⟩
  simp only [time]
  split_ifs
  exact Nat.find_min' hh h

theorem accepts_iff_at_halt (w : List Bool) {t : ℕ} (h : M.halted (M.run w t)) :
    M.accepts w ↔ (M.run w t).state.val=1 := by
  constructor
  · rintro ⟨s,hs⟩
    have hx := M.run_frozen w h (Nat.le_max_right s t)
    have hy := M.run_frozen w (Or.inl hs) (Nat.le_max_left s t)
    rw [hx] at hy
    exact congrArg (fun C : M.Config => C.state.val) hy |>.trans hs
  · intro ht; exact ⟨t,ht⟩

end WLTime.TM

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Stacks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uS uA

namespace WLTime.TypedTape

namespace Machine
variable {S : Type uS} {A : Type uA} (M : Machine S A)

theorem step_live (p : S) (z : ℤ) (tape : ℤ → Symbol A)
    (q : State S) (x : Symbol A) (d : Move)
    (h : M.transition (.inr p) (tape z)=(q,x,d)) :
    M.step ⟨.inr p,z,tape⟩=⟨q,z+d.displacement,Function.update tape z x⟩ := by
  simp only [step,action,halted,reduceCtorEq,or_self,ite_false,h]

theorem step_keep (p : S) (z : ℤ) (tape : ℤ → Symbol A)
    (q : State S) (d : Move)
    (h : M.transition (.inr p) (tape z)=(q,tape z,d)) :
    M.step ⟨.inr p,z,tape⟩=⟨q,z+d.displacement,tape⟩ := by
  rw [M.step_live p z tape q (tape z) d h]
  congr 1
  exact Function.update_eq_self _ _

theorem path_iterate (C : ℕ → Config S A) (n : ℕ)
    (h : ∀ i<n,M.step (C i)=C (i+1)) : M.step^[n] (C 0)=C n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih (fun i hi => h i (by omega))]
    exact h n (by omega)

theorem concat {C D E : Config S A} {a b : ℕ}
    (h : M.step^[a] C=D) (g : M.step^[b] D=E) : M.step^[a+b] C=E := by
  rw [Nat.add_comm,Function.iterate_add_apply,h,g]

variable [Fintype S] [Fintype A]

omit [Fintype A] in
theorem state_halted (p : State S) :
    ((M.stateEquiv p).val=1 ∨ (M.stateEquiv p).val=2) ↔ M.halted p := by
  cases p with
  | inl i => simp [halted,Fin.ext_iff]
  | inr q =>
    have h : 3 ≤ (M.stateEquiv (.inr q)).val := by
      change 3 ≤ 3+(Fintype.equivFin S q).val
      omega
    simp only [halted,reduceCtorEq,or_self,iff_false]
    omega

theorem compile_action (p : State S) (x : Symbol A) :
    M.compile.action (M.stateEquiv p) (M.symbolEquiv x) =
      (M.stateEquiv (M.action p x).1,M.symbolEquiv (M.action p x).2.1,(M.action p x).2.2) := by
  simp only [OneTape.action,M.state_halted,action]
  split_ifs <;> simp

theorem embed_step (C : Config S A) :
    M.embed (M.step C)=M.compile.step OneTape.lineShift (M.embed C) := by
  simp only [embed,step,OneTape.step,M.compile_action,OneTape.moveAt_line]
  congr 1
  funext z
  simp only [Function.update_apply]
  split <;> rfl

theorem embed_initial (w : List Bool) : M.embed (M.initial w)=M.compile.initial w := by
  unfold embed initial OneTape.initial
  congr 1
  funext z
  dsimp only
  by_cases h : 0 ≤ z ∧ z.toNat<w.length
  · simp [h,TM.symbol]
    split_ifs <;> rfl
  · simp [h]
    rfl

theorem embed_run (w : List Bool) (t : ℕ) :
    M.embed (M.run w t)=M.compile.run OneTape.lineShift (M.compile.initial w) t := by
  induction t with
  | zero => exact M.embed_initial w
  | succ t ih =>
    simp only [run,Function.iterate_succ_apply',OneTape.run] at *
    rw [M.embed_step,ih]

end Machine
end WLTime.TypedTape

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Sweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLTime.StackMachine
namespace Machine
variable (M : Machine)

 theorem stackCell_push (s : List (Fin M.alphabet)) (x : Fin M.alphabet) (i : ℕ) :
    M.stackCell (x::s) i = if i=s.length then some x else M.stackCell s i := by
  simp only [stackCell,List.reverse_cons,List.getElem?_append,List.length_reverse]
  by_cases h : i<s.length
  · rw [ite_eq_left h,ite_eq_right (by omega)]
  · rw [ite_eq_right h]
    by_cases he : i=s.length
    · simp [he]
    · have hi : s.length ≤ i := by omega
      have hx : i-s.length ≠ 0 := by omega
      rw [ite_eq_right he]
      rw [List.getElem?_eq_none (l := [x]) (by simp only [List.length_singleton]; omega)]
      rw [List.getElem?_eq_none (l := s.reverse) (by simpa using hi)]

 theorem stackCell_pop (s : List (Fin M.alphabet)) (i : ℕ) :
    M.stackCell s.tail i = if i+1=s.length then none else M.stackCell s i := by
  simp only [stackCell,← List.dropLast_reverse,List.getElem?_dropLast,List.length_reverse]
  by_cases h : i+1<s.length
  · rw [ite_eq_left (show i<s.length-1 by omega),ite_eq_right (show i+1≠s.length by omega)]
  · rw [ite_eq_right (show ¬i<s.length-1 by omega)]
    by_cases he : i+1=s.length
    · rw [ite_eq_left he]
    · rw [ite_eq_right he,List.getElem?_eq_none (by simp only [List.length_reverse]; omega)]

 theorem stackCell_none (s : List (Fin M.alphabet)) : M.stackCell s s.length=none := by
  exact List.getElem?_eq_none (by simp)

 theorem stackCell_some (s : List (Fin M.alphabet)) (i : ℕ) (hi : i<s.length) :
    (M.stackCell s i).isSome=true := by
  rw [stackCell,List.getElem?_eq_getElem (by simpa using hi)]
  rfl

 theorem storage_change (s s' : Fin M.count → List (Fin M.alphabet))
    (k : Fin M.count) (i : ℕ) (x : Option (Fin M.alphabet))
    (hj : ∀ j ≠ k,s' j=s j)
    (hk : ∀ u,M.stackCell (s' k) u=if u=i then x else M.stackCell (s k) u) :
    M.storage s'=Function.update (M.storage s) (-(i:ℤ)-2)
      (M.trackSymbol false (Function.update (M.storageTracks s (-(i:ℤ)-2)) k x)) := by
  funext z
  by_cases hz : z= -(i:ℤ)-2
  · subst z
    rw [Function.update_self,storage]
    have he : decide (-(i:ℤ)-2= -1)=false := by simp; omega
    rw [he,M.storageTracks_index,M.storageTracks_index]
    congr 1
    funext j
    by_cases h : j=k
    · subst j; simp only [Function.update_self,hk,ite_true]
    · simp only [Function.update_of_ne h,hj j h]
  · rw [Function.update_of_ne hz,storage,storage]
    congr 1
    unfold storageTracks
    split_ifs with h
    · funext j
      by_cases he : j=k
      · subst j
        rw [hk,ite_eq_right (by omega)]
      · rw [hj j he]
    · rfl

 theorem storage_push (s : Fin M.count → List (Fin M.alphabet))
    (k : Fin M.count) (x : Fin M.alphabet) :
    M.storage (Function.update s k (x::s k))=
      Function.update (M.storage s) (-((s k).length:ℤ)-2)
        (M.trackSymbol false (Function.update (M.storageTracks s (-((s k).length:ℤ)-2)) k (some x))) := by
  apply M.storage_change s _ k (s k).length (some x)
  · intro j hj; exact Function.update_of_ne hj _ _
  · intro i; rw [Function.update_self,M.stackCell_push]

 theorem storage_pop (s : Fin M.count → List (Fin M.alphabet))
    (k : Fin M.count) (hk : 0<(s k).length) :
    M.storage (Function.update s k (s k).tail)=
      Function.update (M.storage s) (-((s k).length:ℤ)-1)
        (M.trackSymbol false (Function.update (M.storageTracks s (-((s k).length:ℤ)-1)) k none)) := by
  have he : -(((s k).length-1:ℕ):ℤ)-2= -((s k).length:ℤ)-1 := by omega
  rw [← he]
  apply M.storage_change s _ k ((s k).length-1) none
  · intro j hj; exact Function.update_of_ne hj _ _
  · intro i
    rw [Function.update_self,M.stackCell_pop]
    have he : (i+1=(s k).length) ↔ (i=(s k).length-1) := by omega
    simp only [he]

 theorem seek_run (purpose : M.Purpose') (s : Fin M.count → List (Fin M.alphabet)) :
    M.sweep.step^[(s (M.purposeStack purpose)).length]
      (M.located (.inr (.seek purpose)) (-2) (M.storage s))=
      M.located (.inr (.seek purpose)) (-((s (M.purposeStack purpose)).length:ℤ)-2) (M.storage s) := by
  apply M.sweep.path_iterate (fun i =>
    M.located (.inr (.seek purpose)) (-(i:ℤ)-2) (M.storage s))
  intro i hi
  have ht : M.sweep.transition (.inr (.seek purpose)) (M.storage s (-(i:ℤ)-2))=
      (.inr (.seek purpose),M.storage s (-(i:ℤ)-2),.left) := by
    simp only [sweep,sweepTransition,M.storage_tracks,M.storageTracks_index]
    rw [M.stackCell_some _ i hi]
    rfl
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  simp only [Move.displacement,located,Nat.cast_add,Nat.cast_one]
  congr 1
  omega

 theorem return_run (p : M.Control) (s : Fin M.count → List (Fin M.alphabet))
    (n : ℕ) (h : ∀ z< -1,M.sweep.transition (.inr p) (M.storage s z)=
      (.inr p,M.storage s z,.right)) :
    M.sweep.step^[n] (M.located (.inr p) (-(n:ℤ)-1) (M.storage s))=
      M.located (.inr p) (-1) (M.storage s) := by
  have he : M.located (.inr p) (-1) (M.storage s)=
      M.located (.inr p) ((n:ℤ)-(n:ℤ)-1) (M.storage s) := by simp
  rw [he]
  have hz0 : -(n:ℤ)-1=(0:ℤ)-(n:ℤ)-1 := by omega
  rw [hz0]
  apply M.sweep.path_iterate (fun i =>
    M.located (.inr p) ((i:ℤ)-(n:ℤ)-1) (M.storage s))
  intro i hi
  have hz : (i:ℤ)-(n:ℤ)-1< -1 := by omega
  rw [located,M.sweep.step_keep _ _ _ _ _ (h _ hz)]
  simp only [Move.displacement,located,Nat.cast_add,Nat.cast_one]
  congr 1
  omega

 theorem storage_top (s : Fin M.count → List (Fin M.alphabet)) (k : Fin M.count) :
    M.storageTracks s (-((s k).length:ℤ)-1) k=(s k).head? := by
  cases he : s k with
  | nil => simp
  | cons x xs =>
    have hz : -((x::xs).length:ℤ)-1= -(xs.length:ℤ)-2 := by simp; omega
    rw [hz,M.storageTracks_index]
    change M.stackCell (s k) xs.length=_
    rw [he,M.stackCell_push,ite_eq_left rfl]
    rfl

 theorem peek_run (k : Fin M.count) (q : Fin M.states) (v : M.Tops)
    (s : Fin M.count → List (Fin M.alphabet)) :
    M.sweep.step^[2*(s k).length+2]
      (M.located (.inr (.seek (.peek k q v))) (-2) (M.storage s))=
      M.located (.inr (.returnPeek k q (Function.update v k (s k).head?))) (-1) (M.storage s) := by
  have h0 := M.seek_run (.peek k q v) s
  simp only [purposeStack] at h0
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.seek (.peek k q v))) (-((s k).length:ℤ)-2) (M.storage s))=
      M.located (.inr (.read k q v)) (-((s k).length:ℤ)-1) (M.storage s) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.seek (.peek k q v)))
        (M.storage s (-((s k).length:ℤ)-2))=
        (.inr (.read k q v),M.storage s (-((s k).length:ℤ)-2),.right) := by
      simp only [sweep,sweepTransition,purposeStack,M.storage_tracks,M.storageTracks_index,M.stackCell_none]
      rfl
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    unfold located
    congr 1
    simp only [Move.displacement]
    omega
  have h2 : M.sweep.step^[1]
      (M.located (.inr (.read k q v)) (-((s k).length:ℤ)-1) (M.storage s))=
      M.located (.inr (.returnPeek k q (Function.update v k (s k).head?)))
        (-((s k).length:ℤ)-1) (M.storage s) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.read k q v))
        (M.storage s (-((s k).length:ℤ)-1))=
        (.inr (.returnPeek k q (Function.update v k (s k).head?)),
          M.storage s (-((s k).length:ℤ)-1),.stay) := by
      simp only [sweep,sweepTransition,M.storage_tracks,M.storage_top]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    simp only [Move.displacement,add_zero,located]
  have h3 := M.return_run (.returnPeek k q (Function.update v k (s k).head?)) s (s k).length
    (by intro z hz; simp [sweep,sweepTransition,M.storage_bottom,show z≠ -1 by omega])
  have h := M.sweep.concat (M.sweep.concat (M.sweep.concat h0 h1) h2) h3
  rw [show (s k).length+1+1+(s k).length=2*(s k).length+2 by omega] at h
  exact h

 theorem partialTops_update (s : Fin M.count → List (Fin M.alphabet)) (k : Fin M.count) :
    Function.update (M.partialTops s k.val) k (s k).head?=M.partialTops s (k.val+1) := by
  funext j
  by_cases h : j=k
  · subst j; simp [partialTops]
  · rw [Function.update_of_ne h]
    unfold partialTops
    have hn : j.val≠k.val := fun he => h (Fin.ext he)
    have he : (j.val<k.val) ↔ (j.val<k.val+1) := by omega
    simp only [he]

 theorem partialTops_all (s : Fin M.count → List (Fin M.alphabet)) :
    M.partialTops s M.count=M.topTuple s := by
  funext k
  exact ite_eq_left k.isLt

 theorem finish_next (k : Fin M.count) (q : Fin M.states) (v : M.Tops)
    (s : Fin M.count → List (Fin M.alphabet)) (hk : k.val+1<M.count) :
    M.sweep.step^[1] (M.located (.inr (.returnPeek k q v)) (-1) (M.storage s))=
      M.located (.inr (.seek (.peek ⟨k.val+1,hk⟩ q v))) (-2) (M.storage s) := by
  change M.sweep.step _=_
  have ht : M.sweep.transition (.inr (.returnPeek k q v)) (M.storage s (-1))=
      (.inr (.seek (.peek ⟨k.val+1,hk⟩ q v)),M.storage s (-1),.left) := by
    simp only [sweep,sweepTransition,M.storage_bottom,decide_true,ite_true,finishPeek,dite_eq_left hk]
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  rfl

 theorem finish_last (k : Fin M.count) (q : Fin M.states) (v : M.Tops)
    (s : Fin M.count → List (Fin M.alphabet)) (hk : ¬k.val+1<M.count) :
    M.sweep.step^[1] (M.located (.inr (.returnPeek k q v)) (-1) (M.storage s))=
      M.dispatchLocation (M.transition q v) s := by
  change M.sweep.step _=_
  have ht : M.sweep.transition (.inr (.returnPeek k q v)) (M.storage s (-1))=
      M.dispatch (M.transition q v) (M.storage s (-1)) := by
    simp only [sweep,sweepTransition,M.storage_bottom,decide_true,ite_true,finishPeek,dite_eq_right hk]
  rw [located,M.sweep.step_live _ _ _ _ _ _ ht]
  cases M.transition q v <;> simp only [Function.update_eq_self] <;> rfl

 theorem scan_prefix (s : Fin M.count → List (Fin M.alphabet)) (q : Fin M.states)
    (L : ℕ) (hL : ∀ k,(s k).length ≤ L) (i : ℕ) (hi : i<M.count) :
    ∃ t ≤ i*(2*L+3), M.sweep.step^[t]
      (M.located (.inr (.seek (.peek ⟨0,M.count_pos⟩ q (fun _ => none)))) (-2) (M.storage s))=
      M.located (.inr (.seek (.peek ⟨i,hi⟩ q (M.partialTops s i)))) (-2) (M.storage s) := by
  induction i with
  | zero =>
    refine ⟨0,by omega,?_⟩
    have hh : M.partialTops s 0=(fun _ => none) := by
      funext k; exact ite_eq_right (Nat.not_lt_zero _)
    rw [hh]
    rfl
  | succ i ih =>
    have hii : i<M.count := by omega
    obtain ⟨t,ht,hp⟩ := ih hii
    let k : Fin M.count := ⟨i,hii⟩
    have h1 := M.peek_run k q (M.partialTops s i) s
    rw [show i=k.val from rfl,M.partialTops_update] at h1
    have h2 := M.finish_next k q (M.partialTops s (i+1)) s hi
    refine ⟨t+(2*(s k).length+2)+1,?_,M.sweep.concat (M.sweep.concat hp h1) h2⟩
    have := hL k
    nlinarith

 theorem collect_run (s : Fin M.count → List (Fin M.alphabet)) (q : Fin M.states)
    (L : ℕ) (hL : ∀ k,(s k).length ≤ L) :
    ∃ t ≤ 1+M.count*(2*L+3),M.sweep.step^[t]
      (M.located (.inr (.start q)) (-1) (M.storage s))=
      M.dispatchLocation (M.transition q (M.topTuple s)) s := by
  have hi : M.count-1<M.count := by have := M.count_pos; omega
  let k : Fin M.count := ⟨M.count-1,hi⟩
  have he : k.val+1=M.count := by have := M.count_pos; dsimp [k]; omega
  obtain ⟨t,ht,hp⟩ := M.scan_prefix s q L hL (M.count-1) hi
  have h0 : M.sweep.step^[1] (M.located (.inr (.start q)) (-1) (M.storage s))=
      M.located (.inr (.seek (.peek ⟨0,M.count_pos⟩ q (fun _ => none)))) (-2) (M.storage s) := by
    change M.sweep.step _=_
    rw [located,M.sweep.step_keep _ _ _ _ _ (by rfl)]
    rfl
  have h1 := M.peek_run k q (M.partialTops s k.val) s
  rw [M.partialTops_update,he,M.partialTops_all] at h1
  have h2 := M.finish_last k q (M.topTuple s) s (by omega)
  refine ⟨1+t+(2*(s k).length+2)+1,?_,
    M.sweep.concat (M.sweep.concat (M.sweep.concat h0 hp) h1) h2⟩
  have hlen := hL k
  have hkval : M.count-1+1=M.count := he
  nlinarith

 theorem ret_run (s : Fin M.count → List (Fin M.alphabet)) (q : Fin M.states) (n : ℕ) :
    M.sweep.step^[n+1] (M.located (.inr (.ret q)) (-(n:ℤ)-1) (M.storage s))=
      M.located (.inr (.start q)) (-1) (M.storage s) := by
  have h0 := M.return_run (.ret q) s n
    (by intro z hz; simp [sweep,sweepTransition,M.storage_bottom,show z≠ -1 by omega])
  have h1 : M.sweep.step^[1] (M.located (.inr (.ret q)) (-1) (M.storage s))=
      M.located (.inr (.start q)) (-1) (M.storage s) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.ret q)) (M.storage s (-1))=
        (.inr (.start q),M.storage s (-1),.stay) := by
      simp only [sweep,sweepTransition,M.storage_bottom,decide_true,ite_true]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    rfl
  exact M.sweep.concat h0 h1

 theorem push_run (s : Fin M.count → List (Fin M.alphabet)) (k : Fin M.count)
    (x : Fin M.alphabet) (q : Fin M.states) :
    M.sweep.step^[2*(s k).length+2]
      (M.located (.inr (.seek (.push k x q))) (-2) (M.storage s))=
      M.located (.inr (.start q)) (-1) (M.storage (Function.update s k (x::s k))) := by
  have h0 := M.seek_run (.push k x q) s
  simp only [purposeStack] at h0
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.seek (.push k x q))) (-((s k).length:ℤ)-2) (M.storage s))=
      M.located (.inr (.ret q)) (-((s k).length:ℤ)-1)
        (M.storage (Function.update s k (x::s k))) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.seek (.push k x q)))
        (M.storage s (-((s k).length:ℤ)-2))=
        (.inr (.ret q),M.trackSymbol false
          (Function.update (M.storageTracks s (-((s k).length:ℤ)-2)) k (some x)),.right) := by
      have hz : -((s k).length:ℤ)-2≠ -1 := by omega
      simp only [sweep,sweepTransition,purposeStack,M.storage_tracks,M.storageTracks_index,
        M.stackCell_none,Option.isSome_none,Bool.false_eq_true,ite_false,M.storage_bottom,
        decide_eq_false_iff_not.mpr hz]
    rw [located,M.sweep.step_live _ _ _ _ _ _ ht,← M.storage_push]
    unfold located
    congr 1
    simp only [Move.displacement]
    omega
  have h2 := M.ret_run (Function.update s k (x::s k)) q (s k).length
  have h := M.sweep.concat (M.sweep.concat h0 h1) h2
  rw [show (s k).length+1+((s k).length+1)=2*(s k).length+2 by omega] at h
  exact h

 theorem pop_run (s : Fin M.count → List (Fin M.alphabet)) (k : Fin M.count)
    (q : Fin M.states) :
    M.sweep.step^[2*(s k).length+2]
      (M.located (.inr (.seek (.pop k q))) (-2) (M.storage s))=
      M.located (.inr (.start q)) (-1) (M.storage (Function.update s k (s k).tail)) := by
  have h0 := M.seek_run (.pop k q) s
  simp only [purposeStack] at h0
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.seek (.pop k q))) (-((s k).length:ℤ)-2) (M.storage s))=
      M.located (.inr (.erase k q)) (-((s k).length:ℤ)-1) (M.storage s) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.seek (.pop k q)))
        (M.storage s (-((s k).length:ℤ)-2))=
        (.inr (.erase k q),M.storage s (-((s k).length:ℤ)-2),.right) := by
      simp only [sweep,sweepTransition,purposeStack,M.storage_tracks,M.storageTracks_index,M.stackCell_none]
      rfl
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    unfold located
    congr 1
    simp only [Move.displacement]
    omega
  by_cases hk : (s k).length=0
  · have hs : s k=[] := List.eq_nil_of_length_eq_zero hk
    have hu : Function.update s k (s k).tail=s := by rw [hs,List.tail_nil,← hs,Function.update_eq_self]
    have h2 : M.sweep.step^[1] (M.located (.inr (.erase k q)) (-1) (M.storage s))=
        M.located (.inr (.start q)) (-1) (M.storage s) := by
      change M.sweep.step _=_
      have ht : M.sweep.transition (.inr (.erase k q)) (M.storage s (-1))=
          (.inr (.start q),M.storage s (-1),.stay) := by
        simp only [sweep,sweepTransition,M.storage_bottom,decide_true,ite_true]
      rw [located,M.sweep.step_keep _ _ _ _ _ ht]
      rfl
    simp only [hk,Nat.cast_zero,neg_zero,zero_sub] at h1
    rw [hk,hu]
    simpa only [zero_mul,zero_add] using M.sweep.concat h1 h2
  · have hpos : 0<(s k).length := by omega
    have h2 : M.sweep.step^[1]
        (M.located (.inr (.erase k q)) (-((s k).length:ℤ)-1) (M.storage s))=
        M.located (.inr (.ret q)) (-(((s k).length-1:ℕ):ℤ)-1)
          (M.storage (Function.update s k (s k).tail)) := by
      change M.sweep.step _=_
      have ht : M.sweep.transition (.inr (.erase k q))
          (M.storage s (-((s k).length:ℤ)-1))=
          (.inr (.ret q),M.trackSymbol false
            (Function.update (M.storageTracks s (-((s k).length:ℤ)-1)) k none),.right) := by
        have hz : -((s k).length:ℤ)-1≠ -1 := by omega
        simp only [sweep,sweepTransition,M.storage_tracks,M.storage_bottom,
          decide_eq_false_iff_not.mpr hz,Bool.false_eq_true,ite_false]
      rw [located,M.sweep.step_live _ _ _ _ _ _ ht,← M.storage_pop s k hpos]
      unfold located
      congr 1
      simp only [Move.displacement]
      omega
    have h3 := M.ret_run (Function.update s k (s k).tail) q ((s k).length-1)
    have h := M.sweep.concat (M.sweep.concat (M.sweep.concat h0 h1) h2) h3
    rw [show (s k).length+1+1+((s k).length-1+1)=2*(s k).length+2 by omega] at h
    exact h

 theorem dispatch_run (s : Fin M.count → List (Fin M.alphabet)) (q : Fin M.states)
    (a : Command M.count M.alphabet M.states) (L : ℕ) (hL : ∀ k,(s k).length ≤ L) :
    ∃ t ≤ 2*L+3,M.sweep.step^[t] (M.dispatchLocation a s)=
      M.sweepEmbed (M.perform ⟨.inr q,s⟩ a) := by
  cases a with
  | next q' => exact ⟨0,by omega,rfl⟩
  | halt b => exact ⟨0,by omega,rfl⟩
  | push k x q' => exact ⟨2*(s k).length+2,by have := hL k; omega,M.push_run s k x q'⟩
  | pop k q' => exact ⟨2*(s k).length+2,by have := hL k; omega,M.pop_run s k q'⟩

 theorem sweep_simulate_step (C : M.Config) (L : ℕ) (hL : ∀ k,(C.stack k).length ≤ L) :
    ∃ t ≤ 4*(M.count+1)*(L+1),M.sweep.step^[t] (M.sweepEmbed C)=M.sweepEmbed (M.step C) := by
  obtain ⟨p,s⟩ := C
  cases p with
  | inl b => exact ⟨0,by positivity,rfl⟩
  | inr q =>
    obtain ⟨t,ht,hc⟩ := M.collect_run s q L hL
    obtain ⟨u,hu,ha⟩ := M.dispatch_run s q (M.transition q (M.topTuple s)) L hL
    refine ⟨t+u,?_,M.sweep.concat hc ha⟩
    nlinarith

end Machine
end WLTime.StackMachine

end OAI
end

section
-- module Solutions.OAIQW_WLTime.TapeCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLTime.StackMachine
namespace Machine
variable (M : Machine)

 theorem rawTape_nil (z : ℤ) : M.rawTape [] z=.inl 0 := by
  simp [rawTape,TypedTape.Machine.initial]
 theorem rawTape_bit (w : List Bool) (i : ℕ) (hi : i<w.length) :
    M.rawTape w i=.inl (if w[i] then 2 else 1) := by
  simp only [rawTape,TypedTape.Machine.initial,Nat.cast_nonneg,Int.toNat_natCast,hi,and_self,ite_true]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
 theorem rawTape_beyond (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    M.rawTape w i=.inl 0 := by
  simp only [rawTape,TypedTape.Machine.initial,Nat.cast_nonneg,Int.toNat_natCast,true_and,
    ite_eq_right (by omega : ¬i<w.length)]
 theorem mixed_nonneg (u v : List Bool) (z : ℤ) (hz : 0 ≤ z) :
    M.mixed u v z=M.rawTape u z := ite_eq_left hz
 theorem mixed_neg (u v : List Bool) (z : ℤ) (hz : z<0) :
    M.mixed u v z=M.storage (M.inputStacks v) z := ite_eq_right (by omega)
 theorem mixed_bottom (u v : List Bool) (z : ℤ) :
    M.symbolBottom (M.mixed u v z)=decide (z= -1) := by
  by_cases hz : 0 ≤ z
  · rw [M.mixed_nonneg u v z hz]
    have hh : z≠ -1 := by omega
    simp only [rawTape,TypedTape.Machine.initial,decide_eq_false_iff_not.mpr hh]
    split_ifs <;> rfl
  · rw [M.mixed_neg u v z (by omega),M.storage_bottom]
 theorem inputStacks_zero (v : List Bool) :
    M.inputStacks v ⟨0,M.count_pos⟩=v.map M.inputLetter := by
  simp [inputStacks,initialConfig]
 theorem inputStacks_cons (b : Bool) (v : List Bool) :
    M.inputStacks (b::v)=Function.update (M.inputStacks v) ⟨0,M.count_pos⟩
      (M.inputLetter b::M.inputStacks v ⟨0,M.count_pos⟩) := by
  funext k
  by_cases hk : k=⟨0,M.count_pos⟩
  · subst k; simp only [Function.update_self,M.inputStacks_zero,List.map_cons]
  · have hn : k.val≠0 := fun he => hk (Fin.ext he)
    simp only [Function.update_of_ne hk,inputStacks,initialConfig,hn,ite_false]
 theorem storage_nonneg (s : Fin M.count → List (Fin M.alphabet)) (z : ℤ) (hz : 0 ≤ z) :
    M.storage s z=.inl 0 := by
  have h0 : z≠ -1 := by omega
  have h1 : ¬z< -1 := by omega
  simp only [storage,decide_eq_false_iff_not.mpr h0,storageTracks,ite_eq_right h1,trackSymbol,and_self,ite_true]
 theorem mixed_nil (v : List Bool) : M.mixed [] v=M.storage (M.inputStacks v) := by
  funext z
  by_cases hz : 0 ≤ z
  · rw [M.mixed_nonneg [] v z hz,M.rawTape_nil,M.storage_nonneg _ z hz]
  · exact M.mixed_neg [] v z (by omega)
 theorem rawTape_erase (u : List Bool) (b : Bool) :
    M.rawTape u=Function.update (M.rawTape (u++[b])) (u.length:ℤ) (.inl 0) := by
  funext z
  by_cases he : z=(u.length:ℤ)
  · subst z; rw [Function.update_self,M.rawTape_beyond u u.length (by omega)]
  · rw [Function.update_of_ne he]
    by_cases hz : 0 ≤ z
    · have hzz : z=(z.toNat:ℤ) := by omega
      rw [hzz]
      by_cases hi : z.toNat<u.length
      · rw [M.rawTape_bit u _ hi,M.rawTape_bit (u++[b]) _ (by simp; omega)]
        simp only [List.getElem_append_left hi]
      · rw [M.rawTape_beyond u _ (by omega),M.rawTape_beyond (u++[b]) _ (by simp; omega)]
    · simp only [rawTape,TypedTape.Machine.initial,hz,false_and,ite_false]
 theorem mixed_erase (u v : List Bool) (b : Bool) :
    M.mixed u v=Function.update (M.mixed (u++[b]) v) (u.length:ℤ) (.inl 0) := by
  funext z
  by_cases hz : 0 ≤ z
  · rw [M.mixed_nonneg u v z hz,M.rawTape_erase u b]
    by_cases he : z=(u.length:ℤ)
    · simp only [he,Function.update_self]
    · rw [Function.update_of_ne he,Function.update_of_ne he,M.mixed_nonneg _ _ z hz]
  · have he : z≠(u.length:ℤ) := by omega
    rw [Function.update_of_ne he,M.mixed_neg _ _ z (by omega),M.mixed_neg _ _ z (by omega)]
 theorem mixed_push (u v : List Bool) (b : Bool) :
    M.mixed u (b::v)=Function.update (M.mixed u v) (-(v.length:ℤ)-2)
      (M.trackSymbol false (Function.update (M.symbolTracks (M.mixed u v (-(v.length:ℤ)-2)))
        ⟨0,M.count_pos⟩ (some (M.inputLetter b)))) := by
  have hv : (M.inputStacks v ⟨0,M.count_pos⟩).length=v.length := by
    rw [M.inputStacks_zero,List.length_map]
  rw [M.mixed_neg u v _ (by omega),M.storage_tracks]
  have hh := M.storage_push (M.inputStacks v) ⟨0,M.count_pos⟩ (M.inputLetter b)
  rw [hv,← M.inputStacks_cons] at hh
  funext z
  by_cases hz : 0 ≤ z
  · rw [M.mixed_nonneg u (b::v) z hz,Function.update_of_ne (by omega),M.mixed_nonneg u v z hz]
  · rw [M.mixed_neg u (b::v) z (by omega),hh]
    by_cases he : z= -(v.length:ℤ)-2
    · simp only [he,Function.update_self]
    · rw [Function.update_of_ne he,Function.update_of_ne he,M.mixed_neg u v z (by omega)]

 theorem seekEnd_run (u v : List Bool) :
    M.sweep.step^[u.length] (M.located (.inr .seekEnd) 0 (M.mixed u v))=
      M.located (.inr .seekEnd) (u.length:ℤ) (M.mixed u v) := by
  apply M.sweep.path_iterate (fun i => M.located (.inr .seekEnd) (i:ℤ) (M.mixed u v))
  intro i hi
  have ht : M.sweep.transition (.inr .seekEnd) (M.mixed u v (i:ℤ))=
      (.inr .seekEnd,M.mixed u v (i:ℤ),.right) := by
    rw [M.mixed_nonneg u v _ (by omega),M.rawTape_bit u i hi]
    cases u[i] <;> simp [sweep,sweepTransition]
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  simp [located,Move.displacement]

 theorem reverse_path (p : M.Control) (tape : ℤ → M.TapeSymbol) (n : ℕ)
    (h : ∀ i<n,M.sweep.transition (.inr p) (tape (i:ℤ))=(.inr p,tape (i:ℤ),.left)) :
    M.sweep.step^[n] (M.located (.inr p) ((n:ℤ)-1) tape)=M.located (.inr p) (-1) tape := by
  have he : (-1:ℤ)=(n:ℤ)-(n:ℤ)-1 := by omega
  rw [he]
  apply M.sweep.path_iterate (fun i => M.located (.inr p) ((n:ℤ)-(i:ℤ)-1) tape)
  intro i hi
  have hz : (n:ℤ)-(i:ℤ)-1= ((n-i-1:ℕ):ℤ) := by omega
  have ht := h (n-i-1) (by omega)
  rw [← hz] at ht
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  unfold located
  congr 1
  simp only [Move.displacement,Nat.cast_add,Nat.cast_one]
  omega

 theorem mixed_return (p : M.Control) (u v : List Bool) (n : ℕ)
    (h : ∀ z< -1,M.sweep.transition (.inr p) (M.mixed u v z)=
      (.inr p,M.mixed u v z,.right)) :
    M.sweep.step^[n] (M.located (.inr p) (-(n:ℤ)-1) (M.mixed u v))=
      M.located (.inr p) (-1) (M.mixed u v) := by
  have he : (-1:ℤ)=(n:ℤ)-(n:ℤ)-1 := by omega
  rw [he]
  rw [show -(n:ℤ)-1=(0:ℤ)-(n:ℤ)-1 by omega]
  apply M.sweep.path_iterate (fun i => M.located (.inr p) ((i:ℤ)-(n:ℤ)-1) (M.mixed u v))
  intro i hi
  rw [located,M.sweep.step_keep _ _ _ _ _ (h _ (by omega))]
  unfold located
  congr 1
  simp only [Move.displacement,Nat.cast_add,Nat.cast_one]
  omega

 theorem append_run (u v : List Bool) (b : Bool) :
    M.sweep.step^[v.length] (M.located (.inr (.append (M.inputLetter b))) (-2) (M.mixed u v))=
      M.located (.inr (.append (M.inputLetter b))) (-(v.length:ℤ)-2) (M.mixed u v) := by
  apply M.sweep.path_iterate (fun i =>
    M.located (.inr (.append (M.inputLetter b))) (-(i:ℤ)-2) (M.mixed u v))
  intro i hi
  have ht : M.sweep.transition (.inr (.append (M.inputLetter b))) (M.mixed u v (-(i:ℤ)-2))=
      (.inr (.append (M.inputLetter b)),M.mixed u v (-(i:ℤ)-2),.left) := by
    rw [M.mixed_neg u v _ (by omega)]
    simp only [sweep,sweepTransition,M.storage_tracks,M.storageTracks_index,M.inputStacks_zero]
    rw [M.stackCell_some _ i (by simpa using hi)]
    rfl
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  unfold located
  congr 1
  simp only [Move.displacement,Nat.cast_add,Nat.cast_one]
  omega

 theorem seekEnd_finish (u v : List Bool) :
    M.sweep.step^[u.length+1] (M.located (.inr .seekEnd) 0 (M.mixed u v))=
      M.located (.inr .take) ((u.length:ℤ)-1) (M.mixed u v) := by
  have h1 : M.sweep.step^[1] (M.located (.inr .seekEnd) (u.length:ℤ) (M.mixed u v))=
      M.located (.inr .take) ((u.length:ℤ)-1) (M.mixed u v) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr .seekEnd) (M.mixed u v (u.length:ℤ))=
        (.inr .take,M.mixed u v (u.length:ℤ),.left) := by
      rw [M.mixed_nonneg u v _ (by omega),M.rawTape_beyond u u.length (by omega)]
      simp [sweep,sweepTransition]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    rfl
  exact M.sweep.concat (M.seekEnd_run u v) h1

 theorem take_run (u v : List Bool) (b : Bool) :
    M.sweep.step^[1] (M.located (.inr .take) (u.length:ℤ) (M.mixed (u++[b]) v))=
      M.located (.inr (.bring (M.inputLetter b))) ((u.length:ℤ)-1) (M.mixed u v) := by
  change M.sweep.step _=_
  have ht : M.sweep.transition (.inr .take) (M.mixed (u++[b]) v (u.length:ℤ))=
      (.inr (.bring (M.inputLetter b)),.inl 0,.left) := by
    have hb : M.mixed (u++[b]) v (u.length:ℤ)=.inl (if b then 2 else 1) := by
      rw [M.mixed_nonneg _ _ _ (by omega),M.rawTape_bit _ _ (by simp)]
      simp only [List.getElem_append_right (by omega : u.length ≤ u.length),Nat.sub_self,List.getElem_cons_zero]
    rw [hb]
    cases b <;> simp [sweep,sweepTransition,symbolBottom,inputLetter]
  rw [located,M.sweep.step_live _ _ _ _ _ _ ht,← M.mixed_erase]
  rfl

 theorem bring_run (u v : List Bool) (b : Bool) :
    M.sweep.step^[u.length+1]
      (M.located (.inr (.bring (M.inputLetter b))) ((u.length:ℤ)-1) (M.mixed u v))=
      M.located (.inr (.append (M.inputLetter b))) (-2) (M.mixed u v) := by
  have h0 := M.reverse_path (.bring (M.inputLetter b)) (M.mixed u v) u.length (by
    intro i hi
    have hz : (i:ℤ)≠ -1 := by omega
    simp only [sweep,sweepTransition,M.mixed_bottom,decide_eq_false_iff_not.mpr hz,
      Bool.false_eq_true,ite_false])
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.bring (M.inputLetter b))) (-1) (M.mixed u v))=
      M.located (.inr (.append (M.inputLetter b))) (-2) (M.mixed u v) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.bring (M.inputLetter b))) (M.mixed u v (-1))=
        (.inr (.append (M.inputLetter b)),M.mixed u v (-1),.left) := by
      simp only [sweep,sweepTransition,M.mixed_bottom,decide_true,ite_true]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    rfl
  exact M.sweep.concat h0 h1

 theorem append_finish (u v : List Bool) (b : Bool) :
    M.sweep.step^[v.length+1]
      (M.located (.inr (.append (M.inputLetter b))) (-2) (M.mixed u v))=
      M.located (.inr .back) (-(v.length:ℤ)-1) (M.mixed u (b::v)) := by
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.append (M.inputLetter b))) (-(v.length:ℤ)-2) (M.mixed u v))=
      M.located (.inr .back) (-(v.length:ℤ)-1) (M.mixed u (b::v)) := by
    change M.sweep.step _=_
    have hz : -(v.length:ℤ)-2≠ -1 := by omega
    have ht : M.sweep.transition (.inr (.append (M.inputLetter b))) (M.mixed u v (-(v.length:ℤ)-2))=
        (.inr .back,M.trackSymbol false
          (Function.update (M.symbolTracks (M.mixed u v (-(v.length:ℤ)-2)))
            ⟨0,M.count_pos⟩ (some (M.inputLetter b))),.right) := by
      have hv : M.symbolTracks (M.mixed u v (-(v.length:ℤ)-2)) ⟨0,M.count_pos⟩=none := by
        rw [M.mixed_neg u v _ (by omega),M.storage_tracks,M.storageTracks_index]
        change M.stackCell (M.inputStacks v ⟨0,M.count_pos⟩) v.length=none
        rw [M.inputStacks_zero,← List.length_map (f:=M.inputLetter) (as:=v),M.stackCell_none]
      simp only [sweep,sweepTransition,hv,Option.isSome_none,Bool.false_eq_true,ite_false,
        M.mixed_bottom,decide_eq_false_iff_not.mpr hz]
    rw [located,M.sweep.step_live _ _ _ _ _ _ ht,← M.mixed_push]
    unfold located
    congr 1
    simp only [Move.displacement]
    omega
  exact M.sweep.concat (M.append_run u v b) h1

 theorem back_run (u v : List Bool) (n : ℕ) :
    M.sweep.step^[n+1] (M.located (.inr .back) (-(n:ℤ)-1) (M.mixed u v))=
      M.located (.inr .seekEnd) 0 (M.mixed u v) := by
  have h0 := M.mixed_return .back u v n (by
    intro z hz
    simp only [sweep,sweepTransition,M.mixed_bottom,
      decide_eq_false_iff_not.mpr (by omega : z≠ -1),Bool.false_eq_true,ite_false])
  have h1 : M.sweep.step^[1] (M.located (.inr .back) (-1) (M.mixed u v))=
      M.located (.inr .seekEnd) 0 (M.mixed u v) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr .back) (M.mixed u v (-1))=
        (.inr .seekEnd,M.mixed u v (-1),.right) := by
      simp only [sweep,sweepTransition,M.mixed_bottom,decide_true,ite_true]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    rfl
  exact M.sweep.concat h0 h1

 theorem init_cycle (u v : List Bool) (b : Bool) :
    M.sweep.step^[2*(u.length+v.length)+6]
      (M.located (.inr .seekEnd) 0 (M.mixed (u++[b]) v))=
      M.located (.inr .seekEnd) 0 (M.mixed u (b::v)) := by
  have h0 := M.seekEnd_finish (u++[b]) v
  have he : (((u++[b]).length:ℤ)-1)=(u.length:ℤ) := by simp
  rw [he] at h0
  have h := M.sweep.concat (M.sweep.concat (M.sweep.concat (M.sweep.concat h0
    (M.take_run u v b)) (M.bring_run u v b)) (M.append_finish u v b)) (M.back_run u (b::v) v.length)
  have hn : (u++[b]).length+1+1+(u.length+1)+(v.length+1)+(v.length+1)=
      2*(u.length+v.length)+6 := by simp only [List.length_append,List.length_singleton]; omega
  rw [hn] at h
  exact h

 theorem init_empty (v : List Bool) :
    M.sweep.step^[2] (M.located (.inr .seekEnd) 0 (M.mixed [] v))=
      M.sweepEmbed (M.initialConfig v) := by
  have h0 := M.seekEnd_finish [] v
  have h1 : M.sweep.step^[1] (M.located (.inr .take) (-1) (M.mixed [] v))=
      M.sweepEmbed (M.initialConfig v) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr .take) (M.mixed [] v (-1))=
        (.inr (.start M.initial),M.mixed [] v (-1),.stay) := by
      simp only [sweep,sweepTransition,M.mixed_bottom,decide_true,ite_true]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht,M.mixed_nil]
    rfl
  exact M.sweep.concat h0 h1

 theorem init_process (u v : List Bool) :
    M.sweep.step^[u.length*(2*(u.length+v.length)+4)+2]
      (M.located (.inr .seekEnd) 0 (M.mixed u v))=M.sweepEmbed (M.initialConfig (u++v)) := by
  induction u using List.reverseRecOn generalizing v with
  | nil => simpa only [List.length_nil,zero_mul,zero_add,List.nil_append] using M.init_empty v
  | append_singleton u b ih =>
    have h0 := M.init_cycle u v b
    have h1 := ih (b::v)
    have h := M.sweep.concat h0 h1
    have he : 2*(u.length+v.length)+6+(u.length*(2*(u.length+(b::v).length)+4)+2)=
        (u++[b]).length*(2*((u++[b]).length+v.length)+4)+2 := by
      simp only [List.length_cons,List.length_append,List.length_nil]
      ring
    rw [he] at h
    simpa only [List.append_assoc,List.singleton_append] using h

end Machine
end WLTime.StackMachine

namespace WLTime.StackMachine
namespace Machine
variable (M : Machine)

 theorem storage_empty (z : ℤ) : M.storage (M.inputStacks []) z =
    if z= -1 then M.trackSymbol true (fun _ => none) else .inl 0 := by
  have hs : M.storageTracks (M.inputStacks []) z=(fun _ => none) := by
    unfold storageTracks
    split_ifs
    · funext k
      simp [stackCell,inputStacks,initialConfig]
    · rfl
  simp only [storage,hs]
  by_cases hz : z= -1
  · simp only [hz,decide_true,ite_true]
  · simp only [decide_eq_false_iff_not.mpr hz,ite_eq_right hz,trackSymbol,and_self,ite_true]

 theorem mixed_initial (w : List Bool) :
    M.mixed w []=Function.update (M.rawTape w) (-1) (M.trackSymbol true (fun _ => none)) := by
  funext z
  by_cases he : z= -1
  · subst z
    rw [Function.update_self,M.mixed_neg _ _ _ (by omega),M.storage_origin]
  · rw [Function.update_of_ne he]
    by_cases hz : 0 ≤ z
    · exact M.mixed_nonneg w [] z hz
    · rw [M.mixed_neg _ _ z (by omega),M.storage_empty,ite_eq_right he]
      simp only [rawTape,TypedTape.Machine.initial,hz,false_and,ite_false]

 theorem init_mark (w : List Bool) :
    M.sweep.run w 2=M.located (.inr .seekEnd) 0 (M.mixed w []) := by
  have h0 : M.sweep.step (M.sweep.initial w)=M.located (.inr .mark) (-1) (M.rawTape w) := by
    have hh : ¬M.sweep.halted (.inl 0) := by simp [TypedTape.Machine.halted]
    have ha : M.sweep.action (.inl 0) (M.rawTape w 0)=
        (.inr .mark,M.rawTape w 0,.left) := by
      rw [TypedTape.Machine.action,ite_eq_right hh]
      rfl
    change M.sweep.step ⟨.inl 0,0,M.rawTape w⟩=_
    simp only [TypedTape.Machine.step,ha,Function.update_eq_self]
    rfl
  change M.sweep.step (M.sweep.step (M.sweep.initial w))=_
  rw [h0,located,M.sweep.step_live _ _ _ _ _ _ (by rfl),← M.mixed_initial]
  rfl

 theorem sweep_initial (w : List Bool) :
    ∃ t ≤ 4*(w.length+1)^2,M.sweep.run w t=M.sweepEmbed (M.initialConfig w) := by
  have h := M.sweep.concat (M.init_mark w) (M.init_process w [])
  simp only [List.length_nil,Nat.add_zero,List.append_nil] at h
  refine ⟨2+(w.length*(2*w.length+4)+2),by nlinarith,h⟩

 theorem step_length (C : M.Config) (L : ℕ) (hL : ∀ k,(C.stack k).length ≤ L) :
    ∀ k,((M.step C).stack k).length ≤ L+1 := by
  intro k
  obtain ⟨p,s⟩ := C
  dsimp only at hL
  cases p with
  | inl b => exact (hL k).trans (by omega)
  | inr q =>
    simp only [step]
    cases M.transition q (fun k => (s k).head?) with
    | next q' => exact (hL k).trans (by omega)
    | halt b => exact (hL k).trans (by omega)
    | push j x q' =>
      simp only [perform,Function.update_apply]
      split_ifs with hj
      · subst k; simp only [List.length_cons]; exact Nat.add_le_add_right (hL j) 1
      · exact (hL k).trans (by omega)
    | pop j q' =>
      simp only [perform,Function.update_apply]
      split_ifs with hj
      · subst k; simp only [List.length_tail]; have := hL j; omega
      · exact (hL k).trans (by omega)

 theorem iterate_length (C : M.Config) (L : ℕ) (hL : ∀ k,(C.stack k).length ≤ L) (t : ℕ) :
    ∀ k,((M.step^[t] C).stack k).length ≤ L+t := by
  induction t with
  | zero => simpa only [Function.iterate_zero_apply,Nat.add_zero] using hL
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    simpa only [Nat.add_assoc] using M.step_length (M.step^[t] C) (L+t) ih

 theorem sweep_iterate (C : M.Config) (L : ℕ) (hL : ∀ k,(C.stack k).length ≤ L) (t : ℕ) :
    ∃ u ≤ 4*(M.count+1)*t*(L+t+1),
      M.sweep.step^[u] (M.sweepEmbed C)=M.sweepEmbed (M.step^[t] C) := by
  induction t with
  | zero => exact ⟨0,by omega,rfl⟩
  | succ t ih =>
    obtain ⟨u,hu,he⟩ := ih
    obtain ⟨v,hv,hf⟩ := M.sweep_simulate_step (M.step^[t] C) (L+t) (M.iterate_length C L hL t)
    refine ⟨u+v,?_,?_⟩
    · nlinarith
    · rw [Nat.add_comm,Function.iterate_add_apply,he,hf,Function.iterate_succ_apply']

 theorem sweep_run (w : List Bool) (t : ℕ) :
    ∃ u ≤ 8*(M.count+1)*(w.length+t+1)^2,
      M.sweep.run w u=M.sweepEmbed (M.run w t) := by
  obtain ⟨a,ha,he⟩ := M.sweep_initial w
  have hL : ∀ k,((M.initialConfig w).stack k).length ≤ w.length := by
    intro k; simp only [initialConfig]; split_ifs <;> simp
  obtain ⟨b,hb,hf⟩ := M.sweep_iterate (M.initialConfig w) w.length hL t
  refine ⟨a+b,?_,M.sweep.concat he hf⟩
  have hh : (w.length+1)^2 ≤ (w.length+t+1)^2 := by nlinarith
  have htt : t ≤ w.length+t+1 := by omega
  have hmul := Nat.mul_le_mul_right (w.length+t+1) htt
  have hprod := Nat.mul_le_mul_left (4*(M.count+1)) hmul
  nlinarith

 theorem oneTape_simulate (w : List Bool) (t : ℕ) :
    ∃ u ≤ 8*(M.count+1)*(w.length+t+1)^2,M.oneTape.run OneTape.lineShift (M.oneTape.initial w) u=
      M.sweep.embed (M.sweepEmbed (M.run w t)) := by
  obtain ⟨u,hu,he⟩ := M.sweep_run w t
  refine ⟨u,hu,?_⟩
  rw [← M.sweep.embed_run,he]

 theorem oneTape_correct (w : List Bool) (t : ℕ) (b : Bool)
    (hh : (M.run w t).state=.inl b) :
    M.oneTape.toTM.halts w ∧ M.oneTape.toTM.time w ≤ 8*(M.count+1)*(w.length+t+1)^2 ∧
      (M.oneTape.toTM.accepts w ↔ b=true) := by
  obtain ⟨u,hu,he⟩ := M.oneTape_simulate w t
  have hs : (M.oneTape.toTM.run w u).state.val=if b then 1 else 2 := by
    rw [← M.oneTape.embed_run,he]
    simp only [OneTape.embed,TypedTape.Machine.embed,sweepEmbed,located,hh]
    cases b <;> rfl
  have hx : M.oneTape.toTM.halted (M.oneTape.toTM.run w u) := by
    change (M.oneTape.toTM.run w u).state.val=1 ∨ (M.oneTape.toTM.run w u).state.val=2
    rw [hs]
    cases b <;> simp
  refine ⟨⟨u,hx⟩,(M.oneTape.toTM.time_le_of_halted w hx).trans hu,?_⟩
  rw [M.oneTape.toTM.accepts_iff_at_halt w hx]
  rw [hs]
  cases b <;> simp

end Machine
end WLTime.StackMachine

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Programs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uS uT

namespace WLTime.TypedStack

namespace Machine
variable {K : Type uK} {A : Type uA} {S : Type uS} [DecidableEq K] (M : Machine K A S)

variable [Fintype K] [Fintype A] [Fintype S]

 theorem project_perform (C : M.compile.Config) (a : Command K A S) :
    M.project (M.compile.perform C (M.encodeCommand a))=M.perform (M.project C) a := by
  cases a with
  | next q => simp only [encodeCommand,StackMachine.Machine.perform,project,Sum.map_inr,
      Equiv.symm_apply_apply,perform]
  | halt b => rfl
  | push k x q =>
    simp only [encodeCommand,StackMachine.Machine.perform,project,Sum.map_inr,
      Equiv.symm_apply_apply,perform]
    congr 1
    funext j
    by_cases hj : j=k
    · subst j
      simp only [Function.update_self,List.map_cons,M.decode_encode]
    · have hn : M.registerEquiv j≠M.registerEquiv k := fun hh => hj (M.registerEquiv.injective hh)
      simp only [Function.update_of_ne hj,Function.update_of_ne hn]
  | pop k q =>
    simp only [encodeCommand,StackMachine.Machine.perform,project,Sum.map_inr,
      Equiv.symm_apply_apply,perform]
    congr 1
    funext j
    by_cases hj : j=k
    · subst j
      simp only [Function.update_self,List.map_tail]
    · have hn : M.registerEquiv j≠M.registerEquiv k := fun hh => hj (M.registerEquiv.injective hh)
      simp only [Function.update_of_ne hj,Function.update_of_ne hn]

 theorem project_step (C : M.compile.Config) : M.project (M.compile.step C)=M.step (M.project C) := by
  obtain ⟨p,s⟩ := C
  cases p with
  | inl b => rfl
  | inr q =>
    change M.project (M.compile.perform _ (M.encodeCommand _))=_
    rw [M.project_perform]
    simp only [step,project,Sum.map_inr,List.head?_map]

 theorem project_initial (w : List Bool) : M.project (M.compile.initialConfig w)=M.initialConfig w := by
  have hi (b : Bool) : M.decodeSymbol (M.compile.inputLetter b)=M.inputLetter b := by
    cases b <;> rfl
  simp only [project,StackMachine.Machine.initialConfig,Sum.map_inr,Equiv.symm_apply_apply,initialConfig]
  congr 1
  funext k
  have hk : (M.registerEquiv k).val=0 ↔ k=M.inputStack := by
    rw [← M.register_input]
    exact Fin.ext_iff.symm.trans (M.registerEquiv.injective.eq_iff)
  simp only [hk]
  split_ifs
  · simp only [List.map_map]
    exact List.map_congr_left (fun b _ => hi b)
  · rfl

 theorem project_run (w : List Bool) (t : ℕ) : M.project (M.compile.run w t)=M.run w t := by
  induction t with
  | zero => exact M.project_initial w
  | succ t ih =>
    simp only [run,StackMachine.Machine.run,Function.iterate_succ_apply'] at *
    rw [M.project_step,ih]

 theorem compile_halt (w : List Bool) (t : ℕ) (b : Bool)
    (h : (M.run w t).state=.inl b) : (M.compile.run w t).state=.inl b := by
  rw [← M.project_run] at h
  cases he : (M.compile.run w t).state with
  | inl b' => simpa only [project,he,Sum.map_inl,id_eq,Sum.inl.injEq] using h
  | inr q => simp only [project,he,Sum.map_inr,reduceCtorEq] at h

 theorem oneTape_correct (w : List Bool) (t : ℕ) (b : Bool)
    (h : (M.run w t).state=.inl b) :
    M.compile.oneTape.toTM.halts w ∧
      M.compile.oneTape.toTM.time w ≤ 8*(Fintype.card K+1)*(w.length+t+1)^2 ∧
      (M.compile.oneTape.toTM.accepts w ↔ b=true) :=
  M.compile.oneTape_correct w t b (M.compile_halt w t b h)

end Machine
end WLTime.TypedStack

namespace WLTime.TypedStack

variable {K : Type uK} {A : Type uA} {S : Type uS} {T : Type uT} [DecidableEq K]

namespace Execution
 theorem iterate (M : Machine K A S) {q s t b out} (h : Execution M.transition q s t b out) :
    M.step^[t] ⟨.inr q,s⟩=⟨.inl b,out⟩ := by
  induction h with
  | @halt q s b h =>
    change M.perform ⟨.inr q,s⟩ (M.transition q (tops s))=⟨.inl b,s⟩
    rw [h]
    rfl
  | @next q s q' t b out h tail ih =>
    rw [Function.iterate_succ_apply]
    change M.step^[t] (M.perform ⟨.inr q,s⟩ (M.transition q (tops s)))=⟨.inl b,out⟩
    rw [h]
    exact ih
  | @push q s k x q' t b out h tail ih =>
    rw [Function.iterate_succ_apply]
    change M.step^[t] (M.perform ⟨.inr q,s⟩ (M.transition q (tops s)))=⟨.inl b,out⟩
    rw [h]
    exact ih
  | @pop q s k q' t b out h tail ih =>
    rw [Function.iterate_succ_apply]
    change M.step^[t] (M.perform ⟨.inr q,s⟩ (M.transition q (tops s)))=⟨.inl b,out⟩
    rw [h]
    exact ih

 theorem rename {tr : S → Tops K A → Command K A S} {tr' : T → Tops K A → Command K A T}
    (f : S → T) (hf : ∀ q v,tr' (f q) v=Command.rename f (tr q v))
    {q s t b out} (h : Execution tr q s t b out) : Execution tr' (f q) s t b out := by
  induction h with
  | halt h => exact .halt (by rw [hf,h]; rfl)
  | next h tail ih => exact .next (by rw [hf,h]; rfl) ih
  | push h tail ih => exact .push (by rw [hf,h]; rfl) ih
  | pop h tail ih => exact .pop (by rw [hf,h]; rfl) ih

 theorem plug {tr : S → Tops K A → Command K A S} {tr' : T → Tops K A → Command K A T}
    (f : S → T) (r : T) (hf : ∀ q v,tr' (f q) v=Command.redirect f r (tr q v))
    {q s t b mid} (h : Execution tr q s t b mid)
    {u c out} (cont : Execution tr' r mid u c out) : Execution tr' (f q) s (t+u) c out := by
  induction h with
  | halt h =>
    simpa only [Nat.add_comm] using Execution.next (by rw [hf,h]; rfl) cont
  | next h tail ih =>
    simpa only [Nat.add_right_comm] using Execution.next (by rw [hf,h]; rfl) (ih cont)
  | push h tail ih =>
    simpa only [Nat.add_right_comm] using Execution.push (by rw [hf,h]; rfl) (ih cont)
  | pop h tail ih =>
    simpa only [Nat.add_right_comm] using Execution.pop (by rw [hf,h]; rfl) (ih cont)
end Execution

namespace Code

 theorem exec_finite {c : Code K A} {s t out} (h : c.Exec s t out) :
    Execution c.transition c.entry s t false out := by
  induction h with
  | skip s => exact .halt rfl
  | push s k x =>
    exact .push (q' := (1 : Fin 2)) (by simp [entry,transition]) (.halt (by simp [transition]))
  | pushDyn s k f =>
    exact .push (q' := (1 : Fin 2)) (by simp [entry,transition]) (.halt (by simp [transition]))
  | pop s k =>
    exact .pop (q' := (1 : Fin 2)) (by simp [entry,transition]) (.halt (by simp [transition]))
  | @seq a b s mid out t u first second ih1 ih2 =>
    exact ih1.plug Sum.inl (.inr b.entry) (fun _ _ => rfl) (ih2.rename Sum.inr (fun _ _ => rfl))
  | branch_true hp body ih =>
    exact .next (by simp [entry,transition,hp]) (ih.rename (Sum.inr ∘ Sum.inl) (fun _ _ => rfl))
  | branch_false hp body ih =>
    exact .next (by simp [entry,transition,hp]) (ih.rename (Sum.inr ∘ Sum.inr) (fun _ _ => rfl))
  | loop_false hp => exact .halt (by simp [entry,transition,hp])
  | loop_true hp body rest ih1 ih2 =>
    exact .next (by simp [entry,transition,hp])
      (ih1.plug Sum.inr (.inl ()) (fun _ _ => rfl) ih2)

end Code
end WLTime.TypedStack

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K]

 theorem clear_exec (k : K) (s : Stacks K A) :
    (clear k).Exec s (3*(s k).length+1) (Function.update s k []) := by
  generalize hx : s k=xs
  induction xs generalizing s with
  | nil =>
    have hs : Function.update s k []=s := by rw [← hx]; exact Function.update_eq_self k s
    rw [hs]
    exact .loop_false (by simp [nonempty,tops,hx])
  | cons x xs ih =>
    have hstep := ih (Function.update s k xs) (by simp)
    have he : (Function.update (Function.update s k xs) k [])=Function.update s k [] := by simp
    rw [he] at hstep
    have first : Exec (.pop k) s 2 (Function.update s k xs) := by
      simpa only [hx,List.tail_cons] using Exec.pop s k
    have hh := Exec.loop_true (p:=nonempty k) (by simp [nonempty,tops,hx]) first hstep
    convert hh using 1 <;> simp [clear]
    omega

 theorem transfer_exec (a b : K) (hab : a≠b) (zero : A) (s : Stacks K A) :
    (transfer a b zero).Exec s (5*(s a).length+1)
      (Function.update (Function.update s a []) b ((s a).reverse++s b)) := by
  generalize hx : s a=xs
  induction xs generalizing s with
  | nil =>
    have hout : Function.update (Function.update s a []) b (([] : List A).reverse++s b)=s := by
      simp only [List.reverse_nil,List.nil_append]
      rw [← hx,Function.update_eq_self]
      exact Function.update_eq_self b s
    rw [hout]
    exact .loop_false (by simp [nonempty,tops,hx])
  | cons x xs ih =>
    let s₁ := Function.update s b (x::s b)
    let s₂ := Function.update s₁ a xs
    have hs₁a : s₁ a=x::xs := by simp [s₁,Function.update_of_ne hab,hx]
    have hs₂a : s₂ a=xs := by simp [s₂]
    have body : Exec (.seq (.pushDyn b (fun v => (v a).getD zero)) (.pop a)) s 4 s₂ := by
      have hp : Exec (.pushDyn b (fun v => (v a).getD zero)) s 2 s₁ := by
        simpa [tops,hx,s₁] using Exec.pushDyn s b (fun v => (v a).getD zero)
      have hq : Exec (.pop a) s₁ 2 s₂ := by
        simpa [hs₁a,s₂] using Exec.pop s₁ a
      exact .seq hp hq
    have hrest := ih s₂ hs₂a
    have hout : Function.update (Function.update s₂ a []) b (xs.reverse++s₂ b)=
        Function.update (Function.update s a []) b ((x::xs).reverse++s b) := by
      funext k
      by_cases hb : k=b
      · subst k
        simp [s₂,s₁,hab.symm,List.reverse_cons,List.append_assoc]
      · by_cases ha : k=a
        · subst k
          simp [hb]
        · simp [s₂,s₁,hb,ha]
    rw [hout] at hrest
    have hh := Exec.loop_true (p:=nonempty a) (by simp [nonempty,tops,hx]) body hrest
    convert hh using 1 <;> simp [transfer]
    omega

 theorem distribute_exec (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (zero : A) (s : Stacks K A) :
    (distribute a b c zero).Exec s (7*(s a).length+1)
      (Function.update (Function.update (Function.update s a []) b ((s a).reverse++s b))
        c ((s a).reverse++s c)) := by
  generalize hx : s a=xs
  induction xs generalizing s with
  | nil =>
    have hout : Function.update (Function.update (Function.update s a []) b ([]++s b)) c ([]++s c)=s := by
      simp only [List.nil_append]
      rw [← hx,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self]
    change Exec _ s 1 (Function.update (Function.update (Function.update s a []) b ([]++s b)) c ([]++s c))
    rw [hout]
    exact .loop_false (by simp [nonempty,tops,hx])
  | cons x xs ih =>
    let s₁ := Function.update s b (x::s b)
    let s₂ := Function.update s₁ c (x::s c)
    let s₃ := Function.update s₂ a xs
    have hs₁a : s₁ a=x::xs := by simp [s₁,hab,hx]
    have hs₁c : s₁ c=s c := by simp [s₁,hbc.symm]
    have hs₂a : s₂ a=x::xs := by simp [s₂,hac,hs₁a]
    have hs₃a : s₃ a=xs := by simp [s₃]
    have first : Exec (.pushDyn b (fun v => (v a).getD zero)) s 2 s₁ := by
      simpa [tops,hx,s₁] using Exec.pushDyn s b (fun v => (v a).getD zero)
    have second : Exec (.pushDyn c (fun v => (v a).getD zero)) s₁ 2 s₂ := by
      simpa [tops,hs₁a,hs₁c,s₂] using Exec.pushDyn s₁ c (fun v => (v a).getD zero)
    have third : Exec (.pop a) s₂ 2 s₃ := by
      simpa [hs₂a,s₃] using Exec.pop s₂ a
    have body := Exec.seq first (Exec.seq second third)
    have hrest := ih s₃ hs₃a
    have hout : Function.update (Function.update (Function.update s₃ a []) b (xs.reverse++s₃ b))
        c (xs.reverse++s₃ c)=Function.update (Function.update (Function.update s a [])
          b ((x::xs).reverse++s b)) c ((x::xs).reverse++s c) := by
      funext k
      by_cases hc : k=c
      · subst k
        simp [s₃,s₂,s₁,hac.symm,List.reverse_cons,List.append_assoc]
      · by_cases hb : k=b
        · subst k
          simp [s₃,s₂,s₁,hab.symm,hbc,List.reverse_cons,List.append_assoc]
        · by_cases ha : k=a
          · subst k
            simp [hc,hb]
          · simp [s₃,s₂,s₁,hc,hb,ha]
    rw [hout] at hrest
    have hh := Exec.loop_true (p:=nonempty a) (by simp [nonempty,tops,hx]) body hrest
    convert hh using 1 <;> simp [distribute]
    omega

end WLTime.TypedStack.Code

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Arithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uL

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K]

theorem copy_exec (a b tmp : K) (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp)
    (zero : A) (s : Stacks K A) (ht : s tmp=[]) :
    (copy a b tmp zero).Exec s (12*(s a).length+2) (Function.update s b (s a++s b)) := by
  let mid := Function.update (Function.update s a []) tmp (s a).reverse
  have hf : (transfer a tmp zero).Exec s (5*(s a).length+1) mid := by
    simpa only [ht,List.append_nil] using transfer_exec a tmp hat zero s
  have he := Exec.seq hf (distribute_exec tmp a b hat.symm hbt.symm hab zero mid)
  convert he using 1 <;> try rfl
  · simp [mid,List.length_reverse]
    omega
  · funext k
    by_cases hb : k=b
    · subst k
      simp [mid,hbt,hab.symm]
    · by_cases ha : k=a
      · subst k
        simp [mid,hat,hb]
      · by_cases hk : k=tmp
        · subst k
          simp [mid,hb,ha,ht]
        · simp [mid,hb,ha,hk]

theorem moveList_exec (a b tmp : K) (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp)
    (zero : A) (s : Stacks K A) (ht : s tmp=[]) :
    (moveList a b tmp zero).Exec s (10*(s a).length+2)
      (Function.update (Function.update s a []) b (s a++s b)) := by
  let mid := Function.update (Function.update s a []) tmp (s a).reverse
  have hf : (transfer a tmp zero).Exec s (5*(s a).length+1) mid := by
    simpa only [ht,List.append_nil] using transfer_exec a tmp hat zero s
  have he := Exec.seq hf (transfer_exec tmp b hbt.symm zero mid)
  convert he using 1 <;> try rfl
  · simp [mid,List.length_reverse]
    omega
  · funext k
    by_cases hb : k=b
    · subst k
      simp [mid,hbt,hab.symm]
    · by_cases ha : k=a
      · subst k
        simp [mid,hat,hb]
      · by_cases hk : k=tmp
        · subst k
          simp [mid,hb,ha,ht]
        · simp [mid,hb,ha,hk]

end WLTime.TypedStack.Code

namespace WLTime.TypedStack.Code
variable {K : Type uK} {L : Type uL} {A : Type uA} [DecidableEq K] [DecidableEq L]

theorem update_sum_inr (e : L → List A) (s : K → List A) (k : K) (xs : List A) :
    Function.update (Sum.elim e s) (.inr k) xs=Sum.elim e (Function.update s k xs) := by
  funext a
  cases a <;> simp

theorem relabel_inr_exec {c : Code K A} {s t out} (h : c.Exec s t out) (e : L → List A) :
    (c.relabel (Sum.inr : K → L ⊕ K)).Exec (Sum.elim e s) t (Sum.elim e out) := by
  induction h with
  | skip s => exact .skip _
  | push s k x => simpa only [relabel,update_sum_inr,Sum.elim_inr] using Exec.push (Sum.elim e s) (.inr k) x
  | pushDyn s k f =>
    have ht : tops (Sum.elim e s) ∘ Sum.inr=tops s := rfl
    simpa only [relabel,update_sum_inr,Sum.elim_inr,ht] using Exec.pushDyn (Sum.elim e s) (.inr k) (fun v => f (v ∘ Sum.inr))
  | pop s k => simpa only [relabel,update_sum_inr,Sum.elim_inr] using Exec.pop (Sum.elim e s) (.inr k)
  | seq first second ih1 ih2 => exact .seq ih1 ih2
  | branch_true hp body ih => exact .branch_true hp ih
  | branch_false hp body ih => exact .branch_false hp ih
  | loop_false hp => exact .loop_false hp
  | loop_true hp body rest ih1 ih2 => exact .loop_true hp ih1 ih2

end WLTime.TypedStack.Code

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} [DecidableEq K]

theorem extra_succ_update (n : ℕ) (s : Stacks K Bool) :
    Function.update (Sum.elim (extra (n+1)) s) (.inl 0)
      (Sum.elim (extra (n+1)) s (.inl 0)).tail=Sum.elim (extra n) s := by
  funext i
  cases i with
  | inl j => fin_cases j <;> simp [extra,numeral]
  | inr j => simp

theorem countdown_exec (c : Code K Bool) (f : Stacks K Bool → Stacks K Bool)
    (P : Stacks K Bool → Prop) (B : ℕ)
    (hp : ∀ s, P s → P (f s))
    (hc : ∀ s, P s → ∃ t≤B,c.Exec s t (f s))
    (n : ℕ) (s : Stacks K Bool) (hs : P s) :
    ∃ t≤n*(B+3)+1,
      (Code.loop (Code.nonempty (.inl 0))
        (.seq (c.relabel Sum.inr) (.pop (.inl 0))) : Code (Fin 2 ⊕ K) Bool).Exec
        (Sum.elim (extra n) s) t (Sum.elim (extra 0) (f^[n] s)) := by
  induction n generalizing s with
  | zero =>
    refine ⟨1,by omega,?_⟩
    exact .loop_false (by simp [Code.nonempty,tops,extra,numeral])
  | succ n ih =>
    obtain ⟨u,hu,he⟩ := hc s hs
    have he' := Code.relabel_inr_exec he (extra (n+1))
    have hb := Code.Exec.seq he' (Code.Exec.pop _ (.inl 0))
    rw [extra_succ_update] at hb
    obtain ⟨v,hv,hr⟩ := ih (f s) (hp s hs)
    have hh := Code.Exec.loop_true (p:=Code.nonempty (.inl 0))
      (by simp [Code.nonempty,tops,extra,numeral]) hb hr
    refine ⟨u+2+v+1,?_,?_⟩
    · nlinarith
    · simpa only [Function.iterate_succ_apply] using hh

theorem repeat_exec (base : K) (c : Code K Bool) (f : Stacks K Bool → Stacks K Bool)
    (P : Stacks K Bool → Prop) (B n : ℕ)
    (hp : ∀ s,P s → P (f s))
    (hc : ∀ s,P s → ∃ t≤B,c.Exec s t (f s))
    (s : Stacks K Bool) (hs : P s) (hb : s base=numeral n) :
    ∃ t≤n*(B+15)+3,
      (repeatN base c).Exec (Sum.elim (extra 0) s) t
        (Sum.elim (extra 0) (f^[n] s)) := by
  have hf := Code.copy_exec (.inr base : Fin 2 ⊕ K) (.inl 0) (.inl 1)
    (by simp) (by simp) (by simp) false (Sum.elim (extra 0) s) (by simp [extra])
  have he : Function.update (Sum.elim (extra 0) s) (.inl 0)
      (Sum.elim (extra 0) s (.inr base)++Sum.elim (extra 0) s (.inl 0))=
      Sum.elim (extra n) s := by
    funext i
    cases i with
    | inl j => fin_cases j <;> simp [extra,numeral,hb]
    | inr j => simp
  rw [he] at hf
  obtain ⟨u,hu,hr⟩ := countdown_exec c f P B hp hc n s hs
  refine ⟨_,?_,Code.Exec.seq hf hr⟩
  simp only [Sum.elim_inr,hb,numeral,List.length_replicate]
  nlinarith

end WLTime.UnaryPrograms

namespace WLTime.TypedStack.Code
variable {K : Type uK} {L : Type uL} {A : Type uA} [DecidableEq K] [DecidableEq L]

omit [DecidableEq K] [DecidableEq L] in
theorem liftStacks_apply (f : K → L) (hf : Function.Injective f)
    (frame : Stacks L A) (s : Stacks K A) (k : K) : liftStacks f frame s (f k)=s k := by
  classical
  have h : ∃ a,f a=f k := ⟨k,rfl⟩
  rw [liftStacks,dite_eq_left h]
  exact congrArg s (hf h.choose_spec)

theorem liftStacks_update (f : K → L) (hf : Function.Injective f)
    (frame : Stacks L A) (s : Stacks K A) (k : K) (xs : List A) :
    liftStacks f frame (Function.update s k xs)=Function.update (liftStacks f frame s) (f k) xs := by
  classical
  funext l
  by_cases hl : l=f k
  · subst l
    simp only [liftStacks_apply f hf,Function.update_self]
  · rw [Function.update_of_ne hl]
    unfold liftStacks
    split_ifs with h
    · have hne : h.choose≠k := by
        intro hk
        exact hl (h.choose_spec.symm.trans (congrArg f hk))
      exact Function.update_of_ne hne _ _
    · rfl

omit [DecidableEq K] [DecidableEq L] in
theorem liftStacks_tops (f : K → L) (hf : Function.Injective f)
    (frame : Stacks L A) (s : Stacks K A) : tops (liftStacks f frame s) ∘ f=tops s := by
  funext k
  simp only [Function.comp_apply,tops,liftStacks_apply f hf]

theorem relabel_exec (f : K → L) (hf : Function.Injective f)
    {c : Code K A} {s t out} (h : c.Exec s t out) (frame : Stacks L A) :
    (c.relabel f).Exec (liftStacks f frame s) t (liftStacks f frame out) := by
  induction h with
  | skip s => exact .skip _
  | push s k x =>
    simpa only [relabel,liftStacks_update f hf,liftStacks_apply f hf] using
      Exec.push (liftStacks f frame s) (f k) x
  | pushDyn s k g =>
    simpa only [relabel,liftStacks_update f hf,liftStacks_apply f hf,liftStacks_tops f hf] using
      Exec.pushDyn (liftStacks f frame s) (f k) (fun v => g (v ∘ f))
  | pop s k =>
    simpa only [relabel,liftStacks_update f hf,liftStacks_apply f hf] using
      Exec.pop (liftStacks f frame s) (f k)
  | seq first second ih1 ih2 => exact .seq ih1 ih2
  | branch_true hp body ih =>
    exact .branch_true (by simpa only [liftStacks_tops f hf] using hp) ih
  | branch_false hp body ih =>
    exact .branch_false (by simpa only [liftStacks_tops f hf] using hp) ih
  | loop_false hp => exact .loop_false (by simpa only [liftStacks_tops f hf] using hp)
  | loop_true hp body rest ih1 ih2 =>
    exact .loop_true (by simpa only [liftStacks_tops f hf] using hp) ih1 ih2

theorem relabel_exec_of_maps (f : K → L) (hf : Function.Injective f)
    {c : Code K A} {s t out} (h : c.Exec s t out) (s' out' : Stacks L A)
    (hs : ∀ k,s' (f k)=s k) (ho : ∀ k,out' (f k)=out k)
    (hframe : ∀ l,(∀ k,f k≠l) → out' l=s' l) :
    (c.relabel f).Exec s' t out' := by
  classical
  have hi : liftStacks f s' s=s' := by
    funext l
    unfold liftStacks
    split_ifs with hh
    · exact (hs hh.choose).symm.trans (congrArg s' hh.choose_spec)
    · rfl
  have he : liftStacks f s' out=out' := by
    funext l
    unfold liftStacks
    split_ifs with hh
    · exact (ho hh.choose).symm.trans (congrArg out' hh.choose_spec)
    · exact (hframe l (by simpa only [not_exists] using hh)).symm
  simpa only [hi,he] using relabel_exec f hf h s'
end WLTime.TypedStack.Code

namespace WLTime.TypedStack

namespace Program
variable {K : Type uK} [DecidableEq K]

omit [DecidableEq K] in
theorem embed_injective {a b : ℕ} (j : Fin a → Fin b) (hj : Function.Injective j) :
    Function.Injective (embed (K:=K) j) := Sum.map_injective.mpr ⟨hj,Function.injective_id⟩

theorem raise_exec (p : Program K) {s t out} (h : p.Exec s t out)
    {N : ℕ} (j : Fin p.scratch → Fin N) (hj : Function.Injective j) :
    (p.code.relabel (embed (K:=K) j)).Exec
      (Sum.elim (fun _ : Fin N => []) s) t (Sum.elim (fun _ : Fin N => []) out) := by
  apply Code.relabel_exec_of_maps _ (embed_injective j hj) h
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · intro l hl
    cases l with
    | inl x => rfl
    | inr x => exact False.elim (hl (.inr x) rfl)

theorem ofCode_exec {c : Code K Bool} {s t out} (h : c.Exec s t out) :
    (ofCode c).Exec s t out := Code.relabel_inr_exec h (fun _ => [])

theorem seq_exec {p q : Program K} {s t u mid out}
    (hp : p.Exec s t mid) (hq : q.Exec mid u out) :
    (seq p q).Exec s (t+u) out := by
  exact .seq (raise_exec p hp _ (Fin.castAdd_injective _ _))
    (raise_exec q hq _ (Fin.natAdd_injective _ _))

theorem branch_true {test : Tops K Bool → Bool} {p q : Program K} {s t out}
    (ht : test (tops s)=true) (h : p.Exec s t out) :
    (branch test p q).Exec s (t+1) out := by
  exact .branch_true ht (raise_exec p h _ (Fin.castAdd_injective _ _))

theorem branch_false {test : Tops K Bool → Bool} {p q : Program K} {s t out}
    (ht : test (tops s)=false) (h : q.Exec s t out) :
    (branch test p q).Exec s (t+1) out := by
  exact .branch_false ht (raise_exec q h _ (Fin.natAdd_injective _ _))

theorem skip_exec (s : Stacks K Bool) : (skip : Program K).Exec s 1 s := ofCode_exec (.skip s)
theorem push_exec (a : K) (b : Bool) (s : Stacks K Bool) :
    (push a b).Exec s 2 (Function.update s a (b::s a)) := ofCode_exec (.push s a b)
theorem pop_exec (a : K) (s : Stacks K Bool) :
    (pop a).Exec s 2 (Function.update s a (s a).tail) := ofCode_exec (.pop s a)
theorem clear_exec (a : K) (s : Stacks K Bool) :
    (clear a).Exec s (3*(s a).length+1) (Function.update s a []) :=
  ofCode_exec (Code.clear_exec a s)

theorem copy_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (copy a b).Exec s (12*(s a).length+2) (Function.update s b (s a++s b)) := by
  simp only [Exec,copy,ambient]
  have h := Code.copy_exec (.inr a : Fin 1 ⊕ K) (.inr b) (.inl 0)
    (by simpa using hab) (by simp) (by simp) false (Sum.elim (fun _ : Fin 1 => []) s) rfl
  convert h using 1; simp only [Sum.elim_inr,Code.update_sum_inr]; rfl

theorem local_exec {n : ℕ} {p : Program (Fin n ⊕ K)} {s t out}
    (h : p.Exec (Sum.elim (fun _ => []) s) t (Sum.elim (fun _ => []) out)) :
    (allocate p).Exec s t out := by
  apply Code.relabel_exec_of_maps _ (Equiv.injective _) h
  · intro k; cases k with
    | inl i => rfl
    | inr i => cases i <;> rfl
  · intro k; cases k with
    | inl i => rfl
    | inr i => cases i <;> rfl
  · intro l hl
    exact False.elim (hl ((merge p.scratch n).symm l) (Equiv.apply_symm_apply _ l))

theorem repeat_exec (base : K) (p : Program K) (f : Stacks K Bool → Stacks K Bool)
    (P : Stacks K Bool → Prop) (B n : ℕ)
    (hp : ∀ s,P s → P (f s))
    (hc : ∀ s,P s → ∃ t≤B,p.Exec s t (f s))
    (s : Stacks K Bool) (hs : P s) (hb : s base=UnaryPrograms.numeral n) :
    ∃ t≤n*(B+15)+3,(repeatN base p).Exec s t (f^[n] s) := by
  let g : Stacks (Fin p.scratch ⊕ K) Bool → Stacks (Fin p.scratch ⊕ K) Bool :=
    fun z => p.ambient (f (z ∘ Sum.inr))
  let Q : Stacks (Fin p.scratch ⊕ K) Bool → Prop :=
    fun z => ∃ s,z=p.ambient s ∧ P s
  have hg (s) : g (p.ambient s)=p.ambient (f s) := rfl
  have hi (n) (s) : g^[n] (p.ambient s)=p.ambient (f^[n] s) := by
    induction n generalizing s with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply,hg,ih,Function.iterate_succ_apply]
  have hp' : ∀ z,Q z → Q (g z) := by
    rintro _ ⟨s,rfl,hs⟩
    exact ⟨f s,hg s,hp s hs⟩
  have hc' : ∀ z,Q z → ∃ t≤B,p.code.Exec z t (g z) := by
    rintro _ ⟨s,rfl,hs⟩
    exact hc s hs
  obtain ⟨t,ht,he⟩ := UnaryPrograms.repeat_exec (.inr base : Fin p.scratch ⊕ K) p.code g Q B n hp' hc'
    (p.ambient s) ⟨s,rfl,hs⟩ (show p.ambient s (.inr base)=UnaryPrograms.numeral n from hb)
  rw [hi] at he
  refine ⟨t,ht,?_⟩
  apply Code.relabel_exec_of_maps _ (Equiv.injective _) he
  · intro k; cases k with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl
  · intro k; cases k with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl
  · intro l hl
    exact False.elim (hl ((merge 2 p.scratch).symm l) (Equiv.apply_symm_apply _ l))

end Program
end WLTime.TypedStack

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Expressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uL

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} [DecidableEq K]

theorem numeral_add (n m : ℕ) : numeral (n+m)=numeral n++numeral m :=
  List.replicate_add n m true

theorem mulAdd_exec (a b c : K) (hbc : b≠c)
    (s : Stacks K Bool) (na nb : ℕ) (ha : s a=numeral na) (hb : s b=numeral nb) :
    ∃t≤na*(12*nb+17)+3,
      (mulAdd a b c).Exec s t (Function.update s c (numeral (na*nb)++s c)) := by
  let f := fun z : Stacks K Bool => Function.update z c (z b++z c)
  let P := fun z : Stacks K Bool => z b=numeral nb
  have hp : ∀z,P z → P (f z) := by
    intro z hz
    simpa only [P,f,Function.update_of_ne hbc] using hz
  have hc : ∀z,P z → ∃t≤12*nb+2,(Program.copy b c).Exec z t (f z) := by
    intro z hz
    change z b=numeral nb at hz
    refine ⟨12*nb+2,le_rfl,?_⟩
    simpa only [f,hz,numeral_length] using Program.copy_exec b c hbc z
  have hi (n) : f^[n] s=Function.update s c (numeral (n*nb)++s c) := by
    induction n with
    | zero => simpa only [Function.iterate_zero,Function.id_def,Nat.zero_mul,numeral,
        List.replicate_zero,List.nil_append] using (Function.update_eq_self c s).symm
    | succ n ih =>
      rw [Function.iterate_succ_apply',ih]
      simp only [f,Function.update_of_ne hbc,Function.update_self,Function.update_idem,hb]
      congr 1
      rw [Nat.succ_mul,Nat.add_comm,numeral_add,List.append_assoc]
  obtain ⟨t,ht,he⟩ := Program.repeat_exec a (Program.copy b c) f P (12*nb+2) na hp hc s hb ha
  rw [hi] at he
  exact ⟨t,by omega,he⟩

end WLTime.UnaryPrograms

namespace WLTime.TypedStack.Program
variable {K : Type uK} {L : Type uL} [DecidableEq K] [DecidableEq L]

theorem pushes_exec (a : K) (bs : List Bool) (s : Stacks K Bool) :
    (pushes a bs).Exec s (2*bs.length+1) (Function.update s a (bs++s a)) := by
  induction bs with
  | nil => simpa only [pushes,List.length_nil,List.nil_append,Nat.mul_zero,Nat.zero_add,Function.update_eq_self]
      using skip_exec s
  | cons b bs ih =>
    have he := seq_exec ih (push_exec a b (Function.update s a (bs++s a)))
    simpa only [pushes,Function.update_self,Function.update_idem,List.cons_append,List.length_cons,
      Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm 2] using he

theorem overwrite_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (overwrite a b).Exec s (3*(s b).length+12*(s a).length+3) (Function.update s b (s a)) := by
  have h := seq_exec (clear_exec b s) (copy_exec a b hab (Function.update s b []))
  simpa only [overwrite,Function.update_of_ne hab,Function.update_self,Function.update_idem,
    List.append_nil,show 3*(s b).length+1+(12*(s a).length+2)=3*(s b).length+12*(s a).length+3 by omega] using h

theorem putNat_exec (a : K) (n : ℕ) (s : Stacks K Bool) :
    (putNat a n).Exec s (3*(s a).length+2*n+2)
      (Function.update s a (UnaryPrograms.numeral n)) := by
  have h := seq_exec (clear_exec a s) (pushes_exec a (UnaryPrograms.numeral n) (Function.update s a []))
  simpa only [putNat,Function.update_self,Function.update_idem,List.append_nil,
    UnaryPrograms.numeral_length,show 3*(s a).length+1+(2*n+1)=3*(s a).length+2*n+2 by omega] using h

theorem dropN_exec (index dest : K) (n : ℕ) (s : Stacks K Bool)
    (hi : s index=UnaryPrograms.numeral n) :
    ∃ t≤17*n+3,(dropN index dest).Exec s t (Function.update s dest ((s dest).drop n)) := by
  let f := fun s : Stacks K Bool => Function.update s dest (s dest).tail
  have hc (s : Stacks K Bool) (_ : True) : ∃t≤2,(pop dest).Exec s t (f s) := ⟨2,le_rfl,pop_exec dest s⟩
  obtain ⟨t,ht,he⟩ := repeat_exec index (pop dest) f (fun _ => True) 2 n
    (fun _ _ => trivial) hc s trivial hi
  have hf (n) : f^[n] s=Function.update s dest ((s dest).drop n) := by
    induction n with
    | zero => simpa only [Function.iterate_zero,Function.id_def,List.drop_zero] using
        (Function.update_eq_self dest s).symm
    | succ n ih =>
      rw [Function.iterate_succ_apply',ih]
      simp only [f,Function.update_self,Function.update_idem,List.tail_drop]
  rw [hf] at he
  exact ⟨t,by omega,he⟩

theorem putBit_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    ∃t≤3*(s b).length+4,(putBit a b).Exec s t
      (Function.update s b (UnaryPrograms.numeral (if (s a).headD false then 1 else 0))) := by
  have hd : (tops (Function.update s b [])) a=(s a).head? := by simp [tops,hab]
  by_cases h : (s a).headD false=true
  · have ht : (s a).head?=some true := by cases ha : s a with
        | nil => simp [ha] at h
        | cons x xs => simp_all
    have he := seq_exec (clear_exec b s)
      (branch_true (test:=fun v => v a==some true) (p:=push b true) (q:=skip) (by simp [hd,ht])
        (push_exec b true (Function.update s b [])))
    refine ⟨_,?_,by
      simpa only [putBit,h,ite_true,UnaryPrograms.numeral,List.replicate_succ,List.replicate_zero,
        Function.update_self,Function.update_idem] using he⟩
    omega
  · have ht : (s a).head?≠some true := by intro hh; cases ha : s a <;> simp_all
    have he := seq_exec (clear_exec b s)
      (branch_false (test:=fun v => v a==some true) (p:=push b true) (q:=skip) (by simp [hd,ht])
        (skip_exec (Function.update s b [])))
    refine ⟨_,?_,by
      simpa only [putBit,show (s a).headD false=false from Bool.eq_false_iff.mpr h,
        Bool.false_eq_true,ite_false,UnaryPrograms.numeral,List.replicate_zero] using he⟩
    omega

end WLTime.TypedStack.Program

namespace WLTime.NatCode
open TypedStack UnaryPrograms

variable {L : Type uL} [DecidableEq L]

theorem core_exec (op : Binary) (a b c : L) (hac : a≠c) (hbc : b≠c)
    (s : Stacks L Bool) (x y B : ℕ) (ha : s a=numeral x) (hb : s b=numeral y)
    (hx : x≤B) (hy : y≤B) (hs : (s c).length≤B) :
    ∃t≤50*(B+1)^2,(core op a b c).Exec s t (Function.update s c (numeral (op.eval x y))) := by
  have ha' : (Function.update s c []) a=numeral x := by simpa only [Function.update_of_ne hac] using ha
  have hb' : (Function.update s c []) b=numeral y := by simpa only [Function.update_of_ne hbc] using hb
  cases op with
  | add =>
    have h1 := Program.copy_exec a c hac (Function.update s c [])
    simp only [ha',Function.update_self,List.append_nil,Function.update_idem] at h1
    have h2 := Program.copy_exec b c hbc (Function.update s c (numeral x))
    simp only [Function.update_of_ne hbc,Function.update_self,hb,Function.update_idem,
      numeral_length] at h2
    have he := Program.seq_exec (Program.clear_exec c s) (Program.seq_exec h1 h2)
    refine ⟨_,?_,by
      simpa only [core,Binary.eval,numeral_length,numeral_add,Nat.add_comm x] using he⟩
    nlinarith [Nat.zero_le (B*B)]
  | mul =>
    obtain ⟨t,ht,he⟩ := mulAdd_exec a b c hbc (Function.update s c []) x y ha' hb'
    have hh := Program.seq_exec (Program.clear_exec c s) he
    refine ⟨_,?_,by simpa only [core,Binary.eval,Function.update_self,List.append_nil,Function.update_idem] using hh⟩
    have hm : x*y≤B*B := Nat.mul_le_mul hx hy
    nlinarith [Nat.zero_le (B*B)]
  | sub =>
    have h1 := Program.copy_exec a c hac (Function.update s c [])
    simp only [ha',Function.update_self,List.append_nil,Function.update_idem,numeral_length] at h1
    obtain ⟨t,ht,h2⟩ := Program.dropN_exec b c y (Function.update s c (numeral x))
      (by simpa only [Function.update_of_ne hbc] using hb)
    simp only [Function.update_self,Function.update_idem,numeral,List.drop_replicate] at h2
    have he := Program.seq_exec (Program.clear_exec c s) (Program.seq_exec h1 h2)
    refine ⟨_,?_,he⟩
    nlinarith [Nat.zero_le (B*B)]

theorem binary_exec (op : Binary) (a b c : L) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (s : Stacks L Bool) (x y B : ℕ) (ha : s a=numeral x) (hb : s b=numeral y)
    (hx : x≤B) (hy : y≤B) (hs : (s c).length≤B) :
    ∃t≤100*(B+1)^2,(binary op a b c).Exec s t
      (Function.update (Function.update (Function.update s c (numeral (op.eval x y))) a []) b []) := by
  obtain ⟨t,ht,he⟩ := core_exec op a b c hac hbc s x y B ha hb hx hy hs
  have hh := Program.seq_exec he (Program.seq_exec
    (Program.clear_exec a (Function.update s c (numeral (op.eval x y))))
    (Program.clear_exec b (Function.update (Function.update s c (numeral (op.eval x y))) a [])))
  simp only [Function.update_of_ne hac,Function.update_of_ne hab.symm,Function.update_of_ne hbc,
    ha,hb,numeral_length] at hh
  refine ⟨_,?_,hh⟩
  nlinarith [Nat.zero_le (B*B)]

theorem bitAt_exec (word index dest : L)
    (s : Stacks L Bool) (w : List Bool) (n B : ℕ) (hw : s word=w) (hi : s index=numeral n)
    (hn : n≤B) (hwl : w.length≤B) (hd : (s dest).length≤B) :
    ∃t≤100*(B+1)^2,(bitAt word index dest).Exec s t
      (Function.update s dest (numeral (if w.getD n false then 1 else 0))) := by
  let z : Stacks (Fin 1 ⊕ L) Bool := Sum.elim (fun _ => []) s
  let a : Fin 1 ⊕ L := .inl 0
  have h1 := Program.copy_exec (.inr word) a (by simp [a]) z
  have hout : Function.update z a (z (.inr word)++z a)=Function.update z a w := by simp only [z,a,Sum.elim_inr,Sum.elim_inl,hw,List.append_nil]
  rw [hout] at h1
  obtain ⟨t,ht,h2⟩ := Program.dropN_exec (.inr index) a n (Function.update z a w)
    (by simpa only [z,a,Function.update_of_ne (Sum.inr_ne_inl),Sum.elim_inr] using hi)
  simp only [Function.update_self,Function.update_idem] at h2
  obtain ⟨u,hu,h3⟩ := Program.putBit_exec a (.inr dest) (by simp [a]) (Function.update z a (w.drop n))
  simp only [Function.update_self,Function.update_of_ne (show (.inr dest : Fin 1 ⊕ L)≠a by simp [a])] at h3 hu
  have hD : ∀ (w : List Bool) (n : ℕ), (w.drop n).headD false=w.getD n false := by
    intro w n
    induction n generalizing w with
    | zero => cases w <;> rfl
    | succ n ih => cases w with
      | nil => rfl
      | cons a w => exact ih w
  rw [hD] at h3
  have h4 := Program.clear_exec a
    (Function.update (Function.update z a (w.drop n)) (.inr dest)
      (numeral (if w.getD n false then 1 else 0)))
  have he := Program.seq_exec h1 (Program.seq_exec h2 (Program.seq_exec h3 h4))
  have ho : Function.update (Function.update (Function.update z a (w.drop n)) (.inr dest)
      (numeral (if w.getD n false then 1 else 0))) a [] =
      Sum.elim (fun _ : Fin 1 => []) (Function.update s dest (numeral (if w.getD n false then 1 else 0))) := by
    funext j; cases j with
    | inl j =>
      have hj : j=0 := Subsingleton.elim _ _
      subst j
      exact Function.update_self _ _ _
    | inr j => simp only [a,z,Function.update_of_ne (Sum.inr_ne_inl),
        Function.update_apply,Sum.inr.injEq,Sum.elim_inr]
  rw [ho] at he
  refine ⟨_,?_,Program.local_exec he⟩
  have hdrop : (w.drop n).length≤w.length := by rw [List.length_drop]; omega
  simp only [Function.update_of_ne (show a≠(.inr dest : Fin 1 ⊕ L) by simp [a]),
    Function.update_self,z,Sum.elim_inr,hw] at hu ⊢
  nlinarith [Nat.zero_le (B*B)]

end WLTime.NatCode

namespace WLTime.NatCode
open TypedStack UnaryPrograms

namespace Expr
variable {K : Type uK} {L : Type uL}

theorem eval_le (σ : K → ℕ) (w : List Bool) (B : ℕ) (e : Expr K) (h : e.Bounded σ w B) :
    e.eval σ w≤B := by
  cases e with
  | const => exact h
  | var => exact h
  | binary => exact h.2.2
  | bit e => dsimp only [eval]; split_ifs <;> exact le_trans (by omega) h.2

theorem compile_exec (e : Expr K) [DecidableEq L] (ρ : K → L) (word dest : L)
    (hdw : dest≠word) (hdr : ∀ k,dest≠ρ k) (σ : K → ℕ) (w : List Bool) (B : ℕ)
    (he : e.Bounded σ w B) (hwB : w.length≤B) (s : Stacks L Bool)
    (hs : ∀ k,s (ρ k)=numeral (σ k)) (hw : s word=w) (hd : (s dest).length≤B) :
    ∃t≤e.charge*(B+1)^2,(e.compile ρ word dest).Exec s t
      (Function.update s dest (numeral (e.eval σ w))) := by
  induction e generalizing L with
  | const n =>
    refine ⟨_,?_,by simpa only [compile,eval] using Program.putNat_exec dest n s⟩
    change n≤B at he
    change 3*(s dest).length+2*n+2≤20*(B+1)^2
    nlinarith [Nat.zero_le (B*B)]
  | var k =>
    have hh := Program.overwrite_exec (ρ k) dest (hdr k).symm s
    rw [hs k,numeral_length] at hh
    refine ⟨_,?_,by simpa only [compile,eval] using hh⟩
    change σ k≤B at he
    change 3*(s dest).length+12*σ k+3≤20*(B+1)^2
    nlinarith [Nat.zero_le (B*B)]
  | binary op e f ihe ihf =>
    let z : Stacks (Fin 2 ⊕ L) Bool := Sum.elim (fun _ => []) s
    let a : Fin 2 ⊕ L := .inl 0
    let b : Fin 2 ⊕ L := .inl 1
    obtain ⟨t,ht,h1⟩ := ihe (Sum.inr ∘ ρ) (.inr word) a (by simp [a])
      (fun _ => by simp [a]) he.1 z (fun k => hs k) hw (by simp [z,a])
    obtain ⟨u,hu,h2⟩ := ihf (Sum.inr ∘ ρ) (.inr word) b (by simp [b])
      (fun _ => by simp [b]) he.2.1
      (Function.update z a (numeral (e.eval σ w)))
      (fun k => by simpa only [a,Function.comp_apply,Function.update_of_ne Sum.inr_ne_inl,z,Sum.elim_inr] using hs k)
      (by simpa only [a,Function.update_of_ne Sum.inr_ne_inl,z,Sum.elim_inr] using hw)
      (by simp only [a,b,Function.update_of_ne (by simp : (Sum.inl (1 : Fin 2) : Fin 2 ⊕ L)≠.inl 0),z,Sum.elim_inl,List.length_nil]; omega)
    let zz := Function.update (Function.update z a (numeral (e.eval σ w))) b (numeral (f.eval σ w))
    obtain ⟨v,hv,h3⟩ := binary_exec op a b (.inr dest) (by simp [a,b]) (by simp [a]) (by simp [b])
      zz (e.eval σ w) (f.eval σ w) B
      (by simp [zz,a,b]) (by simp [zz]) (e.eval_le σ w B he.1) (f.eval_le σ w B he.2.1)
      (by simpa only [zz,a,b,Function.update_of_ne Sum.inr_ne_inl,z,Sum.elim_inr] using hd)
    have hh := Program.seq_exec h1 (Program.seq_exec h2 h3)
    have ho : Function.update (Function.update (Function.update zz (.inr dest)
        (numeral (op.eval (e.eval σ w) (f.eval σ w)))) a []) b [] =
        Sum.elim (fun _ : Fin 2 => []) (Function.update s dest
          (numeral (op.eval (e.eval σ w) (f.eval σ w)))) := by
      funext j; cases j with
      | inl j => fin_cases j <;> simp [a,b,zz]
      | inr j => simp only [a,b,zz,Function.update_of_ne Sum.inr_ne_inl,
          Function.update_apply,Sum.inr.injEq,z,Sum.elim_inr]
    rw [ho] at hh
    refine ⟨t+(u+v),?_,Program.local_exec hh⟩
    change t+(u+v)≤(e.charge+f.charge+100)*(B+1)^2
    calc
      _ ≤ e.charge*(B+1)^2+(f.charge*(B+1)^2+100*(B+1)^2) := Nat.add_le_add ht (Nat.add_le_add hu hv)
      _ = _ := by ring
  | bit e ih =>
    let z : Stacks (Fin 1 ⊕ L) Bool := Sum.elim (fun _ => []) s
    let a : Fin 1 ⊕ L := .inl 0
    obtain ⟨t,ht,h1⟩ := ih (Sum.inr ∘ ρ) (.inr word) a (by simp [a])
      (fun _ => by simp [a]) he.1 z (fun k => hs k) hw (by simp [z,a])
    obtain ⟨u,hu,h2⟩ := bitAt_exec (.inr word) a (.inr dest)
      (Function.update z a (numeral (e.eval σ w))) w (e.eval σ w) B
      (by simpa only [a,Function.update_of_ne Sum.inr_ne_inl,z,Sum.elim_inr] using hw)
      (Function.update_self _ _ _) (e.eval_le σ w B he.1) hwB
      (by simpa only [a,Function.update_of_ne Sum.inr_ne_inl,z,Sum.elim_inr] using hd)
    have h3 := Program.clear_exec a
      (Function.update (Function.update z a (numeral (e.eval σ w))) (.inr dest)
        (numeral (if w.getD (e.eval σ w) false then 1 else 0)))
    have hh := Program.seq_exec h1 (Program.seq_exec h2 h3)
    have ho : Function.update (Function.update (Function.update z a (numeral (e.eval σ w))) (.inr dest)
        (numeral (if w.getD (e.eval σ w) false then 1 else 0))) a [] =
        Sum.elim (fun _ : Fin 1 => []) (Function.update s dest (numeral (e.bit.eval σ w))) := by
      funext j; cases j with
      | inl j =>
        have hj : j=0 := Subsingleton.elim _ _
        subst j
        exact Function.update_self _ _ _
      | inr j => simp only [a,z,eval,Function.update_of_ne Sum.inr_ne_inl,
          Function.update_apply,Sum.inr.injEq,Sum.elim_inr]
    rw [ho] at hh
    refine ⟨_,?_,Program.local_exec hh⟩
    simp only [a,Function.update_of_ne Sum.inl_ne_inr,Function.update_self,numeral_length]
    change t+(u+(3*e.eval σ w+1))≤(e.charge+120)*(B+1)^2
    have hv := e.eval_le σ w B he.1
    have hlin : 3*e.eval σ w+1≤20*(B+1)^2 := by nlinarith [Nat.zero_le (B*B)]
    calc
      _ ≤ e.charge*(B+1)^2+(100*(B+1)^2+20*(B+1)^2) := Nat.add_le_add ht (Nat.add_le_add hu hlin)
      _ = _ := by ring

end Expr
end WLTime.NatCode

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Predicates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uJ uT uL uP uE

namespace WLTime.NatCode
namespace Expr
variable {K : Type uK} {J : Type uJ}

 theorem bounded_mono (e : Expr K) (σ : K → ℕ) (w : List Bool) {A B : ℕ}
    (h : e.Bounded σ w A) (hAB : A≤B) : e.Bounded σ w B := by
  induction e with
  | const | var => exact h.trans hAB
  | binary op a b ha hb => exact ⟨ha h.1,hb h.2.1,h.2.2.trans hAB⟩
  | bit a ha => exact ⟨ha h.1,h.2.trans hAB⟩
end Expr

namespace Predicate
variable {K : Type uK}

 theorem code_eval (σ : K → ℕ) (w : List Bool) (p : Predicate K) :
    p.code.eval σ w=if p.Holds σ w then 1 else 0 := by
  induction p with
  | truth b => cases b <;> rfl
  | eq a b =>
    simp only [code,Expr.eval,Binary.eval,Holds]
    by_cases hab : a.eval σ w=b.eval σ w <;> simp only [hab,↓reduceIte] <;> omega
  | lt a b =>
    simp only [code,Expr.eval,Binary.eval,Holds]
    by_cases hab : a.eval σ w<b.eval σ w <;> simp only [hab,↓reduceIte] <;> omega
  | bit a => rfl
  | conj a b ha hb =>
    simp only [code,Expr.eval,Binary.eval,Holds,ha,hb]
    split_ifs <;> simp_all
  | neg a ha =>
    simp only [code,Expr.eval,Binary.eval,Holds,ha]
    split_ifs <;> simp_all

 theorem code_le_one (σ : K → ℕ) (w : List Bool) (p : Predicate K) :
    p.code.eval σ w≤1 := by rw [code_eval]; split_ifs <;> omega

 theorem code_bounded (σ : K → ℕ) (w : List Bool) (B : ℕ) (p : Predicate K)
    (h : p.Bounded σ w B) : p.code.Bounded σ w (2*B+1) := by
  have hB : B≤2*B+1 := by omega
  have h1 : 1≤2*B+1 := by omega
  induction p with
  | truth b => change (if b then 1 else 0)≤2*B+1; split_ifs <;> omega
  | eq a b =>
    have ha := a.eval_le σ w B h.1
    have hb := b.eval_le σ w B h.2
    exact ⟨h1,⟨⟨a.bounded_mono σ w h.1 hB,b.bounded_mono σ w h.2 hB,by dsimp [Binary.eval]; omega⟩,
      ⟨b.bounded_mono σ w h.2 hB,a.bounded_mono σ w h.1 hB,by dsimp [Binary.eval]; omega⟩,
      by dsimp [Expr.eval,Binary.eval]; omega⟩,by dsimp [Expr.eval,Binary.eval]; omega⟩
  | lt a b =>
    have hb := b.eval_le σ w B h.2
    exact ⟨h1,⟨h1,⟨b.bounded_mono σ w h.2 hB,a.bounded_mono σ w h.1 hB,
      by dsimp [Binary.eval]; omega⟩,by dsimp [Expr.eval,Binary.eval]; omega⟩,
      by dsimp [Expr.eval,Binary.eval]; omega⟩
  | bit a => exact ⟨a.bounded_mono σ w h hB,h1⟩
  | conj a b ha hb =>
    refine ⟨ha h.1,hb h.2,(Nat.mul_le_mul (a.code_le_one σ w) (b.code_le_one σ w)).trans ?_⟩
    exact h1
  | neg a ha => exact ⟨h1,ha h,by dsimp [Expr.eval,Binary.eval]; omega⟩

end Predicate
end WLTime.NatCode

namespace WLTime.Compression
open NatCode

namespace ReadoutName
variable {r m : ℕ} {T : Type uT} {L : Type uL}

 theorem encode_injective : Function.Injective (encode (r:=r) (m:=m) (T:=T) (L:=L)) := by
  intro x y h
  cases x <;> cases y <;> simp only [encode,Prod.mk.injEq,NameTag.horizontal.injEq,
    NameTag.vertical.injEq,reduceCtorEq,and_true,false_and] at h
  · rcases h with ⟨⟨rfl,rfl⟩,ha,hb⟩
    exact congrArg₂ _ (Fin.ext ha) (Fin.ext hb)
  · rcases h with ⟨⟨rfl,rfl⟩,ha⟩
    exact congrArg _ (Fin.ext ha)
end ReadoutName

namespace FormalName
variable {T : Type uT} {J : Type uJ}

 theorem equal_holds (σ : J → ℕ) (w : List Bool) (n u : FormalName T J) :
    (n.equal u).Holds σ w ↔ n.eval σ w=u.eval σ w := by
  simp only [equal,Predicate.Holds,decide_eq_true_eq,eval,Prod.mk.injEq]
end FormalName

namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} {J : Type uJ} (I : ConsistencyData (r+1) m P E)

 theorem mem_footprintList (K : ℕ) (b : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K)
    (n : RawName (r:=r) (m:=m) (P:=P) (E:=E) K) :
    n∈I.footprintList K b ↔ n∈I.footprint K b := by
  classical
  cases b <;> simp only [footprintList,footprint,List.mem_cons,List.not_mem_nil,or_false,
    Finset.mem_insert,Finset.mem_singleton]

 theorem footprintList_tags (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Fin m) :
    (I.footprintList K (makeBlock K t a b)).map ReadoutName.tag=I.fixedTags K t := by
  rcases t with ⟨i,t|l⟩ <;> rfl

 theorem tagSupported_iff_fixed (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K)
    (a b : Fin m) (v : I.TagValues K) :
    I.TagSupported K (makeBlock K t a b) v ↔ ∀s,s∉I.fixedTags K t → v s=0 := by
  classical
  rw [TagSupported]
  apply forall_congr'
  intro s
  rw [← I.footprintList_tags K t a b,List.mem_map]
  simp only [I.mem_footprintList,not_exists,not_and]

 theorem blockForm_fixed (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K)
    (a b : Fin m) (v : I.TagValues K) :
    I.blockForm K (makeBlock K t a b) (I.tagRead K v)=I.fixedForm K t v := by
  rcases t with ⟨i,t|l⟩ <;> rfl

 theorem blockBias_fixed (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Fin m) :
    I.blockBias K (makeBlock K t a b)=I.fixedBias K t := by
  rcases t with ⟨i,t|l⟩ <;> rfl

 theorem descriptorValid_fixed (K : ℕ) (ε : F₂) (t : BlockTag (r:=r) (P:=P) (E:=E) K)
    (a b : Fin m) (v : I.TagValues K) :
    I.DescriptorValid K ε (makeBlock K t a b,v) ↔
      I.ValidBlock K (makeBlock K t a b) ∧ I.FixedLegal K ε t v := by
  simp only [DescriptorValid,I.tagSupported_iff_fixed,I.blockForm_fixed,I.blockBias_fixed,FixedLegal]

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
open NatCode
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} {J : Type uJ} (I : ConsistencyData (r+1) m P E)

variable (D : E → Fin (r+1) → Expr J → Predicate J)
variable (Q : E → Fin (r+1) → Expr J → Expr J)

 theorem blockPredicate_holds (K : ℕ) (σ : J → ℕ) (w : List Bool)
    (hD : ∀ e i (c : Expr J) (x : Fin m),c.eval σ w=x.val →
      ((D e i c).Holds σ w ↔ x∈I.domain e i))
    (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Expr J) (x y : Fin m)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) :
    (blockPredicate D K t a b).Holds σ w ↔ I.ValidBlock K (makeBlock K t x y) := by
  rcases t with ⟨i,t|l⟩
  · cases t <;> simp only [blockPredicate,labelPredicate,Predicate.Holds,makeBlock,
      ValidBlock,LabelAllowed,true_and,hD _ _ a x ha,hD _ _ b y hb]
  · exact and_congr (hD _ _ a x ha) (hD _ _ b y hb)

 theorem matchCode_eval (K : ℕ) (σ : J → ℕ) (w : List Bool)
    (hQ : ∀ e i (c : Expr J) (x : Fin m) (hx : x∈I.domain e i),c.eval σ w=x.val →
      (Q e i c).eval σ w=(I.coord e i ⟨x,hx⟩).val)
    (l : TypeLink K E) (i : Fin (r+1)) (a : Expr J) (x : Fin m)
    (hx : x∈I.domain l.1 i) (ha : a.eval σ w=x.val) :
    (matchCode Q K l i a).eval σ w=(linkMatch K (fun e => I.coordinatePerm e i) l x).val := by
  by_cases h : l.2.val=4*K
  · simp only [matchCode,ite_eq_left h,linkMatch]
    rw [I.coordinatePerm_apply l.1 i ⟨x,hx⟩]
    exact hQ _ _ a x hx ha
  · simpa only [matchCode,ite_eq_right h,linkMatch,Equiv.refl_apply] using ha

 theorem formalFootprint_correct (K : ℕ) (σ : J → ℕ) (w : List Bool)
    (hQ : ∀ e i (c : Expr J) (x : Fin m) (hx : x∈I.domain e i),c.eval σ w=x.val →
      (Q e i c).eval σ w=(I.coord e i ⟨x,hx⟩).val)
    (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Expr J) (x y : Fin m)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) (ht : I.ValidBlock K (makeBlock K t x y)) :
    (I.formalFootprint Q K t a b).map (FormalName.eval σ w)=
      (I.footprintList K (makeBlock K t x y)).map ReadoutName.encode := by
  rcases t with ⟨i,t|l⟩
  · simp only [formalFootprint,makeBlock,footprintList,List.map_cons,List.map_nil,
      FormalName.eval,ReadoutName.encode,ha,hb]
  · simp only [formalFootprint,makeBlock,footprintList,List.map_cons,List.map_nil,
      FormalName.eval,ReadoutName.encode,ha,hb,Expr.eval,
      I.matchCode_eval Q K σ w hQ l i a x ht.1 ha,
      I.matchCode_eval Q K σ w hQ l (finRotate (r+1) i) b y ht.2 hb]

 theorem valueCode_eq_iff (K : ℕ) (v u : I.TagValues K)
    (n : RawName (r:=r) (m:=m) (P:=P) (E:=E) K) :
    I.valueCode K v n.tag=I.valueCode K u n.tag ↔ I.tagRead K v n=I.tagRead K u n := by
  rw [valueCode,valueCode,Fin.val_inj,(Fintype.equivFin _).injective.eq_iff]
  cases n <;> rfl

 theorem overlapPredicate_holds (K : ℕ) (σ : J → ℕ) (w : List Bool)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J)) :
    (overlapPredicate K l s).Holds σ w ↔ ∃ n∈l,∃u∈s,n.eval σ w=u.eval σ w := by
  rw [overlapPredicate,Predicate.holds_any]
  constructor
  · rintro ⟨p,hp,h⟩
    obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
    exact ⟨a,ha,b,hb,(FormalName.equal_holds σ w a b).mp h⟩
  · rintro ⟨a,ha,b,hb,h⟩
    exact ⟨a.equal b,List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩,
      (FormalName.equal_holds σ w a b).mpr h⟩

 theorem agreePredicate_holds (K : ℕ) (σ : J → ℕ) (w : List Bool) (v u : I.TagValues K)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J)) :
    (I.agreePredicate K v u l s).Holds σ w ↔
      ∀ n∈l,∀z∈s,n.eval σ w=z.eval σ w → I.valueCode K v n.tag=I.valueCode K u z.tag := by
  classical
  rw [agreePredicate,Predicate.holds_all]
  constructor
  · intro h n hn z hz
    have hh := h _ (List.mem_flatMap.mpr ⟨n,hn,List.mem_map.mpr ⟨z,hz,rfl⟩⟩)
    simpa only [Predicate.holds_disj,Predicate.Holds,FormalName.equal_holds,
      decide_eq_true_eq,or_iff_not_imp_left,not_not] using hh
  · intro h p hp
    obtain ⟨n,hn,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hp
    simpa only [Predicate.holds_disj,Predicate.Holds,FormalName.equal_holds,
      decide_eq_true_eq,or_iff_not_imp_left,not_not] using h n hn z hz

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
open NatCode

namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} {J : Type uJ} (I : ConsistencyData (r+1) m P E)

 theorem overlapPredicate_correct (K : ℕ) (σ : J → ℕ) (w : List Bool)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J))
    (L S : List (RawName (r:=r) (m:=m) (P:=P) (E:=E) K))
    (hL : l.map (FormalName.eval σ w)=L.map ReadoutName.encode)
    (hS : s.map (FormalName.eval σ w)=S.map ReadoutName.encode) :
    (overlapPredicate K l s).Holds σ w ↔ ∃n,n∈L ∧ n∈S := by
  rw [overlapPredicate_holds]
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    have hh : FormalName.eval σ w a ∈ l.map (FormalName.eval σ w) := List.mem_map.mpr ⟨a,ha,rfl⟩
    rw [hL] at hh
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hh
    have hh : FormalName.eval σ w b ∈ s.map (FormalName.eval σ w) := List.mem_map.mpr ⟨b,hb,rfl⟩
    rw [hS] at hh
    obtain ⟨y,hy,hf⟩ := List.mem_map.mp hh
    have hxy : x=y := ReadoutName.encode_injective (he.trans (hab.trans hf.symm))
    exact ⟨x,hx,hxy.symm ▸ hy⟩
  · rintro ⟨x,hx,hy⟩
    have hh : x.encode ∈ L.map ReadoutName.encode := List.mem_map.mpr ⟨x,hx,rfl⟩
    rw [← hL] at hh
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hh
    have hh : x.encode ∈ S.map ReadoutName.encode := List.mem_map.mpr ⟨x,hy,rfl⟩
    rw [← hS] at hh
    obtain ⟨b,hb,hf⟩ := List.mem_map.mp hh
    exact ⟨a,ha,b,hb,he.trans hf.symm⟩

 theorem agreePredicate_correct (K : ℕ) (σ : J → ℕ) (w : List Bool) (v u : I.TagValues K)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J))
    (L S : List (RawName (r:=r) (m:=m) (P:=P) (E:=E) K))
    (hL : l.map (FormalName.eval σ w)=L.map ReadoutName.encode)
    (hS : s.map (FormalName.eval σ w)=S.map ReadoutName.encode) :
    (I.agreePredicate K v u l s).Holds σ w ↔ ∀ n∈L,n∈S → I.tagRead K v n=I.tagRead K u n := by
  rw [I.agreePredicate_holds]
  constructor
  · intro h n hn hm
    have hh : n.encode ∈ L.map ReadoutName.encode := List.mem_map.mpr ⟨n,hn,rfl⟩
    rw [← hL] at hh
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hh
    have hh : n.encode ∈ S.map ReadoutName.encode := List.mem_map.mpr ⟨n,hm,rfl⟩
    rw [← hS] at hh
    obtain ⟨b,hb,hf⟩ := List.mem_map.mp hh
    have hab := h a ha b hb (he.trans hf.symm)
    have het : a.tag=n.tag := by simpa only [FormalName.eval,ReadoutName.encode_tag] using congrArg Prod.fst he
    have hft : b.tag=n.tag := by simpa only [FormalName.eval,ReadoutName.encode_tag] using congrArg Prod.fst hf
    rw [het,hft] at hab
    exact (I.valueCode_eq_iff K v u n).mp hab
  · intro h a ha b hb hab
    have hh : FormalName.eval σ w a ∈ l.map (FormalName.eval σ w) := List.mem_map.mpr ⟨a,ha,rfl⟩
    rw [hL] at hh
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hh
    have hh : FormalName.eval σ w b ∈ s.map (FormalName.eval σ w) := List.mem_map.mpr ⟨b,hb,rfl⟩
    rw [hS] at hh
    obtain ⟨y,hy,hf⟩ := List.mem_map.mp hh
    have hxy : x=y := ReadoutName.encode_injective (he.trans (hab.trans hf.symm))
    subst y
    have het : a.tag=x.tag := by simpa only [FormalName.eval,ReadoutName.encode_tag] using (congrArg Prod.fst he).symm
    have hft : b.tag=x.tag := by simpa only [FormalName.eval,ReadoutName.encode_tag] using (congrArg Prod.fst hf).symm
    rw [het,hft]
    exact (I.valueCode_eq_iff K v u x).mpr (h x hx hy)

 theorem makeBlock_eq_iff (K : ℕ) (t u : BlockTag (r:=r) (P:=P) (E:=E) K)
    (a b c d : Fin m) : makeBlock K t a b=makeBlock K u c d ↔ t=u ∧ a=c ∧ b=d := by
  rcases t with ⟨i,t|l⟩ <;> rcases u with ⟨j,u|s⟩ <;>
    simp only [makeBlock,BlockName.site.injEq,BlockName.square.injEq,Prod.mk.injEq,
      Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq] <;> tauto

 theorem sameBlockPredicate_holds (K : ℕ) (σ : J → ℕ) (w : List Bool)
    (t u : BlockTag (r:=r) (P:=P) (E:=E) K) (a b c d : Expr J) (x y z v : Fin m)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val)
    (hc : c.eval σ w=z.val) (hd : d.eval σ w=v.val) :
    (sameBlockPredicate K t u a b c d).Holds σ w ↔ makeBlock K t x y=makeBlock K u z v := by
  simp only [sameBlockPredicate,Predicate.Holds,decide_eq_true_eq,ha,hb,hc,hd,
    Fin.val_inj,makeBlock_eq_iff]

 theorem descriptor_adjacent (K : ℕ) (hK : 0<K) (hr : 1≤r) (ε : F₂)
    (v u : {v : I.Descriptor K // I.DescriptorValid K ε v}) :
    (I.valuationGraph K ε).Adj (I.descriptorEquiv K hK hr ε v) (I.descriptorEquiv K hK hr ε u) ↔
      I.RawAdjacent K v.val u.val := by
  classical
  change (_≠_ ∧ _ ∧ _) ↔ (_≠_ ∧ _ ∧ _)
  apply and_congr
  · apply not_congr
    change (⟨v.val.1,_⟩ : I.Block K) = ⟨u.val.1,_⟩ ↔ v.val.1=u.val.1
    simp only [Subtype.mk.injEq]
  · apply and_congr
    · change (I.footprint K v.val.1 ∩ I.footprint K u.val.1).Nonempty ↔ _
      simp only [Finset.Nonempty,Finset.mem_inter]
    · change (∀n∈I.footprint K v.val.1,n∈I.footprint K u.val.1 →
        (I.atBlock K v.val.1 (I.tagRead K v.val.2)).val n=
        (I.atBlock K u.val.1 (I.tagRead K u.val.2)).val n) ↔ _
      constructor
      · intro h n hn hm
        have he := h n hn hm
        rwa [I.atBlock_apply K _ _ n hn,I.atBlock_apply K _ _ n hm] at he
      · intro h n hn hm
        rw [I.atBlock_apply K _ _ n hn,I.atBlock_apply K _ _ n hm]
        exact h n hn hm

 theorem adjacencyPredicate_correct (Q : E → Fin (r+1) → Expr J → Expr J) (K : ℕ)
    (σ : J → ℕ) (w : List Bool)
    (hQ : ∀e i (a : Expr J) (x : Fin m) (hx : x∈I.domain e i),a.eval σ w=x.val →
      (Q e i a).eval σ w=(I.coord e i ⟨x,hx⟩).val)
    (t u : BlockTag (r:=r) (P:=P) (E:=E) K) (v z : I.TagValues K)
    (a b c d : Expr J) (x y p q : Fin m)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val)
    (hc : c.eval σ w=p.val) (hd : d.eval σ w=q.val)
    (ht : I.ValidBlock K (makeBlock K t x y)) (hu : I.ValidBlock K (makeBlock K u p q)) :
    (I.adjacencyPredicate Q K t u v z a b c d).Holds σ w ↔
      I.RawAdjacent K (makeBlock K t x y,v) (makeBlock K u p q,z) := by
  have hl := I.formalFootprint_correct Q K σ w hQ t a b x y ha hb ht
  have hs := I.formalFootprint_correct Q K σ w hQ u c d p q hc hd hu
  simp only [adjacencyPredicate,Predicate.Holds,sameBlockPredicate_holds K σ w t u a b c d x y p q ha hb hc hd,
    overlapPredicate_correct K σ w _ _ _ _ hl hs,I.agreePredicate_correct K σ w v z _ _ _ _ hl hs,
    RawAdjacent,I.mem_footprintList]

end ConsistencyData
end WLTime.Compression

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Digits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uJ

namespace WLTime.NatCode
namespace Expr
variable {J : Type uJ}

 theorem choose_eval (p : Predicate J) (a b : Expr J) (σ : J → ℕ) (w : List Bool) :
    (choose p a b).eval σ w=if p.Holds σ w then a.eval σ w else b.eval σ w := by
  simp only [choose,eval,Binary.eval,Predicate.code_eval]
  split_ifs <;> simp

 theorem choose_bounded (p : Predicate J) (a b : Expr J) (σ : J → ℕ) (w : List Bool)
    (B : ℕ) (hp : p.Bounded σ w B) (ha : a.Bounded σ w B) (hb : b.Bounded σ w B) :
    (choose p a b).Bounded σ w (2*B+1) := by
  have hp' := p.code_bounded σ w B hp
  have ha' := a.bounded_mono σ w ha (by omega : B≤2*B+1)
  have hb' := b.bounded_mono σ w hb (by omega : B≤2*B+1)
  have hva := a.eval_le σ w B ha
  have hvb := b.eval_le σ w B hb
  refine ⟨⟨hp',ha',?_⟩,⟨⟨by change 1≤2*B+1; omega,hp',?_⟩,hb',?_⟩,?_⟩
  · simp only [Binary.eval,Predicate.code_eval]; split_ifs <;> simp_all; omega
  · change 1-p.code.eval σ w≤2*B+1; omega
  · simp only [Binary.eval,eval,Predicate.code_eval]; split_ifs <;> simp_all; omega
  · change (choose p a b).eval σ w≤2*B+1
    rw [choose_eval]; split_ifs <;> omega

 theorem incCode_eval {m : ℕ} (x : Fin m) (M a : Expr J) (σ : J → ℕ) (w : List Bool)
    (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (incCode M a).eval σ w=(Digits.inc m x).val := by
  rw [incCode,choose_eval,Digits.inc_value]
  simp only [Predicate.Holds,eval,Binary.eval,hM,ha]

 theorem decCode_eval {m : ℕ} (x : Fin m) (M a : Expr J) (σ : J → ℕ) (w : List Bool)
    (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (decCode M a).eval σ w=((Digits.inc m).symm x).val := by
  have h := Digits.inc_value ((Digits.inc m).symm x)
  rw [Equiv.apply_symm_apply] at h
  rw [decCode,choose_eval]
  simp only [Predicate.Holds,eval,Binary.eval,hM,ha]
  have hh := ((Digits.inc m).symm x).isLt
  split_ifs at h ⊢ <;> omega
end Expr
end WLTime.NatCode

namespace WLTime.ProductBox
open NatCode
namespace Formula
variable {d q m : ℕ} {J : Type uJ}

 theorem carryDomain_correct (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (x : Fin m) (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (carryDomain p i M a).Holds σ w ↔ x∈(Box.carry p).domain i := by
  simp only [Box.carry,Digits.CarryDomain,Finset.mem_filter,Finset.mem_univ,true_and,carryDomain]
  split_ifs <;> simp only [Predicate.Holds,Expr.eval,Binary.eval,ha,hM]

 theorem carryCoord_correct (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (x : Fin m) (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (carryCoord p i M a).eval σ w=((Box.carry p).coord i x).val := by
  simp only [carryCoord,Box.carry,Digits.coordinate]
  split_ifs
  · exact Expr.incCode_eval x M a σ w hM ha
  · exact ha

 theorem borrowCoord_correct (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (x : Fin m) (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (borrowCoord p i M a).eval σ w=((Box.carry p).reverse.coord i x).val := by
  simp only [borrowCoord,Box.reverse,Box.carry,Digits.coordinate]
  split_ifs
  · exact Expr.decCode_eval x M a σ w hM ha
  · exact ha

 theorem borrowDomain_correct (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (x : Fin m) (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (borrowDomain p i M a).Holds σ w ↔ x∈(Box.carry p).reverse.domain i := by
  rw [borrowDomain,carryDomain_correct p i M _ σ w _ hM (borrowCoord_correct p i M a σ w x hM ha)]
  change (Digits.coordinate p i).symm x∈(Box.carry p).domain i ↔ _
  simp only [Box.reverse,Finset.mem_image]
  constructor
  · intro h; exact ⟨(Digits.coordinate p i).symm x,h,Equiv.apply_symm_apply _ _⟩
  · rintro ⟨y,hy,he⟩
    change Digits.coordinate p i y=x at he
    rw [← he,Equiv.symm_apply_apply]
    exact hy
end Formula
end WLTime.ProductBox

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Simulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uJ uK uAlphabet

namespace WLTime.CircuitEncoding.BoxTableau
open NatCode ProductBox
namespace Formula
variable {Alphabet : Type uAlphabet} {J : Type uJ} {d q m : ℕ}

 theorem labelDomain_correct (e : Label Alphabet d q) (M a : Expr J) (i : Fin (d+q))
    (σ : J → ℕ) (w : List Bool) (x : Fin m) (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (labelDomain e M a i).Holds σ w ↔ x∈(box e).domain i := by
  cases e with
  | left f g h t s =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [labelDomain,box,Box.product,Fin.addCases_left] using ProductBox.Formula.carryDomain_correct t.castSucc i M a σ w x hM ha
    · simpa only [labelDomain,box,Box.product,Fin.addCases_right] using ProductBox.Formula.carryDomain_correct s i M a σ w x hM ha
  | center f g h t =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [labelDomain,box,Box.product,Fin.addCases_left] using ProductBox.Formula.carryDomain_correct t.castSucc i M a σ w x hM ha
    · simp only [labelDomain,Fin.addCases_right,box,Box.product,Box.identity,Predicate.Holds,Finset.mem_univ]
  | bridge f g h => simp only [labelDomain,box,Box.identity,Predicate.Holds,Finset.mem_univ]
  | right f g h t s =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [labelDomain,box,Box.product,Fin.addCases_left] using ProductBox.Formula.carryDomain_correct t.castSucc i M a σ w x hM ha
    · simpa only [labelDomain,box,Box.product,Fin.addCases_right] using ProductBox.Formula.borrowDomain_correct s i M a σ w x hM ha
  | out f g h => simp only [labelDomain,box,Box.identity,Predicate.Holds,Finset.mem_univ]

 theorem labelCoord_correct (e : Label Alphabet d q) (M a : Expr J) (i : Fin (d+q))
    (σ : J → ℕ) (w : List Bool) (x : Fin m) (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (labelCoord e M a i).eval σ w=((box e).coord i x).val := by
  cases e with
  | left f g h t s =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [labelCoord,box,Box.product,Fin.addCases_left] using ProductBox.Formula.carryCoord_correct t.castSucc i M a σ w x hM ha
    · simpa only [labelCoord,box,Box.product,Fin.addCases_right] using ProductBox.Formula.carryCoord_correct s i M a σ w x hM ha
  | center f g h t =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [labelCoord,box,Box.product,Fin.addCases_left] using ProductBox.Formula.carryCoord_correct t.castSucc i M a σ w x hM ha
    · simpa only [labelCoord,box,Box.product,Box.identity,Fin.addCases_right,Equiv.refl_apply] using ha
  | bridge f g h => exact ha
  | right f g h t s =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [labelCoord,box,Box.product,Fin.addCases_left] using ProductBox.Formula.carryCoord_correct t.castSucc i M a σ w x hM ha
    · simpa only [labelCoord,box,Box.product,Fin.addCases_right] using ProductBox.Formula.borrowCoord_correct s i M a σ w x hM ha
  | out f g h => exact ha

 theorem position_correct [DecidableEq Alphabet] (input : Fin m → Alphabet)
    (C : Alphabet → Expr J → Predicate J) (σ : J → ℕ) (w : List Bool)
    (hC : ∀f a (x : Fin m),a.eval σ w=x.val → ((C f a).Holds σ w ↔ input x=f))
    (s : Alphabet ⊕ Fin q) (a : Expr J) (i : Fin (q+1)) (x : Fin m) (ha : a.eval σ w=x.val) :
    (position C s a i).Holds σ w ↔ x∈positionDomain input s i := by
  cases s with
  | inl f =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [position,positionDomain,Fin.cases_zero,Finset.mem_filter,Finset.mem_univ,true_and]
        using hC f a x ha
    · simp only [position,positionDomain,Fin.cases_succ,Predicate.Holds,Expr.eval,ha,
        Finset.mem_filter,Finset.mem_univ,true_and]
  | inr j =>
    simp only [position,positionDomain,Finset.mem_filter,Finset.mem_univ,true_and]
    split_ifs <;> simp_all only [Predicate.Holds,Expr.eval,true_implies,false_implies]

 theorem seed_correct [DecidableEq Alphabet] (input : Fin m → Alphabet)
    (C : Alphabet → Expr J → Predicate J) (σ : J → ℕ) (w : List Bool)
    (hC : ∀f a (x : Fin m),a.eval σ w=x.val → ((C f a).Holds σ w ↔ input x=f))
    (s : Alphabet ⊕ Fin q) (a : Expr J) (i : Fin (d+(q+1))) (x : Fin m) (ha : a.eval σ w=x.val) :
    (seed C s a i).Holds σ w ↔ x∈seedDomain input s i := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [seed,seedDomain,Fin.addCases_left,Predicate.Holds,Expr.eval,ha,
      Finset.mem_filter,Finset.mem_univ,true_and]
  · simpa only [seed,seedDomain,Fin.addCases_right] using position_correct input C σ w hC s a i x ha

 theorem test_correct (accepting : Alphabet → Prop) (f : {f // accepting f})
    (M a : Expr J) (i : Fin (d+(q+1))) (σ : J → ℕ) (w : List Bool)
    (x : Fin m) (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (test M a i).Holds σ w ↔ x∈testDomain accepting f i := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [test,testDomain,Fin.addCases_left,Predicate.Holds,Expr.eval,Binary.eval,hM,ha,
      Finset.mem_filter,Finset.mem_univ,true_and]
  · simp only [test,testDomain,Fin.addCases_right,Predicate.Holds,Finset.mem_univ]
end Formula
end WLTime.CircuitEncoding.BoxTableau

namespace WLTime.OneTape
open NatCode
variable (M : OneTape) {J : Type uJ}

 theorem inputPredicate_correct (f : M.Cell) (a : Expr J) (σ : J → ℕ) (w : List Bool)
    (x : Fin w.length) (ha : a.eval σ w=x.val) :
    (M.inputPredicate f a).Holds σ w ↔ M.inputCell w x=f := by
  classical
  simp only [inputPredicate,Predicate.holds_disj,Predicate.Holds,Expr.eval,ha,
    decide_eq_true_eq,inputCell,Prod.ext_iff]
  cases w.getD x.val false <;> by_cases hx : x.val=0 <;> simp [hx] <;> tauto
end WLTime.OneTape

namespace WLTime.NatCode
variable {J : Type uJ}
namespace Predicate
 theorem bounded_mono (p : Predicate J) (σ : J → ℕ) (w : List Bool) {A B : ℕ}
    (h : p.Bounded σ w A) (hAB : A≤B) : p.Bounded σ w B := by
  induction p with
  | truth => trivial
  | eq a b | lt a b => exact ⟨a.bounded_mono σ w h.1 hAB,b.bounded_mono σ w h.2 hAB⟩
  | bit a => exact a.bounded_mono σ w h hAB
  | conj a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | neg a ha => exact ha h

end Predicate
namespace Expr
 theorem addOne_bounded (a : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (ha : a.Bounded σ w B) : (binary .add a (.const 1)).Bounded σ w (B+1) :=
  ⟨a.bounded_mono σ w ha (by omega),by change 1≤B+1; omega,by
    change a.eval σ w+1≤B+1
    exact Nat.add_le_add_right (a.eval_le σ w B ha) 1⟩

 theorem subOne_bounded (a : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (hB : 1≤B) (ha : a.Bounded σ w B) : (binary .sub a (.const 1)).Bounded σ w B :=
  ⟨ha,hB,by change a.eval σ w-1≤B; exact (Nat.sub_le _ _).trans (a.eval_le σ w B ha)⟩

 theorem incCode_bounded (M a : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (hB : 1≤B) (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (incCode M a).Bounded σ w (5*B) := by
  have ht := addOne_bounded a σ w B ha
  have h := choose_bounded (.eq (.binary .add a (.const 1)) M) (.const 0)
    (.binary .add a (.const 1)) σ w (B+1) ⟨ht,M.bounded_mono σ w hM (by omega)⟩ (by exact Nat.zero_le _) ht
  exact (incCode M a).bounded_mono σ w h (by omega)

 theorem decCode_bounded (M a : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (hB : 1≤B) (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (decCode M a).Bounded σ w (3*B) := by
  have h := choose_bounded (.eq a (.const 0)) (.binary .sub M (.const 1))
    (.binary .sub a (.const 1)) σ w B ⟨ha,Nat.zero_le _⟩ (subOne_bounded M σ w B hB hM)
      (subOne_bounded a σ w B hB ha)
  exact (decCode M a).bounded_mono σ w h (by omega)
end Expr
end WLTime.NatCode

namespace WLTime.ProductBox.Formula
open NatCode
variable {d : ℕ} {J : Type uJ}
 theorem carryDomain_bounded (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (carryDomain p i M a).Bounded σ w (2*B) := by
  have ht := (Expr.binary .add a (.const 1)).bounded_mono σ w (Expr.addOne_bounded a σ w B ha) (by omega : B+1≤2*B)
  have hm := M.bounded_mono σ w hM (by omega : B≤2*B)
  unfold carryDomain
  split_ifs <;> first | exact ⟨ht,hm⟩ | trivial

 theorem carryCoord_bounded (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (carryCoord p i M a).Bounded σ w (5*B) := by
  unfold carryCoord
  split_ifs
  · exact Expr.incCode_bounded M a σ w B hB hM ha
  · exact a.bounded_mono σ w ha (by omega)

 theorem borrowCoord_bounded (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (borrowCoord p i M a).Bounded σ w (3*B) := by
  unfold borrowCoord
  split_ifs
  · exact Expr.decCode_bounded M a σ w B hB hM ha
  · exact a.bounded_mono σ w ha (by omega)

 theorem borrowDomain_bounded (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (borrowDomain p i M a).Bounded σ w (6*B) := by
  have h := carryDomain_bounded p i M (borrowCoord p i M a) σ w (3*B) (by omega)
    (M.bounded_mono σ w hM (by omega)) (borrowCoord_bounded p i M a σ w B hB hM ha)
  simpa only [borrowDomain,← Nat.mul_assoc] using h
end WLTime.ProductBox.Formula
namespace WLTime.CircuitEncoding.BoxTableau.Formula
open NatCode
variable {Alphabet : Type uAlphabet} {d q : ℕ} {J : Type uJ}
 theorem labelDomain_bounded (e : Label Alphabet d q) (M a : Expr J) (i : Fin (d+q))
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (labelDomain e M a i).Bounded σ w (6*B) := by
  have hcarry {n} (p : Fin (n+1)) (j : Fin n) :=
    (ProductBox.Formula.carryDomain p j M a).bounded_mono σ w
      (ProductBox.Formula.carryDomain_bounded p j M a σ w B hB hM ha) (by omega : 2*B≤6*B)
  have hborrow {n} (p : Fin (n+1)) (j : Fin n) :=
    ProductBox.Formula.borrowDomain_bounded p j M a σ w B hB hM ha
  cases e with
  | left f g h t s =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [labelDomain,Fin.addCases_left] using hcarry t.castSucc j
    · simpa only [labelDomain,Fin.addCases_right] using hcarry s j
  | center f g h t =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [labelDomain,Fin.addCases_left] using hcarry t.castSucc j
    · simp only [labelDomain,Fin.addCases_right,Predicate.Bounded]
  | bridge | out => trivial
  | right f g h t s =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [labelDomain,Fin.addCases_left] using hcarry t.castSucc j
    · simpa only [labelDomain,Fin.addCases_right] using hborrow s j

 theorem labelCoord_bounded (e : Label Alphabet d q) (M a : Expr J) (i : Fin (d+q))
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (labelCoord e M a i).Bounded σ w (6*B) := by
  have hcarry {n} (p : Fin (n+1)) (j : Fin n) :=
    (ProductBox.Formula.carryCoord p j M a).bounded_mono σ w
      (ProductBox.Formula.carryCoord_bounded p j M a σ w B hB hM ha) (by omega : 5*B≤6*B)
  have hborrow {n} (p : Fin (n+1)) (j : Fin n) :=
    (ProductBox.Formula.borrowCoord p j M a).bounded_mono σ w
      (ProductBox.Formula.borrowCoord_bounded p j M a σ w B hB hM ha) (by omega : 3*B≤6*B)
  have hid := a.bounded_mono σ w ha (by omega : B≤6*B)
  cases e with
  | left f g h t s =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [labelCoord,Fin.addCases_left] using hcarry t.castSucc j
    · simpa only [labelCoord,Fin.addCases_right] using hcarry s j
  | center f g h t =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [labelCoord,Fin.addCases_left] using hcarry t.castSucc j
    · simpa only [labelCoord,Fin.addCases_right] using hid
  | bridge | out => exact hid
  | right f g h t s =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [labelCoord,Fin.addCases_left] using hcarry t.castSucc j
    · simpa only [labelCoord,Fin.addCases_right] using hborrow s j

 theorem position_bounded (C : Alphabet → Expr J → Predicate J) (s : Alphabet ⊕ Fin q)
    (a : Expr J) (i : Fin (q+1)) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (ha : a.Bounded σ w B) (hC : ∀f,(C f a).Bounded σ w B) :
    (position C s a i).Bounded σ w B := by
  cases s with
  | inl f =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [position,Fin.cases_zero] using hC f
    · simpa only [position,Fin.cases_succ,Predicate.Bounded,Expr.Bounded,and_true] using
        (show a.Bounded σ w B ∧ 0≤B from ⟨ha,Nat.zero_le _⟩)
  | inr j =>
    simp only [position]
    split_ifs
    · exact ⟨ha,Nat.zero_le _⟩
    · trivial

 theorem seed_bounded (C : Alphabet → Expr J → Predicate J) (s : Alphabet ⊕ Fin q)
    (a : Expr J) (i : Fin (d+(q+1))) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (ha : a.Bounded σ w B) (hC : ∀f,(C f a).Bounded σ w B) :
    (seed C s a i).Bounded σ w B := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [seed,Fin.addCases_left,Predicate.Bounded,Expr.Bounded] using
      (show a.Bounded σ w B ∧ 0≤B from ⟨ha,Nat.zero_le _⟩)
  · simpa only [seed,Fin.addCases_right] using position_bounded C s a j σ w B ha hC

 theorem test_bounded (M a : Expr J) (i : Fin (d+(q+1))) (σ : J → ℕ) (w : List Bool)
    (B : ℕ) (hB : 1≤B) (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (test (d:=d) (q:=q) M a i).Bounded σ w (2*B) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [test,Fin.addCases_left,Predicate.Bounded]
    exact ⟨(Expr.binary .add a (.const 1)).bounded_mono σ w (Expr.addOne_bounded a σ w B ha) (by omega),
      M.bounded_mono σ w hM (by omega)⟩
  · simp only [test,Fin.addCases_right,Predicate.Bounded]
end WLTime.CircuitEncoding.BoxTableau.Formula

end OAI
end

section
-- module Solutions.OAIQW_WLTime.GraphFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uJ uT uP uE uA uB uA' uB' uV uW uU

namespace WLTime.OneTape
open NatCode
variable (M : OneTape) {J : Type uJ}
 theorem inputPredicate_bounded (f : M.Cell) (a : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (ha : a.Bounded σ w B) : (M.inputPredicate f a).Bounded σ w B := by
  simp only [inputPredicate,Predicate.bounded_disj,Predicate.Bounded,Expr.Bounded]
  exact ⟨⟨⟨ha,trivial⟩,ha,trivial⟩,⟨⟨⟨ha,Nat.zero_le _⟩,trivial⟩,⟨ha,Nat.zero_le _⟩,trivial⟩⟩
end WLTime.OneTape

namespace WLTime.Compression
open NatCode
namespace FormalName
variable {T : Type uT} {J : Type uJ}
 theorem equal_bounded (σ : J → ℕ) (w : List Bool) (B : ℕ) (a b : FormalName T J)
    (ha : a.Bounded σ w B) (hb : b.Bounded σ w B) : (a.equal b).Bounded σ w B := by
  exact ⟨trivial,⟨ha.1,hb.1⟩,ha.2,hb.2⟩
end FormalName
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} {J : Type uJ} (I : ConsistencyData (r+1) m P E)
variable (D : E → Fin (r+1) → Expr J → Predicate J) (Q : E → Fin (r+1) → Expr J → Expr J)

 theorem blockPredicate_bounded (K : ℕ) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Expr J)
    (hD : ∀e i,(D e i a).Bounded σ w B ∧ (D e i b).Bounded σ w B) :
    (blockPredicate D K t a b).Bounded σ w B := by
  rcases t with ⟨i,t|l⟩
  · cases t with
    | inl p => exact ⟨trivial,trivial⟩
    | inr e => exact ⟨(hD e.1 i).1,(hD e.1 (finRotate (r+1) i)).2⟩
  · exact ⟨(hD l.1 i).1,(hD l.1 (finRotate (r+1) i)).2⟩

 theorem validPredicate_bounded (K : ℕ) (ε : F₂) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (t : BlockTag (r:=r) (P:=P) (E:=E) K) (v : I.TagValues K) (a b : Expr J)
    (hD : ∀e i,(D e i a).Bounded σ w B ∧ (D e i b).Bounded σ w B) :
    (I.validPredicate D K ε t v a b).Bounded σ w B :=
  ⟨blockPredicate_bounded D K σ w B t a b hD,trivial⟩

 theorem formalFootprint_bounded (K : ℕ) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Expr J)
    (ha : a.Bounded σ w B) (hb : b.Bounded σ w B)
    (hQ : ∀e i,(Q e i a).Bounded σ w B ∧ (Q e i b).Bounded σ w B) :
    ∀n∈I.formalFootprint Q K t a b,n.Bounded σ w B := by
  rcases t with ⟨i,t|l⟩
  · intro n hn
    simp only [formalFootprint,List.mem_cons,List.not_mem_nil,or_false] at hn
    subst n
    exact ⟨ha,hb⟩
  · intro n hn
    simp only [formalFootprint,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl|rfl|rfl|rfl
    · exact ⟨ha,hb⟩
    · unfold FormalName.Bounded matchCode
      split_ifs
      · exact ⟨(hQ l.1 i).1,(hQ l.1 (finRotate (r+1) i)).2⟩
      · exact ⟨ha,hb⟩
    · exact ⟨ha,Nat.zero_le _⟩
    · exact ⟨hb,Nat.zero_le _⟩

 theorem overlapPredicate_bounded (K : ℕ) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J))
    (hl : ∀a∈l,a.Bounded σ w B) (hs : ∀b∈s,b.Bounded σ w B) :
    (overlapPredicate K l s).Bounded σ w B := by
  rw [overlapPredicate,Predicate.bounded_any]
  intro p hp
  obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
  exact FormalName.equal_bounded σ w B a b (hl a ha) (hs b hb)

 theorem agreePredicate_bounded (K : ℕ) (σ : J → ℕ) (w : List Bool) (B : ℕ) (v u : I.TagValues K)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J))
    (hl : ∀a∈l,a.Bounded σ w B) (hs : ∀b∈s,b.Bounded σ w B) :
    (I.agreePredicate K v u l s).Bounded σ w B := by
  rw [agreePredicate,Predicate.bounded_all]
  intro p hp
  obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
  exact ⟨FormalName.equal_bounded σ w B a b (hl a ha) (hs b hb),trivial⟩

 theorem adjacencyPredicate_bounded (K : ℕ) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (t u : BlockTag (r:=r) (P:=P) (E:=E) K) (v z : I.TagValues K) (a b c d : Expr J)
    (ha : a.Bounded σ w B) (hb : b.Bounded σ w B) (hc : c.Bounded σ w B) (hd : d.Bounded σ w B)
    (hQ : ∀e i,(Q e i a).Bounded σ w B ∧ (Q e i b).Bounded σ w B ∧
      (Q e i c).Bounded σ w B ∧ (Q e i d).Bounded σ w B) :
    (I.adjacencyPredicate Q K t u v z a b c d).Bounded σ w B := by
  have hl := I.formalFootprint_bounded Q K σ w B t a b ha hb (fun e i => ⟨(hQ e i).1,(hQ e i).2.1⟩)
  have hs := I.formalFootprint_bounded Q K σ w B u c d hc hd (fun e i => (hQ e i).2.2)
  exact ⟨⟨trivial,⟨ha,hc⟩,hb,hd⟩,overlapPredicate_bounded K σ w B _ _ hl hs,
    I.agreePredicate_bounded K σ w B v z _ _ hl hs⟩
end ConsistencyData
end WLTime.Compression

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression
variable (M : OneTape) (d q : ℕ)

variable {J : Type uJ}

 theorem domain_correct (N : Expr J) (σ : J → ℕ) (w : List Bool) (hN : N.eval σ w=w.length)
    (e : Edge M d q) (i : Fin (d+q+1)) (a : Expr J) (x : Fin w.length) (ha : a.eval σ w=x.val) :
    (domain M d q N e i a).Holds σ w ↔ x∈(instanceData M d q w).domain e i := by
  classical
  cases e with
  | first e | second e | third e =>
    exact BoxTableau.Formula.labelDomain_correct e N a i σ w x hN ha
  | seed s =>
    exact BoxTableau.Formula.seed_correct (M.inputCell w) M.inputPredicate σ w
      (fun f a x hx => M.inputPredicate_correct f a σ w x hx) s a i x ha
  | test f => exact BoxTableau.Formula.test_correct (d:=d) (q:=q) M.letterAccepting f N a i σ w x hN ha

 theorem coord_correct (N : Expr J) (σ : J → ℕ) (w : List Bool) (hN : N.eval σ w=w.length)
    (e : Edge M d q) (i : Fin (d+q+1)) (a : Expr J) (x : Fin w.length)
    (hx : x∈(instanceData M d q w).domain e i) (ha : a.eval σ w=x.val) :
    (coord M d q N e i a).eval σ w=((instanceData M d q w).coord e i ⟨x,hx⟩).val := by
  cases e with
  | first | second | seed | test => exact ha
  | third e => exact BoxTableau.Formula.labelCoord_correct e N a i σ w x hN ha

 theorem fixedLegal_iff (K : ℕ) (ε : F₂) (w : List Bool) (t : BlockTag M d q K)
    (v : Values M d q K) :
    (instanceData M d q []).FixedLegal K ε t v ↔ (instanceData M d q w).FixedLegal K ε t v := by
  unfold ConsistencyData.FixedLegal ConsistencyData.fixedForm ConsistencyData.fixedBias
  rcases t with ⟨i,t|⟨e,j⟩⟩
  · rfl
  · cases e <;> rfl

 theorem validity_correct (N : Expr J) (K : ℕ) (ε : F₂) (σ : J → ℕ) (w : List Bool)
    (hN : N.eval σ w=w.length) (t : BlockTag M d q K) (v : Values M d q K)
    (a b : Expr J) (x y : Fin w.length) (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) :
    (validity M d q N K ε t v a b).Holds σ w ↔
      (instanceData M d q w).DescriptorValid K ε (ConsistencyData.makeBlock K t x y,v) := by
  erw [(instanceData M d q w).descriptorValid_fixed]
  simp only [validity,ConsistencyData.validPredicate,Predicate.Holds,decide_eq_true_eq,
    fixedLegal_iff M d q K ε w t v]
  exact and_congr ((instanceData M d q w).blockPredicate_holds (domain M d q N) K σ w
    (domain_correct M d q N σ w hN) t a b x y ha hb) Iff.rfl

 theorem adjacent_correct (N : Expr J) (K : ℕ) (σ : J → ℕ) (w : List Bool)
    (hN : N.eval σ w=w.length) (t u : BlockTag M d q K) (v z : Values M d q K)
    (a b c e : Expr J) (x y p s : Fin w.length)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) (hc : c.eval σ w=p.val) (he : e.eval σ w=s.val)
    (ht : (instanceData M d q w).ValidBlock K (ConsistencyData.makeBlock K t x y))
    (hu : (instanceData M d q w).ValidBlock K (ConsistencyData.makeBlock K u p s)) :
    (adjacent M d q N K t u v z a b c e).Holds σ w ↔
      (instanceData M d q w).RawAdjacent K (ConsistencyData.makeBlock K t x y,v)
        (ConsistencyData.makeBlock K u p s,z) := by
  change ((instanceData M d q w).adjacencyPredicate (coord M d q N) K t u v z a b c e).Holds σ w ↔ _
  exact (instanceData M d q w).adjacencyPredicate_correct (coord M d q N) K σ w
    (coord_correct M d q N σ w hN) t u v z a b c e x y p s ha hb hc he ht hu
end WLTime.OneTape.Symbolic

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression
variable (M : OneTape) (d q : ℕ) {J : Type uJ}

 theorem domain_bounded (N : Expr J) (e : Edge M d q) (i : Fin (d+q+1)) (a : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hN : N.Bounded σ w B) (ha : a.Bounded σ w B) :
    (domain M d q N e i a).Bounded σ w (6*B) := by
  cases e with
  | first e | second e | third e => exact BoxTableau.Formula.labelDomain_bounded e N a i σ w B hB hN ha
  | seed s =>
    exact (BoxTableau.Formula.seed _ s a i).bounded_mono σ w
      (BoxTableau.Formula.seed_bounded M.inputPredicate s a i σ w B ha (fun f => M.inputPredicate_bounded f a σ w B ha))
      (by omega)
  | test f =>
    exact (BoxTableau.Formula.test (d:=d) (q:=q) N a i).bounded_mono σ w
      (BoxTableau.Formula.test_bounded (d:=d) (q:=q) N a i σ w B hB hN ha) (by omega : 2*B≤6*B)

 theorem coord_bounded (N : Expr J) (e : Edge M d q) (i : Fin (d+q+1)) (a : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hN : N.Bounded σ w B) (ha : a.Bounded σ w B) :
    (coord M d q N e i a).Bounded σ w (6*B) := by
  cases e with
  | third e => exact BoxTableau.Formula.labelCoord_bounded e N a i σ w B hB hN ha
  | first | second | seed | test => exact a.bounded_mono σ w ha (by omega)

 theorem validity_bounded (N : Expr J) (K : ℕ) (ε : F₂) (t : BlockTag M d q K) (v : Values M d q K)
    (a b : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hN : N.Bounded σ w B) (ha : a.Bounded σ w B) (hb : b.Bounded σ w B) :
    (validity M d q N K ε t v a b).Bounded σ w (6*B) :=
  (instanceData M d q []).validPredicate_bounded _ K ε σ w (6*B) t v a b
    (fun e i => ⟨domain_bounded M d q N e i a σ w B hB hN ha,
      domain_bounded M d q N e i b σ w B hB hN hb⟩)

 theorem adjacent_bounded (N : Expr J) (K : ℕ) (t u : BlockTag M d q K) (v z : Values M d q K)
    (a b c e : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hN : N.Bounded σ w B) (ha : a.Bounded σ w B) (hb : b.Bounded σ w B)
    (hc : c.Bounded σ w B) (he : e.Bounded σ w B) :
    (adjacent M d q N K t u v z a b c e).Bounded σ w (6*B) :=
  (instanceData M d q []).adjacencyPredicate_bounded _ K σ w (6*B) t u v z a b c e
    (a.bounded_mono σ w ha (by omega)) (b.bounded_mono σ w hb (by omega))
    (c.bounded_mono σ w hc (by omega)) (e.bounded_mono σ w he (by omega))
    (fun f i => ⟨coord_bounded M d q N f i a σ w B hB hN ha,
      coord_bounded M d q N f i b σ w B hB hN hb,
      coord_bounded M d q N f i c σ w B hB hN hc,
      coord_bounded M d q N f i e σ w B hB hN he⟩)
end WLTime.OneTape.Symbolic

namespace WLTime.Compression.ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

variable [Fintype P] [Fintype E]
open scoped Classical

 theorem mixedCode_le (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Fin m) :
    mixedCode (m:=m) K t a b≤Fintype.card (BlockTag (r:=r) (P:=P) (E:=E) K)*m^2 := by
  have ht := (finProdFinEquiv (finProdFinEquiv (Fintype.equivFin _ t,a),b)).isLt
  change b.val+m*(a.val+m*(Fintype.equivFin _ t).val) < _ at ht
  unfold mixedCode
  nlinarith

 theorem rawCode_make (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Fin m) :
    rawCode K (makeBlock K t a b)=mixedCode K t a b := by rcases t with ⟨i,t|l⟩ <;> rfl

 theorem tagValues_card_pos (K : ℕ) : 0<Fintype.card (I.TagValues K) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨fun _ => 0⟩

end WLTime.Compression.ConsistencyData

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Writer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uV uJ uK uL uT

namespace WLTime.Marking
variable {D : Type uD} {V : Type uV} {p : D → Prop} {count : V → ℕ}

 theorem decodeSlots_adj (e : {d // p d} ≃ V) (G : SimpleGraph V)
    (R : D → D → Prop) (c : D → ℕ)
    (hc : ∀d : {d // p d},count (e d)=c d.val)
    (hR : ∀d f : {d // p d},G.Adj (e d) (e f) ↔ R d.val f.val)
    (L q : ℕ) (d f : D) (i j : Fin L) :
    (rawGraph G (decodeSlots (count:=count) e L q)).Adj (some (.inl (d,i))) (some (.inl (f,j))) ↔
      rectangleAdj (p:=p) R c d f i.val j.val := by
  classical
  by_cases hd : p d
  · by_cases hf : p f
    · have heq : e ⟨d,hd⟩=e ⟨f,hf⟩ ↔ d=f := by
        rw [e.injective.eq_iff,Subtype.mk.injEq]
      have hadj := hR ⟨d,hd⟩ ⟨f,hf⟩
      have hcd := hc ⟨d,hd⟩
      have hcf := hc ⟨f,hf⟩
      by_cases hi : i.val=0 <;> by_cases hj : j.val=0
      · simpa [rawGraph,rawAdj,decodeSlots,hd,hf,hi,hj,slotAdj,rectangleAdj] using hadj
      · by_cases hle : j.val-1<c f
        · have h : j.val≤c f := by omega
          simp [rawGraph,rawAdj,decodeSlots,hd,hf,hi,hj,hcf,hle,slotAdj,rectangleAdj,h,heq]
        · have h : ¬j.val≤c f := by omega
          simp [rawGraph,rawAdj,decodeSlots,hd,hf,hi,hj,hcf,hle,rectangleAdj,h]
      · by_cases hle : i.val-1<c d
        · have h : i.val≤c d := by omega
          simp [rawGraph,rawAdj,decodeSlots,hd,hf,hi,hj,hcd,hle,slotAdj,rectangleAdj,h,heq]
        · have h : ¬i.val≤c d := by omega
          simp [rawGraph,rawAdj,decodeSlots,hd,hf,hi,hj,hcd,hle,rectangleAdj,h]
      · by_cases hli : i.val-1<c d <;> by_cases hlj : j.val-1<c f <;>
          simp [rawGraph,rawAdj,decodeSlots,hd,hf,hi,hj,hcd,hcf,hli,hlj,rectangleAdj,slotAdj]
    · simp [rawGraph,rawAdj,decodeSlots,hd,hf,rectangleAdj]
  · simp [rawGraph,rawAdj,decodeSlots,hd,rectangleAdj]
end WLTime.Marking

namespace WLTime.NatCode
namespace Predicate
variable {J : Type uJ}
 theorem rectangular_holds (p q R same : Predicate J) (a b i j : Expr J)
    (σ : J → ℕ) (w : List Bool) :
    (rectangular p q R same a b i j).Holds σ w ↔
      p.Holds σ w ∧ q.Holds σ w ∧ i.eval σ w≤a.eval σ w ∧ j.eval σ w≤b.eval σ w ∧
        ((i.eval σ w=0 ∧ j.eval σ w=0 ∧ R.Holds σ w) ∨
          (i.eval σ w=0 ∧ j.eval σ w≠0 ∧ same.Holds σ w) ∨
          (i.eval σ w≠0 ∧ j.eval σ w=0 ∧ same.Holds σ w)) := by
  simp only [rectangular,Holds,disj,Expr.eval,le,not_and_or,not_not,Nat.not_lt]
  tauto
end Predicate
end WLTime.NatCode

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression
variable (M : OneTape) (d q K : ℕ)
open scoped Classical

variable {J : Type uJ}

 theorem countExpr_correct (N : Expr J) (σ : J → ℕ) (w : List Bool)
    (hN : N.eval σ w=w.length) (t : BlockTag M d q K) (a b : Expr J)
    (x y : Fin w.length) (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) :
    (countExpr M d q K N t a b).eval σ w=
      ConsistencyData.mixedCode K t x y*((instanceData M d q w).rectCoefficient K*w.length^2+1) := by
  simp only [countExpr,Expr.mul_eval,Expr.add_eval,Expr.eval,hN,ha,hb,
    ConsistencyData.mixedCode,coefficient,pow_two]
  rfl

 theorem sameRect_correct (t u : BlockTag M d q K) (v z : Values M d q K)
    (a b c e : Expr J) (σ : J → ℕ) (w : List Bool) (x y l h : Fin w.length)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val)
    (hc : c.eval σ w=l.val) (he : e.eval σ w=h.val) :
    (sameRect M d q K t u v z a b c e).Holds σ w ↔
      (t,v,x,y)=(u,z,l,h) := by
  simp only [sameRect,Predicate.Holds,decide_eq_true_eq,ha,hb,hc,he,Fin.val_inj,Prod.mk.injEq]
  tauto

 theorem slotPredicate_correct (N : Expr J) (hK : 0<K) (hr : 1≤d+q)
    (ε : F₂) (σ : J → ℕ) (w : List Bool) (hN : N.eval σ w=w.length)
    (t u : BlockTag M d q K) (v z : Values M d q K) (a b i c e j : Expr J)
    (x y l h : Fin w.length) (s t' : Fin ((instanceData M d q w).slotLimit K)) (pad : ℕ)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) (hi : i.eval σ w=s.val)
    (hc : c.eval σ w=l.val) (he : e.eval σ w=h.val) (hj : j.eval σ w=t'.val) :
    (slotPredicate M d q K N ε t u v z a b i c e j).Holds σ w ↔
      ((instanceData M d q w).rectangularGraph K hK hr ε pad).Adj
        (some (.inl ((t,v,x,y),s))) (some (.inl ((u,z,l,h),t'))) := by
  let I := instanceData M d q w
  have hn (f : {f : I.Rect K // I.RectValid K ε f}) :
      I.spacedCount K (I.rectVertexEquiv K hK hr ε f).1=
        ConsistencyData.mixedCode K f.val.1 f.val.2.2.1 f.val.2.2.2*(I.rectCoefficient K*w.length^2+1) := by
    change ConsistencyData.rawCode K (ConsistencyData.makeBlock K f.val.1 f.val.2.2.1 f.val.2.2.2)*_= _
    rw [ConsistencyData.rawCode_make]
  have hR (f g : {f : I.Rect K // I.RectValid K ε f}) :
      (I.valuationGraph K ε).Adj (I.rectVertexEquiv K hK hr ε f) (I.rectVertexEquiv K hK hr ε g) ↔
        I.RawAdjacent K (I.rectEquiv K f.val) (I.rectEquiv K g.val) :=
    I.descriptor_adjacent K hK hr ε _ _
  unfold ConsistencyData.rectangularGraph ConsistencyData.slots
  erw [Marking.decodeSlots_adj (I.rectVertexEquiv K hK hr ε) (I.valuationGraph K ε)
    (fun f g => I.RawAdjacent K (I.rectEquiv K f) (I.rectEquiv K g))
    (fun f => ConsistencyData.mixedCode K f.1 f.2.2.1 f.2.2.2*(I.rectCoefficient K*w.length^2+1))
    hn hR]
  simp only [slotPredicate,Predicate.rectangular_holds,Marking.rectangleAdj,
    validity_correct M d q N K ε σ w hN _ _ _ _ _ _ ha hb,
    validity_correct M d q N K ε σ w hN _ _ _ _ _ _ hc he,
    sameRect_correct M d q K _ _ _ _ _ _ _ _ σ w _ _ _ _ ha hb hc he,
    countExpr_correct M d q K N σ w hN _ _ _ _ _ ha hb,
    countExpr_correct M d q K N σ w hN _ _ _ _ _ hc he,hi,hj]
  dsimp only [ConsistencyData.RectValid,ConsistencyData.rectEquiv,I]
  apply and_congr_right
  intro ht
  apply and_congr_right
  intro hu
  rw [adjacent_correct M d q N K σ w hN t u v z a b c e x y l h ha hb hc he ht.1 hu.1]
  rfl
end WLTime.OneTape.Symbolic

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} [DecidableEq K]
 theorem countdown_indexed (c : Code K Bool) (s : ℕ → Stacks K Bool) (B n i : ℕ)
    (hc : ∀j<n,∃t≤B,c.Exec (s (i+j)) t (s (i+j+1))) :
    ∃t≤n*(B+3)+1,
      (Code.loop (Code.nonempty (.inl 0)) (.seq (c.relabel Sum.inr) (.pop (.inl 0))) :
        Code (Fin 2 ⊕ K) Bool).Exec (Sum.elim (extra n) (s i)) t (Sum.elim (extra 0) (s (i+n))) := by
  induction n generalizing i with
  | zero => exact ⟨1,by omega,.loop_false (by simp [Code.nonempty,tops,extra,numeral])⟩
  | succ n ih =>
    obtain ⟨u,hu,he⟩ := hc 0 (by omega)
    simp only [Nat.add_zero] at he
    have hb := Code.Exec.seq (Code.relabel_inr_exec he (extra (n+1))) (Code.Exec.pop _ (.inl 0))
    rw [extra_succ_update] at hb
    obtain ⟨v,hv,hr⟩ := ih (i+1) (fun j hj => by simpa only [Nat.add_assoc,Nat.add_comm 1] using hc (j+1) (by omega))
    have hh := Code.Exec.loop_true (p:=Code.nonempty (.inl 0))
      (by simp [Code.nonempty,tops,extra,numeral]) hb hr
    refine ⟨u+2+v+1,by nlinarith,?_⟩
    convert hh using 1
    congr 2
    omega

 theorem repeat_indexed (base : K) (c : Code K Bool) (s : ℕ → Stacks K Bool) (B n : ℕ)
    (hc : ∀j<n,∃t≤B,c.Exec (s j) t (s (j+1))) (hb : s 0 base=numeral n) :
    ∃t≤n*(B+15)+3,(repeatN base c).Exec (Sum.elim (extra 0) (s 0)) t (Sum.elim (extra 0) (s n)) := by
  have hf := Code.copy_exec (.inr base : Fin 2 ⊕ K) (.inl 0) (.inl 1)
    (by simp) (by simp) (by simp) false (Sum.elim (extra 0) (s 0)) (by simp [extra])
  have he : Function.update (Sum.elim (extra 0) (s 0)) (.inl 0)
      (Sum.elim (extra 0) (s 0) (.inr base)++Sum.elim (extra 0) (s 0) (.inl 0))=Sum.elim (extra n) (s 0) := by
    funext i; cases i with
    | inl j => fin_cases j <;> simp [extra,numeral,hb]
    | inr j => simp
  rw [he] at hf
  obtain ⟨t,ht,hr⟩ := countdown_indexed c s B n 0 (by simpa only [Nat.zero_add])
  simp only [Nat.zero_add] at hr
  refine ⟨_,?_,Code.Exec.seq hf hr⟩
  simp only [Sum.elim_inr,hb,numeral_length]
  nlinarith
end WLTime.UnaryPrograms

namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]
 theorem repeat_indexed (base : K) (p : Program K) (s : ℕ → Stacks K Bool) (B n : ℕ)
    (hc : ∀j<n,∃t≤B,p.Exec (s j) t (s (j+1))) (hb : s 0 base=UnaryPrograms.numeral n) :
    ∃t≤n*(B+15)+3,(repeatN base p).Exec (s 0) t (s n) := by
  obtain ⟨t,ht,he⟩ := UnaryPrograms.repeat_indexed (.inr base : Fin p.scratch ⊕ K) p.code
    (fun i => p.ambient (s i)) B n hc hb
  refine ⟨t,ht,?_⟩
  apply Code.relabel_exec_of_maps _ (Equiv.injective _) he
  · intro k; cases k with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl
  · intro k; cases k with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl
  · intro l hl; exact False.elim (hl ((merge 2 p.scratch).symm l) (Equiv.apply_symm_apply _ l))
end WLTime.TypedStack.Program

namespace WLTime.NatCode
open TypedStack UnaryPrograms
universe u

namespace Writer
variable {K : Type u}

 theorem numeral_bool_head (p : Prop) [Decidable p] :
    ((numeral (if p then 1 else 0)).head?==some true)=decide p := by by_cases hp:p <;> simp [hp,numeral]

 theorem emit_exec {L : Type uL} [DecidableEq L] (p : Predicate K) (ρ : K → L) (word out : L)
    (_how : out≠word) (_hor : ∀k,out≠ρ k) (σ : K → ℕ) (w : List Bool) (B : ℕ)
    (hp : p.Bounded σ w B) (hwB : w.length≤B) (s : Stacks L Bool)
    (hs : ∀k,s (ρ k)=numeral (σ k)) (hw : s word=w) :
    ∃t≤(4*p.code.charge+20)*(B+1)^2,
      ((Writer.emit p).compile ρ word out).Exec s t
        (Function.update s out (decide (p.Holds σ w)::s out)) := by
  let z : Stacks (Fin 1 ⊕ L) Bool := Sum.elim (fun _ => []) s
  obtain ⟨t,ht,he⟩ := p.code.compile_exec (Sum.inr ∘ ρ) (.inr word) (.inl (0 : Fin 1))
    (by simp) (fun _ => by simp) σ w (2*B+1) (p.code_bounded σ w B hp) (by omega) z
    (fun k => hs k) hw (by simp [z])
  let mid := Function.update z (.inl (0 : Fin 1)) (numeral (p.code.eval σ w))
  have hb := Program.ofCode_exec (Code.Exec.pushDyn mid (.inr out) (fun v => v (.inl 0)==some true))
  have hc := Program.clear_exec (.inl (0 : Fin 1))
    (Function.update mid (.inr out) ((tops mid (.inl 0)==some true)::mid (.inr out)))
  have hh := Program.seq_exec he (Program.seq_exec hb hc)
  have hout : Function.update
      (Function.update mid (.inr out) ((tops mid (.inl 0)==some true)::mid (.inr out))) (.inl 0) []=
      Sum.elim (fun _ : Fin 1 => []) (Function.update s out (decide (p.Holds σ w)::s out)) := by
    funext j; cases j with
    | inl i => have hi:i=0 := Subsingleton.elim _ _; subst i; simp
    | inr j => simp only [mid,z,tops,p.code_eval,numeral_bool_head,
        Function.update_of_ne Sum.inr_ne_inl,Function.update_apply,Sum.inr.injEq,
        Sum.elim_inr,ite_true]
  rw [hout] at hh
  refine ⟨_,?_,Program.local_exec hh⟩
  simp only [mid,Function.update_of_ne Sum.inl_ne_inr,Function.update_self,numeral_length]
  have hv := p.code_le_one σ w
  nlinarith [Nat.zero_le (B*B)]

 theorem compile_exec (p : Writer K) {L : Type uL} [DecidableEq L] (ρ : K → L) (word out : L)
    (how : out≠word) (hor : ∀k,out≠ρ k) (σ : K → ℕ) (w : List Bool) (B : ℕ)
    (hp : p.Safe σ w B) (hwB : w.length≤B) (s : Stacks L Bool)
    (hs : ∀k,s (ρ k)=numeral (σ k)) (hw : s word=w) :
    ∃t≤p.charge*(B+1)^(p.depth+2),(p.compile ρ word out).Exec s t
      (Function.update s out ((p.eval σ w).reverse++s out)) := by
  induction p generalizing L with
  | emit p => simpa only [compile,depth,charge,eval,List.reverse_singleton,List.singleton_append] using
      emit_exec p ρ word out how hor σ w B hp hwB s hs hw
  | seq a b iha ihb =>
    obtain ⟨t,ht,h1⟩ := iha ρ word out how hor σ hp.1 s hs hw
    obtain ⟨v,hv,h2⟩ := ihb ρ word out how hor σ hp.2
      (Function.update s out ((a.eval σ w).reverse++s out))
      (fun k => by simpa only [Function.update_of_ne (hor k).symm] using hs k)
      (by simpa only [Function.update_of_ne how.symm] using hw)
    have hh := Program.seq_exec h1 h2
    refine ⟨t+v,?_,?_⟩
    · have hpa := Nat.pow_le_pow_right (by omega : 1≤B+1) (Nat.add_le_add_right (Nat.le_max_left a.depth b.depth) 2)
      have hpb := Nat.pow_le_pow_right (by omega : 1≤B+1) (Nat.add_le_add_right (Nat.le_max_right a.depth b.depth) 2)
      calc
        t+v ≤ a.charge*(B+1)^(a.depth+2)+b.charge*(B+1)^(b.depth+2) := Nat.add_le_add ht hv
        _ ≤ (a.charge+b.charge)*(B+1)^(max a.depth b.depth+2) := by nlinarith
    · simpa only [compile,eval,List.reverse_append,List.append_assoc,Function.update_self,Function.update_idem] using hh
  | loop n body ih =>
    let z : Stacks (Fin 2 ⊕ L) Bool := Sum.elim (fun _ => []) s
    let N := n.eval σ w
    let words (i : ℕ) := (List.range i).flatMap (fun j => body.eval (Option.elim' j σ) w)
    let st (i : ℕ) : Stacks (Fin 2 ⊕ L) Bool :=
      Function.update (Function.update (Function.update z (.inl 1) (numeral N)) (.inl 0) (numeral i))
        (.inr out) ((words i).reverse++s out)
    have hn := n.eval_le σ w B hp.1
    obtain ⟨t,ht,h0⟩ := n.compile_exec (Sum.inr ∘ ρ) (.inr word) (.inl (1 : Fin 2))
      (by simp) (fun _ => by simp) σ w B hp.1 hwB z (fun k => hs k) hw (by simp [z])
    have hs0 : st 0=Function.update z (.inl 1) (numeral N) := by
      funext j; cases j with
      | inl j =>
        by_cases hj : j=0
        · subst j
          simp only [st,Function.update_of_ne Sum.inl_ne_inr,Function.update_self,numeral,
            List.replicate_zero,Function.update_of_ne (by simp : (Sum.inl (0 : Fin 2) : Fin 2 ⊕ L)≠.inl 1),
            z,Sum.elim_inl]
        · have hj' : j=1 := by omega
          subst j
          simp only [st,Function.update_of_ne Sum.inl_ne_inr,
            Function.update_of_ne (by simp : (Sum.inl (1 : Fin 2) : Fin 2 ⊕ L)≠.inl 0),Function.update_self]
      | inr j =>
        simp only [st,z,words,List.range_zero,List.flatMap_nil,List.reverse_nil,
          List.nil_append,Function.update_of_ne Sum.inr_ne_inl,Function.update_apply,
          Sum.inr.injEq,Sum.elim_inr]
        split_ifs with h
        · subst j; rfl
        · rfl
    rw [← hs0] at h0
    let step := Program.seq
      (body.compile (Option.elim' (.inl (0 : Fin 2)) (Sum.inr ∘ ρ)) (.inr word) (.inr out))
      (Program.push (.inl 0) true)
    have hρ (k) : (Sum.inr (ρ k) : Fin 2 ⊕ L)≠.inr out := by
      intro h; exact hor k (Sum.inr.inj h).symm
    have hword : (Sum.inr word : Fin 2 ⊕ L)≠.inr out := by
      intro h; exact how (Sum.inr.inj h).symm
    have steps : ∀j<N,∃v≤body.charge*(B+1)^(body.depth+2)+2,step.Exec (st j) v (st (j+1)) := by
      intro j hj
      obtain ⟨v,hv,he⟩ := ih (Option.elim' (.inl (0 : Fin 2)) (Sum.inr ∘ ρ)) (.inr word) (.inr out)
        (by simpa using how) (fun k => by cases k <;> simp [hor]) (Option.elim' j σ) (hp.2 j hj) (st j)
        (fun k => by cases k with
          | none => simp only [Option.elim',st,Function.update_of_ne Sum.inl_ne_inr,Function.update_self]
          | some k => simpa only [Option.elim',st,Function.comp_apply,Function.update_of_ne (hρ k),
              Function.update_of_ne Sum.inr_ne_inl,z,Sum.elim_inr] using hs k)
        (by simpa only [st,Function.update_of_ne hword,Function.update_of_ne Sum.inr_ne_inl,z,Sum.elim_inr] using hw)
      have hi := Program.push_exec (.inl (0 : Fin 2)) true
        (Function.update (st j) (.inr out) ((body.eval (Option.elim' j σ) w).reverse++st j (.inr out)))
      have hh := Program.seq_exec he hi
      refine ⟨v+2,by omega,?_⟩
      convert hh using 1
      funext k; cases k with
      | inl k => fin_cases k <;> simp [st,numeral,List.replicate_succ]
      | inr k => simp [st,words,List.range_succ,List.flatMap_append,List.reverse_append,List.append_assoc]
    obtain ⟨v,hv,h1⟩ := Program.repeat_indexed (.inl (1 : Fin 2)) step st
      (body.charge*(B+1)^(body.depth+2)+2) N steps (by simp [st])
    have h2 := Program.clear_exec (.inl (0 : Fin 2)) (st N)
    have h3 := Program.clear_exec (.inl (1 : Fin 2)) (Function.update (st N) (.inl 0) [])
    have hh := Program.seq_exec h0 (Program.seq_exec h1 (Program.seq_exec h2 h3))
    have hout : Function.update (Function.update (st N) (.inl 0) []) (.inl 1) []=
        Sum.elim (fun _ : Fin 2 => []) (Function.update s out (((Writer.loop n body).eval σ w).reverse++s out)) := by
      funext j; cases j with
      | inl j => fin_cases j <;> simp
      | inr j => simp only [st,z,eval,words,N,Function.update_of_ne Sum.inr_ne_inl,
          Function.update_apply,Sum.inr.injEq,Sum.elim_inr]
    rw [hout] at hh
    refine ⟨_,?_,Program.local_exec hh⟩
    simp only [st,Function.update_of_ne Sum.inl_ne_inr,Function.update_self,numeral_length,
      Function.update_of_ne (by simp : (Sum.inl (1 : Fin 2) : Fin 2 ⊕ L)≠.inl 0)]
    change t+(v+(3*N+1+(3*N+1)))≤(n.charge+body.charge+100)*(B+1)^(body.depth+1+2)
    have hexp : body.depth+1+2=(body.depth+2)+1 := by omega
    rw [hexp,pow_succ]
    have hpow : (B+1)^2≤(B+1)^(body.depth+2) := Nat.pow_le_pow_right (by omega) (by omega)
    have hone : 1≤(B+1)^(body.depth+2) := Nat.one_le_pow _ _ (by omega)
    dsimp [N] at hv ⊢
    nlinarith [Nat.mul_le_mul_left n.charge hpow,
      Nat.mul_le_mul_right (body.charge*(B+1)^(body.depth+2)+17) hn,
      Nat.mul_le_mul_left B hone]
end Writer
end WLTime.NatCode

namespace WLTime.NatCode
namespace Expr
variable {K : Type uK} {J : Type uJ}
 theorem rename_bounded (f : K → J) (e : Expr K) (σ : J → ℕ) (w : List Bool) (B : ℕ) :
    (e.rename f).Bounded σ w B ↔ e.Bounded (σ ∘ f) w B := by
  induction e with
  | const | var => rfl
  | binary op a b ha hb =>
    change ((a.rename f).Bounded σ w B ∧ (b.rename f).Bounded σ w B ∧
      op.eval ((a.rename f).eval σ w) ((b.rename f).eval σ w)≤B) ↔ _
    rw [ha,hb,rename_eval,rename_eval]
    rfl
  | bit a ha =>
    exact and_congr ha Iff.rfl

end Expr
namespace Writer
variable {K : Type uK}
 theorem empty_safe (σ : K → ℕ) (w : List Bool) (B : ℕ) : (empty : Writer K).Safe σ w B := by
  exact ⟨Nat.zero_le _,fun i hi => (Nat.not_lt_zero i hi).elim⟩
 theorem each_safe {T : Type uT} (l : List T) (f : T → Writer K) (σ : K → ℕ) (w : List Bool) (B : ℕ)
    (h : ∀t∈l,(f t).Safe σ w B) : (each l f).Safe σ w B := by
  induction l with
  | nil => exact empty_safe σ w B
  | cons t l ih => exact ⟨h t (by simp),ih (fun t ht => h t (by simp [ht]))⟩
 theorem each_depth_le {T : Type uT} (l : List T) (f : T → Writer K) (b : ℕ) (hb : 1≤b)
    (h : ∀t∈l,(f t).depth≤b) : (each l f).depth≤b := by
  induction l with
  | nil => exact hb
  | cons t l ih => exact max_le (h t (by simp)) (ih (fun t ht => h t (by simp [ht])))

 theorem grid_eval (N L : Expr K) (body : Writer (Option (Option (Option K))))
    (σ : K → ℕ) (w : List Bool) :
    (grid N L body).eval σ w=(List.range (N.eval σ w)).flatMap (fun a =>
      (List.range (N.eval σ w)).flatMap (fun b =>
        (List.range (L.eval σ w)).flatMap (fun i => body.eval
          (Option.elim' i (Option.elim' b (Option.elim' a σ))) w))) := by
  simp only [grid,eval,Expr.rename_eval,Function.comp_def,Option.elim'_some]
 theorem grid_safe (N L : Expr K) (body : Writer (Option (Option (Option K))))
    (σ : K → ℕ) (w : List Bool) (B : ℕ) (hN : N.Bounded σ w B) (hL : L.Bounded σ w B)
    (hb : ∀a<N.eval σ w,∀b<N.eval σ w,∀i<L.eval σ w,
      body.Safe (Option.elim' i (Option.elim' b (Option.elim' a σ))) w B) :
    (grid N L body).Safe σ w B := by
  refine ⟨hN,fun a ha => ⟨?_,fun b hb' => ⟨?_,fun i hi => ?_⟩⟩⟩
  · simpa only [Expr.rename_bounded,Function.comp_def,Option.elim'_some] using hN
  · simpa only [Expr.rename_bounded,Function.comp_def,Option.elim'_some] using hL
  · simp only [Expr.rename_eval,Function.comp_def,Option.elim'_some] at hb' hi
    exact hb a ha b hb' i hi
end Writer
end WLTime.NatCode

end OAI
end

section
-- module Solutions.OAIQW_WLTime.MatrixWriter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uW uT uS uJ uR uJ'

namespace WLTime.Enumeration
variable {V : Type uV} {W : Type uW}

 theorem fin_values (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj; simp

 theorem range_flatMap {T : Type uT} (n : ℕ) (f : ℕ → List T) :
    (List.range n).flatMap f=(List.finRange n).flatMap (fun i => f i.val) := by
  rw [← fin_values,List.flatMap_map]

 theorem Listing.length_eq_card [Fintype V] (l : Listing V) : l.items.length=Fintype.card V := by
  rw [← Fintype.card_fin l.items.length]
  exact Fintype.card_congr l.equiv
end WLTime.Enumeration

namespace WLTime.Enumeration
open NatCode
variable {T : Type uT} {S : Type uS} {J : Type uJ}

 theorem rectangle_flatMap {R : Type uR} (t : Listing T) (s : Listing S) (m L p : ℕ)
    (f : Vertex T S m L p → List R) :
    (rectangle t s m L p).items.flatMap f=f none ++
      t.items.flatMap (fun t => s.items.flatMap (fun s => (List.finRange m).flatMap (fun a =>
        (List.finRange m).flatMap (fun b => (List.finRange L).flatMap (fun i => f (some (.inl ((t,s,a,b),i)))))))) ++
      (List.finRange p).flatMap (fun i => f (some (.inr i))) := by
  simp only [rectangle,Listing.option,Listing.sum,Listing.prod,fin,List.flatMap_cons,
    List.flatMap_append,List.flatMap_map,List.flatMap_assoc,List.append_assoc]

 theorem writer_eval (t : Listing T) (s : Listing S) (N L P : Expr J)
    (hub : Writer J) (slot : T → S → Writer (Option (Option (Option J)))) (pad : Writer (Option J))
    (σ : J → ℕ) (w : List Bool) (m a p : ℕ)
    (hN : N.eval σ w=m) (hL : L.eval σ w=a) (hP : P.eval σ w=p)
    (f : Vertex T S m a p → List Bool)
    (hh : hub.eval σ w=f none)
    (hs : ∀t s (x y : Fin m) (i : Fin a),
      (slot t s).eval (Option.elim' i.val (Option.elim' y.val (Option.elim' x.val σ))) w=
        f (some (.inl ((t,s,x,y),i))))
    (hp : ∀i : Fin p,pad.eval (Option.elim' i.val σ) w=f (some (.inr i))) :
    (writer t s N L P hub slot pad).eval σ w=(rectangle t s m a p).items.flatMap f := by
  rw [rectangle_flatMap]
  simp only [writer,Writer.eval,Writer.each_eval,Writer.grid_eval,hN,hL,hP,hh,
    ← List.append_assoc,range_flatMap]
  simp only [hs,hp]

 theorem writer_safe (t : Listing T) (s : Listing S) (N L P : Expr J)
    (hub : Writer J) (slot : T → S → Writer (Option (Option (Option J)))) (pad : Writer (Option J))
    (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (hN : N.Bounded σ w B) (hL : L.Bounded σ w B) (hP : P.Bounded σ w B)
    (hh : hub.Safe σ w B)
    (hs : ∀t s x,x < N.eval σ w → ∀y,y<N.eval σ w → ∀i,i<L.eval σ w →
      (slot t s).Safe (Option.elim' i (Option.elim' y (Option.elim' x σ))) w B)
    (hp : ∀i<P.eval σ w,pad.Safe (Option.elim' i σ) w B) :
    (writer t s N L P hub slot pad).Safe σ w B := by
  refine ⟨hh,⟨Writer.each_safe _ _ σ w B ?_,⟨hP,hp⟩⟩⟩
  intro tag htag
  apply Writer.each_safe
  intro value hvalue
  exact Writer.grid_safe N L (slot tag value) σ w B hN hL (hs tag value)

 theorem writer_depth (t : Listing T) (s : Listing S) (N L P : Expr J)
    (hub : Writer J) (slot : T → S → Writer (Option (Option (Option J)))) (pad : Writer (Option J))
    (b : ℕ) (hh : hub.depth≤b+3) (hs : ∀t s,(slot t s).depth≤b) (hp : pad.depth≤b+2) :
    (writer t s N L P hub slot pad).depth≤b+3 := by
  apply max_le hh
  apply max_le
  · apply Writer.each_depth_le _ _ _ (by omega)
    intro tag htag
    apply Writer.each_depth_le _ _ _ (by omega)
    intro value hvalue
    rw [Writer.grid_depth]
    exact Nat.add_le_add_right (hs tag value) 3
  · exact Nat.add_le_add_right hp 1
end WLTime.Enumeration

namespace WLTime.Enumeration
variable {V : Type uV}
open scoped Classical

 theorem Listing.ofFn_eq_map {R : Type uR} (l : Listing V) (f : V → R) :
    List.ofFn (fun i => f (l.items.get i))=l.items.map f := by
  change List.ofFn (f ∘ l.items.get)=_
  rw [←List.map_ofFn,List.ofFn_get]

 theorem Listing.matrix_bits (l : Listing V) (G : SimpleGraph V) :
    matrixBits (l.matrix G)=l.items.flatMap (fun x => l.items.map (fun y => decide (G.Adj x y))) := by
  classical
  have hx : matrixBits (l.matrix G)=
      (List.ofFn fun i => List.ofFn fun j => decide (G.Adj (l.items.get i) (l.items.get j))).flatten := by
    rfl
  rw [hx]
  have hr (v : V) := l.ofFn_eq_map (fun y => decide (G.Adj v y))
  have ho := l.ofFn_eq_map (fun x => l.items.map (fun y => decide (G.Adj x y)))
  calc
    _ = (List.ofFn fun i => l.items.map (fun y => decide (G.Adj (l.items.get i) y))).flatten := by
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext i
      exact hr _
    _ = (l.items.map (fun x => l.items.map (fun y => decide (G.Adj x y)))).flatten := congrArg List.flatten ho
    _ = _ := rfl
end WLTime.Enumeration

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression Enumeration
variable (M : OneTape) (d q K : ℕ)
open scoped Classical

variable {J : Type uJ}

 theorem Represents.rename {J' : Type uJ'} (f : J → J') (σ : J' → ℕ) (w : List Bool) (pad : ℕ)
    (x : Location M d q K J) (v : RawVertex M d q K w pad)
    (h : Represents M d q K (σ ∘ f) w pad x v) :
    Represents M d q K σ w pad (x.rename f) v := by
  cases h with
  | hub => exact .hub
  | hole i => exact .hole i
  | slot t v a b i x y s ha hb hi =>
    exact .slot t v _ _ _ x y s (by simpa only [Expr.rename_eval] using ha)
      (by simpa only [Expr.rename_eval] using hb) (by simpa only [Expr.rename_eval] using hi)

 theorem adjacency_correct (N : Expr J) (hK : 0<K) (hr : 1≤d+q) (ε : F₂)
    (σ : J → ℕ) (w : List Bool) (pad : ℕ) (hN : N.eval σ w=w.length)
    (x y : Location M d q K J) (v z : RawVertex M d q K w pad)
    (hx : Represents M d q K σ w pad x v) (hy : Represents M d q K σ w pad y z) :
    (adjacency M d q K N ε x y).Holds σ w ↔
      ((instanceData M d q w).rectangularGraph K hK hr ε pad).Adj v z := by
  cases hx <;> cases hy
  case slot.slot t v a b i x y s ha hb hi u z c e j l h t' hc he hj =>
    exact slotPredicate_correct M d q K N hK hr ε σ w hN t u v z a b i c e j x y l h s t' pad ha hb hi hc he hj
  all_goals simp [adjacency,Predicate.Holds,ConsistencyData.rectangularGraph,
    ConsistencyData.slots,Marking.rawGraph,Marking.rawAdj,Marking.decodeSlots]

 theorem columns_eval (N L P : Expr J) (hK : 0<K) (hr : 1≤d+q) (ε : F₂)
    (σ : J → ℕ) (w : List Bool) (pad : ℕ)
    (hN : N.eval σ w=w.length) (hL : L.eval σ w=(instanceData M d q w).slotLimit K)
    (hP : P.eval σ w=pad) (row : Location M d q K J) (x : RawVertex M d q K w pad)
    (hx : Represents M d q K σ w pad row x) :
    (columns M d q K N L P ε row).eval σ w=
      (listing M d q K w pad).items.map
        (fun y => decide (((instanceData M d q w).rectangularGraph K hK hr ε pad).Adj x y)) := by
  classical
  rw [show (listing M d q K w pad).items.map
      (fun y => decide (((instanceData M d q w).rectangularGraph K hK hr ε pad).Adj x y)) =
    (listing M d q K w pad).items.flatMap
      (fun y => [decide (((instanceData M d q w).rectangularGraph K hK hr ε pad).Adj x y)]) from
        List.map_eq_flatMap]
  apply Enumeration.writer_eval _ _ N L P _ _ _ σ w w.length _ pad hN hL hP
  · simp only [Writer.eval,List.singleton_inj]
    exact decide_eq_decide.mpr (adjacency_correct M d q K N hK hr ε σ w pad hN row .hub x none hx .hub)
  · intro t v a b i
    simp only [Writer.eval,List.singleton_inj]
    apply decide_eq_decide.mpr
    apply adjacency_correct M d q K _ hK hr ε _ w pad
    · simpa only [Expr.rename_eval,up3,Function.comp_def,Option.elim'_some] using hN
    · exact Represents.rename M d q K up3 _ w pad row x hx
    · exact .slot t v _ _ _ a b i rfl rfl rfl
  · intro i
    simp only [Writer.eval,List.singleton_inj]
    apply decide_eq_decide.mpr
    apply adjacency_correct M d q K _ hK hr ε _ w pad
    · simpa only [Expr.rename_eval,Function.comp_def,Option.elim'_some] using hN
    · exact Represents.rename M d q K some _ w pad row x hx
    · exact .hole i

 theorem matrixWriter_eval (N L P : Expr J) (hK : 0<K) (hr : 1≤d+q) (ε : F₂)
    (σ : J → ℕ) (w : List Bool) (pad : ℕ)
    (hN : N.eval σ w=w.length) (hL : L.eval σ w=(instanceData M d q w).slotLimit K)
    (hP : P.eval σ w=pad) :
    (matrixWriter M d q K N L P ε).eval σ w=
      (listing M d q K w pad).items.flatMap (fun x => (listing M d q K w pad).items.map
        (fun y => decide (((instanceData M d q w).rectangularGraph K hK hr ε pad).Adj x y))) := by
  apply Enumeration.writer_eval _ _ N L P _ _ _ σ w w.length _ pad hN hL hP
  · exact columns_eval M d q K N L P hK hr ε σ w pad hN hL hP .hub none .hub
  · intro t v a b i
    apply columns_eval M d q K _ _ _ hK hr ε _ w pad
    · simpa only [Expr.rename_eval,up3,Function.comp_def,Option.elim'_some] using hN
    · simpa only [Expr.rename_eval,up3,Function.comp_def,Option.elim'_some] using hL
    · simpa only [Expr.rename_eval,up3,Function.comp_def,Option.elim'_some] using hP
    · exact .slot t v _ _ _ a b i rfl rfl rfl
  · intro i
    apply columns_eval M d q K _ _ _ hK hr ε _ w pad
    · simpa only [Expr.rename_eval,Function.comp_def,Option.elim'_some] using hN
    · simpa only [Expr.rename_eval,Function.comp_def,Option.elim'_some] using hL
    · simpa only [Expr.rename_eval,Function.comp_def,Option.elim'_some] using hP
    · exact .hole i

 theorem columns_depth (N L P : Expr J) (ε : F₂) (row : Location M d q K J) :
    (columns M d q K N L P ε row).depth≤3 :=
  Enumeration.writer_depth _ _ _ _ _ _ _ _ 0 (by exact Nat.zero_le _) (fun _ _ => le_rfl) (by exact Nat.zero_le _)

 theorem matrixWriter_depth (N L P : Expr J) (ε : F₂) : (matrixWriter M d q K N L P ε).depth≤6 :=
  Enumeration.writer_depth _ _ _ _ _ _ _ _ 3 ((columns_depth M d q K N L P ε .hub).trans (by omega))
    (fun t v => columns_depth M d q K _ _ _ ε _) ((columns_depth M d q K _ _ _ ε .hole).trans (by omega))
end WLTime.OneTape.Symbolic

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression Enumeration
variable (M : OneTape) (d q K : ℕ) {J : Type uJ}
open scoped Classical

 theorem tagIndex_le (t : BlockTag M d q K) :
    (Fintype.equivFin _ t).val≤coefficient M d q K := by
  apply (Nat.le_of_lt (Fintype.equivFin _ t).isLt).trans
  exact Nat.le_mul_of_pos_right _ ((instanceData M d q []).tagValues_card_pos K)

 theorem countExpr_bounded (N : Expr J) (t : BlockTag M d q K) (a b : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hm : 1≤w.length)
    (hN : N.eval σ w=w.length) (hNB : N.Bounded σ w B)
    (ha : a.Bounded σ w B) (hb : b.Bounded σ w B)
    (hax : a.eval σ w<w.length) (hbx : b.eval σ w<w.length)
    (hC : coefficient M d q K≤B) (hL : (instanceData M d q w).slotLimit K≤B) :
    (countExpr M d q K N t a b).Bounded σ w B := by
  let c := coefficient M d q K
  let m := w.length
  let z := (Fintype.equivFin _ t).val
  let x := a.eval σ w
  let y := b.eval σ w
  have hz : z≤c := tagIndex_le M d q K t
  have ht : z<Fintype.card (BlockTag M d q K) := (Fintype.equivFin _ t).isLt
  have hraw : y+m*(x+m*z)+1≤c*m^2 := by
    have hh := ConsistencyData.mixedCode_le K t (⟨x,hax⟩ : Fin m) (⟨y,hbx⟩ : Fin m)
    have hc : Fintype.card (BlockTag M d q K)≤c :=
      Nat.le_mul_of_pos_right _ ((instanceData M d q []).tagValues_card_pos K)
    exact hh.trans (Nat.mul_le_mul_right _ hc)
  have hQ : (c*m^2+1)^2+1≤B := hL
  have hcpos : 1≤c := by
    by_contra h
    have hc0 : c=0 := by omega
    rw [hc0,zero_mul] at hraw
    omega
  have hm2 : m*m≤c*m^2 := by simpa only [pow_two] using Nat.le_mul_of_pos_left (m*m) hcpos
  have hcm : c*m^2+1≤B := by nlinarith [Nat.zero_le ((c*m^2)*(c*m^2))]
  have hzm : m*z≤x+m*z := Nat.le_add_left _ _
  have hxm : x+m*z ≤ m*(x+m*z) := Nat.le_mul_of_pos_left _ hm
  have hsum : y+m*(x+m*z)+1≤B := hraw.trans (by omega)
  have hmul : (y+m*(x+m*z)+1)*(c*m^2+1)≤B := by
    calc
      _ ≤ (c*m^2+1)*(c*m^2+1) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ B := by nlinarith
  unfold countExpr
  simp only [Expr.mul,Expr.add,Expr.Bounded,Expr.eval,Binary.eval,hN]
  change (((b.Bounded σ w B ∧ (N.Bounded σ w B ∧ (a.Bounded σ w B ∧
    (N.Bounded σ w B ∧ z≤B ∧ m*z≤B) ∧ x+m*z≤B) ∧ m*(x+m*z)≤B) ∧ y+m*(x+m*z)≤B) ∧
    1≤B ∧ y+m*(x+m*z)+1≤B) ∧ ((c≤B ∧ (N.Bounded σ w B ∧ N.Bounded σ w B ∧ m*m≤B) ∧
    c*(m*m)≤B) ∧ 1≤B ∧ c*(m*m)+1≤B) ∧ (y+m*(x+m*z)+1)*(c*(m*m)+1)≤B)
  exact ⟨⟨⟨hb,⟨hNB,⟨ha,⟨hNB,hz.trans hC,by omega⟩,by omega⟩,by omega⟩,by omega⟩,
      by omega,hsum⟩,⟨⟨hC,⟨hNB,hNB,hm2.trans (by omega)⟩,by nlinarith [hcm]⟩,
      by omega,by simpa only [pow_two] using hcm⟩,by simpa only [pow_two] using hmul⟩

 theorem sameRect_bounded (t u : BlockTag M d q K) (v z : Values M d q K)
    (a b c e : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (ha : a.Bounded σ w B) (hb : b.Bounded σ w B) (hc : c.Bounded σ w B) (he : e.Bounded σ w B) :
    (sameRect M d q K t u v z a b c e).Bounded σ w B := ⟨trivial,⟨ha,hc⟩,hb,he⟩

 theorem slotPredicate_bounded (N : Expr J) (ε : F₂) (t u : BlockTag M d q K)
    (v z : Values M d q K) (a b i c e j : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hm : 1≤w.length)
    (hN : N.eval σ w=w.length) (hNB : N.Bounded σ w B)
    (ha : a.Bounded σ w B) (hb : b.Bounded σ w B) (hi : i.Bounded σ w B)
    (hc : c.Bounded σ w B) (he : e.Bounded σ w B) (hj : j.Bounded σ w B)
    (hax : a.eval σ w<w.length) (hbx : b.eval σ w<w.length)
    (hcx : c.eval σ w<w.length) (hex : e.eval σ w<w.length)
    (hC : coefficient M d q K≤B) (hL : (instanceData M d q w).slotLimit K≤B) :
    (slotPredicate M d q K N ε t u v z a b i c e j).Bounded σ w (6*B) := by
  have hB : 1≤B := hm.trans (hN.symm ▸ N.eval_le σ w B hNB)
  have hBB : B≤6*B := by omega
  have hv := validity_bounded M d q N K ε t v a b σ w B hB hNB ha hb
  have hz := validity_bounded M d q N K ε u z c e σ w B hB hNB hc he
  have hR := adjacent_bounded M d q N K t u v z a b c e σ w B hB hNB ha hb hc he
  have hS := sameRect_bounded M d q K t u v z a b c e σ w B ha hb hc he
  have hS' := (sameRect M d q K t u v z a b c e).bounded_mono σ w hS hBB
  have hx := (countExpr M d q K N t a b).bounded_mono σ w
    (countExpr_bounded M d q K N t a b σ w B hm hN hNB ha hb hax hbx hC hL) hBB
  have hy := (countExpr M d q K N u c e).bounded_mono σ w
    (countExpr_bounded M d q K N u c e σ w B hm hN hNB hc he hcx hex hC hL) hBB
  have hi' := i.bounded_mono σ w hi hBB
  have hj' := j.bounded_mono σ w hj hBB
  unfold slotPredicate Predicate.rectangular Predicate.le Predicate.disj
  simp only [Predicate.Bounded]
  exact ⟨hv,hz,⟨hx,hi'⟩,⟨hy,hj'⟩,⟨⟨hi',by exact Nat.zero_le _⟩,⟨hj',by exact Nat.zero_le _⟩,hR⟩,
    ⟨⟨hi',by exact Nat.zero_le _⟩,⟨hj',by exact Nat.zero_le _⟩,hS'⟩,
    ⟨hi',by exact Nat.zero_le _⟩,⟨hj',by exact Nat.zero_le _⟩,hS'⟩

namespace Location
variable {M d q K}
 theorem rename_bounded {J' : Type uJ'} (f : J → J') (x : Location M d q K J)
    (σ : J' → ℕ) (w : List Bool) (B : ℕ) :
    (x.rename f).Bounded σ w B ↔ x.Bounded (σ ∘ f) w B := by
  cases x <;> simp only [rename,Bounded,Expr.rename_bounded,Expr.rename_eval]
end Location

 theorem adjacency_bounded (N : Expr J) (ε : F₂) (x y : Location M d q K J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hm : 1≤w.length)
    (hN : N.eval σ w=w.length) (hNB : N.Bounded σ w B)
    (hx : x.Bounded σ w B) (hy : y.Bounded σ w B)
    (hC : coefficient M d q K≤B) (hL : (instanceData M d q w).slotLimit K≤B) :
    (adjacency M d q K N ε x y).Bounded σ w (6*B) := by
  cases x <;> cases y
  case slot.slot t v a b i u z c e j =>
    exact slotPredicate_bounded M d q K N ε t u v z a b i c e j σ w B hm hN hNB
      hx.1 hx.2.1 hx.2.2.1 hy.1 hy.2.1 hy.2.2.1 hx.2.2.2.1 hx.2.2.2.2 hy.2.2.2.1 hy.2.2.2.2 hC hL
  all_goals trivial

 theorem columns_safe (N L P : Expr J) (ε : F₂) (row : Location M d q K J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hm : 1≤w.length)
    (hN : N.eval σ w=w.length) (hL : L.eval σ w=(instanceData M d q w).slotLimit K)
    (hNB : N.Bounded σ w B) (hLB : L.Bounded σ w B) (hPB : P.Bounded σ w B)
    (hx : row.Bounded σ w B) (hC : coefficient M d q K≤B) :
    (columns M d q K N L P ε row).Safe σ w (6*B) := by
  have hBB : B≤6*B := by omega
  have hlimit : (instanceData M d q w).slotLimit K≤B := hL ▸ L.eval_le σ w B hLB
  apply Enumeration.writer_safe _ _ N L P _ _ _ σ w (6*B)
    (N.bounded_mono σ w hNB hBB) (L.bounded_mono σ w hLB hBB) (P.bounded_mono σ w hPB hBB)
  · exact adjacency_bounded M d q K N ε row .hub σ w B hm hN hNB hx trivial hC hlimit
  · intro t v a ha b hb i hi
    apply adjacency_bounded M d q K _ ε _ _ _ w B hm
    · simpa only [Expr.rename_eval,up3,Function.comp_def,Option.elim'_some] using hN
    · simpa only [Expr.rename_bounded,up3,Function.comp_def,Option.elim'_some] using hNB
    · simpa only [Location.rename_bounded,up3,Function.comp_def,Option.elim'_some] using hx
    · change a≤B ∧ b≤B ∧ i≤B ∧ a<w.length ∧ b<w.length
      have hnB := N.eval_le σ w B hNB
      have hlB := L.eval_le σ w B hLB
      exact ⟨by omega,by omega,by omega,by omega,by omega⟩
    · exact hC
    · exact hlimit
  · intro i hi
    apply adjacency_bounded M d q K _ ε _ _ _ w B hm
    · simpa only [Expr.rename_eval,Function.comp_def,Option.elim'_some] using hN
    · simpa only [Expr.rename_bounded,Function.comp_def,Option.elim'_some] using hNB
    · simpa only [Location.rename_bounded,Function.comp_def,Option.elim'_some] using hx
    · trivial
    · exact hC
    · exact hlimit

 theorem matrixWriter_safe (N L P : Expr J) (ε : F₂)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hm : 1≤w.length)
    (hN : N.eval σ w=w.length) (hL : L.eval σ w=(instanceData M d q w).slotLimit K)
    (hNB : N.Bounded σ w B) (hLB : L.Bounded σ w B) (hPB : P.Bounded σ w B)
    (hC : coefficient M d q K≤B) :
    (matrixWriter M d q K N L P ε).Safe σ w (6*B) := by
  have hBB : B≤6*B := by omega
  apply Enumeration.writer_safe _ _ N L P _ _ _ σ w (6*B)
    (N.bounded_mono σ w hNB hBB) (L.bounded_mono σ w hLB hBB) (P.bounded_mono σ w hPB hBB)
  · exact columns_safe M d q K N L P ε .hub σ w B hm hN hL hNB hLB hPB trivial hC
  · intro t v a ha b hb i hi
    apply columns_safe M d q K _ _ _ ε _ _ w B hm
    · simpa only [Expr.rename_eval,up3,Function.comp_def,Option.elim'_some] using hN
    · simpa only [Expr.rename_eval,up3,Function.comp_def,Option.elim'_some] using hL
    · simpa only [Expr.rename_bounded,up3,Function.comp_def,Option.elim'_some] using hNB
    · simpa only [Expr.rename_bounded,up3,Function.comp_def,Option.elim'_some] using hLB
    · simpa only [Expr.rename_bounded,up3,Function.comp_def,Option.elim'_some] using hPB
    · change a≤B ∧ b≤B ∧ i≤B ∧ a<w.length ∧ b<w.length
      have hnB := N.eval_le σ w B hNB
      have hlB := L.eval_le σ w B hLB
      exact ⟨by omega,by omega,by omega,by omega,by omega⟩
    · exact hC
  · intro i hi
    apply columns_safe M d q K _ _ _ ε _ _ w B hm
    · simpa only [Expr.rename_eval,Function.comp_def,Option.elim'_some] using hN
    · simpa only [Expr.rename_eval,Function.comp_def,Option.elim'_some] using hL
    · simpa only [Expr.rename_bounded,Function.comp_def,Option.elim'_some] using hNB
    · simpa only [Expr.rename_bounded,Function.comp_def,Option.elim'_some] using hLB
    · simpa only [Expr.rename_bounded,Function.comp_def,Option.elim'_some] using hPB
    · trivial
    · exact hC
end WLTime.OneTape.Symbolic

end OAI
end

section
-- module Solutions.OAIQW_WLTime.MatrixBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uJ uK uL uA

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression Enumeration
variable (M : OneTape) (d q : ℕ)
open scoped Classical

 theorem listing_length (w : List Bool) (pad : ℕ) :
    (listing M d q (d+q+2) w pad).items.length=baseOrder M d q w.length+pad := by
  rw [Enumeration.Listing.length_eq_card]
  simp only [RawVertex,Enumeration.Vertex,Fintype.card_option,Fintype.card_sum,
    Fintype.card_prod,Fintype.card_fin]
  have hL : (instanceData M d q w).slotLimit (d+q+2)=
      (coefficient M d q (d+q+2)*w.length^2+1)^2+1 := rfl
  rw [hL]
  unfold baseOrder coefficient ConsistencyData.rectCoefficient
  simp only [ConsistencyData.BlockTag,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  ring_nf

variable {J : Type uJ}

 theorem pairWriter_eval (N L P : Expr J) (hr : 2≤d+q)
    (σ : J → ℕ) (w : List Bool) (pad : ℕ)
    (hN : N.eval σ w=w.length) (hL : L.eval σ w=(instanceData M d q w).slotLimit (d+q+2))
    (hP : P.eval σ w=pad) :
    (pairWriter M d q N L P).eval σ w=
      matrixBits (pairGraph M d q hr w pad 0)++matrixBits (pairGraph M d q hr w pad 1) := by
  simp only [pairWriter,Writer.eval,pairGraph]
  erw [Listing.matrix_bits,Listing.matrix_bits]
  rw [matrixWriter_eval M d q _ _ _ _ (by omega) (by omega) 0 σ w pad hN hL hP,
    matrixWriter_eval M d q _ _ _ _ (by omega) (by omega) 1 σ w pad hN hL hP]
  rfl

 theorem pairWriter_depth (N L P : Expr J) : (pairWriter M d q N L P).depth≤6 :=
  max_le (matrixWriter_depth M d q _ N L P 0) (matrixWriter_depth M d q _ N L P 1)

 theorem pairWriter_safe (N L P : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ) (hm : 1≤w.length)
    (hN : N.eval σ w=w.length) (hL : L.eval σ w=(instanceData M d q w).slotLimit (d+q+2))
    (hNB : N.Bounded σ w B) (hLB : L.Bounded σ w B) (hPB : P.Bounded σ w B)
    (hC : coefficient M d q (d+q+2)≤B) :
    (pairWriter M d q N L P).Safe σ w (6*B) :=
  ⟨matrixWriter_safe M d q _ N L P 0 σ w B hm hN hL hNB hLB hPB hC,
    matrixWriter_safe M d q _ N L P 1 σ w B hm hN hL hNB hLB hPB hC⟩
end WLTime.OneTape.Symbolic

namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]

 theorem seqShared_exec {p q : Program K} {s t u mid out}
    (hp : p.Exec s t mid) (hq : q.Exec mid u out) : (seqShared p q).Exec s (t+u) out := by
  exact .seq (raise_exec p hp _ (Fin.castLE_injective _)) (raise_exec q hq _ (Fin.castLE_injective _))
 theorem doubleUnary_exec (a : K) (m : ℕ) (s : Stacks K Bool) (hm : s a=UnaryPrograms.numeral m) :
    (doubleUnary a).Exec s (17*m+3) (Function.update s a (UnaryPrograms.numeral (2*m))) := by
  let z : Stacks (Fin 1 ⊕ K) Bool := Sum.elim (fun _ => []) s
  let mid := Function.update z (.inl 0) (UnaryPrograms.numeral m)
  have hc : (copy (.inr a) (.inl (0 : Fin 1))).Exec z (12*m+2) mid := by
    simpa only [z,Sum.elim_inr,Sum.elim_inl,hm,List.append_nil,UnaryPrograms.numeral_length] using
      copy_exec (Sum.inr a) (Sum.inl (0 : Fin 1)) (by simp) z
  have ht := ofCode_exec (Code.transfer_exec (Sum.inl (0 : Fin 1)) (Sum.inr a) (by simp) false mid)
  have he := seqShared_exec hc ht
  have hout : Function.update (Function.update mid (.inl 0) []) (.inr a)
      ((mid (.inl 0)).reverse++mid (.inr a))=
      Sum.elim (fun _ : Fin 1 => []) (Function.update s a (UnaryPrograms.numeral (2*m))) := by
    funext k; cases k with
    | inl i => have hi : i=0 := Subsingleton.elim _ _; subst i; simp only [Function.update_of_ne (Sum.inl_ne_inr),Function.update_self,Sum.elim_inl]
    | inr k =>
      by_cases hk : k=a
      · subst k
        simp only [Function.update_self,mid,z,Function.update_of_ne (Sum.inr_ne_inl),Sum.elim_inr,hm,
          UnaryPrograms.numeral,List.reverse_replicate,List.replicate_append_replicate,two_mul]
      · simp only [mid,z,Function.update_of_ne (Sum.inr_ne_inl),
          Function.update_of_ne (fun h : Sum.inr k=Sum.inr a => hk (Sum.inr.inj h)),
          Function.update_of_ne hk,Sum.elim_inr]
  rw [hout] at he
  apply local_exec
  convert he using 1
  simp only [mid,Function.update_self,UnaryPrograms.numeral_length]
  omega
 omit [DecidableEq K] in
 theorem loadDigits_scratch (a : K) (ds : List ℕ) : (loadDigits a ds).scratch≤2 := by
  induction ds with
  | nil => exact Nat.zero_le _
  | cons b bs ih => simpa only [loadDigits,seqShared,doubleUnary_scratch,pushes_scratch,max_zero] using max_le ih le_rfl
 theorem loadDigits_exec (a : K) (ds : List ℕ) (s : Stacks K Bool) (hs : s a=[]) :
    ∃t≤24*(ds.length+1)*(Nat.ofDigits 2 ds+1),
      (loadDigits a ds).Exec s t (Function.update s a (UnaryPrograms.numeral (Nat.ofDigits 2 ds))) := by
  induction ds with
  | nil =>
    refine ⟨1,by simp [Nat.ofDigits],?_⟩
    simpa only [loadDigits,Nat.ofDigits,UnaryPrograms.numeral,List.replicate_zero,←hs,Function.update_eq_self] using skip_exec s
  | cons b bs ih =>
    obtain ⟨t,ht,he⟩ := ih
    have hdouble := doubleUnary_exec a (Nat.ofDigits 2 bs)
      (Function.update s a (UnaryPrograms.numeral (Nat.ofDigits 2 bs))) (by simp)
    simp only [Function.update_idem] at hdouble
    have hpush := pushes_exec a (UnaryPrograms.numeral b)
      (Function.update s a (UnaryPrograms.numeral (2*Nat.ofDigits 2 bs)))
    have hf := seqShared_exec he (seqShared_exec hdouble hpush)
    refine ⟨t+(17*Nat.ofDigits 2 bs+3+(2*b+1)),?_,?_⟩
    · simp only [List.length_cons,Nat.ofDigits_cons]
      have hv : Nat.ofDigits 2 bs≤b+2*Nat.ofDigits 2 bs := by omega
      have hprod := Nat.mul_le_mul_left (24*(bs.length+1)) (Nat.add_le_add_right hv 1)
      nlinarith
    · simpa only [loadDigits,Function.update_self,Function.update_idem,UnaryPrograms.numeral_length,
        UnaryPrograms.numeral,List.length_replicate,←List.replicate_add,Nat.ofDigits_cons] using hf
 theorem loadNat_exec (a : K) (n : ℕ) (s : Stacks K Bool) (hs : s a=[]) :
    ∃t≤24*((Nat.digits 2 n).length+1)*(n+1),
      (loadNat a n).Exec s t (Function.update s a (UnaryPrograms.numeral n)) := by
  simpa only [loadNat,Nat.ofDigits_digits] using loadDigits_exec a (Nat.digits 2 n) s hs
end WLTime.TypedStack.Program

namespace WLTime.TypedStack.Code
variable {K : Type uK} [DecidableEq K]
theorem countLoop_exec (a b : K) (hab : a≠b) (xs : List Bool) (s : Stacks K Bool) (hs : s a=xs) :
    (countLoop a b).Exec s (5*xs.length+1)
      (Function.update (Function.update s a []) b (UnaryPrograms.numeral xs.length++s b)) := by
  induction xs generalizing s with
  | nil =>
    have h := Exec.loop_false (p:=nonempty a) (a:=Code.seq (.pop a) (.push b true)) (s:=s)
      (by simp [nonempty,tops,hs])
    have hout : (Function.update (Function.update s a []) b (UnaryPrograms.numeral 0++s b))=s := by
      simp only [UnaryPrograms.numeral,List.replicate_zero,List.nil_append]
      funext k; by_cases hb : k=b
      · subst k; simp
      · by_cases ha : k=a
        · subst k; simp [hab,hs]
        · simp [hb,ha]
    change (countLoop a b).Exec s 1 _
    simp only [List.length_nil]
    rw [hout]
    exact h
  | cons x xs ih =>
    let z := Function.update (Function.update s a xs) b (true::s b)
    have he : (Code.seq (.pop a) (.push b true)).Exec s 4 z := by
      simpa only [hs,List.tail_cons,Function.update_of_ne hab.symm,z] using
        Exec.seq (Exec.pop s a) (Exec.push (Function.update s a (s a).tail) b true)
    have hz : z a=xs := by simp [z,hab]
    have hi := ih z hz
    have h := Exec.loop_true (p:=nonempty a) (by simp [nonempty,tops,hs]) he hi
    have hout : Function.update (Function.update s a []) b (UnaryPrograms.numeral (x::xs).length++s b)=
        Function.update (Function.update z a []) b (UnaryPrograms.numeral xs.length++z b) := by
      funext k; by_cases hb : k=b
      · subst k
        simp only [Function.update_self,z,UnaryPrograms.numeral,List.length_cons]
        rw [List.replicate_succ']; simp only [List.append_assoc,List.singleton_append]
      · by_cases ha : k=a
        · subst k; simp [hab,z]
        · simp [hb,ha,z]
    rw [hout]
    have htime : 5*(x::xs).length+1=4+(5*xs.length+1)+1 := by simp only [List.length_cons]; omega
    rw [htime]
    exact h
end WLTime.TypedStack.Code
namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]
theorem countLength_exec (a b : K) (s : Stacks K Bool) :
    (countLength a b).Exec s (17*(s a).length+3)
      (Function.update s b (UnaryPrograms.numeral (s a).length++s b)) := by
  let z : Stacks (Fin 1 ⊕ K) Bool := Sum.elim (fun _ => []) s
  let mid := Function.update z (.inl (0 : Fin 1)) (s a)
  have hc : (copy (.inr a) (.inl (0 : Fin 1))).Exec z (12*(s a).length+2) mid := by
    simpa only [z,Sum.elim_inr,Sum.elim_inl,List.append_nil] using
      copy_exec (Sum.inr a) (Sum.inl (0 : Fin 1)) (by simp) z
  have hl := ofCode_exec (Code.countLoop_exec (Sum.inl (0 : Fin 1)) (Sum.inr b) (by simp)
    (s a) mid (by simp [mid]))
  have he := seq_exec hc hl
  have hout : Function.update (Function.update mid (.inl 0) []) (.inr b)
      (UnaryPrograms.numeral (s a).length++mid (.inr b))=
      Sum.elim (fun _ : Fin 1 => []) (Function.update s b (UnaryPrograms.numeral (s a).length++s b)) := by
    funext k; cases k with
    | inl i => have hi:i=0 := Subsingleton.elim _ _; subst i; simp
    | inr k => simp only [mid,z,Function.update_of_ne Sum.inr_ne_inl,Sum.elim_inr,
        Function.update_apply,Sum.inr.injEq]
  rw [hout] at he
  apply local_exec
  convert he using 1
  omega
end WLTime.TypedStack.Program

namespace WLTime.NatCode.Expr
variable {K : Type uK}

 theorem bounded_degree (e : Expr K) (σ : K → ℕ) (w : List Bool) (Q : ℕ) (hQ : 2≤Q)
    (h : e.AtomsBounded σ Q) : e.Bounded σ w (Q^e.degree) := by
  induction e with
  | const n => simpa only [Bounded,degree,pow_one,AtomsBounded] using h
  | var k => simpa only [Bounded,degree,pow_one,AtomsBounded] using h
  | binary op a b ia ib =>
    have ha := ia h.1
    have hb := ib h.2
    have hqa : Q^a.degree≤Q^(a.degree+b.degree+1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hqb : Q^b.degree≤Q^(a.degree+b.degree+1) := Nat.pow_le_pow_right (by omega) (by omega)
    refine ⟨a.bounded_mono σ w ha hqa,b.bounded_mono σ w hb hqb,?_⟩
    have va := a.eval_le σ w _ ha
    have vb := b.eval_le σ w _ hb
    have h1a : 1≤Q^a.degree := Nat.one_le_pow _ _ (by omega)
    have h1b : 1≤Q^b.degree := Nat.one_le_pow _ _ (by omega)
    change op.eval (a.eval σ w) (b.eval σ w)≤Q^(a.degree+b.degree+1)
    rw [pow_succ,pow_add]
    cases op with
    | add =>
      change a.eval σ w+b.eval σ w≤_
      have haa : Q^a.degree≤Q^a.degree*Q^b.degree := Nat.le_mul_of_pos_right _ (by omega)
      have hbb : Q^b.degree≤Q^a.degree*Q^b.degree := Nat.le_mul_of_pos_left _ (by omega)
      nlinarith
    | mul =>
      change a.eval σ w*b.eval σ w≤_
      exact (Nat.mul_le_mul va vb).trans (Nat.le_mul_of_pos_right _ (by omega))
    | sub =>
      change a.eval σ w-b.eval σ w≤_
      exact (Nat.sub_le _ _).trans (va.trans (by simpa only [pow_succ,pow_add] using hqa))
  | bit a ia =>
    have ha := ia h
    exact ⟨a.bounded_mono σ w ha (Nat.pow_le_pow_right (by omega) (by simp [degree])),
      Nat.one_le_pow _ _ (by omega)⟩
end WLTime.NatCode.Expr

end OAI
end

section
-- module Solutions.OAIQW_WLTime.TapePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uB uL uS uT

namespace WLTime.OneTape.Symbolic
open NatCode TypedStack UnaryPrograms
open scoped Classical
variable (M : OneTape) (d q : ℕ)
namespace FullWriter

 theorem eval_N (m n : ℕ) (w : List Bool) : N.eval (args m n) w=m := rfl
 theorem eval_L (n : ℕ) (w : List Bool) : (L M d q).eval (args w.length n) w=
    (instanceData M d q w).slotLimit (d+q+2) := by
  simp only [L,E,R,N,Expr.eval,Binary.eval,args,Bool.false_eq_true,ite_false]
  change _=(coefficient M d q (d+q+2)*w.length^2+1)^2+1
  ring_nf
 theorem eval_B (m n : ℕ) (w : List Bool) : (B M d q).eval (args m n) w=baseOrder M d q m := by
  simp only [B,L,E,R,N,Expr.eval,Binary.eval,args,Bool.false_eq_true,ite_false,baseOrder]
  ring_nf
 theorem eval_P (m n : ℕ) (w : List Bool) : (P M d q).eval (args m n) w=n-baseOrder M d q m := by
  change n-(B M d q).eval (args m n) w=_
  rw [eval_B]

 theorem safe (n : ℕ) (w : List Bool) (hm : 1≤w.length) :
    (body M d q).Safe (args w.length n) w (6*(coefficient M d q (d+q+2)+n+w.length+2)^27) := by
  let Q := coefficient M d q (d+q+2)+n+w.length+2
  have hQ : 2≤Q := by dsimp [Q]; omega
  have hat : ∀e∈([N,L M d q,P M d q] : List (Expr Bool)),e.AtomsBounded (args w.length n) Q := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl <;>
      simp only [N,L,E,R,P,B,Expr.AtomsBounded,args,Bool.false_eq_true,ite_false,ite_true] <;>
      dsimp [Q] <;> omega
  have hB (e : Expr Bool) (he : e∈[N,L M d q,P M d q]) (hd : e.degree≤27) :
      e.Bounded (args w.length n) w (Q^27) :=
    e.bounded_mono _ _ (e.bounded_degree _ _ Q hQ (hat e he))
      (Nat.pow_le_pow_right (by omega) hd)
  apply pairWriter_safe M d q N (L M d q) (P M d q) (args w.length n) w (Q^27) hm
    (eval_N _ _ _) (eval_L M d q n w)
  · exact hB N (by simp) (by decide)
  · exact hB _ (by simp) (by simp only [L,E,R,N,Expr.degree]; decide)
  · exact hB _ (by simp) (by simp only [P,B,L,E,R,N,Expr.degree]; decide)
  · have hCQ : coefficient M d q (d+q+2)≤Q := by dsimp [Q]; omega
    exact hCQ.trans (Nat.le_self_pow (by omega) Q)

 theorem correct (n : ℕ) (w : List Bool) (hm : 1≤w.length) (hr : 2≤d+q)
    (hn : baseOrder M d q w.length≤n) :
    ∃t≤budget M d q n w.length,∃out,
      (program M d q n).Exec (fun r => if r=Reg.word then w else []) t out ∧
      out .output=(encodePair
        (pairGraph M d q hr w (n-baseOrder M d q w.length) 0)
        (pairGraph M d q hr w (n-baseOrder M d q w.length) 1)).reverse := by
  let s : Stacks Reg Bool := fun r => if r=Reg.word then w else []
  let s1 := Function.update s Reg.len (numeral w.length)
  let s2 := Function.update s1 Reg.order (numeral n)
  let s3 := Function.update s2 Reg.output (encodeNat n).reverse
  have hcount : (Program.countLength Reg.word Reg.len).Exec s (17*w.length+3) s1 := by
    simpa [s,s1] using Program.countLength_exec Reg.word Reg.len s
  obtain ⟨t,ht,hload⟩ := Program.loadNat_exec Reg.order n s1 (by simp [s1,s])
  have hpush : (Program.pushes Reg.output (encodeNat n).reverse).Exec s2 (2*(encodeNat n).length+1) s3 := by
    simpa [s3,s2,s1,s] using Program.pushes_exec Reg.output (encodeNat n).reverse s2
  have hQ : w.length≤6*(coefficient M d q (d+q+2)+n+w.length+2)^27 := by
    have hmQ : w.length≤coefficient M d q (d+q+2)+n+w.length+2 := by omega
    have hp := Nat.le_self_pow (by decide : 27≠0) (coefficient M d q (d+q+2)+n+w.length+2)
    omega
  obtain ⟨v,hv,hbody⟩ := (body M d q).compile_exec rho Reg.word Reg.output (by decide)
    (by intro b; cases b <;> decide) (args w.length n) w _ (safe M d q n w hm) hQ s3
    (by intro b; cases b <;> simp [s3,s2,s1,s,rho,args]) (by simp [s3,s2,s1,s])
  have hd := pairWriter_depth M d q N (L M d q) (P M d q)
  have hv' : v≤(body M d q).charge*(6*(coefficient M d q (d+q+2)+n+w.length+2)^27+1)^8 :=
    hv.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by change (pairWriter M d q N (L M d q) (P M d q)).depth+2≤8; omega)))
  have he := Program.seqShared_exec hcount (Program.seqShared_exec hload (Program.seqShared_exec hpush hbody))
  refine ⟨_,?_,_,he,?_⟩
  · dsimp [budget]; omega
  · simp only [Function.update_self]
    have hlen : (listing M d q (d+q+2) w (n-baseOrder M d q w.length)).items.length=n := by
      rw [listing_length,Nat.add_sub_of_le hn]
    have hb := pairWriter_eval M d q N (L M d q) (P M d q) hr (args w.length n) w
      (n-baseOrder M d q w.length) (eval_N _ _ _) (eval_L M d q n w) (eval_P M d q _ _ _)
    change ((body M d q).eval (args w.length n) w).reverse++(s3 Reg.output) = _
    rw [show (body M d q).eval (args w.length n) w=_ from hb]
    simp only [s3,Function.update_self,encodePair,hlen,List.reverse_append,List.append_assoc]
end FullWriter
end WLTime.OneTape.Symbolic

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} {B : Type uB} [DecidableEq K]
 theorem listMap_update (f : A → B) (s : Stacks K A) (k : K) (xs : List A) :
    listMap f (Function.update s k xs)=Function.update (listMap f s) k (xs.map f) := by
  funext j; by_cases h : j=k
  · subst j; simp only [listMap,Function.update_self]
  · simp only [listMap,Function.update_of_ne h]
 omit [DecidableEq K] in
 theorem unmap_tops (f : A → B) (g : B → A) (h : Function.LeftInverse g f) (s : Stacks K A) :
    (fun k => (tops (listMap f s) k).map g)=tops s := by
  funext k
  cases hs : s k with
  | nil => simp only [tops,listMap,hs,List.map_nil,List.head?_nil,Option.map_none]
  | cons x xs => simp only [tops,listMap,hs,List.map_cons,List.head?_cons,Option.map_some,h x]
 theorem mapLetters_exec (f : A → B) (g : B → A) (h : Function.LeftInverse g f)
    {c : Code K A} {s t out} (hc : c.Exec s t out) :
    (c.mapLetters f g).Exec (listMap f s) t (listMap f out) := by
  induction hc with
  | skip s => exact .skip _
  | push s k x => simpa only [mapLetters,listMap_update,List.map_cons,listMap] using Exec.push (listMap f s) k (f x)
  | pushDyn s k hh =>
    simpa only [mapLetters,listMap_update,List.map_cons,unmap_tops f g h,listMap] using
      Exec.pushDyn (listMap f s) k (fun v => f (hh (fun k => (v k).map g)))
  | pop s k => simpa only [mapLetters,listMap_update,List.map_tail,listMap] using Exec.pop (listMap f s) k
  | seq ha hb ia ib => exact .seq ia ib
  | branch_true ht he ih => exact .branch_true (by simpa only [unmap_tops f g h] using ht) ih
  | branch_false ht he ih => exact .branch_false (by simpa only [unmap_tops f g h] using ht) ih
  | loop_false ht => exact .loop_false (by simpa only [unmap_tops f g h] using ht)
  | loop_true ht he hr ie ir => exact .loop_true (by simpa only [unmap_tops f g h] using ht) ie ir
end WLTime.TypedStack.Code

namespace WLTime.TypedStack.Code
variable {K : Type uK} {L : Type uL} {A : Type uA} [DecidableEq K] [DecidableEq L]
theorem relabel_inl_exec {c : Code K A} {s t out} (h : c.Exec s t out) (e : L → List A) :
    (c.relabel (Sum.inl : K → K ⊕ L)).Exec (Sum.elim s e) t (Sum.elim out e) := by
  apply relabel_exec_of_maps _ Sum.inl_injective h
  · intro k; rfl
  · intro k; rfl
  · intro k hk; cases k with
    | inl k => exact False.elim (hk k rfl)
    | inr k => rfl
end WLTime.TypedStack.Code

namespace WLTime.TapePair
variable {A : Type uA}

 theorem getD_tail (s : List A) (n : ℕ) (blank : A) :
    s.tail.getD n blank=s.getD (n+1) blank := by cases s <;> rfl

theorem contents_moveWrite (blank x : A) (d : Move) (s : Tape A) (z : ℤ) :
    contents blank (moveWrite blank x d s) z =
      if z+d.displacement=0 then x else contents blank s (z+d.displacement) := by
  cases d with
  | stay =>
    simp only [Move.displacement,add_zero,moveWrite,contents]
    by_cases hz : z<0
    · have h0 : z≠0 := by omega
      simp only [hz,ite_true,h0,ite_false]
    · by_cases h0 : z=0
      · subst z; simp
      · have he : z.toNat=(z-1).toNat+1 := by omega
        simp only [hz,ite_false,h0,he,List.getD_cons_succ,getD_tail]
  | right =>
    simp only [Move.displacement,moveWrite,contents]
    by_cases hz : z<0
    · by_cases he : z+1=0
      · have hz' : (-z-1).toNat=0 := by omega
        simp only [hz,ite_true,he,hz',List.getD_cons_zero]
      · have hz' : z+1<0 := by omega
        have ht : (-z-1).toNat=(-(z+1)-1).toNat+1 := by omega
        simp only [hz,ite_true,he,ite_false,hz',ht,List.getD_cons_succ]
    · have hz' : ¬z+1<0 := by omega
      have he : z+1≠0 := by omega
      have ht : (z+1).toNat=z.toNat+1 := by omega
      simp only [hz,ite_false,he,hz',getD_tail,ht]
  | left =>
    simp only [Move.displacement,moveWrite,contents]
    by_cases hz : z<0
    · have hz' : z+ -1<0 := by omega
      have he : z+ -1≠0 := by omega
      have ht : (-(z+ -1)-1).toNat=(-z-1).toNat+1 := by omega
      simp only [hz,ite_true,he,ite_false,hz',getD_tail,ht]
    · by_cases h0 : z=0
      · subst z
        cases s.left <;> rfl
      · by_cases h1 : z=1
        · subst z
          simp
        · have hz' : ¬z+ -1<0 := by omega
          have he : z+ -1≠0 := by omega
          have ht : z.toNat=((z+ -1).toNat-1)+1+1 := by omega
          have hs : (z+ -1).toNat-1+1=(z+ -1).toNat := by omega
          simp only [hz,ite_false,he,hz']
          calc
            (s.left.headD blank::x::s.right.tail).getD z.toNat blank =
                s.right.tail.getD ((z+ -1).toNat-1) blank := by
              rw [ht,List.getD_cons_succ,List.getD_cons_succ]
            _ = s.right.getD (z+ -1).toNat blank := by rw [getD_tail,hs]

end WLTime.TapePair

namespace WLTime.TMStack
open TypedStack
variable {K : Type uK} {A : Type uA} [DecidableEq K]

theorem single_exec (blank x : A) (k : K) (d : Move) (s : K → TapePair.Tape A) :
    (single blank k x d).Exec (store s) (tapeCost d)
      (store (Function.update s k (TapePair.moveWrite blank x d (s k)))) := by
  have hs : (k,false)≠(k,true) := by simp
  have ht (a : K) (b : Bool) (ha : a≠k) : (a,b)≠(k,true) ∧ (a,b)≠(k,false) := by
    constructor <;> intro h <;> apply ha <;> exact congrArg Prod.fst h
  cases d with
  | stay =>
    have hg := Code.Exec.seq (Code.Exec.pop (store s) (k,true))
      (Code.Exec.push _ (k,true) x)
    convert hg using 1 <;> try rfl
    funext ⟨a,b⟩
    by_cases ha : a=k
    · subst a; cases b <;> simp [store,TapePair.moveWrite,hs]
    · rcases ht a b ha with ⟨h1,h2⟩
      simp [store,TapePair.moveWrite,Function.update_of_ne ha,Function.update_of_ne h1]
  | right =>
    have hg := Code.Exec.seq (Code.Exec.pop (store s) (k,true))
      (Code.Exec.push _ (k,false) x)
    convert hg using 1 <;> try rfl
    funext ⟨a,b⟩
    by_cases ha : a=k
    · subst a; cases b <;> simp [store,TapePair.moveWrite,hs]
    · rcases ht a b ha with ⟨h1,h2⟩
      simp [store,TapePair.moveWrite,Function.update_of_ne ha,Function.update_of_ne h1,
        Function.update_of_ne h2]
  | left =>
    have hg := Code.Exec.seq (Code.Exec.seq (Code.Exec.seq (Code.Exec.pop (store s) (k,true))
      (Code.Exec.push _ (k,true) x))
      (Code.Exec.pushDyn _ (k,true) (fun v => (v (k,false)).getD blank)))
      (Code.Exec.pop _ (k,false))
    convert hg using 1 <;> try rfl
    funext ⟨a,b⟩
    by_cases ha : a=k
    · subst a; cases b <;> simp [store,TapePair.moveWrite,tops,hs,List.headD]
      cases (s k).left <;> rfl
    · rcases ht a b ha with ⟨h1,h2⟩
      simp [store,TapePair.moveWrite,Function.update_of_ne ha,Function.update_of_ne h1,
        Function.update_of_ne h2]

omit [DecidableEq K] in
theorem bodyCost_le (d : K → Move) (ks : List K) : bodyCost d ks ≤ 8*ks.length+1 := by
  have hh (k : K) : tapeCost (d k) ≤ 8 := by cases d k <;> decide
  induction ks with
  | nil => simp [bodyCost]
  | cons k ks ih =>
    simp only [bodyCost,List.map_cons,List.sum_cons,List.length_cons,Function.comp_apply] at *
    have := hh k
    omega

theorem body_exec (blank : A) (w : K → A) (d : K → Move) (ks : List K) (s : K → TapePair.Tape A)
    (hn : ks.Nodup) :
    (body blank w d ks).Exec (store s) (bodyCost d ks)
      (store (fun k => if k∈ks then TapePair.moveWrite blank (w k) (d k) (s k) else s k)) := by
  induction ks generalizing s with
  | nil => simpa [body,bodyCost] using Code.Exec.skip (store s)
  | cons k ks ih =>
    have he := Code.Exec.seq (single_exec blank (w k) k (d k) s)
      (ih (Function.update s k (TapePair.moveWrite blank (w k) (d k) (s k))) hn.of_cons)
    convert he using 1 <;> try rfl
    congr 1
    funext a
    by_cases ha : a=k
    · subst a
      have hm := List.nodup_cons.mp hn |>.1
      simp [hm]
    · simp [ha]

end WLTime.TMStack

namespace WLTime.TMStack
open TypedStack
variable (M : TM)

theorem stepCode_exec (p : Payload M) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) :
    (stepCode M p).Exec (store s) (bodyCost p.2.2 (List.finRange M.tapes))
      (store (nextTapes M p s)) := by
  unfold stepCode nextTapes
  simpa only [List.mem_finRange,ite_true] using
    body_exec (blank M) p.2.1 p.2.2 (List.finRange M.tapes) s (List.nodup_finRange _)

theorem next_relative {C : M.Config} {s : Fin M.tapes → TapePair.Tape (Fin M.symbols)}
    (h : Relative M C s) (hh : ¬M.halted C) :
    Relative M (M.step C) (nextTapes M (M.transition C.state (fun a => C.tape a (C.head a))) s) := by
  intro a z
  simp only [nextTapes,TapePair.contents_moveWrite]
  rw [h]
  simp only [TM.step,hh,ite_false]
  simp only [add_assoc,add_eq_left]
  rw [add_comm ((M.transition C.state (fun a => C.tape a (C.head a))).2.2 a).displacement z]

end WLTime.TMStack

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Consumer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uB

namespace WLTime.TMStack
open TypedStack
variable (M : TM)

theorem initial_relative (w : List Bool) : Relative M (M.initial w) (initialTapes M w) := by
  intro a z
  simp only [TapePair.contents,initialTapes,TM.initial,zero_add]
  by_cases hz : z<0
  · have hz' : ¬0≤z := by omega
    simp only [hz,ite_true,List.getD_nil,hz',false_and,and_false,ite_false]
    rfl
  · have hz' : 0≤z := by omega
    simp only [hz,ite_false,hz']
    by_cases ha : a.val=0
    · simp only [ha,ite_true,true_and]
      by_cases hb : z.toNat<w.length
      · simp only [hb,ite_true,List.getD_eq_getElem (w.map M.symbol) (blank M) (by simpa only [List.length_map] using hb),
          List.getElem_map,List.getD_eq_getElem _ _ hb]
      · have hb' : w.length≤z.toNat := by omega
        simp only [hb,ite_false,List.getD_eq_default (w.map M.symbol) (blank M) (by simpa only [List.length_map] using hb')]
        rfl
    · simp only [ha,ite_false,false_and,List.getD_nil]
      rfl

end WLTime.TMStack

namespace WLTime.OneTape.Symbolic.FullWriter
open NatCode TypedStack UnaryPrograms
open scoped Classical
variable (U : OneTape) (d q : ℕ)
 theorem scratch_le (n : ℕ) : (program U d q n).scratch ≤ scratchBound U d q := by
  have h := Program.loadDigits_scratch Reg.order (Nat.digits 2 n)
  simp only [program,Program.seqShared,Program.pushes_scratch,scratchBound,Program.loadNat]
  omega

 theorem code_correct (n : ℕ) (w : List Bool) (hm : 1 ≤ w.length) (hr : 2 ≤ d+q)
    (hn : baseOrder U d q w.length ≤ n) :
    ∃t ≤ budget U d q n w.length,∃out,
      (program U d q n).code.Exec (TMConsumer.boolInput (.inr Reg.word) w) t out ∧
      out (.inr Reg.output)=(encodePair
        (pairGraph U d q hr w (n-baseOrder U d q w.length) 0)
        (pairGraph U d q hr w (n-baseOrder U d q w.length) 1)).reverse := by
  obtain ⟨t,ht,out,he,ho⟩ := correct U d q n w hm hr hn
  refine ⟨t,ht,(program U d q n).ambient out,?_,ho⟩
  have hs : (program U d q n).ambient (fun r => if r=Reg.word then w else [])=
      TMConsumer.boolInput (.inr Reg.word) w := by
    funext k; cases k <;> simp [Program.ambient,TMConsumer.boolInput]
  simpa only [Program.Exec,hs] using he

end WLTime.OneTape.Symbolic.FullWriter

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Transducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uT

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} {T : Type uT} [DecidableEq K] [DecidableEq T]
 theorem casesList_exec (select : Tops K A → T) (body : T → Code K A) (xs : List T)
    {s t out} (hx : select (tops s)∈xs) (he : (body (select (tops s))).Exec s t out) :
    ∃u ≤ t+xs.length,(casesList select body xs).Exec s u out := by
  induction xs with
  | nil => simp at hx
  | cons x xs ih =>
    by_cases h : select (tops s)=x
    · refine ⟨t+1,by simp,?_⟩
      exact .branch_true (by simpa using h) (h ▸ he)
    · have hm : select (tops s)∈xs := (List.mem_cons.mp hx).resolve_left h
      obtain ⟨u,hu,he'⟩ := ih hm
      exact ⟨u+1,by simp only [List.length_cons]; omega,.branch_false (by simpa using h) he'⟩
 theorem casesAll_exec [Fintype T] (select : Tops K A → T) (body : T → Code K A)
    {s t out} (he : (body (select (tops s))).Exec s t out) :
    ∃u ≤ t+Fintype.card T,(casesAll select body).Exec s u out := by
  simpa only [Finset.length_toList,Finset.card_univ,casesAll] using
    casesList_exec select body Finset.univ.toList (by simp) he
end WLTime.TypedStack.Code

namespace WLTime.TMTransducer
open TypedStack
variable (M : TM)

 theorem select_store (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) :
    select M (tops (store M q s ds))=(q,fun a => (s a).right.headD (TMStack.blank M)) := by
  apply Prod.ext
  · rfl
  · funext a
    change (((s a).right.map Sum.inl).head?.map (symbolDecode M)).getD (TMStack.blank M)=(s a).right.headD (TMStack.blank M)
    cases (s a).right <;> rfl

 theorem body_exec (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move)
    (p : TMStack.Payload M) :
    (stepBody M p).Exec (store M q s ds) (TMStack.bodyCost p.2.2 (List.finRange M.tapes)+6)
      (store M p.1 (TMStack.nextTapes M p s) (p.2.2 ⟨0,M.tapes_pos⟩::ds)) := by
  have hb := Code.mapLetters_exec (Sum.inl : Fin M.symbols → Letter M) (symbolDecode M)
    (by intro x; rfl) (TMStack.stepCode_exec M p s)
  have he := Code.relabel_inr_exec hb
    (fun i : Fin 2 => if i.val=0 then [Sum.inr (Sum.inl q)] else ds.map (fun d => Sum.inr (Sum.inr d)))
  let mid := store M q (TMStack.nextTapes M p s) ds
  have hp := Code.Exec.pop mid (stateReg M)
  have hq := Code.Exec.push (Function.update mid (stateReg M) (mid (stateReg M)).tail)
    (stateReg M) (Sum.inr (Sum.inl p.1))
  have hd := Code.Exec.push
    (Function.update (Function.update mid (stateReg M) (mid (stateReg M)).tail)
      (stateReg M) (Sum.inr (Sum.inl p.1)::(mid (stateReg M)).tail))
    (historyReg M) (Sum.inr (Sum.inr (p.2.2 ⟨0,M.tapes_pos⟩)))
  have hex := Code.Exec.seq he (Code.Exec.seq hp (Code.Exec.seq hq hd))
  unfold stepBody
  convert hex using 1 <;> try rfl
  funext k
  cases k with
  | inl i => fin_cases i <;> rfl
  | inr k => rfl

 theorem step_exec (C : M.Config) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move)
    (hr : TMStack.Relative M C s) :
    ∃u ≤ stepFactor M-1,(step M).Exec (store M C.state s ds) u
      (store M (M.transition C.state (fun a => C.tape a (C.head a))).1
        (TMStack.nextTapes M (M.transition C.state (fun a => C.tape a (C.head a))) s)
        ((M.transition C.state (fun a => C.tape a (C.head a))).2.2 ⟨0,M.tapes_pos⟩::ds)) := by
  have hs : select M (tops (store M C.state s ds))=(C.state,fun a => C.tape a (C.head a)) := by
    rw [select_store]
    congr 1
    funext a
    have h := hr a 0
    simpa only [TapePair.contents_zero,add_zero] using h
  have hb := body_exec M C.state s ds (M.transition C.state (fun a => C.tape a (C.head a)))
  change ((fun x : Key M => stepBody M (M.transition x.1 x.2))
    (C.state,fun a => C.tape a (C.head a))).Exec _ _ _ at hb
  rw [←hs] at hb
  obtain ⟨u,hu,he⟩ := Code.casesAll_exec (select M) (fun x => stepBody M (M.transition x.1 x.2)) hb
  refine ⟨u,?_,he⟩
  have ht := TMStack.bodyCost_le (M.transition C.state (fun a => C.tape a (C.head a))).2.2 (List.finRange M.tapes)
  simp only [List.length_finRange] at ht
  dsimp [stepFactor]
  omega

 theorem run_exec (C : M.Config) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) (v : ℕ)
    (hr : TMStack.Relative M C s) (hh : M.halted (M.step^[v] C)) :
    ∃u ≤ stepFactor M*v+1,∃s' ds',
      (runCode M).Exec (store M C.state s ds) u (store M (M.step^[v] C).state s' ds') ∧
      TMStack.Relative M (M.step^[v] C) s' ∧ ds'.length ≤ ds.length+v ∧
      (M.step^[v] C).head ⟨0,M.tapes_pos⟩ = C.head ⟨0,M.tapes_pos⟩+
        (ds'.map Move.displacement).sum-(ds.map Move.displacement).sum := by
  induction v generalizing C s ds with
  | zero =>
    refine ⟨1,by omega,s,ds,?_,hr,by simp,by simp⟩
    apply Code.Exec.loop_false
    simp only [live,select_store,decide_eq_false_iff_not,not_not]
    exact hh
  | succ v ih =>
    by_cases hhalt : M.halted C
    · have hf : M.step^[v+1] C=C := Function.iterate_fixed (by simp [TM.step,hhalt]) _
      refine ⟨1,by omega,s,ds,?_,by simpa only [hf] using hr,by simp,by simp [hf]⟩
      rw [hf]
      apply Code.Exec.loop_false
      simpa only [live,select_store,decide_eq_false_iff_not,not_not,TM.halted] using hhalt
    · let p := M.transition C.state (fun a => C.tape a (C.head a))
      have hC : (M.step C).state=p.1 := by simp only [TM.step,hhalt,ite_false,p]
      obtain ⟨a,ha,he⟩ := step_exec M C s ds hr
      change (step M).Exec _ a (store M p.1 (TMStack.nextTapes M p s) (p.2.2 ⟨0,M.tapes_pos⟩::ds)) at he
      obtain ⟨b,hb,s',ds',hf,hr',hlen,hhead⟩ := ih (M.step C) (TMStack.nextTapes M p s)
        (p.2.2 ⟨0,M.tapes_pos⟩::ds) (TMStack.next_relative M hr hhalt)
        (by simpa only [Function.iterate_succ_apply] using hh)
      rw [hC] at hf
      have ht : live M (tops (store M C.state s ds))=true := by
        simpa only [live,select_store,decide_eq_true_eq,TM.halted] using hhalt
      have hsf : 1 ≤ stepFactor M := by dsimp [stepFactor]; omega
      have ha' : a+1 ≤ stepFactor M := by omega
      refine ⟨a+b+1,by nlinarith, s',ds',?_,?_,?_,?_⟩
      · simpa only [Function.iterate_succ_apply,runCode] using Code.Exec.loop_true ht he hf
      · simpa only [Function.iterate_succ_apply] using hr'
      · simp only [List.length_cons] at hlen; omega
      · simp only [Function.iterate_succ_apply]
        rw [hhead]
        simp only [TM.step,hhalt,ite_false,List.map_cons,List.sum_cons,p]
        omega
end WLTime.TMTransducer

namespace WLTime.TapePair
variable {A : Type uA}
 theorem contents_move (blank : A) (d : Move) (s : Tape A) (z : ℤ) :
    contents blank (move blank d s) z=contents blank s (z+d.displacement) := by
  rw [move,contents_moveWrite]
  split_ifs with h
  · rw [h,contents_zero]
  · rfl
end WLTime.TapePair
namespace WLTime.TMTransducer
open TypedStack
variable (M : TM)

 theorem rewindBody_exec (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (d : Move) (ds : List Move) :
    (rewindBody M d ((s (zeroTape M)).right.headD (TMStack.blank M))).Exec (store M q s (d::ds))
      (TMStack.tapeCost d.inverse+2) (store M q (moveOrigin M s d) ds) := by
  have he := TMStack.single_exec (TMStack.blank M) ((s (zeroTape M)).right.headD (TMStack.blank M))
    (zeroTape M) d.inverse s
  have hf := Code.mapLetters_exec (Sum.inl : Fin M.symbols → Letter M) (symbolDecode M) (by intro x; rfl) he
  have hg := Code.relabel_inr_exec hf
    (fun i : Fin 2 => if i.val=0 then [Sum.inr (Sum.inl q)] else (d::ds).map (fun d => Sum.inr (Sum.inr d)))
  let mid := store M q (moveOrigin M s d) (d::ds)
  have hp := Code.Exec.seq hg (Code.Exec.pop mid (historyReg M))
  unfold rewindBody
  convert hp using 1 <;> try rfl
  funext k
  cases k with
  | inl i => fin_cases i <;> rfl
  | inr k => rfl
 theorem rewindStep_exec (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (d : Move) (ds : List Move) :
    ∃u ≤ rewindFactor M-1,(rewindStep M).Exec (store M q s (d::ds)) u
      (store M q (moveOrigin M s d) ds) := by
  have hs : rewindKey M (tops (store M q s (d::ds)))=(d,(s (zeroTape M)).right.headD (TMStack.blank M)) := by
    apply Prod.ext
    · rfl
    · exact congrArg (fun v => (v (zeroTape M))) (congrArg Prod.snd (select_store M q s (d::ds)))
  have he := rewindBody_exec M q s d ds
  change ((fun x : Move × Fin M.symbols => rewindBody M x.1 x.2)
    (d,(s (zeroTape M)).right.headD (TMStack.blank M))).Exec _ _ _ at he
  rw [←hs] at he
  obtain ⟨u,hu,hf⟩ := Code.casesAll_exec (rewindKey M) (fun x => rewindBody M x.1 x.2) he
  refine ⟨u,?_,hf⟩
  have ht : TMStack.tapeCost d.inverse ≤ 8 := by cases d <;> decide
  dsimp [rewindFactor]
  omega
 theorem rewind_exec (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) :
    ∃u ≤ rewindFactor M*ds.length+1,(rewindCode M).Exec (store M q s ds) u
      (store M q (rewindTapes M s ds) []) := by
  induction ds generalizing s with
  | nil => exact ⟨1,by simp,Code.Exec.loop_false rfl⟩
  | cons d ds ih =>
    obtain ⟨a,ha,he⟩ := rewindStep_exec M q s d ds
    obtain ⟨b,hb,hf⟩ := ih (moveOrigin M s d)
    have hp : 1 ≤ rewindFactor M := by dsimp [rewindFactor]; omega
    refine ⟨a+b+1,?_,Code.Exec.loop_true rfl he hf⟩
    simp only [List.length_cons]
    have hh : a+1 ≤ rewindFactor M := by omega
    nlinarith only [hh,hb]
 theorem rewind_contents (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) (z : ℤ) :
    TapePair.contents (TMStack.blank M) (rewindTapes M s ds (zeroTape M)) z=
      TapePair.contents (TMStack.blank M) (s (zeroTape M)) (z-(ds.map Move.displacement).sum) := by
  induction ds generalizing s z with
  | nil => simp only [rewindTapes,List.map_nil,List.sum_nil,sub_zero]
  | cons d ds ih =>
    rw [rewindTapes,ih]
    simp only [moveOrigin,Function.update_self,TapePair.contents_move,Move.inverse_displacement,
      List.map_cons,List.sum_cons]
    congr 1
    omega
 theorem rewind_absolute (C : M.Config) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move)
    (hr : TMStack.Relative M C s) (hh : C.head (zeroTape M)=(ds.map Move.displacement).sum) (z : ℤ) :
    TapePair.contents (TMStack.blank M) (rewindTapes M s ds (zeroTape M)) z=C.tape (zeroTape M) z := by
  rw [rewind_contents,hr,hh]
  congr 1
  omega
end WLTime.TMTransducer

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K]
 theorem takeN_exec (a b : K) (hab : a≠b) (f : A → A) (zero : A) (n : ℕ) (s : Stacks K A) :
    (takeN a b f zero n).Exec s (4*n+1)
      (Function.update (Function.update s a ((s a).drop n)) b
        (((readN zero (s a) n).map f).reverse++s b)) := by
  induction n generalizing s with
  | zero =>
    simpa only [takeN,readN,List.ofFn_zero,List.map_nil,List.reverse_nil,List.nil_append,List.drop_zero,
      Function.update_eq_self] using Exec.skip s
  | succ n ih =>
    let mid := Function.update (Function.update s b (f ((s a).headD zero)::s b)) a (s a).tail
    have hfirst : Exec (.seq (.pushDyn b (fun v => f ((v a).getD zero))) (.pop a)) s 4 mid := by
      have hp := Exec.pushDyn s b (fun v => f ((v a).getD zero))
      have he := Exec.seq hp (Exec.pop _ a)
      have hh : (s a).head?.getD zero=(s a).headD zero := by cases s a <;> rfl
      simpa only [mid,tops,hh,Function.update_of_ne hab] using he
    have he := Exec.seq hfirst (ih mid)
    have hread : readN zero (s a) (n+1)=(s a).headD zero::readN zero (s a).tail n := by
      unfold readN
      rw [List.ofFn_succ]
      apply congrArg₂ List.cons
      · cases s a <;> rfl
      · congr 1
        funext i
        exact (TapePair.getD_tail (s a) i.val zero).symm
    unfold takeN
    convert he using 1
    · omega
    · funext k
      by_cases hb : k=b
      · subst k
        simp [mid,hab.symm,hread,List.reverse_cons,List.append_assoc]
      · by_cases ha : k=a
        · subst k
          simp only [Function.update_self,Function.update_of_ne hb,mid]
          cases s a <;> simp
        · simp [mid,hb,ha]
end WLTime.TypedStack.Code
namespace WLTime.TMTransducer
open TypedStack
variable (M : TM)
 theorem output_prefix (input output : List Bool) (ho : M.outputs input output)
    (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move)
    (hr : TMStack.Relative M (M.run input (M.time input)) s)
    (hh : (M.run input (M.time input)).head (zeroTape M)=(ds.map Move.displacement).sum) :
    Code.readN (TMStack.blank M) (rewindTapes M s ds (zeroTape M)).right output.length=output.map M.symbol := by
  apply List.ext_getElem
  · simp [Code.readN]
  · intro i hi hj
    have hit : i<output.length := by simpa [Code.readN] using hi
    have h := rewind_absolute M _ s ds hr hh (i : ℤ)
    have ho' := ho.2 ⟨i,hit⟩
    simpa only [Code.readN,List.getElem_ofFn,List.getElem_map,TapePair.contents,
      not_lt.mpr (Int.natCast_nonneg i),ite_false,Int.toNat_natCast,List.get_eq_getElem] using h.trans ho'
end WLTime.TMTransducer

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K] [Fintype K]
 theorem mass_update (s : Stacks K A) (k : K) (xs : List A) :
    mass (Function.update s k xs)+(s k).length=mass s+xs.length := by
  unfold mass
  have he : (fun j => (Function.update s k xs j).length)=Function.update (fun j => (s j).length) k xs.length := by
    funext j
    by_cases h : j=k <;> simp [h]
  rw [he,Finset.sum_update_of_mem (Finset.mem_univ k),Finset.sdiff_singleton_eq_erase]
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  omega
 theorem mass_exec {c : Code K A} {s : Stacks K A} {t : ℕ} {out : Stacks K A} (h : c.Exec s t out) :
    mass out≤ mass s+t := by
  induction h with
  | skip => omega
  | push s k x => have h := mass_update s k (x::s k); simp only [List.length_cons] at h; omega
  | pushDyn s k f => have h := mass_update s k (f (tops s)::s k); simp only [List.length_cons] at h; omega
  | pop s k => have h := mass_update s k (s k).tail; simp only [List.length_tail] at h; omega
  | seq _ _ ih ih' => omega
  | branch_true _ _ ih => omega
  | branch_false _ _ ih => omega
  | loop_false => omega
  | loop_true _ _ _ ih ih' => omega

 omit [Fintype K] in
 theorem clearList_exec (ks : List K) (s : Stacks K A) (hk : ks.Nodup) :
    (clearList ks).Exec s (3*(ks.map (fun k => (s k).length)).sum+ks.length+1) (cleared ks s) := by
  induction ks generalizing s with
  | nil =>
    have hz : cleared ([] : List K) s=s := by funext k; simp [cleared]
    rw [hz]
    simpa [clearList] using Exec.skip s
  | cons k ks ih =>
    obtain ⟨hn,hd⟩ := List.nodup_cons.mp hk
    have he := Exec.seq (clear_exec k s) (ih (Function.update s k []) hd)
    have hsum : (ks.map (fun j => (Function.update s k [] j).length)).sum=(ks.map (fun j => (s j).length)).sum := by
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [Function.update_of_ne (by intro h; subst j; exact hn hj)]
    have hout : cleared ks (Function.update s k [])=cleared (k::ks) s := by
      funext j
      by_cases h : j=k <;> by_cases hh : j∈ks <;> simp [cleared,h,hh]
    rw [hsum,hout] at he
    convert he using 1 <;> try rfl
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega
 theorem clearList_cost (ks : List K) (s : Stacks K A) (hk : ks.Nodup) :
    (ks.map (fun k => (s k).length)).sum≤ mass s := by
  rw [←List.sum_toFinset _ hk]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
end WLTime.TypedStack.Code

end OAI
end

section
-- module Solutions.OAIQW_WLTime.SparseSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA

namespace WLTime.BitWords
 theorem value_ofFn {w : ℕ} (f : Fin w → Bool) : value (List.ofFn f)=Nat.ofBits f := by
  induction w with
  | zero => simp [value]
  | succ w ih =>
    rw [List.ofFn_succ,value_cons,Nat.ofBits_succ,ih]
    dsimp only [Function.comp_def]
    omega
 theorem value_lt (xs : List Bool) : value xs<2^xs.length := by
  rw [←List.ofFn_get xs,value_ofFn]
  simpa only [List.length_ofFn] using Nat.ofBits_lt_two_pow xs.get
 theorem value_word {w : ℕ} (a : Word w) : value (wordBits a)=a.val := by
  rw [wordBits,value_ofFn,Nat.ofBits_testBit,Nat.mod_eq_of_lt a.isLt]
 theorem testBit_value (xs : List Bool) (i : ℕ) : (value xs).testBit i=xs.getD i false := by
  rw [←List.ofFn_get xs,value_ofFn,Nat.testBit_ofBits]
  simp only [List.ofFn_get]
  split_ifs with h
  · change xs[i]=xs.getD i false
    exact (List.getD_eq_getElem _ _ h).symm
  · exact (List.getD_eq_default xs false (Nat.le_of_not_gt h)).symm
 theorem inc_value (xs : List Bool) : value (inc xs)=(value xs+1)%2^xs.length := by
  induction xs with
  | nil => simp [inc]
  | cons b xs ih =>
    cases b
    · have hx := value_lt xs
      simp only [inc,value_cons,Bool.toNat_false,Bool.toNat_true,List.length_cons,pow_succ]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [inc,value_cons,Bool.toNat_false,Bool.toNat_true,List.length_cons,pow_succ,ih,zero_add]
      have he : 1+2*value xs+1=2*(value xs+1) := by omega
      rw [he,Nat.mul_comm (2^xs.length) 2,Nat.mul_mod_mul_left]
 theorem word_injective {w : ℕ} : Function.Injective (wordBits (w:=w)) := by
  intro a b h
  apply Fin.ext
  simpa only [value_word] using congrArg value h
end WLTime.BitWords

namespace WLTime.BitWords
 theorem carry_le (xs : List Bool) : carry xs≤xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [carry]; omega
 theorem inc_decompose (xs : List Bool) : inc xs=List.replicate (carry xs) false++raise (rest xs) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [inc,carry,rest,raise,ih,List.replicate_succ]
end WLTime.BitWords
namespace WLTime.TypedStack.Code
open BitWords
variable {K : Type uK} [DecidableEq K]
 theorem carryCode_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (carryCode a b).Exec s (5*carry (s a)+1)
      (Function.update (Function.update s a (rest (s a))) b (List.replicate (carry (s a)) false++s b)) := by
  generalize hx : s a=xs
  induction xs generalizing s with
  | nil =>
    have hout : Function.update (Function.update s a (rest [])) b (List.replicate (carry []) false++s b)=s := by
      simp only [rest,carry,List.replicate_zero,List.nil_append]
      rw [←hx,Function.update_eq_self,Function.update_eq_self]
    rw [hout]
    exact .loop_false (by simp [tops,hx])
  | cons x xs ih =>
    cases x
    · have hout : Function.update (Function.update s a (rest (false::xs))) b (List.replicate (carry (false::xs)) false++s b)=s := by
        simp only [rest,carry,List.replicate_zero,List.nil_append]
        rw [←hx,Function.update_eq_self,Function.update_eq_self]
      rw [hout]
      exact .loop_false (by simp [tops,hx])
    · let mid := Function.update (Function.update s a xs) b (false::s b)
      have hb : (Code.seq (.pop a) (.push b false)).Exec s 4 mid := by
        simpa only [hx,List.tail_cons,Function.update_of_ne hab.symm,mid] using
          Exec.seq (Exec.pop s a) (Exec.push (Function.update s a (s a).tail) b false)
      have hs : mid a=xs := by simp [mid,hab]
      have hh := ih mid hs
      have hout : Function.update (Function.update mid a (rest xs)) b (List.replicate (carry xs) false++mid b)=
          Function.update (Function.update s a (rest (true::xs))) b (List.replicate (carry (true::xs)) false++s b) := by
        funext k
        by_cases hk : k=b
        · subst k
          simp only [Function.update_self,mid,carry]
          rw [List.replicate_succ']
          simp only [List.append_assoc,List.singleton_append]
        · by_cases ha : k=a
          · subst k; simp [mid,hk,rest]
          · simp [mid,hk,ha]
      rw [hout] at hh
      have he := Exec.loop_true (p:=fun v : Tops K Bool => v a==some true) (by simp [tops,hx]) hb hh
      convert he using 1
      · rfl
      · simp [carry]; omega
 theorem raiseCode_exec (a : K) (s : Stacks K Bool) :
    ∃u≤5,(raiseCode a).Exec s u (Function.update s a (raise (s a))) := by
  cases hx : s a with
  | nil =>
    refine ⟨2,by omega,?_⟩
    have ht : Function.update s a (raise (s a))=s := by rw [hx]; change Function.update s a []=s; rw [←hx]; exact Function.update_eq_self _ _
    rw [hx] at ht
    rw [ht]
    exact Exec.branch_false (by simp [nonempty,tops,hx]) (Exec.skip s)
  | cons b xs =>
    have he := Exec.seq (Exec.pop s a) (Exec.push (Function.update s a (s a).tail) a true)
    have hf := Exec.branch_true (b:=.skip) (p:=nonempty a) (by simp [nonempty,tops,hx]) he
    refine ⟨5,by omega,?_⟩
    simpa only [raiseCode,hx,List.tail_cons,Function.update_self,Function.update_idem,raise] using hf
 theorem increment_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) (hb : s b=[]) :
    ∃u≤10*(s a).length+7,(increment a b).Exec s u (Function.update s a (inc (s a))) := by
  let mid := Function.update (Function.update s a (rest (s a))) b (List.replicate (carry (s a)) false)
  have hc : (carryCode a b).Exec s (5*carry (s a)+1) mid := by simpa only [hb,List.append_nil] using carryCode_exec a b hab s
  obtain ⟨u,hu,he⟩ := raiseCode_exec a mid
  have ht := transfer_exec b a hab.symm false (Function.update mid a (raise (mid a)))
  have hf := Exec.seq hc (Exec.seq he ht)
  have hout : Function.update (Function.update (Function.update mid a (raise (mid a))) b []) a
      (((Function.update mid a (raise (mid a))) b).reverse++(Function.update mid a (raise (mid a))) a)=
      Function.update s a (inc (s a)) := by
    funext k
    by_cases ha : k=a
    · subst k
      simp [mid,hab,hab.symm,inc_decompose]
    · by_cases hkb : k=b
      · subst k; simp [mid,ha,hb]
      · simp [mid,ha,hkb]
  rw [hout] at hf
  refine ⟨_,?_,hf⟩
  simp only [mid,Function.update_of_ne hab.symm,Function.update_self,List.length_replicate]
  have h := carry_le (s a)
  omega
end WLTime.TypedStack.Code

namespace WLTime.SparseMatch
open TypedStack
 theorem body_exec (x y q : Bool) (xs ys fs hs : List Bool) :
    body.Exec (state (x::xs) (y::ys) (q::fs) hs) 8
      (state xs ys ((q&&(x==y))::q::fs) (x::hs)) := by
  let s := state (x::xs) (y::ys) (q::fs) hs
  let s₁ := Function.update s 2 ((q&&(x==y))::q::fs)
  let s₂ := Function.update s₁ 3 (x::hs)
  let s₃ := Function.update s₂ 0 xs
  have h₁ : (Code.pushDyn 2 (fun v : Tops Reg Bool => (v 2).getD false && ((v 0).getD false == (v 1).getD false))).Exec s 2 s₁ := by
    simpa [s,s₁,state,tops] using Code.Exec.pushDyn s 2 (fun v => (v 2).getD false && ((v 0).getD false == (v 1).getD false))
  have h₂ : (Code.pushDyn 3 (fun v : Tops Reg Bool => (v 0).getD false)).Exec s₁ 2 s₂ := by
    simpa [s₂,s₁,s,state,tops] using Code.Exec.pushDyn s₁ 3 (fun v => (v 0).getD false)
  have h₃ : (Code.pop 0).Exec s₂ 2 s₃ := by simpa [s₃,s₂,s₁,s,state] using Code.Exec.pop s₂ 0
  have h₄ : (Code.pop 1).Exec s₃ 2 (state xs ys ((q&&(x==y))::q::fs) (x::hs)) := by
    have he := Code.Exec.pop s₃ 1
    convert he using 1
    funext i; fin_cases i <;> simp [s₃,s₂,s₁,s,state]
  exact Code.Exec.seq h₁ (Code.Exec.seq h₂ (Code.Exec.seq h₃ h₄))
 theorem program_exec (xs ys tail fs hs : List Bool) (q : Bool) (hlen : ys.length=xs.length) :
    ∃gs, gs.length=xs.length+fs.length+1 ∧ gs.headD false=(q && (xs==ys)) ∧
      (program xs.length).Exec (state (xs++tail) ys (q::fs) hs) (8*xs.length+1)
        (state tail [] gs (xs.reverse++hs)) := by
  induction xs generalizing ys fs hs q with
  | nil =>
    have hy : ys=[] := List.eq_nil_of_length_eq_zero hlen
    subst ys
    exact ⟨q::fs,by simp,by simp,by simpa [program,state] using Code.Exec.skip (state tail [] (q::fs) hs)⟩
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hy : ys.length=xs.length := by simpa using hlen
      obtain ⟨gs,hg,hhead,he⟩ := ih ys (q::fs) (x::hs) (q&&(x==y)) hy
      refine ⟨gs,by simp only [List.length_cons] at hg ⊢; omega,?_,?_⟩
      · rw [hhead]
        simp only [List.cons_beq_cons]
        cases q <;> cases hxy : (x==y) <;> simp
      · have h := Code.Exec.seq (body_exec x y q (xs++tail) ys fs hs) he
        simpa only [program,List.length_cons,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
end WLTime.SparseMatch
namespace WLTime.SparseTake
open TypedStack
 theorem body_exec (x : Bool) (xs bs cs : List Bool) :
    body.Exec (state (x::xs) bs cs) 6 (state xs (x::bs) (x::cs)) := by
  let s := state (x::xs) bs cs
  let s₁ := Function.update s 1 (x::bs)
  let s₂ := Function.update s₁ 2 (x::cs)
  have he₁ : (Code.pushDyn 1 (fun v : Tops Reg Bool => (v 0).getD false)).Exec s 2 s₁ := by
    simpa [s₁,s,state,tops] using Code.Exec.pushDyn s 1 (fun v => (v 0).getD false)
  have he₂ : (Code.pushDyn 2 (fun v : Tops Reg Bool => (v 0).getD false)).Exec s₁ 2 s₂ := by
    simpa [s₂,s₁,s,state,tops] using Code.Exec.pushDyn s₁ 2 (fun v => (v 0).getD false)
  have he₃ : (Code.pop 0).Exec s₂ 2 (state xs (x::bs) (x::cs)) := by
    have he := Code.Exec.pop s₂ 0
    convert he using 1
    funext i; fin_cases i <;> simp [s₂,s₁,s,state]
  exact Code.Exec.seq he₁ (Code.Exec.seq he₂ he₃)
 theorem program_exec (xs tail bs cs : List Bool) :
    (program xs.length).Exec (state (xs++tail) bs cs) (6*xs.length+1)
      (state tail (xs.reverse++bs) (xs.reverse++cs)) := by
  induction xs generalizing bs cs with
  | nil => simpa [program,state] using Code.Exec.skip (state tail bs cs)
  | cons x xs ih =>
    have he := Code.Exec.seq (body_exec x (xs++tail) bs cs) (ih (x::bs) (x::cs))
    simpa only [program,List.length_cons,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he
end WLTime.SparseTake

namespace WLTime.SparseLookup
open TypedStack
 theorem matchMap_inj : Function.Injective matchMap := by decide
 theorem takeMap_inj : Function.Injective takeMap := by decide
 theorem first_exec (key value query tail hist : List Bool)
    (hk : key.length=query.length) (hv : value.length=query.length) :
    ∃fs, fs.length=query.length+1 ∧ fs.headD false=(key==query) ∧
      (first query.length).Exec (state (key++value++tail) query [] hist [] [] [] [])
        (26*query.length+6)
        (state tail query [] (value.reverse++key.reverse++hist) [] fs value.reverse []) := by
  let s₀ := state (key++value++tail) query [] hist [] [] [] []
  let s₁ := state (key++value++tail) query [] hist query [] [] []
  let s₂ := state (key++value++tail) query [] hist query [true] [] []
  have h₁ : (Code.copy 1 4 7 false).Exec s₀ (12*query.length+2) s₁ := by
    have h := Code.copy_exec (1 : Reg) 4 7 (by decide) (by decide) (by decide) false s₀ rfl
    convert h using 1
    · rfl
    · funext i; fin_cases i <;> simp [s₁,s₀,state]
  have h₂ : (Code.push 5 true).Exec s₁ 2 s₂ := by
    have h := Code.Exec.push s₁ 5 true
    convert h using 1
    funext i; fin_cases i <;> simp [s₂,s₁,state]
  obtain ⟨fs,hlen,hhead,hm⟩ := SparseMatch.program_exec key query (value++tail) [] hist true hk.symm
  have h₃ : ((SparseMatch.program query.length).relabel matchMap).Exec s₂ (8*query.length+1)
      (state (value++tail) query [] (key.reverse++hist) [] fs [] []) := by
    rw [hk] at hm
    apply Code.relabel_exec_of_maps matchMap matchMap_inj hm
    · intro i; fin_cases i <;> simp [s₂,state,SparseMatch.state,matchMap,List.append_assoc]
    · intro i; fin_cases i <;> simp [state,SparseMatch.state,matchMap]
    · intro i hi; fin_cases i <;> simp_all [state,s₂,matchMap]
      <;> first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl) | exact False.elim (hi 3 rfl)
  have h₄ : ((SparseTake.program query.length).relabel takeMap).Exec
      (state (value++tail) query [] (key.reverse++hist) [] fs [] []) (6*query.length+1)
      (state tail query [] (value.reverse++key.reverse++hist) [] fs value.reverse []) := by
    have ht := SparseTake.program_exec value tail (key.reverse++hist) []
    rw [hv] at ht
    apply Code.relabel_exec_of_maps takeMap takeMap_inj ht
    · intro i; fin_cases i <;> simp [state,SparseTake.state,takeMap]
    · intro i; fin_cases i <;> simp [state,SparseTake.state,takeMap,List.append_assoc]
    · intro i hi; fin_cases i <;> simp_all [state,takeMap]
      <;> first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl)
  refine ⟨fs,by simpa [hk] using hlen,by simpa using hhead,?_⟩
  have he := Code.Exec.seq h₁ (Code.Exec.seq h₂ (Code.Exec.seq h₃ h₄))
  convert he using 1
  · rfl
  · omega
 theorem finish_exec (tail query hist fs value : List Bool) :
    ∃u ≤ 5*value.length+3*fs.length+3,
      finish.Exec (state tail query [] hist [] fs value.reverse []) u
        (state tail query (if fs.headD false then value else []) hist [] [] [] []) := by
  let s := state tail query [] hist [] fs value.reverse []
  let out := if fs.headD false then value else []
  let mid := state tail query out hist [] fs [] []
  have hb : ∃u ≤ 5*value.length+2,
      (Code.branch (fun v : Tops Reg Bool => (v 5).getD false) (.transfer 6 2 false) (.clear 6)).Exec s u mid := by
    cases hh : fs.headD false
    · have he := Code.clear_exec (6 : Reg) s
      have ho : out=[] := ite_eq_right (by rw [hh]; decide)
      have hm : Function.update s 6 []=mid := by
        funext i; fin_cases i <;> simp [s,mid,state,ho]
      rw [hm] at he
      refine ⟨_,?_,Code.Exec.branch_false (by simpa [tops,s,state] using hh) he⟩
      simp [s,state]; omega
    · have he := Code.transfer_exec (6 : Reg) 2 (by decide) false s
      have ho : out=value := ite_eq_left hh
      have hm : Function.update (Function.update s 6 []) 2 ((s 6).reverse++s 2)=mid := by
        funext i; fin_cases i <;> simp [s,mid,state,ho]
      rw [hm] at he
      refine ⟨_,?_,Code.Exec.branch_true (by simpa [tops,s,state] using hh) he⟩
      simp [s,state]
  obtain ⟨u,hu,he⟩ := hb
  have hc := Code.clear_exec (5 : Reg) mid
  have hf : Function.update mid 5 []=state tail query out hist [] [] [] [] := by
    funext i; fin_cases i <;> simp [mid,state]
  rw [hf] at hc
  refine ⟨_,?_,Code.Exec.seq he hc⟩
  change u+(3*fs.length+1) ≤ _
  omega
 theorem one_exec (key value query tail hist : List Bool)
    (hk : key.length=query.length) (hv : value.length=query.length) :
    ∃u ≤ 40*(query.length+1),
      (one query.length).Exec (state (key++value++tail) query [] hist [] [] [] []) u
        (state tail query (if key=query then value else []) (value.reverse++key.reverse++hist) [] [] [] []) := by
  obtain ⟨fs,hf,hh,he⟩ := first_exec key value query tail hist hk hv
  obtain ⟨u,hu,hg⟩ := finish_exec tail query (value.reverse++key.reverse++hist) fs value
  rw [hh] at hg
  simp only [beq_iff_eq] at hg
  refine ⟨_,?_,Code.Exec.seq he hg⟩
  rw [hf,hv] at hu
  omega
end WLTime.SparseLookup
namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K]
 theorem pushList_exec (k : K) (xs : List A) (s : Stacks K A) :
    (pushList k xs).Exec s (2*xs.length+1) (Function.update s k (xs++s k)) := by
  induction xs with
  | nil => simpa [pushList] using Exec.skip s
  | cons x xs ih =>
    have he := Exec.seq ih (Exec.push (Function.update s k (xs++s k)) k x)
    simpa only [pushList,List.length_cons,List.cons_append,Function.update_self,Function.update_idem,
      Nat.mul_add,Nat.mul_one,Nat.add_assoc] using he
end WLTime.TypedStack.Code
namespace WLTime.SparseLookup
open TypedStack
 theorem split_log (q : List Bool) (l : List Entry) : consumed q l++remaining q l=l := by
  induction l with
  | nil => rfl
  | cons e l ih => by_cases he : e.1=q <;> simp [consumed,remaining,he,ih]
 theorem flatten_append (l m : List Entry) : flatten (l++m)=flatten l++flatten m := by simp [flatten]
 theorem flatten_length (w : ℕ) (l : List Entry) (hw : WellFormed w l) : (flatten l).length=2*w*l.length := by
  induction l with
  | nil => simp [flatten]
  | cons e l ih =>
    have he := hw e (by simp)
    have hl : WellFormed w l := fun a ha => hw a (by simp [ha])
    have hh := ih hl
    simp only [flatten,List.flatMap_cons,List.length_append,List.length_cons] at *
    rw [he.1,he.2,hh]
    ring
 theorem consumed_length (q : List Bool) (l : List Entry) : (flatten (consumed q l)).length ≤ (flatten l).length := by
  have hh := congrArg (fun l => (flatten l).length) (split_log q l)
  rw [flatten_append,List.length_append] at hh
  omega
 theorem search_exec (q : List Bool) (l : List Entry) (hist : List Bool) (hq : 0<q.length) (hw : WellFormed q.length l) :
    ∃u ≤ 42*(q.length+1)*l.length+1,
      (search q.length).Exec (state (flatten l) q [] hist [] [] [] []) u
        (state (flatten (remaining q l)) q (found q l) ((flatten (consumed q l)).reverse++hist) [] [] [] []) := by
  induction l generalizing hist with
  | nil =>
    refine ⟨1,by simp,?_⟩
    have he : (search q.length).Exec (state [] q [] hist [] [] [] []) 1 (state [] q [] hist [] [] [] []) :=
      Code.Exec.loop_false (by simp [keepGoing,Code.nonempty,tops,state])
    simpa [flatten,consumed,remaining,found] using he
  | cons e l ih =>
    have he := hw e (by simp)
    have hl : WellFormed q.length l := fun a ha => hw a (by simp [ha])
    have hkne : e.1≠[] := by
      intro h
      have hh := he.1
      rw [h,List.length_nil] at hh
      omega
    obtain ⟨a,ha,hstep⟩ := one_exec e.1 e.2 q (flatten l) hist he.1 he.2
    by_cases h : e.1=q
    · have hval : e.2≠[] := by intro hh; rw [hh,List.length_nil] at he; omega
      simp only [ite_eq_left h] at hstep
      have hstop : (search q.length).Exec
          (state (flatten l) q e.2 (e.2.reverse++e.1.reverse++hist) [] [] [] []) 1
          (state (flatten l) q e.2 (e.2.reverse++e.1.reverse++hist) [] [] [] []) :=
        Code.Exec.loop_false (by simp [keepGoing,Code.nonempty,tops,state,hval])
      have hex := Code.Exec.loop_true (p:=keepGoing) (by simp [keepGoing,Code.nonempty,tops,state,hkne]) hstep hstop
      refine ⟨a+1+1,?_,?_⟩
      · simp only [List.length_cons]; nlinarith
      · simpa only [search,flatten,List.flatMap_cons,consumed,remaining,found,ite_eq_left h,List.flatMap_nil,List.append_nil,
          List.reverse_append,List.append_assoc] using hex
    · simp only [ite_eq_right h] at hstep
      obtain ⟨b,hb,hrest⟩ := ih (e.2.reverse++e.1.reverse++hist) hl
      have hex := Code.Exec.loop_true (p:=keepGoing) (by simp [keepGoing,Code.nonempty,tops,state,hkne]) hstep hrest
      refine ⟨a+b+1,?_,?_⟩
      · simp only [List.length_cons]; nlinarith
      · simpa only [search,flatten,List.flatMap_cons,consumed,remaining,found,ite_eq_right h,List.reverse_append,List.append_assoc] using hex
end WLTime.SparseLookup

end OAI
end

section
-- module Solutions.OAIQW_WLTime.SparseStore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB

namespace WLTime.SparseLookup
open TypedStack
 theorem supplyZero_exec (w : ℕ) (log q out : List Bool) :
    ∃u ≤ 2*w+2,
      (supplyZero w).Exec (state log q out [] [] [] [] []) u
        (state log q (if out=[] then List.replicate w false else out) [] [] [] [] []) := by
  let s := state log q out [] [] [] [] []
  by_cases ho : out=[]
  · have hp := Code.pushList_exec (2 : Reg) (List.replicate w false) s
    have he := Code.Exec.branch_false (a:=Code.skip) (p:=Code.nonempty 2) (by simp [Code.nonempty,tops,s,state,ho]) hp
    refine ⟨1+(2*w+1),by omega,?_⟩
    have hh : Function.update s 2 (List.replicate w false++s 2)=state log q (if out=[] then List.replicate w false else out) [] [] [] [] [] := by
      funext i; fin_cases i <;> simp [s,state,ho]
    rw [hh] at he
    simpa only [supplyZero,s,List.length_replicate,Nat.add_comm] using he
  · have he := Code.Exec.branch_true (b:=Code.pushList 2 (List.replicate w false)) (p:=Code.nonempty 2)
      (by simp [Code.nonempty,tops,s,state,ho]) (Code.Exec.skip s)
    exact ⟨2,by omega,by simpa only [supplyZero,s,ite_eq_right ho] using he⟩
 theorem program_exec (q : List Bool) (l : List Entry) (hq : 0<q.length) (hw : WellFormed q.length l) :
    ∃u ≤ 60*(q.length+1)*(l.length+1),
      (program q.length).Exec (state (flatten l) q [] [] [] [] [] []) u
        (state (flatten l) q (answer q.length q l) [] [] [] [] []) := by
  obtain ⟨a,ha,he⟩ := search_exec q l [] hq hw
  simp only [List.append_nil] at he
  let mid := state (flatten (remaining q l)) q (found q l) (flatten (consumed q l)).reverse [] [] [] []
  have ht := Code.transfer_exec (3 : Reg) 0 (by decide) false mid
  have hs : Function.update (Function.update mid 3 []) 0 ((mid 3).reverse++mid 0)=
      state (flatten l) q (found q l) [] [] [] [] [] := by
    have hsplit : flatten (consumed q l)++flatten (remaining q l)=flatten l := by rw [←flatten_append,split_log]
    funext i; fin_cases i <;> simp [mid,state,hsplit]
  rw [hs] at ht
  obtain ⟨b,hb,hf⟩ := supplyZero_exec q.length (flatten l) q (found q l)
  refine ⟨_,?_,Code.Exec.seq he (Code.Exec.seq ht hf)⟩
  change a+(5*(flatten (consumed q l)).reverse.length+1+b) ≤ _
  rw [List.length_reverse]
  have hpre := consumed_length q l
  rw [flatten_length q.length l hw] at hpre
  nlinarith
end WLTime.SparseLookup

namespace WLTime.WordMemory
open TypedStack
 theorem entries_wellFormed {w : ℕ} (l : Log w) : SparseLookup.WellFormed w (entries l) := by
  intro e he
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
  simp [wordBits]
 theorem entries_length {w : ℕ} (l : Log w) : (entries l).length=l.length := by simp [entries]
 theorem word_zero (w : ℕ) : wordBits (⟨0,by positivity⟩ : Word w)=List.replicate w false := by
  simp [wordBits,List.ofFn_const]
 theorem answer_read {w : ℕ} (hw : 0<w) (q : Word w) (l : Log w) :
    SparseLookup.answer w (wordBits q) (entries l)=wordBits (read q l) := by
  induction l with
  | nil => simp [SparseLookup.answer,SparseLookup.found,entries,read,wordBits,List.ofFn_const]
  | cons e l ih =>
    by_cases he : e.1=q
    · have hne : wordBits e.2≠[] := by intro h; have hh := congrArg List.length h; simp [wordBits] at hh; omega
      simp [entries,SparseLookup.answer,SparseLookup.found,he,hne,read]
    · have hb : wordBits e.1≠wordBits q := fun h => he (BitWords.word_injective h)
      change SparseLookup.answer w (wordBits q) ((wordBits e.1,wordBits e.2)::entries l)=wordBits (if e.1=q then e.2 else read q l)
      rw [ite_eq_right he]
      unfold SparseLookup.answer
      rw [SparseLookup.found,ite_eq_right hb]
      exact ih
 theorem lookup_exec {w : ℕ} (hw : 0<w) (q : Word w) (l : Log w) :
    ∃u ≤ 60*(w+1)*(l.length+1),
      (SparseLookup.program w).Exec
        (SparseLookup.state (SparseLookup.flatten (entries l)) (wordBits q) [] [] [] [] [] []) u
        (SparseLookup.state (SparseLookup.flatten (entries l)) (wordBits q) (wordBits (read q l)) [] [] [] [] []) := by
  have hq : (wordBits q).length=w := by simp [wordBits]
  have he := SparseLookup.program_exec (wordBits q) (entries l) (by simpa [hq] using hw)
    (by rw [hq]; exact entries_wellFormed l)
  simpa only [hq,entries_length,answer_read hw] using he
 theorem read_prepend {w : ℕ} (l : Log w) (a v : Word w) :
    (fun q => read q ((a,v)::l))=Function.update (fun q => read q l) a v := by
  funext q
  by_cases h : a=q <;> simp [read,h,eq_comm]
end WLTime.WordMemory
namespace WLTime.SparseStore
open TypedStack
 theorem program_exec (log key value : List Bool) :
    program.Exec (state log key value []) (12*(key.length+value.length)+4)
      (state (key++value++log) key value []) := by
  let s := state log key value []
  let mid := state (value++log) key value []
  have h₁ : (Code.copy 2 0 3 false).Exec s (12*value.length+2) mid := by
    have h := Code.copy_exec (2 : Reg) 0 3 (by decide) (by decide) (by decide) false s rfl
    convert h using 1
    · rfl
    · funext i; fin_cases i <;> simp [s,mid,state]
  have h₂ : (Code.copy 1 0 3 false).Exec mid (12*key.length+2) (state (key++value++log) key value []) := by
    have h := Code.copy_exec (1 : Reg) 0 3 (by decide) (by decide) (by decide) false mid rfl
    convert h using 1
    · rfl
    · funext i; fin_cases i <;> simp [mid,state,List.append_assoc]
  have he := Code.Exec.seq h₁ h₂
  convert he using 1
  · rfl
  · omega
end WLTime.SparseStore

namespace WLTime.BitWords
 theorem value_sum (n : ℕ) (f : ℕ → Bool) :
    value (List.ofFn (fun i : Fin n => f i.val))=∑i∈Finset.range n, if f i then 2^i else 0 := by
  induction n generalizing f with
  | zero => simp [value]
  | succ n ih =>
    rw [List.ofFn_succ,value_cons]
    simp only [Fin.val_zero,Fin.val_succ]
    rw [ih (fun i => f (i+1))]
    rw [Finset.sum_range_succ']
    simp only [pow_succ]
    have hsum : (∑i∈Finset.range n,if f (i+1) then 2^i*2 else 0)=
        2*(∑i∈Finset.range n,if f (i+1) then 2^i else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      cases f (i+1) <;> simp [Nat.mul_comm]
    rw [hsum]
    cases f 0 <;> simp [Bool.toNat,Nat.add_comm]
end WLTime.BitWords
namespace WLTime.WordMemory
open TypedStack
 theorem chunk_length (w : ℕ) (input : List Bool) (a : ℕ) : (chunk w input a).length=w := by simp [chunk,Code.readN]
 theorem chunk_value (w : ℕ) (input : List Bool) (a : ℕ) :
    BitWords.value (chunk w input a)=
      ∑i∈Finset.range w,if input.getD (w*a+i) false then 2^i else 0 := by
  unfold chunk Code.readN
  rw [BitWords.value_sum w (fun i => (input.drop (w*a)).getD i false)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [List.getD_eq_getElem?_getD,List.getElem?_drop]
 theorem packed_bits (w : ℕ) (input : List Bool) (a : Word w) :
    wordBits (RAM.packedWord w input a)=chunk w input a.val := by
  have hv := BitWords.value_lt (chunk w input a.val)
  rw [chunk_length] at hv
  have he : (RAM.packedWord w input a).val=BitWords.value (chunk w input a.val) := by
    change _ % (2^w)=_
    rw [←chunk_value,Nat.mod_eq_of_lt hv]
  apply List.ext_getElem
  · simp [wordBits,chunk_length]
  · intro i hi hj
    simp only [wordBits,List.getElem_ofFn,he,BitWords.testBit_value]
    exact List.getD_eq_getElem _ _ hj
 theorem chunk_zero (w : ℕ) (input : List Bool) (a : ℕ) (ha : input.length  ≤  w*a) :
    chunk w input a=List.replicate w false := by
  simp [chunk,Code.readN,List.drop_eq_nil_of_le ha,List.ofFn_const]
end WLTime.WordMemory
namespace WLTime.WordMemory
 theorem address_val (w a : ℕ) (ha : a<2^w) : (address w a).val=a := Nat.mod_eq_of_lt ha
 theorem address_eq (w a : ℕ) (q : Word w) (ha : a<2^w) : address w a=q ↔ a=q.val := by
  rw [Fin.ext_iff,address_val w a ha]
 theorem initialLog_length (w : ℕ) (input : List Bool) (a : ℕ) : (initialLog w input a).length=a := by
  induction a with
  | zero => rfl
  | succ a ih => simp [initialLog,ih]
 theorem read_initialLog (w : ℕ) (input : List Bool) (a : ℕ) (q : Word w) (ha : a ≤ 2^w) :
    read q (initialLog w input a)=if q.val<a then RAM.packedWord w input q else ⟨0,by positivity⟩ := by
  induction a with
  | zero => simp [initialLog,read]
  | succ a ih =>
    have hal : a<2^w := by omega
    have hh := ih (by omega)
    simp only [initialLog,read]
    by_cases he : address w a=q
    · rw [ite_eq_left he,he,ite_eq_left (by have := (address_eq w a q hal).mp he; omega)]
    · rw [ite_eq_right he,hh]
      have hne : a≠q.val := fun h => he ((address_eq w a q hal).mpr h)
      have heq : (q.val<a) ↔ (q.val<a+1) := by omega
      simp only [heq]
 theorem initialLog_correct (w : ℕ) (input : List Bool) (a : ℕ) (ha : a ≤ 2^w) (hl : input.length ≤ w*a) :
    (fun q => read q (initialLog w input a))=RAM.packedWord w input := by
  funext q
  rw [read_initialLog w input a q ha]
  split_ifs with hq
  · rfl
  · apply BitWords.word_injective
    rw [word_zero,packed_bits,chunk_zero w input q.val (hl.trans (Nat.mul_le_mul_left w (by omega)))]
 theorem number_of_chunks (w : ℕ) (hw : 0<w) (input : List Bool) :
    ∃n ≤ input.length, input.length ≤ w*n ∧ ∀ a < n, w*a < input.length := by
  have hex : ∃n,input.length ≤ w*n := ⟨input.length,by nlinarith⟩
  let n := Nat.find hex
  refine ⟨n,Nat.find_min' hex (by nlinarith),Nat.find_spec hex,?_⟩
  intro a ha
  exact Nat.lt_of_not_ge (Nat.find_min hex ha)
end WLTime.WordMemory
namespace WLTime.BitWords
 theorem eq_word {w : ℕ} (xs : List Bool) (a : Word w) (hl : xs.length=w) (hv : value xs=a.val) : xs=wordBits a := by
  apply List.ext_getElem
  · simpa [wordBits] using hl
  · intro i hi hj
    simp only [wordBits,List.getElem_ofFn,←hv,testBit_value]
    exact (List.getD_eq_getElem _ _ hi).symm
 theorem inc_address (w a : ℕ) : inc (wordBits (WordMemory.address w a))=wordBits (WordMemory.address w (a+1)) := by
  apply eq_word
  · simp [wordBits]
  · rw [inc_value,value_word]
    simp only [wordBits,List.length_ofFn,WordMemory.address]
    simp only [Nat.add_mod,Nat.mod_mod]
end WLTime.BitWords

namespace WLTime.RAMInput
open TypedStack WordMemory
theorem storeMap_inj : Function.Injective storeMap := by decide
 theorem body_exec (w : ℕ) (input log addr : List Bool) (ha : addr.length=w) :
    ∃ u ≤ 50*(w+1), (body w).Exec (state input log addr [] [] []) u
      (state (input.drop w) (addr++Code.readN false input w++log) (BitWords.inc addr) [] [] []) := by
  let value := Code.readN false input w
  have hv : value.length=w := by simp [value,Code.readN]
  let s₀ := state input log addr [] [] []
  let s₁ := state (input.drop w) log addr [] value.reverse []
  let s₂ := state (input.drop w) log addr value [] []
  let s₃ := state (input.drop w) (addr++value++log) addr value [] []
  let s₄ := state (input.drop w) (addr++value++log) addr [] [] []
  have h₁ : (Code.takeN 0 4 id false w).Exec s₀ (4*w+1) s₁ := by
    have he := Code.takeN_exec (0 : Reg) 4 (by decide) id false w s₀
    convert he using 1
    funext i; fin_cases i <;> simp [s₀,s₁,state,value]
  have h₂ : (Code.transfer 4 3 false).Exec s₁ (5*w+1) s₂ := by
    have he := Code.transfer_exec (4 : Reg) 3 (by decide) false s₁
    convert he using 1
    · simp [s₁,state,hv]
    · funext i; fin_cases i <;> simp [s₁,s₂,state]
  have h₃ : (SparseStore.program.relabel storeMap).Exec s₂ (24*w+4) s₃ := by
    have he := SparseStore.program_exec log addr value
    have hc : 12*(addr.length+value.length)+4=24*w+4 := by rw [ha,hv]; omega
    rw [hc] at he
    apply Code.relabel_exec_of_maps storeMap storeMap_inj he
    · intro i; fin_cases i <;> simp [s₂,state,storeMap,SparseStore.state]
    · intro i; fin_cases i <;> simp [s₃,state,storeMap,SparseStore.state]
    · intro i hi; fin_cases i <;> simp_all [state,s₂,s₃,storeMap]

      exact False.elim (hi 0 rfl)
  have h₄ : (Code.clear 3).Exec s₃ (3*w+1) s₄ := by
    have he := Code.clear_exec (3 : Reg) s₃
    convert he using 1
    · simp [s₃,state,hv]
    · funext i; fin_cases i <;> simp [s₃,s₄,state]
  obtain ⟨u,hu,he⟩ := Code.increment_exec (2 : Reg) 5 (by decide) s₄ rfl
  have h₅ : (Code.increment 2 5).Exec s₄ u
      (state (input.drop w) (addr++value++log) (BitWords.inc addr) [] [] []) := by
    convert he using 1
    funext i; fin_cases i <;> simp [s₄,state]
  refine ⟨_,?_,Code.Exec.seq h₁ (Code.Exec.seq h₂ (Code.Exec.seq h₃ (Code.Exec.seq h₄ h₅)))⟩
  change u ≤ 10*addr.length+7 at hu
  rw [ha] at hu
  omega

 theorem body_packed (w : ℕ) (input : List Bool) (a : ℕ) (ha : a<2^w) :
    ∃ u ≤ 50*(w+1), (body w).Exec (packedState w input a) u (packedState w input (a+1)) := by
  obtain ⟨u,hu,he⟩ := body_exec w (input.drop (w*a))
    (SparseLookup.flatten (entries (initialLog w input a))) (wordBits (address w a)) (by simp [wordBits])
  refine ⟨u,hu,?_⟩
  convert he using 1 <;> try rfl
  unfold packedState
  rw [BitWords.inc_address]
  have hdrop : (input.drop (w*a)).drop w=input.drop (w*(a+1)) := by simp [List.drop_drop,Nat.mul_add,Nat.add_comm]
  rw [hdrop]
  rw [show initialLog w input (a+1)=(address w a,RAM.packedWord w input (address w a))::initialLog w input a from rfl]
  simp only [entries,SparseLookup.flatten,List.map_cons,List.flatMap_cons]
  rw [packed_bits,address_val w a ha]
  simp only [chunk,List.append_assoc]
 theorem loop_packed (w : ℕ) (input : List Bool) (n : ℕ) (hn : n ≤ 2^w)
    (hfinal : input.length ≤ w*n) (hmin : ∀ a < n, w*a < input.length) (t a : ℕ) (hat : a+t=n) :
    ∃ u ≤ 51*(w+1)*t+1, (loopCode w).Exec (packedState w input a) u (packedState w input n) := by
  induction t generalizing a with
  | zero =>
    have han : a=n := by omega
    subst a
    refine ⟨1,by omega,Code.Exec.loop_false ?_⟩
    simp [running,Code.nonempty,tops,packedState,state,List.drop_eq_nil_of_le hfinal]
  | succ t ih =>
    have han : a<n := by omega
    obtain ⟨u,hu,he⟩ := body_packed w input a (by omega)
    obtain ⟨v,hv,hh⟩ := ih (a+1) (by omega)
    have hp : running (tops (packedState w input a))=true := by
      simpa [running,Code.nonempty,tops,packedState,state,Option.isSome_iff_ne_none] using hmin a han
    refine ⟨_,?_,Code.Exec.loop_true hp he hh⟩
    nlinarith
 theorem program_exec (w : ℕ) (hw : 0<w) (input : List Bool) (hfit : input.length ≤ w*2^w) :
    ∃ n ≤ input.length, (fun q => read q (initialLog w input n))=RAM.packedWord w input ∧
      ∃ u ≤ 60*(w+1)*(input.length+1), (program w).Exec (state input [] [] [] [] []) u
        (state [] (SparseLookup.flatten (entries (initialLog w input n))) [] [] [] []) := by
  obtain ⟨n,hn,hfinal,hmin⟩ := number_of_chunks w hw input
  have hlimit : n ≤ 2^w := by
    by_contra h
    have ht := hmin (2^w) (by omega)
    omega
  refine ⟨n,hn,initialLog_correct w input n hlimit hfinal,?_⟩
  have hinit : (Code.pushList 2 (List.replicate w false)).Exec (state input [] [] [] [] []) (2*w+1) (packedState w input 0) := by
    have he := Code.pushList_exec (2 : Reg) (List.replicate w false) (state input [] [] [] [] [])
    convert he using 1
    · simp
    · funext i; fin_cases i <;> simp [packedState,state,initialLog,entries,SparseLookup.flatten,address,wordBits,List.ofFn_const]
  obtain ⟨u,hu,he⟩ := loop_packed w input n hlimit hfinal hmin n 0 (by omega)
  have hclear : (Code.clear 2).Exec (packedState w input n) (3*w+1)
      (state [] (SparseLookup.flatten (entries (initialLog w input n))) [] [] [] []) := by
    have hh := Code.clear_exec (2 : Reg) (packedState w input n)
    convert hh using 1
    · simp [packedState,state,wordBits]
    · funext i; fin_cases i <;> simp [packedState,state,List.drop_eq_nil_of_le hfinal]
  refine ⟨_,?_,Code.Exec.seq hinit (Code.Exec.seq he hclear)⟩
  nlinarith
end WLTime.RAMInput

namespace WLTime.TypedStack.Code
variable {A : Type uA} {B : Type uB}
 theorem readN_all (z : A) (xs : List A) : readN z xs xs.length=xs := by
  apply List.ext_getElem
  · simp [readN]
  · intro i hi hj
    simp only [readN,List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ hj
 theorem readN_map (z : A) (f : A → B) (xs : List A) (n : ℕ) :
    readN (f z) (xs.map f) n=(readN z xs n).map f := by
  apply List.ext_getElem
  · simp [readN]
  · intro i hi hj
    simp only [readN,List.getElem_ofFn,List.getElem_map]
    exact List.getD_map _ _ _
end WLTime.TypedStack.Code
namespace WLTime.TMPort
open TypedStack
variable (M : TM)
 theorem load_exec (xs : List Bool) : (load M xs.length).Exec (inputState M xs) (9*xs.length+4)
    (innerState M (M.initial xs).state (TMStack.initialTapes M xs) []) := by
  have he := Code.takeN_exec (port M) (temp M) (by simp [port,temp]) (inputSymbol M) (.inl false) xs.length (inputState M xs)
  have hr : Code.readN (.inl false) (inputState M xs (port M)) xs.length=xs.map Sum.inl := by
    rw [inputState,ite_eq_left rfl]
    rw [←List.length_map (f:=Sum.inl) (as:=xs)]
    exact Code.readN_all _ _
  have hm : (xs.map Sum.inl).map (inputSymbol M)=(xs.map M.symbol).map (fun a => Sum.inr (Sum.inl a)) := by
    simp only [List.map_map]; rfl
  rw [hr,hm] at he
  let mid := Function.update (Function.update (inputState M xs) (port M) []) (temp M)
    (((xs.map M.symbol).map (fun a => Sum.inr (Sum.inl a))).reverse)
  have he' : (Code.takeN (port M) (temp M) (inputSymbol M) (.inl false) xs.length).Exec (inputState M xs) (4*xs.length+1) mid := by
    simpa [mid,inputState,port,temp,←List.map_drop] using he
  have ht := Code.transfer_exec (temp M) (tapeIn M) (by simp [temp,tapeIn]) (.inl false) mid
  let after := Function.update (Function.update mid (temp M) []) (tapeIn M) ((mid (temp M)).reverse++mid (tapeIn M))
  have hp := Code.Exec.push after (.inr (TMTransducer.stateReg M)) (.inr (.inr (.inl (M.initial xs).state)))
  have hex := Code.Exec.seq he' (Code.Exec.seq ht hp)
  have hout : Function.update after (.inr (TMTransducer.stateReg M))
      (.inr (.inr (.inl (M.initial xs).state))::after (.inr (TMTransducer.stateReg M)))=
      innerState M (M.initial xs).state (TMStack.initialTapes M xs) [] := by
    funext k
    cases k with
    | inl i => fin_cases i <;> simp [after,mid,inputState,innerState,port,temp,tapeIn,TMTransducer.stateReg]
    | inr k => cases k with
      | inl i => fin_cases i <;> simp [after,mid,inputState,innerState,port,temp,tapeIn,TMTransducer.stateReg,TMTransducer.store,Code.listMap]
      | inr k =>
        rcases k with ⟨a,b⟩
        by_cases ha : a=TMTransducer.zeroTape M
        · subst a
          cases b <;> simp [after,mid,inputState,innerState,port,temp,tapeIn,TMTransducer.stateReg,TMTransducer.store,Code.listMap,TMStack.store,TMStack.initialTapes,TMTransducer.zeroTape,List.map_map,Function.comp_def]
        · have hv : a.val≠0 := fun h => ha (Fin.ext h)
          cases b <;> simp [after,mid,inputState,innerState,port,temp,tapeIn,TMTransducer.stateReg,TMTransducer.store,Code.listMap,TMStack.store,TMStack.initialTapes,hv,TMTransducer.zeroTape,Function.update_apply]
          ; simp_all [Fin.ext_iff]
  rw [hout] at hex
  convert hex using 1
  · rfl
  · simp [mid]; omega
 theorem run_exec (input output : List Bool) (ho : M.outputs input output) :
    ∃u  ≤  TMTransducer.stepFactor M*M.time input+1,∃s ds,
      (runCode M).Exec (innerState M (M.initial input).state (TMStack.initialTapes M input) []) u
        (innerState M (M.run input (M.time input)).state s ds) ∧
      TMStack.Relative M (M.run input (M.time input)) s ∧ ds.length ≤  M.time input ∧
      (M.run input (M.time input)).head (TMTransducer.zeroTape M)=(ds.map Move.displacement).sum := by
  obtain ⟨u,hu,s,ds,he,hr,hlen,hh⟩ := TMTransducer.run_exec M (M.initial input)
    (TMStack.initialTapes M input) [] (M.time input) (TMStack.initial_relative M input)
    (M.time_halted input ho.1)
  refine ⟨u,hu,s,ds,?_,hr,by simpa using hlen,by simpa only [TM.initial,List.map_nil,List.sum_nil,sub_zero,zero_add,TM.run,TMTransducer.zeroTape] using hh⟩
  exact Code.relabel_inr_exec (Code.mapLetters_exec Sum.inr (unletter M) (by intro a; rfl) he) (fun _ : Fin 3 => [])
 theorem rewind_exec (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) :
    ∃u  ≤  TMTransducer.rewindFactor M*ds.length+1,(rewindCode M).Exec (innerState M q s ds) u
      (innerState M q (TMTransducer.rewindTapes M s ds) []) := by
  obtain ⟨u,hu,he⟩ := TMTransducer.rewind_exec M q s ds
  exact ⟨u,hu,Code.relabel_inr_exec (Code.mapLetters_exec Sum.inr (unletter M) (by intro a; rfl) he) (fun _ : Fin 3 => [])⟩
end WLTime.TMPort

end OAI
end

section
-- module Solutions.OAIQW_WLTime.RAMMemory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

namespace WLTime.TMPort
open TypedStack
variable (M : TM)
 theorem output_symbol (b : Bool) : outputSymbol M (.inr (.inl (M.symbol b)))=.inl b := by
  cases b <;> simp [outputSymbol,TM.symbol]
 theorem extract_exec (s : Stacks (Reg M) (Letter M)) (ys : List Bool)
    (hp : s (port M)=[]) (hr : s (result M)=[])
    (hout : Code.readN (.inr (.inl (TMStack.blank M))) (s (tapeIn M)) ys.length=
      ys.map (fun b => .inr (.inl (M.symbol b)))) :
    (extract M ys.length).Exec s (9*ys.length+2)
      (Function.update (Function.update s (tapeIn M) ((s (tapeIn M)).drop ys.length)) (port M) (ys.map Sum.inl)) := by
  have he := Code.takeN_exec (tapeIn M) (result M) (by simp [tapeIn,result]) (outputSymbol M)
    (.inr (.inl (TMStack.blank M))) ys.length s
  have hm : (ys.map (fun b => Sum.inr (Sum.inl (M.symbol b)))).map (outputSymbol M)=ys.map Sum.inl := by
    simp only [List.map_map]
    congr 1
    funext b
    exact output_symbol M b
  rw [hout,hm,hr,List.append_nil] at he
  let mid := Function.update (Function.update s (tapeIn M) ((s (tapeIn M)).drop ys.length)) (result M) (ys.map Sum.inl).reverse
  have ht := Code.transfer_exec (result M) (port M) (by simp [result,port]) (.inl false) mid
  have hh := Code.Exec.seq he ht
  have hf : Function.update (Function.update mid (result M) []) (port M) ((mid (result M)).reverse++mid (port M))=
      Function.update (Function.update s (tapeIn M) ((s (tapeIn M)).drop ys.length)) (port M) (ys.map Sum.inl) := by
    funext k
    by_cases hkp : k=port M
    · subst k; simp [mid,port,result,tapeIn,show s (.inl 0)=[] from hp]
    · by_cases hkr : k=result M
      · subst k; simp [mid,port,result,tapeIn,show s (.inl 2)=[] from hr]
      · simp [mid,hkp,hkr]
  rw [hf] at hh
  convert hh using 1
  · rfl
  · simp [mid]; omega
 theorem extract_inner (input output : List Bool) (ho : M.outputs input output)
    (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move)
    (hr : TMStack.Relative M (M.run input (M.time input)) s)
    (hh : (M.run input (M.time input)).head (TMTransducer.zeroTape M)=(ds.map Move.displacement).sum) :
    Code.readN (.inr (.inl (TMStack.blank M)))
      (innerState M (M.run input (M.time input)).state (TMTransducer.rewindTapes M s ds) [] (tapeIn M)) output.length=
      output.map (fun b => .inr (.inl (M.symbol b))) := by
  have h := TMTransducer.output_prefix M input output ho s ds hr hh
  change Code.readN _ (((TMTransducer.rewindTapes M s ds (TMTransducer.zeroTape M)).right.map Sum.inl).map Sum.inr) _=_
  rw [Code.readN_map,Code.readN_map,h]
  simp only [List.map_map]
  rfl
end WLTime.TMPort
namespace WLTime.TMPort
open TypedStack
open scoped Classical
variable (M : TM)
 theorem input_mass (xs : List Bool) : Code.mass (inputState M xs)=xs.length := by
  unfold Code.mass inputState
  rw [Finset.sum_eq_single (port M)]
  · simp
  · intro b hb hne; simp [hne]
  · simp
 theorem private_nodup : (privateRegs M).Nodup := by
  exact (Finset.nodup_toList (Finset.univ : Finset (TMTransducer.Reg M))).map Sum.inr_injective
 theorem private_mem (k : Reg M) : k∈privateRegs M ↔ ∃r,k=Sum.inr r := by
  simp [privateRegs,eq_comm]
 theorem cleanup (q : Fin M.states) (s : Fin M.tapes → TapePair.Tape (Fin M.symbols)) (ds : List Move) (ys : List Bool) :
    Code.cleared (privateRegs M)
      (Function.update (Function.update (innerState M q s ds) (tapeIn M)
        ((innerState M q s ds (tapeIn M)).drop ys.length)) (port M) (ys.map Sum.inl))=inputState M ys := by
  funext k
  cases k with
  | inl i =>
    have hn : (Sum.inl i : Reg M)∉privateRegs M := by rw [private_mem]; simp
    simp only [Code.cleared,ite_eq_right hn,inputState]
    by_cases h : (Sum.inl i : Reg M)=port M
    · rw [ite_eq_left h,h,Function.update_self]
    · rw [ite_eq_right h,Function.update_of_ne h,Function.update_of_ne (show (Sum.inl i : Reg M)≠tapeIn M from Sum.inl_ne_inr)]
      rfl
  | inr r =>
    have hn : (Sum.inr r : Reg M)∈privateRegs M := by rw [private_mem]; exact ⟨r,rfl⟩
    simp only [Code.cleared,ite_eq_left hn,inputState,port,Sum.inr_ne_inl,ite_false]
 theorem program_exec (input output : List Bool) (ho : M.outputs input output) :
    ∃u ≤ factor M*(input.length+M.time input+output.length+1),
      (program M input.length output.length).Exec (inputState M input) u (inputState M output) := by
  have hl := load_exec M input
  obtain ⟨a,ha,s,ds,he,hr,hd,hh⟩ := run_exec M input output ho
  obtain ⟨b,hb,hf⟩ := rewind_exec M (M.run input (M.time input)).state s ds
  let z := innerState M (M.run input (M.time input)).state (TMTransducer.rewindTapes M s ds) []
  have hg := extract_exec M z output rfl rfl (extract_inner M input output ho s ds hr hh)
  let out := Function.update (Function.update z (tapeIn M) ((z (tapeIn M)).drop output.length)) (port M) (output.map Sum.inl)
  have hpre := Code.Exec.seq hl (Code.Exec.seq he (Code.Exec.seq hf hg))
  have hmass := Code.mass_exec hpre
  rw [input_mass] at hmass
  have hs := Code.clearList_cost (privateRegs M) out (private_nodup M)
  have hc := Code.clearList_exec (privateRegs M) out (private_nodup M)
  rw [cleanup] at hc
  have hfull := Code.Exec.seq hl (Code.Exec.seq he (Code.Exec.seq hf (Code.Exec.seq hg hc)))
  refine ⟨_,?_,hfull⟩
  have hlen : (privateRegs M).length=Fintype.card (TMTransducer.Reg M) := by simp [privateRegs]
  rw [hlen]
  have hbb := (Nat.mul_le_mul_left (TMTransducer.rewindFactor M) hd)
  have hbound : a+b ≤ (TMTransducer.stepFactor M+TMTransducer.rewindFactor M)*M.time input+2 := by nlinarith only [ha,hb,hbb]
  change Code.mass out ≤ input.length+(9*input.length+4+(a+(b+(9*output.length+2)))) at hmass
  dsimp only [factor]
  nlinarith only [hmass,hs,hbound,Nat.zero_le ((TMTransducer.stepFactor M+TMTransducer.rewindFactor M)*(input.length+output.length+1)),
    Nat.zero_le (Fintype.card (TMTransducer.Reg M)*(input.length+M.time input+output.length))]
end WLTime.TMPort

namespace WLTime.TypedStack.Code
variable {A : Type uA}
theorem readN_prefix (z : A) (xs tail : List A) : readN z (xs++tail) xs.length=xs := by
  apply List.ext_getElem
  · simp [readN]
  · intro i hi hj
    simp only [readN,List.getElem_ofFn,List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hj,List.getElem?_eq_getElem hj]
    rfl
end WLTime.TypedStack.Code
namespace WLTime.RAMSlices
open TypedStack
 theorem read_exec (pre value post : List Bool) :
    ∃ u ≤ 60*((pre++value++post).length+1),
      (read pre.length value.length).Exec (state (pre++value++post) [] [] []) u
        (state (pre++value++post) value [] []) := by
  let file := pre++value++post
  let s₀ := state file [] [] []
  let s₁ := state file [] file []
  let s₂ := state file [] (value++post) pre.reverse
  let s₃ := state file [] (value++post) []
  let s₄ := state file [] post value.reverse
  let s₅ := state file [] [] value.reverse
  have h₁ : (Code.copy 0 2 3 false).Exec s₀ (12*file.length+2) s₁ := by
    have he := Code.copy_exec (0 : Reg) 2 3 (by decide) (by decide) (by decide) false s₀ rfl
    convert he using 1 <;> try rfl
    funext i; fin_cases i <;> simp [s₀,s₁,state]
  have h₂ : (Code.takeN 2 3 id false pre.length).Exec s₁ (4*pre.length+1) s₂ := by
    have he := Code.takeN_exec (2 : Reg) 3 (by decide) id false pre.length s₁
    convert he using 1
    funext i; fin_cases i <;> simp [s₁,s₂,state,file,List.append_assoc,Code.readN_prefix]
  have h₃ : (Code.clear 3).Exec s₂ (3*pre.length+1) s₃ := by
    have he := Code.clear_exec (3 : Reg) s₂
    convert he using 1
    · simp [s₂,state]
    · funext i; fin_cases i <;> simp [s₂,s₃,state]
  have h₄ : (Code.takeN 2 3 id false value.length).Exec s₃ (4*value.length+1) s₄ := by
    have he := Code.takeN_exec (2 : Reg) 3 (by decide) id false value.length s₃
    convert he using 1
    funext i; fin_cases i <;> simp [s₃,s₄,state,Code.readN_prefix]
  have h₅ : (Code.clear 2).Exec s₄ (3*post.length+1) s₅ := by
    have he := Code.clear_exec (2 : Reg) s₄
    convert he using 1
    · rfl
    · funext i; fin_cases i <;> simp [s₄,s₅,state]
  have h₆ : (Code.transfer 3 1 false).Exec s₅ (5*value.length+1) (state file value [] []) := by
    have he := Code.transfer_exec (3 : Reg) 1 (by decide) false s₅
    convert he using 1
    · simp [s₅,state]
    · funext i; fin_cases i <;> simp [s₅,state]
  refine ⟨_,?_,Code.Exec.seq h₁ (Code.Exec.seq h₂ (Code.Exec.seq h₃ (Code.Exec.seq h₄ (Code.Exec.seq h₅ h₆))))⟩
  simp only [file,List.length_append]
  omega
 theorem write_exec (pre old post value : List Bool) (hlen : value.length=old.length) :
    ∃ u ≤ 30*((pre++old++post).length+1),
      (write pre.length old.length).Exec (state (pre++old++post) value [] []) u
        (state (pre++value++post) [] [] []) := by
  let s₀ := state (pre++old++post) value [] []
  let s₁ := state (old++post) value pre.reverse []
  let s₂ := state post value pre.reverse old.reverse
  let s₃ := state post value pre.reverse []
  let s₄ := state (value++post) [] pre.reverse []
  have h₁ : (Code.takeN 0 2 id false pre.length).Exec s₀ (4*pre.length+1) s₁ := by
    have he := Code.takeN_exec (0 : Reg) 2 (by decide) id false pre.length s₀
    convert he using 1
    funext i; fin_cases i <;> simp [s₀,s₁,state,List.append_assoc,Code.readN_prefix]
  have h₂ : (Code.takeN 0 3 id false old.length).Exec s₁ (4*old.length+1) s₂ := by
    have he := Code.takeN_exec (0 : Reg) 3 (by decide) id false old.length s₁
    convert he using 1
    funext i; fin_cases i <;> simp [s₁,s₂,state,Code.readN_prefix]
  have h₃ : (Code.clear 3).Exec s₂ (3*old.length+1) s₃ := by
    have he := Code.clear_exec (3 : Reg) s₂
    convert he using 1
    · simp [s₂,state]
    · funext i; fin_cases i <;> simp [s₂,s₃,state]
  have h₄ : (Code.moveList 1 0 3 false).Exec s₃ (10*value.length+2) s₄ := by
    have he := Code.moveList_exec (1 : Reg) 0 3 (by decide) (by decide) (by decide) false s₃ rfl
    convert he using 1 <;> try rfl
    funext i; fin_cases i <;> simp [s₃,s₄,state]
  have h₅ : (Code.transfer 2 0 false).Exec s₄ (5*pre.length+1) (state (pre++value++post) [] [] []) := by
    have he := Code.transfer_exec (2 : Reg) 0 (by decide) false s₄
    convert he using 1
    · simp [s₄,state]
    · funext i; fin_cases i <;> simp [s₄,state,List.append_assoc]
  refine ⟨_,?_,Code.Exec.seq h₁ (Code.Exec.seq h₂ (Code.Exec.seq h₃ (Code.Exec.seq h₄ h₅)))⟩
  simp only [List.length_append]
  omega
end WLTime.RAMSlices

namespace WLTime.RegisterFile
 theorem zero (R w : ℕ) : registerBits (fun _ : Fin R => (⟨0,by positivity⟩ : Word w))=List.replicate (R*w) false := by
  simp [registerBits,wordBits,List.ofFn_const]
 theorem update_list {R w : ℕ} (a : Fin R → Word w) (i : Fin R) (v : Word w) :
    (List.ofFn (fun j => wordBits (Function.update a i v j)))=
      (List.ofFn (fun j => wordBits (a j))).set i.val (wordBits v) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_ofFn,List.getElem_set]
    by_cases h : j=i.val
    · subst j
      simp
    · have hh : (⟨j,by simpa using hj⟩ : Fin R)≠i := by simpa [Fin.ext_iff] using h
      simp [Ne.symm h,hh]
 theorem split {R w : ℕ} (a : Fin R → Word w) (i : Fin R) :
    ∃ pre post : List Bool, pre.length=w*i.val ∧
      registerBits a=pre++wordBits (a i)++post ∧
      ∀ v : Word w,registerBits (Function.update a i v)=pre++wordBits v++post := by
  let xs := List.ofFn (fun j => wordBits (a j))
  have hi : i.val<xs.length := by simp [xs]
  have hw : ∀x∈xs,x.length=w := by
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    simp [wordBits]
  have hs : xs=xs.take i.val++xs[i.val]::xs.drop (i.val+1) := by
    have h := List.take_append_drop i.val xs
    rw [List.drop_eq_getElem_cons hi] at h
    exact h.symm
  refine ⟨(xs.take i.val).flatten,(xs.drop (i.val+1)).flatten,?_,?_,?_⟩
  · rw [flatten_length w _ (fun x hx => hw x (List.mem_of_mem_take hx)),List.length_take]
    rw [Nat.min_eq_left (Nat.le_of_lt hi)]
  · change xs.flatten=_
    conv_lhs => rw [hs]
    simp only [List.flatten_append,List.flatten_cons,List.append_assoc]
    simp only [xs,List.getElem_ofFn]
  · intro v
    unfold registerBits
    rw [update_list,List.set_eq_take_append_cons_drop,ite_eq_left (by simp)]
    simp only [List.flatten_append,List.flatten_cons,List.append_assoc]
    rfl
end WLTime.RegisterFile

namespace WLTime.RAMMemory
open TypedStack WordMemory
theorem keyMap_inj : Function.Injective keyMap := by decide
theorem valueMap_inj : Function.Injective valueMap := by decide
theorem lookupMap_inj : Function.Injective lookupMap := by decide
theorem storeMap_inj : Function.Injective storeMap := by decide
 theorem readKey_exec {R w : ℕ} (a : Fin R → Word w) (i : Fin R) (log value : List Bool) :
    ∃ u ≤ 60*(R*w+1), (readKey w i.val).Exec (state (registerBits a) log [] value) u
      (state (registerBits a) log (wordBits (a i)) value) := by
  obtain ⟨pre,post,hpre,hs,_⟩ := RegisterFile.split a i
  obtain ⟨u,hu,he⟩ := RAMSlices.read_exec pre (wordBits (a i)) post
  rw [←hs,RegisterFile.length] at hu
  rw [hpre,show (wordBits (a i)).length=w from by simp [wordBits]] at he
  refine ⟨u,hu,?_⟩
  apply Code.relabel_exec_of_maps keyMap keyMap_inj he
  · intro k; fin_cases k <;> simp [state,keyMap,RAMSlices.state,hs]
  · intro k; fin_cases k <;> simp [state,keyMap,RAMSlices.state,hs]
  · intro k hk; fin_cases k <;> simp_all [state,keyMap,Fin.forall_fin_succ]
 theorem readValue_exec {R w : ℕ} (a : Fin R → Word w) (i : Fin R) (log key : List Bool) :
    ∃ u ≤ 60*(R*w+1), (readValue w i.val).Exec (state (registerBits a) log key []) u
      (state (registerBits a) log key (wordBits (a i))) := by
  obtain ⟨pre,post,hpre,hs,_⟩ := RegisterFile.split a i
  obtain ⟨u,hu,he⟩ := RAMSlices.read_exec pre (wordBits (a i)) post
  rw [←hs,RegisterFile.length] at hu
  rw [hpre,show (wordBits (a i)).length=w from by simp [wordBits]] at he
  refine ⟨u,hu,?_⟩
  apply Code.relabel_exec_of_maps valueMap valueMap_inj he
  · intro k; fin_cases k <;> simp [state,valueMap,RAMSlices.state,hs]
  · intro k; fin_cases k <;> simp [state,valueMap,RAMSlices.state,hs]
  · intro k hk; fin_cases k <;> simp_all [state,valueMap,Fin.forall_fin_succ]
 theorem writeValue_exec {R w : ℕ} (a : Fin R → Word w) (i : Fin R) (v : Word w) (log key : List Bool) :
    ∃ u ≤ 30*(R*w+1), (writeValue w i.val).Exec (state (registerBits a) log key (wordBits v)) u
      (state (registerBits (Function.update a i v)) log key []) := by
  obtain ⟨pre,post,hpre,hs,ht⟩ := RegisterFile.split a i
  obtain ⟨u,hu,he⟩ := RAMSlices.write_exec pre (wordBits (a i)) post (wordBits v) (by simp [wordBits])
  rw [←hs,RegisterFile.length] at hu
  rw [hpre,show (wordBits (a i)).length=w from by simp [wordBits]] at he
  refine ⟨u,hu,?_⟩
  apply Code.relabel_exec_of_maps valueMap valueMap_inj he
  · intro k; fin_cases k <;> simp [state,valueMap,RAMSlices.state,hs]
  · intro k; fin_cases k <;> simp [state,valueMap,RAMSlices.state,ht]
  · intro k hk; fin_cases k <;> simp_all [state,valueMap,Fin.forall_fin_succ]
 theorem lookup_exec {w : ℕ} (hw : 0<w) (q : Word w) (l : Log w) (file : List Bool) :
    ∃ u ≤ 60*(w+1)*(l.length+1), (lookup w).Exec (state file (SparseLookup.flatten (entries l)) (wordBits q) []) u
      (state file (SparseLookup.flatten (entries l)) (wordBits q) (wordBits (read q l))) := by
  obtain ⟨u,hu,he⟩ := WordMemory.lookup_exec hw q l
  refine ⟨u,hu,?_⟩
  apply Code.relabel_exec_of_maps lookupMap lookupMap_inj he
  · intro k; fin_cases k <;> simp [state,lookupMap,SparseLookup.state]
  · intro k; fin_cases k <;> simp [state,lookupMap,SparseLookup.state]
  · intro k hk; fin_cases k <;> simp_all [state,lookupMap,Fin.forall_fin_succ]
 theorem store_exec {w : ℕ} (q v : Word w) (l : Log w) (file : List Bool) :
    store.Exec (state file (SparseLookup.flatten (entries l)) (wordBits q) (wordBits v)) (24*w+4)
      (state file (SparseLookup.flatten (entries ((q,v)::l))) (wordBits q) (wordBits v)) := by
  have he := SparseStore.program_exec (SparseLookup.flatten (entries l)) (wordBits q) (wordBits v)
  have hc : 12*((wordBits q).length+(wordBits v).length)+4=24*w+4 := by simp [wordBits]; omega
  rw [hc] at he
  apply Code.relabel_exec_of_maps storeMap storeMap_inj he
  · intro k; fin_cases k <;> simp [state,storeMap,SparseStore.state]
  · intro k; fin_cases k <;> simp [state,storeMap,SparseStore.state,entries,SparseLookup.flatten,List.append_assoc]
  · intro k hk; fin_cases k <;> simp_all [state,storeMap,Fin.forall_fin_succ]
 theorem clear_key (file log key value : List Bool) :
    (Code.clear 2).Exec (state file log key value) (3*key.length+1) (state file log [] value) := by
  have he := Code.clear_exec (2 : Reg) (state file log key value)
  convert he using 1 <;> try rfl
  funext k; fin_cases k <;> simp [state]
 theorem clear_value (file log key value : List Bool) :
    (Code.clear 3).Exec (state file log key value) (3*value.length+1) (state file log key []) := by
  have he := Code.clear_exec (3 : Reg) (state file log key value)
  convert he using 1 <;> try rfl
  funext k; fin_cases k <;> simp [state]
 theorem cost_arith (R w L : ℕ) :
    90*(R*w+1)+60*(w+1)*(L+1)+(3*w+1) ≤ cost R w L ∧
    120*(R*w+1)+(24*w+4)+2*(3*w+1) ≤ cost R w 0 := by
  have h₁ : R*w+1 ≤ (R+1)*(w+1) := by nlinarith
  have h₂ : (R+1)*(w+1) ≤ (R+1)*(w+1)*(L+1) := Nat.le_mul_of_pos_right _ (by omega)
  have h₃ : (w+1)*(L+1) ≤ (R+1)*(w+1)*(L+1) := Nat.mul_le_mul_right _ (by nlinarith)
  have h₄ : w+1 ≤ (R+1)*(w+1) := by nlinarith
  unfold cost
  constructor <;> nlinarith only [h₁,h₂,h₃,h₄]
 theorem load_exec {R w : ℕ} (hw : 0<w) (a : Fin R → Word w) (l : Log w) (dest addr : Fin R) :
    ∃ u ≤ cost R w l.length, (load w dest.val addr.val).Exec (state (registerBits a) (SparseLookup.flatten (entries l)) [] []) u
      (state (registerBits (Function.update a dest (read (a addr) l))) (SparseLookup.flatten (entries l)) [] []) := by
  obtain ⟨x,hx,he⟩ := readKey_exec a addr (SparseLookup.flatten (entries l)) []
  obtain ⟨y,hy,hf⟩ := lookup_exec hw (a addr) l (registerBits a)
  obtain ⟨z,hz,hg⟩ := writeValue_exec a dest (read (a addr) l) (SparseLookup.flatten (entries l)) (wordBits (a addr))
  have hh := clear_key (registerBits (Function.update a dest (read (a addr) l))) (SparseLookup.flatten (entries l)) (wordBits (a addr)) []
  have hc := (cost_arith R w l.length).1
  refine ⟨_,?_,Code.Exec.seq he (Code.Exec.seq hf (Code.Exec.seq hg hh))⟩
  simp only [wordBits,List.length_ofFn]
  omega
 theorem save_exec {R w : ℕ} (a : Fin R → Word w) (l : Log w) (addr src : Fin R) :
    ∃ u ≤ cost R w 0, (save w addr.val src.val).Exec (state (registerBits a) (SparseLookup.flatten (entries l)) [] []) u
      (state (registerBits a) (SparseLookup.flatten (entries ((a addr,a src)::l))) [] []) := by
  obtain ⟨x,hx,he⟩ := readKey_exec a addr (SparseLookup.flatten (entries l)) []
  obtain ⟨y,hy,hf⟩ := readValue_exec a src (SparseLookup.flatten (entries l)) (wordBits (a addr))
  have hg := store_exec (a addr) (a src) l (registerBits a)
  have hh := clear_key (registerBits a) (SparseLookup.flatten (entries ((a addr,a src)::l))) (wordBits (a addr)) (wordBits (a src))
  have hj := clear_value (registerBits a) (SparseLookup.flatten (entries ((a addr,a src)::l))) [] (wordBits (a src))
  have hc := (cost_arith R w 0).2
  refine ⟨_,?_,Code.Exec.seq he (Code.Exec.seq hf (Code.Exec.seq hg (Code.Exec.seq hh hj)))⟩
  simp only [wordBits,List.length_ofFn]
  omega
end WLTime.RAMMemory

end OAI
end

section
-- module Solutions.OAIQW_WLTime.RAMInstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLTime.ZeroTest
open TypedStack
 theorem marks_length (xs : List Bool) (b : Bool) (hist : List Bool) :
    (marks xs b hist).length=xs.length+hist.length+1 := by
  induction xs generalizing b hist with
  | nil => simp [marks]
  | cons x xs ih => simp [marks,ih]; omega
 theorem marks_head (xs : List Bool) (b : Bool) (hist : List Bool) :
    (marks xs b hist).headD false=(b||xs.any id) := by
  induction xs generalizing b hist with
  | nil => simp [marks]
  | cons x xs ih =>
    change (marks xs (b||x) (b::hist)).headD false=(b||(x::xs).any id)
    rw [ih]
    simp only [List.any_cons, Bool.or_assoc, id_eq]
 theorem loop_exec (xs : List Bool) (b : Bool) (hist : List Bool) :
    loopCode.Exec (state xs (b::hist)) (5*xs.length+1) (state [] (marks xs b hist)) := by
  induction xs generalizing b hist with
  | nil => exact Code.Exec.loop_false (by simp [Code.nonempty,tops,state])
  | cons x xs ih =>
    let s₀ := state (x::xs) (b::hist)
    let s₁ := Function.update s₀ 1 ((b||x)::b::hist)
    have hp : (Code.pushDyn 1 (fun v : Tops Reg Bool => (v 1).getD false || (v 0).getD false)).Exec s₀ 2 s₁ := by
      simpa [s₀,s₁,state,tops] using Code.Exec.pushDyn s₀ 1 (fun v : Tops Reg Bool => (v 1).getD false || (v 0).getD false)
    have he : (Code.pop 0).Exec s₁ 2 (state xs ((b||x)::b::hist)) := by
      have h := Code.Exec.pop s₁ 0
      convert h using 1
      funext i; fin_cases i <;> simp [s₁,s₀,state]
    have hh := Code.Exec.loop_true (p:=Code.nonempty (0 : Reg)) (by simp [Code.nonempty,tops,s₀,state])
      (Code.Exec.seq hp he) (ih (b||x) (b::hist))
    convert hh using 1 <;> try rfl
    simp only [List.length_cons]; omega
 theorem finish_exec (fs : List Bool) :
    finish.Exec (state [] fs) (3*fs.length+4) (state [] [fs.headD false]) := by
  have hc : (Code.clear 1).Exec (state [] fs) (3*fs.length+1) (state [] []) := by
    have he := Code.clear_exec (1 : Reg) (state [] fs)
    convert he using 1 <;> try rfl
    funext k; fin_cases k <;> simp [state]
  have hp (b : Bool) : (Code.push 1 b).Exec (state [] []) 2 (state [] [b]) := by
    have he := Code.Exec.push (state [] [] : Stacks Reg Bool) 1 b
    convert he using 1
    funext k; fin_cases k <;> simp [state]
  cases hh : fs.headD false
  · have he := Code.Exec.branch_false (a:=.seq (.clear 1) (.push 1 true)) (p:=fun v : Tops Reg Bool => (v 1).getD false)
      (by simpa [tops,state] using hh) (Code.Exec.seq hc (hp false))
    simpa only [finish,hh,Nat.add_assoc] using he
  · have he := Code.Exec.branch_true (b:=.seq (.clear 1) (.push 1 false)) (p:=fun v : Tops Reg Bool => (v 1).getD false)
      (by simpa [tops,state] using hh) (Code.Exec.seq hc (hp true))
    simpa only [finish,hh,Nat.add_assoc] using he
 theorem program_exec (xs : List Bool) :
    program.Exec (state xs []) (8*xs.length+10) (state [] [xs.any id]) := by
  have hp : (Code.push 1 false).Exec (state xs []) 2 (state xs [false]) := by
    have he := Code.Exec.push (state xs [] : Stacks Reg Bool) 1 false
    convert he using 1
    funext k; fin_cases k <;> simp [state]
  have he := loop_exec xs false []
  have hf := finish_exec (marks xs false [])
  rw [marks_head,marks_length] at hf
  simp only [Bool.false_or,List.length_nil,Nat.add_zero] at hf
  have hg := Code.Exec.seq hp (Code.Exec.seq he hf)
  convert hg using 1
  · rfl
  · omega
 theorem any_false_iff (xs : List Bool) : xs.any id=false ↔ xs=List.replicate xs.length false := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases x <;> simp [List.replicate_succ,ih]
 theorem word_zero_iff {w : ℕ} (a : Word w) : (wordBits a).any id=false ↔ a.val=0 := by
  rw [any_false_iff]
  constructor
  · intro h
    have he : wordBits a=wordBits (⟨0,by positivity⟩ : Word w) := by
      rw [WordMemory.word_zero]
      simpa [wordBits] using h
    exact congrArg Fin.val (BitWords.word_injective he)
  · intro h
    have he : a=(⟨0,by positivity⟩ : Word w) := Fin.ext h
    rw [he,WordMemory.word_zero]
    simp
end WLTime.ZeroTest

namespace WLTime.SparseRAM
open WordMemory
 theorem execute_log_length {R P w : ℕ} (I : RAMInstruction R P) (C : Config R P w) :
    (execute I C).log.length ≤ C.log.length+I.depth := by
  induction I generalizing C with
  | halt b => simp [execute,RAMInstruction.depth]
  | jump pc => simp [execute,RAMInstruction.depth]
  | compute op next ih =>
    have h := ih {C with registers := op.apply w C.registers}
    simpa only [execute,RAMInstruction.depth] using h.trans (by dsimp; omega)
  | load dest addr next ih =>
    have h := ih {C with registers := Function.update C.registers dest (read (C.registers addr) C.log)}
    exact h.trans (by change C.log.length+next.depth ≤ C.log.length+(next.depth+1); omega)
  | store addr src next ih =>
    have h := ih {C with log := (C.registers addr,C.registers src)::C.log}
    simpa only [execute,RAMInstruction.depth,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  | branchZero reg yes no ih ih' =>
    by_cases hz : (C.registers reg).val=0
    · simpa only [execute,ite_eq_left hz,RAMInstruction.depth] using (ih C).trans (by omega)
    · simpa only [execute,ite_eq_right hz,RAMInstruction.depth] using (ih' C).trans (by omega)
 theorem execute_forget (A : RAM) (n : ℕ) (I : RAMInstruction A.registers A.locations)
    (C : Config A.registers A.locations (A.width.bits n)) :
    A.execute I (forget A n C)=forget A n (execute I C) := by
  induction I generalizing C with
  | halt b => rfl
  | jump pc => rfl
  | compute op next ih => exact ih {C with registers := op.apply (A.width.bits n) C.registers}
  | load dest addr next ih => exact ih {C with registers := Function.update C.registers dest (read (C.registers addr) C.log)}
  | store addr src next ih =>
    have h := ih {C with log := (C.registers addr,C.registers src)::C.log}
    simpa only [execute,RAM.execute,forget,read_prepend] using h
  | branchZero reg yes no ih ih' =>
    by_cases hz : (C.registers reg).val=0
    · simpa [execute,RAM.execute,forget,hz] using ih C
    · simpa [execute,RAM.execute,forget,hz] using ih' C
 theorem step_forget (A : RAM) (n : ℕ) (C : Config A.registers A.locations (A.width.bits n)) :
    A.step (forget A n C)=forget A n (step A (A.width.bits n) C) := by
  cases h : C.answer with
  | none => simpa only [RAM.step,step,forget,h] using execute_forget A n (A.program C.pc) C
  | some b => simp only [RAM.step,step,forget,h]
 theorem iterate_forget (A : RAM) (n : ℕ) (C : Config A.registers A.locations (A.width.bits n)) (t : ℕ) :
    A.step^[t] (forget A n C)=forget A n ((step A (A.width.bits n))^[t] C) := by
  induction t generalizing C with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply,Function.iterate_succ_apply,step_forget,ih]
 theorem step_fixed (A : RAM) (w : ℕ) (C : Config A.registers A.locations w) (h : C.answer.isSome=true) :
    step A w C=C := by cases hh : C.answer <;> simp_all [step]
end WLTime.SparseRAM
namespace WLTime.RAM
 theorem time_halted (A : RAM) (n : ℕ) (input : List Bool) (h : A.halts n input) :
    (A.run n input (A.time n input)).answer.isSome=true := by
  unfold time
  split_ifs
  exact Nat.find_spec h
 theorem run_add_halted (A : RAM) (n : ℕ) (input : List Bool) (t s : ℕ) (h : (A.run n input t).answer.isSome=true) :
    A.run n input (t+s)=A.run n input t := by
  have hh : A.step (A.run n input t)=A.run n input t := by
    cases he : (A.run n input t).answer <;> simp_all [step]
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.add_succ]
    have hr : A.run n input (t+s+1)=A.step (A.run n input (t+s)) := Function.iterate_succ_apply' _ _ _
    rw [hr,ih,hh]
 theorem accepts_iff_answer (A : RAM) (n : ℕ) (input : List Bool) (t : ℕ) (b : Bool)
    (h : (A.run n input t).answer=some b) : A.accepts n input ↔ b=true := by
  constructor
  · rintro ⟨s,hs⟩
    have ht : (A.run n input t).answer.isSome=true := by rw [h]; rfl
    have hu : (A.run n input s).answer.isSome=true := by rw [hs]; rfl
    have he₁ := A.run_add_halted n input t s ht
    have he₂ := A.run_add_halted n input s t hu
    rw [Nat.add_comm] at he₂
    have he := congrArg Config.answer (he₁.symm.trans he₂)
    rw [h,hs] at he
    exact Option.some.inj he
  · intro hb
    exact ⟨t,by rw [h,hb]⟩
end WLTime.RAM

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
theorem memMap_inj : Function.Injective (memMap A) := by
  intro i j h
  exact Fin.ext (congrArg (fun r : Reg A => match r with | .inl k => k.val | .inr _ => 0) h)
 theorem liftMem_mem (s : Stacks RAMMemory.Reg Bool) (pc : Fin A.locations) (answer : Option Bool) (i : RAMMemory.Reg) :
    liftMem A s pc answer (memMap A i)=(s i).map Sum.inl := by simp [liftMem,memMap,i.isLt]
 theorem mem_exec {s out : Stacks RAMMemory.Reg Bool} {c : Code RAMMemory.Reg Bool} {t : ℕ}
    (he : c.Exec s t out) (pc : Fin A.locations) (answer : Option Bool) :
    ((c.mapLetters Sum.inl (decode A)).relabel (memMap A)).Exec (liftMem A s pc answer) t (liftMem A out pc answer) := by
  have h := Code.mapLetters_exec (Sum.inl : Bool → Letter A) (decode A) (by intro b; rfl) he
  apply Code.relabel_exec_of_maps _ (memMap_inj A) h
  · intro i; exact liftMem_mem A s pc answer i
  · intro i; exact liftMem_mem A out pc answer i
  · intro r hr
    cases r with
    | inl i =>
      by_cases hi : i.val<12
      · exact False.elim (hr ⟨i.val,hi⟩ rfl)
      · simp [liftMem,hi]
    | inr r => rfl
 theorem opReg_inj (i : Index A) : Function.Injective (opReg A i) := by
  intro r s h
  by_cases hr : r=TMPort.port (operation A i).implementation
  · by_cases hs : s=TMPort.port (operation A i).implementation
    · exact hr.trans hs.symm
    · simp [opReg,hr,hs] at h
  · by_cases hs : s=TMPort.port (operation A i).implementation
    · simp [opReg,hr,hs] at h
    · simpa [opReg,hr,hs] using h
 theorem opLetter_inj (i : Index A) : Function.Injective (opLetter A i) := by
  intro x y h
  cases x <;> cases y <;> simp_all [opLetter]
 theorem opDecode_left (i : Index A) : Function.LeftInverse (opDecode A i) (opLetter A i) :=
  Function.leftInverse_invFun (opLetter_inj A i)
 theorem fileState_opReg (i : Index A) (xs log : List Bool) (pc : Fin A.locations) (answer : Option Bool)
    (r : TMPort.Reg (operation A i).implementation) :
    fileState A xs log pc answer (opReg A i r)=
    Code.listMap (opLetter A i) (TMPort.inputState (operation A i).implementation xs) r := by
  by_cases h : r=TMPort.port (operation A i).implementation
  · subst r
    simp [fileState,liftMem,RAMMemory.state,opReg,TMPort.inputState,Code.listMap,opLetter,List.map_map,Function.comp_def]
  · simp [fileState,liftMem,opReg,h,TMPort.inputState,Code.listMap]
 theorem op_exec (i : Index A) (input output log : List Bool) (pc : Fin A.locations) (answer : Option Bool)
    (ho : (operation A i).implementation.outputs input output) :
    ∃u ≤ TMPort.factor (operation A i).implementation*(input.length+(operation A i).implementation.time input+output.length+1),
      (opCode A i input.length output.length).Exec (fileState A input log pc answer) u (fileState A output log pc answer) := by
  obtain ⟨u,hu,he⟩ := TMPort.program_exec _ input output ho
  refine ⟨u,hu,?_⟩
  have hh := Code.mapLetters_exec (opLetter A i) (opDecode A i) (opDecode_left A i) he
  apply Code.relabel_exec_of_maps _ (opReg_inj A i) hh
  · exact fileState_opReg A i input log pc answer
  · exact fileState_opReg A i output log pc answer
  · intro r hr
    cases r with
    | inl k =>
      have hk : k≠0 := by
        intro h; subst k
        exact hr (TMPort.port _) (by simp [opReg])
      fin_cases k <;> simp_all [fileState,liftMem,RAMMemory.state]
    | inr r => rfl
end
end WLTime.RAMAlphabet

namespace WLTime.RAMTests
open TypedStack
open scoped Classical
theorem testMap_inj : Function.Injective testMap := by decide
 theorem exec {R w : ℕ} (a : Fin R → Word w) (i : Fin R) (log : List Bool) :
    ∃u ≤ 60*(R*w+1)+8*w+10,(testCode w i.val).Exec (RAMMemory.state (registerBits a) log [] []) u
      (flags (registerBits a) log ((wordBits (a i)).any id)) := by
  obtain ⟨t,ht,he⟩ := RAMMemory.readKey_exec a i log []
  have hz := ZeroTest.program_exec (wordBits (a i))
  have hh : (ZeroTest.program.relabel testMap).Exec
      (RAMMemory.state (registerBits a) log (wordBits (a i)) []) (8*w+10)
      (flags (registerBits a) log ((wordBits (a i)).any id)) := by
    have hl : (wordBits (a i)).length=w := by simp [wordBits]
    rw [hl] at hz
    apply Code.relabel_exec_of_maps _ testMap_inj hz
    · intro k; fin_cases k <;> simp [testMap,RAMMemory.state,ZeroTest.state]
    · intro k; fin_cases k <;> simp [testMap,RAMMemory.state,ZeroTest.state,flags]
    · intro k hk; fin_cases k <;> simp_all [testMap,RAMMemory.state,flags,Fin.forall_fin_succ]
  exact ⟨_,by omega,Code.Exec.seq he hh⟩
 theorem pop_exec (file log : List Bool) (b : Bool) :
    (Code.pop 11).Exec (flags file log b) 2 (RAMMemory.state file log [] []) := by
  have he := Code.Exec.pop (flags file log b) 11
  convert he using 1
  funext k; fin_cases k <;> simp [flags,RAMMemory.state]
end WLTime.RAMTests
namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
 theorem prefix_exec (pre file log : List Bool) (pc : Fin A.locations) (answer : Option Bool) :
    (Code.pushList (.inl 0) (pre.map (Sum.inl : Bool → Letter A))).Exec (fileState A file log pc answer)
      (2*pre.length+1) (fileState A (pre++file) log pc answer) := by
  have h := Code.pushList_exec (.inl 0 : Reg A) (pre.map (Sum.inl : Bool → Letter A)) (fileState A file log pc answer)
  simp only [List.length_map] at h
  convert h using 1
  funext k
  cases k with
  | inl j => fin_cases j <;> simp [fileState,liftMem,RAMMemory.state]
  | inr j => simp [fileState,liftMem]
 theorem compute_exec {w : ℕ} (op : WordOperation A.registers) (h : op ∈ operations A)
    (C : SparseRAM.Config A.registers A.locations w) :
    ∃u ≤ 2*(encodeNat w).length+1+TMPort.factor op.implementation*
      ((encodeNat w).length+2*(A.registers*w)+op.constant*(w+1)^op.exponent+1),
      (compute A w op h).Exec (state A C) u (state A {C with registers := op.apply w C.registers}) := by
  have hp := prefix_exec A (encodeNat w) (registerBits C.registers)
    (SparseLookup.flatten (WordMemory.entries C.log)) C.pc C.answer
  have ho := op.computes w C.registers
  have he := op_exec A (locate A op h) (encodeNat w++registerBits C.registers)
    (registerBits (op.apply w C.registers)) (SparseLookup.flatten (WordMemory.entries C.log)) C.pc C.answer
  rw [locate_eq] at he
  obtain ⟨u,hu,he⟩ := he ho
  simp only [List.length_append,RegisterFile.length] at hu he
  refine ⟨_,?_,Code.Exec.seq hp he⟩
  have hc := op.cost w C.registers
  exact Nat.add_le_add_left (hu.trans (Nat.mul_le_mul_left _ (by omega))) _
end
end WLTime.RAMAlphabet

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
 theorem basic_le_unit (w : ℕ) : 1000*(A.registers+1)*(w+1) ≤ unitCost A w := Nat.le_add_right _ _
 theorem six_le_unit (w : ℕ) : 6≤unitCost A w := (by nlinarith : 6≤1000*(A.registers+1)*(w+1)).trans (basic_le_unit A w)
 theorem op_le_unit (w : ℕ) (op : WordOperation A.registers) (h : op ∈ operations A) : opCost A w op ≤ unitCost A w := by
  have he := Finset.single_le_sum (f:=fun i : Index A => opCost A w (operation A i)) (fun i _ => Nat.zero_le _) (Finset.mem_univ (locate A op h))
  rw [locate_eq] at he
  exact he.trans (Nat.le_add_left _ _)
 theorem memory_le_unit (w L : ℕ) : RAMMemory.cost A.registers w L ≤ unitCost A w*(L+1) := by
  have he := Nat.mul_le_mul_right (L+1) (basic_le_unit A w)
  unfold RAMMemory.cost
  nlinarith only [he]
 theorem test_le_unit (w : ℕ) : 60*(A.registers*w+1)+8*w+13 ≤ unitCost A w := by
  exact (by nlinarith : 60*(A.registers*w+1)+8*w+13≤1000*(A.registers+1)*(w+1)).trans (basic_le_unit A w)
 theorem halt_exec {w : ℕ} (C : SparseRAM.Config A.registers A.locations w) (b : Bool) :
    ∃u ≤ 6,(haltCode A b).Exec (state A C) u (state A {C with answer := some b}) := by
  have hc := Code.clear_exec (.inl 13 : Reg A) (state A C)
  have hp := Code.Exec.push (Function.update (state A C) (.inl 13) []) (.inl 13) (.inl b)
  have he := Code.Exec.seq hc hp
  have hout : Function.update (Function.update (state A C) (.inl 13) []) (.inl 13)
      (Sum.inl b::(Function.update (state A C) (.inl 13) []) (.inl 13))=state A {C with answer := some b} := by
    funext k
    cases k with
    | inl j => fin_cases j <;> simp [state,liftMem]
    | inr j => simp [state,liftMem]
  rw [hout] at he
  refine ⟨_,?_,he⟩
  cases C.answer <;> simp [state,liftMem]
 theorem jump_exec {w : ℕ} (C : SparseRAM.Config A.registers A.locations w) (pc : Fin A.locations) :
    (jumpCode A pc).Exec (state A C) 6 (state A {C with pc := pc}) := by
  have hc := Code.clear_exec (.inl 12 : Reg A) (state A C)
  have hp := Code.Exec.push (Function.update (state A C) (.inl 12) []) (.inl 12) (.inr (.inl pc))
  have he := Code.Exec.seq hc hp
  convert he using 1
  · rfl
  · simp [state,liftMem]
  · funext k
    cases k with
    | inl j => fin_cases j <;> simp [state,liftMem]
    | inr j => simp [state,liftMem]
 theorem test_tops (file log : List Bool) (b : Bool) (pc : Fin A.locations) (answer : Option Bool) :
    ((tops (liftMem A (RAMTests.flags file log b) pc answer) (.inl 11)).map (decode A)).getD false=b := by
  simp [tops,liftMem,RAMTests.flags,decode]
 theorem combine_cost (B L D a b : ℕ) (ha : a≤ B*(L+1)) (hb : b≤B*D*(L+D+2)) :
    a+b≤B*(D+1)*(L+(D+1)+1) := by
  have hh : B*(L+1)≤B*(L+D+2) := Nat.mul_le_mul_left _ (by omega)
  calc
    a+b≤B*(L+D+2)+B*D*(L+D+2) := Nat.add_le_add (ha.trans hh) hb
    _=B*(D+1)*(L+(D+1)+1) := by ring
end
end WLTime.RAMAlphabet

end OAI
end

section
-- module Solutions.OAIQW_WLTime.RAMSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uX uT

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
 theorem bound_mono (B L D E : ℕ) (h : D≤E) : B*D*(L+D+1)≤B*E*(L+E+2) :=
  Nat.mul_le_mul (Nat.mul_le_mul_left _ h) (by omega)
 theorem instruction_exec {w : ℕ} (hw : 0<w) (I : RAMInstruction A.registers A.locations)
    (h : ∀op ∈ I.operations,op ∈ operations A) (C : SparseRAM.Config A.registers A.locations w) :
    ∃u ≤ unitCost A w*I.depth*(C.log.length+I.depth+1),
      (instruction A w I h).Exec (state A C) u (state A (SparseRAM.execute I C)) := by
  induction I generalizing C with
  | halt b =>
    obtain ⟨u,hu,he⟩ := halt_exec A C b
    refine ⟨u,?_,he⟩
    exact (hu.trans (six_le_unit A w)).trans (by simp only [RAMInstruction.depth,Nat.mul_one]; exact Nat.le_mul_of_pos_right _ (by omega))
  | jump pc =>
    refine ⟨6,?_,jump_exec A C pc⟩
    exact (six_le_unit A w).trans (by simp only [RAMInstruction.depth,Nat.mul_one]; exact Nat.le_mul_of_pos_right _ (by omega))
  | compute op next ih =>
    let hn : ∀q ∈ next.operations,q ∈ operations A := fun q hq => h q (by simp [RAMInstruction.operations,hq])
    let hop : op ∈ operations A := h op (by simp [RAMInstruction.operations])
    obtain ⟨x,hx,he⟩ := compute_exec A op hop C
    obtain ⟨y,hy,hf⟩ := ih hn {C with registers := op.apply w C.registers}
    refine ⟨x+y,?_,Code.Exec.seq he hf⟩
    apply combine_cost
    · exact (hx.trans (op_le_unit A w op hop)).trans (Nat.le_mul_of_pos_right _ (by omega))
    · exact hy.trans (bound_mono _ _ _ _ le_rfl)
  | load dest addr next ih =>
    obtain ⟨x,hx,he⟩ := RAMMemory.load_exec hw C.registers C.log dest addr
    have hh := mem_exec A he C.pc C.answer
    obtain ⟨y,hy,hf⟩ := ih h {C with registers := Function.update C.registers dest (WordMemory.read (C.registers addr) C.log)}
    refine ⟨x+y,?_,Code.Exec.seq hh hf⟩
    apply combine_cost
    · exact hx.trans (memory_le_unit A w C.log.length)
    · exact hy.trans (bound_mono _ _ _ _ le_rfl)
  | store addr src next ih =>
    obtain ⟨x,hx,he⟩ := RAMMemory.save_exec C.registers C.log addr src
    have hh := mem_exec A he C.pc C.answer
    obtain ⟨y,hy,hf⟩ := ih h {C with log := (C.registers addr,C.registers src)::C.log}
    refine ⟨x+y,?_,Code.Exec.seq hh hf⟩
    apply combine_cost
    · exact hx.trans ((memory_le_unit A w 0).trans (by simpa using Nat.le_mul_of_pos_right (unitCost A w) (by omega : 0<C.log.length+1)))
    · change y≤unitCost A w*next.depth*(C.log.length+1+next.depth+1) at hy
      convert hy using 1
      congr 1
      omega
  | branchZero reg yes no ih ih' =>
    let hy : ∀q ∈ yes.operations,q ∈ operations A := fun q hq => h q (by simp [RAMInstruction.operations,hq])
    let hn : ∀q ∈ no.operations,q ∈ operations A := fun q hq => h q (by simp [RAMInstruction.operations,hq])
    obtain ⟨x,hx,he⟩ := RAMTests.exec C.registers reg (SparseLookup.flatten (WordMemory.entries C.log))
    have hh := mem_exec A he C.pc C.answer
    have hp := mem_exec A (RAMTests.pop_exec (registerBits C.registers)
      (SparseLookup.flatten (WordMemory.entries C.log)) ((wordBits (C.registers reg)).any id)) C.pc C.answer
    have htest := test_tops A (registerBits C.registers) (SparseLookup.flatten (WordMemory.entries C.log))
      ((wordBits (C.registers reg)).any id) C.pc C.answer
    have hx' : x+3≤unitCost A w*(C.log.length+1) :=
      (show x+3≤unitCost A w from (by have ht := test_le_unit A w; omega)).trans (Nat.le_mul_of_pos_right _ (by omega))
    by_cases hz : (C.registers reg).val=0
    · have hb := (ZeroTest.word_zero_iff (C.registers reg)).mpr hz
      have ht := htest.trans hb
      obtain ⟨y,hy',hf⟩ := ih hy C
      have hc := Code.Exec.seq hh (Code.Exec.branch_false
        (a:=.seq (.pop (.inl 11)) (instruction A w no hn)) (p:=fun v : Tops (Reg A) (Letter A) => ((v (.inl 11)).map (decode A)).getD false) ht (Code.Exec.seq hp hf))
      refine ⟨x+(1+(2+y)),?_,?_⟩
      · have hy'' := hy'.trans (bound_mono (unitCost A w) C.log.length yes.depth (max yes.depth no.depth) (le_max_left _ _))
        have hbound := combine_cost (unitCost A w) C.log.length (max yes.depth no.depth) (x+3) y hx' hy''
        simpa only [RAMInstruction.depth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hbound
      · convert hc using 1
        all_goals try rfl
        · omega
        · simp only [SparseRAM.execute,ite_eq_left hz]
    · have hb : (wordBits (C.registers reg)).any id=true := by
        cases hb : (wordBits (C.registers reg)).any id
        · exact False.elim (hz ((ZeroTest.word_zero_iff _).mp hb))
        · rfl
      have ht := htest.trans hb
      obtain ⟨y,hy',hf⟩ := ih' hn C
      have hc := Code.Exec.seq hh (Code.Exec.branch_true
        (b:=.seq (.pop (.inl 11)) (instruction A w yes hy)) (p:=fun v : Tops (Reg A) (Letter A) => ((v (.inl 11)).map (decode A)).getD false) ht (Code.Exec.seq hp hf))
      refine ⟨x+(1+(2+y)),?_,?_⟩
      · have hy'' := hy'.trans (bound_mono (unitCost A w) C.log.length no.depth (max yes.depth no.depth) (le_max_right _ _))
        have hbound := combine_cost (unitCost A w) C.log.length (max yes.depth no.depth) (x+3) y hx' hy''
        simpa only [RAMInstruction.depth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hbound
      · convert hc using 1
        all_goals try rfl
        · omega
        · simp only [SparseRAM.execute,ite_eq_right hz]
end
end WLTime.RAMAlphabet

namespace WLTime.SparseRAM
 theorem iterate_fixed (A : RAM) (w : ℕ) (C : Config A.registers A.locations w) (h : C.answer.isSome=true) (t : ℕ) :
    (step A w)^[t] C=C := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,step_fixed A w C h]
end WLTime.SparseRAM
namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
theorem depth_le (pc : Fin A.locations) : (A.program pc).depth≤depth A := Finset.le_sup (f:=fun pc : Fin A.locations => (A.program pc).depth) (Finset.mem_univ pc)
theorem stepBound_mono (w L L' : ℕ) (h : L≤L') : stepBound A w L ≤ stepBound A w L' := by
  unfold stepBound
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
theorem select_state {w : ℕ} (C : SparseRAM.Config A.registers A.locations w) : selectPC A (tops (state A C))=C.pc := by
  simp [selectPC,tops,state,liftMem]
 theorem dispatch_exec {w : ℕ} (hw : 0<w) (C : SparseRAM.Config A.registers A.locations w) :
    ∃u ≤ stepBound A w C.log.length,(dispatch A w).Exec (state A C) u (state A (SparseRAM.execute (A.program C.pc) C)) := by
  obtain ⟨t,ht,he⟩ := instruction_exec A hw (A.program C.pc) (mem_program A C.pc) C
  have hh : ((fun pc : Fin A.locations => instruction A w (A.program pc) (mem_program A pc)) (selectPC A (tops (state A C)))).Exec
      (state A C) t (state A (SparseRAM.execute (A.program C.pc) C)) := by simpa only [select_state] using he
  obtain ⟨u,hu,hg⟩ := Code.casesAll_exec (selectPC A) (fun pc : Fin A.locations => instruction A w (A.program pc) (mem_program A pc)) hh
  refine ⟨u,?_,hg⟩
  simp only [Fintype.card_fin] at hu
  have hd := depth_le A C.pc
  have hb : t≤unitCost A w*depth A*(C.log.length+depth A+1) := ht.trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ hd) (by omega))
  unfold stepBound
  omega
 theorem running_state {w : ℕ} (C : SparseRAM.Config A.registers A.locations w) :
    running A (tops (state A C)) = !C.answer.isSome := by
  cases h : C.answer <;> simp [running,tops,state,liftMem,h]
 theorem loop_exec {w : ℕ} (hw : 0<w) (t : ℕ) (C : SparseRAM.Config A.registers A.locations w)
    (hend : ((SparseRAM.step A w)^[t] C).answer.isSome=true) :
    ∃u ≤ (stepBound A w (C.log.length+t*depth A)+1)*t+1,
      (loopCode A w).Exec (state A C) u (state A ((SparseRAM.step A w)^[t] C)) := by
  induction t generalizing C with
  | zero =>
    simp only [Function.iterate_zero, id_eq] at hend ⊢
    refine ⟨1,by simp,?_⟩
    apply Code.Exec.loop_false
    simpa only [running_state,hend] using (show (!true)=false by rfl)
  | succ t ih =>
    cases ha : C.answer with
    | some b =>
      have hc : C.answer.isSome=true := by rw [ha]; rfl
      have hf := SparseRAM.iterate_fixed A w C hc (t+1)
      rw [hf]
      refine ⟨1,by omega,Code.Exec.loop_false ?_⟩
      simp only [running_state,hc,Bool.not_true]
    | none =>
      let C' := SparseRAM.execute (A.program C.pc) C
      have hs : SparseRAM.step A w C=C' := by simp [SparseRAM.step,ha,C']
      have hend' : ((SparseRAM.step A w)^[t] C').answer.isSome=true := by
        simpa only [Function.iterate_succ_apply,hs] using hend
      obtain ⟨x,hx,he⟩ := dispatch_exec A hw C
      obtain ⟨y,hy,hf⟩ := ih C' hend'
      have hl : C'.log.length≤C.log.length+depth A :=
        (SparseRAM.execute_log_length (A.program C.pc) C).trans (Nat.add_le_add_left (depth_le A C.pc) _)
      have hb := stepBound_mono A w C.log.length (C.log.length+(t+1)*depth A) (by omega)
      have hh := stepBound_mono A w (C'.log.length+t*depth A) (C.log.length+(t+1)*depth A) (by nlinarith only [hl])
      refine ⟨x+y+1,?_,?_⟩
      · have hh' := Nat.mul_le_mul_right t (Nat.add_le_add_right hh 1)
        nlinarith only [hx,hy,hb,hh']
      · have hg := Code.Exec.loop_true (p:=running A) (by simp only [running_state,ha,Option.isSome_none,Bool.not_false]) he hf
        simpa only [loopCode,Function.iterate_succ_apply,hs] using hg
end
end WLTime.RAMAlphabet

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
theorem inputMap_inj : Function.Injective inputMap := by
  intro i j h
  exact Fin.ext (Fin.mk.inj h)
 theorem loader_exec (w : ℕ) (hw : 0<w) (input : List Bool) (hfit : input.length≤w*2^w) :
    ∃n ≤ input.length, (fun q => WordMemory.read q (WordMemory.initialLog w input n))=RAM.packedWord w input ∧
      ∃u ≤60*(w+1)*(input.length+1),(loader w).Exec (RAMMemory.state input [] [] []) u
        (RAMMemory.state [] (SparseLookup.flatten (WordMemory.entries (WordMemory.initialLog w input n))) [] []) := by
  obtain ⟨n,hn,hm,u,hu,he⟩ := RAMInput.program_exec w hw input hfit
  refine ⟨n,hn,hm,u,hu,?_⟩
  apply Code.relabel_exec_of_maps _ inputMap_inj he
  · intro i; fin_cases i <;> simp [inputMap,RAMMemory.state,RAMInput.state]
  · intro i; fin_cases i <;> simp [inputMap,RAMMemory.state,RAMInput.state]
  · intro i hi; fin_cases i <;> simp_all [inputMap,RAMMemory.state,Fin.forall_fin_succ]
 theorem init_exec (w : ℕ) (hw : 0<w) (input : List Bool) (hfit : input.length≤w*2^w) :
    ∃n ≤ input.length, (fun q => WordMemory.read q (WordMemory.initialLog w input n))=RAM.packedWord w input ∧
      ∃u ≤ initBound A w input.length,(initCode A w).Exec (inputState A input) u (state A (initial A w input n)) := by
  obtain ⟨n,hn,hm,t,ht,he⟩ := loader_exec w hw input hfit
  have hp : (Code.push (.inl 12) (.inr (.inl ⟨0,A.locations_pos⟩))).Exec (inputState A input) 2
      (fileState A input [] ⟨0,A.locations_pos⟩ none) := by
    have hh := Code.Exec.push (inputState A input) (.inl 12) (.inr (.inl ⟨0,A.locations_pos⟩))
    convert hh using 1
    funext r
    cases r with
    | inl i => fin_cases i <;> simp [inputState,fileState,liftMem,RAMMemory.state]
    | inr r => simp [inputState,fileState,liftMem]
  have hh := mem_exec A he ⟨0,A.locations_pos⟩ none
  have hg := prefix_exec A (List.replicate (A.registers*w) false) []
    (SparseLookup.flatten (WordMemory.entries (WordMemory.initialLog w input n))) ⟨0,A.locations_pos⟩ none
  have hout : fileState A (List.replicate (A.registers*w) false++[]) (SparseLookup.flatten (WordMemory.entries (WordMemory.initialLog w input n))) ⟨0,A.locations_pos⟩ none=state A (initial A w input n) := by
    simp only [List.append_nil,state,fileState,initial,RegisterFile.zero]
  rw [hout,List.length_replicate] at hg
  refine ⟨n,hn,hm,_,?_,Code.Exec.seq hp (Code.Exec.seq hh hg)⟩
  have h₁ : (w+1)*(input.length+1)≤(A.registers+1)*(w+1)*(input.length+1) :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have h₂ : A.registers*w≤(A.registers+1)*(w+1)*(input.length+1) := by
    exact (by nlinarith : A.registers*w≤(A.registers+1)*(w+1)).trans (Nat.le_mul_of_pos_right _ (by omega))
  have h₃ : 1≤(A.registers+1)*(w+1)*(input.length+1) := by
    have : 0<(A.registers+1)*(w+1)*(input.length+1) := by positivity
    omega
  unfold initBound
  nlinarith only [ht,h₁,h₂,h₃]
 theorem initial_forget (n : ℕ) (input : List Bool) (chunks : ℕ)
    (hm : (fun q => WordMemory.read q (WordMemory.initialLog (A.width.bits n) input chunks))=RAM.packedWord (A.width.bits n) input) :
    SparseRAM.forget A n (initial A (A.width.bits n) input chunks)=A.initial n input := by
  unfold SparseRAM.forget initial RAM.initial
  congr 1
 theorem program_exec (n : ℕ) (input : List Bool) (hfit : input.length≤A.width.bits n*2^(A.width.bits n)) (hh : A.halts n input) :
    ∃u ≤ budget A (A.width.bits n) input.length (A.time n input),∃b out,
      (program A (A.width.bits n)).Exec (inputState A input) u out ∧
      out (.inl 13)=[.inl b] ∧ (b=true ↔ A.accepts n input) := by
  obtain ⟨chunks,hchunks,hm,t,ht,he⟩ := init_exec A (A.width.bits n) (A.width.positive n) input hfit
  let C := initial A (A.width.bits n) input chunks
  let T := A.time n input
  let out := (SparseRAM.step A (A.width.bits n))^[T] C
  have hforget : A.run n input T=SparseRAM.forget A n out := by
    rw [RAM.run,←initial_forget A n input chunks hm]
    exact SparseRAM.iterate_forget A n C T
  have hend : out.answer.isSome=true := by
    have h := A.time_halted n input hh
    rw [hforget] at h
    exact h
  obtain ⟨s,hs,hf⟩ := loop_exec A (A.width.positive n) T C hend
  have hl : C.log.length=chunks := WordMemory.initialLog_length _ _ _
  rw [hl] at hs
  obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp hend
  refine ⟨t+s,?_,b,state A out,Code.Exec.seq he hf,?_,?_⟩
  · have hm' := stepBound_mono A (A.width.bits n) (chunks+T*depth A) (input.length+T*depth A) (by omega)
    have hx := Nat.mul_le_mul_right T (Nat.add_le_add_right hm' 1)
    unfold budget
    dsimp only [T] at *
    omega
  · simp [state,liftMem,hb]
  · have ha : (A.run n input T).answer=some b := by rw [hforget]; exact hb
    exact (A.accepts_iff_answer n input T b ha).symm
end
end WLTime.RAMAlphabet

end OAI
end

section
-- module Solutions.OAIQW_WLTime.RAMBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uX

namespace WLTime.TypedStack.Code
variable {K : Type uK} {X : Type uX} [DecidableEq K]
 theorem haltMachine_run (c : Code K X) (input : K) (letter : Bool → X) (answer : Tops K X → Bool)
    (w : List Bool) {t out} (h : c.Exec (fun r => if r=input then w.map letter else []) t out) :
    ((haltMachine c input letter answer).run w (t+1)).state=.inl (answer (tops out)) := by
  have he := (exec_finite h).plug Sum.inl (.inr ()) (fun _ _ => rfl)
    (Execution.halt (tr:=haltTransition c answer) (q:=.inr ()) (s:=out) rfl)
  exact congrArg Config.state (he.iterate (haltMachine c input letter answer))
variable [Fintype K] [Fintype X]
 theorem haltOneTape_correct (c : Code K X) (input : K) (letter : Bool → X) (answer : Tops K X → Bool)
    (w : List Bool) {t out} (h : c.Exec (fun r => if r=input then w.map letter else []) t out) :
    (haltOneTape c input letter answer).toTM.halts w ∧
    (haltOneTape c input letter answer).toTM.time w≤8*(Fintype.card K+1)*(w.length+t+2)^2 ∧
    ((haltOneTape c input letter answer).toTM.accepts w ↔ answer (tops out)=true) := by
  have hr := haltMachine_run c input letter answer w h
  have he := (haltMachine c input letter answer).oneTape_correct w (t+1) (answer (tops out)) hr
  simpa only [haltOneTape,show w.length+(t+1)+1=w.length+t+2 by omega] using he
end WLTime.TypedStack.Code

namespace WLTime.TypedStack.Code
theorem Exec.of_decEq {K : Type uK} {X : Type uX} {i j : DecidableEq K} {c : Code K X} {s t out}
    (h : @Exec K X i c s t out) : @Exec K X j c s t out := by
  have he : i=j := Subsingleton.elim _ _
  cases he
  exact h
end WLTime.TypedStack.Code

namespace WLTime.RAMConsumer
open TypedStack
noncomputable section
variable {K : Type uK} [DecidableEq K] (A : RAM)
 attribute [local instance] OAI.WLTime.RAMConsumer.instDecidableEqReg
local instance instDecidableEqLetter_r093f74_1 : DecidableEq (Letter A) := Classical.decEq _
theorem prefix_exec (c : Code K Bool) (output : K) {s t out} (h : c.Exec s t out)
    (ys : List Bool) (ho : out output=ys.reverse) :
    (preludeCode A c output).Exec (Sum.elim (Code.listMap Sum.inl s) (fun _ => []))
      (t+(5*ys.length+1))
      (Sum.elim (Function.update (Code.listMap Sum.inl out) output []) (RAMAlphabet.inputState A ys)) := by
  have hc := Code.relabel_inl_exec
    (Code.mapLetters_exec Sum.inl (RAMAlphabet.decode A) (by intro b; rfl) h) (fun _ : RAMAlphabet.Reg A => [])
  have ht := Code.transfer_exec (Sum.inl output) (Sum.inr (.inl 0 : RAMAlphabet.Reg A)) (by simp)
    (.inl false : Letter A) (Sum.elim (Code.listMap Sum.inl out) (fun _ : RAMAlphabet.Reg A => []))
  have hf := Code.Exec.seq hc ht
  simp only [Sum.elim_inl,Sum.elim_inr] at hf
  have he : Function.update
      (Function.update (Sum.elim (Code.listMap Sum.inl out) (fun _ : RAMAlphabet.Reg A => [])) (.inl output) [])
        (.inr (.inl 0)) (((Code.listMap Sum.inl out) output).reverse++[])=
      Sum.elim (Function.update (Code.listMap Sum.inl out) output []) (RAMAlphabet.inputState A ys) := by
    funext r
    cases r with
    | inl r =>
      rw [Function.update_of_ne (show (Sum.inl r : Reg A K)≠.inr (.inl 0) from Sum.inl_ne_inr)]
      simp only [Function.update_apply,Sum.inl.injEq,Sum.elim_inl]
    | inr r =>
      simp only [Function.update_apply,Sum.inr.injEq,Sum.inr_ne_inl,ite_false,Sum.elim_inr,
        RAMAlphabet.inputState,Code.listMap,ho,List.map_reverse,List.reverse_reverse,List.append_nil]
      by_cases hr : r=(.inl 0 : RAMAlphabet.Reg A)
      · simp only [ite_eq_left hr]
      · simp only [ite_eq_right hr]
  rw [he] at hf
  simpa only [preludeCode,Code.listMap,Sum.elim_inl,Sum.elim_inr,ho,List.length_map,List.length_reverse] using hf
 theorem code_exec (c : Code K Bool) (input output : K) (n : ℕ) (w ys : List Bool)
    {t out} (he : c.Exec (fun r => if r=input then w else []) t out) (ho : out output=ys.reverse)
    (hfit : ys.length ≤ A.width.bits n*2^(A.width.bits n)) (hh : A.halts n ys) :
    ∃u  ≤ t+5*ys.length+RAMAlphabet.budget A (A.width.bits n) ys.length (A.time n ys)+1,∃last b,
      (code A c output (A.width.bits n)).Exec (fun r => if r=.inl input then w.map Sum.inl else []) u last ∧
      answer A (tops last)=(!b) ∧ (b=true ↔ A.accepts n ys) := by
  obtain ⟨v,hv,b,last,hg,ha,hb⟩ := RAMAlphabet.program_exec A n ys hfit hh
  have hg' : (RAMAlphabet.program A (A.width.bits n)).Exec (RAMAlphabet.inputState A ys) v last := Code.Exec.of_decEq hg
  have hf := Code.Exec.seq (prefix_exec A c output he ys ho)
    (Code.relabel_inr_exec hg'  (Function.update (Code.listMap Sum.inl out) output []))
  have hs : Sum.elim (Code.listMap (Sum.inl : Bool → Letter A) (fun r => if r=input then w else []))
      (fun _ : RAMAlphabet.Reg A => [])=(fun r => if r=.inl input then w.map Sum.inl else []) := by
    funext r
    cases r with
    | inl r =>
      by_cases hr : r=input
      · simp only [Code.listMap,Sum.elim_inl,Sum.inl.injEq,ite_eq_left hr]
      · simp only [Code.listMap,Sum.elim_inl,Sum.inl.injEq,ite_eq_right hr,List.map_nil]
    | inr r => simp only [Sum.elim_inr,Sum.inr_ne_inl,ite_false]
  rw [hs] at hf
  refine ⟨t+(5*ys.length+1)+v,by omega,_,b,hf,?_,hb⟩
  simp only [answer,tops,Sum.elim_inr,ha,List.head?_cons,Option.map_some,Option.getD_some,RAMAlphabet.decode]
variable [Fintype K]
 theorem correct (c : Code K Bool) (input output : K) (n : ℕ) (w ys : List Bool)
    {t out} (he : c.Exec (fun r => if r=input then w else []) t out) (ho : out output=ys.reverse)
    (hfit : ys.length ≤ A.width.bits n*2^(A.width.bits n)) (hh : A.halts n ys) :
    (oneTape A c input output n).toTM.halts w ∧
    (oneTape A c input output n).toTM.time w ≤
      8*(Fintype.card K+Fintype.card (RAMAlphabet.Reg A)+1)*
        (w.length+t+5*ys.length+RAMAlphabet.budget A (A.width.bits n) ys.length (A.time n ys)+3)^2 ∧
    ((oneTape A c input output n).toTM.accepts w ↔ ¬A.accepts n ys) := by
  obtain ⟨u,hu,last,b,hc,ha,hb⟩ := code_exec A c input output n w ys he ho hfit hh
  obtain ⟨ht,htime,hans⟩ := Code.haltOneTape_correct (code A c output (A.width.bits n)) (.inl input) Sum.inl (answer A) w hc
  refine ⟨ht,htime.trans ?_,hans.trans ?_⟩
  · simp only [Reg,Fintype.card_sum]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  · rw [ha]
    cases b <;> simp_all
end
end WLTime.RAMConsumer

namespace WLTime.OneTape.Symbolic.RAMWriter
open TypedStack
open scoped Classical
noncomputable section
variable (U : OneTape) (d q : ℕ) (A : RAM)
 theorem correct_oai (n : ℕ) (w : List Bool) (hm : 1 ≤ w.length) (hr : 2 ≤ d+q)
    (hn : baseOrder U d q w.length ≤ n)
    (ys : List Bool) (hys : ys=encodePair (pairGraph U d q hr w (n-baseOrder U d q w.length) 0)
      (pairGraph U d q hr w (n-baseOrder U d q w.length) 1))
    (hh : A.halts n ys) :
    (consumer U d q A n).toTM.halts w ∧
    (consumer U d q A n).toTM.time w ≤ consumerFactor U d q A*
      (w.length+FullWriter.budget U d q n w.length+5*ys.length+
        RAMAlphabet.budget A (A.width.bits n) ys.length (A.time n ys)+3)^2 ∧
    ((consumer U d q A n).toTM.accepts w ↔ ¬A.accepts n ys) := by
  have hgn : (listing U d q (d+q+2) w (n-baseOrder U d q w.length)).items.length=n := by
    rw [listing_length,Nat.add_sub_of_le hn]
  have hfit := A.input_fits _ (pairGraph U d q hr w (n-baseOrder U d q w.length) 0)
    (pairGraph U d q hr w (n-baseOrder U d q w.length) 1)
  have hfit' : ys.length ≤ A.width.bits n*2^(A.width.bits n) := by
    simpa only [hys,hgn] using hfit
  obtain ⟨t,ht,out,he,ho⟩ := FullWriter.code_correct U d q n w hm hr hn
  rw [←hys] at ho
  have hc := RAMConsumer.correct A (FullWriter.program U d q n).code (.inr FullWriter.Reg.word) (.inr FullWriter.Reg.output) n w ys he ho hfit' hh
  refine ⟨hc.1,hc.2.1.trans ?_,hc.2.2⟩
  have hs := FullWriter.scratch_le U d q n
  rw [Fintype.card_sum,Fintype.card_fin,FullWriter.card_reg]
  exact Nat.mul_le_mul (by unfold consumerFactor; omega) (Nat.pow_le_pow_left (by omega) 2)
end
end WLTime.OneTape.Symbolic.RAMWriter

end OAI
end

theorem solution : type_of% @OAI.WLTime.OneTape.Symbolic.RAMWriter.correct_oai := @OAI.WLTime.OneTape.Symbolic.RAMWriter.correct_oai

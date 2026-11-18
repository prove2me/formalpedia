-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.padded_residual_multitape
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:02:54.863675+00:00
-- url     : https://prove2.me/submissions/d7018258-c4e1-4773-907a-ace2a9c7e719

import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Bounds
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
import Definitions.Def_QAdvFew_PoQOracle_tup
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_StudentTeacher976_Adaptivity_Complexity
set_option autoImplicit false
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

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeBinary
open Turing QAdvFew.PoQOracle

 def tracks (g : ℕ) := 2*(g+2)+1
 def workSlot (g : ℕ) (j : Fin (g+2)) : Fin (tracks g) := ⟨j.val, by unfold tracks; omega⟩
 def querySlot (g : ℕ) (j : Fin (g+2)) : Fin (tracks g) := ⟨g+2+j.val, by unfold tracks; omega⟩
 def originSlot (g : ℕ) : Fin (tracks g) := ⟨2*(g+2), by unfold tracks; omega⟩

 def oneHot (g : ℕ) (a : Fin (g+3)) (j : Fin (g+2)) : Option Bool :=
   if a.val = j.val+1 then some true else none

 theorem oneHot_injective (g : ℕ) : Function.Injective (oneHot g) := by
   intro a b h
   apply Fin.ext
   by_cases ha : a.val = 0
   · by_cases hb : b.val = 0
     · omega
     · let j : Fin (g+2) := ⟨b.val-1, by omega⟩
       have he := congrArg (fun f => f j) h
       have ha' : a.val ≠ j.val+1 := by dsimp [j]; omega
       have hb' : b.val = j.val+1 := by dsimp [j]; omega
       simp [oneHot, ha', hb'] at he
   · let j : Fin (g+2) := ⟨a.val-1, by omega⟩
     have he := congrArg (fun f => f j) h
     have ha' : a.val = j.val+1 := by dsimp [j]; omega
     have hb' : b.val = j.val+1 := by
       by_contra hh
       simp [oneHot, ha', hh] at he
     omega

 noncomputable def decode (g : ℕ) (f : Fin (g+2) → Option Bool) : Fin (g+3) := by
   classical
   exact if h : ∃ a, oneHot g a = f then h.choose else 0

 theorem decode_oneHot (g : ℕ) (a : Fin (g+3)) : decode g (oneHot g a) = a := by
   classical
   have h : ∃ b, oneHot g b = oneHot g a := ⟨a, rfl⟩
   unfold decode
   rw [dif_pos h]
   exact oneHot_injective g h.choose_spec

 @[simp] theorem oneHot_zero (g : ℕ) (j : Fin (g+2)) : oneHot g 0 j = none := by
   unfold oneHot
   rw [if_neg (by simp <;> omega)]

 def direction (m : Fin 3) : SignType := if m = 0 then .neg else if m = 1 then .zero else .pos

 theorem direction_cast (m : Fin 3) : (direction m).cast (α := ℤ) = (m.val : ℤ)-1 := by
   fin_cases m <;> rfl

 inductive State (k : ℕ)
   | initial | copy | rewind | run (q : Fin (k+6))
   deriving DecidableEq, Fintype

 def moves (g : ℕ) (wm qm : SignType) (i : Fin (tracks g)) : SignType :=
   if i.val < g+2 then wm else if i.val < 2*(g+2) then qm else wm

 def movingAction (g k : ℕ) (next : Option (State k)) (wm qm : SignType) : Action (tracks g) Bool (State k) where
   inputTape := 0
   workTapes := fun i => (none, moves g wm qm i)
   output := none
   state := next

 def writeAction (g k : ℕ) (next : Option (State k)) (out : Option Bool)
     (wa qa : Fin (g+3)) (im wm qm : SignType) : Action (tracks g) Bool (State k) where
   inputTape := im
   workTapes := fun i =>
     if hw : i.val < g+2 then (some (oneHot g wa ⟨i.val, hw⟩), wm)
     else if hq : i.val < 2*(g+2) then (some (oneHot g qa ⟨i.val-(g+2), by omega⟩), qm)
     else (none, wm)
   output := out
   state := next

 def resultState {k : ℕ} (q : Fin (k+6)) : Option (State k) :=
   if q = 1 ∨ q = 2 then none else some (.run q)

 def resultBit {k : ℕ} (q : Fin (k+6)) : Option Bool :=
   if q = 1 then some true else if q = 2 then some false else none

 noncomputable def machine (V : OTM) : MultiTapeTM (tracks V.g) Bool (State V.k) :=
   MultiTapeTM.ofTr .initial fun s input read => match s with
     | .initial =>
       { inputTape := 0
         workTapes := fun i => (if i = originSlot V.g then some (some true) else none, 0)
         output := none
         state := some .copy }
     | .copy => match input with
       | some bit => writeAction V.g V.k (some .copy) none (OTM.symOf V.g bit) 0 .pos .pos .zero
       | none => movingAction V.g V.k (some .rewind) .zero .zero
     | .rewind => if read (originSlot V.g) = some true then movingAction V.g V.k (some (.run 0)) .zero .zero
       else movingAction V.g V.k (some .rewind) .neg .zero
     | .run q => if q = 3 then movingAction V.g V.k (some (.run 5)) .zero .zero
       else
         let wa := decode V.g (fun j => read (workSlot V.g j))
         let qa := decode V.g (fun j => read (querySlot V.g j))
         let d := V.δ q wa qa
         writeAction V.g V.k (resultState d.1) (resultBit d.1) d.2.1 d.2.2.2.1
           .zero (direction d.2.2.1) (direction d.2.2.2.2)

end StudentTeacher976.Adaptivity.NativeBinary

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeBinary
open Turing QAdvFew.PoQOracle

 def encodedTapes (g : ℕ) (w q : ℤ → Fin (g+3)) (i : Fin (tracks g)) (z : ℤ) : Option Bool :=
   if hw : i.val < g+2 then oneHot g (w z) ⟨i.val, hw⟩
   else if hq : i.val < 2*(g+2) then oneHot g (q z) ⟨i.val-(g+2), by omega⟩
   else if z = 0 then some true else none

 def positions (g : ℕ) (wh qh : ℤ) (i : Fin (tracks g)) : ℤ :=
   if i.val < g+2 then wh else if i.val < 2*(g+2) then qh else wh

 def cfg (V : OTM) (x : List Bool) (s : Option (State V.k)) (ip : Fin (x.length+2))
     (w q : ℤ → Fin (V.g+3)) (wh qh : ℤ) (out : List Bool) : Turing.Cfg (tracks V.g) Bool (State V.k) x where
   state := s
   inputPos := ip
   workTapes := encodedTapes V.g w q
   workTapePos := positions V.g wh qh
   output := out

 theorem work_read (V : OTM) (x : List Bool) (s : Option (State V.k)) (ip : Fin (x.length+2))
     (w q : ℤ → Fin (V.g+3)) (wh qh : ℤ) (out : List Bool) (j : Fin (V.g+2)) :
     (cfg V x s ip w q wh qh out).workTapeSymbols (workSlot V.g j) = oneHot V.g (w wh) j := by
   simp [cfg, Turing.Cfg.workTapeSymbols, encodedTapes, positions, workSlot]

 theorem query_read (V : OTM) (x : List Bool) (s : Option (State V.k)) (ip : Fin (x.length+2))
     (w q : ℤ → Fin (V.g+3)) (wh qh : ℤ) (out : List Bool) (j : Fin (V.g+2)) :
     (cfg V x s ip w q wh qh out).workTapeSymbols (querySlot V.g j) = oneHot V.g (q qh) j := by
   have hlo : ¬ V.g+2+j.val < V.g+2 := by omega
   have hhi : V.g+2+j.val < 2*(V.g+2) := by omega
   simp [cfg, Turing.Cfg.workTapeSymbols, encodedTapes, positions, querySlot, hlo, hhi]

 theorem origin_read (V : OTM) (x : List Bool) (s : Option (State V.k)) (ip : Fin (x.length+2))
     (w q : ℤ → Fin (V.g+3)) (wh qh : ℤ) (out : List Bool) :
     (cfg V x s ip w q wh qh out).workTapeSymbols (originSlot V.g) =
       if wh = 0 then some true else none := by
   have hlo : ¬ 2*(V.g+2) < V.g+2 := by omega
   simp [cfg, Turing.Cfg.workTapeSymbols, encodedTapes, positions, originSlot, hlo]

 theorem oneHot_update (g : ℕ) (w : ℤ → Fin (g+3)) (p : ℤ) (a : Fin (g+3)) (j : Fin (g+2)) :
     (fun z => oneHot g (Function.update w p a z) j) =
       Function.update (fun z => oneHot g (w z) j) p (oneHot g a j) := by
   funext z
   by_cases h : z = p <;> simp [Function.update, h]

 theorem encoded_work_region (g : ℕ) (w q : ℤ → Fin (g+3)) (i : Fin (tracks g))
     (hw : i.val < g+2) : encodedTapes g w q i = fun z => oneHot g (w z) ⟨i.val, hw⟩ := by
   funext z
   unfold encodedTapes
   rw [dif_pos hw]

 theorem encoded_query_region (g : ℕ) (w q : ℤ → Fin (g+3)) (i : Fin (tracks g))
     (hw : ¬ i.val < g+2) (hq : i.val < 2*(g+2)) :
     encodedTapes g w q i = fun z => oneHot g (q z) ⟨i.val-(g+2), by omega⟩ := by
   funext z
   unfold encodedTapes
   rw [dif_neg hw, dif_pos hq]

 theorem encoded_origin_region (g : ℕ) (w q : ℤ → Fin (g+3)) (i : Fin (tracks g))
     (hw : ¬ i.val < g+2) (hq : ¬ i.val < 2*(g+2)) :
     encodedTapes g w q i = fun z => if z = 0 then some true else none := by
   funext z
   unfold encodedTapes
   rw [dif_neg hw, dif_neg hq]

 theorem apply_write (V : OTM) (x : List Bool) (s next : Option (State V.k)) (ip : Fin (x.length+2))
     (w q : ℤ → Fin (V.g+3)) (wh qh : ℤ) (out : List Bool) (outBit : Option Bool)
     (wa qa : Fin (V.g+3)) (im wm qm : SignType) :
     (writeAction V.g V.k next outBit wa qa im wm qm).apply (cfg V x s ip w q wh qh out) =
       cfg V x next (moveInputPos ip im) (Function.update w wh wa) (Function.update q qh qa)
         (wh+wm.cast) (qh+qm.cast) (out++outBit.toList) := by
   apply Turing.Cfg.ext
   · rfl
   · rfl
   · funext i
     by_cases hw : i.val < V.g+2
     · simp only [Action.apply, writeAction, cfg, positions, hw, ↓reduceDIte, ↓reduceIte]
       rw [encoded_work_region V.g w q i hw,
         encoded_work_region V.g (Function.update w wh wa) (Function.update q qh qa) i hw]
       exact (oneHot_update _ _ _ _ _).symm
     · by_cases hq : i.val < 2*(V.g+2)
       · simp only [Action.apply, writeAction, cfg, positions, hw, hq, ↓reduceDIte, ↓reduceIte]
         rw [encoded_query_region V.g w q i hw hq,
           encoded_query_region V.g (Function.update w wh wa) (Function.update q qh qa) i hw hq]
         exact (oneHot_update _ _ _ _ _).symm
       · simp only [Action.apply, writeAction, cfg, positions, hw, hq, ↓reduceDIte, ↓reduceIte]
         rw [encoded_origin_region V.g w q i hw hq,
           encoded_origin_region V.g (Function.update w wh wa) (Function.update q qh qa) i hw hq]
   · funext i
     by_cases hw : i.val < V.g+2
     · simp only [Action.apply, writeAction, cfg, positions, hw, ↓reduceDIte, ↓reduceIte]
     · by_cases hq : i.val < 2*(V.g+2) <;>
         simp only [Action.apply, writeAction, cfg, positions, hw, hq, ↓reduceDIte, ↓reduceIte]
   · rfl

 theorem apply_moving (V : OTM) (x : List Bool) (s next : Option (State V.k)) (ip : Fin (x.length+2))
     (w q : ℤ → Fin (V.g+3)) (wh qh : ℤ) (out : List Bool) (wm qm : SignType) :
     (movingAction V.g V.k next wm qm).apply (cfg V x s ip w q wh qh out) =
       cfg V x next ip w q (wh+wm.cast) (qh+qm.cast) out := by
   apply Turing.Cfg.ext
   · rfl
   · simp [Action.apply, movingAction, cfg]
   · rfl
   · funext i
     by_cases hw : i.val < V.g+2
     · simp [Action.apply, movingAction, cfg, positions, moves, hw]
     · by_cases hq : i.val < 2*(V.g+2) <;>
         simp [Action.apply, movingAction, cfg, positions, moves, hw, hq]
   · simp [Action.apply, movingAction, cfg]

end StudentTeacher976.Adaptivity.NativeBinary

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeBinary
open Turing QAdvFew.PoQOracle

 def rightPos (x : List Bool) : Fin (x.length+2) := ⟨x.length+1, by omega⟩

 def encode (V : OTM) (x : List Bool) (c : V.Cfg) : Turing.Cfg (tracks V.g) Bool (State V.k) x :=
   cfg V x (resultState c.state) (rightPos x) c.work c.query c.wh c.qh (resultBit c.state).toList

 theorem encoded_work (V : OTM) (x : List Bool) (c : V.Cfg) :
     decode V.g (fun j => (encode V x c).workTapeSymbols (workSlot V.g j)) = c.work c.wh := by
   simp only [encode, work_read]
   exact decode_oneHot _ _

 theorem encoded_query (V : OTM) (x : List Bool) (c : V.Cfg) :
     decode V.g (fun j => (encode V x c).workTapeSymbols (querySlot V.g j)) = c.query c.qh := by
   simp only [encode, query_read]
   exact decode_oneHot _ _

 theorem encode_step (V : OTM) (x : List Bool) (c : V.Cfg) :
     (machine V).step (encode V x c) = encode V x (V.step (fun _ => false) c) := by
   by_cases h1 : c.state = 1
   · have hc : (encode V x c).state = none := by simp [encode, cfg, resultState, h1]
     rw [MultiTapeTM.step_of_halt hc]
     simp [OTM.step, h1]
   by_cases h2 : c.state = 2
   · have hc : (encode V x c).state = none := by simp [encode, cfg, resultState, h2]
     rw [MultiTapeTM.step_of_halt hc]
     simp [OTM.step, h2]
   have hstate : (encode V x c).state = some (.run c.state) := by simp [encode, cfg, resultState, h1, h2]
   have hbit : resultBit c.state = none := by simp [resultBit, h1, h2]
   rw [MultiTapeTM.step_of_state hstate]
   by_cases h3 : c.state = 3
   · have hn : V.step (fun _ => false) c = {c with state := 5} := by
       have hh : ¬ (c.state = 1 ∨ c.state = 2) := by simp [h1,h2]
       unfold OTM.step
       rw [if_neg hh, if_pos h3]
       rfl
     simp only [machine, MultiTapeTM.tr_ofTr, h3, ↓reduceIte]
     rw [encode, apply_moving, hn]
     simp (disch := omega) [encode, resultState, resultBit, cfg, hbit, h3, Fin.ext_iff, Nat.mod_eq_of_lt]
   · simp only [machine, MultiTapeTM.tr_ofTr, h3, ↓reduceIte, encoded_work, encoded_query]
     have hh : ¬ (c.state = 1 ∨ c.state = 2) := by simp [h1,h2]
     rw [OTM.Precheck.normal_step V (fun _ => false) c hh h3 _ _ _ _ _ rfl]
     simp only [encode, hbit, Option.toList_none]
     rw [apply_write]
     simp only [moveInputPos_zero, direction_cast, List.nil_append]
     let d := V.δ c.state (c.work c.wh) (c.query c.qh)
     change cfg V x (resultState d.1) (moveInputPos (rightPos x) (0 : SignType))
       (Function.update c.work c.wh d.2.1) (Function.update c.query c.qh d.2.2.2.1)
       (c.wh+((d.2.2.1.val : ℤ)-1)) (c.qh+((d.2.2.2.2.val : ℤ)-1)) (resultBit d.1).toList =
       cfg V x (resultState d.1) (rightPos x)
         (Function.update c.work c.wh d.2.1) (Function.update c.query c.qh d.2.2.2.1)
         (c.wh+(d.2.2.1.val : ℤ)-1) (c.qh+(d.2.2.2.2.val : ℤ)-1) (resultBit d.1).toList
     rw [moveInputPos_zero]
     congr 1 <;> omega

 theorem encode_iterate (V : OTM) (x : List Bool) (c : V.Cfg) (t : ℕ) :
     (machine V).step^[t] (encode V x c) = encode V x ((V.step (fun _ => false))^[t] c) := by
   induction t with
   | zero => rfl
   | succ t ih =>
     rw [Function.iterate_succ_apply', ih, encode_step, Function.iterate_succ_apply']

end StudentTeacher976.Adaptivity.NativeBinary

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeBinary
open Turing QAdvFew.PoQOracle

 def partialInput (g : ℕ) (x : List Bool) (p : ℕ) (z : ℤ) : Fin (g+3) :=
   if 0 ≤ z ∧ z < p then OTM.symOf g (x.getD z.toNat false) else 0

 @[simp] theorem partialInput_zero (g : ℕ) (x : List Bool) : partialInput g x 0 = fun _ => 0 := by
   funext z
   unfold partialInput
   rw [if_neg (by omega)]

 theorem partialInput_update (g : ℕ) (x : List Bool) (p : ℕ) :
     Function.update (partialInput g x p) (p : ℤ) (OTM.symOf g (x.getD p false)) = partialInput g x (p+1) := by
   funext z
   by_cases hz : z = p
   · subst z; simp [partialInput]
   · rw [Function.update_of_ne hz]
     unfold partialInput
     have heq : (0 ≤ z ∧ z < (p : ℤ)) ↔ (0 ≤ z ∧ z < (p+1 : ℕ)) := by omega
     simp only [heq]

 theorem partialInput_complete (V : OTM) (x : List Bool) : partialInput V.g x x.length = (V.init x).work := rfl

 def copyCfg (V : OTM) (x : List Bool) (p : ℕ) (hp : p ≤ x.length) :
     Turing.Cfg (tracks V.g) Bool (State V.k) x :=
   cfg V x (some .copy) ⟨p+1, by omega⟩ (partialInput V.g x p) (fun _ => 0) p 0 []

 theorem initial_step (V : OTM) (x : List Bool) :
     (machine V).step ((machine V).initCfg x) = copyCfg V x 0 (by omega) := by
   rw [MultiTapeTM.step_of_state (q := State.initial) rfl]
   simp only [machine, MultiTapeTM.tr_ofTr]
   apply Turing.Cfg.ext
   · rfl
   · simp [Action.apply, MultiTapeNTM.initCfg, Turing.Cfg.init, copyCfg, cfg]
   · funext i z
     by_cases hw : i.val < V.g+2
     · have hno : i ≠ originSlot V.g := by intro h; have he := congrArg Fin.val h; dsimp [originSlot] at he; omega
       simp [Action.apply, MultiTapeNTM.initCfg, Turing.Cfg.init, copyCfg, cfg, encodedTapes,
         partialInput_zero, oneHot_zero, hno, hw]
     · by_cases hq : i.val < 2*(V.g+2)
       · have hno : i ≠ originSlot V.g := by intro h; have he := congrArg Fin.val h; dsimp [originSlot] at he; omega
         simp [Action.apply, MultiTapeNTM.initCfg, Turing.Cfg.init, copyCfg, cfg, encodedTapes,
           partialInput_zero, oneHot_zero, hno, hw, hq]
       · have heq : i = originSlot V.g := by
           apply Fin.ext
           dsimp [originSlot]
           have hi := i.isLt
           unfold tracks at hi
           omega
         subst i
         simp [Action.apply, MultiTapeNTM.initCfg, Turing.Cfg.init, copyCfg, cfg, encodedTapes,
           originSlot, Function.update, hw, hq]
   · funext i
     by_cases hw : i.val < V.g+2 <;> by_cases hq : i.val < 2*(V.g+2) <;>
       simp [Action.apply, MultiTapeNTM.initCfg, Turing.Cfg.init, copyCfg, cfg, positions, hw, hq]
   · rfl

 theorem copy_step (V : OTM) (x : List Bool) (p : ℕ) (hp : p < x.length) :
     (machine V).step (copyCfg V x p (by omega)) = copyCfg V x (p+1) (by omega) := by
   have hin : (copyCfg V x p (by omega)).inputSymbol = some (x.getD p false) := by
     have hi : (copyCfg V x p (by omega)).inputPos.val = 1+p := by simp [copyCfg, cfg]; omega
     rw [List.getD_eq_getElem _ _ hp]
     exact inputSymbolInner (cfg := copyCfg V x p (by omega)) p hi hp
   rw [MultiTapeTM.step_of_state (q := State.copy) rfl]
   simp only [machine, MultiTapeTM.tr_ofTr, hin]
   simp only [copyCfg]
   rw [apply_write, partialInput_update]
   have hip : moveInputPos (⟨p+1, by omega⟩ : Fin (x.length+2)) SignType.pos = ⟨(p+1)+1, by omega⟩ :=
     moveInputPos_pos_of_ne_right _ (by simp; omega)
   rw [hip]
   simp

 theorem copy_run (V : OTM) (x : List Bool) (p : ℕ) (hp : p ≤ x.length) :
     (machine V).runFrom (copyCfg V x 0 (by omega)) p = copyCfg V x p hp := by
   induction p with
   | zero => rfl
   | succ p ih =>
     rw [MultiTapeTM.runFrom, Function.iterate_succ_apply']
     change (machine V).step ((machine V).runFrom (copyCfg V x 0 (by omega)) p) = _
     rw [ih (by omega)]
     exact copy_step V x p (by omega)

 def rewindCfg (V : OTM) (x : List Bool) (t : ℕ) : Turing.Cfg (tracks V.g) Bool (State V.k) x :=
   cfg V x (some .rewind) (rightPos x) (V.init x).work (fun _ => 0) ((x.length : ℤ)-t) 0 []

 theorem copy_end (V : OTM) (x : List Bool) :
     (machine V).step (copyCfg V x x.length le_rfl) = rewindCfg V x 0 := by
   have hin : (copyCfg V x x.length le_rfl).inputSymbol = none := by
     apply inputSymbol_eq_none_of_boundary
     exact Or.inr rfl
   rw [MultiTapeTM.step_of_state (q := State.copy) rfl]
   simp only [machine, MultiTapeTM.tr_ofTr]
   rw [hin]
   simp only [copyCfg]
   rw [apply_moving, partialInput_complete]
   simp [rewindCfg, rightPos]

 theorem rewind_step (V : OTM) (x : List Bool) (t : ℕ) (ht : t < x.length) :
     (machine V).step (rewindCfg V x t) = rewindCfg V x (t+1) := by
   have hpos : (x.length : ℤ)-t ≠ 0 := by omega
   rw [MultiTapeTM.step_of_state (q := State.rewind) rfl]
   simp only [machine, MultiTapeTM.tr_ofTr, rewindCfg, origin_read, hpos, ↓reduceIte, reduceCtorEq]
   rw [apply_moving]
   simp
   congr 1 <;> omega

 theorem rewind_run (V : OTM) (x : List Bool) :
     (machine V).runFrom (rewindCfg V x 0) x.length = rewindCfg V x x.length := by
   have hh : ∀ t ≤ x.length, (machine V).runFrom (rewindCfg V x 0) t = rewindCfg V x t := by
     intro t ht
     induction t with
     | zero => rfl
     | succ t ih =>
       rw [MultiTapeTM.runFrom, Function.iterate_succ_apply']
       change (machine V).step ((machine V).runFrom (rewindCfg V x 0) t) = _
       rw [ih (by omega)]
       exact rewind_step V x t (by omega)
   exact hh x.length le_rfl

 theorem rewind_end (V : OTM) (x : List Bool) :
     (machine V).step (rewindCfg V x x.length) = encode V x (V.init x) := by
   rw [MultiTapeTM.step_of_state (q := State.rewind) rfl]
   simp only [machine, MultiTapeTM.tr_ofTr, rewindCfg, origin_read, sub_self, ↓reduceIte]
   rw [apply_moving]
   simp (disch := omega) [encode, OTM.init, resultState, resultBit, Fin.ext_iff, Nat.mod_eq_of_lt]

end StudentTeacher976.Adaptivity.NativeBinary

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeBinary
open Turing QAdvFew.PoQOracle

 theorem prefix_run (V : OTM) (x : List Bool) :
     (machine V).runFrom ((machine V).initCfg x) (2*x.length+3) = encode V x (V.init x) := by
   have htime : 2*x.length+3 = (((1+x.length)+1)+x.length)+1 := by omega
   rw [htime, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
     MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add]
   simp only [MultiTapeTM.runFrom_one]
   rw [initial_step, copy_run V x x.length le_rfl, copy_end, rewind_run, rewind_end]

 theorem full_run (V : OTM) (x : List Bool) (t : ℕ) :
     (machine V).runFrom ((machine V).initCfg x) (2*x.length+3+t) =
       encode V x (V.runCfg (fun _ => false) x t) := by
   rw [MultiTapeTM.runFrom_add, prefix_run]
   exact encode_iterate V x (V.init x) t

 theorem halt_of_result (V : OTM) (x : List Bool) (t : ℕ)
     (ht : (V.result (fun _ => false) x t).isSome) :
     ((machine V).runFrom ((machine V).initCfg x) (2*x.length+3+t)).Halted := by
   rw [full_run]
   change resultState (V.runCfg (fun _ => false) x t).state = none
   change (resultBit (V.runCfg (fun _ => false) x t).state).isSome at ht
   unfold resultBit at ht
   split_ifs at ht with h1 h2
   · simp [resultState, h1]
   · simp [resultState, h2]
   · simp at ht

 theorem output_of_result (V : OTM) (x : List Bool) (t : ℕ)
     (ht : (V.result (fun _ => false) x t).isSome) :
     ((machine V).runFrom ((machine V).initCfg x) (2*x.length+3+t)).output =
       [(V.result (fun _ => false) x t).getD false] := by
   rw [full_run]
   change (V.result (fun _ => false) x t).toList = _
   cases he : V.result (fun _ => false) x t with
   | none => simp [he] at ht
   | some b => rfl

 theorem native_polytime (V : OTM) (clock : Polynomial ℕ)
     (ht : ∀ x : List Bool, (V.result (fun _ => false) x (clock.eval x.length)).isSome) :
     MultiTapeTM.ComputableInPolyTime
       (fun x : List Bool => (V.result (fun _ => false) x (clock.eval x.length)).getD false)
       MultiTapeTM.encBits MultiTapeTM.encBool := by
   let t : ℕ → ℕ := fun n => 2*n+3+clock.eval n
   have hpoly : Cslib.PolynomiallyBounded t := by
     dsimp [t]
     fun_prop
   apply MultiTapeTM.ComputableInTimeAndSpace.computableInPolyTime hpoly
   refine ⟨tracks V.g, State V.k, inferInstance, machine V, fun x => ?_⟩
   have hh := halt_of_result V x (clock.eval x.length) (ht x)
   have ho := output_of_result V x (clock.eval x.length) (ht x)
   refine ⟨⟨t x.length, hh, ho⟩, MultiTapeTM.runsInTime_of_halted hh,
     MultiTapeTM.runsInSpace_of_halted hh le_rfl⟩

end StudentTeacher976.Adaptivity.NativeBinary

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.TupleCodec
open Turing.MultiTapeTM QAdvFew.PoQOracle

 def converter : Transducer Bool (Option Bool) where
   q₀ := none
   step
     | none, b => (some b, [])
     | some true, b => (none, [true,b])
     | some false, _ => (none, [false])
   final _ := []
   length_step_le q b := by cases q with
     | none => simp
     | some a => cases a <;> simp
   length_final_le _ := by simp

 theorem convert_nil : converter.run none [] = [] := rfl
 theorem convert_pair (a b : Bool) (w : List Bool) :
     converter.run none (a::b::w) = (if a then [true,b] else [false]) ++ converter.run none w := by
   cases a <;> rfl

 theorem convert_encoded (w v : List Bool) :
     converter.run none (w.flatMap (fun b => [true,b]) ++ [false,false] ++ v) =
       frame w ++ converter.run none v := by
   induction w with
   | nil => rfl
   | cons b w ih =>
     change true::b::converter.run none (w.flatMap (fun b => [true,b]) ++ [false,false] ++ v) =
       true::b::(frame w ++ converter.run none v)
     rw [ih]

 theorem convert_tup (ws : List (List Bool)) : converter.run none (tup ws) = encList encBits ws := by
   induction ws with
   | nil => rfl
   | cons w ws ih =>
     simp only [tup, List.flatMap_cons] at *
     rw [convert_encoded, ih, encList_cons]
     rfl

 def decodeTuple (w : List Bool) : List (List Bool) := frames (converter.run none w)

 theorem decode_tup (ws : List (List Bool)) : decodeTuple (tup ws) = ws := by
   rw [decodeTuple, convert_tup, frames_encList]
   exact List.map_id ws

 theorem converter_poly : ComputableInPolyTime (converter.run none) encBits encBits := by
   have htm (w : List Bool) := converter.computesInTimeAndSpace_toTM w
   apply ComputableInTimeAndSpace.computableInPolyTime (t := fun n => 2*n+3) (by fun_prop)
   refine ⟨0, _, inferInstance, converter.toTM, fun w => ?_⟩
   exact htm w

 theorem decoder_poly : ComputableInPolyTime decodeTuple encBits (encList encBits) := by
   exact computableInDegree_frames.computableInPolyTime.comp converter_poly

 def encoder : Transducer Bool Bool where
   q₀ := false
   step
     | false, true => (true, [true])
     | false, false => (false, [false,false])
     | true, b => (false, [b])
   final _ := []
   length_step_le q b := by cases q <;> cases b <;> simp
   length_final_le _ := by simp

 theorem encoder_frame (w v : List Bool) : encoder.run false (frame w ++ v) =
     (w.flatMap (fun b => [true,b]) ++ [false,false]) ++ encoder.run false v := by
   induction w with
   | nil => rfl
   | cons b w ih =>
     change true::b::encoder.run false (frame w ++ v) =
       true::b::((w.flatMap (fun b => [true,b]) ++ [false,false]) ++ encoder.run false v)
     rw [ih]

 theorem encoder_list (ws : List (List Bool)) : encoder.run false (encList encBits ws) = tup ws := by
   induction ws with
   | nil => rfl
   | cons w ws ih =>
     rw [encList_cons]
     change encoder.run false (frame w ++ encList encBits ws) = _
     rw [encoder_frame, ih]
     rfl

 theorem encoder_raw_poly : ComputableInPolyTime (encoder.run false) encBits encBits := by
   apply ComputableInTimeAndSpace.computableInPolyTime (t := fun n => 2*n+3) (by fun_prop)
   exact ⟨0, _, inferInstance, encoder.toTM, fun w => encoder.computesInTimeAndSpace_toTM w⟩

 theorem encode_poly : ComputableTidilyInPolyTime tup (encList encBits) encBits := by
   have hh := encoder_raw_poly.tidy.comp (ComputableTidilyInPolyTime.encode (encList encBits))
   exact hh.of_enc_eq fun ws => (encoder_list ws).symm

end StudentTeacher976.Adaptivity.TupleCodec

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.PaddingMachine
open Turing.MultiTapeTM QAdvFew.PoQOracle
open TupleCodec

 def outer (w : List Bool) : List Bool := (decodeTuple w).headD []
 def rest (w : List Bool) : List (List Bool) := (decodeTuple w).tail
 def left (w : List Bool) : List Bool := (decodeTuple (outer w)).headD []
 def right (w : List Bool) : List Bool := (decodeTuple (outer w)).tail.headD []
 def trimmed (ps : List (Polynomial ℕ)) (w : List Bool) : List (List Bool) :=
   List.zipWith (fun n s => s.take n) (ps.map fun p => p.eval (left w).length) (rest w)
 def argument (ps : List (Polynomial ℕ)) (w : List Bool) : List Bool :=
   tup (left w :: right w :: trimmed ps w)
 def valid (w : List Bool) : Bool := outer w == tup [left w, right w]
 def result (V : OTM) (clock : Polynomial ℕ) (ps : List (Polynomial ℕ)) (w : List Bool) : Bool :=
   valid w && !(V.result (fun _ => false) (argument ps w) (clock.eval (argument ps w).length)).getD false

 theorem outer_poly : ComputableTidilyInPolyTime outer encBits encBits := by
   exact (ComputableTidilyInPolyTime.headD []).comp decoder_poly.tidy
 theorem rest_poly : ComputableTidilyInPolyTime rest encBits (encList encBits) := by
   exact (ComputableTidilyInPolyTime.tail (encA := encBits)).comp decoder_poly.tidy
 theorem left_poly : ComputableTidilyInPolyTime left encBits encBits := by
   exact (ComputableTidilyInPolyTime.headD []).comp (decoder_poly.tidy.comp outer_poly)
 theorem right_poly : ComputableTidilyInPolyTime right encBits encBits := by
   exact (ComputableTidilyInPolyTime.headD []).comp
     ((ComputableTidilyInPolyTime.tail (encA := encBits)).comp (decoder_poly.tidy.comp outer_poly))

 theorem bounds_poly (ps : List (Polynomial ℕ)) :
     ComputableTidilyInPolyTime (fun w => ps.map fun p => p.eval (left w).length) encBits (encList encUnary) := by
   apply ComputableTidilyInPolyTime.mapConst
   intro p hp
   exact (ComputableTidilyInPolyTime.unary_eval p).comp
     (ComputableTidilyInPolyTime.length_bits.comp left_poly)

 theorem trimmed_poly (ps : List (Polynomial ℕ)) :
     ComputableTidilyInPolyTime (trimmed ps) encBits (encList encBits) := by
   have hz := (ComputableTidilyInPolyTime.zip encUnary encBits).comp ((bounds_poly ps).prod rest_poly)
   have ht : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => p.2.take p.1)
       (encPair encUnary encBits) encBits := by fun_prop
   have hh := (ComputableTidilyInPolyTime.map ht).comp hz
   change ComputableTidilyInPolyTime (fun w => List.zipWith (fun n s => s.take n)
     (ps.map fun p => p.eval (left w).length) (rest w)) encBits (encList encBits)
   simp only [Function.comp_def, List.map_zip_eq_zipWith] at hh
   have he : Function.curry (fun p : ℕ × List Bool => p.2.take p.1) = (fun n s => s.take n) := rfl
   rw [he] at hh
   exact hh

 theorem argument_poly (ps : List (Polynomial ℕ)) :
     ComputableTidilyInPolyTime (argument ps) encBits encBits := by
   apply encode_poly.comp
   exact left_poly.cons' (right_poly.cons' (trimmed_poly ps))

 theorem valid_poly : ComputableTidilyInPolyTime valid encBits encBool := by
   apply ComputableTidilyInPolyTime.beq outer_poly
   apply encode_poly.comp
   exact left_poly.cons' (right_poly.cons' (ComputableTidilyInPolyTime.const []))

 theorem result_poly (V : OTM) (clock : Polynomial ℕ) (ps : List (Polynomial ℕ))
     (ht : ∀ w : List Bool, (V.result (fun _ => false) w (clock.eval w.length)).isSome) :
     ComputableInPolyTime (result V clock ps) encBits encBool := by
   exact ComputableInPolyTime.of_tidy (valid_poly.bool_and'
     (ComputableTidilyInPolyTime.bool_not.comp
       ((NativeBinary.native_polytime V clock ht).tidy.comp (argument_poly ps))))

end StudentTeacher976.Adaptivity.PaddingMachine

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.PaddingMachine
open QAdvFew.PoQOracle TupleCodec

 theorem getD_false_iff (o : Option Bool) : o.getD false = false ↔ ¬ o = some true := by
   cases o with
   | none => simp
   | some b => cases b <;> simp

 theorem argument_tup (ps : List (Polynomial ℕ)) (s : List Bool) (ys : List (List Bool)) :
     argument ps (tup (s::ys)) =
       tup (left (tup (s::ys)) :: right (tup (s::ys)) ::
         List.zipWith (fun n w => w.take n)
           (ps.map fun p => p.eval (left (tup (s::ys))).length) ys) := by
   simp [argument, trimmed, rest, decode_tup]

 theorem result_correct (V : OTM) (clock : Polynomial ℕ) (ps : List (Polynomial ℕ))
     (s : List Bool) (ys : List (List Bool)) :
     result V clock ps (tup (s :: ys)) = true ↔
       ∃ x y : List Bool, s = tup [x, y] ∧
         ¬ V.result (fun _ => false)
           (tup (x :: y :: List.zipWith (fun n w => w.take n) (ps.map fun p => p.eval x.length) ys))
           (clock.eval (tup (x :: y :: List.zipWith (fun n w => w.take n)
             (ps.map fun p => p.eval x.length) ys)).length) = some true := by
   simp only [result, Bool.and_eq_true, Bool.not_eq_true', getD_false_iff]
   constructor
   · rintro ⟨hv, hr⟩
     have he : s = tup [left (tup (s::ys)), right (tup (s::ys))] := by
       simpa [valid, outer, decode_tup] using hv
     refine ⟨left (tup (s::ys)), right (tup (s::ys)), he, ?_⟩
     rw [argument_tup] at hr
     exact hr
   · rintro ⟨x, y, rfl, hr⟩
     constructor
     · simp [valid, outer, left, right, decode_tup]
     · simpa [argument, trimmed, rest, left, right, outer, decode_tup] using hr

end StudentTeacher976.Adaptivity.PaddingMachine

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity
open Turing.MultiTapeTM

 theorem polytime_clock {f : List Bool → Bool}
     (hf : ComputableInPolyTime f encBits encBool) :
     ∃ (k : ℕ) (S : Type) (_ : Fintype S), ∃ M : Turing.MultiTapeTM k Bool S,
       ∃ p : Polynomial ℕ, ∀ w : List Bool,
         (M.runFrom (M.initCfg w) (p.eval w.length)).Halted ∧
         (M.runFrom (M.initCfg w) (p.eval w.length)).output = [f w] := by
   classical
   obtain ⟨t, s, ht, hs, k, S, hS, M, hM⟩ := hf
   letI : Finite S := hS
   letI : Fintype S := Fintype.ofFinite S
   obtain ⟨c, d, hbound⟩ := Cslib.polynomiallyBounded_iff_le.mp ht
   let p : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1)^d
   have hp (n : ℕ) : t n ≤ p.eval n := by
     simpa [p] using hbound n
   refine ⟨k, S, inferInstance, M, p, fun w => ?_⟩
   have hh := runsInTime_iff_halted.mp (hM w).2.1
   have he := runFrom_eq_of_halt M (M.initCfg w) (hp w.length) hh
   rw [he]
   refine ⟨hh, ?_⟩
   obtain ⟨u, hu, ho⟩ := (hM w).1
   change (M.runFrom (M.initCfg w) u).output = [f w] at ho
   rcases le_total u (t w.length) with hl | hl
   · rw [runFrom_eq_of_halt M (M.initCfg w) hl hu]
     exact ho
   · rw [runFrom_eq_of_halt M (M.initCfg w) hl hh] at ho
     exact ho

end StudentTeacher976.Adaptivity

set_option autoImplicit false
open QAdvFew.PoQOracle
open StudentTeacher976.Adaptivity

theorem solution (V : OTM) (clock : Polynomial ℕ) (ps : List (Polynomial ℕ))
    (htotal : ∀ s : Word, (V.result (fun _ => false) s (clock.eval s.length)).isSome) :
    ∃ (k : ℕ) (S : Type) (_ : Fintype S), ∃ M : Turing.MultiTapeTM k Bool S, ∃ bound : Polynomial ℕ,
      (∀ s : Word, (M.runFrom (M.initCfg s) (bound.eval s.length)).Halted) ∧
      ∀ (s : Word) (ys : List Word),
        (M.runFrom (M.initCfg (tup (s :: ys))) (bound.eval (tup (s :: ys)).length)).output.head?.getD false = true ↔
          ∃ x y : Word, s = tup [x, y] ∧
            ¬ V.result (fun _ => false)
              (tup (x :: y :: List.zipWith (fun n w => w.take n) (ps.map fun p => p.eval x.length) ys))
              (clock.eval (tup (x :: y :: List.zipWith (fun n w => w.take n)
                (ps.map fun p => p.eval x.length) ys)).length) = some true := by
  obtain ⟨k, S, hS, M, bound, hM⟩ := polytime_clock (PaddingMachine.result_poly V clock ps htotal)
  refine ⟨k, S, hS, M, bound, fun s => (hM s).1, ?_⟩
  intro s ys
  rw [(hM (tup (s::ys))).2]
  simpa only [List.head?_cons, Option.getD_some] using PaddingMachine.result_correct V clock ps s ys

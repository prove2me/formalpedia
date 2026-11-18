-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.auxiliary_test_protocol
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:39:31.165752+00:00
-- url     : https://prove2.me/submissions/a7816ab8-ee9a-4d14-a117-b8e5eb284fac

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_StudentTeacher976_Adaptivity_DFA
import Definitions.Def_StudentTeacher976_Adaptivity_Complexity
import Definitions.Def_StudentTeacher976_Adaptivity_OracleProtocol
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Bounds
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_StudentTeacher976_Adaptivity_Auxiliary
set_option autoImplicit false

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.FiniteCodec
open Turing.MultiTapeTM

 noncomputable def decode {α : Type} [Fintype α] [Inhabited α] (enc : α ↪ List Bool) (w : List Bool) : α := by
   classical
   exact ((Finset.univ.toList).find? fun a => enc a == w).getD default

 theorem decode_enc {α : Type} [Fintype α] [Inhabited α] (enc : α ↪ List Bool) (a : α) : decode enc (enc a) = a := by
   classical
   have hex : ((Finset.univ.toList).find? fun b => enc b == enc a).isSome := by
     apply List.find?_isSome.mpr
     exact ⟨a, by simp, by simp⟩
   unfold decode
   cases hf : (Finset.univ.toList.find? fun b => enc b == enc a) with
   | none => simp [hf] at hex
   | some b =>
     have hb : enc b = enc a := by simpa using List.find?_some hf
     have he := enc.injective hb
     simp [hf, he]

 theorem decode_poly {α : Type} [Fintype α] [Inhabited α] (enc : α ↪ List Bool) :
     ComputableTidilyInPolyTime (decode enc) encBits enc := by
   classical
   apply ComputableTidilyInPolyTime.optionGetDWithInput
   · apply ComputableTidilyInPolyTime.findWithInput (encA := enc)
     · exact ComputableTidilyInPolyTime.const Finset.univ.toList
     · apply ComputableTidilyInPolyTime.beq
       · exact (ComputableTidilyInPolyTime.encode enc).comp (ComputableTidilyInPolyTime.snd encBits enc)
       · exact ComputableTidilyInPolyTime.fst encBits enc
   · exact ComputableTidilyInPolyTime.const default

 noncomputable def decoder {α : Type} [Fintype α] [Inhabited α] (enc : α ↪ List Bool) : Decoder enc where
   decode := decode enc
   decode_enc := decode_enc enc
   computable := (ComputableInPolyTime.of_tidy (decode_poly enc)).exists_degree

 def encFin (n : ℕ) : Fin n ↪ List Bool where
   toFun := fun a => List.replicate a.val true
   inj' := by
     intro a b h
     apply Fin.ext
     simpa using congrArg List.length h

end StudentTeacher976.Adaptivity.FiniteCodec

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

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM

structure Simulation (M N : OTM) where
  states : Fin (M.k + 6) ↪ Fin (N.k + 6)
  symbols : Fin (M.g + 3) ↪ Fin (N.g + 3)
  accept : states 1 = 1
  reject : states 2 = 2
  queryState : states 3 = 3
  yes : states 4 = 4
  no : states 5 = 5
  blank : symbols 0 = 0
  bitFalse : symbols 1 = 1
  bitTrue : symbols 2 = 2
  transition : ∀ q a b,
    N.δ (states q) (symbols a) (symbols b) =
      let d := M.δ q a b
      (states d.1, symbols d.2.1, d.2.2.1, symbols d.2.2.2.1, d.2.2.2.2)

namespace Simulation
variable {M N : OTM} (E : Simulation M N)

private theorem state_accept (q : Fin (M.k + 6)) : E.states q = 1 ↔ q = 1 := by
  rw [← E.accept, E.states.injective.eq_iff]
private theorem state_reject (q : Fin (M.k + 6)) : E.states q = 2 ↔ q = 2 := by
  rw [← E.reject, E.states.injective.eq_iff]
private theorem state_query (q : Fin (M.k + 6)) : E.states q = 3 ↔ q = 3 := by
  rw [← E.queryState, E.states.injective.eq_iff]

 theorem bitOf_symbols (a : Fin (M.g + 3)) : bitOf (E.symbols a) = bitOf a := by
  have h1 : E.symbols a = 1 ↔ a = 1 := by rw [← E.bitFalse, E.symbols.injective.eq_iff]
  have h2 : E.symbols a = 2 ↔ a = 2 := by rw [← E.bitTrue, E.symbols.injective.eq_iff]
  simp only [bitOf, h1, h2]

 theorem readBits_symbols (tape : ℤ → Fin (M.g + 3)) (hi : ℤ) :
    readBits (fun i => E.symbols (tape i)) hi = readBits tape hi := by
  unfold readBits
  simp only [E.bitOf_symbols]

 def cfg (c : M.Cfg) : N.Cfg where
  state := E.states c.state
  work := fun i => E.symbols (c.work i)
  wh := c.wh
  query := fun i => E.symbols (c.query i)
  qh := c.qh
  wlo := c.wlo
  whi := c.whi
  qlo := c.qlo
  qhi := c.qhi

private theorem symbols_update (tape : ℤ → Fin (M.g + 3)) (pos : ℤ) (a : Fin (M.g + 3)) :
    (fun i => E.symbols (Function.update tape pos a i)) =
      Function.update (fun i => E.symbols (tape i)) pos (E.symbols a) := by
  funext i
  by_cases h : i = pos <;> simp [Function.update, h]

 theorem cfg_step (O : Oracle) (c : M.Cfg) : E.cfg (M.step O c) = N.step O (E.cfg c) := by
  dsimp only [step, cfg]
  simp only [E.state_accept, E.state_reject, E.state_query, E.readBits_symbols]
  by_cases hh : c.state = 1 ∨ c.state = 2
  · simp only [if_pos hh]
  · simp only [if_neg hh]
    by_cases hq : c.state = 3
    · simp only [if_pos hq]
      split <;> simp only [E.yes, E.no]
    · simp only [if_neg hq, E.transition, E.symbols_update]

 theorem cfg_iterate (O : Oracle) (c : M.Cfg) (t : ℕ) :
    E.cfg ((M.step O)^[t] c) = (N.step O)^[t] (E.cfg c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', E.cfg_step, ih]

 theorem cfg_init (x : List Bool) (hstart : E.states 0 = 0) : E.cfg (M.init x) = N.init x := by
  have hsym : ∀ b, E.symbols (symOf M.g b) = symOf N.g b := by
    intro b
    cases b <;> simp only [symOf, Bool.false_eq_true, ↓reduceIte, E.bitFalse, E.bitTrue]
  dsimp only [cfg, init]
  simp only [hstart, E.blank]
  congr 1
  funext i
  split <;> simp only [hsym, E.blank]

 theorem runCfg (O : Oracle) (x : List Bool) (t : ℕ) (hstart : E.states 0 = 0) :
    E.cfg (M.runCfg O x t) = N.runCfg O x t := by
  rw [OTM.runCfg, E.cfg_iterate, E.cfg_init x hstart]
  rfl

 theorem result (O : Oracle) (x : List Bool) (t : ℕ) (hstart : E.states 0 = 0) :
    N.result O x t = M.result O x t := by
  unfold OTM.result
  rw [← E.runCfg O x t hstart]
  dsimp only [cfg]
  simp only [E.state_accept, E.state_reject]

 theorem output (O : Oracle) (x : List Bool) (t : ℕ) (hstart : E.states 0 = 0) :
    N.output O x t = M.output O x t := by
  unfold OTM.output
  rw [← E.runCfg O x t hstart]
  exact E.readBits_symbols _ _

 theorem runCfg_after_prefix (O : Oracle) (x y : List Bool) (s t : ℕ)
    (hprefix : N.runCfg O x s = E.cfg (M.init y)) :
    N.runCfg O x (s + t) = E.cfg (M.runCfg O y t) := by
  unfold OTM.runCfg at *
  rw [Nat.add_comm s t, Function.iterate_add_apply, hprefix, ← E.cfg_iterate]

 theorem result_after_prefix (O : Oracle) (x y : List Bool) (s t : ℕ)
    (hprefix : N.runCfg O x s = E.cfg (M.init y)) :
    N.result O x (s + t) = M.result O y t := by
  unfold OTM.result
  rw [E.runCfg_after_prefix O x y s t hprefix]
  dsimp only [cfg]
  simp only [E.state_accept, E.state_reject]

 theorem output_after_prefix (O : Oracle) (x y : List Bool) (s t : ℕ)
    (hprefix : N.runCfg O x s = E.cfg (M.init y)) :
    N.output O x (s + t) = M.output O y t := by
  unfold OTM.output
  rw [E.runCfg_after_prefix O x y s t hprefix]
  exact E.readBits_symbols _ _

 theorem cfg_valid (c : M.Cfg) (h : Valid M c) : Valid N (E.cfg c) := by
  constructor
  · refine ⟨h.work.lo_head, h.work.head_hi, h.work.lo_zero, h.work.zero_hi, ?_⟩
    intro i hi
    change E.symbols (c.work i) = 0
    rw [h.work.outside i hi, E.blank]
  · refine ⟨h.query.lo_head, h.query.head_hi, h.query.lo_zero, h.query.zero_hi, ?_⟩
    intro i hi
    change E.symbols (c.query i) = 0
    rw [h.query.outside i hi, E.blank]

 theorem core_after_prefix (O : Oracle) (x y : List Bool) (s t : ℕ)
    (hprefix : CoreEq N (N.runCfg O x s) (E.cfg (M.init y))) :
    CoreEq N (N.runCfg O x (s + t)) (E.cfg (M.runCfg O y t)) := by
  have hrun : N.runCfg O x (s + t) = (N.step O)^[t] (N.runCfg O x s) := by
    unfold OTM.runCfg
    rw [Nat.add_comm s t, Function.iterate_add_apply]
  rw [hrun]
  change CoreEq N ((N.step O)^[t] (N.runCfg O x s)) (E.cfg ((M.step O)^[t] (M.init y)))
  rw [E.cfg_iterate]
  exact coreEq_iterate N O _ _ t (valid_runCfg N O x s) (E.cfg_valid _ (valid_init M y)) hprefix

 theorem result_after_core_prefix (O : Oracle) (x y : List Bool) (s t : ℕ)
    (hprefix : CoreEq N (N.runCfg O x s) (E.cfg (M.init y))) :
    N.result O x (s + t) = M.result O y t := by
  have hcore := E.core_after_prefix O x y s t hprefix
  unfold OTM.result
  dsimp only
  rw [hcore.state]
  dsimp only [cfg]
  simp only [E.state_accept, E.state_reject]

 theorem output_after_core_prefix (O : Oracle) (x y : List Bool) (s t : ℕ)
    (hprefix : CoreEq N (N.runCfg O x s) (E.cfg (M.init y))) :
    N.output O x (s + t) = M.output O y t := by
  have hcore := E.core_after_prefix O x y s t hprefix
  unfold OTM.output
  calc
    readBits (N.runCfg O x (s + t)).work (N.runCfg O x (s + t)).whi =
        readBits (E.cfg (M.runCfg O y t)).work (E.cfg (M.runCfg O y t)).whi :=
      coreEq_readBits_work N _ _ (valid_runCfg N O x (s + t))
        (E.cfg_valid _ (valid_runCfg M O y t)) hcore
    _ = _ := E.readBits_symbols _ _

end Simulation
end QAdvFew.PoQOracle.OTM

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM
namespace Precheck


def state (M : OTM) (D : DFA) (q : Fin (M.k + 6)) : Fin ((M.k + D.size + 2) + 6) :=
  ⟨if q.val = 0 then M.k + 6 else q.val, by split <;> omega⟩

def symbol (M : OTM) (a : Fin (M.g + 3)) : Fin ((M.g + 2) + 3) := ⟨a.val, by omega⟩

def markFalse (M : OTM) : Fin ((M.g + 2) + 3) := ⟨M.g + 3, by omega⟩
def markTrue (M : OTM) : Fin ((M.g + 2) + 3) := ⟨M.g + 4, by omega⟩

def scan (M : OTM) (D : DFA) (s : Fin D.size) : Fin ((M.k + D.size + 2) + 6) :=
  ⟨M.k + 7 + s.val, by omega⟩
def reset (M : OTM) (D : DFA) : Fin ((M.k + D.size + 2) + 6) :=
  ⟨M.k + 7 + D.size, by omega⟩

def decodeState (M : OTM) (D : DFA) (q : Fin ((M.k + D.size + 2) + 6)) : Fin (M.k + 6) :=
  if h : q.val < M.k + 6 then ⟨q.val, h⟩ else 0

def decodeSymbol (M : OTM) (a : Fin ((M.g + 2) + 3)) : Fin (M.g + 3) :=
  if h : a.val < M.g + 3 then ⟨a.val, h⟩ else 0

 abbrev machine (M : OTM) (D : DFA) : OTM where
  k := M.k + D.size + 2
  g := M.g + 2
  δ := fun q a b =>
    if hstart : q.val = 0 then
      if a = 1 then (scan M D (D.next D.start false), markFalse M, 2, b, 1)
      else if a = 2 then (scan M D (D.next D.start true), markTrue M, 2, b, 1)
      else (if D.accept D.start then state M D 0 else 2, a, 1, b, 1)
    else if hsim : q.val ≤ M.k + 6 then
      let d := M.δ (decodeState M D q) (decodeSymbol M a) (decodeSymbol M b)
      (state M D d.1, symbol M d.2.1, d.2.2.1, symbol M d.2.2.2.1, d.2.2.2.2)
    else if hs : q.val < M.k + 7 + D.size then
      let s : Fin D.size := ⟨q.val - (M.k + 7), by omega⟩
      if a = 1 then (scan M D (D.next s false), a, 2, b, 1)
      else if a = 2 then (scan M D (D.next s true), a, 2, b, 1)
      else (if D.accept s then reset M D else 2, a, if D.accept s then 0 else 1, b, 1)
    else
      if a = markFalse M then (state M D 0, 1, 1, b, 1)
      else if a = markTrue M then (state M D 0, 2, 1, b, 1)
      else (reset M D, a, 0, b, 1)

 theorem state_injective (M : OTM) (D : DFA) : Function.Injective (state M D) := by
  intro q r heq
  have hval := congrArg Fin.val heq
  dsimp only [state] at hval
  apply Fin.ext
  split at hval <;> split at hval <;> omega

 theorem symbol_injective (M : OTM) : Function.Injective (symbol M) := by
  intro a b h
  have hv := congrArg (fun c : Fin ((M.g + 2) + 3) => c.val) h
  exact Fin.ext hv

 theorem decode_state (M : OTM) (D : DFA) (q : Fin (M.k + 6)) :
    decodeState M D (state M D q) = q := by
  unfold decodeState state
  by_cases hq : q.val = 0
  · apply Fin.ext
    simp [hq]
  · simp only [hq, ↓reduceIte, q.isLt, ↓reduceDIte]

 theorem decode_symbol (M : OTM) (a : Fin (M.g + 3)) : decodeSymbol M (symbol M a) = a := by
  unfold decodeSymbol symbol
  simp only [a.isLt, ↓reduceDIte]

private theorem state_number (M : OTM) (D : DFA) (n : ℕ) (hn : 0 < n) (hn6 : n < 6) :
    state M D ⟨n, by omega⟩ = ⟨n, by omega⟩ := by
  apply Fin.ext
  simp [state, Nat.ne_of_gt hn]

private theorem symbol_number (M : OTM) (n : ℕ) (hn : n < 3) :
    symbol M ⟨n, by omega⟩ = ⟨n, by omega⟩ := rfl

 theorem delta_state (M : OTM) (D : DFA) (q : Fin (M.k + 6)) (a b : Fin (M.g + 3)) :
    (machine M D).δ (state M D q) (symbol M a) (symbol M b) =
      let d := M.δ q a b
      (state M D d.1, symbol M d.2.1, d.2.2.1, symbol M d.2.2.2.1, d.2.2.2.2) := by
  have hpos : (state M D q).val ≠ 0 := by dsimp [state]; split <;> omega
  have hle : (state M D q).val ≤ M.k + 6 := by dsimp [state]; split <;> omega
  dsimp only [machine]
  rw [dif_neg hpos, dif_pos hle]
  simp only [decode_state, decode_symbol]

 def simulation (M : OTM) (D : DFA) : Simulation M (machine M D) where
  states := ⟨state M D, state_injective M D⟩
  symbols := ⟨symbol M, symbol_injective M⟩
  accept := by
    change state M D (1 : Fin (M.k + 6)) = (1 : Fin ((M.k + D.size + 2) + 6))
    apply Fin.ext
    simp (disch := omega) [state, Nat.mod_eq_of_lt]
  reject := by
    change state M D (2 : Fin (M.k + 6)) = (2 : Fin ((M.k + D.size + 2) + 6))
    apply Fin.ext
    simp (disch := omega) [state, Nat.mod_eq_of_lt]
  queryState := by
    change state M D (3 : Fin (M.k + 6)) = (3 : Fin ((M.k + D.size + 2) + 6))
    apply Fin.ext
    simp (disch := omega) [state, Nat.mod_eq_of_lt]
  yes := by
    change state M D (4 : Fin (M.k + 6)) = (4 : Fin ((M.k + D.size + 2) + 6))
    apply Fin.ext
    simp (disch := omega) [state, Nat.mod_eq_of_lt]
  no := by
    change state M D (5 : Fin (M.k + 6)) = (5 : Fin ((M.k + D.size + 2) + 6))
    apply Fin.ext
    simp (disch := omega) [state, Nat.mod_eq_of_lt]
  blank := by apply Fin.ext; rfl
  bitFalse := by
    change symbol M (1 : Fin (M.g + 3)) = (1 : Fin ((M.g + 2) + 3))
    apply Fin.ext
    simp (disch := omega) [symbol, Nat.mod_eq_of_lt]
  bitTrue := by
    change symbol M (2 : Fin (M.g + 3)) = (2 : Fin ((M.g + 2) + 3))
    apply Fin.ext
    simp (disch := omega) [symbol, Nat.mod_eq_of_lt]
  transition := by
    intro q a b
    exact delta_state M D q a b

private theorem scan_zero_ne (M : OTM) (D : DFA) (s : Fin D.size) :
    (scan M D s).val ≠ 0 := by dsimp [scan]; omega
private theorem scan_not_sim (M : OTM) (D : DFA) (s : Fin D.size) :
    ¬ (scan M D s).val ≤ M.k + 6 := by dsimp [scan]; omega
private theorem scan_in_range (M : OTM) (D : DFA) (s : Fin D.size) :
    (scan M D s).val < M.k + 7 + D.size := by dsimp [scan]; omega

 theorem delta_scan_bit (M : OTM) (D : DFA) (s : Fin D.size) (b : Bool)
    (c : Fin ((M.g + 2) + 3)) :
    (machine M D).δ (scan M D s) (symOf (M.g + 2) b) c =
      (scan M D (D.next s b), symOf (M.g + 2) b, 2, c, 1) := by
  dsimp only [machine]
  rw [dif_neg (scan_zero_ne M D s), dif_neg (scan_not_sim M D s), dif_pos (scan_in_range M D s)]
  have heq : (⟨(scan M D s).val - (M.k + 7), by have := scan_in_range M D s; dsimp [scan] at *; omega⟩ : Fin D.size) = s := by
    apply Fin.ext
    dsimp [scan]
    omega
  rw [heq]
  cases b <;> simp (disch := omega) [symOf, Fin.ext_iff, Nat.mod_eq_of_lt]

 theorem delta_scan_end (M : OTM) (D : DFA) (s : Fin D.size)
    (c : Fin ((M.g + 2) + 3)) :
    (machine M D).δ (scan M D s) 0 c =
      (if D.accept s then reset M D else 2, 0, if D.accept s then 0 else 1, c, 1) := by
  dsimp only [machine]
  rw [dif_neg (scan_zero_ne M D s), dif_neg (scan_not_sim M D s), dif_pos (scan_in_range M D s)]
  have heq : (⟨(scan M D s).val - (M.k + 7), by have := scan_in_range M D s; dsimp [scan] at *; omega⟩ : Fin D.size) = s := by
    apply Fin.ext
    dsimp [scan]
    omega
  rw [heq]
  simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]

 theorem delta_start_bit (M : OTM) (D : DFA) (b : Bool)
    (c : Fin ((M.g + 2) + 3)) :
    (machine M D).δ 0 (symOf (M.g + 2) b) c =
      (scan M D (D.next D.start b), if b then markTrue M else markFalse M, 2, c, 1) := by
  dsimp only [machine]
  simp only [Fin.val_zero, dif_pos rfl]
  cases b <;> simp (disch := omega) [symOf, Fin.ext_iff, Nat.mod_eq_of_lt]

 theorem delta_start_empty (M : OTM) (D : DFA) (c : Fin ((M.g + 2) + 3)) :
    (machine M D).δ 0 0 c = (if D.accept D.start then state M D 0 else 2, 0, 1, c, 1) := by
  dsimp only [machine]
  simp only [Fin.val_zero, dif_pos rfl]
  simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]

 theorem delta_reset_bit (M : OTM) (D : DFA) (b : Bool)
    (c : Fin ((M.g + 2) + 3)) :
    (machine M D).δ (reset M D) (symOf (M.g + 2) b) c =
      (reset M D, symOf (M.g + 2) b, 0, c, 1) := by
  have h0 : (reset M D).val ≠ 0 := by dsimp [reset]; omega
  have h1 : ¬ (reset M D).val ≤ M.k + 6 := by dsimp [reset]; omega
  have h2 : ¬ (reset M D).val < M.k + 7 + D.size := by dsimp [reset]; omega
  dsimp only [machine]
  rw [dif_neg h0, dif_neg h1, dif_neg h2]
  cases b <;> simp (disch := omega) [symOf, markFalse, markTrue, Fin.ext_iff, Nat.mod_eq_of_lt]

 theorem delta_reset_marker (M : OTM) (D : DFA) (b : Bool)
    (c : Fin ((M.g + 2) + 3)) :
    (machine M D).δ (reset M D) (if b then markTrue M else markFalse M) c =
      (state M D 0, symOf (M.g + 2) b, 1, c, 1) := by
  have h0 : (reset M D).val ≠ 0 := by dsimp [reset]; omega
  have h1 : ¬ (reset M D).val ≤ M.k + 6 := by dsimp [reset]; omega
  have h2 : ¬ (reset M D).val < M.k + 7 + D.size := by dsimp [reset]; omega
  dsimp only [machine]
  rw [dif_neg h0, dif_neg h1, dif_neg h2]
  cases b <;> simp (disch := omega) [symOf, markFalse, markTrue, Fin.ext_iff, Nat.mod_eq_of_lt]

def markedCfg (M : OTM) (D : DFA) (x : List Bool) (first : Bool)
    (q : Fin ((M.k + D.size + 2) + 6)) (head : ℕ) : (machine M D).Cfg :=
  { (machine M D).init x with
    state := q
    work := Function.update ((machine M D).init x).work 0
      (if first then markTrue M else markFalse M)
    wh := head }

private theorem marked_read (M : OTM) (D : DFA) (x : List Bool) (first : Bool)
    (q : Fin ((M.k + D.size + 2) + 6)) (t : ℕ) (ht : 0 < t) (htx : t < x.length) :
    (markedCfg M D x first q t).work (t : ℤ) = symOf (M.g + 2) (x.getD t false) := by
  dsimp only [markedCfg]
  rw [Function.update_of_ne (by omega)]
  have hti : (t : ℤ) < x.length := by exact_mod_cast htx
  simp only [init, Int.natCast_nonneg, hti, and_self, if_true, Int.toNat_natCast]

private theorem state_small_ne_scan (M : OTM) (D : DFA) (s : Fin D.size) (n : ℕ) (hn : n < 6) :
    scan M D s ≠ (⟨n, by omega⟩ : Fin ((M.k + D.size + 2) + 6)) := by
  intro heq
  have hv := congrArg Fin.val heq
  dsimp [scan] at hv
  omega

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

 theorem step_marked_scan (M : OTM) (D : DFA) (O : Oracle) (x : List Bool) (first : Bool)
    (s : Fin D.size) (t : ℕ) (ht : 0 < t) (htx : t < x.length) :
    (machine M D).step O (markedCfg M D x first (scan M D s) t) =
      markedCfg M D x first (scan M D (D.next s (x.getD t false))) (t + 1) := by
  have hread := marked_read M D x first (scan M D s) t ht htx
  have hh : ¬ (scan M D s = 1 ∨ scan M D s = 2) := by
    simp (disch := omega) [scan, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hq : scan M D s ≠ 3 := by
    simp (disch := omega) [scan, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hu : Function.update (markedCfg M D x first (scan M D s) t).work (t : ℤ)
      (symOf (M.g + 2) (x.getD t false)) = (markedCfg M D x first (scan M D s) t).work := by
    rw [← hread, Function.update_eq_self]
  have hd : (machine M D).δ (markedCfg M D x first (scan M D s) t).state
      ((markedCfg M D x first (scan M D s) t).work (markedCfg M D x first (scan M D s) t).wh)
      ((markedCfg M D x first (scan M D s) t).query (markedCfg M D x first (scan M D s) t).qh) =
      (scan M D (D.next s (x.getD t false)), symOf (M.g + 2) (x.getD t false), 2, 0, 1) := by
    change (machine M D).δ (scan M D s) ((markedCfg M D x first (scan M D s) t).work (t : ℤ)) 0 = _
    rw [hread, delta_scan_bit]
  rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]
  dsimp only [markedCfg] at hu ⊢
  rw [hu]
  simp (disch := omega) [init, min_eq_left, max_eq_left, Function.update_eq_self] <;> omega

 theorem step_initial_nonempty (M : OTM) (D : DFA) (O : Oracle) (b : Bool) (xs : List Bool) :
    (machine M D).step O ((machine M D).init (b :: xs)) =
      markedCfg M D (b :: xs) b (scan M D (D.next D.start b)) 1 := by
  have hh : ¬ (((machine M D).init (b :: xs)).state = 1 ∨ ((machine M D).init (b :: xs)).state = 2) := by
    change ¬ ((0 : Fin ((M.k + D.size + 2) + 6)) = 1 ∨ 0 = 2)
    simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  have hq : ((machine M D).init (b :: xs)).state ≠ 3 := by
    change (0 : Fin ((M.k + D.size + 2) + 6)) ≠ 3
    simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  have hread : ((machine M D).init (b :: xs)).work 0 = symOf (M.g + 2) b := by
    simp [init]
  have hd : (machine M D).δ ((machine M D).init (b :: xs)).state
      (((machine M D).init (b :: xs)).work ((machine M D).init (b :: xs)).wh)
      (((machine M D).init (b :: xs)).query ((machine M D).init (b :: xs)).qh) =
      (scan M D (D.next D.start b), if b then markTrue M else markFalse M, 2, 0, 1) := by
    change (machine M D).δ 0 (((machine M D).init (b :: xs)).work 0) 0 = _
    rw [hread, delta_start_bit]
  rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]
  simp (disch := omega) [markedCfg, init, min_eq_left, max_eq_left, Function.update_eq_self]

 theorem scan_run_nonempty (M : OTM) (D : DFA) (O : Oracle) (b : Bool) (xs : List Bool)
    (t : ℕ) (ht : 0 < t) (htlen : t ≤ (b :: xs).length) :
    (machine M D).runCfg O (b :: xs) t =
      markedCfg M D (b :: xs) b (scan M D (((b :: xs).take t).foldl D.next D.start)) t := by
  revert ht htlen
  induction t with
  | zero => intro ht; omega
  | succ t ih =>
    intro ht htlen
    by_cases ht0 : t = 0
    · subst t
      change (machine M D).step O ((machine M D).init (b :: xs)) = _
      simpa using step_initial_nonempty M D O b xs
    · have htp : 0 < t := by omega
      have htl : t < (b :: xs).length := by omega
      have hfold : (((b :: xs).take (t + 1)).foldl D.next D.start) =
          D.next (((b :: xs).take t).foldl D.next D.start) ((b :: xs).getD t false) := by
        rw [List.take_succ_eq_append_getElem htl, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil, List.getD_eq_getElem _ _ htl]
      rw [hfold]
      rw [OTM.runCfg, Function.iterate_succ_apply']
      change (machine M D).step O ((machine M D).runCfg O (b :: xs) t) = _
      rw [ih htp (by omega)]
      exact step_marked_scan M D O (b :: xs) b _ t htp htl

private theorem marked_end (M : OTM) (D : DFA) (x : List Bool) (first : Bool)
    (q : Fin ((M.k + D.size + 2) + 6)) (hx : 0 < x.length) :
    (markedCfg M D x first q x.length).work (x.length : ℤ) = 0 := by
  dsimp only [markedCfg]
  rw [Function.update_of_ne (by omega)]
  simp [init]

 theorem step_scan_finish (M : OTM) (D : DFA) (O : Oracle) (x : List Bool) (first : Bool)
    (s : Fin D.size) (hx : 0 < x.length) (hacc : D.accept s = true) :
    (machine M D).step O (markedCfg M D x first (scan M D s) x.length) =
      markedCfg M D x first (reset M D) (x.length - 1) := by
  have hread := marked_end M D x first (scan M D s) hx
  have hh : ¬ (scan M D s = 1 ∨ scan M D s = 2) := by
    simp (disch := omega) [scan, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hq : scan M D s ≠ 3 := by
    simp (disch := omega) [scan, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hu : Function.update (markedCfg M D x first (scan M D s) x.length).work (x.length : ℤ) 0 =
      (markedCfg M D x first (scan M D s) x.length).work := by
    rw [← hread, Function.update_eq_self]
  have hd : (machine M D).δ (markedCfg M D x first (scan M D s) x.length).state
      ((markedCfg M D x first (scan M D s) x.length).work (markedCfg M D x first (scan M D s) x.length).wh)
      ((markedCfg M D x first (scan M D s) x.length).query (markedCfg M D x first (scan M D s) x.length).qh) =
      (reset M D, 0, 0, 0, 1) := by
    change (machine M D).δ (scan M D s) ((markedCfg M D x first (scan M D s) x.length).work (x.length : ℤ)) 0 = _
    rw [hread, delta_scan_end]
    simp [hacc]
  rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]
  dsimp only [markedCfg] at hu ⊢
  rw [hu]
  simp (disch := omega) [init, min_eq_left, max_eq_left, Function.update_eq_self] <;> omega

 theorem step_reset_walk (M : OTM) (D : DFA) (O : Oracle) (x : List Bool) (first : Bool)
    (t : ℕ) (ht : 0 < t) (htx : t < x.length) :
    (machine M D).step O (markedCfg M D x first (reset M D) t) =
      markedCfg M D x first (reset M D) (t - 1) := by
  have hread := marked_read M D x first (reset M D) t ht htx
  have hh : ¬ (reset M D = 1 ∨ reset M D = 2) := by
    simp (disch := omega) [reset, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hq : reset M D ≠ 3 := by
    simp (disch := omega) [reset, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hu : Function.update (markedCfg M D x first (reset M D) t).work (t : ℤ)
      (symOf (M.g + 2) (x.getD t false)) = (markedCfg M D x first (reset M D) t).work := by
    rw [← hread, Function.update_eq_self]
  have hd : (machine M D).δ (markedCfg M D x first (reset M D) t).state
      ((markedCfg M D x first (reset M D) t).work (markedCfg M D x first (reset M D) t).wh)
      ((markedCfg M D x first (reset M D) t).query (markedCfg M D x first (reset M D) t).qh) =
      (reset M D, symOf (M.g + 2) (x.getD t false), 0, 0, 1) := by
    change (machine M D).δ (reset M D) ((markedCfg M D x first (reset M D) t).work (t : ℤ)) 0 = _
    rw [hread, delta_reset_bit]
  rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]
  dsimp only [markedCfg] at hu ⊢
  rw [hu]
  simp (disch := omega) [init, min_eq_left, max_eq_left, Function.update_eq_self] <;> omega

 theorem step_restore (M : OTM) (D : DFA) (O : Oracle) (b : Bool) (xs : List Bool) :
    (machine M D).step O (markedCfg M D (b :: xs) b (reset M D) 0) =
      { (machine M D).init (b :: xs) with state := state M D 0 } := by
  have hh : ¬ (reset M D = 1 ∨ reset M D = 2) := by
    simp (disch := omega) [reset, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hq : reset M D ≠ 3 := by
    simp (disch := omega) [reset, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hfirst : ((machine M D).init (b :: xs)).work 0 = symOf (M.g + 2) b := by simp [init]
  have hu : Function.update (markedCfg M D (b :: xs) b (reset M D) 0).work 0 (symOf (M.g + 2) b) =
      ((machine M D).init (b :: xs)).work := by
    dsimp only [markedCfg]
    rw [Function.update_idem, ← hfirst, Function.update_eq_self]
  have hd : (machine M D).δ (markedCfg M D (b :: xs) b (reset M D) 0).state
      ((markedCfg M D (b :: xs) b (reset M D) 0).work (markedCfg M D (b :: xs) b (reset M D) 0).wh)
      ((markedCfg M D (b :: xs) b (reset M D) 0).query (markedCfg M D (b :: xs) b (reset M D) 0).qh) =
      (state M D 0, symOf (M.g + 2) b, 1, 0, 1) := by
    change (machine M D).δ (reset M D) (Function.update ((machine M D).init (b :: xs)).work (0 : ℤ) (if b then markTrue M else markFalse M) (0 : ℤ)) 0 = _
    rw [Function.update_self, delta_reset_marker]
  rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]
  dsimp only [markedCfg] at hu ⊢
  simp only [Nat.cast_zero]
  rw [hu]
  simp [init, Function.update_eq_self] <;> omega

 theorem core_initial_simulation (M : OTM) (D : DFA) (x : List Bool) :
    CoreEq (machine M D) ({ (machine M D).init x with state := state M D 0 })
      ((simulation M D).cfg (M.init x)) := by
  have hsym : ∀ b, symbol M (symOf M.g b) = symOf (M.g + 2) b := by
    intro b
    cases b <;> apply Fin.ext <;> simp (disch := omega) [symbol, symOf, Nat.mod_eq_of_lt]
  constructor
  · rfl
  · change ((machine M D).init x).work = fun i => symbol M ((M.init x).work i)
    funext i
    dsimp only [init]
    split
    · exact (hsym _).symm
    · rfl
  · rfl
  · change (fun _ : ℤ => (0 : Fin ((M.g + 2) + 3))) = fun i : ℤ => symbol M ((M.init x).query i)
    rfl
  · rfl

 theorem reset_run_nonempty (M : OTM) (D : DFA) (O : Oracle) (b : Bool) (xs : List Bool)
    (hacc : D.accept (D.run (b :: xs)) = true) (j : ℕ) (hj : j ≤ (b :: xs).length - 1) :
    (machine M D).runCfg O (b :: xs) ((b :: xs).length + 1 + j) =
      markedCfg M D (b :: xs) b (reset M D) ((b :: xs).length - 1 - j) := by
  revert hj
  induction j with
  | zero =>
    intro hj
    simp only [Nat.add_zero, Nat.sub_zero]
    rw [OTM.runCfg, Function.iterate_succ_apply']
    change (machine M D).step O ((machine M D).runCfg O (b :: xs) (b :: xs).length) = _
    rw [scan_run_nonempty M D O b xs _ (by simp) (by rfl)]
    simp only [List.take_length]
    exact step_scan_finish M D O (b :: xs) b _ (by simp) hacc
  | succ j ih =>
    intro hj
    rw [show (b :: xs).length + 1 + (j + 1) = ((b :: xs).length + 1 + j) + 1 by omega]
    rw [OTM.runCfg, Function.iterate_succ_apply']
    change (machine M D).step O ((machine M D).runCfg O (b :: xs) ((b :: xs).length + 1 + j)) = _
    rw [ih (by omega)]
    rw [step_reset_walk M D O (b :: xs) b _ (by omega) (by omega)]
    congr 1 <;> omega

 theorem core_prefix_nonempty (M : OTM) (D : DFA) (O : Oracle) (b : Bool) (xs : List Bool)
    (hacc : D.accept (D.run (b :: xs)) = true) :
    CoreEq (machine M D) ((machine M D).runCfg O (b :: xs) (2 * (b :: xs).length + 1))
      ((simulation M D).cfg (M.init (b :: xs))) := by
  have hreset := reset_run_nonempty M D O b xs hacc ((b :: xs).length - 1) (by rfl)
  have htime : (b :: xs).length + 1 + ((b :: xs).length - 1) = 2 * (b :: xs).length := by simp; omega
  rw [htime, Nat.sub_self] at hreset
  rw [OTM.runCfg, Function.iterate_succ_apply']
  change CoreEq (machine M D) ((machine M D).step O ((machine M D).runCfg O (b :: xs) (2 * (b :: xs).length))) _
  rw [hreset, step_restore]
  exact core_initial_simulation M D (b :: xs)

 theorem step_initial_empty (M : OTM) (D : DFA) (O : Oracle) (hacc : D.accept D.start = true) :
    (machine M D).step O ((machine M D).init []) =
      { (machine M D).init [] with state := state M D 0 } := by
  have hh : ¬ (((machine M D).init []).state = 1 ∨ ((machine M D).init []).state = 2) := by
    change ¬ ((0 : Fin ((M.k + D.size + 2) + 6)) = 1 ∨ 0 = 2)
    simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  have hq : ((machine M D).init []).state ≠ 3 := by
    change (0 : Fin ((M.k + D.size + 2) + 6)) ≠ 3
    simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  have hd : (machine M D).δ ((machine M D).init []).state
      (((machine M D).init []).work ((machine M D).init []).wh)
      (((machine M D).init []).query ((machine M D).init []).qh) =
      (state M D 0, 0, 1, 0, 1) := by
    change (machine M D).δ 0 0 0 = _
    rw [delta_start_empty]
    simp [hacc]
  rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]
  simp [init, Function.update_eq_self]

 theorem core_prefix (M : OTM) (D : DFA) (O : Oracle) (x : List Bool)
    (hacc : D.accept (D.run x) = true) :
    CoreEq (machine M D) ((machine M D).runCfg O x (2 * x.length + 1))
      ((simulation M D).cfg (M.init x)) := by
  cases x with
  | nil =>
    change CoreEq (machine M D) ((machine M D).step O ((machine M D).init [])) _
    rw [step_initial_empty M D O hacc]
    exact core_initial_simulation M D []
  | cons b xs => exact core_prefix_nonempty M D O b xs hacc

 theorem result_accept (M : OTM) (D : DFA) (O : Oracle) (x : List Bool) (t : ℕ)
    (hacc : D.accept (D.run x) = true) :
    (machine M D).result O x (2 * x.length + 1 + t) = M.result O x t :=
  (simulation M D).result_after_core_prefix O x x _ t (core_prefix M D O x hacc)

 theorem step_scan_reject (M : OTM) (D : DFA) (O : Oracle) (x : List Bool) (first : Bool)
    (s : Fin D.size) (hx : 0 < x.length) (hacc : D.accept s = false) :
    ((machine M D).step O (markedCfg M D x first (scan M D s) x.length)).state = 2 := by
  have hread := marked_end M D x first (scan M D s) hx
  have hh : ¬ (scan M D s = 1 ∨ scan M D s = 2) := by
    simp (disch := omega) [scan, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hq : scan M D s ≠ 3 := by
    simp (disch := omega) [scan, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hd : (machine M D).δ (markedCfg M D x first (scan M D s) x.length).state
      ((markedCfg M D x first (scan M D s) x.length).work (markedCfg M D x first (scan M D s) x.length).wh)
      ((markedCfg M D x first (scan M D s) x.length).query (markedCfg M D x first (scan M D s) x.length).qh) =
      (2, 0, 1, 0, 1) := by
    change (machine M D).δ (scan M D s) ((markedCfg M D x first (scan M D s) x.length).work (x.length : ℤ)) 0 = _
    rw [hread, delta_scan_end]
    simp [hacc]
  rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]

 theorem reject_state (M : OTM) (D : DFA) (O : Oracle) (x : List Bool)
    (hacc : D.accept (D.run x) = false) :
    ((machine M D).runCfg O x (x.length + 1)).state = 2 := by
  cases x with
  | nil =>
    change ((machine M D).step O ((machine M D).init [])).state = 2
    have hh : ¬ (((machine M D).init []).state = 1 ∨ ((machine M D).init []).state = 2) := by
      change ¬ ((0 : Fin ((M.k + D.size + 2) + 6)) = 1 ∨ 0 = 2)
      simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
    have hq : ((machine M D).init []).state ≠ 3 := by
      change (0 : Fin ((M.k + D.size + 2) + 6)) ≠ 3
      simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
    have hd : (machine M D).δ ((machine M D).init []).state
        (((machine M D).init []).work ((machine M D).init []).wh)
        (((machine M D).init []).query ((machine M D).init []).qh) = (2, 0, 1, 0, 1) := by
      change (machine M D).δ 0 0 0 = _
      rw [delta_start_empty]
      simp only [DFA.run, List.foldl_nil] at hacc
      simp [hacc]
    rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]
  | cons b xs =>
    rw [OTM.runCfg, Function.iterate_succ_apply']
    change ((machine M D).step O ((machine M D).runCfg O (b :: xs) (b :: xs).length)).state = 2
    rw [scan_run_nonempty M D O b xs _ (by simp) (by rfl)]
    simp only [List.take_length]
    exact step_scan_reject M D O (b :: xs) b _ (by simp) hacc

 theorem result_reject (M : OTM) (D : DFA) (O : Oracle) (x : List Bool) (t : ℕ)
    (hacc : D.accept (D.run x) = false) :
    (machine M D).result O x (2 * x.length + 1 + t) = some false := by
  have hre : (machine M D).result O x (x.length + 1) = some false := by
    unfold result
    dsimp only
    rw [reject_state M D O x hacc]
    simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  have hhalt : ((machine M D).result O x (x.length + 1)).isSome := by rw [hre]; rfl
  rw [result_of_le (machine M D) O x (x.length + 1) _ hhalt (by omega), hre]

 theorem result_precheck (M : OTM) (D : DFA) (O : Oracle) (x : List Bool) (t : ℕ) :
    (machine M D).result O x (2 * x.length + 1 + t) =
      if D.accept (D.run x) then M.result O x t else some false := by
  cases hacc : D.accept (D.run x) with
  | false => simpa only [hacc, Bool.false_eq_true, if_false] using result_reject M D O x t hacc
  | true => simpa only [hacc, if_true] using result_accept M D O x t hacc

end Precheck
end QAdvFew.PoQOracle.OTM

namespace StudentTeacher976.Adaptivity
open QAdvFew.PoQOracle

 theorem delta_regular_restrict {i : ℕ} {L : Language} (hL : L ∈ Delta i)
    (D : OTM.Precheck.DFA) : L ∩ {x | D.accept (D.run x) = true} ∈ Delta i := by
  obtain ⟨O, M, clock, hO, htotal, hdec⟩ := hL
  let bound : Polynomial ℕ := (2 * Polynomial.X + 1) + clock
  have heval : ∀ n, bound.eval n = 2 * n + 1 + clock.eval n := by intro n; simp [bound]
  refine ⟨O, OTM.Precheck.machine M D, bound, hO, ?_, ?_⟩
  · intro s
    rw [heval, OTM.Precheck.result_precheck]
    split
    · exact htotal s
    · rfl
  · intro x
    rw [heval, OTM.Precheck.result_precheck]
    change (x ∈ L ∧ D.accept (D.run x) = true) ↔ _
    rw [hdec]
    cases hb : D.accept (D.run x) <;> simp

end StudentTeacher976.Adaptivity

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
namespace StudentTeacher976.Adaptivity.NativeCPU
open QAdvFew.PoQOracle Turing.MultiTapeTM

 abbrev Body (M : OTM) := Fin (M.k+6) × List (Fin (M.g+3)) × ℕ × List (Fin (M.g+3)) × ℕ
 abbrev State (M : OTM) := ℕ × ℕ × Body M

 def bodyEnc (M : OTM) : Body M ↪ List Bool :=
   encPair (FiniteCodec.encFin (M.k+6))
     (encPair (encList (FiniteCodec.encFin (M.g+3)))
       (encPair encUnary (encPair (encList (FiniteCodec.encFin (M.g+3))) encUnary)))
 def stateEnc (M : OTM) : State M ↪ List Bool := encPair encUnary (encPair encUnary (bodyEnc M))

 noncomputable def bodyDecoder (M : OTM) : Decoder (bodyEnc M) :=
   (FiniteCodec.decoder (FiniteCodec.encFin (M.k+6))).pair
     (((FiniteCodec.decoder (FiniteCodec.encFin (M.g+3))).list).pair
       (Decoder.unary.pair (((FiniteCodec.decoder (FiniteCodec.encFin (M.g+3))).list).pair Decoder.unary)))
 noncomputable def stateDecoder (M : OTM) : Decoder (stateEnc M) :=
   Decoder.unary.pair (Decoder.unary.pair (bodyDecoder M))

 def encodeTape (M : OTM) (R : ℕ) (tape : ℤ → Fin (M.g+3)) : List (Fin (M.g+3)) :=
   (List.range (2*R+1)).map fun (j : ℕ) => tape ((j : ℤ)-R)

 @[simp] theorem length_encodeTape (M : OTM) (R : ℕ) (tape : ℤ → Fin (M.g+3)) :
     (encodeTape M R tape).length = 2*R+1 := by simp [encodeTape]

 def encodeBody (M : OTM) (R : ℕ) (c : M.Cfg) : Body M :=
   (c.state, encodeTape M R c.work, (c.wh+R).toNat, encodeTape M R c.query, (c.qh+R).toNat)

 theorem encodeTape_at (M : OTM) (R : ℕ) (tape : ℤ → Fin (M.g+3)) (z : ℤ)
     (hz : -(R : ℤ) ≤ z ∧ z ≤ R) :
     (encodeTape M R tape).getD (z+R).toNat 0 = tape z := by
   have hi : (z+R).toNat < 2*R+1 := by omega
   rw [List.getD_eq_getElem _ _ (by simpa using hi)]
   simp only [encodeTape, List.getElem_map, List.getElem_range]
   congr 1
   omega

 theorem encodeTape_update (M : OTM) (R : ℕ) (tape : ℤ → Fin (M.g+3)) (z : ℤ)
     (hz : -(R : ℤ) ≤ z ∧ z ≤ R) (a : Fin (M.g+3)) :
     encodeTape M R (Function.update tape z a) = (encodeTape M R tape).set (z+R).toNat a := by
   apply List.ext_getElem
   · simp
   · intro j hj hj'
     have hj0 : j < 2*R+1 := by simpa using hj
     simp only [encodeTape, List.getElem_map, List.getElem_range, List.getElem_set]
     by_cases he : (z+R).toNat = j
     · have he' : (j : ℤ)-R = z := by omega
       simp [he, he']
     · have he' : (j : ℤ)-R ≠ z := by omega
       simp [he, he', Function.update_of_ne he']

 def moveHead (h : ℕ) (m : Fin 3) : ℕ := h+m.val-1

 theorem moveHead_encode (R : ℕ) (z : ℤ) (m : Fin 3)
     (hbefore : 0 ≤ z+R) (hafter : 0 ≤ z+(m.val : ℤ)-1+R) :
     moveHead (z+R).toNat m = (z+(m.val : ℤ)-1+R).toNat := by
   unfold moveHead
   omega

 def stepBody (M : OTM) (answer : Bool) (c : Body M) : Body M :=
   if c.1 = 1 ∨ c.1 = 2 then c
   else if c.1 = 3 then (if answer then 4 else 5, c.2)
   else
     let d := M.δ c.1 (c.2.1.getD c.2.2.1 0) (c.2.2.2.1.getD c.2.2.2.2 0)
     (d.1, c.2.1.set c.2.2.1 d.2.1, moveHead c.2.2.1 d.2.2.1,
       c.2.2.2.1.set c.2.2.2.2 d.2.2.2.1, moveHead c.2.2.2.2 d.2.2.2.2)

end StudentTeacher976.Adaptivity.NativeCPU

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeCPU
open QAdvFew.PoQOracle Turing.MultiTapeTM

 theorem set_eq_parts {α : Type} (l : List α) (j : ℕ) (a : α) :
     l.set j a = if j < l.length then l.take j ++ a::l.drop (j+1) else l := by
   induction l generalizing j with
   | nil => cases j <;> rfl
   | cons b l ih =>
     cases j with
     | zero => rfl
     | succ j =>
       simp only [List.set_cons_succ, List.length_cons, Nat.succ_lt_succ_iff, List.take_succ_cons,
         List.drop_succ_cons]
       rw [ih]
       split <;> simp_all

 theorem set_poly {α : Type} (enc : α ↪ List Bool) :
     ComputableTidilyInPolyTime (fun p : (List α × ℕ) × α => p.1.1.set p.1.2 p.2)
       (encPair (encPair (encList enc) encUnary) enc) (encList enc) := by
   simp_rw [set_eq_parts]
   apply ComputableTidilyInPolyTime.ite_decide
   · fun_prop
   · apply ComputableTidilyInPolyTime.listAppend'
     · fun_prop
     · apply ComputableTidilyInPolyTime.cons'
       · fun_prop
       · apply ComputableTidilyInPolyTime.listDropWithInput
         · fun_prop
         · fun_prop
   · fun_prop

 def readSymbols {g : ℕ} (tape : List (Fin (g+3))) : List Bool :=
   ((tape.map OTM.bitOf).takeWhile (·.isSome)).reduceOption

 theorem readSymbols_cons {g : ℕ} (a : Fin (g+3)) (l : List (Fin (g+3))) :
     readSymbols (a::l) = match OTM.bitOf a with
       | none => []
       | some b => b::readSymbols l := by
   cases h : OTM.bitOf a <;> simp [readSymbols, h]

 theorem readSymbols_prefix {g : ℕ} (l : List (Fin (g+3))) :
     readSymbols l =
       (l.take ((l.map fun a => (OTM.bitOf a).isSome).idxOf false)).map (fun a => (OTM.bitOf a).getD false) := by
   induction l with
   | nil => rfl
   | cons a l ih =>
     rw [readSymbols_cons]
     cases h : OTM.bitOf a with
     | none => simp [h]
     | some b => simp [h, ih]

 theorem readSymbols_poly (g : ℕ) :
     ComputableTidilyInPolyTime (readSymbols (g := g)) (encList (FiniteCodec.encFin (g+3))) encBits := by
   let enc := FiniteCodec.encFin (g+3)
   have hflags : ComputableTidilyInPolyTime (fun l : List (Fin (g+3)) => l.map fun a => (OTM.bitOf a).isSome)
       (encList enc) (encList encBool) := ComputableTidilyInPolyTime.map (ComputableTidilyInPolyTime.of_finite _)
   have hindex : ComputableTidilyInPolyTime
       (fun l : List (Fin (g+3)) => (l.map fun a => (OTM.bitOf a).isSome).idxOf false)
       (encList enc) encUnary := by
     apply (ComputableTidilyInPolyTime.idxOfWithInput (encA := encBool))
     · exact hflags
     · fun_prop
   have hprefix : ComputableTidilyInPolyTime
       (fun l : List (Fin (g+3)) => l.take ((l.map fun a => (OTM.bitOf a).isSome).idxOf false))
       (encList enc) (encList enc) := by
     exact ComputableTidilyInPolyTime.listTakeWithInput ComputableTidilyInPolyTime.id' hindex
   have hbits := (ComputableTidilyInPolyTime.map
     (encA := enc) (encB := encBool) (ComputableTidilyInPolyTime.of_finite
       (fun a : Fin (g+3) => (OTM.bitOf a).getD false))).comp hprefix
   have hraw := (bits_encList_polyTime encBool).2.tidy.comp hbits
   convert hraw using 1
   funext l
   exact readSymbols_prefix l

end StudentTeacher976.Adaptivity.NativeCPU

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeCPU
open QAdvFew.PoQOracle Turing.MultiTapeTM

 abbrev DeltaResult (M : OTM) := Fin (M.k+6) × Fin (M.g+3) × Fin 3 × Fin (M.g+3) × Fin 3
 def deltaEnc (M : OTM) : DeltaResult M ↪ List Bool :=
   encPair (FiniteCodec.encFin (M.k+6)) (encPair (FiniteCodec.encFin (M.g+3))
     (encPair (FiniteCodec.encFin 3) (encPair (FiniteCodec.encFin (M.g+3)) (FiniteCodec.encFin 3))))

 def deltaBody (M : OTM) (c : Body M) : DeltaResult M :=
   M.δ c.1 (c.2.1.getD c.2.2.1 0) (c.2.2.2.1.getD c.2.2.2.2 0)

 theorem deltaBody_poly (M : OTM) : ComputableTidilyInPolyTime (deltaBody M) (bodyEnc M) (deltaEnc M) := by
   have htable : ComputableTidilyInPolyTime
       (fun p : Fin (M.k+6) × Fin (M.g+3) × Fin (M.g+3) => M.δ p.1 p.2.1 p.2.2)
       (encPair (FiniteCodec.encFin (M.k+6)) (encPair (FiniteCodec.encFin (M.g+3)) (FiniteCodec.encFin (M.g+3))))
       (deltaEnc M) := ComputableTidilyInPolyTime.of_finite _
   apply htable.comp (g := fun c : Body M => (c.1, c.2.1.getD c.2.2.1 0, c.2.2.2.1.getD c.2.2.2.2 0))
   unfold bodyEnc
   apply ComputableTidilyInPolyTime.prod
   · fun_prop
   · apply ComputableTidilyInPolyTime.prod
     · fun_prop
     · fun_prop

 theorem moveHead_poly : ComputableTidilyInPolyTime (fun p : ℕ × Fin 3 => moveHead p.1 p.2)
     (encPair encUnary (FiniteCodec.encFin 3)) encUnary := by
   have hm : ComputableTidilyInPolyTime (fun m : Fin 3 => m.val) (FiniteCodec.encFin 3) encUnary :=
     ComputableTidilyInPolyTime.of_finite _
   unfold moveHead
   fun_prop

 def normalBody (M : OTM) (c : Body M) : Body M :=
   let d := deltaBody M c
   (d.1, c.2.1.set c.2.2.1 d.2.1, moveHead c.2.2.1 d.2.2.1,
     c.2.2.2.1.set c.2.2.2.2 d.2.2.2.1, moveHead c.2.2.2.2 d.2.2.2.2)

 theorem normalBody_poly (M : OTM) : ComputableTidilyInPolyTime (normalBody M) (bodyEnc M) (bodyEnc M) := by
   have hd := deltaBody_poly M
   have hwset := set_poly (FiniteCodec.encFin (M.g+3))
   unfold normalBody
   change ComputableTidilyInPolyTime
     (fun c : Body M => ((deltaBody M c).1, c.2.1.set c.2.2.1 (deltaBody M c).2.1,
       moveHead c.2.2.1 (deltaBody M c).2.2.1,
       c.2.2.2.1.set c.2.2.2.2 (deltaBody M c).2.2.2.1,
       moveHead c.2.2.2.2 (deltaBody M c).2.2.2.2)) (bodyEnc M) (bodyEnc M)
   unfold bodyEnc
   apply ComputableTidilyInPolyTime.prod
   · exact (ComputableTidilyInPolyTime.fst _ _).comp hd
   · apply ComputableTidilyInPolyTime.prod
     · apply hwset.comp (g := fun c : Body M => ((c.2.1,c.2.2.1),(deltaBody M c).2.1))
       fun_prop (disch := unfold bodyEnc deltaEnc at *; fun_prop)
     · apply ComputableTidilyInPolyTime.prod
       · apply moveHead_poly.comp (g := fun c : Body M => (c.2.2.1,(deltaBody M c).2.2.1))
         fun_prop (disch := unfold bodyEnc deltaEnc at *; fun_prop)
       · apply ComputableTidilyInPolyTime.prod
         · apply hwset.comp (g := fun c : Body M => ((c.2.2.2.1,c.2.2.2.2),(deltaBody M c).2.2.2.1))
           fun_prop (disch := unfold bodyEnc deltaEnc at *; fun_prop)
         · apply moveHead_poly.comp (g := fun c : Body M => (c.2.2.2.2,(deltaBody M c).2.2.2.2))
           fun_prop (disch := unfold bodyEnc deltaEnc at *; fun_prop)

 theorem stepBody_poly (M : OTM) :
     ComputableTidilyInPolyTime (fun p : Bool × Body M => stepBody M p.1 p.2)
       (encPair encBool (bodyEnc M)) (bodyEnc M) := by
   change ComputableTidilyInPolyTime
     (fun p : Bool × Body M => if p.2.1 = 1 ∨ p.2.1 = 2 then p.2
       else if p.2.1 = 3 then (if p.1 then 4 else 5, p.2.2) else normalBody M p.2)
     (encPair encBool (bodyEnc M)) (bodyEnc M)
   apply ComputableTidilyInPolyTime.ite_decide
   · unfold bodyEnc
     apply ComputableTidilyInPolyTime.decide_or <;> fun_prop
   · exact ComputableTidilyInPolyTime.snd _ _
   · apply ComputableTidilyInPolyTime.ite_decide
     · unfold bodyEnc; fun_prop
     · unfold bodyEnc
       apply ComputableTidilyInPolyTime.prod
       · have h : ComputableTidilyInPolyTime (fun b : Bool => (if b then 4 else 5 : Fin (M.k+6))) encBool (FiniteCodec.encFin (M.k+6)) :=
           ComputableTidilyInPolyTime.of_finite _
         exact h.comp (ComputableTidilyInPolyTime.fst _ _)
       · fun_prop
     · exact (normalBody_poly M).comp (ComputableTidilyInPolyTime.snd _ _)

end StudentTeacher976.Adaptivity.NativeCPU

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeCPU
open QAdvFew.PoQOracle

 theorem stepBody_encode (M : OTM) (O : Oracle) (R : ℕ) (c : M.Cfg)
     (hw : -(R : ℤ) ≤ c.wh ∧ c.wh ≤ R) (hq : -(R : ℤ) ≤ c.qh ∧ c.qh ≤ R)
     (hnextw : -(R : ℤ) ≤ (M.step O c).wh ∧ (M.step O c).wh ≤ R)
     (hnextq : -(R : ℤ) ≤ (M.step O c).qh ∧ (M.step O c).qh ≤ R) :
     stepBody M (O (OTM.readBits c.query c.qhi)) (encodeBody M R c) = encodeBody M R (M.step O c) := by
   by_cases hh : c.state = 1 ∨ c.state = 2
   · simp [stepBody, encodeBody, OTM.step, hh]
   by_cases h3 : c.state = 3
   · simp (disch := omega) [stepBody, encodeBody, OTM.step, hh, h3, Fin.ext_iff, Nat.mod_eq_of_lt]
   let d := M.δ c.state (c.work c.wh) (c.query c.qh)
   have hs := OTM.Precheck.normal_step M O c hh h3 d.1 d.2.1 d.2.2.2.1 d.2.2.1 d.2.2.2.2 rfl
   have hwa : 0 ≤ c.wh+(d.2.2.1.val : ℤ)-1+R := by rw [hs] at hnextw; dsimp only at hnextw; omega
   have hqa : 0 ≤ c.qh+(d.2.2.2.2.val : ℤ)-1+R := by rw [hs] at hnextq; dsimp only at hnextq; omega
   have hmW := moveHead_encode R c.wh d.2.2.1 (by omega) hwa
   have hmQ := moveHead_encode R c.qh d.2.2.2.2 (by omega) hqa
   have hwup := encodeTape_update M R c.work c.wh hw d.2.1
   have hqup := encodeTape_update M R c.query c.qh hq d.2.2.2.1
   rw [hs]
   simp only [stepBody, encodeBody, hh, h3, ↓reduceIte, encodeTape_at M R c.work c.wh hw,
     encodeTape_at M R c.query c.qh hq]
   change (d.1, (encodeTape M R c.work).set (c.wh+R).toNat d.2.1,
       moveHead (c.wh+R).toNat d.2.2.1,
       (encodeTape M R c.query).set (c.qh+R).toNat d.2.2.2.1,
       moveHead (c.qh+R).toNat d.2.2.2.2) =
     (d.1, encodeTape M R (Function.update c.work c.wh d.2.1),
       (c.wh+(d.2.2.1.val : ℤ)-1+R).toNat,
       encodeTape M R (Function.update c.query c.qh d.2.2.2.1),
       (c.qh+(d.2.2.2.2.val : ℤ)-1+R).toNat)
   rw [hwup, hqup, hmW, hmQ]

end StudentTeacher976.Adaptivity.NativeCPU

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeCPU
open QAdvFew.PoQOracle

 theorem move_bounds (z : ℤ) (m : Fin 3) : z-1 ≤ z+(m.val : ℤ)-1 ∧ z+(m.val : ℤ)-1 ≤ z+1 := by
   have hm := m.isLt
   omega

 theorem cfg_bounds_step (M : OTM) (O : Oracle) (x : List Bool) (t : ℕ) (c : M.Cfg)
     (h : -(t : ℤ) ≤ c.wh ∧ c.wh ≤ t ∧ -(t : ℤ) ≤ c.qh ∧ c.qh ≤ t ∧
       c.whi ≤ x.length+t ∧ c.qhi ≤ t) :
     -((t+1 : ℕ) : ℤ) ≤ (M.step O c).wh ∧ (M.step O c).wh ≤ t+1 ∧
       -((t+1 : ℕ) : ℤ) ≤ (M.step O c).qh ∧ (M.step O c).qh ≤ t+1 ∧
       (M.step O c).whi ≤ x.length+(t+1) ∧ (M.step O c).qhi ≤ t+1 := by
   unfold OTM.step
   split
   · try dsimp only
     omega
   · split
     · try dsimp only
       omega
     · try dsimp only
       have hw := move_bounds c.wh (M.δ c.state (c.work c.wh) (c.query c.qh)).2.2.1
       have hq := move_bounds c.qh (M.δ c.state (c.work c.wh) (c.query c.qh)).2.2.2.2
       omega

 theorem cfg_bounds (M : OTM) (O : Oracle) (x : List Bool) (t : ℕ) :
     let c := M.runCfg O x t;
     -(t : ℤ) ≤ c.wh ∧ c.wh ≤ t ∧ -(t : ℤ) ≤ c.qh ∧ c.qh ≤ t ∧
       c.whi ≤ x.length+t ∧ c.qhi ≤ t := by
   induction t with
   | zero => simp [OTM.runCfg, OTM.init]
   | succ t ih =>
     rw [OTM.runCfg, Function.iterate_succ_apply']
     exact cfg_bounds_step M O x t (M.runCfg O x t) ih

 theorem radius_bounds (M : OTM) (O : Oracle) (x : List Bool) (T t : ℕ) (ht : t ≤ T) :
     let R := x.length+T+1;
     let c := M.runCfg O x t;
     -(R : ℤ) ≤ c.wh ∧ c.wh ≤ R ∧ -(R : ℤ) ≤ c.qh ∧ c.qh ≤ R ∧ c.whi ≤ R ∧ c.qhi ≤ R := by
   have h := cfg_bounds M O x t
   dsimp only at *
   omega

 theorem encodeTape_tail (M : OTM) (R : ℕ) (tape : ℤ → Fin (M.g+3)) :
     (encodeTape M R tape).drop R = (List.range (R+1)).map (fun (j : ℕ) => tape (j : ℤ)) := by
   apply List.ext_getElem
   · simp <;> omega
   · intro j hj hj'
     have hj0 : j < R+1 := by simpa using hj'
     simp only [List.getElem_drop, encodeTape, List.getElem_map, List.getElem_range]
     congr 1
     omega

 theorem readSymbols_range (M : OTM) (R : ℕ) (tape : ℤ → Fin (M.g+3)) :
     NativeCPU.readSymbols ((List.range (R+1)).map (fun (j : ℕ) => tape (j : ℤ))) = OTM.readBits tape R := by
   unfold NativeCPU.readSymbols OTM.readBits
   have hcast : ((R : ℤ)+1).toNat = R+1 := by omega
   rw [hcast]
   rw [List.map_map]
   change (((List.range (R+1)).map (fun (j : ℕ) => OTM.bitOf (tape (j : ℤ)))).takeWhile (·.isSome)).reduceOption =
     (((List.flatMap (fun (j : ℕ) => [(j : ℤ)]) (List.range (R+1))).map (fun j => OTM.bitOf (tape j))).takeWhile (·.isSome)).reduceOption
   rw [← List.map_eq_flatMap, List.map_map]
   rfl

 theorem read_encoded_query (M : OTM) (O : Oracle) (x : List Bool) (T t : ℕ) (ht : t ≤ T) :
     readSymbols ((encodeBody M (x.length+T+1) (M.runCfg O x t)).2.2.2.1.drop (x.length+T+1)) =
       OTM.readBits (M.runCfg O x t).query (M.runCfg O x t).qhi := by
   change readSymbols ((encodeTape M (x.length+T+1) (M.runCfg O x t).query).drop _) = _
   rw [encodeTape_tail, readSymbols_range]
   have hv := (OTM.valid_runCfg M O x t).query
   have hb := (radius_bounds M O x T t ht).2.2.2.2.2
   exact OTM.readBits_of_le _ _ _ hv.zero_hi hb (hv.outside _ (by omega))

end StudentTeacher976.Adaptivity.NativeCPU

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeCPU
open QAdvFew.PoQOracle Turing.MultiTapeTM

 def initialTape (M : OTM) (R : ℕ) (x : List Bool) : List (Fin (M.g+3)) :=
   (List.range (2*R+1)).map fun (j : ℕ) =>
     if R ≤ j ∧ j < R+x.length then OTM.symOf M.g (x.getD (j-R) false) else 0

 theorem initialTape_encode (M : OTM) (R : ℕ) (x : List Bool) :
     initialTape M R x = encodeTape M R (M.init x).work := by
   apply List.map_congr_left
   intro j hj
   have he : (R ≤ j ∧ j < R+x.length) ↔ (0 ≤ (j : ℤ)-R ∧ (j : ℤ)-R < x.length) := by omega
   simp only [OTM.init, ← he]
   split
   · congr 2
     omega
   · rfl

 theorem query_init_encode (M : OTM) (R : ℕ) (x : List Bool) :
     encodeTape M R (M.init x).query = List.replicate (2*R+1) 0 := by simp [encodeTape, OTM.init]

 theorem initialTape_poly (M : OTM) :
     ComputableTidilyInPolyTime (fun p : ℕ × List Bool => initialTape M p.1 p.2)
       (encPair encUnary encBits) (encList (FiniteCodec.encFin (M.g+3))) := by
   have hsym : ComputableTidilyInPolyTime (OTM.symOf M.g) encBool (FiniteCodec.encFin (M.g+3)) :=
     ComputableTidilyInPolyTime.of_finite _
   unfold initialTape
   apply ComputableTidilyInPolyTime.mapWithInput (encA := encUnary)
   · apply ComputableTidilyInPolyTime.range.comp
     fun_prop
   · apply ComputableTidilyInPolyTime.ite_decide
     · apply ComputableTidilyInPolyTime.decide_and <;> fun_prop
     · apply hsym.comp
       fun_prop
     · fun_prop

 def radius (p : Polynomial ℕ) (x : List Bool) : ℕ := x.length+p.eval x.length+1
 def initialBody (M : OTM) (R : ℕ) (x : List Bool) : Body M :=
   (0, initialTape M R x, R, List.replicate (2*R+1) 0, R)
 def initialState (M : OTM) (p : Polynomial ℕ) (x : List Bool) : State M :=
   (p.eval x.length, radius p x, initialBody M (radius p x) x)

 theorem initialBody_encode (M : OTM) (R : ℕ) (x : List Bool) :
     initialBody M R x = encodeBody M R (M.init x) := by
   simp only [initialBody, encodeBody, OTM.init, Int.zero_add, Int.toNat_natCast]
   rw [initialTape_encode M R x]
   change (0, encodeTape M R (M.init x).work, R, List.replicate (2*R+1) 0, R) =
     (0, encodeTape M R (M.init x).work, R, encodeTape M R (M.init x).query, R)
   rw [query_init_encode M R x]

 theorem radius_poly (p : Polynomial ℕ) : ComputableTidilyInPolyTime (radius p) encBits encUnary := by
   unfold radius
   have hp := ComputableTidilyInPolyTime.unary_eval p
   fun_prop

 theorem initialState_poly (M : OTM) (p : Polynomial ℕ) :
     ComputableTidilyInPolyTime (initialState M p) encBits (stateEnc M) := by
   have hr := radius_poly p
   have hp := (ComputableTidilyInPolyTime.unary_eval p).comp ComputableTidilyInPolyTime.length_bits
   have hi := (initialTape_poly M).comp (hr.prod ComputableTidilyInPolyTime.id')
   unfold initialState initialBody stateEnc bodyEnc
   apply ComputableTidilyInPolyTime.prod hp
   apply ComputableTidilyInPolyTime.prod hr
   apply ComputableTidilyInPolyTime.prod
   · fun_prop
   · apply ComputableTidilyInPolyTime.prod hi
     apply ComputableTidilyInPolyTime.prod hr
     apply ComputableTidilyInPolyTime.prod
     · apply ComputableTidilyInPolyTime.replicate
       · fun_prop
       · fun_prop
     · exact hr

end StudentTeacher976.Adaptivity.NativeCPU

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeCPU
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 def queryBody (M : OTM) (R : ℕ) (c : Body M) : Word := readSymbols (c.2.2.2.1.drop R)
 def outputBody (M : OTM) (decision : Bool) (R : ℕ) (c : Body M) : Word :=
   if decision then [decide (c.1 = 1)] else readSymbols (c.2.1.drop R)

 def response (M : OTM) (decision : Bool) (st : State M) : Word :=
   if st.1 = 0 then OracleDriver.record true false [] (outputBody M decision st.2.1 st.2.2)
   else OracleDriver.record false false (queryBody M st.2.1 st.2.2) (stateEnc M st)

 noncomputable def cpu (M : OTM) (p : Polynomial ℕ) (decision : Bool) (w : Word) : Word :=
   if w.headD false then
     let st := (stateDecoder M).decode ((frames (w.drop 3)).tail.headD [])
     response M decision (st.1-1, st.2.1, stepBody M (w.getD 2 false) st.2.2)
   else if (w.drop 1).headD false then (frames (w.drop 3)).tail.headD []
   else response M decision (initialState M p (w.drop 2))

 theorem frames_two (q s : Word) : frames (frame q ++ frame s) = [q,s] := by
   rw [frames_frame_append]
   have hs := frames_frame_append s []
   simp only [List.append_nil, frames_nil] at hs
   rw [hs]

 theorem cpu_initial (M : OTM) (p : Polynomial ℕ) (decision : Bool) (x : Word) :
     cpu M p decision (OracleDriver.shifted x) = response M decision (initialState M p x) := by
   simp [cpu, OracleDriver.shifted]

 theorem cpu_continue (M : OTM) (p : Polynomial ℕ) (decision answer : Bool) (q : Word) (st : State M) :
     cpu M p decision (OracleDriver.record false answer q (stateEnc M st)) =
       response M decision (st.1-1, st.2.1, stepBody M answer st.2.2) := by
   simp [cpu, OracleDriver.record, frames_two, Decoder.decode_enc]

 theorem cpu_final (M : OTM) (p : Polynomial ℕ) (decision answer : Bool) (q out : Word) :
     cpu M p decision (OracleDriver.finalRecord answer q out) = out := by
   simp [cpu, OracleDriver.finalRecord, frames_two]

end StudentTeacher976.Adaptivity.NativeCPU

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeCPU
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 theorem frame_poly : ComputableTidilyInPolyTime frame encBits encBits :=
   ComputableTidilyInPolyTime.of_linear (ComputableTidilyInLinearTimeAndSpace.of_frame (fun _ => rfl))

 theorem record_poly :
     ComputableTidilyInPolyTime (fun p : Bool × Bool × Word × Word => OracleDriver.record p.1 p.2.1 p.2.2.1 p.2.2.2)
       (encPair encBool (encPair encBool (encPair encBits encBits))) encBits := by
   have hf := frame_poly
   unfold OracleDriver.record
   fun_prop

 theorem queryBody_poly (M : OTM) :
     ComputableTidilyInPolyTime (fun p : ℕ × Body M => queryBody M p.1 p.2)
       (encPair encUnary (bodyEnc M)) encBits := by
   apply (readSymbols_poly M.g).comp (g := fun p : ℕ × Body M => p.2.2.2.2.1.drop p.1)
   unfold bodyEnc
   fun_prop

 theorem outputBody_poly (M : OTM) (decision : Bool) :
     ComputableTidilyInPolyTime (fun p : ℕ × Body M => outputBody M decision p.1 p.2)
       (encPair encUnary (bodyEnc M)) encBits := by
   cases decision with
   | false =>
     apply (readSymbols_poly M.g).comp (g := fun p : ℕ × Body M => p.2.2.1.drop p.1)
     unfold bodyEnc
     fun_prop
   | true =>
     unfold outputBody bodyEnc
     simp only [Bool.true_eq, if_true]
     fun_prop

 theorem response_poly (M : OTM) (decision : Bool) :
     ComputableTidilyInPolyTime (response M decision) (stateEnc M) encBits := by
   have hq := (queryBody_poly M).comp
     (ComputableTidilyInPolyTime.snd encUnary (encPair encUnary (bodyEnc M)))
   have ho := (outputBody_poly M decision).comp
     (ComputableTidilyInPolyTime.snd encUnary (encPair encUnary (bodyEnc M)))
   have he := ComputableTidilyInPolyTime.encode (stateEnc M)
   unfold response
   apply ComputableTidilyInPolyTime.ite_decide
   · unfold stateEnc; fun_prop
   · apply record_poly.comp (g := fun st : State M => (true,false,[],outputBody M decision st.2.1 st.2.2))
     exact (ComputableTidilyInPolyTime.const true).prod
       ((ComputableTidilyInPolyTime.const false).prod ((ComputableTidilyInPolyTime.const []).prod ho))
   · apply record_poly.comp (g := fun st : State M => (false,false,queryBody M st.2.1 st.2.2,stateEnc M st))
     exact (ComputableTidilyInPolyTime.const false).prod
       ((ComputableTidilyInPolyTime.const false).prod (hq.prod he))

 def parseStateWord (w : Word) : Word := (frames (w.drop 3)).tail.headD []

 theorem parseStateWord_poly : ComputableTidilyInPolyTime parseStateWord encBits encBits := by
   have hf := computableInDegree_frames.computableInPolyTime.tidy
   unfold parseStateWord
   apply (ComputableTidilyInPolyTime.headD (encA := encBits) (encL := encList encBits) []).comp
   apply (ComputableTidilyInPolyTime.tail (encA := encBits) (encL := encList encBits)).comp
   apply hf.comp
   fun_prop

 def advanceState (M : OTM) (answer : Bool) (st : State M) : State M :=
   (st.1-1, st.2.1, stepBody M answer st.2.2)

 theorem advanceState_poly (M : OTM) :
     ComputableTidilyInPolyTime (fun p : Bool × State M => advanceState M p.1 p.2)
       (encPair encBool (stateEnc M)) (stateEnc M) := by
   have hs := stepBody_poly M
   unfold advanceState stateEnc
   apply ComputableTidilyInPolyTime.prod
   · fun_prop
   · apply ComputableTidilyInPolyTime.prod
     · fun_prop
     · apply hs.comp (g := fun p : Bool × State M => (p.1,p.2.2.2))
       fun_prop

 theorem cpu_poly (M : OTM) (p : Polynomial ℕ) (decision : Bool) :
     ComputableTidilyInPolyTime (cpu M p decision) encBits encBits := by
   have hd := (stateDecoder M).computableInPolyTime.tidy.comp parseStateWord_poly
   have hr := response_poly M decision
   have hi := initialState_poly M p
   have ha := advanceState_poly M
   unfold cpu
   apply (ComputableTidilyInPolyTime.headD false).cond
   · apply hr.comp (g := fun w : Word => advanceState M (w.getD 2 false)
       ((stateDecoder M).decode (parseStateWord w)))
     apply ha.comp (g := fun w : Word => (w.getD 2 false,(stateDecoder M).decode (parseStateWord w)))
     apply ComputableTidilyInPolyTime.prod
     · fun_prop
     · exact hd
   · apply ComputableTidilyInPolyTime.cond
     · fun_prop
     · exact parseStateWord_poly
     · apply hr.comp (g := fun w : Word => initialState M p (w.drop 2))
       apply hi.comp (g := fun w : Word => w.drop 2)
       fun_prop

end StudentTeacher976.Adaptivity.NativeCPU

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeCPU
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 theorem encFin_length (n : ℕ) (a : Fin n) : (FiniteCodec.encFin n a).length = a.val := by
   change (List.replicate a.val true).length = a.val
   simp

 theorem encList_length_le {α : Type} (enc : α ↪ Word) (K : ℕ) (hk : ∀ a, (enc a).length ≤ K) (l : List α) :
     (encList enc l).length ≤ (2*K+1)*l.length := by
   induction l with
   | nil => simp
   | cons a l ih =>
     rw [encList_cons, List.length_append, length_frame]
     have ha := hk a
     simp only [List.length_cons]
     nlinarith

 theorem readSymbols_length {g : ℕ} (l : List (Fin (g+3))) : (readSymbols l).length ≤ l.length := by
   induction l with
   | nil => rfl
   | cons a l ih =>
     rw [readSymbols_cons]
     cases h : OTM.bitOf a <;> simp [ih]

 theorem body_size (M : OTM) (R : ℕ) (c : M.Cfg)
     (hw : -(R : ℤ) ≤ c.wh ∧ c.wh ≤ R) (hq : -(R : ℤ) ≤ c.qh ∧ c.qh ≤ R) :
     (bodyEnc M (encodeBody M R c)).length ≤ 100*(M.k+M.g+10)*(R+1) := by
   have hs (a : Fin (M.g+3)) : (FiniteCodec.encFin (M.g+3) a).length ≤ M.g+2 := by
     rw [encFin_length]
     have ha := a.isLt
     omega
   have hW := encList_length_le (FiniteCodec.encFin (M.g+3)) (M.g+2) hs (encodeTape M R c.work)
   have hQ := encList_length_le (FiniteCodec.encFin (M.g+3)) (M.g+2) hs (encodeTape M R c.query)
   simp only [length_encodeTape] at hW hQ
   have hheadW : (c.wh+R).toNat ≤ 2*R := by omega
   have hheadQ : (c.qh+R).toNat ≤ 2*R := by omega
   have hstate := c.state.isLt
   simp only [bodyEnc, encodeBody, encPair_apply, List.length_append, length_frame,
     encFin_length, encUnary_apply, List.length_replicate]
   nlinarith

 theorem query_size (M : OTM) (R : ℕ) (c : Body M) (h : c.2.2.2.1.length = 2*R+1) :
     (queryBody M R c).length ≤ R+1 := by
   have hh := readSymbols_length (c.2.2.2.1.drop R)
   simp only [List.length_drop, h] at hh
   change (readSymbols (c.2.2.2.1.drop R)).length ≤ R+1
   omega

 theorem output_size (M : OTM) (decision : Bool) (R : ℕ) (c : Body M) (h : c.2.1.length = 2*R+1) :
     (outputBody M decision R c).length ≤ R+1 := by
   cases decision with
   | true => simp [outputBody]
   | false =>
     have hh := readSymbols_length (c.2.1.drop R)
     simp only [List.length_drop, h] at hh
     simp only [outputBody, Bool.false_eq_true, ↓reduceIte]
     omega

end StudentTeacher976.Adaptivity.NativeCPU

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeCPU
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 def runtimeState (M : OTM) (O : Oracle) (x : Word) (T t : ℕ) : State M :=
   (T-t, x.length+T+1, encodeBody M (x.length+T+1) (M.runCfg O x t))

 theorem runtime_initial (M : OTM) (O : Oracle) (p : Polynomial ℕ) (x : Word) :
     initialState M p x = runtimeState M O x (p.eval x.length) 0 := by
   simp only [initialState, runtimeState, radius, Nat.sub_zero, OTM.runCfg, Function.iterate_zero_apply]
   rw [initialBody_encode]

 theorem read_encoded_work (M : OTM) (O : Oracle) (x : Word) (T t : ℕ) (ht : t ≤ T) :
     readSymbols ((encodeBody M (x.length+T+1) (M.runCfg O x t)).2.1.drop (x.length+T+1)) =
       OTM.readBits (M.runCfg O x t).work (M.runCfg O x t).whi := by
   change readSymbols ((encodeTape M (x.length+T+1) (M.runCfg O x t).work).drop _) = _
   rw [encodeTape_tail, readSymbols_range]
   have hv := (OTM.valid_runCfg M O x t).work
   have hb := (radius_bounds M O x T t ht).2.2.2.2.1
   exact OTM.readBits_of_le _ _ _ hv.zero_hi hb (hv.outside _ (by omega))

 def nativeOutput (M : OTM) (O : Oracle) (x : Word) (T : ℕ) (decision : Bool) : Word :=
   if decision then [(M.result O x T).getD false] else M.output O x T

 theorem runtime_output (M : OTM) (O : Oracle) (x : Word) (T : ℕ) (decision : Bool) :
     outputBody M decision (x.length+T+1) (encodeBody M (x.length+T+1) (M.runCfg O x T)) =
       nativeOutput M O x T decision := by
   cases decision with
   | false => exact read_encoded_work M O x T T le_rfl
   | true =>
     unfold outputBody nativeOutput
     simp only [Bool.true_eq, ↓reduceIte]
     have he : (M.result O x T).getD false = decide ((M.runCfg O x T).state = 1) := by
       by_cases h1 : (M.runCfg O x T).state = 1
       · simp [OTM.result, h1]
       · by_cases h2 : (M.runCfg O x T).state = 2 <;> simp (disch := omega) [OTM.result, h1, h2, Fin.ext_iff, Nat.mod_eq_of_lt]
     rw [he]
     rfl

 theorem runtime_advance (M : OTM) (O : Oracle) (x : Word) (T t : ℕ) (ht : t < T) :
     advanceState M (O (queryBody M (x.length+T+1) (runtimeState M O x T t).2.2)) (runtimeState M O x T t) =
       runtimeState M O x T (t+1) := by
   have h := radius_bounds M O x T t (by omega)
   have hn := radius_bounds M O x T (t+1) (by omega)
   have hs : M.runCfg O x (t+1) = M.step O (M.runCfg O x t) := Function.iterate_succ_apply' _ _ _
   rw [hs] at hn
   have hstep := stepBody_encode M O (x.length+T+1) (M.runCfg O x t)
     ⟨h.1,h.2.1⟩ ⟨h.2.2.1,h.2.2.2.1⟩ ⟨hn.1,hn.2.1⟩ ⟨hn.2.2.1,hn.2.2.2.1⟩
   have hq := read_encoded_query M O x T t (by omega)
   change queryBody M (x.length+T+1) (encodeBody M (x.length+T+1) (M.runCfg O x t)) = _ at hq
   unfold advanceState runtimeState
   rw [hq, hstep, ← hs]
   congr 1 <;> omega

 def traceBound (M : OTM) (x : Word) (T : ℕ) : ℕ := 1000*(M.k+M.g+10)*(x.length+T+2)

 theorem runtime_state_size (M : OTM) (O : Oracle) (x : Word) (T t : ℕ) (ht : t ≤ T) :
     (stateEnc M (runtimeState M O x T t)).length ≤ 200*(M.k+M.g+10)*(x.length+T+2) := by
   have h := radius_bounds M O x T t ht
   have hs := body_size M (x.length+T+1) (M.runCfg O x t) ⟨h.1,h.2.1⟩ ⟨h.2.2.1,h.2.2.2.1⟩
   simp only [runtimeState, stateEnc, encPair_apply, List.length_append, length_frame,
     encUnary_apply, List.length_replicate]
   have ht' : T-t ≤ x.length+T+1 := by omega
   nlinarith

 theorem runtime_query_size (M : OTM) (O : Oracle) (x : Word) (T t : ℕ) :
     (queryBody M (x.length+T+1) (runtimeState M O x T t).2.2).length ≤ x.length+T+2 := by
   apply query_size M
   simp [runtimeState, encodeBody]

 theorem runtime_record_size (M : OTM) (O : Oracle) (x : Word) (T t : ℕ) (ht : t ≤ T)
     (done answer : Bool) :
     (OracleDriver.record done answer
       (queryBody M (x.length+T+1) (runtimeState M O x T t).2.2)
       (stateEnc M (runtimeState M O x T t))).length ≤ traceBound M x T := by
   have hs := runtime_state_size M O x T t ht
   have hq := runtime_query_size M O x T t
   simp only [OracleDriver.record, List.length_cons, List.length_append, length_frame]
   unfold traceBound
   nlinarith

 theorem runtime_done_size (M : OTM) (O : Oracle) (x : Word) (T : ℕ) (decision : Bool) :
     (OracleDriver.record true false [] (nativeOutput M O x T decision)).length ≤ traceBound M x T := by
   have ho := output_size M decision (x.length+T+1) (encodeBody M (x.length+T+1) (M.runCfg O x T))
     (by simp [encodeBody])
   rw [runtime_output] at ho
   simp only [OracleDriver.record, List.length_cons, List.length_append, length_frame, List.length_nil, Nat.mul_zero, Nat.zero_add]
   unfold traceBound
   nlinarith

end StudentTeacher976.Adaptivity.NativeCPU

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeCPU
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 theorem cpu_native_trace (M : OTM) (p : Polynomial ℕ) (decision : Bool) (O : Oracle) (x : Word) :
     OracleDriver.Trace (cpu M p decision) O (traceBound M x (p.eval x.length))
       (OracleDriver.shifted x) (nativeOutput M O x (p.eval x.length) decision) (p.eval x.length) := by
   let T := p.eval x.length
   let B := traceBound M x T
   have go : ∀ m t : ℕ, m+t=T → ∀ input : Word,
       input.length ≤ B → cpu M p decision input = response M decision (runtimeState M O x T t) →
       OracleDriver.Trace (cpu M p decision) O B input (nativeOutput M O x T decision) m := by
     intro m
     induction m with
     | zero =>
       intro t h input hinput hcpu
       have ht : t=T := by omega
       subst t
       have hz : (runtimeState M O x T T).1 = 0 := by simp [runtimeState]
       have hr : cpu M p decision input = OracleDriver.record true false [] (nativeOutput M O x T decision) := by
         rw [hcpu, response, if_pos hz]
         exact congrArg (OracleDriver.record true false []) (runtime_output M O x T decision)
       exact OracleDriver.Trace.done input false [] (nativeOutput M O x T decision)
         (nativeOutput M O x T decision) hinput (runtime_done_size M O x T decision) hr
         (cpu_final M p decision false [] (nativeOutput M O x T decision))
     | succ m ih =>
       intro t h input hinput hcpu
       have ht : t<T := by omega
       let st := runtimeState M O x T t
       let q := queryBody M (x.length+T+1) st.2.2
       let s := stateEnc M st
       have hn : st.1 ≠ 0 := by dsimp [st, runtimeState]; omega
       have hr : cpu M p decision input = OracleDriver.record false false q s := by
         rw [hcpu, response, if_neg hn]
         rfl
       have hnext : cpu M p decision (OracleDriver.record false (O q) q s) =
           response M decision (runtimeState M O x T (t+1)) := by
         rw [cpu_continue]
         change response M decision (advanceState M (O q) st) = _
         rw [runtime_advance M O x T t ht]
       have hsize : (OracleDriver.record false (O q) q s).length ≤ B :=
         runtime_record_size M O x T t (by omega) false (O q)
       have htail := ih (t+1) (by omega) (OracleDriver.record false (O q) q s) hsize hnext
       exact OracleDriver.Trace.query input false q s (nativeOutput M O x T decision) m hinput
         (runtime_record_size M O x T t (by omega) false false) hr htail
   apply go T 0 (by omega)
   · simp only [OracleDriver.shifted, List.length_cons]
     dsimp [B, traceBound]
     nlinarith
   · rw [cpu_initial, runtime_initial M O p x]

 theorem native_protocol (M : OTM) (p : Polynomial ℕ) (decision : Bool) :
     ∃ C : Word → Word, ComputableInPolyTime C encBits encBits ∧
       ∃ B : Polynomial ℕ, ∀ O : Oracle, ∀ x : Word,
         OracleDriver.Trace C O (B.eval x.length) (OracleDriver.shifted x)
           (nativeOutput M O x (p.eval x.length) decision) (p.eval x.length) := by
   refine ⟨cpu M p decision, ComputableInPolyTime.of_tidy (cpu_poly M p decision),
     1000*Polynomial.C (M.k+M.g+10)*(Polynomial.X+p+2), ?_⟩
   intro O x
   simpa only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_C, Polynomial.eval_add,
     Polynomial.eval_X, traceBound] using cpu_native_trace M p decision O x

end StudentTeacher976.Adaptivity.NativeCPU

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeCPU
open QAdvFew.PoQOracle Turing.MultiTapeTM

 def pureStep (M : OTM) (O : Oracle) (st : State M) : State M :=
   advanceState M (O (queryBody M st.2.1 st.2.2)) st

 theorem pureStep_poly (M : OTM) (O : Oracle) (hO : ComputableTidilyInPolyTime O encBits encBool) :
     ComputableTidilyInPolyTime (pureStep M O) (stateEnc M) (stateEnc M) := by
   have hquery := (queryBody_poly M).comp (ComputableTidilyInPolyTime.snd encUnary (encPair encUnary (bodyEnc M)))
   have hanswer := hO.comp hquery
   exact (advanceState_poly M).comp (hanswer.prod ComputableTidilyInPolyTime.id')

 theorem pureStep_runtime (M : OTM) (O : Oracle) (x : Word) (T t : ℕ) (ht : t < T) :
     pureStep M O (runtimeState M O x T t) = runtimeState M O x T (t+1) :=
   runtime_advance M O x T t ht

 theorem pure_iterate_runtime (M : OTM) (O : Oracle) (p : Polynomial ℕ) (x : Word) (t : ℕ)
     (ht : t ≤ p.eval x.length) :
     (pureStep M O)^[t] (initialState M p x) = runtimeState M O x (p.eval x.length) t := by
   induction t with
   | zero => exact runtime_initial M O p x
   | succ t ih =>
     rw [Function.iterate_succ_apply', ih (by omega)]
     exact pureStep_runtime M O x _ t (by omega)

 theorem fold_ticks {α : Type} (step : α → α) (n : ℕ) (a : α) :
     (List.replicate n ()).foldl (fun s _ => step s) a = step^[n] a := by
   induction n generalizing a with
   | zero => rfl
   | succ n ih => rw [List.replicate_succ, List.foldl_cons, ih, Function.iterate_succ_apply]

 def runPure (M : OTM) (O : Oracle) (p : Polynomial ℕ) (x : Word) : State M :=
   (List.replicate (p.eval x.length) ()).foldl (fun st _ => pureStep M O st) (initialState M p x)

 theorem runPure_poly (M : OTM) (O : Oracle) (p : Polynomial ℕ)
     (hO : ComputableTidilyInPolyTime O encBits encBool) :
     ComputableTidilyInPolyTime (runPure M O p) encBits (stateEnc M) := by
   have hp := (ComputableTidilyInPolyTime.unary_eval p).comp ComputableTidilyInPolyTime.length_bits
   have hlist : ComputableTidilyInPolyTime (fun x : Word => List.replicate (p.eval x.length) ()) encBits (encList encUnit) :=
     ComputableTidilyInPolyTime.replicate hp (ComputableTidilyInPolyTime.const ())
   have hstep := (pureStep_poly M O hO).comp (ComputableTidilyInPolyTime.fst (stateEnc M) encUnit)
   have hB : ComputableTidilyInPolyTime (fun x : Word => 200*(M.k+M.g+10)*(x.length+p.eval x.length+2)) encBits encUnary := by
     fun_prop
   unfold runPure
   apply ComputableTidilyInPolyTime.foldl' hlist (initialState_poly M p) hstep hB.polyBounded
   intro x i hi
   simp only [List.length_replicate] at hi
   rw [List.take_replicate, Nat.min_eq_left hi, fold_ticks, pure_iterate_runtime M O p x i hi]
   exact runtime_state_size M O x _ i hi

 theorem native_pure (M : OTM) (O : Oracle) (p : Polynomial ℕ) (decision : Bool)
     (hO : ComputableTidilyInPolyTime O encBits encBool) :
     ComputableTidilyInPolyTime (fun x : Word => nativeOutput M O x (p.eval x.length) decision) encBits encBits := by
   have hf := runPure_poly M O p hO
   have hout := (outputBody_poly M decision).comp
     (ComputableTidilyInPolyTime.snd encUnary (encPair encUnary (bodyEnc M)))
   have hc := hout.comp hf
   apply hc.of_enc_eq
   intro x
   change nativeOutput M O x (p.eval x.length) decision =
     outputBody M decision (runPure M O p x).2.1 (runPure M O p x).2.2
   rw [runPure, fold_ticks, pure_iterate_runtime M O p x _ le_rfl]
   exact (runtime_output M O x (p.eval x.length) decision).symm

end StudentTeacher976.Adaptivity.NativeCPU

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
namespace StudentTeacher976.Adaptivity
open QAdvFew.PoQOracle Turing.MultiTapeTM

 theorem getD_true_iff (o : Option Bool) : o.getD false = true ↔ o = some true := by
   cases o with
   | none => simp
   | some b => cases b <;> simp

 theorem sigma_zero_oracle_pure (O : Oracle) (hO : {x | O x = true} ∈ Sigma 0) :
     ComputableTidilyInPolyTime O encBits encBool := by
   obtain ⟨V, p, ps, hps, ht, hL⟩ := hO
   have he : ps = [] := List.length_eq_zero_iff.mp hps
   subst ps
   simp only [List.map_nil, AvgPHETH.AltLen] at hL
   have htuple : ComputableTidilyInPolyTime (fun x : Word => tup [x]) encBits encBits :=
     TupleCodec.encode_poly.comp (ComputableTidilyInPolyTime.id'.cons' (ComputableTidilyInPolyTime.const []))
   have hf := (NativeBinary.native_polytime V p ht).tidy.comp htuple
   apply hf.of_enc_eq
   intro x
   change [O x] = [(V.result (fun _ => false) (tup [x]) (p.eval (tup [x]).length)).getD false]
   congr 1
   apply Bool.eq_iff_iff.mpr
   exact (hL x).trans (getD_true_iff _).symm

 theorem inFP_zero_pure {f : Word → Word} (h : InFP 0 f) :
     ComputableTidilyInPolyTime f encBits encBits := by
   obtain ⟨O, M, p, hO, hf⟩ := h
   have hnative := NativeCPU.native_pure M O p false (sigma_zero_oracle_pure O hO)
   apply hnative.of_enc_eq
   intro x
   exact (hf x).2.symm

 theorem length_function_pure (r : ℕ → ℕ) (hr : PolyTimeLength r) :
     ComputableTidilyInPolyTime (fun x : Word => r x.length) encBits encUnary := by
   have h := ComputableTidilyInPolyTime.length_bits.comp (inFP_zero_pure hr)
   simpa only [Function.comp_def, List.length_replicate] using h

 theorem resource_function_pure (r : ℕ → ℕ) (hr : PolyTimeLength r) :
     ComputableTidilyInPolyTime (fun x : Word => resource r x.length) encBits encUnary := by
   have hpad : ComputableTidilyInPolyTime (fun x : Word => if x.isEmpty then [false] else x) encBits encBits :=
     ComputableTidilyInPolyTime.bitsIsEmpty.cond (ComputableTidilyInPolyTime.const [false]) ComputableTidilyInPolyTime.id'
   have h := (length_function_pure r hr).comp hpad
   convert h using 1
   funext x
   cases x with
   | nil => simp [resource]
   | cons b x => simp [resource, Nat.max_eq_right (show 1 ≤ x.length+1 by omega)]

end StudentTeacher976.Adaptivity

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.UnaryDivision
open Turing.MultiTapeTM

 def step (d : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
   if s.2+1=d then (s.1+1,0) else (s.1,s.2+1)

 theorem step_poly : ComputableTidilyInPolyTime (fun p : ℕ × (ℕ × ℕ) => step p.1 p.2)
     (encPair encUnary (encPair encUnary encUnary)) (encPair encUnary encUnary) := by
   unfold step
   apply ComputableTidilyInPolyTime.ite_decide <;> fun_prop

 def Inv (d n : ℕ) (s : ℕ × ℕ) : Prop :=
   d*s.1+s.2=n ∧ (d=0 ∨ s.2<d) ∧ s.1≤n ∧ s.2≤n ∧ (d=0 → s.1=0)

 theorem preserve (d n : ℕ) (s : ℕ × ℕ) (h : Inv d n s) : Inv d (n+1) (step d s) := by
   rcases s with ⟨q,r⟩
   unfold Inv at *
   dsimp only at h
   unfold step
   split
   · rename_i he
     dsimp only
     refine ⟨by nlinarith [h.1], by omega, by omega, by omega, by omega⟩
   · rename_i he
     dsimp only
     refine ⟨by omega, by omega, by omega, by omega, h.2.2.2.2⟩

 theorem invariant (d n : ℕ) : Inv d n ((step d)^[n] (0,0)) := by
   induction n with
   | zero => simp [Inv] <;> omega
   | succ n ih => rw [Function.iterate_succ_apply']; exact preserve d n _ ih

 theorem correct (d n : ℕ) : (step d)^[n] (0,0) = (n/d,n%d) := by
   have h := invariant d n
   unfold Inv at h
   by_cases hd : d=0
   · subst d
     apply Prod.ext <;> simp only [Nat.div_zero, Nat.mod_zero]
     · exact h.2.2.2.2 rfl
     · omega
   · have hrem : ((step d)^[n] (0,0)).2 < d := by omega
     have hdiv : n/d = ((step d)^[n] (0,0)).1 := Nat.div_eq_of_lt_le (by nlinarith [h.1]) (by nlinarith [h.1])
     have he := Nat.div_add_mod n d
     apply Prod.ext
     · exact hdiv.symm
     · rw [hdiv] at he
       omega

 theorem fold_ticks {α : Type} (f : α → α) (n : ℕ) (a : α) :
     (List.replicate n ()).foldl (fun s _ => f s) a = f^[n] a := by
   induction n generalizing a with
   | zero => rfl
   | succ n ih => rw [List.replicate_succ, List.foldl_cons, ih, Function.iterate_succ_apply]

 theorem divmod_poly : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (p.1/p.2,p.1%p.2))
     (encPair encUnary encUnary) (encPair encUnary encUnary) := by
   have hpar := ComputableTidilyInPolyTime.snd encUnary encUnary
   have hlist : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => List.replicate p.1 ())
       (encPair encUnary encUnary) (encList encUnit) :=
     ComputableTidilyInPolyTime.replicate (ComputableTidilyInPolyTime.fst encUnary encUnary)
       (ComputableTidilyInPolyTime.const ())
   have hinit : ComputableTidilyInPolyTime (fun _ : ℕ × ℕ => ((0,0) : ℕ × ℕ))
       (encPair encUnary encUnary) (encPair encUnary encUnary) := ComputableTidilyInPolyTime.const _
   have hstep := step_poly.comp
     (ComputableTidilyInPolyTime.fst (encPair encUnary (encPair encUnary encUnary)) encUnit)
   have hbound : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => 3*p.1+1)
       (encPair encUnary encUnary) encUnary := by fun_prop
   have hfold := ComputableTidilyInPolyTime.foldlWith (encA := encUnit) (step := fun d s (_ : Unit) => step d s) hpar hlist hinit hstep hbound.polyBounded
   have hf : ComputableTidilyInPolyTime
       (fun p : ℕ × ℕ => (List.replicate p.1 ()).foldl (fun s _ => step p.2 s) (0,0))
       (encPair encUnary encUnary) (encPair encUnary encUnary) := by
     apply hfold
     intro p i hi
     simp only [List.length_replicate] at hi
     rw [List.take_replicate, Nat.min_eq_left hi, fold_ticks]
     have h := invariant p.2 i
     unfold Inv at h
     simp only [length_encPair, encUnary_apply, List.length_replicate]
     omega
   apply hf.of_enc_eq
   intro p
   rw [fold_ticks, correct]

 theorem div_poly : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1/p.2)
     (encPair encUnary encUnary) encUnary := divmod_poly.fst'
 theorem mod_poly : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1%p.2)
     (encPair encUnary encUnary) encUnary := divmod_poly.snd'

end StudentTeacher976.Adaptivity.UnaryDivision

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AuxiliaryData
open QAdvFew.PoQOracle Turing.MultiTapeTM
private theorem readComponent_encoded (u v : Word) :
    readComponent (u.flatMap (fun b => [true, b]) ++ [false, false] ++ v) = some (u, v) := by
  induction u with
  | nil => simp [readComponent]
  | cons b u ih =>
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ih ⊢
    simpa [readComponent] using congrArg (fun o => o.map (fun p : Word × Word => (b :: p.1, p.2))) ih

private theorem readComponent_sound (s u v : Word) (h : readComponent s = some (u, v)) :
    s = u.flatMap (fun b => [true, b]) ++ [false, false] ++ v := by
  induction s using readComponent.induct generalizing u v with
  | case1 rest =>
    simp only [readComponent, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | case2 b rest ih =>
    simp only [readComponent, Option.map_eq_some_iff] at h
    obtain ⟨⟨u', v'⟩, huv, heq⟩ := h
    cases heq
    simp [ih _ _ huv]
  | case3 s => simp_all [readComponent]

private theorem decodeTupleFuel_sound (fuel : ℕ) (s : Word) (Y : List Word)
    (h : decodeTupleFuel fuel s = some Y) : tup Y = s := by
  induction fuel generalizing s Y with
  | zero =>
    cases s with
    | nil =>
      have : Y = [] := by simpa [decodeTupleFuel] using h.symm
      subst Y
      rfl
    | cons b s => simp [decodeTupleFuel] at h
  | succ fuel ih =>
    cases s with
    | nil =>
      have : Y = [] := by simpa [decodeTupleFuel] using h.symm
      subst Y
      rfl
    | cons b s =>
      simp only [decodeTupleFuel, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨⟨u, v⟩, huv, Y', hY', rfl⟩ := h
      have hs := readComponent_sound (b :: s) u v huv
      simp only [tup, List.flatMap_cons]
      rw [← ih v Y' hY'] at hs
      simpa [tup, List.append_assoc] using hs.symm

private theorem decodeTupleFuel_encoded (Y : List Word) (fuel : ℕ) (hf : Y.length ≤ fuel) :
    decodeTupleFuel fuel (tup Y) = some Y := by
  induction Y generalizing fuel with
  | nil => simp [tup, decodeTupleFuel]
  | cons u Y ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hnon : tup (u :: Y) ≠ [] := by
        simp [tup, List.flatMap_cons]
      have heq : tup (u :: Y) = u.flatMap (fun b => [true, b]) ++ [false, false] ++ tup Y := by
        simp [tup, List.append_assoc]
      rw [heq]
      cases hword : u.flatMap (fun b => [true, b]) ++ [false, false] ++ tup Y with
      | nil => exact (hnon (heq.trans hword)).elim
      | cons b s =>
        rw [decodeTupleFuel, ← hword, readComponent_encoded]
        simp [ih fuel (by simpa using hf)]

private theorem tup_length (Y : List Word) : (tup Y).length = 2 * (Y.map List.length).sum + 2 * Y.length := by
  induction Y with
  | nil => simp [tup]
  | cons u Y ih =>
    have hbits : (u.flatMap fun b => [true, b]).length = 2 * u.length := by
      induction u with
      | nil => simp
      | cons b u ih => simp [ih]; omega
    simp only [tup, List.flatMap_cons, List.length_append, hbits, List.length_cons,
      List.length_nil, List.map_cons, List.sum_cons]
    change 2 * u.length + (1 + (1 + 0)) + (tup Y).length = _
    rw [ih]
    ring

 theorem decodeTuple_encoded (Y : List Word) : decodeTuple (tup Y) = some Y :=
  decodeTupleFuel_encoded Y _ (by rw [tup_length]; omega)

 theorem decodeTuple_sound (s : Word) (Y : List Word) (h : decodeTuple s = some Y) : tup Y = s :=
  decodeTupleFuel_sound s.length s Y h


 theorem decode_validated (w : Word) : StudentTeacher976.Adaptivity.decodeTuple w =
     if tup (TupleCodec.decodeTuple w) = w then some (TupleCodec.decodeTuple w) else none := by
   cases h : StudentTeacher976.Adaptivity.decodeTuple w with
   | none =>
     have hn : tup (TupleCodec.decodeTuple w) ≠ w := by
       intro he
       have hc := decodeTuple_encoded (TupleCodec.decodeTuple w)
       rw [he, h] at hc
       cases hc
     simp [hn]
   | some Y =>
     have he := decodeTuple_sound w Y h
     have hy : TupleCodec.decodeTuple w = Y := by rw [← he, TupleCodec.decode_tup]
     simp only [hy]
     rw [if_pos he]

 theorem decode_poly : ComputableTidilyInPolyTime StudentTeacher976.Adaptivity.decodeTuple
     encBits (encOption (encList encBits)) := by
   have hd := TupleCodec.decoder_poly.tidy
   have he := TupleCodec.encode_poly.comp hd
   change ComputableTidilyInPolyTime (fun w : Word => StudentTeacher976.Adaptivity.decodeTuple w) encBits (encOption (encList encBits))
   simp_rw [decode_validated]
   apply ComputableTidilyInPolyTime.ite_decide
   · exact he.decide_eq' ComputableTidilyInPolyTime.id'
   · exact (ComputableTidilyInPolyTime.optionSome (encList encBits)).comp hd
   · exact ComputableTidilyInPolyTime.const none

 theorem leading_true_length (w : Word) : (w.takeWhile id).length = w.idxOf false := by
   induction w with
   | nil => rfl
   | cons b w ih => cases b <;> simp [ih]

 theorem first_false_poly : ComputableTidilyInPolyTime (fun w : Word => w.idxOf false) encBits encUnary := by
   have hw := (bits_encList_polyTime encBool).1.tidy
   exact (ComputableTidilyInPolyTime.idxOf encBool).comp (hw.prod (ComputableTidilyInPolyTime.const false))

 theorem rawIndex_poly : ComputableTidilyInPolyTime (fun p : Word × Word => rawIndex p.1 p.2)
     (encPair encBits encBits) encUnary := by
   unfold rawIndex
   simp_rw [leading_true_length]
   apply first_false_poly.comp (g := fun p : Word × Word => p.2.take p.1.length)
   fun_prop

 theorem rawWitness_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (fun p : Word × Word × Word => rawWitness W p.1 p.2.1 p.2.2)
       (encPair encBits (encPair encBits encBits)) encBits := by
   have hp := ComputableTidilyInPolyTime.unary_eval W.length
   unfold rawWitness
   fun_prop

 theorem decodeBlocks_poly : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × Word => decodeBlocks p.1 p.2.1 p.2.2)
     (encPair encUnary (encPair encUnary encBits)) (encList encBits) := by
   unfold decodeBlocks
   apply ComputableTidilyInPolyTime.mapWithInput (encA := encUnary)
   · apply ComputableTidilyInPolyTime.range.comp
     fun_prop
   · fun_prop

 theorem blockInput_poly (r : ℕ → ℕ) (hr : PolyTimeLength r) :
     ComputableTidilyInPolyTime (blockInput r) encBits (encOption (encList encBits)) := by
   have hk := resource_function_pure r hr
   have hn := ComputableTidilyInPolyTime.length_bits
   have hdiv := UnaryDivision.div_poly.comp (hn.prod hk)
   have hmod := UnaryDivision.mod_poly.comp (hn.prod hk)
   have hb := decodeBlocks_poly.comp (hdiv.prod (hk.prod ComputableTidilyInPolyTime.id'))
   unfold blockInput
   dsimp only
   apply ComputableTidilyInPolyTime.ite_decide
   · apply ComputableTidilyInPolyTime.decide_and
     · fun_prop
     · apply ComputableTidilyInPolyTime.decide_and
       · fun_prop
       · exact hmod.decide_eq' (ComputableTidilyInPolyTime.const 0)
   · exact (ComputableTidilyInPolyTime.optionSome (encList encBits)).comp hb
   · exact ComputableTidilyInPolyTime.const none

end StudentTeacher976.Adaptivity.AuxiliaryData

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeBatch
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl
open NativeCPU

 abbrev State (M : OTM) := Word × List Word × Word × NativeCPU.State M
 def stateEnc (M : OTM) : State M ↪ Word :=
   encPair encBits (encPair (encList encBits) (encPair encBits (NativeCPU.stateEnc M)))
 noncomputable def stateDecoder (M : OTM) : Decoder (stateEnc M) :=
   Decoder.bits.pair (Decoder.bits.list.pair (Decoder.bits.pair (NativeCPU.stateDecoder M)))

 def emit (M : OTM) (st : State M) : Word :=
   OracleDriver.record false false (queryBody M st.2.2.2.2.1 st.2.2.2.2.2) (stateEnc M st)

 def begin (M : OTM) (p : Polynomial ℕ) (post : Word × Word → Word)
     (ctx : Word) (todo : List Word) (acc : Word) : Word :=
   if todo.isEmpty then OracleDriver.record true false [] (post (ctx,acc.reverse))
   else emit M (ctx,todo.tail,acc,initialState M p (todo.headD []))

 def advanceResponse (M : OTM) (p : Polynomial ℕ) (post : Word × Word → Word) (answer : Bool) (st : State M) : Word :=
   let native := advanceState M answer st.2.2.2
   if native.1=0 then begin M p post st.1 st.2.1 (decide (native.2.2.1=1)::st.2.2.1)
   else emit M (st.1,st.2.1,st.2.2.1,native)

 noncomputable def cpu (M : OTM) (p : Polynomial ℕ) (prep : Word → List Word) (post : Word × Word → Word) (w : Word) : Word :=
   if w.headD false then advanceResponse M p post (w.getD 2 false)
     ((stateDecoder M).decode ((frames (w.drop 3)).tail.headD []))
   else if (w.drop 1).headD false then (frames (w.drop 3)).tail.headD []
   else begin M p post (w.drop 2) (prep (w.drop 2)) []

 theorem cpu_initial (M : OTM) (p : Polynomial ℕ) (prep : Word → List Word) (post : Word × Word → Word) (x : Word) :
     cpu M p prep post (OracleDriver.shifted x) = begin M p post x (prep x) [] := by simp [cpu, OracleDriver.shifted]
 theorem cpu_continue (M : OTM) (p : Polynomial ℕ) (prep : Word → List Word) (post : Word × Word → Word)
     (answer : Bool) (q : Word) (st : State M) :
     cpu M p prep post (OracleDriver.record false answer q (stateEnc M st)) = advanceResponse M p post answer st := by
   simp [cpu, OracleDriver.record, NativeCPU.frames_two, Decoder.decode_enc]
 theorem cpu_final (M : OTM) (p : Polynomial ℕ) (prep : Word → List Word) (post : Word × Word → Word)
     (answer : Bool) (q out : Word) : cpu M p prep post (OracleDriver.finalRecord answer q out) = out := by
   simp [cpu, OracleDriver.finalRecord, NativeCPU.frames_two]

 theorem emit_poly (M : OTM) : ComputableTidilyInPolyTime (emit M) (stateEnc M) encBits := by
   have hq := (NativeCPU.queryBody_poly M).comp (encIn := stateEnc M)
     (g := fun st : State M => (st.2.2.2.2.1,st.2.2.2.2.2)) (by unfold stateEnc NativeCPU.stateEnc; fun_prop)
   have he := ComputableTidilyInPolyTime.encode (stateEnc M)
   exact NativeCPU.record_poly.comp
     ((ComputableTidilyInPolyTime.const false).prod ((ComputableTidilyInPolyTime.const false).prod (hq.prod he)))

 theorem begin_poly (M : OTM) (p : Polynomial ℕ) (post : Word × Word → Word)
     (hpost : ComputableTidilyInPolyTime post (encPair encBits encBits) encBits) :
     ComputableTidilyInPolyTime (fun st : Word × List Word × Word => begin M p post st.1 st.2.1 st.2.2)
       (encPair encBits (encPair (encList encBits) encBits)) encBits := by
   have hi := NativeCPU.initialState_poly M p
   have he := emit_poly M
   unfold begin
   apply ComputableTidilyInPolyTime.cond
   · fun_prop
   · apply NativeCPU.record_poly.comp (g := fun st : Word × List Word × Word => (true,false,[],post (st.1,st.2.2.reverse)))
     fun_prop
   · apply he.comp (g := fun st : Word × List Word × Word => (st.1,st.2.1.tail,st.2.2,initialState M p (st.2.1.headD [])))
     unfold stateEnc
     fun_prop

 theorem advanceResponse_poly (M : OTM) (p : Polynomial ℕ) (post : Word × Word → Word)
     (hpost : ComputableTidilyInPolyTime post (encPair encBits encBits) encBits) :
     ComputableTidilyInPolyTime (fun p' : Bool × State M => advanceResponse M p post p'.1 p'.2)
       (encPair encBool (stateEnc M)) encBits := by
   have hn := (NativeCPU.advanceState_poly M).comp (encIn := encPair encBool (stateEnc M))
     (g := fun p' : Bool × State M => (p'.1,p'.2.2.2.2)) (by unfold stateEnc; fun_prop)
   have hcounter : ComputableTidilyInPolyTime (fun p' : Bool × State M => (advanceState M p'.1 p'.2.2.2.2).1)
       (encPair encBool (stateEnc M)) encUnary := by
     unfold NativeCPU.stateEnc at hn
     exact hn.fst'
   have hcontrol : ComputableTidilyInPolyTime (fun p' : Bool × State M => (advanceState M p'.1 p'.2.2.2.2).2.2.1)
       (encPair encBool (stateEnc M)) (FiniteCodec.encFin (M.k+6)) := by
     unfold NativeCPU.stateEnc NativeCPU.bodyEnc at hn
     exact hn.snd'.snd'.fst'
   have hbit := hcontrol.decide_eq' (ComputableTidilyInPolyTime.const 1)
   have hb := begin_poly M p post hpost
   have he := emit_poly M
   unfold advanceResponse
   apply ComputableTidilyInPolyTime.ite_decide
   · exact hcounter.decide_eq' (ComputableTidilyInPolyTime.const 0)
   · apply hb.comp (g := fun p' : Bool × State M => (p'.2.1,p'.2.2.1,
       decide ((advanceState M p'.1 p'.2.2.2.2).2.2.1=1)::p'.2.2.2.1))
     apply ComputableTidilyInPolyTime.prod
     · unfold stateEnc; fun_prop
     · apply ComputableTidilyInPolyTime.prod
       · unfold stateEnc; fun_prop
       · apply ComputableTidilyInPolyTime.bitsCons hbit
         unfold stateEnc; fun_prop
   · apply he.comp (g := fun p' : Bool × State M =>
       (p'.2.1,p'.2.2.1,p'.2.2.2.1,advanceState M p'.1 p'.2.2.2.2))
     unfold stateEnc
     apply ComputableTidilyInPolyTime.prod
     · fun_prop
     · apply ComputableTidilyInPolyTime.prod
       · fun_prop
       · apply ComputableTidilyInPolyTime.prod
         · fun_prop
         · exact hn

 theorem cpu_poly (M : OTM) (p : Polynomial ℕ) (prep : Word → List Word) (post : Word × Word → Word)
     (hprep : ComputableTidilyInPolyTime prep encBits (encList encBits))
     (hpost : ComputableTidilyInPolyTime post (encPair encBits encBits) encBits) :
     ComputableTidilyInPolyTime (cpu M p prep post) encBits encBits := by
   have hd := (stateDecoder M).computableInPolyTime.tidy.comp NativeCPU.parseStateWord_poly
   have hc := advanceResponse_poly M p post hpost
   have hb := begin_poly M p post hpost
   unfold cpu
   apply (ComputableTidilyInPolyTime.headD false).cond
   · apply hc.comp (g := fun w : Word => (w.getD 2 false,(stateDecoder M).decode (NativeCPU.parseStateWord w)))
     apply ComputableTidilyInPolyTime.prod
     · fun_prop
     · exact hd
   · apply ComputableTidilyInPolyTime.cond
     · fun_prop
     · exact NativeCPU.parseStateWord_poly
     · apply hb.comp (g := fun w : Word => (w.drop 2,prep (w.drop 2),[]))
       fun_prop

end StudentTeacher976.Adaptivity.NativeBatch

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeBatch
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 theorem polyEvalMono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
   simp only [Polynomial.eval_eq_sum, Polynomial.sum]
   apply Finset.sum_le_sum
   intro i hi
   exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

 theorem count_le_code (l : List Word) : l.length ≤ (encList encBits l).length := by
   induction l with
   | nil => rfl
   | cons x l ih => simp only [encList_cons, List.length_append, length_frame, encBits_apply, List.length_cons]; omega

 theorem tail_code_le (x : Word) (l : List Word) : (encList encBits l).length ≤ (encList encBits (x::l)).length := by
   simp

 theorem member_length_le {l : List Word} {x : Word} (h : x ∈ l) : x.length ≤ (encList encBits l).length := by
   induction l with
   | nil => cases h
   | cons a l ih =>
     rcases List.mem_cons.mp h with rfl | h
     · simp <;> omega
     · exact (ih h).trans (tail_code_le a l)

 def limit (M : OTM) (p postBound : Polynomial ℕ) (L : ℕ) : ℕ :=
   20*L+20+1000*(M.k+M.g+10)*(L+p.eval L+2)+2*postBound.eval (3*L+1)

 theorem current_state_size (M : OTM) (O : Oracle) (p : Polynomial ℕ) (L : ℕ)
     (ctx : Word) (todo : List Word) (acc current : Word) (t : ℕ)
     (hctx : ctx.length ≤ L) (htodo : (encList encBits todo).length ≤ L) (hacc : acc.length ≤ L)
     (hc : current.length ≤ L) (ht : t ≤ p.eval current.length) :
     (stateEnc M (ctx,todo,acc,NativeCPU.runtimeState M O current (p.eval current.length) t)).length ≤
       6*L+3+200*(M.k+M.g+10)*(L+p.eval L+2) := by
   have hs := NativeCPU.runtime_state_size M O current (p.eval current.length) t ht
   have hm := polyEvalMono p hc
   have hlarge : (NativeCPU.stateEnc M (NativeCPU.runtimeState M O current (p.eval current.length) t)).length ≤
       200*(M.k+M.g+10)*(L+p.eval L+2) :=
     hs.trans (Nat.mul_le_mul_left _ (by omega))
   simp only [stateEnc, encPair_apply, List.length_append, length_frame, encBits_apply]
   omega

 theorem current_record_size (M : OTM) (O : Oracle) (p postBound : Polynomial ℕ) (L : ℕ)
     (ctx : Word) (todo : List Word) (acc current : Word) (t : ℕ) (done answer : Bool)
     (hctx : ctx.length ≤ L) (htodo : (encList encBits todo).length ≤ L) (hacc : acc.length ≤ L)
     (hc : current.length ≤ L) (ht : t ≤ p.eval current.length) :
     let native := NativeCPU.runtimeState M O current (p.eval current.length) t;
     (OracleDriver.record done answer (NativeCPU.queryBody M native.2.1 native.2.2)
       (stateEnc M (ctx,todo,acc,native))).length ≤ limit M p postBound L := by
   have hs := current_state_size M O p L ctx todo acc current t hctx htodo hacc hc ht
   have hq := NativeCPU.runtime_query_size M O current (p.eval current.length) t
   have hm := polyEvalMono p hc
   dsimp only [NativeCPU.runtimeState] at *
   simp only [OracleDriver.record, List.length_cons, List.length_append, length_frame]
   unfold limit
   nlinarith

 theorem post_output_bound (post : Word × Word → Word) (postBound : Polynomial ℕ)
     (hpost : ∀ a : Word × Word, (post a).length ≤ postBound.eval (encPair encBits encBits a).length)
     (L : ℕ) (ctx res : Word) (hctx : ctx.length ≤ L) (hres : res.length ≤ L) :
     (post (ctx,res)).length ≤ postBound.eval (3*L+1) := by
   apply (hpost (ctx,res)).trans
   apply polyEvalMono
   simp only [encPair_apply, List.length_append, length_frame, encBits_apply]
   omega

 theorem done_record_size (M : OTM) (p postBound : Polynomial ℕ) (post : Word × Word → Word)
     (hpost : ∀ a : Word × Word, (post a).length ≤ postBound.eval (encPair encBits encBits a).length)
     (L : ℕ) (ctx res : Word) (hctx : ctx.length ≤ L) (hres : res.length ≤ L) :
     (OracleDriver.record true false [] (post (ctx,res))).length ≤ limit M p postBound L := by
   have ho := post_output_bound post postBound hpost L ctx res hctx hres
   simp only [OracleDriver.record, List.length_cons, List.length_append, length_frame, List.length_nil,
     Nat.mul_zero, Nat.zero_add]
   unfold limit
   omega

end StudentTeacher976.Adaptivity.NativeBatch

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeBatch
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 def result (M : OTM) (O : Oracle) (p : Polynomial ℕ) (w : Word) : Bool :=
   (M.result O w (p.eval w.length)).getD false
 def scores (M : OTM) (O : Oracle) (p : Polynomial ℕ) (todo : List Word) : Word := todo.map (result M O p)
 def clocks (p : Polynomial ℕ) (todo : List Word) : ℕ := (todo.map fun w => p.eval w.length).sum

 theorem runtime_result (M : OTM) (O : Oracle) (p : Polynomial ℕ) (w : Word) :
     decide ((NativeCPU.runtimeState M O w (p.eval w.length) (p.eval w.length)).2.2.1=1) = result M O p w := by
   have h := NativeCPU.runtime_output M O w (p.eval w.length) true
   change [decide ((M.runCfg O w (p.eval w.length)).state=1)] = [result M O p w] at h
   exact List.singleton_inj.mp h

 theorem begin_cons (M : OTM) (O : Oracle) (p : Polynomial ℕ) (post : Word × Word → Word)
     (ctx w : Word) (todo : List Word) (acc : Word) :
     begin M p post ctx (w::todo) acc = emit M (ctx,todo,acc,NativeCPU.runtimeState M O w (p.eval w.length) 0) := by
   simp only [begin, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.tail_cons, List.headD_cons]
   rw [NativeCPU.runtime_initial M O p w]

 theorem after_current (M : OTM) (O : Oracle) (p : Polynomial ℕ) (post : Word × Word → Word)
     (ctx : Word) (todo : List Word) (acc w : Word) (t : ℕ) (ht : t < p.eval w.length) :
     let native := NativeCPU.runtimeState M O w (p.eval w.length) t;
     advanceResponse M p post (O (NativeCPU.queryBody M native.2.1 native.2.2)) (ctx,todo,acc,native) =
       if t+1=p.eval w.length then begin M p post ctx todo (result M O p w::acc)
       else emit M (ctx,todo,acc,NativeCPU.runtimeState M O w (p.eval w.length) (t+1)) := by
   dsimp only
   have hadv : NativeCPU.advanceState M
       (O (NativeCPU.queryBody M (NativeCPU.runtimeState M O w (p.eval w.length) t).2.1
         (NativeCPU.runtimeState M O w (p.eval w.length) t).2.2))
       (NativeCPU.runtimeState M O w (p.eval w.length) t) =
       NativeCPU.runtimeState M O w (p.eval w.length) (t+1) :=
     NativeCPU.runtime_advance M O w _ t ht
   simp only [advanceResponse, hadv]
   by_cases he : t+1=p.eval w.length
   · have hz : (NativeCPU.runtimeState M O w (p.eval w.length) (t+1)).1=0 := by simp [he, NativeCPU.runtimeState]
     rw [if_pos hz, if_pos he, he, runtime_result]
   · have hz : (NativeCPU.runtimeState M O w (p.eval w.length) (t+1)).1≠0 := by dsimp [NativeCPU.runtimeState]; omega
     rw [if_neg hz, if_neg he]

 theorem batch_trace (M : OTM) (p postBound : Polynomial ℕ) (prep : Word → List Word) (post : Word × Word → Word)
     (hpost : ∀ a : Word × Word, (post a).length ≤ postBound.eval (encPair encBits encBits a).length)
     (hpos : ∀ w : Word, 0 < p.eval w.length) (O : Oracle) (L : ℕ) (ctx : Word) (hctx : ctx.length ≤ L)
     (todo : List Word) (acc input : Word) (htodo : (encList encBits todo).length ≤ L)
     (hcount : acc.length+todo.length ≤ L) (hinput : input.length ≤ limit M p postBound L)
     (hcpu : cpu M p prep post input = begin M p post ctx todo acc) :
     OracleDriver.Trace (cpu M p prep post) O (limit M p postBound L) input
       (post (ctx,acc.reverse++scores M O p todo)) (clocks p todo) := by
   induction todo generalizing acc input with
   | nil =>
     have ha : acc.length ≤ L := by simpa using hcount
     have hr : cpu M p prep post input = OracleDriver.record true false [] (post (ctx,acc.reverse)) := by
       simpa only [begin, List.isEmpty_nil, ↓reduceIte] using hcpu
     have ht := OracleDriver.Trace.done (O := O) input false [] (post (ctx,acc.reverse)) (post (ctx,acc.reverse))
       hinput (done_record_size M p postBound post hpost L ctx acc.reverse hctx (by simpa using ha)) hr
       (cpu_final M p prep post false [] _)
     simpa only [scores, clocks, List.map_nil, List.sum_nil, List.append_nil] using ht
   | cons w todo ih =>
     have htail : (encList encBits todo).length ≤ L := (tail_code_le w todo).trans htodo
     have hw : w.length ≤ L := (member_length_le ((show w ∈ w :: todo from List.mem_cons_self))).trans htodo
     have ha : acc.length ≤ L := by simp only [List.length_cons] at hcount; omega
     let T := p.eval w.length
     let out := post (ctx,acc.reverse++(result M O p w::scores M O p todo))
     have current : ∀ m t : ℕ, m+t=T → 0 < m → ∀ input : Word,
         input.length ≤ limit M p postBound L →
         cpu M p prep post input = emit M (ctx,todo,acc,NativeCPU.runtimeState M O w T t) →
         OracleDriver.Trace (cpu M p prep post) O (limit M p postBound L) input out (m+clocks p todo) := by
       intro m
       induction m with
       | zero => intro t ht hm; omega
       | succ m ihm =>
         intro t ht hm input hinput hcpu
         have ht' : t<T := by omega
         let native := NativeCPU.runtimeState M O w T t
         let query := NativeCPU.queryBody M native.2.1 native.2.2
         let code := stateEnc M (ctx,todo,acc,native)
         have hr : cpu M p prep post input = OracleDriver.record false false query code := hcpu
         have hsize := current_record_size M O p postBound L ctx todo acc w t false false hctx htail ha hw (by omega)
         have hreply := current_record_size M O p postBound L ctx todo acc w t false (O query) hctx htail ha hw (by omega)
         have hc := cpu_continue M p prep post (O query) query (ctx,todo,acc,native)
         rw [after_current M O p post ctx todo acc w t ht'] at hc
         have hnext : OracleDriver.Trace (cpu M p prep post) O (limit M p postBound L)
             (OracleDriver.record false (O query) query code) out (m+clocks p todo) := by
           by_cases hm0 : m=0
           · subst m
             have he : t+1=T := by omega
             rw [if_pos he] at hc
             have ht := ih (result M O p w::acc) (OracleDriver.record false (O query) query code) htail
               (by simp only [List.length_cons] at *; omega) hreply hc
             simpa only [out, List.reverse_cons, List.append_assoc, List.singleton_append, Nat.zero_add] using ht
           · have he : t+1≠T := by omega
             rw [if_neg he] at hc
             exact ihm (t+1) (by omega) (by omega) _ hreply hc
         have hnode := OracleDriver.Trace.query input false query code out (m+clocks p todo)
           hinput hsize hr hnext
         convert hnode using 1 <;> omega
     have hstart : cpu M p prep post input = emit M (ctx,todo,acc,NativeCPU.runtimeState M O w T 0) := by
       rw [hcpu, begin_cons M O p post ctx w todo acc]
     have ht := current T 0 (by omega) (hpos w) input hinput hstart
     simpa only [out, scores, clocks, List.map_cons, List.sum_cons] using ht

end StudentTeacher976.Adaptivity.NativeBatch

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeBatch
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 theorem clocks_bound (p : Polynomial ℕ) (todo : List Word) (L : ℕ)
     (h : ∀ w ∈ todo, w.length ≤ L) : clocks p todo ≤ todo.length*p.eval L := by
   induction todo with
   | nil => simp [clocks]
   | cons w todo ih =>
     have hw := polyEvalMono p (h w (List.mem_cons_self ..))
     have ht := ih (fun x hx => h x (List.mem_cons_of_mem w hx))
     simp only [clocks, List.map_cons, List.sum_cons, List.length_cons] at *
     nlinarith

 theorem protocol (M : OTM) (p : Polynomial ℕ) (hpos : ∀ w : Word, 0 < p.eval w.length)
     (prep : Word → List Word) (post : Word × Word → Word)
     (hprep : ComputableTidilyInPolyTime prep encBits (encList encBits))
     (hpost : ComputableTidilyInPolyTime post (encPair encBits encBits) encBits) :
     ∃ C : Word → Word, ComputableInPolyTime C encBits encBits ∧ ∃ T B : Polynomial ℕ,
       ∀ (O : Oracle) (x : Word), ∃ steps ≤ T.eval x.length,
         OracleDriver.Trace C O (B.eval x.length) (OracleDriver.shifted x)
           (post (x,scores M O p (prep x))) steps := by
   obtain ⟨qBound, hq⟩ := hprep.polyBounded_length.exists_polynomial
   obtain ⟨postBound, hp⟩ := hpost.polyBounded_length.exists_polynomial
   let len : Polynomial ℕ := Polynomial.X+qBound+1
   let T : Polynomial ℕ := len*p.comp len
   let B : Polynomial ℕ := 20*len+20+1000*Polynomial.C (M.k+M.g+10)*(len+p.comp len+2)+2*postBound.comp (3*len+1)
   refine ⟨cpu M p prep post, ComputableInPolyTime.of_tidy (cpu_poly M p prep post hprep hpost), T, B, ?_⟩
   intro O x
   let L := len.eval x.length
   have hL : L = x.length+qBound.eval x.length+1 := by simp [L, len]
   have hctx : x.length ≤ L := by omega
   have htodo : (encList encBits (prep x)).length ≤ L := (hq x).trans (by simp only [encBits_apply]; omega)
   have hcount : (prep x).length ≤ L := (count_le_code (prep x)).trans htodo
   have hsizes : ∀ w ∈ prep x, w.length ≤ L := fun w hw => (member_length_le hw).trans htodo
   have hcost : clocks p (prep x) ≤ T.eval x.length := by
     have hc := (clocks_bound p (prep x) L hsizes).trans (Nat.mul_le_mul_right _ hcount)
     simpa [T, L] using hc
   have hinput : (OracleDriver.shifted x).length ≤ limit M p postBound L := by
     simp only [OracleDriver.shifted, List.length_cons]
     unfold limit
     omega
   have ht := batch_trace M p postBound prep post hp hpos O L x hctx (prep x) [] (OracleDriver.shifted x)
     htodo (by simpa using hcount) hinput (cpu_initial M p prep post x)
   refine ⟨clocks p (prep x), hcost, ?_⟩
   have he : B.eval x.length = limit M p postBound L := by simp [B, limit, L]
   rw [he]
   simpa only [List.reverse_nil, List.nil_append] using ht

end StudentTeacher976.Adaptivity.NativeBatch

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AuxiliaryTestData
open QAdvFew.PoQOracle Turing.MultiTapeTM

 def parts (s : Word) : Word × Word × Word :=
   let l := TupleCodec.decodeTuple s
   (l.headD [], l.tail.headD [], l.tail.tail.headD [])
 theorem parts_tup (x y z : Word) : parts (tup [x,y,z]) = (x,y,z) := by simp [parts, TupleCodec.decode_tup]
 theorem parts_poly : ComputableTidilyInPolyTime parts encBits (encPair encBits (encPair encBits encBits)) := by
   have hd := TupleCodec.decoder_poly.tidy
   unfold parts
   fun_prop

 def blocks (r : ℕ → ℕ) (s : Word) : List Word := (blockInput r (parts s).1).getD []
 def candidates (s : Word) : List Word := (decodeTuple (parts s).2.1).getD []
 def index (s : Word) : ℕ := rawIndex (parts s).1 (parts s).2.2
 def coordinate (r : ℕ → ℕ) (s : Word) : Word := (blocks r s).getD (index s) []
 def challenge {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (s : Word) : Word :=
   rawWitness W (parts s).1 (coordinate r s) (parts s).2.2
 def proposed (s : Word) : Word := (candidates s).getD (index s) []

 theorem blocks_poly (r : ℕ → ℕ) (hr : PolyTimeLength r) :
     ComputableTidilyInPolyTime (blocks r) encBits (encList encBits) := by
   have hb := (AuxiliaryData.blockInput_poly r hr).comp parts_poly.fst'
   unfold blocks
   fun_prop
 theorem candidates_poly : ComputableTidilyInPolyTime candidates encBits (encList encBits) := by
   have hd := AuxiliaryData.decode_poly.comp parts_poly.snd'.fst'
   unfold candidates
   fun_prop
 theorem index_poly : ComputableTidilyInPolyTime index encBits encUnary := by
   exact AuxiliaryData.rawIndex_poly.comp (parts_poly.fst'.prod parts_poly.snd'.snd')
 theorem coordinate_poly (r : ℕ → ℕ) (hr : PolyTimeLength r) :
     ComputableTidilyInPolyTime (coordinate r) encBits encBits :=
   (ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []).comp ((blocks_poly r hr).prod index_poly)
 theorem challenge_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (hr : PolyTimeLength r) :
     ComputableTidilyInPolyTime (challenge W r) encBits encBits :=
   (AuxiliaryData.rawWitness_poly W).comp (parts_poly.fst'.prod ((coordinate_poly r hr).prod parts_poly.snd'.snd'))
 theorem proposed_poly : ComputableTidilyInPolyTime proposed encBits encBits :=
   (ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []).comp (candidates_poly.prod index_poly)

 def prep {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (s : Word) : List Word :=
   [tup [coordinate r s, challenge W r s],tup [coordinate r s, proposed s]]
 theorem prep_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (hr : PolyTimeLength r) :
     ComputableTidilyInPolyTime (prep W r) encBits (encList encBits) := by
   have ha := coordinate_poly r hr
   have hb := challenge_poly W r hr
   have hc := proposed_poly
   have h1 := TupleCodec.encode_poly.comp (ha.cons' (hb.cons' (ComputableTidilyInPolyTime.const [])))
   have h2 := TupleCodec.encode_poly.comp (ha.cons' (hc.cons' (ComputableTidilyInPolyTime.const [])))
   exact h1.cons' (h2.cons' (ComputableTidilyInPolyTime.const []))

 def shape {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (s : Word) : Bool :=
   decide ((candidates s).length = (blocks r s).length) &&
     (List.range (blocks r s).length).all (fun j => decide
       (((candidates s).getD j []).length = W.length.eval ((blocks r s).getD j []).length))
 theorem shape_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (hr : PolyTimeLength r) :
     ComputableTidilyInPolyTime (shape W r) encBits encBool := by
   have hb := blocks_poly r hr
   have hc := candidates_poly
   have he := ComputableTidilyInPolyTime.unary_eval W.length
   have hj : ComputableTidilyInPolyTime (fun p : Word × ℕ =>
       decide (((candidates p.1).getD p.2 []).length = W.length.eval ((blocks r p.1).getD p.2 []).length))
       (encPair encBits encUnary) encBool := by
     have hc' := (ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []).comp
       ((hc.comp (ComputableTidilyInPolyTime.fst encBits encUnary)).prod (ComputableTidilyInPolyTime.snd encBits encUnary))
     have hb' := (ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []).comp
       ((hb.comp (ComputableTidilyInPolyTime.fst encBits encUnary)).prod (ComputableTidilyInPolyTime.snd encBits encUnary))
     exact (ComputableTidilyInPolyTime.length_bits.comp hc').decide_eq'
       (he.comp (ComputableTidilyInPolyTime.length_bits.comp hb'))
   have hall := ComputableTidilyInPolyTime.allWithInput
     (test := fun s j => decide (((candidates s).getD j []).length = W.length.eval ((blocks r s).getD j []).length))
     (ComputableTidilyInPolyTime.range.comp (ComputableTidilyInPolyTime.length_list encBits |>.comp hb)) hj
   unfold shape
   exact ComputableTidilyInPolyTime.bool_and'
     (((ComputableTidilyInPolyTime.length_list encBits).comp hc).decide_eq'
       ((ComputableTidilyInPolyTime.length_list encBits).comp hb)) hall

 def post {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (a : Word × Word) : Word :=
   let s := a.1
   let p := parts s
   [decide (s = tup [p.1,p.2.1,p.2.2]) &&
     (if (blockInput r p.1).isSome then
       (decodeTuple p.2.1).isSome && shape W r s &&
       (!(decide (index s < (blocks r s).length) &&
           decide ((challenge W r s).length = W.length.eval (coordinate r s).length) && a.2.headD false) ||
          (decide ((proposed s).length = W.length.eval (coordinate r s).length) && a.2.getD 1 false))
      else decide (p.2.1 = []))]

 theorem post_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (hr : PolyTimeLength r) :
     ComputableTidilyInPolyTime (post W r) (encPair encBits encBits) encBits := by
   have hs := parts_poly
   have hb := blocks_poly r hr
   have hc := candidates_poly
   have hj := index_poly
   have ha := coordinate_poly r hr
   have hw := challenge_poly W r hr
   have hy := proposed_poly
   have hshape := shape_poly W r hr
   have hblock := (AuxiliaryData.blockInput_poly r hr).comp hs.fst'
   have hdecode := AuxiliaryData.decode_poly.comp hs.snd'.fst'
   have he := ComputableTidilyInPolyTime.unary_eval W.length
   have ht : ComputableTidilyInPolyTime (fun s : Word => tup [(parts s).1,(parts s).2.1,(parts s).2.2]) encBits encBits :=
     TupleCodec.encode_poly.comp (hs.fst'.cons' (hs.snd'.fst'.cons' (hs.snd'.snd'.cons' (ComputableTidilyInPolyTime.const []))))
   have henc := ComputableTidilyInPolyTime.id'.decide_eq' ht
   have hbs : ComputableTidilyInPolyTime (fun s : Word => (blockInput r (parts s).1).isSome) encBits encBool := by fun_prop
   have hds : ComputableTidilyInPolyTime (fun s : Word => (decodeTuple (parts s).2.1).isSome) encBits encBool := by fun_prop
   have hlt : ComputableTidilyInPolyTime (fun s : Word => decide (index s < (blocks r s).length)) encBits encBool := by fun_prop
   have hcw := (ComputableTidilyInPolyTime.length_bits.comp hw).decide_eq'
     (he.comp (ComputableTidilyInPolyTime.length_bits.comp ha))
   have hcy := (ComputableTidilyInPolyTime.length_bits.comp hy).decide_eq'
     (he.comp (ComputableTidilyInPolyTime.length_bits.comp ha))
   have hnil := hs.snd'.fst'.decide_eq' (ComputableTidilyInPolyTime.const ([] : Word))
   unfold post
   dsimp only
   apply ComputableTidilyInPolyTime.bitsCons
   · apply ComputableTidilyInPolyTime.bool_and'
     · exact henc.comp (ComputableTidilyInPolyTime.fst encBits encBits)
     · apply ComputableTidilyInPolyTime.cond
       · exact hbs.comp (ComputableTidilyInPolyTime.fst encBits encBits)
       · apply ComputableTidilyInPolyTime.bool_and'
         · exact ComputableTidilyInPolyTime.bool_and'
             (hds.comp (ComputableTidilyInPolyTime.fst encBits encBits))
             (hshape.comp (ComputableTidilyInPolyTime.fst encBits encBits))
         · apply ComputableTidilyInPolyTime.bool_or.comp (g := fun a : Word × Word =>
             (!(decide (index a.1 < (blocks r a.1).length) &&
               decide ((challenge W r a.1).length = W.length.eval (coordinate r a.1).length) && a.2.headD false),
              decide ((proposed a.1).length = W.length.eval (coordinate r a.1).length) && a.2.getD 1 false))
           apply ComputableTidilyInPolyTime.prod
           · apply ComputableTidilyInPolyTime.bool_not.comp
             apply ComputableTidilyInPolyTime.bool_and'
             · exact ComputableTidilyInPolyTime.bool_and'
                 (hlt.comp (ComputableTidilyInPolyTime.fst encBits encBits))
                 (hcw.comp (ComputableTidilyInPolyTime.fst encBits encBits))
             · fun_prop
           · apply ComputableTidilyInPolyTime.bool_and'
             · exact hcy.comp (ComputableTidilyInPolyTime.fst encBits encBits)
             · fun_prop
       · exact hnil.comp (ComputableTidilyInPolyTime.fst encBits encBits)
   · exact ComputableTidilyInPolyTime.const []

 theorem shape_iff {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (s : Word) :
     shape W r s = true ↔
       (candidates s).length = (blocks r s).length ∧
       ∀ j < (blocks r s).length, ((candidates s).getD j []).length = W.length.eval ((blocks r s).getD j []).length := by
   simp [shape, List.all_eq_true, List.mem_range]

 noncomputable def computed (M : OTM) (O : Oracle) (p : Polynomial ℕ)
     {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (s : Word) : Word :=
   post W r (s,NativeBatch.scores M O p (prep W r s))

 theorem computed_triple (M : OTM) (O : Oracle) (p : Polynomial ℕ)
     {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ)
     (hW : ∀ a b, NativeBatch.result M O p (tup [a,b]) = true ↔ W.test a b)
     (x y z : Word) : (computed M O p W r (tup [x,y,z])).headD false = true ↔ auxiliaryTest W r x y z := by
   classical
   cases hb : blockInput r x with
   | none => simp [computed, post, parts_tup, auxiliaryTest, hb]
   | some X =>
     cases hy : decodeTuple y with
     | none => simp [computed, post, parts_tup, auxiliaryTest, hb, hy]
     | some Y =>
       simp [computed, post, parts_tup, auxiliaryTest, hb, hy, shape, blocks, candidates,
         prep, coordinate, challenge, proposed, index, NativeBatch.scores,
         List.all_eq_true, List.mem_range, Bool.eq_false_iff, hW, ValidWitness]
       simp only [← Nat.not_lt]
       tauto

 theorem computed_correct (M : OTM) (O : Oracle) (p : Polynomial ℕ)
     {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ)
     (hW : ∀ a b, NativeBatch.result M O p (tup [a,b]) = true ↔ W.test a b)
     (s : Word) : (computed M O p W r s).headD false = true ↔
       ∃ x y z, s = tup [x,y,z] ∧ auxiliaryTest W r x y z := by
   have hraw : (computed M O p W r s).headD false = true →
       s = tup [(parts s).1,(parts s).2.1,(parts s).2.2] := by
     intro h
     exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
   constructor
   · intro h
     have he := hraw h
     refine ⟨(parts s).1,(parts s).2.1,(parts s).2.2,he,?_⟩
     exact (computed_triple M O p W r hW _ _ _).mp (he ▸ h)
   · rintro ⟨x,y,z,rfl,h⟩
     exact (computed_triple M O p W r hW x y z).mpr h

end StudentTeacher976.Adaptivity.AuxiliaryTestData

set_option autoImplicit false
open QAdvFew.PoQOracle QAdvFew.PoQOracle.OTM.FiniteControl Turing.MultiTapeTM
open StudentTeacher976.Adaptivity

theorem solution (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (hr : AdmissibleRounds r) :
    ∃ (O : Oracle) (cpu F : Word → Word) (T B : Polynomial ℕ),
      {x | O x = true} ∈ Sigma i ∧
      ComputableInPolyTime cpu encBits encBits ∧
      (∀ x : Word, ∃ steps ≤ T.eval x.length,
        OracleDriver.Trace cpu O (B.eval x.length) (OracleDriver.shifted x) (F x) steps) ∧
      ∀ s : Word, (F s).head?.getD false = true ↔
        ∃ x y z, s = tup [x,y,z] ∧ auxiliaryTest W r x y z := by
  obtain ⟨O, M, p, hO, htotal, hW⟩ := W.efficient
  have hpos : ∀ w : Word, 0 < p.eval w.length := by
    intro w
    have ht := htotal w
    by_contra hn
    have hz : p.eval w.length = 0 := by omega
    rw [hz] at ht
    norm_num [OTM.result, OTM.runCfg, OTM.init, Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < M.k + 6 by omega)] at ht
  have htest : ∀ a b, NativeBatch.result M O p (tup [a,b]) = true ↔ W.test a b := by
    intro a b
    rw [NativeBatch.result, getD_true_iff, ← hW]
    constructor
    · rintro ⟨u,v,he,huv⟩
      have hh := congrArg TupleCodec.decodeTuple he
      simp only [TupleCodec.decode_tup, List.cons.injEq, and_true] at hh
      obtain ⟨rfl,rfl⟩ := hh
      exact huv
    · exact fun h => ⟨a,b,rfl,h⟩
  obtain ⟨C,hC,T,B,htrace⟩ := NativeBatch.protocol M p hpos
    (AuxiliaryTestData.prep W r) (AuxiliaryTestData.post W r)
    (AuxiliaryTestData.prep_poly W r hr.1) (AuxiliaryTestData.post_poly W r hr.1)
  refine ⟨O,C,AuxiliaryTestData.computed M O p W r,T,B,hO,hC,htrace O,?_⟩
  intro s
  exact AuxiliaryTestData.computed_correct M O p W r htest s



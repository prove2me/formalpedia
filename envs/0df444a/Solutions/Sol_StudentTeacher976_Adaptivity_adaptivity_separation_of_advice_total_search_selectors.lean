-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.adaptivity_separation_of_advice_total_search_selectors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:54:51.592196+00:00
-- url     : https://prove2.me/submissions/639d566c-d466-418f-af75-d5d215b32fe9

import Definitions.Def_StudentTeacher976_Adaptivity_InputConversion
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
import Theorems.Thm_StudentTeacher976_Adaptivity_oracle_protocol_machine
import Definitions.Def_StudentTeacher976_Adaptivity_Teacher
import Definitions.Def_StudentTeacher976_Adaptivity_AdviceSelectors
import Mathlib
import Theorems.Thm_StudentTeacher976_Adaptivity_good_pair_advice_cover
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_StudentTeacher976_Adaptivity_Witness
import Theorems.Thm_StudentTeacher976_Adaptivity_sigma_witness_presentation
import Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_test_efficient
import Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_student_uniform
import Definitions.Def_StudentTeacher976_Adaptivity_Selectors

set_option autoImplicit false

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.FixedPoints
private theorem crossing_fixed_point (g : ℕ → ℕ) (hg : Monotone g)
    (n B : ℕ) (hpos : 1 ≤ g n) (hB : 0 < B ∧ g (n * B) ≤ B) :
    ∃ k, 0 < k ∧ k ≤ B ∧ k = g (n * k) := by
  have hex : ∃ k, 0 < k ∧ g (n * k) ≤ k := ⟨B, hB⟩
  let k := Nat.find hex
  have hk : 0 < k ∧ g (n * k) ≤ k := Nat.find_spec hex
  have hkle : k ≤ B := Nat.find_min' hex hB
  refine ⟨k, hk.1, hkle, ?_⟩
  apply Nat.le_antisymm
  · by_cases h1 : k = 1
    · simpa [h1] using hpos
    · have hprev : ¬ (0 < k - 1 ∧ g (n * (k - 1)) ≤ k - 1) :=
        Nat.find_min hex (show k - 1 < k by omega)
      have hm := hg (Nat.mul_le_mul_left n (Nat.sub_le k 1))
      omega
  · exact hk.2

 theorem fixed_point_poly_bound (g : ℕ → ℕ) (hg : Monotone g)
    (ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ m : ℕ, 0 < m → 1 ≤ g m ∧ (g m : ℝ) ≤ (m : ℝ) ^ (1 - ε)) :
    ∃ d : ℕ, ∀ n : ℕ, 0 < n → ∃ k : ℕ,
      0 < k ∧ k ≤ (n + 1) ^ d ∧ k = g (n * k) := by
  obtain ⟨d, hd⟩ := exists_nat_gt (1 / ε)
  have hdε : 1 ≤ (d : ℝ) * ε := by
    have := (div_lt_iff₀ hε).mp hd
    linarith
  refine ⟨d, ?_⟩
  intro n hn
  let B := (n + 1) ^ d
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hBre : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hpow : (n : ℝ) ^ (1 - ε) < (B : ℝ) ^ ε := by
    calc
      (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)
      _ = (n : ℝ) := Real.rpow_one _
      _ < (n : ℝ) + 1 := by linarith
      _ = ((n : ℝ) + 1) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ((n : ℝ) + 1) ^ ((d : ℝ) * ε) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hdε
      _ = (B : ℝ) ^ ε := by
        simp only [B, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
        rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
  have hstrict : ((n * B : ℕ) : ℝ) ^ (1 - ε) < (B : ℝ) := by
    calc
      ((n * B : ℕ) : ℝ) ^ (1 - ε) =
          (n : ℝ) ^ (1 - ε) * (B : ℝ) ^ (1 - ε) := by
        rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
      _ < (B : ℝ) ^ ε * (B : ℝ) ^ (1 - ε) :=
        mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hBre _)
      _ = (B : ℝ) := by
        rw [← Real.rpow_add hBre]
        simp
  have hnat : g (n * B) < B := by
    exact_mod_cast lt_of_le_of_lt (hbound (n * B) (by positivity)).2 hstrict
  exact crossing_fixed_point g hg n B (hbound n hn).1 ⟨hBpos, Nat.le_of_lt hnat⟩

end StudentTeacher976.Adaptivity.FixedPoints
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AuxiliaryStudentData
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AuxiliaryTestData (parts parts_poly parts_tup blocks blocks_poly)

 def replies (s : Word) : List Word :=
   (TupleCodec.decodeTuple (parts s).2.2).flatMap TupleCodec.decodeTuple
 theorem replies_poly : ComputableTidilyInPolyTime replies encBits (encList encBits) := by
   have hd := TupleCodec.decoder_poly.tidy
   unfold replies
   apply ComputableTidilyInPolyTime.flatMapWithInput
   · exact hd.comp parts_poly.snd'.snd'
   · exact hd.comp (ComputableTidilyInPolyTime.snd encBits encBits)
 theorem replies_encoded (x : Word) (t : ℕ) (H : List (List Word)) :
     replies (tup [x,List.replicate (t+1) true,tup (H.map tup)]) = H.flatten := by
   simp [replies, parts_tup, TupleCodec.decode_tup, List.flatMap_map, Function.comp_def]

 def pool {i : ℕ} {L : Language} (W : WitnessPresentation i L) (s a : Word) : List Word :=
   (replies s).map fun z => rawWitness W (parts s).1 a z
 theorem pool_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (fun p : Word × Word => pool W p.1 p.2)
       (encPair encBits encBits) (encList encBits) := by
   have hr := replies_poly.comp (ComputableTidilyInPolyTime.fst encBits encBits)
   have hp := parts_poly
   have hw := AuxiliaryData.rawWitness_poly W
   unfold pool
   apply ComputableTidilyInPolyTime.mapWithInput hr
   apply hw.comp (g := fun p : (Word × Word) × Word => ((parts p.1.1).1,p.1.2,p.2))
   fun_prop

 def prep {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (s : Word) : List Word :=
   (blocks r s).flatMap fun a => (pool W s a).map fun w => tup [a,w]
 theorem prep_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (hr : PolyTimeLength r) :
     ComputableTidilyInPolyTime (prep W r) encBits (encList encBits) := by
   have hp := pool_poly W
   have ht : ComputableTidilyInPolyTime (fun p : (Word × Word) × Word => tup [p.1.2,p.2])
       (encPair (encPair encBits encBits) encBits) encBits := by
     apply TupleCodec.encode_poly.comp
     fun_prop
   have hm := ComputableTidilyInPolyTime.mapWithInput (f := fun (p : Word × Word) w => tup [p.2,w]) hp ht
   unfold prep
   exact ComputableTidilyInPolyTime.flatMapWithInput (blocks_poly r hr) hm

 def select {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word) (pool : List Word) (bits : Word) : Word :=
   (((pool.zip bits).find? fun wb => decide (wb.1.length = W.length.eval a.length) && wb.2).map Prod.fst).getD
     (List.replicate (W.length.eval a.length) false)
 theorem select_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (fun p : Word × List Word × Word => select W p.1 p.2.1 p.2.2)
       (encPair encBits (encPair (encList encBits) encBits)) encBits := by
   have he := ComputableTidilyInPolyTime.unary_eval W.length
   have hz : ComputableTidilyInPolyTime (fun p : Word × List Word × Word => p.2.1.zip p.2.2)
       (encPair encBits (encPair (encList encBits) encBits)) (encList (encPair encBits encBool)) := by
     apply (ComputableTidilyInPolyTime.zip encBits encBool).comp
     apply ComputableTidilyInPolyTime.prod
     · fun_prop
     · exact (bits_encList_polyTime encBool).1.tidy.comp (by fun_prop)
   have hf := ComputableTidilyInPolyTime.findWithInput
     (test := fun (p : Word × List Word × Word) (wb : Word × Bool) =>
       decide (wb.1.length = W.length.eval p.1.length) && wb.2) hz (by fun_prop)
   unfold select
   have hzero : ComputableTidilyInPolyTime (fun p : Word × List Word × Word =>
       List.replicate (W.length.eval p.1.length) false)
       (encPair encBits (encPair (encList encBits) encBits)) encBits := by
     apply (bits_encList_polyTime encBool).2.tidy.comp
     apply ComputableTidilyInPolyTime.replicate
     · exact he.comp (ComputableTidilyInPolyTime.length_bits.comp
         (ComputableTidilyInPolyTime.fst encBits (encPair (encList encBits) encBits)))
     · exact ComputableTidilyInPolyTime.const false
   have hsel := ComputableTidilyInPolyTime.optionElimWithInput hf hzero
     (body := fun (_ : Word × List Word × Word) (wb : Word × Bool) => wb.1) (by fun_prop)
   convert hsel using 1
   funext p
   cases (p.2.1.zip p.2.2).find? (fun wb => decide (wb.1.length = W.length.eval p.1.length) && wb.2) <;> rfl

 theorem select_correct {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word)
     (pool : List Word) (f : Word → Bool) (hf : ∀ w, f w = true ↔ W.test a w) :
     select W a pool (pool.map f) =
       (pool.find? fun w => @decide (ValidWitness W a w) (Classical.propDecidable _)).getD (List.replicate (W.length.eval a.length) false) := by
   classical
   have hp : (fun w => decide (w.length = W.length.eval a.length) && f w) =
       (fun w => decide (ValidWitness W a w)) := by
     funext w
     apply Bool.eq_iff_iff.mpr
     change ((decide (w.length = W.length.eval a.length) && f w) = true) ↔
       (decide (ValidWitness W a w) = true)
     rw [Bool.and_eq_true_iff, decide_eq_true_eq, decide_eq_true_eq, hf]
     rfl
   unfold select
   rw [← List.map_prod_left_eq_zip]
   simp only [List.find?_map, Option.map_map, Function.comp_def]
   rw [hp]
   change ((pool.find? fun w => decide (ValidWitness W a w)).map id).getD _ = _
   rw [Option.map_id]
   rfl

 theorem chunk_flatMap (X : List Word) (f : Word → Word) (d j : ℕ) (hj : j < X.length)
     (hlen : ∀ a ∈ X, (f a).length = d) :
     ((X.flatMap f).drop (j*d)).take d = f (X.getD j []) := by
   induction X generalizing j with
   | nil => simp at hj
   | cons a X ih =>
     have ha := hlen a List.mem_cons_self
     cases j with
     | zero => simpa [ha] using (show ((f a ++ X.flatMap f).take (f a).length) = f a by simp)
     | succ j =>
       have hh := ih j (by simpa using hj) (fun b hb => hlen b (List.mem_cons_of_mem a hb))
       have he : (f a).drop (j*d+d) = [] := List.drop_eq_nil_iff.mpr (by omega)
       simpa [List.flatMap_cons, Nat.succ_mul, List.drop_append, ha, Nat.add_sub_cancel, he] using hh

 def assembled {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (s bits : Word) : List Word :=
   (blocks r s).zipIdx.map fun aj => select W aj.1 (pool W s aj.1)
     ((bits.drop (aj.2*(replies s).length)).take (replies s).length)

 def post {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (a : Word × Word) : Word :=
   if (parts a.1).2.1.length ≤ resource r (parts a.1).1.length+1 then
     tup [if (blockInput r (parts a.1).1).isSome then tup (assembled W r a.1 a.2) else []]
   else tup []

 theorem assembled_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (hr : PolyTimeLength r) :
     ComputableTidilyInPolyTime (fun a : Word × Word => assembled W r a.1 a.2)
       (encPair encBits encBits) (encList encBits) := by
   have hp := pool_poly W
   have hz := (ComputableTidilyInPolyTime.zipIdx encBits).comp
     ((blocks_poly r hr).comp (ComputableTidilyInPolyTime.fst encBits encBits))
   have hn := (ComputableTidilyInPolyTime.length_list encBits).comp replies_poly
   have hn' : ComputableTidilyInPolyTime (fun p : (Word × Word) × (Word × ℕ) => (replies p.1.1).length)
       (encPair (encPair encBits encBits) (encPair encBits encUnary)) encUnary :=
     hn.comp (g := fun p : (Word × Word) × (Word × ℕ) => p.1.1) (by fun_prop)
   unfold assembled
   apply ComputableTidilyInPolyTime.mapWithInput hz
   apply (select_poly W).comp (g := fun p : (Word × Word) × (Word × ℕ) =>
     (p.2.1,pool W p.1.1 p.2.1,(p.1.2.drop (p.2.2*(replies p.1.1).length)).take (replies p.1.1).length))
   apply ComputableTidilyInPolyTime.prod
   · fun_prop
   · apply ComputableTidilyInPolyTime.prod
     · apply hp.comp (g := fun p : (Word × Word) × (Word × ℕ) => (p.1.1,p.2.1))
       fun_prop
     · fun_prop

 theorem post_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (hr : PolyTimeLength r) :
     ComputableTidilyInPolyTime (post W r) (encPair encBits encBits) encBits := by
   have hs := parts_poly
   have hb := (AuxiliaryData.blockInput_poly r hr).comp hs.fst'
   have hbs := hb.optionIsSome
   have hround := (resource_function_pure r hr).comp hs.fst'
   have hround' : ComputableTidilyInPolyTime (fun s : Word => resource r (parts s).1.length+1) encBits encUnary := by fun_prop
   have hcheck := ComputableTidilyInPolyTime.unary_le'
     (ComputableTidilyInPolyTime.length_bits.comp hs.snd'.fst') hround'
   have ha := assembled_poly W r hr
   have ht := TupleCodec.encode_poly.comp ha
   unfold post
   apply ComputableTidilyInPolyTime.ite_decide
   · exact hcheck.comp (ComputableTidilyInPolyTime.fst encBits encBits)
   · apply TupleCodec.encode_poly.comp
     apply ComputableTidilyInPolyTime.cons'
     · apply ComputableTidilyInPolyTime.cond
       · exact hbs.comp (ComputableTidilyInPolyTime.fst encBits encBits)
       · exact ht
       · exact ComputableTidilyInPolyTime.const []
     · exact ComputableTidilyInPolyTime.const []
   · exact ComputableTidilyInPolyTime.const (tup [])

 theorem assembled_correct (M : OTM) (O : Oracle) (p : Polynomial ℕ)
     {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ)
     (hW : ∀ a b, NativeBatch.result M O p (tup [a,b]) = true ↔ W.test a b) (s : Word) :
     assembled W r s (NativeBatch.scores M O p (prep W r s)) =
       (blocks r s).map (fun a =>
         ((pool W s a).find? fun w => @decide (ValidWitness W a w) (Classical.propDecidable _)).getD
           (List.replicate (W.length.eval a.length) false)) := by
   classical
   have he : NativeBatch.scores M O p (prep W r s) =
       (blocks r s).flatMap (fun a => (pool W s a).map fun w => NativeBatch.result M O p (tup [a,w])) := by
     simp [NativeBatch.scores, prep, List.map_flatMap, List.map_map, Function.comp_def]
   unfold assembled
   rw [he]
   apply List.ext_getElem (by simp)
   intro j hj hj'
   simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
   have hjb : j < (blocks r s).length := by simpa using hj'
   have hh := chunk_flatMap (blocks r s)
     (fun a => (pool W s a).map fun w => NativeBatch.result M O p (tup [a,w])) (replies s).length j hjb
     (by intro a ha; simp [pool])
   rw [hh]
   rw [List.getD_eq_getElem _ _ hjb]
   exact select_correct W _ _ _ (hW _)

 noncomputable def computed (M : OTM) (O : Oracle) (p : Polynomial ℕ)
     {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ) (s : Word) : Word :=
   post W r (s,NativeBatch.scores M O p (prep W r s))

 theorem computed_encoded (M : OTM) (O : Oracle) (p : Polynomial ℕ)
     {i : ℕ} {L : Language} (W : WitnessPresentation i L) (r : ℕ → ℕ)
     (hW : ∀ a b, NativeBatch.result M O p (tup [a,b]) = true ↔ W.test a b)
     (x : Word) (t : ℕ) (H : List (List Word)) :
     computed M O p W r (tup [x,List.replicate (t+1) true,tup (H.map tup)]) = tup (auxiliaryStudent W r x t H) := by
   classical
   unfold computed post
   rw [parts_tup]
   simp only [List.length_replicate]
   have hround : t+1 ≤ resource r x.length+1 ↔ t < resource (fun m => r m+1) x.length := by
     change t+1 ≤ r (max 1 x.length)+1 ↔ t < r (max 1 x.length)+1
     omega
   simp only [hround, auxiliaryStudent]
   split
   · rw [assembled_correct M O p W r hW]
     cases hb : blockInput r x with
     | none => simp [hb]
     | some X =>
       simp [hb, blocks, parts_tup, auxiliaryCandidate, pool, replies_encoded]
   · rfl

end StudentTeacher976.Adaptivity.AuxiliaryStudentData
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.OracleTag
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 def query (w : Word) : Word := (frames (w.drop 3)).headD []
 def state (w : Word) : Word := (frames (w.drop 3)).tail.headD []
 def mapRecord (f : Word → Word) (w : Word) : Word := w.take 3 ++ frame (f (query w)) ++ frame (state w)
 theorem map_record (f : Word → Word) (done answer : Bool) (q s : Word) :
     mapRecord f (OracleDriver.record done answer q s) = OracleDriver.record done answer (f q) s := by
   simp [mapRecord,query,state,OracleDriver.record,NativeCPU.frames_two]
 theorem map_final (f : Word → Word) (answer : Bool) (q s : Word) :
     mapRecord f (OracleDriver.finalRecord answer q s) = OracleDriver.finalRecord answer (f q) s := by
   simp [mapRecord,query,state,OracleDriver.finalRecord,NativeCPU.frames_two]

 def untag (w : Word) : Word :=
   if w.headD false || (w.drop 1).headD false then mapRecord List.tail w else w
 def cpu (tag : Bool) (C : Word → Word) (w : Word) : Word :=
   if !(w.headD false) && (w.drop 1).headD false then C (untag w)
   else mapRecord (tag :: ·) (C (untag w))

 theorem cpu_initial (tag : Bool) (C : Word → Word) (x : Word) :
     cpu tag C (OracleDriver.shifted x) = mapRecord (tag :: ·) (C (OracleDriver.shifted x)) := by
   simp [cpu,untag,OracleDriver.shifted]
 theorem cpu_continue (tag : Bool) (C : Word → Word) (done answer : Bool) (q s : Word) :
     cpu tag C (OracleDriver.record done answer (tag::q) s) =
       mapRecord (tag :: ·) (C (OracleDriver.record done answer q s)) := by
   have h0 : (OracleDriver.record done answer (tag::q) s).headD false = true := rfl
   have h1 : ((OracleDriver.record done answer (tag::q) s).drop 1).headD false = done := rfl
   simp only [cpu,untag,h0,h1,Bool.not_true,Bool.false_and,Bool.true_or,Bool.false_eq_true,↓reduceIte]
   rw [map_record]
   rfl

 theorem cpu_final (tag : Bool) (C : Word → Word) (answer : Bool) (q s : Word) :
     cpu tag C (OracleDriver.finalRecord answer (tag::q) s) = C (OracleDriver.finalRecord answer q s) := by
   have h0 : (OracleDriver.finalRecord answer (tag::q) s).headD false = false := rfl
   have h1 : ((OracleDriver.finalRecord answer (tag::q) s).drop 1).headD false = true := rfl
   simp only [cpu,untag,h0,h1,Bool.not_false,Bool.true_and,Bool.false_or,Bool.true_eq,↓reduceIte]
   rw [map_final]
   rfl

 theorem mapRecord_poly (f : Word → Word) (hf : ComputableTidilyInPolyTime f encBits encBits) :
     ComputableTidilyInPolyTime (mapRecord f) encBits encBits := by
   have hfr := computableInDegree_frames.computableInPolyTime.tidy
   have hframe := NativeCPU.frame_poly
   unfold mapRecord query state
   fun_prop
 theorem cpu_poly (tag : Bool) (C : Word → Word) (hC : ComputableTidilyInPolyTime C encBits encBits) :
     ComputableTidilyInPolyTime (cpu tag C) encBits encBits := by
   have hm := mapRecord_poly List.tail (by fun_prop)
   have ht := mapRecord_poly (tag :: ·) (by fun_prop)
   have hu : ComputableTidilyInPolyTime untag encBits encBits := by unfold untag; fun_prop
   unfold cpu
   fun_prop

 theorem record_size (tag : Bool) (done answer : Bool) (q s : Word) :
     (OracleDriver.record done answer (tag::q) s).length = (OracleDriver.record done answer q s).length+2 := by
   simp [OracleDriver.record,length_frame]

 theorem trace (tag : Bool) (C : Word → Word) (O J : Oracle) (hJ : ∀ q, J (tag::q) = O q)
     (B : ℕ) (input out : Word) (steps : ℕ) (ht : OracleDriver.Trace C O B input out steps) :
     ∀ input' : Word, input'.length ≤ B+2 → cpu tag C input' = mapRecord (tag :: ·) (C input) →
       OracleDriver.Trace (cpu tag C) J (B+2) input' out steps := by
   induction ht with
   | done input answer q s out hinput hsize hcpu hfinal =>
     intro input' hinput' hc
     rw [hcpu,map_record] at hc
     exact OracleDriver.Trace.done input' answer (tag::q) s out hinput'
       (by rw [record_size]; omega) hc (by rw [cpu_final,hfinal])
   | query input answer q s out steps hinput hsize hcpu next ih =>
     intro input' hinput' hc
     rw [hcpu,map_record] at hc
     apply OracleDriver.Trace.query input' answer (tag::q) s out steps hinput'
       (by rw [record_size]; omega) hc
     rw [hJ]
     apply ih (OracleDriver.record false (O q) (tag::q) s)
     · have hn : (OracleDriver.record false (O q) q s).length ≤ B := by cases next <;> assumption
       rw [record_size]
       omega
     · exact cpu_continue tag C false (O q) q s

 theorem protocol (tag : Bool) (C : Word → Word) (O J : Oracle) (hJ : ∀ q, J (tag::q) = O q)
     (f : Word → Word) (T B : Polynomial ℕ)
     (ht : ∀ x : Word, ∃ steps ≤ T.eval x.length,
       OracleDriver.Trace C O (B.eval x.length) (OracleDriver.shifted x) (f x) steps) :
     ∀ x : Word, ∃ steps ≤ T.eval x.length,
       OracleDriver.Trace (cpu tag C) J ((B+2).eval x.length) (OracleDriver.shifted x) (f x) steps := by
   intro x
   obtain ⟨steps,hsteps,htrace⟩ := ht x
   refine ⟨steps,hsteps,?_⟩
   have hi : (OracleDriver.shifted x).length ≤ B.eval x.length := by cases htrace <;> assumption
   simpa only [Polynomial.eval_add,Polynomial.eval_ofNat] using
     trace tag C O J hJ (B.eval x.length) _ _ _ htrace _ (by omega) (cpu_initial tag C x)

end StudentTeacher976.Adaptivity.OracleTag
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.ProtocolCompose
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl
open OracleTag (query state)

 theorem query_record (done answer : Bool) (q s : Word) : query (OracleDriver.record done answer q s) = q := by
   simp only [query,OracleDriver.record,List.drop_succ_cons,List.drop_zero,NativeCPU.frames_two,List.headD_cons]
 theorem state_record (done answer : Bool) (q s : Word) : state (OracleDriver.record done answer q s) = s := by
   simp only [state,OracleDriver.record,List.drop_succ_cons,List.drop_zero,NativeCPU.frames_two,List.tail_cons,List.headD_cons]
 theorem query_final (answer : Bool) (q s : Word) : query (OracleDriver.finalRecord answer q s) = q := by
   simp only [query,OracleDriver.finalRecord,List.drop_succ_cons,List.drop_zero,NativeCPU.frames_two,List.headD_cons]
 theorem state_final (answer : Bool) (q s : Word) : state (OracleDriver.finalRecord answer q s) = s := by
   simp only [state,OracleDriver.finalRecord,List.drop_succ_cons,List.drop_zero,NativeCPU.frames_two,List.tail_cons,List.headD_cons]
 def wrap (phase : Bool) (w : Word) : Word := w.take 3 ++ frame (query w) ++ frame (phase :: state w)
 theorem wrap_record (phase done answer : Bool) (q s : Word) :
     wrap phase (OracleDriver.record done answer q s) = OracleDriver.record done answer q (phase::s) := by
   simp [wrap,query,state,OracleDriver.record,NativeCPU.frames_two]
 def finalRequest (w : Word) : Word := OracleDriver.finalRecord (w.getD 2 false) (query w) (state w)
 theorem finalRequest_record (done answer : Bool) (q s : Word) :
     finalRequest (OracleDriver.record done answer q s) = OracleDriver.finalRecord answer q s := by
   simp [finalRequest,query,state,OracleDriver.record,NativeCPU.frames_two]
 def finishFirst (C D : Word → Word) (response : Word) : Word :=
   if response.getD 1 false then wrap false (D (OracleDriver.shifted (C (finalRequest response))))
   else wrap true response
 def cpu (C D : Word → Word) (w : Word) : Word :=
   if w.headD false then
     if (state w).headD false then
       finishFirst C D (C (OracleDriver.record false (w.getD 2 false) (query w) (state w).tail))
     else wrap false (D (OracleDriver.record false (w.getD 2 false) (query w) (state w).tail))
   else if (w.drop 1).headD false then D (OracleDriver.finalRecord (w.getD 2 false) (query w) (state w).tail)
   else finishFirst C D (C w)

 theorem finish_done (C D : Word → Word) (answer : Bool) (q s : Word) :
     finishFirst C D (OracleDriver.record true answer q s) =
       wrap false (D (OracleDriver.shifted (C (OracleDriver.finalRecord answer q s)))) := by
   have h : (OracleDriver.record true answer q s).getD 1 false = true := rfl
   simp only [finishFirst,h,Bool.true_eq,↓reduceIte,finalRequest_record]
 theorem finish_query (C D : Word → Word) (answer : Bool) (q s : Word) :
     finishFirst C D (OracleDriver.record false answer q s) = wrap true (OracleDriver.record false answer q s) := by
   simp [finishFirst,OracleDriver.record]
 theorem cpu_initial (C D : Word → Word) (x : Word) :
     cpu C D (OracleDriver.shifted x) = finishFirst C D (C (OracleDriver.shifted x)) := by
   simp [cpu,OracleDriver.shifted]
 theorem cpu_continue_first (C D : Word → Word) (answer : Bool) (q s : Word) :
     cpu C D (OracleDriver.record false answer q (true::s)) = finishFirst C D (C (OracleDriver.record false answer q s)) := by
   have h0 : (OracleDriver.record false answer q (true::s)).headD false = true := rfl
   have h2 : (OracleDriver.record false answer q (true::s)).getD 2 false = answer := rfl
   simp only [cpu,h0,h2,query_record,state_record,List.headD_cons,List.tail_cons,
     Bool.true_eq,Bool.false_eq_true,↓reduceIte]
 theorem cpu_continue_second (C D : Word → Word) (answer : Bool) (q s : Word) :
     cpu C D (OracleDriver.record false answer q (false::s)) = wrap false (D (OracleDriver.record false answer q s)) := by
   have h0 : (OracleDriver.record false answer q (false::s)).headD false = true := rfl
   have h2 : (OracleDriver.record false answer q (false::s)).getD 2 false = answer := rfl
   simp only [cpu,h0,h2,query_record,state_record,List.headD_cons,List.tail_cons,
     Bool.true_eq,Bool.false_eq_true,↓reduceIte]
 theorem cpu_final (C D : Word → Word) (answer : Bool) (q s : Word) :
     cpu C D (OracleDriver.finalRecord answer q (false::s)) = D (OracleDriver.finalRecord answer q s) := by
   have h0 : (OracleDriver.finalRecord answer q (false::s)).headD false = false := rfl
   have h1 : ((OracleDriver.finalRecord answer q (false::s)).drop 1).headD false = true := rfl
   have h2 : (OracleDriver.finalRecord answer q (false::s)).getD 2 false = answer := rfl
   simp only [cpu,h0,h1,h2,query_final,state_final,List.tail_cons,
     Bool.true_eq,Bool.false_eq_true,↓reduceIte]
 theorem wrap_size (phase done answer : Bool) (q s : Word) :
     (OracleDriver.record done answer q (phase::s)).length = (OracleDriver.record done answer q s).length+2 := by
   simp [OracleDriver.record,length_frame]
   omega

 theorem wrap_poly (phase : Bool) : ComputableTidilyInPolyTime (wrap phase) encBits encBits := by
   have hfr := computableInDegree_frames.computableInPolyTime.tidy
   have hf := NativeCPU.frame_poly
   unfold wrap query state
   fun_prop
 theorem finalRequest_poly : ComputableTidilyInPolyTime finalRequest encBits encBits := by
   have hfr := computableInDegree_frames.computableInPolyTime.tidy
   have hf := NativeCPU.frame_poly
   unfold finalRequest query state OracleDriver.finalRecord
   fun_prop
 theorem finishFirst_poly (C D : Word → Word)
     (hC : ComputableTidilyInPolyTime C encBits encBits) (hD : ComputableTidilyInPolyTime D encBits encBits) :
     ComputableTidilyInPolyTime (finishFirst C D) encBits encBits := by
   have hw0 := wrap_poly false
   have hw1 := wrap_poly true
   have hf := finalRequest_poly
   unfold finishFirst OracleDriver.shifted
   fun_prop
 theorem cpu_poly (C D : Word → Word)
     (hC : ComputableTidilyInPolyTime C encBits encBits) (hD : ComputableTidilyInPolyTime D encBits encBits) :
     ComputableTidilyInPolyTime (cpu C D) encBits encBits := by
   have hfinish := finishFirst_poly C D hC hD
   have hw := wrap_poly false
   have hr := NativeCPU.record_poly
   have hfr := computableInDegree_frames.computableInPolyTime.tidy
   have hq : ComputableTidilyInPolyTime query encBits encBits := by unfold query; fun_prop
   have hs : ComputableTidilyInPolyTime state encBits encBits := by unfold state; fun_prop
   have hf : ComputableTidilyInPolyTime (fun w : Word => OracleDriver.finalRecord (w.getD 2 false) (query w) (state w).tail)
       encBits encBits := by
     have hframe := NativeCPU.frame_poly
     unfold OracleDriver.finalRecord
     fun_prop
   unfold cpu
   fun_prop

 theorem second_trace (C D : Word → Word) (O : Oracle) (B K : ℕ) (hBK : B+2 ≤ K)
     (input out : Word) (steps : ℕ) (ht : OracleDriver.Trace D O B input out steps) :
     ∀ input' : Word, input'.length ≤ K → cpu C D input' = wrap false (D input) →
       OracleDriver.Trace (cpu C D) O K input' out steps := by
   induction ht with
   | done input answer q s out hinput hsize hcpu hfinal =>
     intro input' hi hc
     rw [hcpu,wrap_record] at hc
     exact OracleDriver.Trace.done input' answer q (false::s) out hi
       (by rw [wrap_size]; omega) hc (by rw [cpu_final,hfinal])
   | query input answer q s out steps hinput hsize hcpu next ih =>
     intro input' hi hc
     rw [hcpu,wrap_record] at hc
     apply OracleDriver.Trace.query input' answer q (false::s) out steps hi (by rw [wrap_size]; omega) hc
     apply ih (OracleDriver.record false (O q) q (false::s))
     · have hn : (OracleDriver.record false (O q) q s).length ≤ B := by cases next <;> assumption
       rw [wrap_size]
       omega
     · exact cpu_continue_second C D (O q) q s

 theorem first_trace (C D : Word → Word) (O : Oracle) (B1 B2 K : ℕ)
     (hB1 : B1+2 ≤ K) (hB2 : B2+2 ≤ K) (input middle out : Word) (steps1 steps2 : ℕ)
     (ht1 : OracleDriver.Trace C O B1 input middle steps1)
     (ht2 : OracleDriver.Trace D O B2 (OracleDriver.shifted middle) out steps2) :
     ∀ input' : Word, input'.length ≤ K → cpu C D input' = finishFirst C D (C input) →
       OracleDriver.Trace (cpu C D) O K input' out (steps1+steps2) := by
   induction ht1 with
   | done input answer q s middle hinput hsize hcpu hfinal =>
     intro input' hi hc
     rw [hcpu,finish_done,hfinal] at hc
     simpa only [Nat.zero_add] using second_trace C D O B2 K hB2 _ _ _ ht2 input' hi hc
   | query input answer q s middle steps1 hinput hsize hcpu next ih =>
     intro input' hi hc
     rw [hcpu,finish_query,wrap_record] at hc
     have hn : (OracleDriver.record false (O q) q s).length ≤ B1 := by cases next <;> assumption
     have hnext := ih ht2 (OracleDriver.record false (O q) q (true::s))
       (by rw [wrap_size]; omega) (cpu_continue_first C D (O q) q s)
     have hnode := OracleDriver.Trace.query input' answer q (true::s) out (steps1+steps2) hi
       (by rw [wrap_size]; omega) hc hnext
     convert hnode using 1 <;> omega

 theorem output_bound (C : Word → Word) (O : Oracle) (p : Polynomial ℕ)
     (hC : ∀ w : Word, (C w).length ≤ p.eval w.length)
     (B : ℕ) (input out : Word) (steps : ℕ) (ht : OracleDriver.Trace C O B input out steps) :
     out.length ≤ p.eval B := by
   induction ht with
   | done input answer q s out hinput hsize hcpu hfinal =>
     rw [← hfinal]
     apply (hC _).trans (NativeBatch.polyEvalMono p ?_)
     simpa only [OracleDriver.finalRecord,OracleDriver.record,List.length_cons] using hsize
   | query input answer q s out steps hinput hsize hcpu next ih => exact ih

 theorem protocol (C D : Word → Word) (hC : ComputableTidilyInPolyTime C encBits encBits)
     (hD : ComputableTidilyInPolyTime D encBits encBits) (O : Oracle) (f g : Word → Word)
     (T1 B1 T2 B2 : Polynomial ℕ)
     (ht1 : ∀ x : Word, ∃ steps ≤ T1.eval x.length,
       OracleDriver.Trace C O (B1.eval x.length) (OracleDriver.shifted x) (f x) steps)
     (ht2 : ∀ y : Word, ∃ steps ≤ T2.eval y.length,
       OracleDriver.Trace D O (B2.eval y.length) (OracleDriver.shifted y) (g y) steps) :
     ∃ T B : Polynomial ℕ, ∀ x : Word, ∃ steps ≤ T.eval x.length,
       OracleDriver.Trace (cpu C D) O (B.eval x.length) (OracleDriver.shifted x) (g (f x)) steps := by
   obtain ⟨p,hp⟩ := hC.polyBounded_length.exists_polynomial
   let F := p.comp B1
   let T := T1+T2.comp F
   let B := B1+B2.comp F+2
   refine ⟨T,B,?_⟩
   intro x
   obtain ⟨s1,hs1,htrace1⟩ := ht1 x
   obtain ⟨s2,hs2,htrace2⟩ := ht2 (f x)
   have hf : (f x).length ≤ F.eval x.length := by
     simpa only [F,Polynomial.eval_comp,encBits_apply] using output_bound C O p hp _ _ _ _ htrace1
   have ht2' := hs2.trans (NativeBatch.polyEvalMono T2 hf)
   have hb2 := NativeBatch.polyEvalMono B2 hf
   have hinput : (OracleDriver.shifted x).length ≤ B1.eval x.length := by cases htrace1 <;> assumption
   have ht := first_trace C D O (B1.eval x.length) (B2.eval (f x).length) (B.eval x.length)
     (by simp [B] <;> omega) (by simp [B] <;> omega) _ _ _ s1 s2 htrace1 htrace2 (OracleDriver.shifted x)
     (by simp [B] <;> omega) (cpu_initial C D x)
   refine ⟨s1+s2,?_,ht⟩
   simpa only [T,Polynomial.eval_add,Polynomial.eval_comp] using Nat.add_le_add hs1 ht2'

end StudentTeacher976.Adaptivity.ProtocolCompose
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.ProtocolContext
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl
open OracleTag (query state)
open ProtocolCompose (query_record state_record query_final state_final)

 def packed (ctx s : Word) : Word := frame ctx ++ frame s
 def context (s : Word) : Word := (frames s).headD []
 def previous (s : Word) : Word := (frames s).tail.headD []
 theorem context_packed (ctx s : Word) : context (packed ctx s) = ctx := by simp [context,packed,NativeCPU.frames_two]
 theorem previous_packed (ctx s : Word) : previous (packed ctx s) = s := by simp [previous,packed,NativeCPU.frames_two]
 def wrap (ctx w : Word) : Word := w.take 3 ++ frame (query w) ++ frame (packed ctx (state w))
 theorem wrap_record (ctx : Word) (done answer : Bool) (q s : Word) :
     wrap ctx (OracleDriver.record done answer q s) = OracleDriver.record done answer q (packed ctx s) := by
   simp only [wrap,query_record,state_record]
   rfl
 def cpu (C : Word → Word) (w : Word) : Word :=
   if w.headD false then wrap (context (state w))
     (C (OracleDriver.record false (w.getD 2 false) (query w) (previous (state w))))
   else if (w.drop 1).headD false then
     tup [context (state w),C (OracleDriver.finalRecord (w.getD 2 false) (query w) (previous (state w)))]
   else wrap (w.drop 2) (C w)
 theorem cpu_initial (C : Word → Word) (x : Word) :
     cpu C (OracleDriver.shifted x) = wrap x (C (OracleDriver.shifted x)) := by simp [cpu,OracleDriver.shifted]
 theorem cpu_continue (C : Word → Word) (ctx : Word) (answer : Bool) (q s : Word) :
     cpu C (OracleDriver.record false answer q (packed ctx s)) =
       wrap ctx (C (OracleDriver.record false answer q s)) := by
   have h0 : (OracleDriver.record false answer q (packed ctx s)).headD false = true := rfl
   have h2 : (OracleDriver.record false answer q (packed ctx s)).getD 2 false = answer := rfl
   simp only [cpu,h0,h2,Bool.true_eq,↓reduceIte,query_record,state_record,context_packed,previous_packed]
 theorem cpu_final (C : Word → Word) (ctx : Word) (answer : Bool) (q s : Word) :
     cpu C (OracleDriver.finalRecord answer q (packed ctx s)) = tup [ctx,C (OracleDriver.finalRecord answer q s)] := by
   have h0 : (OracleDriver.finalRecord answer q (packed ctx s)).headD false = false := rfl
   have h1 : ((OracleDriver.finalRecord answer q (packed ctx s)).drop 1).headD false = true := rfl
   have h2 : (OracleDriver.finalRecord answer q (packed ctx s)).getD 2 false = answer := rfl
   simp only [cpu,h0,h1,h2,Bool.false_eq_true,Bool.true_eq,↓reduceIte,query_final,state_final,context_packed,previous_packed]
 theorem size_bound (ctx : Word) (done answer : Bool) (q s : Word) :
     (OracleDriver.record done answer q (packed ctx s)).length ≤
       2*(OracleDriver.record done answer q s).length+4*ctx.length+10 := by
   simp [OracleDriver.record,packed,length_frame]
   omega

 theorem wrap_poly : ComputableTidilyInPolyTime (fun p : Word × Word => wrap p.1 p.2) (encPair encBits encBits) encBits := by
   have hfr := computableInDegree_frames.computableInPolyTime.tidy
   have hf := NativeCPU.frame_poly
   unfold wrap query state packed
   fun_prop
 theorem context_poly : ComputableTidilyInPolyTime context encBits encBits := by
   have hfr := computableInDegree_frames.computableInPolyTime.tidy
   unfold context
   fun_prop
 theorem previous_poly : ComputableTidilyInPolyTime previous encBits encBits := by
   have hfr := computableInDegree_frames.computableInPolyTime.tidy
   unfold previous
   fun_prop
 theorem cpu_poly (C : Word → Word) (hC : ComputableTidilyInPolyTime C encBits encBits) :
     ComputableTidilyInPolyTime (cpu C) encBits encBits := by
   have hw := wrap_poly
   have hc := context_poly
   have hp := previous_poly
   have hq : ComputableTidilyInPolyTime query encBits encBits := by
     have hfr := computableInDegree_frames.computableInPolyTime.tidy
     unfold query
     fun_prop
   have hs : ComputableTidilyInPolyTime state encBits encBits := by
     have hfr := computableInDegree_frames.computableInPolyTime.tidy
     unfold state
     fun_prop
   have hr := NativeCPU.record_poly
   have hf : ComputableTidilyInPolyTime (fun w : Word =>
       OracleDriver.finalRecord (w.getD 2 false) (query w) (previous (state w))) encBits encBits := by
     have hframe := NativeCPU.frame_poly
     unfold OracleDriver.finalRecord
     fun_prop
   have ht := TupleCodec.encode_poly
   unfold cpu
   apply ComputableTidilyInPolyTime.cond
   · fun_prop
   · apply hw.comp (g := fun w : Word => (context (state w),C (OracleDriver.record false (w.getD 2 false) (query w) (previous (state w)))))
     fun_prop
   · apply ComputableTidilyInPolyTime.cond
     · fun_prop
     · apply ht.comp
       fun_prop
     · apply hw.comp (g := fun w : Word => (w.drop 2,C w))
       fun_prop

 theorem trace (C : Word → Word) (O : Oracle) (ctx : Word) (B K : ℕ) (hBK : 2*B+4*ctx.length+10 ≤ K)
     (input out : Word) (steps : ℕ) (ht : OracleDriver.Trace C O B input out steps) :
     ∀ input' : Word, input'.length ≤ K → cpu C input' = wrap ctx (C input) →
       OracleDriver.Trace (cpu C) O K input' (tup [ctx,out]) steps := by
   induction ht with
   | done input answer q s out hinput hsize hcpu hfinal =>
     intro input' hi hc
     rw [hcpu,wrap_record] at hc
     exact OracleDriver.Trace.done input' answer q (packed ctx s) (tup [ctx,out]) hi
       ((size_bound ctx true answer q s).trans (by omega)) hc (by rw [cpu_final,hfinal])
   | query input answer q s out steps hinput hsize hcpu next ih =>
     intro input' hi hc
     rw [hcpu,wrap_record] at hc
     apply OracleDriver.Trace.query input' answer q (packed ctx s) (tup [ctx,out]) steps hi
       ((size_bound ctx false answer q s).trans (by omega)) hc
     apply ih (OracleDriver.record false (O q) q (packed ctx s))
     · have hn : (OracleDriver.record false (O q) q s).length ≤ B := by cases next <;> assumption
       exact (size_bound ctx false (O q) q s).trans (by omega)
     · exact cpu_continue C ctx (O q) q s

 theorem protocol (C : Word → Word) (O : Oracle) (f : Word → Word) (T B : Polynomial ℕ)
     (ht : ∀ x : Word, ∃ steps ≤ T.eval x.length,
       OracleDriver.Trace C O (B.eval x.length) (OracleDriver.shifted x) (f x) steps) :
     ∀ x : Word, ∃ steps ≤ T.eval x.length,
       OracleDriver.Trace (cpu C) O ((2*B+4*Polynomial.X+10).eval x.length)
         (OracleDriver.shifted x) (tup [x,f x]) steps := by
   intro x
   obtain ⟨steps,hsteps,htrace⟩ := ht x
   have hi : (OracleDriver.shifted x).length ≤ B.eval x.length := by cases htrace <;> assumption
   refine ⟨steps,hsteps,?_⟩
   apply trace C O x (B.eval x.length) _ (by simp) _ _ _ htrace _
   · simp
     omega
   · exact cpu_initial C x

end StudentTeacher976.Adaptivity.ProtocolContext
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.OracleTag
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 theorem native (tag : Bool) (M : OTM) (p : Polynomial ℕ) (decision : Bool)
     (O J : Oracle) (hJ : ∀ q, J (tag::q) = O q) :
     ∃ (M' : OTM) (p' : Polynomial ℕ), ∀ x : Word,
       M'.result J x (p'.eval x.length) = some ((NativeCPU.nativeOutput M O x (p.eval x.length) decision).headD false) ∧
       M'.output J x (p'.eval x.length) = NativeCPU.nativeOutput M O x (p.eval x.length) decision := by
   obtain ⟨C,hC,B,htrace⟩ := NativeCPU.native_protocol M p decision
   have ht : ∀ x : Word, ∃ steps ≤ p.eval x.length,
       OracleDriver.Trace C O (B.eval x.length) (OracleDriver.shifted x)
         (NativeCPU.nativeOutput M O x (p.eval x.length) decision) steps :=
     fun x => ⟨_,le_rfl,htrace O x⟩
   have htag := protocol tag C O J hJ _ p B ht
   obtain ⟨M',hM'⟩ := oracle_protocol_machine (cpu tag C) (ComputableInPolyTime.of_tidy (cpu_poly tag C hC.tidy))
   obtain ⟨p',hp'⟩ := hM' J _ p (B+2) htag
   exact ⟨M',p',by simpa only [List.headD_eq_head?_getD] using hp'⟩

end StudentTeacher976.Adaptivity.OracleTag
end

section
set_option autoImplicit false
open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity

private def haltMachine (b : Bool) : OTM where
  k := 0
  g := 0
  δ := fun _ a c => (if b then 1 else 2, a, 1, c, 1)

private theorem haltMachine_result (b : Bool) (O : Oracle) (x : Word) :
    (haltMachine b).result O x 1 = some b := by
  cases b <;> rfl

private theorem altLen_const (lengths : List ℕ) (start : Bool) (P : Prop) :
    AvgPHETH.AltLen lengths start (fun _ => P) ↔ P := by
  induction lengths generalizing start with
  | nil => rfl
  | cons n ns ih =>
    cases start with
    | false =>
      simp only [AvgPHETH.AltLen, ih]
      constructor
      · intro h; exact h (List.replicate n false) (by simp)
      · exact fun h _ _ => h
    | true =>
      simp only [AvgPHETH.AltLen, ih]
      constructor
      · rintro ⟨w, hw, h⟩; exact h
      · intro h; exact ⟨List.replicate n false, by simp, h⟩

 theorem empty_mem_sigma (i : ℕ) : (∅ : Language) ∈ Sigma i := by
  refine ⟨haltMachine false, 1, List.replicate i 0, by simp, ?_, ?_⟩
  · intro s
    simpa using congrArg Option.isSome (haltMachine_result false (fun _ => false) s)
  · intro x
    simp only [Set.mem_empty_iff_false]
    have hres : ∀ ys : List Word,
        (haltMachine false).result (fun _ => false) (tup (x :: ys))
          ((1 : Polynomial ℕ).eval (tup (x :: ys)).length) = some true ↔ False := by
      intro ys
      simp [haltMachine_result]
    simp only [hres]
    exact (altLen_const _ true False).symm

 theorem univ_mem_sigma (i : ℕ) : (Set.univ : Language) ∈ Sigma i := by
  refine ⟨haltMachine true, 1, List.replicate i 0, by simp, ?_, ?_⟩
  · intro s
    simpa using congrArg Option.isSome (haltMachine_result true (fun _ => false) s)
  · intro x
    simp only [Set.mem_univ]
    have hres : ∀ ys : List Word,
        (haltMachine true).result (fun _ => false) (tup (x :: ys))
          ((1 : Polynomial ℕ).eval (tup (x :: ys)).length) = some true ↔ True := by
      intro ys
      simp [haltMachine_result]
    simp only [hres]
    exact (altLen_const _ true True).symm

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

private theorem haltMachine_output (b : Bool) (O : Oracle) (x : Word) :
    (haltMachine b).output O x 1 = x := by
  change OTM.readBits (Function.update ((haltMachine b).init x).work 0
      (((haltMachine b).init x).work 0)) (max (x.length : ℤ) 0) = x
  rw [Function.update_eq_self, max_eq_left (by omega)]
  exact init_readBits (haltMachine b) x

 theorem inFP_id (i : ℕ) : InFP i (fun x => x) := by
  refine ⟨fun _ => false, haltMachine true, 1, ?_, ?_⟩
  · simpa using empty_mem_sigma i
  · intro x
    constructor
    · simpa using congrArg Option.isSome (haltMachine_result true (fun _ => false) x)
    · simpa using haltMachine_output true (fun _ => false) x

end StudentTeacher976.Adaptivity
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity
open QAdvFew.PoQOracle Turing.MultiTapeTM

 theorem native_boolean_pure (M : OTM) (p : Polynomial ℕ) :
     ComputableTidilyInPolyTime (fun x : Word => (M.result (fun _ => false) x (p.eval x.length)).getD false) encBits encBool := by
   have h := NativeCPU.native_pure M (fun _ => false) p true (ComputableTidilyInPolyTime.const false)
   have hh := (ComputableTidilyInPolyTime.headD (encA := encBool) (encL := encBits) false).comp h
   simpa only [Function.comp_def, NativeCPU.nativeOutput, Bool.true_eq, ↓reduceIte, List.headD_cons] using hh

 theorem pure_word_machine (f : Word → Word) (hf : ComputableTidilyInPolyTime f encBits encBits) (O : Oracle) :
     ∃ (M : OTM) (p : Polynomial ℕ), ∀ x : Word,
       M.result O x (p.eval x.length) = some ((f x).headD false) ∧ M.output O x (p.eval x.length) = f x := by
   let dummy : OTM := ⟨0,0,fun _ a b => (1,a,1,b,1)⟩
   obtain ⟨C,hC,T,B,htrace⟩ := NativeBatch.protocol dummy 1 (by intro w; simp)
     (fun _ => []) (fun a : Word × Word => f a.1)
     (ComputableTidilyInPolyTime.const []) (hf.comp (ComputableTidilyInPolyTime.fst encBits encBits))
   obtain ⟨M,hM⟩ := oracle_protocol_machine C hC
   obtain ⟨p,hp⟩ := hM O f T B (by simpa using htrace O)
   exact ⟨M,p,by simpa only [List.headD_eq_head?_getD] using hp⟩

 theorem pure_inFP (i : ℕ) (f : Word → Word) (hf : ComputableTidilyInPolyTime f encBits encBits) : InFP i f := by
   obtain ⟨M,p,hM⟩ := pure_word_machine f hf (fun _ => false)
   refine ⟨fun _ => false,M,p,by simpa using empty_mem_sigma i,?_⟩
   intro x
   exact ⟨by rw [(hM x).1]; rfl,(hM x).2⟩

end StudentTeacher976.Adaptivity
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.SigmaClosure
open QAdvFew.PoQOracle Turing.MultiTapeTM
theorem extend_word (n m : ℕ) (hnm : n ≤ m) (u : Word) (hu : u.length = n) :
    ∃ w : Word, w.length = m ∧ w.take n = u := by
  refine ⟨u ++ List.replicate (m - n) false, ?_, ?_⟩
  · simp [hu]; omega
  · rw [← hu, List.take_left]

 theorem altLen_trim {short long : List ℕ} (hrel : List.Forall₂ (· ≤ ·) short long)
    (start : Bool) (P : List Word → Prop) :
    AvgPHETH.AltLen long start
        (fun ys => P (List.zipWith (fun n w => w.take n) short ys)) ↔
      AvgPHETH.AltLen short start P := by
  induction hrel generalizing start P with
  | nil => rfl
  | @cons n m ns ms hnm htail ih =>
    cases start with
    | true =>
      change (∃ w : Word, w.length = m ∧ AvgPHETH.AltLen ms false
        (fun ys => P (w.take n :: List.zipWith (fun n w => w.take n) ns ys))) ↔
        ∃ u : Word, u.length = n ∧ AvgPHETH.AltLen ns false (fun ys => P (u :: ys))
      constructor
      · rintro ⟨w, hw, hrec⟩
        refine ⟨w.take n, by simp [hw, Nat.min_eq_left hnm], ?_⟩
        exact (ih false (fun ys => P (w.take n :: ys))).mp hrec
      · rintro ⟨u, hu, hrec⟩
        obtain ⟨w, hw, ht⟩ := extend_word n m hnm u hu
        refine ⟨w, hw, ?_⟩
        rw [ht]
        exact (ih false (fun ys => P (u :: ys))).mpr hrec
    | false =>
      change (∀ w : Word, w.length = m → AvgPHETH.AltLen ms true
        (fun ys => P (w.take n :: List.zipWith (fun n w => w.take n) ns ys))) ↔
        ∀ u : Word, u.length = n → AvgPHETH.AltLen ns true (fun ys => P (u :: ys))
      constructor
      · intro h u hu
        obtain ⟨w, hw, ht⟩ := extend_word n m hnm u hu
        have hrec := h w hw
        rw [ht] at hrec
        exact (ih true (fun ys => P (u :: ys))).mp hrec
      · intro h w hw
        have hrec := h (w.take n) (by simp [hw, Nat.min_eq_left hnm])
        exact (ih true (fun ys => P (w.take n :: ys))).mpr hrec


 def outer (w : Word) : Word := (TupleCodec.decodeTuple w).headD []
 def rest (w : Word) : List Word := (TupleCodec.decodeTuple w).tail
 def inner (w : Word) : Word := (outer w).tail
 def trimmed (ps : List (Polynomial ℕ)) (w : Word) : List Word :=
   List.zipWith (fun n s => s.take n) (ps.map fun p => p.eval (inner w).length) (rest w)
 def argument (ps : List (Polynomial ℕ)) (w : Word) : Word := tup (inner w :: trimmed ps w)

 theorem outer_poly : ComputableTidilyInPolyTime outer encBits encBits :=
   (ComputableTidilyInPolyTime.headD []).comp TupleCodec.decoder_poly.tidy
 theorem rest_poly : ComputableTidilyInPolyTime rest encBits (encList encBits) :=
   (ComputableTidilyInPolyTime.tail (encA := encBits)).comp TupleCodec.decoder_poly.tidy
 theorem inner_poly : ComputableTidilyInPolyTime inner encBits encBits := by
   exact (ComputableTidilyInPolyTime.tail (encA := encBool)).comp outer_poly
 theorem bounds_poly (ps : List (Polynomial ℕ)) :
     ComputableTidilyInPolyTime (fun w => ps.map fun p => p.eval (inner w).length) encBits (encList encUnary) := by
   apply ComputableTidilyInPolyTime.mapConst
   intro p hp
   exact (ComputableTidilyInPolyTime.unary_eval p).comp (ComputableTidilyInPolyTime.length_bits.comp inner_poly)
 theorem trimmed_poly (ps : List (Polynomial ℕ)) :
     ComputableTidilyInPolyTime (trimmed ps) encBits (encList encBits) := by
   have hz := (ComputableTidilyInPolyTime.zip encUnary encBits).comp ((bounds_poly ps).prod rest_poly)
   have ht : ComputableTidilyInPolyTime (fun p : ℕ × Word => p.2.take p.1)
       (encPair encUnary encBits) encBits := by fun_prop
   have hh := (ComputableTidilyInPolyTime.map ht).comp hz
   change ComputableTidilyInPolyTime (fun w => List.zipWith (fun n s => s.take n)
     (ps.map fun p => p.eval (inner w).length) (rest w)) encBits (encList encBits)
   simp only [Function.comp_def,List.map_zip_eq_zipWith] at hh
   have he : Function.curry (fun p : ℕ × Word => p.2.take p.1) = (fun n s => s.take n) := rfl
   rw [he] at hh
   exact hh
 theorem argument_poly (ps : List (Polynomial ℕ)) : ComputableTidilyInPolyTime (argument ps) encBits encBits :=
   TupleCodec.encode_poly.comp (inner_poly.cons' (trimmed_poly ps))

 def decision (V0 V1 : OTM) (p0 p1 : Polynomial ℕ) (ps0 ps1 : List (Polynomial ℕ)) (s : Word) : Word :=
   [if (outer s).headD false then (V1.result (fun _ => false) (argument ps1 s) (p1.eval (argument ps1 s).length)).getD false
     else (V0.result (fun _ => false) (argument ps0 s) (p0.eval (argument ps0 s).length)).getD false]
 theorem decision_poly (V0 V1 : OTM) (p0 p1 : Polynomial ℕ) (ps0 ps1 : List (Polynomial ℕ)) :
     ComputableTidilyInPolyTime (decision V0 V1 p0 p1 ps0 ps1) encBits encBits := by
   have h0 := (native_boolean_pure V0 p0).comp (argument_poly ps0)
   have h1 := (native_boolean_pure V1 p1).comp (argument_poly ps1)
   unfold decision
   apply ComputableTidilyInPolyTime.bitsCons
   · apply ComputableTidilyInPolyTime.cond
     · exact (ComputableTidilyInPolyTime.headD false).comp outer_poly
     · exact h1
     · exact h0
   · exact ComputableTidilyInPolyTime.const []

 noncomputable def common (ps qs : List (Polynomial ℕ)) : List (Polynomial ℕ) := List.zipWith (·+·) ps qs
 theorem first_lengths (ps qs : List (Polynomial ℕ)) (hlen : ps.length = qs.length) (a b : ℕ) (hab : a ≤ b) :
     List.Forall₂ (· ≤ ·) (ps.map fun p => p.eval a) ((common ps qs).map fun p => p.eval b) := by
   induction ps generalizing qs with
   | nil => simp [common]
   | cons p ps ih =>
     cases qs with
     | nil => simp at hlen
     | cons q qs =>
       apply List.Forall₂.cons
       · have hm := NativeBatch.polyEvalMono p hab
         simp only [common,List.zipWith_cons_cons,List.map_cons,Polynomial.eval_add]
         omega
       · exact ih qs (by simpa using hlen)
 theorem second_lengths (ps qs : List (Polynomial ℕ)) (hlen : ps.length = qs.length) (a b : ℕ) (hab : a ≤ b) :
     List.Forall₂ (· ≤ ·) (qs.map fun p => p.eval a) ((common ps qs).map fun p => p.eval b) := by
   induction ps generalizing qs with
   | nil => have hq : qs=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm); subst qs; simp [common]
   | cons p ps ih =>
     cases qs with
     | nil => simp at hlen
     | cons q qs =>
       apply List.Forall₂.cons
       · have hm := NativeBatch.polyEvalMono q hab
         simp only [common,List.zipWith_cons_cons,List.map_cons,Polynomial.eval_add]
         omega
       · exact ih qs (by simpa using hlen)

 def taggedJoin (L0 L1 : Language) : Language := {w | if w.headD false then w.tail ∈ L1 else w.tail ∈ L0}

 theorem taggedJoin_sigma (i : ℕ) (L0 L1 : Language) (h0 : L0 ∈ Sigma i) (h1 : L1 ∈ Sigma i) :
     taggedJoin L0 L1 ∈ Sigma i := by
   obtain ⟨V0,p0,ps0,hlen0,ht0,hL0⟩ := h0
   obtain ⟨V1,p1,ps1,hlen1,ht1,hL1⟩ := h1
   obtain ⟨M,p,hM⟩ := pure_word_machine (decision V0 V1 p0 p1 ps0 ps1) (decision_poly ..) (fun _ => false)
   have hlen : ps0.length=ps1.length := hlen0.trans hlen1.symm
   refine ⟨M,p,common ps0 ps1,?_,?_,?_⟩
   · simp [common,hlen0,hlen1]
   · intro s; rw [(hM s).1]; rfl
   · intro w
     have htail : w.tail.length ≤ w.length := by simp only [List.length_tail]; omega
     have hfirst := first_lengths ps0 ps1 hlen w.tail.length w.length htail
     have hsecond := second_lengths ps0 ps1 hlen w.tail.length w.length htail
     change (if w.headD false then w.tail ∈ L1 else w.tail ∈ L0) ↔ _
     simp only [(hM _).1,decision,List.headD_cons,Option.some.injEq]
     by_cases hb : w.headD false = true
     · simp only [hb,Bool.false_eq_true,↓reduceIte]
       rw [hL1]
       have ht := altLen_trim hsecond true (fun ys => V1.result (fun _ => false) (tup (w.tail::ys))
         (p1.eval (tup (w.tail::ys)).length) = some true)
       simpa only [outer,inner,rest,argument,trimmed,TupleCodec.decode_tup,List.headD_cons,List.tail_cons,hb,
         Bool.false_eq_true,↓reduceIte,getD_true_iff] using ht.symm
     · simp only [hb,Bool.false_eq_true,↓reduceIte]
       rw [hL0]
       have ht := altLen_trim hfirst true (fun ys => V0.result (fun _ => false) (tup (w.tail::ys))
         (p0.eval (tup (w.tail::ys)).length) = some true)
       simpa only [outer,inner,rest,argument,trimmed,TupleCodec.decode_tup,List.headD_cons,List.tail_cons,hb,
         Bool.false_eq_true,↓reduceIte,getD_true_iff] using ht.symm

end StudentTeacher976.Adaptivity.SigmaClosure
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.OracleComputations
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 def Computes (O : Oracle) (f : Word → Word) : Prop :=
   ∃ (M : OTM) (p : Polynomial ℕ), ∀ x : Word,
     M.result O x (p.eval x.length) = some ((f x).headD false) ∧ M.output O x (p.eval x.length) = f x

 theorem of_protocol (C : Word → Word) (hC : ComputableTidilyInPolyTime C encBits encBits)
     (O : Oracle) (f : Word → Word) (T B : Polynomial ℕ)
     (ht : ∀ x : Word, ∃ steps ≤ T.eval x.length,
       OracleDriver.Trace C O (B.eval x.length) (OracleDriver.shifted x) (f x) steps) : Computes O f := by
   obtain ⟨M,hM⟩ := oracle_protocol_machine C (ComputableInPolyTime.of_tidy hC)
   obtain ⟨p,hp⟩ := hM O f T B ht
   exact ⟨M,p,by simpa only [List.headD_eq_head?_getD] using hp⟩

 theorem to_protocol (O : Oracle) (f : Word → Word) (hf : Computes O f) :
     ∃ C : Word → Word, ComputableTidilyInPolyTime C encBits encBits ∧ ∃ T B : Polynomial ℕ,
       ∀ x : Word, ∃ steps ≤ T.eval x.length,
         OracleDriver.Trace C O (B.eval x.length) (OracleDriver.shifted x) (f x) steps := by
   obtain ⟨M,p,hM⟩ := hf
   obtain ⟨C,hC,B,htrace⟩ := NativeCPU.native_protocol M p false
   refine ⟨C,hC.tidy,p,B,?_⟩
   intro x
   refine ⟨p.eval x.length,le_rfl,?_⟩
   simpa only [NativeCPU.nativeOutput,Bool.false_eq_true,↓reduceIte,(hM x).2] using htrace O x

 theorem of_pure (O : Oracle) (f : Word → Word) (hf : ComputableTidilyInPolyTime f encBits encBits) : Computes O f :=
   pure_word_machine f hf O

 theorem of_native (O : Oracle) (M : OTM) (p : Polynomial ℕ) (f : Word → Word)
     (hf : ∀ x : Word, M.output O x (p.eval x.length) = f x) : Computes O f := by
   obtain ⟨C,hC,B,htrace⟩ := NativeCPU.native_protocol M p false
   apply of_protocol C hC.tidy O f p B
   intro x
   refine ⟨p.eval x.length,le_rfl,?_⟩
   simpa only [NativeCPU.nativeOutput,Bool.false_eq_true,↓reduceIte,hf x] using htrace O x

 theorem compose (O : Oracle) (f g : Word → Word) (hf : Computes O f) (hg : Computes O g) :
     Computes O (fun x => g (f x)) := by
   obtain ⟨C,hC,T1,B1,ht1⟩ := to_protocol O f hf
   obtain ⟨D,hD,T2,B2,ht2⟩ := to_protocol O g hg
   obtain ⟨T,B,htrace⟩ := ProtocolCompose.protocol C D hC hD O f g T1 B1 T2 B2 ht1 ht2
   exact of_protocol _ (ProtocolCompose.cpu_poly C D hC hD) O _ T B htrace

 theorem retain (O : Oracle) (f : Word → Word) (hf : Computes O f) :
     Computes O (fun x => tup [x,f x]) := by
   obtain ⟨C,hC,T,B,htrace⟩ := to_protocol O f hf
   exact of_protocol _ (ProtocolContext.cpu_poly C hC) O _ T (2*B+4*Polynomial.X+10)
     (ProtocolContext.protocol C O f T B htrace)

 theorem retag (tag : Bool) (O J : Oracle) (hJ : ∀ q, J (tag::q) = O q)
     (f : Word → Word) (hf : Computes O f) : Computes J f := by
   obtain ⟨C,hC,T,B,htrace⟩ := to_protocol O f hf
   exact of_protocol _ (OracleTag.cpu_poly tag C hC) J _ T (B+2)
     (OracleTag.protocol tag C O J hJ f T B htrace)

 def joinOracle (O0 O1 : Oracle) (w : Word) : Bool := if w.headD false then O1 w.tail else O0 w.tail
 theorem join_false (O0 O1 : Oracle) (q : Word) : joinOracle O0 O1 (false::q) = O0 q := by simp [joinOracle]
 theorem join_true (O0 O1 : Oracle) (q : Word) : joinOracle O0 O1 (true::q) = O1 q := by simp [joinOracle]
 theorem join_sigma (i : ℕ) (O0 O1 : Oracle) (h0 : {x | O0 x=true} ∈ Sigma i) (h1 : {x | O1 x=true} ∈ Sigma i) :
     {x | joinOracle O0 O1 x=true} ∈ Sigma i := by
   have he : {x | joinOracle O0 O1 x=true} = SigmaClosure.taggedJoin {x | O0 x=true} {x | O1 x=true} := by
     ext w
     simp only [Set.mem_setOf_eq,joinOracle,SigmaClosure.taggedJoin]
     split <;> rfl
   rw [he]
   exact SigmaClosure.taggedJoin_sigma i _ _ h0 h1

 theorem inFP_iff (i : ℕ) (f : Word → Word) :
     InFP i f ↔ ∃ O : Oracle, {x | O x=true} ∈ Sigma i ∧ Computes O f := by
   constructor
   · rintro ⟨O,M,p,hO,hM⟩
     exact ⟨O,hO,of_native O M p f (fun x => (hM x).2)⟩
   · rintro ⟨O,hO,M,p,hM⟩
     exact ⟨O,M,p,hO,fun x => ⟨by rw [(hM x).1]; rfl,(hM x).2⟩⟩

 theorem inFP_compose (i : ℕ) (f g : Word → Word) (hf : InFP i f) (hg : InFP i g) :
     InFP i (fun x => g (f x)) := by
   obtain ⟨O0,h0,hf⟩ := (inFP_iff i f).mp hf
   obtain ⟨O1,h1,hg⟩ := (inFP_iff i g).mp hg
   let J := joinOracle O0 O1
   apply (inFP_iff i _).mpr
   exact ⟨J,join_sigma i O0 O1 h0 h1,
     compose J f g (retag false O0 J (join_false O0 O1) f hf) (retag true O1 J (join_true O0 O1) g hg)⟩

 theorem inFP_retain (i : ℕ) (f : Word → Word) (hf : InFP i f) : InFP i (fun x => tup [x,f x]) := by
   obtain ⟨O,hO,hf⟩ := (inFP_iff i f).mp hf
   exact (inFP_iff i _).mpr ⟨O,hO,retain O f hf⟩

 theorem inFP_post (i : ℕ) (f g : Word → Word) (hf : InFP i f)
     (hg : ComputableTidilyInPolyTime g encBits encBits) : InFP i (fun x => g (f x)) := by
   obtain ⟨O,hO,hf⟩ := (inFP_iff i f).mp hf
   exact (inFP_iff i _).mpr ⟨O,hO,compose O f g hf (of_pure O g hg)⟩

end StudentTeacher976.Adaptivity.OracleComputations
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NormalizationData
open QAdvFew.PoQOracle Turing.MultiTapeTM

 def original (s : Word) : Word := (TupleCodec.decodeTuple s).headD []
 def guesses (s : Word) : List (List Word) :=
   (TupleCodec.decodeTuple ((TupleCodec.decodeTuple s).tail.headD [])).map TupleCodec.decodeTuple
 def inputs (s : Word) : List Word := TupleCodec.decodeTuple (AuxiliaryTestData.parts (original s)).1
 def replies (s : Word) : List Word :=
   (TupleCodec.decodeTuple (AuxiliaryTestData.parts (original s)).2.2).flatMap TupleCodec.decodeTuple
 def replyWords (z : Word) : List Word := TupleCodec.decodeTuple ((TupleCodec.decodeTuple z).tail.headD [])
 def pool (s : Word) (j : ℕ) : List Word :=
   (replies s).map (fun z => (replyWords z).getD j []) ++ (guesses s).map (fun Y => Y.getD j [])
 def cap (s : Word) : ℕ := (guesses s).flatten.length
 def count (s : Word) : ℕ := (replies s).length+(guesses s).length
 def coordinate (s : Word) (j : ℕ) : Word := (inputs s).getD j []

 theorem original_poly : ComputableTidilyInPolyTime original encBits encBits :=
   (ComputableTidilyInPolyTime.headD []).comp TupleCodec.decoder_poly.tidy
 theorem guesses_poly : ComputableTidilyInPolyTime guesses encBits (encList (encList encBits)) := by
   have hd := TupleCodec.decoder_poly.tidy
   unfold guesses
   apply (ComputableTidilyInPolyTime.map hd).comp
   fun_prop
 theorem inputs_poly : ComputableTidilyInPolyTime inputs encBits (encList encBits) :=
   TupleCodec.decoder_poly.tidy.comp ((AuxiliaryTestData.parts_poly.comp original_poly).fst')
 theorem replies_poly : ComputableTidilyInPolyTime replies encBits (encList encBits) := by
   have hd := TupleCodec.decoder_poly.tidy
   have hp := AuxiliaryTestData.parts_poly.comp original_poly
   unfold replies
   apply ComputableTidilyInPolyTime.flatMapWithInput
   · exact hd.comp hp.snd'.snd'
   · exact hd.comp (ComputableTidilyInPolyTime.snd encBits encBits)
 theorem replyWords_poly : ComputableTidilyInPolyTime replyWords encBits (encList encBits) := by
   have hd := TupleCodec.decoder_poly.tidy
   unfold replyWords
   apply hd.comp
   fun_prop
 theorem pool_poly : ComputableTidilyInPolyTime (fun p : Word × ℕ => pool p.1 p.2)
     (encPair encBits encUnary) (encList encBits) := by
   have hr := replies_poly
   have hg := guesses_poly
   have hw := replyWords_poly
   have hget := ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []
   have hleft : ComputableTidilyInPolyTime (fun p : Word × ℕ => (replies p.1).map fun z => (replyWords z).getD p.2 [])
       (encPair encBits encUnary) (encList encBits) := by
     apply ComputableTidilyInPolyTime.mapWithInput (hr.comp (ComputableTidilyInPolyTime.fst encBits encUnary))
     apply hget.comp (g := fun p : (Word × ℕ) × Word => (replyWords p.2,p.1.2))
     fun_prop
   have hright : ComputableTidilyInPolyTime (fun p : Word × ℕ => (guesses p.1).map fun Y => Y.getD p.2 [])
       (encPair encBits encUnary) (encList encBits) := by
     apply ComputableTidilyInPolyTime.mapWithInput (hg.comp (ComputableTidilyInPolyTime.fst encBits encUnary))
     apply hget.comp (g := fun p : (Word × ℕ) × List Word => (p.2,p.1.2))
     fun_prop
   exact ComputableTidilyInPolyTime.listAppend' hleft hright
 theorem cap_poly : ComputableTidilyInPolyTime cap encBits encUnary := by
   have hg := guesses_poly
   unfold cap
   fun_prop
 theorem count_poly : ComputableTidilyInPolyTime count encBits encUnary := by
   have hr := (ComputableTidilyInPolyTime.length_list encBits).comp replies_poly
   have hg := (ComputableTidilyInPolyTime.length_list (encList encBits)).comp guesses_poly
   unfold count
   fun_prop
 theorem coordinate_poly : ComputableTidilyInPolyTime (fun p : Word × ℕ => coordinate p.1 p.2)
     (encPair encBits encUnary) encBits :=
   (ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []).comp
     ((inputs_poly.comp (ComputableTidilyInPolyTime.fst encBits encUnary)).prod (ComputableTidilyInPolyTime.snd encBits encUnary))

 def choose {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word) (pool : List Word) (bits fallback : Word) : Word :=
   (((pool.zip bits).find? fun wb => decide (wb.1.length = W.length.eval a.length) && wb.2).map Prod.fst).getD fallback
 theorem choose_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (fun p : Word × List Word × Word × Word => choose W p.1 p.2.1 p.2.2.1 p.2.2.2)
       (encPair encBits (encPair (encList encBits) (encPair encBits encBits))) encBits := by
   have he := ComputableTidilyInPolyTime.unary_eval W.length
   have hz : ComputableTidilyInPolyTime (fun p : Word × List Word × Word × Word => p.2.1.zip p.2.2.1)
       (encPair encBits (encPair (encList encBits) (encPair encBits encBits))) (encList (encPair encBits encBool)) := by
     apply (ComputableTidilyInPolyTime.zip encBits encBool).comp
       (g := fun p : Word × List Word × Word × Word => (p.2.1,p.2.2.1))
     apply ComputableTidilyInPolyTime.prod
     · fun_prop
     · exact (bits_encList_polyTime encBool).1.tidy.comp (by fun_prop)
   have hf := ComputableTidilyInPolyTime.findWithInput
     (test := fun (p : Word × List Word × Word × Word) (wb : Word × Bool) =>
       decide (wb.1.length = W.length.eval p.1.length) && wb.2) hz (by fun_prop)
   have hsel := ComputableTidilyInPolyTime.optionElimWithInput hf
     (fallback := fun p : Word × List Word × Word × Word => p.2.2.2) (by fun_prop)
     (body := fun (_ : Word × List Word × Word × Word) (wb : Word × Bool) => wb.1) (by fun_prop)
   unfold choose
   convert hsel using 1
   funext p
   cases (p.2.1.zip p.2.2.1).find? (fun wb => decide (wb.1.length = W.length.eval p.1.length) && wb.2) <;> rfl
 theorem choose_correct {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word)
     (pool : List Word) (f : Word → Bool) (hf : ∀ w, f w=true ↔ W.test a w) (fallback : Word) :
     choose W a pool (pool.map f) fallback =
       (pool.find? fun w => @decide (ValidWitness W a w) (Classical.propDecidable _)).getD fallback := by
   classical
   have hp : (fun w => decide (w.length = W.length.eval a.length) && f w) = (fun w => decide (ValidWitness W a w)) := by
     funext w
     apply Bool.eq_iff_iff.mpr
     rw [Bool.and_eq_true_iff,decide_eq_true_eq,decide_eq_true_eq,hf]
     rfl
   unfold choose
   rw [← List.map_prod_left_eq_zip]
   simp only [List.find?_map,Option.map_map,Function.comp_def]
   rw [hp]
   change ((pool.find? fun w => decide (ValidWitness W a w)).map id).getD _ = _
   rw [Option.map_id]
   rfl

 def prep (s : Word) : List Word :=
   (List.range (cap s)).flatMap fun j => (pool s j).map fun w => tup [coordinate s j,w]
 theorem prep_poly : ComputableTidilyInPolyTime prep encBits (encList encBits) := by
   have hp := pool_poly
   have hc := coordinate_poly
   have hmap : ComputableTidilyInPolyTime (fun p : Word × ℕ => (pool p.1 p.2).map fun w => tup [coordinate p.1 p.2,w])
       (encPair encBits encUnary) (encList encBits) := by
     apply ComputableTidilyInPolyTime.mapWithInput hp
     apply TupleCodec.encode_poly.comp
     fun_prop
   unfold prep
   exact ComputableTidilyInPolyTime.flatMapWithInput (ComputableTidilyInPolyTime.range.comp cap_poly) hmap

 def row {i : ℕ} {L : Language} (W : WitnessPresentation i L) (s bits : Word) (Y : List Word) : List Word :=
   Y.zipIdx.map fun yj => choose W (coordinate s yj.2) (pool s yj.2)
     ((bits.drop (yj.2*count s)).take (count s)) yj.1
 def post {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word × Word) : Word :=
   tup (((guesses a.1).map (row W a.1 a.2)).map tup)

 theorem row_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (fun p : Word × Word × List Word => row W p.1 p.2.1 p.2.2)
       (encPair encBits (encPair encBits (encList encBits))) (encList encBits) := by
   have hp := pool_poly
   have hc := coordinate_poly
   have hn : ComputableTidilyInPolyTime (fun p : (Word × Word × List Word) × (Word × ℕ) => count p.1.1)
       (encPair (encPair encBits (encPair encBits (encList encBits))) (encPair encBits encUnary)) encUnary :=
     count_poly.comp (g := fun p : (Word × Word × List Word) × (Word × ℕ) => p.1.1) (by fun_prop)
   unfold row
   apply ComputableTidilyInPolyTime.mapWithInput
     ((ComputableTidilyInPolyTime.zipIdx encBits).comp (by fun_prop))
   apply (choose_poly W).comp (g := fun p : (Word × Word × List Word) × (Word × ℕ) =>
     (coordinate p.1.1 p.2.2,pool p.1.1 p.2.2,(p.1.2.1.drop (p.2.2*count p.1.1)).take (count p.1.1),p.2.1))
   apply ComputableTidilyInPolyTime.prod
   · apply hc.comp (g := fun p : (Word × Word × List Word) × (Word × ℕ) => (p.1.1,p.2.2))
     fun_prop
   · apply ComputableTidilyInPolyTime.prod
     · apply hp.comp (g := fun p : (Word × Word × List Word) × (Word × ℕ) => (p.1.1,p.2.2))
       fun_prop
     · fun_prop

 theorem post_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (post W) (encPair encBits encBits) encBits := by
   have hr := row_poly W
   have hg := guesses_poly
   have hm : ComputableTidilyInPolyTime (fun a : Word × Word => (guesses a.1).map (row W a.1 a.2))
       (encPair encBits encBits) (encList (encList encBits)) := by
     apply ComputableTidilyInPolyTime.mapWithInput (hg.comp (ComputableTidilyInPolyTime.fst encBits encBits))
     apply hr.comp (g := fun p : (Word × Word) × List Word => (p.1.1,p.1.2,p.2))
     fun_prop
   unfold post
   exact TupleCodec.encode_poly.comp ((ComputableTidilyInPolyTime.map TupleCodec.encode_poly).comp hm)

 theorem pool_length (s : Word) (j : ℕ) : (pool s j).length = count s := by simp [pool,count]
 theorem member_length_cap (s : Word) (Y : List Word) (hY : Y ∈ guesses s) : Y.length ≤ cap s := by
   have helper : ∀ G : List (List Word), ∀ Y ∈ G, Y.length ≤ G.flatten.length := by
     intro G
     induction G with
     | nil => simp
     | cons A G ih =>
       intro Y hY
       rcases List.mem_cons.mp hY with rfl | hY
       · simp
       · have hh := ih Y hY
         simp only [List.flatten_cons,List.length_append]
         omega
   exact helper (guesses s) Y hY

 theorem chunk_flatMap {α : Type} (X : List α) (fallback : α) (f : α → Word) (d j : ℕ) (hj : j < X.length)
     (hlen : ∀ a ∈ X, (f a).length = d) :
     ((X.flatMap f).drop (j*d)).take d = f (X.getD j fallback) := by
   induction X generalizing j with
   | nil => simp at hj
   | cons a X ih =>
     have ha := hlen a List.mem_cons_self
     cases j with
     | zero => simpa [ha] using (show ((f a ++ X.flatMap f).take (f a).length) = f a by simp)
     | succ j =>
       have hh := ih j (by simpa using hj) (fun b hb => hlen b (List.mem_cons_of_mem a hb))
       have he : (f a).drop (j*d+d) = [] := List.drop_eq_nil_iff.mpr (by omega)
       simpa [List.flatMap_cons,Nat.succ_mul,List.drop_append,ha,Nat.add_sub_cancel,he] using hh

 theorem row_correct (M : OTM) (O : Oracle) (p : Polynomial ℕ)
     {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (hW : ∀ a b, NativeBatch.result M O p (tup [a,b])=true ↔ W.test a b)
     (s : Word) (Y : List Word) (hY : Y ∈ guesses s) :
     row W s (NativeBatch.scores M O p (prep s)) Y =
       Y.mapIdx (fun j y => ((pool s j).find? fun w => @decide (ValidWitness W (coordinate s j) w)
         (Classical.propDecidable _)).getD y) := by
   classical
   have he : NativeBatch.scores M O p (prep s) =
       (List.range (cap s)).flatMap (fun j => (pool s j).map fun w => NativeBatch.result M O p (tup [coordinate s j,w])) := by
     simp [NativeBatch.scores,prep,List.map_flatMap,List.map_map,Function.comp_def]
   unfold row
   rw [he]
   apply List.ext_getElem (by simp)
   intro j hj hj'
   simp only [List.getElem_map,List.getElem_zipIdx,List.getElem_mapIdx,Nat.zero_add]
   have hjY : j < Y.length := by simpa using hj'
   have hjcap : j < cap s := lt_of_lt_of_le hjY (member_length_cap s Y hY)
   have hh := chunk_flatMap (List.range (cap s)) 0
     (fun j => (pool s j).map fun w => NativeBatch.result M O p (tup [coordinate s j,w])) (count s) j
     (by simpa using hjcap) (by intro a ha; simp [pool_length])
   rw [List.getD_eq_getElem _ _ (by simpa using hjcap),List.getElem_range] at hh
   rw [hh]
   exact choose_correct W _ _ _ (hW _) _

 def studentInput (X : List Word) (t : ℕ) (H : List (List TupleReply)) : Word :=
   tup [tup X,List.replicate (t+1) true,tup (H.map fun B => tup (B.map encodeReply))]
 theorem original_encoded (s v : Word) : original (tup [s,v]) = s := by simp [original,TupleCodec.decode_tup]
 theorem guesses_encoded (s : Word) (G : List (List Word)) : guesses (tup [s,tup (G.map tup)]) = G := by
   simp [guesses,TupleCodec.decode_tup,List.map_map,Function.comp_def]
 theorem inputs_encoded (X : List Word) (t : ℕ) (H : List (List TupleReply)) (v : Word) :
     inputs (tup [studentInput X t H,v]) = X := by
   simp [inputs,original_encoded,studentInput,AuxiliaryTestData.parts_tup,TupleCodec.decode_tup]
 theorem replies_encoded (X : List Word) (t : ℕ) (H : List (List TupleReply)) (v : Word) :
     replies (tup [studentInput X t H,v]) = H.flatten.map encodeReply := by
   simp [replies,original_encoded,studentInput,AuxiliaryTestData.parts_tup,TupleCodec.decode_tup,
     List.flatMap_map,List.map_flatMap,Function.comp_def,List.flatMap_def]
 theorem replyWords_encoded (z : TupleReply) : replyWords (encodeReply z) = z.2 := by
   simp [replyWords,encodeReply,TupleCodec.decode_tup]

 theorem post_encoded (M : OTM) (O : Oracle) (p : Polynomial ℕ)
     {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (hW : ∀ a b, NativeBatch.result M O p (tup [a,b])=true ↔ W.test a b)
     (X : List Word) (t : ℕ) (H : List (List TupleReply)) :
     let s := tup [studentInput X t H,tup ((f X t H).map tup)];
     post W (s,NativeBatch.scores M O p (prep s)) = tup ((normalize W f X t H).map tup) := by
   classical
   dsimp only
   unfold post
   rw [guesses_encoded]
   congr 1
   congr 1
   unfold normalize
   apply List.map_congr_left
   intro Y hY
   rw [row_correct M O p W hW _ Y (by simpa only [guesses_encoded] using hY)]
   simp only [pool,replies_encoded,guesses_encoded,coordinate,inputs_encoded,List.map_map,
     Function.comp_def,replyWords_encoded,normalize]

end StudentTeacher976.Adaptivity.NormalizationData
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceSemantic
theorem words_spec (n : ℕ) (w : Word) : w ∈ wordsOfLength n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [wordsOfLength, List.length_eq_zero_iff]
  | succ n ih =>
    cases w with
    | nil => simp [wordsOfLength]
    | cons b w =>
      cases b <;> simp [wordsOfLength, ih]

theorem leastWitness_spec {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    {x : Word} (hx : ∃ y, ValidWitness W x y) :
    ∃ y, leastWitness W x = some y ∧ ValidWitness W x y := by
  classical
  obtain ⟨y, hylen, hy⟩ := hx
  have hex : ∃ y ∈ wordsOfLength (W.length.eval x.length), W.test x y :=
    ⟨y, (words_spec _ _).mpr hylen, hy⟩
  have hn : (leastWitness W x).isSome := by
    simpa [leastWitness, List.find?_isSome] using hex
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hn
  refine ⟨z, hz, ?_⟩
  have hmem := List.mem_of_find?_eq_some (show _ = some z from hz)
  have htest := List.find?_some (show _ = some z from hz)
  exact ⟨(words_spec _ _).mp hmem, of_decide_eq_true htest⟩

theorem teacher_spec {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    {n k : ℕ} {X : List Word} (hX : TupleShape n k X)
    {B : List (List Word)} {z : TupleReply} (hz : teacher W X B = some z) :
    ReplyShape W n k z ∧ ∀ Y ∈ B, ¬ TupleTest W X Y z := by
  classical
  unfold teacher at hz
  obtain ⟨j, hj, hrest⟩ := Option.bind_eq_some_iff.mp hz
  have hjprop := List.find?_some hj
  have hjmem := List.mem_of_find?_eq_some hj
  have hjlt : j < X.length := List.mem_range.mp hjmem
  have hjp : (∃ w, ValidWitness W (X.getD j []) w) ∧
      ¬ ∃ Y ∈ B, ValidWitness W (X.getD j []) (Y.getD j []) := by
    simpa using hjprop
  obtain ⟨w, hw, hvalid⟩ := leastWitness_spec W hjp.1
  simp only [hw, Option.map_some, Option.some.injEq] at hrest
  subst z
  have hlen : ∀ j < X.length, (X.getD j []).length = n := by
    intro j hj
    apply hX.2
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  constructor
  · refine ⟨by simpa [hX.1] using hjlt, ?_, ?_⟩
    · simp [TupleShape, hX.1]
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
      have halt := List.mem_range.mp ha
      by_cases h : a = j
      · subst a
        rw [if_pos rfl]
        exact hvalid.1.trans (congrArg (fun l => W.length.eval l) (hlen j hjlt))
      · simp only [if_neg h, List.length_replicate, hlen a halt]
  · intro Y hY htest
    apply hjp.2
    refine ⟨Y, hY, htest.2.2 hjlt ?_⟩
    simpa [List.getD_map, hjlt] using hvalid

theorem trace_le {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (f : TupleStudent) (q : ℕ) (X : List Word) (t : ℕ) :
    (fixedTrace W f q X t).length ≤ t := by
  induction t with
  | zero => simp [fixedTrace]
  | succ t ih =>
    simp only [fixedTrace]
    split
    · omega
    · split <;> simp_all <;> omega

theorem trace_spec {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (f : TupleStudent) (q n k : ℕ) (X : List Word) (hX : TupleShape n k X) (t : ℕ) :
    (∀ z ∈ fixedTrace W f q X t, ReplyShape W n k z) ∧
    ∀ s, s < (fixedTrace W f q X t).length →
      teacher W X (normalize W f X s
        (((fixedTrace W f q X t).take s).map fun z => List.replicate q z)) =
        some ((fixedTrace W f q X t).getD s (0, [])) := by
  classical
  induction t with
  | zero => simp [fixedTrace]
  | succ t ih =>
    rw [fixedTrace]
    split
    · exact ih
    · rename_i hfull
      have hlen : (fixedTrace W f q X t).length = t := by
        have := trace_le W f q X t
        omega
      split
      · exact ih
      · rename_i z hz
        constructor
        · intro z' hz'
          rcases List.mem_append.mp hz' with h | h
          · exact ih.1 z' h
          · have heq : z' = z := by simpa using h
            subst z'
            exact (teacher_spec W hX hz).1
        · intro s hs
          have hsle : s ≤ t := by simpa [hlen] using hs
          by_cases hst : s < t
          · rw [List.take_append_of_le_length (by omega), List.getD_append _ _ _ _ (by omega)]
            exact ih.2 s (by omega)
          · have heq : s = t := by omega
            subst s
            rw [List.take_append_of_le_length (by omega), List.getD_append_right _ _ _ _ (by omega)]
            have htake : (fixedTrace W f q X t).take t = fixedTrace W f q X t :=
              List.take_of_length_le (by omega)
            rw [htake]
            simpa [hlen] using hz

theorem trace_short {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (f : TupleStudent) (n k q : ℕ) (X : List Word) (hX : TupleShape n k X)
    (hfshape : TupleStudentShape W n k q f)
    (hwin : TupleStudentWins W n k q (normalize W f)) :
    (fixedTrace W f q X k).length < k := by
  classical
  have hle := trace_le W f q X k
  by_contra! hnot
  have hlen : (fixedTrace W f q X k).length = k := by omega
  let Z := fixedTrace W f q X k
  let H := Z.map fun z => List.replicate q z
  have hspec := trace_spec W f q n k X hX k
  have hshape : TupleHistoryShape W n k q k H := by
    refine ⟨by simp [H, Z, hlen], ?_⟩
    intro B hB
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hB
    refine ⟨by simp, ?_⟩
    intro z' hz'
    have : z' = z := (List.mem_replicate.mp hz').2
    subst z'
    exact hspec.1 z hz
  obtain ⟨t, ht, j, hj, htest⟩ := hwin X H hX hshape
  have hpast : (Z.take t).map (fun z => List.replicate q z) = H.take t := by
    simp [H, List.map_take]
  have hteach := hspec.2 t (by omega)
  have hteacher := (teacher_spec W hX hteach).2
  have hpastshape : TupleHistoryShape W n k q t (H.take t) := by
    refine ⟨by simp [H, Z, hlen, Nat.min_eq_left (Nat.le_of_lt ht)], ?_⟩
    intro B hB
    exact hshape.2 B (List.mem_of_mem_take hB)
  have hflen : (normalize W f X t (H.take t)).length = q := by
    simpa [normalize] using (hfshape.1 X t (H.take t) hX ht hpastshape).1
  have hmem : (normalize W f X t (H.take t)).getD j [] ∈
      normalize W f X t (H.take t) := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hget : H.getD t [] = List.replicate q (Z.getD t (0, [])) := by
    have htz : t < Z.length := by simpa [Z, hlen] using ht
    rw [List.getD_eq_getElem _ _ (by simpa [H] using htz)]
    rw [List.getD_eq_getElem Z (0, []) htz]
    simp [H]
  have hreply : (H.getD t []).getD j (0, []) = Z.getD t (0, []) := by
    rw [hget, List.getD_replicate _ hj]
  apply hteacher ((normalize W f X t (H.take t)).getD j [])
  · simpa only [← hpast] using hmem
  · simpa only [hreply, ← hpast] using htest

 theorem terminal_before {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (q : ℕ) (X : List Word) (k : ℕ)
     (hshort : (fixedTrace W f q X k).length < k) :
     ∃ t < k, (fixedTrace W f q X t).length = t ∧
       teacher W X (normalize W f X t ((fixedTrace W f q X t).map fun z => List.replicate q z)) = none := by
   induction k with
   | zero => simp at hshort
   | succ k ih =>
     by_cases hs : (fixedTrace W f q X k).length < k
     · obtain ⟨t,ht,hlen,hterm⟩ := ih hs
       exact ⟨t,by omega,hlen,hterm⟩
     · have hlen : (fixedTrace W f q X k).length = k := by have := trace_le W f q X k; omega
       refine ⟨k,by omega,hlen,?_⟩
       rw [fixedTrace, if_neg hs] at hshort
       cases ht : teacher W X (normalize W f X k ((fixedTrace W f q X k).map fun z => List.replicate q z)) with
       | none => rfl
       | some z => simp [ht,hlen] at hshort

 theorem trace_mem_succ {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (q : ℕ) (X : List Word) (t : ℕ) :
     ∀ z ∈ fixedTrace W f q X t, z ∈ fixedTrace W f q X (t+1) := by
   intro z hz
   rw [fixedTrace]
   split
   · exact hz
   · split
     · exact hz
     · exact List.mem_append_left _ hz

 theorem trace_mem_mono {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (q : ℕ) (X : List Word) {t k : ℕ} (htk : t ≤ k) :
     ∀ z ∈ fixedTrace W f q X t, z ∈ fixedTrace W f q X k := by
   induction k with
   | zero =>
     have he : t=0 := by omega
     subst t
     exact fun _ h => h
   | succ k ih =>
     by_cases he : t=k+1
     · subst t; exact fun _ h => h
     · intro z hz
       exact trace_mem_succ W f q X k z (ih (by omega) z hz)

 theorem find_narrow {α : Type} (l : List α) (p q : α → Bool) {a : α}
     (h : l.find? p = some a) (ha : q a = true) : l.find? (fun b => p b && q b) = some a := by
   induction l with
   | nil => simp at h
   | cons b l ih =>
     by_cases hb : p b = true
     · have he : b=a := by simpa [List.find?_cons,hb] using h
       subst b
       simp [List.find?_cons,hb,ha]
     · have hh : l.find? p = some a := by simpa [List.find?_cons,hb] using h
       simpa [List.find?_cons,hb] using ih hh

 theorem find_narrow_none {α : Type} (l : List α) (p q : α → Bool)
     (h : l.find? p = none) : l.find? (fun b => p b && q b) = none := by
   induction l with
   | nil => rfl
   | cons b l ih =>
     have hb : p b ≠ true := by intro hb; simp [List.find?_cons,hb] at h
     have hh : l.find? p = none := by simpa [List.find?_cons,hb] using h
     simpa [List.find?_cons,hb] using ih hh

 noncomputable def cutTeacher {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (x : Word) (batch : List (List Word)) : Option TupleReply := by
   classical
   exact ((List.range X.length).find? fun j => decide
     ((∃ z, ValidWitness W (X.getD j []) z) ∧
       ¬ ∃ Y ∈ batch, ValidWitness W (X.getD j []) (Y.getD j [])) && decide (X.getD j [] ≠ x)).bind fun j =>
       (leastWitness W (X.getD j [])).map fun z =>
         (j,(List.range X.length).map fun h =>
           if h=j then z else List.replicate (W.length.eval (X.getD h []).length) false)

 theorem cutTeacher_none {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (x : Word) (batch : List (List Word)) (h : teacher W X batch = none) :
     cutTeacher W X x batch = none := by
   classical
   unfold teacher at h
   unfold cutTeacher
   generalize hp : (List.range X.length).find? (fun j => decide
     ((∃ z, ValidWitness W (X.getD j []) z) ∧
       ¬ ∃ Y ∈ batch, ValidWitness W (X.getD j []) (Y.getD j []))) = found at h ⊢
   cases found with
   | none =>
     rw [find_narrow_none _ _ _ hp]
     rfl
   | some j =>
     have hjp : (∃ z, ValidWitness W (X.getD j []) z) ∧
         ¬ ∃ Y ∈ batch, ValidWitness W (X.getD j []) (Y.getD j []) := by
       simpa using List.find?_some hp
     obtain ⟨w,hw,hvalid⟩ := leastWitness_spec W hjp.1
     simp only [Option.bind_some,hw,Option.map_some] at h
     cases h

 theorem cutTeacher_some {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (x : Word) (batch : List (List Word)) (z : TupleReply)
     (h : teacher W X batch = some z) (hx : X.getD z.1 [] ≠ x) :
     cutTeacher W X x batch = some z := by
   classical
   unfold teacher at h
   unfold cutTeacher
   obtain ⟨j,hj,hr⟩ := Option.bind_eq_some_iff.mp h
   have hjp : (∃ z, ValidWitness W (X.getD j []) z) ∧
       ¬ ∃ Y ∈ batch, ValidWitness W (X.getD j []) (Y.getD j []) := by
     simpa using List.find?_some hj
   obtain ⟨w,hw,hvalid⟩ := leastWitness_spec W hjp.1
   simp only [hw,Option.map_some,Option.some.injEq] at hr
   subst z
   rw [find_narrow _ _ _ hj (by simpa using hx)]
   simp only [Option.bind_some,hw,Option.map_some]

 noncomputable def cutTrace {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (q : ℕ) (X : List Word) (x : Word) : ℕ → List TupleReply
   | 0 => []
   | t+1 =>
     let replies := cutTrace W f q X x t
     if replies.length < t then replies
     else match cutTeacher W X x (normalize W f X t (replies.map fun z => List.replicate q z)) with
       | none => replies
       | some z => replies++[z]

 theorem cutTrace_eq {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (q : ℕ) (X : List Word) (x : Word) (k : ℕ)
     (havoid : ∀ z ∈ fixedTrace W f q X k, X.getD z.1 [] ≠ x) :
     ∀ t ≤ k, cutTrace W f q X x t = fixedTrace W f q X t := by
   intro t
   induction t with
   | zero => intro ht; rfl
   | succ t ih =>
     intro ht
     rw [cutTrace, fixedTrace, ih (by omega)]
     split
     · rfl
     · cases hh : teacher W X (normalize W f X t ((fixedTrace W f q X t).map fun z => List.replicate q z)) with
       | none => rw [cutTeacher_none W X x _ hh]
       | some z =>
         have hz : z ∈ fixedTrace W f q X (t+1) := by
           simp [fixedTrace,hh,show ¬ (fixedTrace W f q X t).length < t by assumption]
         have hx := havoid z (trace_mem_mono W f q X ht z hz)
         rw [cutTeacher_some W X x _ z hh hx]

 theorem teacher_none_covers {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (batch : List (List Word)) (j : ℕ) (hj : j < X.length)
     (hpos : ∃ w, ValidWitness W (X.getD j []) w) (h : teacher W X batch = none) :
     ∃ Y ∈ batch, ValidWitness W (X.getD j []) (Y.getD j []) := by
   classical
   by_contra hn
   have hex : ∃ a ∈ List.range X.length, (∃ z, ValidWitness W (X.getD a []) z) ∧
       ¬ ∃ Y ∈ batch, ValidWitness W (X.getD a []) (Y.getD a []) := ⟨j,List.mem_range.mpr hj,hpos,hn⟩
   have hs : ((List.range X.length).find? (fun a => decide
     ((∃ z, ValidWitness W (X.getD a []) z) ∧
       ¬ ∃ Y ∈ batch, ValidWitness W (X.getD a []) (Y.getD a [])))).isSome := by
     simpa [List.find?_isSome] using hex
   obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp hs
   have hjp : (∃ z, ValidWitness W (X.getD a []) z) ∧
       ¬ ∃ Y ∈ batch, ValidWitness W (X.getD a []) (Y.getD a []) := by
     simpa using List.find?_some ha
   obtain ⟨w,hw,hvalid⟩ := leastWitness_spec W hjp.1
   unfold teacher at h
   rw [ha] at h
   simp only [Option.bind_some,hw,Option.map_some] at h
   cases h

 def CutAccepts {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (q k : ℕ) (X : List Word) (x : Word) (j : ℕ) : Prop :=
   ∃ t < k, ∃ Y ∈ normalize W f X t ((cutTrace W f q X x t).map fun z => List.replicate q z),
     ValidWitness W x (Y.getD j [])

 theorem cut_accept_sound {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (q k : ℕ) (X : List Word) (x : Word) (j : ℕ)
     (h : CutAccepts W f q k X x j) : x ∈ L := by
   obtain ⟨t,ht,Y,hY,hlen,hvalid⟩ := h
   exact (W.represents x).mpr ⟨Y.getD j [],hlen,hvalid⟩

 theorem cut_accept_complete {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (n k q : ℕ) (X : List Word) (x : Word) (j : ℕ)
     (hX : TupleShape n k X) (hj : j < X.length) (hxj : X.getD j [] = x)
     (hpos : ∃ w, ValidWitness W x w)
     (hfshape : TupleStudentShape W n k q f)
     (hwin : TupleStudentWins W n k q (normalize W f))
     (havoid : ∀ z ∈ fixedTrace W f q X k, X.getD z.1 [] ≠ x) :
     CutAccepts W f q k X x j := by
   obtain ⟨t,ht,hlen,hterm⟩ := terminal_before W f q X k (trace_short W f n k q X hX hfshape hwin)
   have hcover := teacher_none_covers W X
     (normalize W f X t ((fixedTrace W f q X t).map fun z => List.replicate q z)) j hj (hxj.symm ▸ hpos) hterm
   obtain ⟨Y,hY,hvalid⟩ := hcover
   refine ⟨t,ht,Y,?_,?_⟩
   · simpa only [cutTrace_eq W f q X x k havoid t (Nat.le_of_lt ht)] using hY
   · simpa only [hxj] using hvalid

 theorem good_pair_recognized {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (n k q : ℕ) (hk : 0 < k) (S : Finset Word) (x : Word)
     (hg : GoodPair W n k q f S x)
     (hfshape : TupleStudentShape W n k q f)
     (hwin : TupleStudentWins W n k q (normalize W f)) :
     ∃ j < (orderedInput S x).length, CutAccepts W f q k (orderedInput S x) x j := by
   classical
   obtain ⟨hcard,hS,hx,hnot,havoid⟩ := hg
   have hmem : x ∈ orderedInput S x := by simp [orderedInput]
   obtain ⟨j,hj,hget⟩ := List.mem_iff_getElem.mp hmem
   have hxj : (orderedInput S x).getD j [] = x := by rw [List.getD_eq_getElem _ _ hj,hget]
   have hX : TupleShape n k (orderedInput S x) := by
     constructor
     · simp only [orderedInput,Finset.length_sort,Finset.card_insert_of_notMem hnot,hcard]
       omega
     · intro a ha
       have hsa : a=x ∨ a ∈ S := by simpa [orderedInput] using ha
       rcases hsa with rfl | hsa
       · exact hx.1
       · exact (hS a hsa).1
   exact ⟨j,hj,cut_accept_complete W f n k q _ x j hX hj hxj hx.2 hfshape hwin havoid⟩

 theorem leastWitness_some_valid {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (a w : Word) (h : leastWitness W a = some w) : ValidWitness W a w := by
   classical
   have hm := List.mem_of_find?_eq_some (show _ = some w from h)
   have hp := List.find?_some (show _ = some w from h)
   exact ⟨(words_spec _ _).mp hm,of_decide_eq_true hp⟩

 noncomputable def knownTeacher {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (x : Word) (wit : Word → Word) (batch : List (List Word)) : Option TupleReply := by
   classical
   exact ((List.range X.length).find? fun j => decide
     (X.getD j [] ≠ x ∧ ¬ ∃ Y ∈ batch, ValidWitness W (X.getD j []) (Y.getD j []))).map fun j =>
       (j,(List.range X.length).map fun h =>
         if h=j then wit (X.getD j []) else List.replicate (W.length.eval (X.getD h []).length) false)

 theorem knownTeacher_eq_cut {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (x : Word) (wit : Word → Word) (batch : List (List Word))
     (hknown : ∀ a ∈ X, a ≠ x → leastWitness W a = some (wit a)) :
     knownTeacher W X x wit batch = cutTeacher W X x batch := by
   classical
   have hpred : (List.range X.length).find? (fun j => decide
       (X.getD j [] ≠ x ∧ ¬ ∃ Y ∈ batch, ValidWitness W (X.getD j []) (Y.getD j []))) =
       (List.range X.length).find? (fun j => decide
       ((∃ z, ValidWitness W (X.getD j []) z) ∧
         ¬ ∃ Y ∈ batch, ValidWitness W (X.getD j []) (Y.getD j [])) && decide (X.getD j [] ≠ x)) := by
     apply List.find?_congr
     intro j hj
     have hjl : j < X.length := List.mem_range.mp hj
     have hm : X.getD j [] ∈ X := by rw [List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem _
     by_cases he : X.getD j [] = x
     · simp only [he,ne_eq,not_true_eq_false,decide_false,Bool.and_false,and_false,false_and]
     · have hv := leastWitness_some_valid W _ _ (hknown _ hm he)
       have hp : ∃ z, ValidWitness W (X.getD j []) z := ⟨_,hv⟩
       simp only [he,hp,not_false_eq_true,decide_true,true_and,Bool.and_true,ne_eq]
   unfold knownTeacher cutTeacher
   rw [hpred]
   cases hh : (List.range X.length).find? (fun j => decide
       ((∃ z, ValidWitness W (X.getD j []) z) ∧
         ¬ ∃ Y ∈ batch, ValidWitness W (X.getD j []) (Y.getD j [])) && decide (X.getD j [] ≠ x)) with
   | none => rfl
   | some j =>
     have hjl : j < X.length := List.mem_range.mp (List.mem_of_find?_eq_some hh)
     have hm : X.getD j [] ∈ X := by rw [List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem _
     have hn : X.getD j [] ≠ x := by
       have hb := List.find?_some hh
       exact of_decide_eq_true (Bool.and_eq_true_iff.mp hb).2
     simp only [Option.map_some,Option.bind_some,hknown _ hm hn]

 noncomputable def knownTrace {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (q : ℕ) (X : List Word) (x : Word) (wit : Word → Word) : ℕ → List TupleReply
   | 0 => []
   | t+1 =>
     let replies := knownTrace W f q X x wit t
     if replies.length < t then replies
     else match knownTeacher W X x wit (normalize W f X t (replies.map fun z => List.replicate q z)) with
       | none => replies
       | some z => replies++[z]

 theorem knownTrace_eq_cut {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (q : ℕ) (X : List Word) (x : Word) (wit : Word → Word)
     (hknown : ∀ a ∈ X, a ≠ x → leastWitness W a = some (wit a)) (t : ℕ) :
     knownTrace W f q X x wit t = cutTrace W f q X x t := by
   induction t with
   | zero => rfl
   | succ t ih =>
     simp only [knownTrace,cutTrace,ih,knownTeacher_eq_cut W X x wit _ hknown]

 theorem knownTeacher_wit_congr {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (x : Word) (wit0 wit1 : Word → Word) (batch : List (List Word))
     (h : ∀ a ∈ X, a ≠ x → wit0 a=wit1 a) :
     knownTeacher W X x wit0 batch=knownTeacher W X x wit1 batch := by
   classical
   unfold knownTeacher
   cases hh : (List.range X.length).find? (fun j => decide
       (X.getD j [] ≠ x ∧ ¬ ∃ Y ∈ batch, ValidWitness W (X.getD j []) (Y.getD j []))) with
   | none => rfl
   | some j =>
     have hj : j < X.length := List.mem_range.mp (List.mem_of_find?_eq_some hh)
     have hm : X.getD j [] ∈ X := by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
     have hx : X.getD j [] ≠ x := by
       have hp : X.getD j [] ≠ x ∧ ¬ ∃ Y ∈ batch, ValidWitness W (X.getD j []) (Y.getD j []) := by
         simpa using List.find?_some hh
       exact hp.1
     simp only [Option.map_some,h _ hm hx]

end StudentTeacher976.Adaptivity.AdviceSemantic
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceTeacherData
open QAdvFew.PoQOracle Turing.MultiTapeTM

 def field (s : Word) (j : ℕ) : Word := (TupleCodec.decodeTuple s).getD j []
 def inputs (s : Word) : List Word := TupleCodec.decodeTuple (field s 0)
 def target (s : Word) : Word := field s 1
 def guesses (s : Word) : List (List Word) := (TupleCodec.decodeTuple (field s 2)).map TupleCodec.decodeTuple
 def dictionary (s : Word) : List Word := TupleCodec.decodeTuple (field s 3)
 def key (entry : Word) : Word := (TupleCodec.decodeTuple entry).headD []
 def value (entry : Word) : Word := (TupleCodec.decodeTuple entry).tail.headD []
 def witness (s a : Word) : Word := ((dictionary s).find? fun e => key e == a).elim [] value
 def coordinate (s : Word) (j : ℕ) : Word := (inputs s).getD j []
 def pool (s : Word) (j : ℕ) : List Word := (guesses s).map fun Y => Y.getD j []
 def count (s : Word) : ℕ := (guesses s).length
 def prep (s : Word) : List Word :=
   (List.range (inputs s).length).flatMap fun j => (pool s j).map fun w => tup [coordinate s j,w]

 theorem field_poly (j : ℕ) : ComputableTidilyInPolyTime (fun s => field s j) encBits encBits :=
   (ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []).comp
     (TupleCodec.decoder_poly.tidy.prod (ComputableTidilyInPolyTime.const j))
 theorem inputs_poly : ComputableTidilyInPolyTime inputs encBits (encList encBits) :=
   TupleCodec.decoder_poly.tidy.comp (field_poly 0)
 theorem target_poly : ComputableTidilyInPolyTime target encBits encBits := field_poly 1
 theorem guesses_poly : ComputableTidilyInPolyTime guesses encBits (encList (encList encBits)) :=
   (ComputableTidilyInPolyTime.map TupleCodec.decoder_poly.tidy).comp (TupleCodec.decoder_poly.tidy.comp (field_poly 2))
 theorem dictionary_poly : ComputableTidilyInPolyTime dictionary encBits (encList encBits) :=
   TupleCodec.decoder_poly.tidy.comp (field_poly 3)
 theorem key_poly : ComputableTidilyInPolyTime key encBits encBits :=
   (ComputableTidilyInPolyTime.headD []).comp TupleCodec.decoder_poly.tidy
 theorem value_poly : ComputableTidilyInPolyTime value encBits encBits := by
   have hd := TupleCodec.decoder_poly.tidy
   unfold value
   fun_prop
 theorem witness_poly : ComputableTidilyInPolyTime (fun p : Word × Word => witness p.1 p.2)
     (encPair encBits encBits) encBits := by
   have hk := key_poly
   have hv := value_poly
   have hf := ComputableTidilyInPolyTime.findWithInput
     (test := fun (p : Word × Word) e => key e == p.2)
     (dictionary_poly.comp (ComputableTidilyInPolyTime.fst encBits encBits)) (by fun_prop)
   exact ComputableTidilyInPolyTime.optionElimWithInput hf (ComputableTidilyInPolyTime.const [])
     (body := fun (_ : Word × Word) e => value e) (hv.comp (ComputableTidilyInPolyTime.snd (encPair encBits encBits) encBits))
 theorem coordinate_poly : ComputableTidilyInPolyTime (fun p : Word × ℕ => coordinate p.1 p.2)
     (encPair encBits encUnary) encBits :=
   (ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []).comp
     ((inputs_poly.comp (ComputableTidilyInPolyTime.fst encBits encUnary)).prod (ComputableTidilyInPolyTime.snd encBits encUnary))
 theorem pool_poly : ComputableTidilyInPolyTime (fun p : Word × ℕ => pool p.1 p.2)
     (encPair encBits encUnary) (encList encBits) := by
   unfold pool
   apply ComputableTidilyInPolyTime.mapWithInput (guesses_poly.comp (ComputableTidilyInPolyTime.fst encBits encUnary))
   apply (ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []).comp
     (g := fun p : (Word × ℕ) × List Word => (p.2,p.1.2))
   fun_prop
 theorem count_poly : ComputableTidilyInPolyTime count encBits encUnary :=
   (ComputableTidilyInPolyTime.length_list (encList encBits)).comp guesses_poly
 theorem prep_poly : ComputableTidilyInPolyTime prep encBits (encList encBits) := by
   have hp := pool_poly
   have hc := coordinate_poly
   have hm : ComputableTidilyInPolyTime (fun p : Word × ℕ => (pool p.1 p.2).map fun w => tup [coordinate p.1 p.2,w])
       (encPair encBits encUnary) (encList encBits) := by
     apply ComputableTidilyInPolyTime.mapWithInput hp
     apply TupleCodec.encode_poly.comp
     fun_prop
   unfold prep
   exact ComputableTidilyInPolyTime.flatMapWithInput
     (ComputableTidilyInPolyTime.range.comp ((ComputableTidilyInPolyTime.length_list encBits).comp inputs_poly)) hm

 def covered {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word) (pool : List Word) (bits : Word) : Bool :=
   ((pool.zip bits).find? fun wb => decide (wb.1.length = W.length.eval a.length) && wb.2).isSome
 theorem covered_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (fun p : Word × List Word × Word => covered W p.1 p.2.1 p.2.2)
       (encPair encBits (encPair (encList encBits) encBits)) encBool := by
   have he := ComputableTidilyInPolyTime.unary_eval W.length
   have hz : ComputableTidilyInPolyTime (fun p : Word × List Word × Word => p.2.1.zip p.2.2)
       (encPair encBits (encPair (encList encBits) encBits)) (encList (encPair encBits encBool)) := by
     apply (ComputableTidilyInPolyTime.zip encBits encBool).comp (g := fun p : Word × List Word × Word => (p.2.1,p.2.2))
     apply ComputableTidilyInPolyTime.prod
     · fun_prop
     · exact (bits_encList_polyTime encBool).1.tidy.comp (by fun_prop)
   have hf := ComputableTidilyInPolyTime.findWithInput
     (test := fun (p : Word × List Word × Word) (wb : Word × Bool) =>
       decide (wb.1.length = W.length.eval p.1.length) && wb.2) hz (by fun_prop)
   exact hf.optionIsSome
 theorem covered_correct {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word)
     (pool : List Word) (f : Word → Bool) (hf : ∀ w, f w=true ↔ W.test a w) :
     covered W a pool (pool.map f)=true ↔ ∃ w ∈ pool, ValidWitness W a w := by
   unfold covered
   rw [← List.map_prod_left_eq_zip]
   simp [List.find?_map,List.find?_isSome,ValidWitness,hf]

 def chooseIndex {i : ℕ} {L : Language} (W : WitnessPresentation i L) (s bits : Word) : Option ℕ :=
   (List.range (inputs s).length).find? fun j =>
     decide (coordinate s j ≠ target s) && !(covered W (coordinate s j) (pool s j) ((bits.drop (j*count s)).take (count s)))
 def zeros {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word) : Word := List.replicate (W.length.eval a.length) false
 def reply {i : ℕ} {L : Language} (W : WitnessPresentation i L) (s : Word) (j : ℕ) : Word :=
   encodeReply (j,(List.range (inputs s).length).map fun h => if h=j then witness s (coordinate s j) else zeros W (coordinate s h))
 def post {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word × Word) : Word :=
   (chooseIndex W a.1 a.2).elim (tup []) (fun j => tup [reply W a.1 j])

 theorem chooseIndex_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (fun a : Word × Word => chooseIndex W a.1 a.2)
       (encPair encBits encBits) (encOption encUnary) := by
   have hc := coordinate_poly
   have hp := pool_poly
   have ht := target_poly
   have hn : ComputableTidilyInPolyTime (fun p : (Word × Word) × ℕ => count p.1.1)
       (encPair (encPair encBits encBits) encUnary) encUnary :=
     count_poly.comp (g := fun p : (Word × Word) × ℕ => p.1.1) (by fun_prop)
   have hcov : ComputableTidilyInPolyTime (fun p : (Word × Word) × ℕ =>
       covered W (coordinate p.1.1 p.2) (pool p.1.1 p.2) ((p.1.2.drop (p.2*count p.1.1)).take (count p.1.1)))
       (encPair (encPair encBits encBits) encUnary) encBool := by
     apply (covered_poly W).comp (g := fun p : (Word × Word) × ℕ =>
       (coordinate p.1.1 p.2,pool p.1.1 p.2,(p.1.2.drop (p.2*count p.1.1)).take (count p.1.1)))
     apply ComputableTidilyInPolyTime.prod
     · apply hc.comp (g := fun p : (Word × Word) × ℕ => (p.1.1,p.2))
       fun_prop
     · apply ComputableTidilyInPolyTime.prod
       · apply hp.comp (g := fun p : (Word × Word) × ℕ => (p.1.1,p.2))
         fun_prop
       · fun_prop
   unfold chooseIndex
   apply ComputableTidilyInPolyTime.findWithInput
   · apply ComputableTidilyInPolyTime.range.comp
     exact ((ComputableTidilyInPolyTime.length_list encBits).comp inputs_poly).comp (ComputableTidilyInPolyTime.fst encBits encBits)
   · apply ComputableTidilyInPolyTime.bool_and'
     · have hcoord := hc.comp (encIn := encPair (encPair encBits encBits) encUnary) (g := fun p : (Word × Word) × ℕ => (p.1.1,p.2)) (by fun_prop)
       have htar := ht.comp (encIn := encPair (encPair encBits encBits) encUnary) (g := fun p : (Word × Word) × ℕ => p.1.1) (by fun_prop)
       simpa only [Function.comp_def,decide_not] using
         ComputableTidilyInPolyTime.bool_not.comp (hcoord.decide_eq' htar)
     · exact ComputableTidilyInPolyTime.bool_not.comp hcov

 theorem zeros_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (zeros W) encBits encBits := by
   apply (bits_encList_polyTime encBool).2.tidy.comp
   exact ComputableTidilyInPolyTime.replicate
     ((ComputableTidilyInPolyTime.unary_eval W.length).comp ComputableTidilyInPolyTime.length_bits)
     (ComputableTidilyInPolyTime.const false)
 theorem encodeReply_poly : ComputableTidilyInPolyTime encodeReply (encPair encUnary (encList encBits)) encBits := by
   have hi : ComputableTidilyInPolyTime (fun a : ℕ × List Word => List.replicate a.1 true)
       (encPair encUnary (encList encBits)) encBits :=
     (ComputableTidilyInPolyTime.encode encUnary).comp (ComputableTidilyInPolyTime.fst encUnary (encList encBits))
   unfold encodeReply
   apply TupleCodec.encode_poly.comp
   exact hi.cons' ((TupleCodec.encode_poly.comp (ComputableTidilyInPolyTime.snd encUnary (encList encBits))).cons'
     (ComputableTidilyInPolyTime.const []))
 theorem reply_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (fun p : Word × ℕ => reply W p.1 p.2)
       (encPair encBits encUnary) encBits := by
   have hc := coordinate_poly
   have hw := witness_poly
   have hz := zeros_poly W
   have hvalues : ComputableTidilyInPolyTime (fun p : Word × ℕ =>
       (List.range (inputs p.1).length).map fun h => if h=p.2 then witness p.1 (coordinate p.1 p.2) else zeros W (coordinate p.1 h))
       (encPair encBits encUnary) (encList encBits) := by
     apply ComputableTidilyInPolyTime.mapWithInput
     · apply ComputableTidilyInPolyTime.range.comp
       exact ((ComputableTidilyInPolyTime.length_list encBits).comp inputs_poly).comp (ComputableTidilyInPolyTime.fst encBits encUnary)
     · apply ComputableTidilyInPolyTime.ite_decide
       · fun_prop
       · apply hw.comp (g := fun p : (Word × ℕ) × ℕ => (p.1.1,coordinate p.1.1 p.1.2))
         apply ComputableTidilyInPolyTime.prod
         · fun_prop
         · exact hc.comp (ComputableTidilyInPolyTime.fst (encPair encBits encUnary) encUnary)
       · apply hz.comp
         exact hc.comp (g := fun p : (Word × ℕ) × ℕ => (p.1.1,p.2)) (by fun_prop)
   unfold reply
   exact encodeReply_poly.comp ((ComputableTidilyInPolyTime.snd encBits encUnary).prod hvalues)
 theorem post_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (post W) (encPair encBits encBits) encBits := by
   have hr := reply_poly W
   unfold post
   apply ComputableTidilyInPolyTime.optionElimWithInput (chooseIndex_poly W) (ComputableTidilyInPolyTime.const (tup []))
   apply TupleCodec.encode_poly.comp
   apply ComputableTidilyInPolyTime.cons'
   · exact hr.comp (g := fun p : (Word × Word) × ℕ => (p.1.1,p.2)) (by fun_prop)
   · exact ComputableTidilyInPolyTime.const []

 def encodeOption (o : Option TupleReply) : Word := o.elim (tup []) (fun z => tup [encodeReply z])
 noncomputable def expectedIndex {i : ℕ} {L : Language} (W : WitnessPresentation i L) (s : Word) : Option ℕ := by
   classical
   exact (List.range (inputs s).length).find? (fun j => decide
     (coordinate s j ≠ target s ∧ ¬ ∃ Y ∈ guesses s, ValidWitness W (coordinate s j) (Y.getD j [])))
 theorem chooseIndex_correct (M : OTM) (O : Oracle) (p : Polynomial ℕ)
     {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (hW : ∀ a b, NativeBatch.result M O p (tup [a,b])=true ↔ W.test a b) (s : Word) :
     chooseIndex W s (NativeBatch.scores M O p (prep s)) = expectedIndex W s := by
   classical
   have he : NativeBatch.scores M O p (prep s) =
       (List.range (inputs s).length).flatMap (fun j => (pool s j).map fun w => NativeBatch.result M O p (tup [coordinate s j,w])) := by
     simp [NativeBatch.scores,prep,List.map_flatMap,List.map_map,Function.comp_def]
   unfold chooseIndex expectedIndex
   rw [he]
   apply List.find?_congr
   intro j hj
   have hjl : j < (inputs s).length := List.mem_range.mp hj
   have hh := NormalizationData.chunk_flatMap (List.range (inputs s).length) 0
     (fun j => (pool s j).map fun w => NativeBatch.result M O p (tup [coordinate s j,w])) (count s) j
     (by simpa using hjl) (by intro a ha; simp [pool,count])
   rw [List.getD_eq_getElem _ _ (by simpa using hjl),List.getElem_range] at hh
   rw [hh]
   apply Bool.eq_iff_iff.mpr
   have hcov : covered W (coordinate s j) (pool s j)
       ((pool s j).map fun w => NativeBatch.result M O p (tup [coordinate s j,w]))=true ↔
       ∃ Y ∈ guesses s, ValidWitness W (coordinate s j) (Y.getD j []) := by
     simpa [pool] using covered_correct W (coordinate s j) (pool s j)
       (fun w => NativeBatch.result M O p (tup [coordinate s j,w])) (hW (coordinate s j))
   simp only [List.getD_eq_getElem?_getD] at hcov
   by_cases hcv : covered W (coordinate s j) (pool s j)
       ((pool s j).map fun w => NativeBatch.result M O p (tup [coordinate s j,w]))=true
   · simp [hcv,hcov.mp hcv]
   · have hb := Bool.eq_false_iff.mpr hcv
     have hn : ¬ ∃ Y ∈ guesses s, ValidWitness W (coordinate s j) (Y[j]?.getD []) := fun h => hcv (hcov.mpr h)
     simp [hb,hn]

 theorem post_correct (M : OTM) (O : Oracle) (p : Polynomial ℕ)
     {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (hW : ∀ a b, NativeBatch.result M O p (tup [a,b])=true ↔ W.test a b) (s : Word) :
     post W (s,NativeBatch.scores M O p (prep s)) = encodeOption
       (AdviceSemantic.knownTeacher W (inputs s) (target s) (witness s) (guesses s)) := by
   classical
   unfold post
   rw [chooseIndex_correct M O p W hW s]
   unfold AdviceSemantic.knownTeacher expectedIndex
   change _ = encodeOption (Option.map _ _)
   dsimp only [Prod.fst,Prod.snd]
   unfold coordinate
   generalize (List.range (inputs s).length).find? (fun j => decide
     ((inputs s).getD j [] ≠ target s ∧ ¬ ∃ Y ∈ guesses s, ValidWitness W ((inputs s).getD j []) (Y.getD j []))) = found
   cases found with
   | none => rfl
   | some j => rfl

 def encodeInput (X : List Word) (x : Word) (G : List (List Word)) (D : List (Word × Word)) : Word :=
   tup [tup X,x,tup (G.map tup),tup (D.map fun p => tup [p.1,p.2])]
 theorem inputs_encoded (X : List Word) (x : Word) (G : List (List Word)) (D : List (Word × Word)) :
     inputs (encodeInput X x G D)=X := by simp [inputs,field,encodeInput,TupleCodec.decode_tup]
 theorem target_encoded (X : List Word) (x : Word) (G : List (List Word)) (D : List (Word × Word)) :
     target (encodeInput X x G D)=x := by simp [target,field,encodeInput,TupleCodec.decode_tup]
 theorem guesses_encoded (X : List Word) (x : Word) (G : List (List Word)) (D : List (Word × Word)) :
     guesses (encodeInput X x G D)=G := by simp [guesses,field,encodeInput,TupleCodec.decode_tup,List.map_map,Function.comp_def]
 theorem dictionary_encoded (X : List Word) (x : Word) (G : List (List Word)) (D : List (Word × Word)) :
     dictionary (encodeInput X x G D)=D.map (fun p => tup [p.1,p.2]) := by simp [dictionary,field,encodeInput,TupleCodec.decode_tup]
 theorem key_encoded (a b : Word) : key (tup [a,b])=a := by simp [key,TupleCodec.decode_tup]
 theorem value_encoded (a b : Word) : value (tup [a,b])=b := by simp [value,TupleCodec.decode_tup]
 theorem witness_encoded (X : List Word) (x : Word) (G : List (List Word))
     (keys : List Word) (wit : Word → Word) (a : Word) (ha : a ∈ keys) :
     witness (encodeInput X x G (keys.map fun a => (a,wit a))) a=wit a := by
   have hex : ((dictionary (encodeInput X x G (keys.map fun a => (a,wit a)))).find? (fun e => key e == a)).isSome := by
     rw [dictionary_encoded]
     apply List.find?_isSome.mpr
     refine ⟨tup [a,wit a],?_,?_⟩
     · exact List.mem_map.mpr ⟨(a,wit a),List.mem_map.mpr ⟨a,ha,rfl⟩,rfl⟩
     · simp [key_encoded]
   obtain ⟨entry,hentry⟩ := Option.isSome_iff_exists.mp hex
   have hm := List.mem_of_find?_eq_some hentry
   rw [dictionary_encoded] at hm
   obtain ⟨pair,hpair,rfl⟩ := List.mem_map.mp hm
   obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hpair
   have he : b=a := by simpa only [key_encoded,beq_iff_eq] using List.find?_some hentry
   subst b
   unfold witness
   rw [hentry]
   exact value_encoded _ _

 def targetIndex (s : Word) : ℕ := (inputs s).idxOf (target s)
 def accepts {i : ℕ} {L : Language} (W : WitnessPresentation i L) (s bits : Word) : Bool :=
   decide (targetIndex s < (inputs s).length) && decide (coordinate s (targetIndex s)=target s) &&
     covered W (target s) (pool s (targetIndex s)) ((bits.drop (targetIndex s*count s)).take (count s))
 def withAcceptance {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word × Word) : Word :=
   tup [[accepts W a.1 a.2],post W a]
 theorem targetIndex_poly : ComputableTidilyInPolyTime targetIndex encBits encUnary := by
   change ComputableTidilyInPolyTime (fun s : Word => targetIndex s) encBits encUnary
   have hi := (ComputableTidilyInPolyTime.idxOf encBits).comp (inputs_poly.prod target_poly)
   have hbeq (a b : Word) : @BEq.beq Word (@instBEqOfDecidableEq Word inferInstance) a b = (a == b) := by
     apply Bool.eq_iff_iff.mpr
     simp only [beq_iff_eq]
   simpa only [targetIndex,Function.comp_def,List.idxOf,hbeq] using hi
 theorem accepts_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (fun a : Word × Word => accepts W a.1 a.2) (encPair encBits encBits) encBool := by
   have hi := targetIndex_poly
   have hp := pool_poly
   have hc := coordinate_poly
   have ht := target_poly
   have hlen := (ComputableTidilyInPolyTime.length_list encBits).comp inputs_poly
   have hn := count_poly
   have hpool : ComputableTidilyInPolyTime (fun s : Word => pool s (targetIndex s)) encBits (encList encBits) :=
     hp.comp (ComputableTidilyInPolyTime.id'.prod hi)
   have hcoord : ComputableTidilyInPolyTime (fun s : Word => coordinate s (targetIndex s)) encBits encBits :=
     hc.comp (ComputableTidilyInPolyTime.id'.prod hi)
   have hcov : ComputableTidilyInPolyTime (fun a : Word × Word =>
       covered W (target a.1) (pool a.1 (targetIndex a.1))
         ((a.2.drop (targetIndex a.1*count a.1)).take (count a.1))) (encPair encBits encBits) encBool := by
     apply (covered_poly W).comp (g := fun a : Word × Word =>
       (target a.1,pool a.1 (targetIndex a.1),(a.2.drop (targetIndex a.1*count a.1)).take (count a.1)))
     apply ComputableTidilyInPolyTime.prod
     · exact ht.comp (ComputableTidilyInPolyTime.fst encBits encBits)
     · apply ComputableTidilyInPolyTime.prod
       · exact hpool.comp (ComputableTidilyInPolyTime.fst encBits encBits)
       · fun_prop
   unfold accepts
   apply ComputableTidilyInPolyTime.bool_and'
   · apply ComputableTidilyInPolyTime.bool_and'
     · exact (ComputableTidilyInPolyTime.unary_lt.comp (hi.prod hlen)).comp (ComputableTidilyInPolyTime.fst encBits encBits)
     · exact (hcoord.decide_eq' ht).comp (ComputableTidilyInPolyTime.fst encBits encBits)
   · exact hcov
 theorem withAcceptance_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (withAcceptance W) (encPair encBits encBits) encBits := by
   unfold withAcceptance
   apply TupleCodec.encode_poly.comp
   exact ((accepts_poly W).bitsCons (ComputableTidilyInPolyTime.const [])).cons'
     ((post_poly W).cons' (ComputableTidilyInPolyTime.const []))

 theorem scores_at (M : OTM) (O : Oracle) (p : Polynomial ℕ) (s : Word) (j : ℕ) (hj : j < (inputs s).length) :
     ((NativeBatch.scores M O p (prep s)).drop (j*count s)).take (count s) =
       (pool s j).map (fun w => NativeBatch.result M O p (tup [coordinate s j,w])) := by
   have he : NativeBatch.scores M O p (prep s) =
       (List.range (inputs s).length).flatMap (fun j => (pool s j).map fun w => NativeBatch.result M O p (tup [coordinate s j,w])) := by
     simp [NativeBatch.scores,prep,List.map_flatMap,List.map_map,Function.comp_def]
   rw [he]
   have hh := NormalizationData.chunk_flatMap (List.range (inputs s).length) 0
     (fun j => (pool s j).map fun w => NativeBatch.result M O p (tup [coordinate s j,w])) (count s) j
     (by simpa using hj) (by intro a ha; simp [pool,count])
   rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_range] at hh
   exact hh
 theorem accepts_iff (M : OTM) (O : Oracle) (p : Polynomial ℕ)
     {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (hW : ∀ a b, NativeBatch.result M O p (tup [a,b])=true ↔ W.test a b) (s : Word)
     (hmem : target s ∈ inputs s) :
     accepts W s (NativeBatch.scores M O p (prep s))=true ↔
       ∃ Y ∈ guesses s, ValidWitness W (target s) (Y.getD (targetIndex s) []) := by
   have hj : targetIndex s < (inputs s).length := List.idxOf_lt_length_iff.mpr hmem
   have hc : coordinate s (targetIndex s)=target s := by
     unfold coordinate targetIndex
     rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.mpr hmem)]
     exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hmem)
   unfold accepts
   rw [scores_at M O p s (targetIndex s) hj,hc]
   simp only [hj,hc,decide_true,Bool.true_and]
   simpa [pool] using covered_correct W (target s) (pool s (targetIndex s))
     (fun w => NativeBatch.result M O p (tup [target s,w])) (hW (target s))
 theorem accepts_sound (M : OTM) (O : Oracle) (p : Polynomial ℕ)
     {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (hW : ∀ a b, NativeBatch.result M O p (tup [a,b])=true ↔ W.test a b) (s : Word)
     (h : accepts W s (NativeBatch.scores M O p (prep s))=true) : target s ∈ L := by
   have hj : targetIndex s < (inputs s).length := by
     exact of_decide_eq_true ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1)
   have hm : target s ∈ inputs s := List.idxOf_lt_length_iff.mp hj
   obtain ⟨Y,hY,hlen,hvalid⟩ := (accepts_iff M O p W hW s hm).mp h
   exact (W.represents (target s)).mpr ⟨_,hlen,hvalid⟩

 def dictWitness (D : List (Word × Word)) (a : Word) : Word :=
   ((D.find? fun p => p.1 == a).map Prod.snd).getD []
 theorem witness_dict (X : List Word) (x : Word) (G : List (List Word)) (D : List (Word × Word)) (a : Word) :
     witness (encodeInput X x G D) a=dictWitness D a := by
   unfold witness dictWitness
   rw [dictionary_encoded,List.find?_map]
   simp only [Function.comp_def,key_encoded]
   cases hh : D.find? (fun p => p.1 == a) with
   | none => rfl
   | some p => exact value_encoded _ _

end StudentTeacher976.Adaptivity.AdviceTeacherData
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity
open QAdvFew.PoQOracle

 theorem witness_machine (i : ℕ) (L : Language) (W : WitnessPresentation i L) :
     ∃ (O : Oracle) (M : OTM) (p : Polynomial ℕ), {x | O x=true} ∈ Sigma i ∧
       (∀ w : Word, 0 < p.eval w.length) ∧
       ∀ a b, NativeBatch.result M O p (tup [a,b])=true ↔ W.test a b := by
   obtain ⟨O,M,p,hO,htotal,hW⟩ := W.efficient
   refine ⟨O,M,p,hO,?_,?_⟩
   · intro w
     have ht := htotal w
     by_contra hn
     have hz : p.eval w.length=0 := by omega
     rw [hz] at ht
     norm_num [OTM.result,OTM.runCfg,OTM.init,Fin.ext_iff,Nat.mod_eq_of_lt (show 2 < M.k+6 by omega)] at ht
   · intro a b
     rw [NativeBatch.result,getD_true_iff,← hW]
     constructor
     · rintro ⟨u,v,he,huv⟩
       have hh := congrArg TupleCodec.decodeTuple he
       simp only [TupleCodec.decode_tup,List.cons.injEq,and_true] at hh
       obtain ⟨rfl,rfl⟩ := hh
       exact huv
     · exact fun h => ⟨a,b,rfl,h⟩

end StudentTeacher976.Adaptivity
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceTeacherData
open QAdvFew.PoQOracle Turing.MultiTapeTM

 theorem uniform (i : ℕ) (L : Language) (W : WitnessPresentation i L) :
     ∃ F : Word → Word, InFP i F ∧ ∀ s : Word,
       F s=encodeOption (AdviceSemantic.knownTeacher W (inputs s) (target s) (witness s) (guesses s)) := by
   obtain ⟨O,M,p,hO,hpos,hW⟩ := witness_machine i L W
   let F := fun s => post W (s,NativeBatch.scores M O p (prep s))
   obtain ⟨C,hC,T,B,htrace⟩ := NativeBatch.protocol M p hpos prep (post W) prep_poly (post_poly W)
   have hF : OracleComputations.Computes O F := OracleComputations.of_protocol C hC.tidy O F T B (htrace O)
   exact ⟨F,(OracleComputations.inFP_iff i F).mpr ⟨O,hO,hF⟩,post_correct M O p W hW⟩

 theorem uniform_with_acceptance (i : ℕ) (L : Language) (W : WitnessPresentation i L) :
     ∃ F : Word → Word, InFP i F ∧ ∀ s : Word,
       field (F s) 1=encodeOption (AdviceSemantic.knownTeacher W (inputs s) (target s) (witness s) (guesses s)) ∧
       ((field (F s) 0).headD false=true → target s ∈ L) ∧
       (target s ∈ inputs s → ((field (F s) 0).headD false=true ↔
         ∃ Y ∈ guesses s, ValidWitness W (target s) (Y.getD (targetIndex s) []))) := by
   obtain ⟨O,M,p,hO,hpos,hW⟩ := witness_machine i L W
   let F := fun s => withAcceptance W (s,NativeBatch.scores M O p (prep s))
   obtain ⟨C,hC,T,B,htrace⟩ := NativeBatch.protocol M p hpos prep (withAcceptance W) prep_poly (withAcceptance_poly W)
   have hF : OracleComputations.Computes O F := OracleComputations.of_protocol C hC.tidy O F T B (htrace O)
   refine ⟨F,(OracleComputations.inFP_iff i F).mpr ⟨O,hO,hF⟩,?_⟩
   intro s
   have hr : field (F s) 1=post W (s,NativeBatch.scores M O p (prep s)) := by
     simp [F,withAcceptance,field,TupleCodec.decode_tup]
   have ha : (field (F s) 0).headD false=accepts W s (NativeBatch.scores M O p (prep s)) := by
     simp [F,withAcceptance,field,TupleCodec.decode_tup]
   refine ⟨hr.trans (post_correct M O p W hW s),?_,?_⟩
   · rw [ha]
     exact accepts_sound M O p W hW s
   · intro hm
     rw [ha]
     exact accepts_iff M O p W hW s hm

 theorem uniform_structured (i : ℕ) (L : Language) (W : WitnessPresentation i L) :
     ∃ (F : Word → Word) (flag : Word → Bool), InFP i F ∧ ∀ s : Word,
       F s=tup [[flag s],encodeOption (AdviceSemantic.knownTeacher W (inputs s) (target s) (witness s) (guesses s))] ∧
       (flag s=true → target s ∈ L) ∧
       (target s ∈ inputs s → (flag s=true ↔
         ∃ Y ∈ guesses s, ValidWitness W (target s) (Y.getD (targetIndex s) []))) := by
   obtain ⟨O,M,p,hO,hpos,hW⟩ := witness_machine i L W
   let flag := fun s => accepts W s (NativeBatch.scores M O p (prep s))
   let F := fun s => withAcceptance W (s,NativeBatch.scores M O p (prep s))
   obtain ⟨C,hC,T,B,htrace⟩ := NativeBatch.protocol M p hpos prep (withAcceptance W) prep_poly (withAcceptance_poly W)
   have hF : OracleComputations.Computes O F := OracleComputations.of_protocol C hC.tidy O F T B (htrace O)
   refine ⟨F,flag,(OracleComputations.inFP_iff i F).mpr ⟨O,hO,hF⟩,?_⟩
   intro s
   refine ⟨?_,accepts_sound M O p W hW s,accepts_iff M O p W hW s⟩
   unfold F withAcceptance
   rw [post_correct M O p W hW s]

end StudentTeacher976.Adaptivity.AdviceTeacherData
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeIteration
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 abbrev State (M : OTM) := ℕ × NativeCPU.State M
 def stateEnc (M : OTM) : State M ↪ Word := encPair encUnary (NativeCPU.stateEnc M)
 noncomputable def decoder (M : OTM) : Decoder (stateEnc M) := Decoder.unary.pair (NativeCPU.stateDecoder M)
 def emit (M : OTM) (st : State M) : Word :=
   OracleDriver.record false false (NativeCPU.queryBody M st.2.2.1 st.2.2.2) (stateEnc M st)
 def begin (M : OTM) (p : Polynomial ℕ) (k : ℕ) (w : Word) : Word :=
   if k=0 then OracleDriver.record true false [] w else emit M (k-1,NativeCPU.initialState M p w)
 def advanceResponse (M : OTM) (p : Polynomial ℕ) (answer : Bool) (st : State M) : Word :=
   let native := NativeCPU.advanceState M answer st.2
   if native.1=0 then begin M p st.1 (NativeCPU.outputBody M false native.2.1 native.2.2)
   else emit M (st.1,native)
 noncomputable def cpu (M : OTM) (p : Polynomial ℕ) (prep : Word → ℕ × Word) (w : Word) : Word :=
   if w.headD false then advanceResponse M p (w.getD 2 false) ((decoder M).decode (NativeCPU.parseStateWord w))
   else if (w.drop 1).headD false then NativeCPU.parseStateWord w
   else let a := prep (w.drop 2); begin M p a.1 a.2
 theorem cpu_initial (M : OTM) (p : Polynomial ℕ) (prep : Word → ℕ × Word) (x : Word) :
     cpu M p prep (OracleDriver.shifted x) = begin M p (prep x).1 (prep x).2 := by simp [cpu,OracleDriver.shifted]
 theorem cpu_continue (M : OTM) (p : Polynomial ℕ) (prep : Word → ℕ × Word) (answer : Bool) (q : Word) (st : State M) :
     cpu M p prep (OracleDriver.record false answer q (stateEnc M st)) = advanceResponse M p answer st := by
   simp [cpu,OracleDriver.record,NativeCPU.parseStateWord,NativeCPU.frames_two,Decoder.decode_enc]
 theorem cpu_final (M : OTM) (p : Polynomial ℕ) (prep : Word → ℕ × Word) (answer : Bool) (q out : Word) :
     cpu M p prep (OracleDriver.finalRecord answer q out) = out := by
   simp [cpu,OracleDriver.finalRecord,NativeCPU.parseStateWord,NativeCPU.frames_two]
 theorem emit_poly (M : OTM) : ComputableTidilyInPolyTime (emit M) (stateEnc M) encBits := by
   have hq := (NativeCPU.queryBody_poly M).comp (encIn := stateEnc M)
     (g := fun st : State M => (st.2.2.1,st.2.2.2)) (by unfold stateEnc NativeCPU.stateEnc; fun_prop)
   have hs := ComputableTidilyInPolyTime.encode (stateEnc M)
   exact NativeCPU.record_poly.comp
     ((ComputableTidilyInPolyTime.const false).prod ((ComputableTidilyInPolyTime.const false).prod (hq.prod hs)))
 theorem begin_poly (M : OTM) (p : Polynomial ℕ) :
     ComputableTidilyInPolyTime (fun a : ℕ × Word => begin M p a.1 a.2) (encPair encUnary encBits) encBits := by
   have he := emit_poly M
   have hi := NativeCPU.initialState_poly M p
   unfold begin
   apply ComputableTidilyInPolyTime.ite_decide
   · fun_prop
   · apply NativeCPU.record_poly.comp (g := fun a : ℕ × Word => (true,false,[],a.2))
     fun_prop
   · apply he.comp (g := fun a : ℕ × Word => (a.1-1,NativeCPU.initialState M p a.2))
     unfold stateEnc
     fun_prop
 theorem advanceResponse_poly (M : OTM) (p : Polynomial ℕ) :
     ComputableTidilyInPolyTime (fun a : Bool × State M => advanceResponse M p a.1 a.2)
       (encPair encBool (stateEnc M)) encBits := by
   have hn := (NativeCPU.advanceState_poly M).comp (encIn := encPair encBool (stateEnc M))
     (g := fun a : Bool × State M => (a.1,a.2.2)) (by unfold stateEnc; fun_prop)
   have hc : ComputableTidilyInPolyTime (fun a : Bool × State M => (NativeCPU.advanceState M a.1 a.2.2).1)
       (encPair encBool (stateEnc M)) encUnary := by
     unfold NativeCPU.stateEnc at hn
     exact hn.fst'
   have ho := (NativeCPU.outputBody_poly M false).comp (encIn := encPair encBool (stateEnc M))
     (g := fun a : Bool × State M => (NativeCPU.advanceState M a.1 a.2.2).2) hn.snd'
   have hb := begin_poly M p
   have he := emit_poly M
   unfold advanceResponse
   apply ComputableTidilyInPolyTime.ite_decide
   · exact hc.decide_eq' (ComputableTidilyInPolyTime.const 0)
   · apply hb.comp (g := fun a : Bool × State M => (a.2.1,NativeCPU.outputBody M false (NativeCPU.advanceState M a.1 a.2.2).2.1 (NativeCPU.advanceState M a.1 a.2.2).2.2))
     apply ComputableTidilyInPolyTime.prod
     · unfold stateEnc; fun_prop
     · exact ho
   · apply he.comp (g := fun a : Bool × State M => (a.2.1,NativeCPU.advanceState M a.1 a.2.2))
     unfold stateEnc
     apply ComputableTidilyInPolyTime.prod
     · fun_prop
     · exact hn
 theorem cpu_poly (M : OTM) (p : Polynomial ℕ) (prep : Word → ℕ × Word)
     (hp : ComputableTidilyInPolyTime prep encBits (encPair encUnary encBits)) :
     ComputableTidilyInPolyTime (cpu M p prep) encBits encBits := by
   have hd := (decoder M).computableInPolyTime.tidy.comp NativeCPU.parseStateWord_poly
   have ha := advanceResponse_poly M p
   have hb := begin_poly M p
   unfold cpu
   apply ComputableTidilyInPolyTime.cond
   · fun_prop
   · apply ha.comp (g := fun w : Word => (w.getD 2 false,(decoder M).decode (NativeCPU.parseStateWord w)))
     fun_prop
   · apply ComputableTidilyInPolyTime.cond
     · fun_prop
     · exact NativeCPU.parseStateWord_poly
     · apply hb.comp
       fun_prop

end StudentTeacher976.Adaptivity.NativeIteration
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeIteration
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 def limit (M : OTM) (p : Polynomial ℕ) (L : ℕ) : ℕ := 20*L+1000*(M.k+M.g+10)*(L+p.eval L+2)+20
 theorem state_size (M : OTM) (O : Oracle) (p : Polynomial ℕ) (L k : ℕ) (w : Word) (t : ℕ)
     (hk : k ≤ L) (hw : w.length ≤ L) (ht : t ≤ p.eval w.length) :
     (stateEnc M (k,NativeCPU.runtimeState M O w (p.eval w.length) t)).length ≤
       2*L+1+200*(M.k+M.g+10)*(L+p.eval L+2) := by
   have hs := NativeCPU.runtime_state_size M O w (p.eval w.length) t ht
   have hm := NativeBatch.polyEvalMono p hw
   have hlarge : (NativeCPU.stateEnc M (NativeCPU.runtimeState M O w (p.eval w.length) t)).length ≤
       200*(M.k+M.g+10)*(L+p.eval L+2) := hs.trans (Nat.mul_le_mul_left _ (by omega))
   simp only [stateEnc,encPair_apply,List.length_append,length_frame,encUnary_apply,List.length_replicate]
   omega
 theorem record_size (M : OTM) (O : Oracle) (p : Polynomial ℕ) (L k : ℕ) (w : Word) (t : ℕ) (done answer : Bool)
     (hk : k ≤ L) (hw : w.length ≤ L) (ht : t ≤ p.eval w.length) :
     let native := NativeCPU.runtimeState M O w (p.eval w.length) t;
     (OracleDriver.record done answer (NativeCPU.queryBody M native.2.1 native.2.2) (stateEnc M (k,native))).length ≤ limit M p L := by
   have hs := state_size M O p L k w t hk hw ht
   have hq := NativeCPU.runtime_query_size M O w (p.eval w.length) t
   have hm := NativeBatch.polyEvalMono p hw
   dsimp only [NativeCPU.runtimeState] at *
   simp only [OracleDriver.record,List.length_cons,List.length_append,length_frame]
   unfold limit
   nlinarith
 theorem done_size (M : OTM) (p : Polynomial ℕ) (L : ℕ) (w : Word) (hw : w.length ≤ L) :
     (OracleDriver.record true false [] w).length ≤ limit M p L := by
   simp only [OracleDriver.record,List.length_cons,List.length_append,length_frame,List.length_nil,Nat.mul_zero,Nat.zero_add]
   unfold limit
   omega

end StudentTeacher976.Adaptivity.NativeIteration
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeIteration
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 def cost (p : Polynomial ℕ) (f : Word → Word) : ℕ → Word → ℕ
   | 0, _ => 0
   | k+1,w => p.eval w.length+cost p f k (f w)
 theorem after_current (M : OTM) (O : Oracle) (p : Polynomial ℕ) (f : Word → Word)
     (hf : ∀ w : Word, M.output O w (p.eval w.length)=f w) (k : ℕ) (w : Word) (t : ℕ) (ht : t < p.eval w.length) :
     let native := NativeCPU.runtimeState M O w (p.eval w.length) t;
     advanceResponse M p (O (NativeCPU.queryBody M native.2.1 native.2.2)) (k,native) =
       if t+1=p.eval w.length then begin M p k (f w)
       else emit M (k,NativeCPU.runtimeState M O w (p.eval w.length) (t+1)) := by
   dsimp only
   have hadv : NativeCPU.advanceState M
       (O (NativeCPU.queryBody M (NativeCPU.runtimeState M O w (p.eval w.length) t).2.1
         (NativeCPU.runtimeState M O w (p.eval w.length) t).2.2))
       (NativeCPU.runtimeState M O w (p.eval w.length) t) = NativeCPU.runtimeState M O w (p.eval w.length) (t+1) :=
     NativeCPU.runtime_advance M O w _ t ht
   simp only [advanceResponse,hadv]
   by_cases he : t+1=p.eval w.length
   · have hz : (NativeCPU.runtimeState M O w (p.eval w.length) (t+1)).1=0 := by simp [he,NativeCPU.runtimeState]
     rw [if_pos hz,if_pos he,he]
     apply congrArg (begin M p k)
     exact (NativeCPU.runtime_output M O w (p.eval w.length) false).trans (hf w)
   · have hz : (NativeCPU.runtimeState M O w (p.eval w.length) (t+1)).1≠0 := by dsimp [NativeCPU.runtimeState]; omega
     rw [if_neg hz,if_neg he]

 theorem loop_trace (M : OTM) (O : Oracle) (p : Polynomial ℕ) (f : Word → Word)
     (hf : ∀ w : Word, M.output O w (p.eval w.length)=f w)
     (hpos : ∀ w : Word, 0 < p.eval w.length) (prep : Word → ℕ × Word) (L k : ℕ) (w input : Word)
     (hk : k ≤ L) (horbit : ∀ j ≤ k, (f^[j] w).length ≤ L)
     (hinput : input.length ≤ limit M p L) (hcpu : cpu M p prep input=begin M p k w) :
     OracleDriver.Trace (cpu M p prep) O (limit M p L) input (f^[k] w) (cost p f k w) := by
   induction k generalizing w input with
   | zero =>
     have hw : w.length ≤ L := by simpa using horbit 0 (by omega)
     have hc : cpu M p prep input = OracleDriver.record true false [] w := by simpa only [begin,↓reduceIte] using hcpu
     exact OracleDriver.Trace.done input false [] w w hinput (done_size M p L w hw) hc (cpu_final M p prep false [] w)
   | succ k ih =>
     have hw : w.length ≤ L := by simpa using horbit 0 (by omega)
     have htail : ∀ j ≤ k, (f^[j] (f w)).length ≤ L := by
       intro j hj
       simpa only [Function.iterate_succ_apply] using horbit (j+1) (by omega)
     let T := p.eval w.length
     let out := f^[k] (f w)
     have current : ∀ m t : ℕ, m+t=T → 0 < m → ∀ input : Word,
         input.length ≤ limit M p L →
         cpu M p prep input=emit M (k,NativeCPU.runtimeState M O w T t) →
         OracleDriver.Trace (cpu M p prep) O (limit M p L) input out (m+cost p f k (f w)) := by
       intro m
       induction m with
       | zero => intro t ht hm; omega
       | succ m ihm =>
         intro t ht hm input hinput hcpu
         have ht' : t<T := by omega
         let native := NativeCPU.runtimeState M O w T t
         let query := NativeCPU.queryBody M native.2.1 native.2.2
         let code := stateEnc M (k,native)
         have hr : cpu M p prep input=OracleDriver.record false false query code := hcpu
         have hsize := record_size M O p L k w t false false (by omega) hw (by omega)
         have hreply := record_size M O p L k w t false (O query) (by omega) hw (by omega)
         have hc := cpu_continue M p prep (O query) query (k,native)
         rw [after_current M O p f hf k w t ht'] at hc
         have hnext : OracleDriver.Trace (cpu M p prep) O (limit M p L)
             (OracleDriver.record false (O query) query code) out (m+cost p f k (f w)) := by
           by_cases hm0 : m=0
           · subst m
             have he : t+1=T := by omega
             rw [if_pos he] at hc
             simpa only [Nat.zero_add,out] using ih (f w) _ (by omega) htail hreply hc
           · have he : t+1≠T := by omega
             rw [if_neg he] at hc
             exact ihm (t+1) (by omega) (by omega) _ hreply hc
         have hnode := OracleDriver.Trace.query input false query code out (m+cost p f k (f w)) hinput hsize hr hnext
         convert hnode using 1 <;> omega
     have hstart : cpu M p prep input=emit M (k,NativeCPU.runtimeState M O w T 0) := by
       rw [hcpu]
       simp only [begin,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,Nat.add_sub_cancel]
       rw [NativeCPU.runtime_initial M O p w]
     have ht := current T 0 (by omega) (hpos w) input hinput hstart
     simpa only [cost,out,Function.iterate_succ_apply] using ht

 theorem cost_bound (p : Polynomial ℕ) (f : Word → Word) (L k : ℕ) (w : Word)
     (horbit : ∀ j ≤ k, (f^[j] w).length ≤ L) : cost p f k w ≤ k*p.eval L := by
   induction k generalizing w with
   | zero => simp [cost]
   | succ k ih =>
     have hw : w.length ≤ L := by simpa using horbit 0 (by omega)
     have hm := NativeBatch.polyEvalMono p hw
     have htail : ∀ j ≤ k, (f^[j] (f w)).length ≤ L := by
       intro j hj
       simpa only [Function.iterate_succ_apply] using horbit (j+1) (by omega)
     have hc := ih (f w) htail
     simp only [cost]
     nlinarith

end StudentTeacher976.Adaptivity.NativeIteration
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NativeIteration
open QAdvFew.PoQOracle Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 theorem protocol (M : OTM) (O : Oracle) (p : Polynomial ℕ) (f : Word → Word)
     (hf : ∀ w : Word, M.output O w (p.eval w.length)=f w) (hpos : ∀ w : Word, 0 < p.eval w.length)
     (prep : Word → ℕ × Word) (hp : ComputableTidilyInPolyTime prep encBits (encPair encUnary encBits))
     (B : Polynomial ℕ) (horbit : ∀ x : Word, ∀ j ≤ (prep x).1, (f^[j] (prep x).2).length ≤ B.eval x.length) :
     ∃ T S : Polynomial ℕ, ∀ x : Word, ∃ steps ≤ T.eval x.length,
       OracleDriver.Trace (cpu M p prep) O (S.eval x.length) (OracleDriver.shifted x)
         (f^[(prep x).1] (prep x).2) steps := by
   obtain ⟨Q,hQ⟩ := hp.polyBounded_length.exists_polynomial
   let len : Polynomial ℕ := Polynomial.X+Q+B+1
   let T := len*p.comp len
   let S := 20*len+1000*Polynomial.C (M.k+M.g+10)*(len+p.comp len+2)+20
   refine ⟨T,S,?_⟩
   intro x
   let L := len.eval x.length
   have hL : L = x.length+Q.eval x.length+B.eval x.length+1 := by simp [L,len]
   have hpair := hQ x
   simp only [encPair_apply,List.length_append,length_frame,encUnary_apply,List.length_replicate,encBits_apply] at hpair
   have hk : (prep x).1 ≤ L := by omega
   have ho : ∀ j ≤ (prep x).1, (f^[j] (prep x).2).length ≤ L := fun j hj => (horbit x j hj).trans (by omega)
   have hi : (OracleDriver.shifted x).length ≤ limit M p L := by
     simp only [OracleDriver.shifted,List.length_cons]
     unfold limit
     omega
   have ht := loop_trace M O p f hf hpos prep L (prep x).1 (prep x).2 (OracleDriver.shifted x)
     hk ho hi (cpu_initial M p prep x)
   have hcost := (cost_bound p f L (prep x).1 (prep x).2 ho).trans (Nat.mul_le_mul_right (p.eval L) hk)
   refine ⟨cost p f (prep x).1 (prep x).2,?_,?_⟩
   · simpa only [T,L,Polynomial.eval_mul,Polynomial.eval_comp] using hcost
   · have he : S.eval x.length=limit M p L := by simp [S,limit,L]
     rw [he]
     exact ht

 theorem computes (O : Oracle) (f : Word → Word) (hf : OracleComputations.Computes O f)
     (prep : Word → ℕ × Word) (hp : ComputableTidilyInPolyTime prep encBits (encPair encUnary encBits))
     (B : Polynomial ℕ) (horbit : ∀ x : Word, ∀ j ≤ (prep x).1, (f^[j] (prep x).2).length ≤ B.eval x.length) :
     OracleComputations.Computes O (fun x => f^[(prep x).1] (prep x).2) := by
   obtain ⟨M,p,hM⟩ := hf
   have hpos : ∀ w : Word, 0 < p.eval w.length := by
     intro w
     have ht := (hM w).1
     by_contra hn
     have hz : p.eval w.length=0 := by omega
     rw [hz] at ht
     norm_num [OTM.result,OTM.runCfg,OTM.init,Fin.ext_iff,Nat.mod_eq_of_lt (show 2 < M.k+6 by omega),
       Nat.mod_eq_of_lt (show 1 < M.k+6 by omega)] at ht
     cases ht
   obtain ⟨T,S,htrace⟩ := protocol M O p f (fun w => (hM w).2) hpos prep hp B horbit
   exact OracleComputations.of_protocol _ (cpu_poly M p prep hp) O _ T S htrace

 theorem inFP_iterate (i : ℕ) (f : Word → Word) (hf : InFP i f)
     (prep : Word → ℕ × Word) (hp : ComputableTidilyInPolyTime prep encBits (encPair encUnary encBits))
     (B : Polynomial ℕ) (horbit : ∀ x : Word, ∀ j ≤ (prep x).1, (f^[j] (prep x).2).length ≤ B.eval x.length) :
     InFP i (fun x => f^[(prep x).1] (prep x).2) := by
   obtain ⟨O,hO,hf⟩ := (OracleComputations.inFP_iff i f).mp hf
   exact (OracleComputations.inFP_iff i _).mpr ⟨O,hO,computes O f hf prep hp B horbit⟩

end StudentTeacher976.Adaptivity.NativeIteration
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceLoopData
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)

 def history (s : Word) : List Word := TupleCodec.decodeTuple (field s 5)
 def queries (s : Word) : ℕ := (field s 3).length
 def studentArgument (s : Word) : Word :=
   tup [field s 0,field s 4,tup ((history s).map fun z => tup (List.replicate (queries s) z))]
 def teacherArgument (v : Word) : Word :=
   let s := field v 0
   tup [field s 0,field s 1,field v 1,field s 2]
 def rebuild (s roundWord historyWord status : Word) : Word :=
   tup [field s 0,field s 1,field s 2,field s 3,roundWord,historyWord,status]
 def finish (u : Word) : Word :=
   let v := field u 0
   let s := field v 0
   let response := field u 1
   if !(field s 6).isEmpty then s
   else if (field response 0).headD false then rebuild s (field s 4) (field s 5) [true]
   else if (TupleCodec.decodeTuple (field response 1)).isEmpty then rebuild s (field s 4) (field s 5) [false]
   else rebuild s ((field s 4)++[true]) (tup ((history s)++[(TupleCodec.decodeTuple (field response 1)).headD []])) []
 def step (F T : Word → Word) (s : Word) : Word :=
   let v := tup [s,F (studentArgument s)]
   finish (tup [v,T (teacherArgument v)])

 theorem history_poly : ComputableTidilyInPolyTime history encBits (encList encBits) :=
   TupleCodec.decoder_poly.tidy.comp (field_poly 5)
 theorem queries_poly : ComputableTidilyInPolyTime queries encBits encUnary :=
   ComputableTidilyInPolyTime.length_bits.comp (field_poly 3)
 theorem studentArgument_poly : ComputableTidilyInPolyTime studentArgument encBits encBits := by
   have hq := queries_poly
   have hhist := history_poly
   have hinner : ComputableTidilyInPolyTime (fun p : Word × Word => tup (List.replicate (queries p.1) p.2))
       (encPair encBits encBits) encBits := by
     apply TupleCodec.encode_poly.comp
     exact ComputableTidilyInPolyTime.replicate
       (hq.comp (ComputableTidilyInPolyTime.fst encBits encBits)) (ComputableTidilyInPolyTime.snd encBits encBits)
   have hh := ComputableTidilyInPolyTime.mapWithInput (f := fun s z => tup (List.replicate (queries s) z)) hhist hinner
   unfold studentArgument
   exact TupleCodec.encode_poly.comp ((field_poly 0).cons' ((field_poly 4).cons'
     ((TupleCodec.encode_poly.comp hh).cons' (ComputableTidilyInPolyTime.const []))))
 theorem teacherArgument_poly : ComputableTidilyInPolyTime teacherArgument encBits encBits := by
   have h0 := field_poly 0
   have h1 := field_poly 1
   have h2 := field_poly 2
   unfold teacherArgument
   apply TupleCodec.encode_poly.comp
   fun_prop
 theorem rebuild_poly : ComputableTidilyInPolyTime (fun p : Word × Word × Word × Word => rebuild p.1 p.2.1 p.2.2.1 p.2.2.2)
     (encPair encBits (encPair encBits (encPair encBits encBits))) encBits := by
   have h0 := field_poly 0
   have h1 := field_poly 1
   have h2 := field_poly 2
   have h3 := field_poly 3
   unfold rebuild
   apply TupleCodec.encode_poly.comp
   fun_prop
 theorem finish_poly : ComputableTidilyInPolyTime finish encBits encBits := by
   have h0 := field_poly 0
   have h1 := field_poly 1
   have h4 := field_poly 4
   have h5 := field_poly 5
   have h6 := field_poly 6
   have hd := TupleCodec.decoder_poly.tidy
   have hh := history_poly
   have hr := rebuild_poly
   have htup := TupleCodec.encode_poly
   unfold finish
   apply ComputableTidilyInPolyTime.cond
   · fun_prop
   · fun_prop
   · apply ComputableTidilyInPolyTime.cond
     · fun_prop
     · apply hr.comp (g := fun u : Word =>
         (field (field u 0) 0,field (field (field u 0) 0) 4,field (field (field u 0) 0) 5,[true]))
       fun_prop
     · apply ComputableTidilyInPolyTime.cond
       · fun_prop
       · apply hr.comp (g := fun u : Word =>
           (field (field u 0) 0,field (field (field u 0) 0) 4,field (field (field u 0) 0) 5,[false]))
         fun_prop
       · apply hr.comp (g := fun u : Word =>
           (field (field u 0) 0,(field (field (field u 0) 0) 4)++[true],
             tup ((history (field (field u 0) 0))++[(TupleCodec.decodeTuple (field (field u 1) 1)).headD []]),[]))
         fun_prop

 theorem step_inFP (i : ℕ) (F T : Word → Word) (hF : InFP i F) (hT : InFP i T) : InFP i (step F T) := by
   have hcall := OracleComputations.inFP_compose i studentArgument F (pure_inFP i _ studentArgument_poly) hF
   have hretain := OracleComputations.inFP_retain i _ hcall
   have hteacher := OracleComputations.inFP_compose i teacherArgument T (pure_inFP i _ teacherArgument_poly) hT
   have htretain := OracleComputations.inFP_retain i _ hteacher
   have hboth := OracleComputations.inFP_compose i _ _ hretain htretain
   exact OracleComputations.inFP_post i _ finish hboth finish_poly

 def encodeState (X : List Word) (x : Word) (D : List (Word × Word)) (q t : ℕ) (Z : List TupleReply) (status : Word) : Word :=
   tup [tup X,x,tup (D.map fun p => tup [p.1,p.2]),List.replicate q true,List.replicate (t+1) true,tup (Z.map encodeReply),status]
 theorem studentArgument_encoded (X : List Word) (x : Word) (D : List (Word × Word)) (q t : ℕ) (Z : List TupleReply) (status : Word) :
     studentArgument (encodeState X x D q t Z status) = NormalizationData.studentInput X t (Z.map fun z => List.replicate q z) := by
   simp [studentArgument,encodeState,field,history,queries,NormalizationData.studentInput,TupleCodec.decode_tup,
     List.map_map,Function.comp_def,List.map_replicate]
 theorem teacherArgument_encoded (X : List Word) (x : Word) (D : List (Word × Word)) (q t : ℕ) (Z : List TupleReply)
     (status : Word) (G : List (List Word)) :
     teacherArgument (tup [encodeState X x D q t Z status,tup (G.map tup)]) = AdviceTeacherData.encodeInput X x G D := by
   simp [teacherArgument,encodeState,field,AdviceTeacherData.encodeInput,TupleCodec.decode_tup]

 theorem rebuild_encoded (X : List Word) (x : Word) (D : List (Word × Word)) (q t : ℕ) (Z : List TupleReply)
     (status r h st : Word) :
     rebuild (encodeState X x D q t Z status) r h st =
       tup [tup X,x,tup (D.map fun p => tup [p.1,p.2]),List.replicate q true,r,h,st] := by
   simp [rebuild,encodeState,field,TupleCodec.decode_tup]
 theorem finish_done (X : List Word) (x : Word) (D : List (Word × Word)) (q t : ℕ) (Z : List TupleReply)
     (status batch response : Word) (hs : status ≠ []) :
     finish (tup [tup [encodeState X x D q t Z status,batch],response]) = encodeState X x D q t Z status := by
   simp [finish,encodeState,field,TupleCodec.decode_tup,hs,List.isEmpty_iff]
 theorem finish_accept (X : List Word) (x : Word) (D : List (Word × Word)) (q t : ℕ) (Z : List TupleReply)
     (batch reply : Word) :
     finish (tup [tup [encodeState X x D q t Z [],batch],tup [[true],reply]]) = encodeState X x D q t Z [true] := by
   simp [finish,encodeState,rebuild,field,TupleCodec.decode_tup]
 theorem finish_reject (X : List Word) (x : Word) (D : List (Word × Word)) (q t : ℕ) (Z : List TupleReply)
     (batch : Word) :
     finish (tup [tup [encodeState X x D q t Z [],batch],tup [[false],AdviceTeacherData.encodeOption none]]) =
       encodeState X x D q t Z [false] := by
   simp [finish,encodeState,rebuild,field,TupleCodec.decode_tup,AdviceTeacherData.encodeOption]
 theorem finish_reply (X : List Word) (x : Word) (D : List (Word × Word)) (q t : ℕ) (Z : List TupleReply)
     (batch : Word) (z : TupleReply) :
     finish (tup [tup [encodeState X x D q t Z [],batch],tup [[false],AdviceTeacherData.encodeOption (some z)]]) =
       encodeState X x D q (t+1) (Z++[z]) [] := by
   simp [finish,encodeState,rebuild,field,history,TupleCodec.decode_tup,AdviceTeacherData.encodeOption,
     List.map_append,List.replicate_succ',List.append_assoc]

end StudentTeacher976.Adaptivity.AdviceLoopData
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.WordOrder
open QAdvFew.PoQOracle Turing.MultiTapeTM

 def less (a b : Word) : Bool :=
   (((a.zip b).find? fun p => p.1 != p.2).map fun p => !p.1 && p.2).getD (decide (a.length < b.length))
 theorem less_nil (b : Word) : less [] b = decide (0 < b.length) := by simp [less]
 theorem less_right_nil (a : Word) : less a [] = false := by simp [less]
 theorem less_cons (a b : Bool) (u v : Word) : less (a::u) (b::v) = if a=b then less u v else (!a && b) := by
   cases a <;> cases b <;> simp [less]
 theorem less_iff (a b : Word) : less a b=true ↔ a < b := by
   induction a generalizing b with
   | nil => cases b <;> simp [less_nil]
   | cons a u ih =>
     cases b with
     | nil => simp [less_right_nil]
     | cons b v =>
       cases a <;> cases b <;> simp [less_cons,List.cons_lt_cons_iff,ih]
 theorem less_poly : ComputableTidilyInPolyTime (fun p : Word × Word => less p.1 p.2)
     (encPair encBits encBits) encBool := by
   have hz : ComputableTidilyInPolyTime (fun p : Word × Word => p.1.zip p.2)
       (encPair encBits encBits) (encList (encPair encBool encBool)) := by
     exact (ComputableTidilyInPolyTime.zip encBool encBool).comp
       (((bits_encList_polyTime encBool).1.tidy.comp (ComputableTidilyInPolyTime.fst encBits encBits)).prod
         ((bits_encList_polyTime encBool).1.tidy.comp (ComputableTidilyInPolyTime.snd encBits encBits)))
   have hf := ComputableTidilyInPolyTime.findWithInput
     (test := fun (_ : Word × Word) (p : Bool × Bool) => p.1 != p.2) hz (by fun_prop)
   have hlen : ComputableTidilyInPolyTime (fun p : Word × Word => decide (p.1.length < p.2.length))
       (encPair encBits encBits) encBool := by fun_prop
   have hsel := ComputableTidilyInPolyTime.optionElimWithInput hf hlen
     (body := fun (_ : Word × Word) (p : Bool × Bool) => !p.1 && p.2) (by fun_prop)
   unfold less
   convert hsel using 1
   funext p
   cases (p.1.zip p.2).find? (fun p => p.1 != p.2) <;> rfl

 def insert (x : Word) (l : List Word) : List Word :=
   let j := (l.map fun y => less y x).idxOf false
   l.take j ++ x :: l.drop j
 theorem insert_orderedInsert (x : Word) (l : List Word) : insert x l=List.orderedInsert (· ≤ ·) x l := by
   induction l with
   | nil => simp [insert,List.orderedInsert]
   | cons y l ih =>
     by_cases he : x ≤ y
     · have hless : less y x=false := Bool.eq_false_iff.mpr (by intro h; exact (not_lt_of_ge he) ((less_iff y x).mp h))
       simp [insert,List.orderedInsert,he,hless]
     · have hless : less y x=true := (less_iff y x).mpr (lt_of_not_ge he)
       simp [insert,List.orderedInsert,he,hless,← ih]
 theorem insert_poly : ComputableTidilyInPolyTime (fun p : Word × List Word => insert p.1 p.2)
     (encPair encBits (encList encBits)) (encList encBits) := by
   have hm : ComputableTidilyInPolyTime (fun p : Word × List Word => p.2.map fun y => less y p.1)
       (encPair encBits (encList encBits)) (encList encBool) := by
     apply ComputableTidilyInPolyTime.mapWithInput (by fun_prop)
     exact less_poly.comp (g := fun p : (Word × List Word) × Word => (p.2,p.1.1)) (by fun_prop)
   have hj := (ComputableTidilyInPolyTime.idxOf encBool).comp (hm.prod (ComputableTidilyInPolyTime.const false))
   unfold insert
   fun_prop

 theorem insert_sorted_set (S : Finset Word) (x : Word) (hnot : x ∉ S) :
     insert x (S.sort (· ≤ ·)) = orderedInput S x := by
   classical
   rw [insert_orderedInsert]
   have hp := List.perm_orderedInsert (· ≤ ·) x (S.sort (· ≤ ·))
   have hn : (List.orderedInsert (· ≤ ·) x (S.sort (· ≤ ·))).Nodup := by
     apply hp.nodup_iff.mpr
     exact List.nodup_cons.mpr ⟨by simpa using hnot,Finset.sort_nodup _ _⟩
   have hs : (List.orderedInsert (· ≤ ·) x (S.sort (· ≤ ·))).Pairwise (· ≤ ·) :=
     (Finset.pairwise_sort _ (· ≤ ·)).orderedInsert x _
   have he : (List.orderedInsert (· ≤ ·) x (S.sort (· ≤ ·))).toFinset = (Insert.insert x S : Finset Word) := by
     ext y
     simp
   have hh := (List.toFinset_sort (r := (· ≤ ·)) hn).mpr hs
   rw [he] at hh
   exact hh.symm

end StudentTeacher976.Adaptivity.WordOrder
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceEncoding
open QAdvFew.PoQOracle

 def keys (A : List (Finset Word)) (R : Finset Word) : List Word := (A.flatMap fun S => S.sort (· ≤ ·)) ++ R.sort (· ≤ ·)
 noncomputable def wit {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word) : Word := (leastWitness W a).getD []
 noncomputable def encode {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (k : ℕ) (A : List (Finset Word)) (R : Finset Word) : Word :=
   tup [List.replicate k true,tup (A.map fun S => tup (S.sort (· ≤ ·))),tup (R.sort (· ≤ ·)),
     tup ((keys A R).map fun a => tup [a,wit W a])]
 theorem tup_cons_length (a : Word) (l : List Word) : (tup (a::l)).length=2*a.length+2+(tup l).length := by
   have he : tup (a::l)=a.flatMap (fun b => [true,b]) ++ [false,false] ++ tup l := rfl
   rw [he]
   simp only [List.length_append,List.length_cons,List.length_nil]
   have hh : (a.flatMap fun b => [true,b]).length=2*a.length := by simp [Nat.mul_comm]
   rw [hh]

 theorem tup_pair_length (a b : Word) : (tup [a,b]).length=2*a.length+2*b.length+4 := by
   rw [tup_cons_length,tup_cons_length]
   change _+2+(2*b.length+2+0)=_
   omega
 theorem tup_bound (l : List Word) (B : ℕ) (h : ∀ w ∈ l, w.length ≤ B) :
     (tup l).length ≤ 2*l.length*(B+1) := by
   induction l with
   | nil => simp [tup]
   | cons a l ih =>
     have ha := h a List.mem_cons_self
     have hl := ih (fun w hw => h w (List.mem_cons_of_mem a hw))
     rw [tup_cons_length,List.length_cons]
     nlinarith
 theorem keys_length (A : List (Finset Word)) (R : Finset Word) (k : ℕ)
     (hA : ∀ S ∈ A, S.card ≤ k) (hR : R.card ≤ k) : (keys A R).length ≤ A.length*k+k := by
   have hsum : (A.flatMap fun S => S.sort (· ≤ ·)).length ≤ A.length*k := by
     induction A with
     | nil => simp
     | cons S A ih =>
       have hS := hA S List.mem_cons_self
       have ht := ih (fun T hT => hA T (List.mem_cons_of_mem S hT))
       simp only [List.flatMap_cons,List.length_append,Finset.length_sort,List.length_cons]
       nlinarith
   simpa only [keys,List.length_append,Finset.length_sort] using Nat.add_le_add hsum hR
 theorem keys_positive {i : ℕ} {L : Language} (W : WitnessPresentation i L) (n : ℕ)
     (A : List (Finset Word)) (R : Finset Word)
     (hA : ∀ S ∈ A, ∀ a ∈ S, a ∈ positiveInputs W n) (hR : ∀ a ∈ R, a ∈ positiveInputs W n) :
     ∀ a ∈ keys A R, a ∈ positiveInputs W n := by
   intro a ha
   rcases List.mem_append.mp ha with ha | ha
   · obtain ⟨S,hS,ha⟩ := List.mem_flatMap.mp ha
     exact hA S hS a (by simpa using ha)
   · exact hR a (by simpa using ha)
 theorem wit_valid {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word)
     (h : ∃ w, ValidWitness W a w) : ValidWitness W a (wit W a) := by
   obtain ⟨w,hw,hvalid⟩ := AdviceSemantic.leastWitness_spec W h
   simpa only [wit,hw,Option.getD_some] using hvalid
 theorem encode_size {i : ℕ} {L : Language} (W : WitnessPresentation i L) (n k : ℕ) (hk : 0 < k)
     (A : List (Finset Word)) (R : Finset Word)
     (hAlen : A.length ≤ k*(n+1)) (hAcard : ∀ S ∈ A, S.card ≤ k) (hRcard : R.card ≤ k)
     (hApos : ∀ S ∈ A, ∀ a ∈ S, a ∈ positiveInputs W n) (hRpos : ∀ a ∈ R, a ∈ positiveInputs W n) :
     (encode W k A R).length ≤ 100*(k*(n+1))^2*(n+W.length.eval n+10) := by
   let B := k*(n+1)
   let C := B^2
   let D := C*(n+W.length.eval n+10)
   have hB : 1 ≤ B := by dsimp [B]; nlinarith
   have hkB : k ≤ B := by dsimp [B]; nlinarith
   have hBC : B ≤ C := by dsimp [C]; nlinarith
   have hCD : C ≤ D := by dsimp [D]; nlinarith
   have hD : 1 ≤ D := by omega
   have hrows : ∀ S ∈ A, (tup (S.sort (· ≤ ·))).length ≤ 2*k*(n+1) := by
     intro S hS
     have hb := tup_bound (S.sort (· ≤ ·)) n (fun a ha => le_of_eq (hApos S hS a (by simpa using ha)).1)
     simp only [Finset.length_sort] at hb
     exact hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (hAcard S hS)))
   have hcover := tup_bound (A.map fun S => tup (S.sort (· ≤ ·))) (2*k*(n+1))
     (by intro w hw; obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hw; exact hrows S hS)
   simp only [List.length_map] at hcover
   have hcover' : (tup (A.map fun S => tup (S.sort (· ≤ ·)))).length ≤ 6*C := by
     have hAB : A.length ≤ B := hAlen
     have he : 2*k*(n+1)=2*B := by dsimp [B]; ring
     rw [he] at hcover
     have hh := hcover.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hAB))
     dsimp [C]
     nlinarith
   have hres := tup_bound (R.sort (· ≤ ·)) n (fun a ha => le_of_eq (hRpos a (by simpa using ha)).1)
   simp only [Finset.length_sort] at hres
   have hres' : (tup (R.sort (· ≤ ·))).length ≤ 2*B := by
     exact hres.trans (by dsimp [B]; nlinarith)
   have hkeys := keys_length A R k hAcard hRcard
   have hkeys' : (keys A R).length ≤ 2*C := by
     have hh : A.length*k+k ≤ B*B+B := by
       have hm := Nat.mul_le_mul hAlen hkB
       dsimp [B] at *
       nlinarith
     dsimp [C]
     nlinarith
   have hpos := keys_positive W n A R hApos hRpos
   have hdictRows : ∀ w ∈ (keys A R).map (fun a => tup [a,wit W a]), w.length ≤ 2*(n+W.length.eval n+2) := by
     intro w hw
     obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
     have hv := wit_valid W a (hpos a ha).2
     have hla := (hpos a ha).1
     have hlw : (wit W a).length=W.length.eval n := by rw [hv.1,hla]
     rw [tup_pair_length,hla,hlw]
     omega
   have hdict := tup_bound ((keys A R).map fun a => tup [a,wit W a]) (2*(n+W.length.eval n+2)) hdictRows
   simp only [List.length_map] at hdict
   have hdict' : (tup ((keys A R).map fun a => tup [a,wit W a])).length ≤ 8*D := by
     have hh := hdict.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hkeys'))
     dsimp [D]
     nlinarith
   unfold encode
   rw [tup_cons_length,tup_cons_length,tup_cons_length,tup_cons_length]
   simp only [List.length_replicate,show (tup ([] : List Word)).length=0 from rfl]
   change _ ≤ 100*C*(n+W.length.eval n+10)
   rw [Nat.mul_assoc]
   change _ ≤ 100*D
   have hc6 : 6*C ≤ 6*D := by omega
   have hr2 : 2*B ≤ 2*D := by omega
   have hkD : k ≤ D := by omega
   omega

 noncomputable def bound {i : ℕ} {L : Language} (W : WitnessPresentation i L) (d : ℕ) : Polynomial ℕ :=
   100*(Polynomial.X+1)^(2*(d+1))*(Polynomial.X+W.length+10)
 theorem polynomial_size {i : ℕ} {L : Language} (W : WitnessPresentation i L) (d n k : ℕ) (hk : 0 < k)
     (hkd : k ≤ (n+1)^d) (A : List (Finset Word)) (R : Finset Word)
     (hAlen : A.length ≤ k*(n+1)) (hAcard : ∀ S ∈ A, S.card ≤ k) (hRcard : R.card ≤ k)
     (hApos : ∀ S ∈ A, ∀ a ∈ S, a ∈ positiveInputs W n) (hRpos : ∀ a ∈ R, a ∈ positiveInputs W n) :
     (encode W k A R).length ≤ (bound W d).eval n := by
   have hs := encode_size W n k hk A R hAlen hAcard hRcard hApos hRpos
   have hkp : k*(n+1) ≤ (n+1)^(d+1) := by
     rw [pow_succ]
     exact Nat.mul_le_mul_right _ hkd
   have hpow := Nat.pow_le_pow_left hkp 2
   have hb := hs.trans (Nat.mul_le_mul_right (n+W.length.eval n+10) (Nat.mul_le_mul_left 100 hpow))
   simpa only [bound,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
     Polynomial.eval_X,Polynomial.eval_one,← pow_mul,Nat.mul_comm (d+1) 2] using hb

end StudentTeacher976.Adaptivity.AdviceEncoding
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.SerializationBounds
open QAdvFew.PoQOracle

 theorem word_le_tup (l : List Word) (w : Word) (hw : w ∈ l) : w.length ≤ (tup l).length := by
   induction l with
   | nil => simp at hw
   | cons a l ih =>
     rw [AdviceEncoding.tup_cons_length]
     rcases List.mem_cons.mp hw with rfl | hw
     · omega
     · have hh := ih hw
       omega
 theorem count_le_tup (l : List Word) : l.length ≤ (tup l).length := by
   induction l with
   | nil => rfl
   | cons a l ih => rw [List.length_cons,AdviceEncoding.tup_cons_length]; omega
 theorem dictWitness_bound (D : List (Word × Word)) (a : Word) :
     (AdviceTeacherData.dictWitness D a).length ≤ (tup (D.map fun p => tup [p.1,p.2])).length := by
   unfold AdviceTeacherData.dictWitness
   cases hh : D.find? (fun p => p.1 == a) with
   | none => simp
   | some p =>
     have hp := List.mem_of_find?_eq_some hh
     have hval := word_le_tup [p.1,p.2] p.2 (by simp)
     exact hval.trans (word_le_tup _ (tup [p.1,p.2]) (List.mem_map.mpr ⟨p,hp,rfl⟩))

 def initial (X : List Word) (x : Word) (D : List (Word × Word)) (q : ℕ) : Word :=
   AdviceLoopData.encodeState X x D q 0 [] []
 theorem static_bounds (X : List Word) (x : Word) (D : List (Word × Word)) (q S : ℕ)
     (hS : (initial X x D q).length ≤ S) :
     (tup X).length ≤ S ∧ x.length ≤ S ∧ (tup (D.map fun p => tup [p.1,p.2])).length ≤ S ∧ q ≤ S ∧
       X.length ≤ S ∧ (∀ a ∈ X, a.length ≤ S) ∧ ∀ a ∈ X, (AdviceTeacherData.dictWitness D a).length ≤ S := by
   let l := [tup X,x,tup (D.map fun p => tup [p.1,p.2]),List.replicate q true,[true],[],[]]
   have he : initial X x D q=tup l := rfl
   have hcode : (tup l).length ≤ S := he ▸ hS
   have hX := (word_le_tup l (tup X) (by simp [l])).trans hcode
   have hx := (word_le_tup l x (by simp [l])).trans hcode
   have hD := (word_le_tup l (tup (D.map fun p => tup [p.1,p.2])) (by simp [l])).trans hcode
   have hq : q ≤ S := by
     have hh := (word_le_tup l (List.replicate q true) (by simp [l])).trans hcode
     simpa only [List.length_replicate] using hh
   exact ⟨hX,hx,hD,hq,(count_le_tup X).trans hX,
     fun a ha => (word_le_tup X a ha).trans hX,fun a ha => (dictWitness_bound D a).trans hD⟩

end StudentTeacher976.Adaptivity.SerializationBounds
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceRecognizer

 def HasWitness {i : ℕ} {L : Language} (W : WitnessPresentation i L) (X : List Word)
     (x : Word) (G : List (List Word)) : Prop :=
   ∃ Y ∈ G, ValidWitness W x (Y.getD (X.idxOf x) [])
 noncomputable def recognizes {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (q : ℕ) (X : List Word) (x : Word) (wit : Word → Word) : ℕ → ℕ → List TupleReply → Bool := by
   classical
   exact fun budget => match budget with
   | 0 => fun _ _ => false
   | b+1 => fun t Z =>
       let G := normalize W f X t (Z.map fun z => List.replicate q z)
       if HasWitness W X x G then true
       else match AdviceSemantic.knownTeacher W X x wit G with
       | none => false
       | some z => recognizes W f q X x wit b (t+1) (Z++[z])

 theorem sound {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (q : ℕ) (X : List Word) (x : Word) (wit : Word → Word)
     (budget t : ℕ) (Z : List TupleReply) (h : recognizes W f q X x wit budget t Z=true) : x ∈ L := by
   induction budget generalizing t Z with
   | zero => simp [recognizes] at h
   | succ b ih =>
     classical
     rw [recognizes] at h
     dsimp only at h
     split at h
     · rename_i hw
       obtain ⟨Y,hY,hlen,hvalid⟩ := hw
       exact (W.represents x).mpr ⟨_,hlen,hvalid⟩
     · split at h
       · cases h
       · exact ih _ _ h

 theorem path_complete {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (q : ℕ) (X : List Word) (x : Word) (wit : Word → Word)
     (P : List TupleReply) (budget t : ℕ) (Z : List TupleReply) (hb : P.length < budget)
     (hpath : ∀ s < P.length, AdviceSemantic.knownTeacher W X x wit
       (normalize W f X (t+s) ((Z++P.take s).map fun z => List.replicate q z)) = some (P.getD s (0,[])))
     (hwin : HasWitness W X x
       (normalize W f X (t+P.length) ((Z++P).map fun z => List.replicate q z))) :
     recognizes W f q X x wit budget t Z=true := by
   classical
   induction P generalizing budget t Z with
   | nil =>
     cases budget with
     | zero => simp at hb
     | succ b =>
       have hw : HasWitness W X x (normalize W f X t (Z.map fun z => List.replicate q z)) := by simpa using hwin
       simp only [recognizes]
       try dsimp only
       rw [if_pos hw]
   | cons z P ih =>
     cases budget with
     | zero => simp at hb
     | succ b =>
       rw [recognizes]
       try dsimp only
       split
       · rfl
       · have hfirst := hpath 0 (by simp)
         simp only [Nat.add_zero,List.take_zero,List.append_nil,List.getD_cons_zero] at hfirst
         rw [hfirst]
         apply ih b (t+1) (Z++[z]) (by simpa using hb)
         · intro s hs
           have hh := hpath (s+1) (by simpa using hs)
           simpa only [List.take_succ_cons,List.getD_cons_succ,List.append_assoc,List.singleton_append,
             Nat.add_assoc,Nat.add_comm 1 s] using hh
         · simpa only [List.length_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_comm 1 P.length] using hwin

 theorem complete {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (f : TupleStudent) (n k q : ℕ) (X : List Word) (x : Word) (wit : Word → Word)
     (hX : TupleShape n k X) (hx : x ∈ X) (hpos : ∃ w, ValidWitness W x w)
     (hshape : TupleStudentShape W n k q f) (hwin : TupleStudentWins W n k q (normalize W f))
     (havoid : ∀ z ∈ fixedTrace W f q X k, X.getD z.1 [] ≠ x)
     (hknown : ∀ a ∈ X, a ≠ x → leastWitness W a = some (wit a)) :
     recognizes W f q X x wit k 0 []=true := by
   classical
   obtain ⟨t,ht,hlen,hterm⟩ := AdviceSemantic.terminal_before W f q X k (AdviceSemantic.trace_short W f n k q X hX hshape hwin)
   let P := fixedTrace W f q X t
   have hPlen : P.length=t := hlen
   have hidx : X.idxOf x < X.length := List.idxOf_lt_length_iff.mpr hx
   have hxj : X.getD (X.idxOf x) []=x := by rw [List.getD_eq_getElem _ _ hidx]; exact List.getElem_idxOf hidx
   apply path_complete W f q X x wit P k 0 [] (by omega)
   · intro s hs
     have hteach := (AdviceSemantic.trace_spec W f q n k X hX t).2 s hs
     have hmem : P.getD s (0,[]) ∈ P := by rw [List.getD_eq_getElem _ _ hs]; exact List.getElem_mem _
     have hax := havoid (P.getD s (0,[])) (AdviceSemantic.trace_mem_mono W f q X (Nat.le_of_lt ht) _ hmem)
     have hc := AdviceSemantic.cutTeacher_some W X x _ _ hteach hax
     rw [← AdviceSemantic.knownTeacher_eq_cut W X x wit _ hknown] at hc
     simpa only [Nat.zero_add,List.nil_append] using hc
   · have hw := AdviceSemantic.teacher_none_covers W X
       (normalize W f X t (P.map fun z => List.replicate q z)) (X.idxOf x) hidx (hxj.symm ▸ hpos) hterm
     simpa only [HasWitness,Nat.zero_add,List.nil_append,hPlen,hxj] using hw

end StudentTeacher976.Adaptivity.AdviceRecognizer
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceLoopSemantic
open QAdvFew.PoQOracle

 abbrev State := ℕ × List TupleReply × Option Bool
 def modeWord (o : Option Bool) : Word := o.elim [] (fun b => [b])
 noncomputable def advance {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (q : ℕ) (X : List Word) (x : Word) (wit : Word → Word) (st : State) : State := by
   classical
   exact match st.2.2 with
   | some _ => st
   | none =>
     let G := normalize W f X st.1 (st.2.1.map fun z => List.replicate q z)
     if AdviceRecognizer.HasWitness W X x G then (st.1,st.2.1,some true)
     else match AdviceSemantic.knownTeacher W X x wit G with
       | none => (st.1,st.2.1,some false)
       | some z => (st.1+1,st.2.1++[z],none)

 theorem iterate_stopped {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (q : ℕ) (X : List Word) (x : Word) (wit : Word → Word) (budget t : ℕ) (Z : List TupleReply) (b : Bool) :
     (advance W f q X x wit)^[budget] (t,Z,some b)=(t,Z,some b) := by
   induction budget with
   | zero => rfl
   | succ budget ih => simpa only [Function.iterate_succ_apply,advance] using ih
 theorem iterate_recognizes {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (q : ℕ) (X : List Word) (x : Word) (wit : Word → Word) (budget t : ℕ) (Z : List TupleReply) :
     ((advance W f q X x wit)^[budget] (t,Z,none)).2.2.getD false=
       AdviceRecognizer.recognizes W f q X x wit budget t Z := by
   classical
   induction budget generalizing t Z with
   | zero => rfl
   | succ budget ih =>
     rw [Function.iterate_succ_apply,advance,AdviceRecognizer.recognizes]
     dsimp only
     split
     · rw [iterate_stopped]
       rfl
     · cases ht : AdviceSemantic.knownTeacher W X x wit
         (normalize W f X t (Z.map fun z => List.replicate q z)) with
       | none => rw [iterate_stopped]; rfl
       | some z => exact ih _ _

 def encode (X : List Word) (x : Word) (D : List (Word × Word)) (q : ℕ) (st : State) : Word :=
   AdviceLoopData.encodeState X x D q st.1 st.2.1 (modeWord st.2.2)

 theorem step_encode {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (F T : Word → Word) (flag : Word → Bool)
     (hF : ∀ X t H, F (NormalizationData.studentInput X t H)=tup ((normalize W f X t H).map tup))
     (hT : ∀ s : Word, T s=QAdvFew.PoQOracle.tup [[flag s],AdviceTeacherData.encodeOption
       (AdviceSemantic.knownTeacher W (AdviceTeacherData.inputs s) (AdviceTeacherData.target s)
         (AdviceTeacherData.witness s) (AdviceTeacherData.guesses s))])
     (hflag : ∀ s : Word, AdviceTeacherData.target s ∈ AdviceTeacherData.inputs s →
       (flag s=true ↔ ∃ Y ∈ AdviceTeacherData.guesses s, ValidWitness W (AdviceTeacherData.target s)
         (Y.getD (AdviceTeacherData.targetIndex s) [])))
     (q : ℕ) (X : List Word) (x : Word) (D : List (Word × Word)) (wit : Word → Word) (hx : x ∈ X)
     (hdict : ∀ G : List (List Word), ∀ a ∈ X, a ≠ x →
       AdviceTeacherData.witness (AdviceTeacherData.encodeInput X x G D) a=wit a) (st : State) :
     AdviceLoopData.step F T (encode X x D q st)=encode X x D q (advance W f q X x wit st) := by
   classical
   rcases st with ⟨t,Z,mode⟩
   cases mode with
   | some b =>
     change AdviceLoopData.step F T (AdviceLoopData.encodeState X x D q t Z [b])=AdviceLoopData.encodeState X x D q t Z [b]
     unfold AdviceLoopData.step
     exact AdviceLoopData.finish_done X x D q t Z [b] _ _ (by simp)
   | none =>
     let G := normalize W f X t (Z.map fun z => List.replicate q z)
     let arg := AdviceTeacherData.encodeInput X x G D
     have hknown : AdviceSemantic.knownTeacher W (AdviceTeacherData.inputs arg) (AdviceTeacherData.target arg)
         (AdviceTeacherData.witness arg) (AdviceTeacherData.guesses arg)=AdviceSemantic.knownTeacher W X x wit G := by
       rw [AdviceTeacherData.inputs_encoded,AdviceTeacherData.target_encoded,AdviceTeacherData.guesses_encoded]
       exact AdviceSemantic.knownTeacher_wit_congr W X x _ wit G (hdict G)
     have hform : T arg=tup [[flag arg],AdviceTeacherData.encodeOption (AdviceSemantic.knownTeacher W X x wit G)] := by
       rw [hT,hknown]
     have hfc : flag arg=true ↔ AdviceRecognizer.HasWitness W X x G := by
       have hh := hflag arg (by simpa only [arg,AdviceTeacherData.inputs_encoded,AdviceTeacherData.target_encoded] using hx)
       simpa only [arg,AdviceTeacherData.target_encoded,AdviceTeacherData.guesses_encoded,AdviceTeacherData.targetIndex,
         AdviceTeacherData.inputs_encoded,AdviceRecognizer.HasWitness] using hh
     have hstep : AdviceLoopData.step F T (AdviceLoopData.encodeState X x D q t Z []) =
         AdviceLoopData.finish (tup [tup [AdviceLoopData.encodeState X x D q t Z [],tup (G.map tup)],
           tup [[flag arg],AdviceTeacherData.encodeOption (AdviceSemantic.knownTeacher W X x wit G)]]) := by
       unfold AdviceLoopData.step
       rw [AdviceLoopData.studentArgument_encoded,hF]
       dsimp only
       rw [AdviceLoopData.teacherArgument_encoded]
       change AdviceLoopData.finish (tup [tup [AdviceLoopData.encodeState X x D q t Z [],tup (G.map tup)],T arg]) = _
       rw [hform]
     change AdviceLoopData.step F T (AdviceLoopData.encodeState X x D q t Z []) =
       encode X x D q (if AdviceRecognizer.HasWitness W X x G then (t,Z,some true)
         else match AdviceSemantic.knownTeacher W X x wit G with
           | none => (t,Z,some false)
           | some z => (t+1,Z++[z],none))
     by_cases hw : AdviceRecognizer.HasWitness W X x G
     · have hb := hfc.mpr hw
       rw [if_pos hw]
       rw [hb,AdviceLoopData.finish_accept] at hstep
       exact hstep
     · have hb : flag arg=false := Bool.eq_false_iff.mpr (fun h => hw (hfc.mp h))
       rw [if_neg hw]
       rw [hb] at hstep
       cases ht : AdviceSemantic.knownTeacher W X x wit G with
       | none =>
         rw [ht,AdviceLoopData.finish_reject] at hstep
         exact hstep
       | some z =>
         rw [ht,AdviceLoopData.finish_reply] at hstep
         exact hstep

 theorem iterate_map {α β : Type} (f : β → β) (g : α → α) (e : α → β)
     (h : ∀ a, f (e a)=e (g a)) (k : ℕ) (a : α) : f^[k] (e a)=e (g^[k] a) := by
   induction k with
   | zero => rfl
   | succ k ih => rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih,h]

end StudentTeacher976.Adaptivity.AdviceLoopSemantic
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceTeacherBounds
open QAdvFew.PoQOracle Turing.MultiTapeTM

 def replyBound {i : ℕ} {L : Language} (W : WitnessPresentation i L) (S : ℕ) : ℕ :=
   2*S+4*S*(S+W.length.eval S+1)+4
 theorem reply_size {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (x : Word) (wit : Word → Word) (G : List (List Word)) (S : ℕ)
     (hXlen : X.length ≤ S) (hX : ∀ a ∈ X, a.length ≤ S) (hwit : ∀ a ∈ X, (wit a).length ≤ S)
     (z : TupleReply) (hz : AdviceSemantic.knownTeacher W X x wit G=some z) :
     (encodeReply z).length ≤ replyBound W S := by
   classical
   unfold AdviceSemantic.knownTeacher at hz
   obtain ⟨j,hj,hz⟩ := Option.map_eq_some_iff.mp hz
   subst z
   have hjX : j < X.length := List.mem_range.mp (List.mem_of_find?_eq_some hj)
   have ha : X.getD j [] ∈ X := by rw [List.getD_eq_getElem _ _ hjX]; exact List.getElem_mem _
   let Y := (List.range X.length).map fun h => if h=j then wit (X.getD j []) else List.replicate (W.length.eval (X.getD h []).length) false
   have hYlen : Y.length=X.length := by simp [Y]
   have hY : ∀ y ∈ Y, y.length ≤ S+W.length.eval S := by
     intro y hy
     obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hy
     have hhX : h < X.length := List.mem_range.mp hh
     have hhmem : X.getD h [] ∈ X := by rw [List.getD_eq_getElem _ _ hhX]; exact List.getElem_mem _
     by_cases he : h=j
     · rw [if_pos he]
       exact (hwit _ ha).trans (Nat.le_add_right _ _)
     · rw [if_neg he,List.length_replicate]
       exact (NativeBatch.polyEvalMono W.length (hX _ hhmem)).trans (Nat.le_add_left _ _)
   have htuple := AdviceEncoding.tup_bound Y (S+W.length.eval S) hY
   rw [hYlen] at htuple
   have htuple' : (tup Y).length ≤ 2*S*(S+W.length.eval S+1) :=
     htuple.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hXlen))
   change (tup [List.replicate j true,tup Y]).length ≤ _
   rw [AdviceEncoding.tup_pair_length,List.length_replicate]
   unfold replyBound
   nlinarith

 theorem option_size {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (x : Word) (wit : Word → Word) (G : List (List Word)) (S : ℕ)
     (hXlen : X.length ≤ S) (hX : ∀ a ∈ X, a.length ≤ S) (hwit : ∀ a ∈ X, (wit a).length ≤ S) :
     (AdviceTeacherData.encodeOption (AdviceSemantic.knownTeacher W X x wit G)).length ≤ 2*replyBound W S+2 := by
   cases hh : AdviceSemantic.knownTeacher W X x wit G with
   | none => simp [AdviceTeacherData.encodeOption,tup]
   | some z =>
     have hz := reply_size W X x wit G S hXlen hX hwit z hh
     change (tup [encodeReply z]).length ≤ _
     rw [AdviceEncoding.tup_cons_length]
     change 2*(encodeReply z).length+2+0 ≤ _
     omega
 theorem response_size {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (x : Word) (wit : Word → Word) (G : List (List Word)) (S : ℕ) (b : Bool)
     (hXlen : X.length ≤ S) (hX : ∀ a ∈ X, a.length ≤ S) (hwit : ∀ a ∈ X, (wit a).length ≤ S) :
     (tup [[b],AdviceTeacherData.encodeOption (AdviceSemantic.knownTeacher W X x wit G)]).length ≤ 4*replyBound W S+10 := by
   have hz := option_size W X x wit G S hXlen hX hwit
   rw [AdviceEncoding.tup_pair_length]
   simp only [List.length_cons,List.length_nil]
   omega

 theorem witness_size (s a : Word) (S : ℕ)
     (hvalues : ∀ e ∈ AdviceTeacherData.dictionary s, (AdviceTeacherData.value e).length ≤ S) :
     (AdviceTeacherData.witness s a).length ≤ S := by
   unfold AdviceTeacherData.witness
   cases hh : (AdviceTeacherData.dictionary s).find? (fun e => AdviceTeacherData.key e == a) with
   | none => simp
   | some e => exact hvalues e (List.mem_of_find?_eq_some hh)

end StudentTeacher976.Adaptivity.AdviceTeacherBounds
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceLoopBounds
open QAdvFew.PoQOracle
open AdviceLoopSemantic

 def Invariant {i : ℕ} {L : Language} (W : WitnessPresentation i L) (S j : ℕ) (st : State) : Prop :=
   st.1 ≤ j ∧ st.2.1.length ≤ j ∧ ∀ z ∈ st.2.1, (encodeReply z).length ≤ AdviceTeacherBounds.replyBound W S
 theorem invariant_step {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (q : ℕ) (X : List Word) (x : Word) (wit : Word → Word) (S j : ℕ)
     (hXlen : X.length ≤ S) (hX : ∀ a ∈ X, a.length ≤ S) (hwit : ∀ a ∈ X, (wit a).length ≤ S)
     (st : State) (h : Invariant W S j st) : Invariant W S (j+1) (advance W f q X x wit st) := by
   classical
   rcases st with ⟨t,Z,mode⟩
   obtain ⟨ht,hZ,hz⟩ := h
   dsimp only [Prod.fst,Prod.snd] at ht hZ hz
   cases mode with
   | some b => exact ⟨by simpa [advance] using (show t ≤ j+1 by omega),by simpa [advance] using (show Z.length ≤ j+1 by omega),hz⟩
   | none =>
     unfold advance
     dsimp only
     split
     · dsimp only [Invariant]
       exact ⟨by omega,by omega,hz⟩
     · cases hh : AdviceSemantic.knownTeacher W X x wit (normalize W f X t (Z.map fun z => List.replicate q z)) with
       | none =>
         dsimp only [Invariant]
         exact ⟨by omega,by omega,hz⟩
       | some z =>
         dsimp only [Invariant]
         refine ⟨by omega,by simp only [List.length_append,List.length_cons,List.length_nil]; omega,?_⟩
         intro a ha
         rcases List.mem_append.mp ha with ha | ha
         · exact hz a ha
         · have he : a=z := by simpa using ha
           subst a
           exact AdviceTeacherBounds.reply_size W X x wit _ S hXlen hX hwit z hh
 theorem invariant_iterate {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (q : ℕ) (X : List Word) (x : Word) (wit : Word → Word) (S : ℕ)
     (hXlen : X.length ≤ S) (hX : ∀ a ∈ X, a.length ≤ S) (hwit : ∀ a ∈ X, (wit a).length ≤ S) (j : ℕ) :
     Invariant W S j ((advance W f q X x wit)^[j] (0,[],none)) := by
   induction j with
   | zero => exact ⟨le_rfl,le_rfl,by simp⟩
   | succ j ih =>
     rw [Function.iterate_succ_apply']
     exact invariant_step W f q X x wit S j hXlen hX hwit _ ih

 theorem modeWord_length (o : Option Bool) : (modeWord o).length ≤ 1 := by cases o <;> simp [modeWord]
 theorem encode_bound {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (x : Word) (D : List (Word × Word)) (q S A k : ℕ)
     (hXcode : (tup X).length ≤ A) (hxcode : x.length ≤ A)
     (hDcode : (tup (D.map fun p => tup [p.1,p.2])).length ≤ A) (hq : q ≤ A)
     (st : State) (h : Invariant W S k st) :
     (encode X x D q st).length ≤ 14*(A+k+2*k*(AdviceTeacherBounds.replyBound W S+1)+2) := by
   obtain ⟨ht,hZ,hz⟩ := h
   have hhist := AdviceEncoding.tup_bound (st.2.1.map encodeReply) (AdviceTeacherBounds.replyBound W S)
     (by intro z hz'; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz'; exact hz a ha)
   simp only [List.length_map] at hhist
   have hhist' : (tup (st.2.1.map encodeReply)).length ≤ 2*k*(AdviceTeacherBounds.replyBound W S+1) :=
     hhist.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hZ))
   have hmode := modeWord_length st.2.2
   unfold encode AdviceLoopData.encodeState
   have hrq : (List.replicate q true).length=q := List.length_replicate ..
   have hrt : (List.replicate (st.1+1) true).length=st.1+1 := List.length_replicate ..
   have hh := AdviceEncoding.tup_bound
     [tup X,x,tup (D.map fun p => tup [p.1,p.2]),List.replicate q true,List.replicate (st.1+1) true,
       tup (st.2.1.map encodeReply),modeWord st.2.2]
     (A+k+2*k*(AdviceTeacherBounds.replyBound W S+1)+1) (by
       intro w hw
       simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
       rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
   simpa only [List.length_cons,List.length_nil] using hh

end StudentTeacher976.Adaptivity.AdviceLoopBounds
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceGameData
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)

 def budget (s : Word) : ℕ := (field s 0).length
 def point (s : Word) : Word := field s 2
 def base (s : Word) : List Word := TupleCodec.decodeTuple (field s 1)
 def inputs (s : Word) : List Word := WordOrder.insert (point s) (base s)
 def dictionary (s : Word) : List (Word × Word) :=
   (TupleCodec.decodeTuple (field s 3)).map fun e => (AdviceTeacherData.key e,AdviceTeacherData.value e)
 def queries (s : Word) : ℕ := (field s 4).length
 def initial (s : Word) : Word := SerializationBounds.initial (inputs s) (point s) (dictionary s) (queries s)
 def prep (s : Word) : ℕ × Word := (budget s,initial s)
 def finalBit (s : Word) : Word := [(field s 6).headD false]

 theorem budget_poly : ComputableTidilyInPolyTime budget encBits encUnary :=
   ComputableTidilyInPolyTime.length_bits.comp (field_poly 0)
 theorem point_poly : ComputableTidilyInPolyTime point encBits encBits := field_poly 2
 theorem base_poly : ComputableTidilyInPolyTime base encBits (encList encBits) :=
   TupleCodec.decoder_poly.tidy.comp (field_poly 1)
 theorem inputs_poly : ComputableTidilyInPolyTime inputs encBits (encList encBits) := by
   change ComputableTidilyInPolyTime (fun s : Word => WordOrder.insert (point s) (base s)) encBits (encList encBits)
   exact WordOrder.insert_poly.comp (g := fun s : Word => (point s,base s)) (point_poly.prod base_poly)
 theorem dictionary_poly : ComputableTidilyInPolyTime dictionary encBits (encList (encPair encBits encBits)) :=
   (ComputableTidilyInPolyTime.map (AdviceTeacherData.key_poly.prod AdviceTeacherData.value_poly)).comp
     (TupleCodec.decoder_poly.tidy.comp (field_poly 3))
 theorem queries_poly : ComputableTidilyInPolyTime queries encBits encUnary :=
   ComputableTidilyInPolyTime.length_bits.comp (field_poly 4)
 theorem initial_poly : ComputableTidilyInPolyTime initial encBits encBits := by
   have hX := inputs_poly
   have hx := point_poly
   have hD := dictionary_poly
   have hq := (ComputableTidilyInPolyTime.encode encUnary).comp queries_poly
   have hentries : ComputableTidilyInPolyTime (fun s => (dictionary s).map fun p => tup [p.1,p.2]) encBits (encList encBits) := by
     apply ComputableTidilyInPolyTime.mapWithInput hD
     apply TupleCodec.encode_poly.comp
     fun_prop
   unfold initial SerializationBounds.initial AdviceLoopData.encodeState
   apply TupleCodec.encode_poly.comp
   exact (TupleCodec.encode_poly.comp hX).cons' (hx.cons' ((TupleCodec.encode_poly.comp hentries).cons'
     (hq.cons' ((ComputableTidilyInPolyTime.const [true]).cons' ((ComputableTidilyInPolyTime.const (tup [])).cons'
       ((ComputableTidilyInPolyTime.const []).cons' (ComputableTidilyInPolyTime.const [])))))))
 theorem prep_poly : ComputableTidilyInPolyTime prep encBits (encPair encUnary encBits) := budget_poly.prod initial_poly
 theorem finalBit_poly : ComputableTidilyInPolyTime finalBit encBits encBits :=
   ((ComputableTidilyInPolyTime.headD (encA := encBool) (encL := encBits) false).comp (field_poly 6)).bitsCons
     (ComputableTidilyInPolyTime.const [])
 theorem point_mem (s : Word) : point s ∈ inputs s := by
   rw [inputs,WordOrder.insert_orderedInsert]
   simp

 def encodeInput (k : ℕ) (S : List Word) (x : Word) (D : List (Word × Word)) (q : ℕ) : Word :=
   tup [List.replicate k true,tup S,x,tup (D.map fun p => tup [p.1,p.2]),List.replicate q true]
 theorem budget_encoded (k : ℕ) (S : List Word) (x : Word) (D : List (Word × Word)) (q : ℕ) :
     budget (encodeInput k S x D q)=k := by simp [budget,encodeInput,field,TupleCodec.decode_tup]
 theorem point_encoded (k : ℕ) (S : List Word) (x : Word) (D : List (Word × Word)) (q : ℕ) :
     point (encodeInput k S x D q)=x := by simp [point,encodeInput,field,TupleCodec.decode_tup]
 theorem inputs_encoded (k : ℕ) (S : List Word) (x : Word) (D : List (Word × Word)) (q : ℕ) :
     inputs (encodeInput k S x D q)=WordOrder.insert x S := by simp [inputs,point,base,encodeInput,field,TupleCodec.decode_tup]
 theorem dictionary_encoded (k : ℕ) (S : List Word) (x : Word) (D : List (Word × Word)) (q : ℕ) :
     dictionary (encodeInput k S x D q)=D := by
   simp [dictionary,encodeInput,field,TupleCodec.decode_tup,List.map_map,Function.comp_def,AdviceTeacherData.key_encoded,AdviceTeacherData.value_encoded]
 theorem queries_encoded (k : ℕ) (S : List Word) (x : Word) (D : List (Word × Word)) (q : ℕ) :
     queries (encodeInput k S x D q)=q := by simp [queries,encodeInput,field,TupleCodec.decode_tup]

 theorem finalBit_encode (X : List Word) (x : Word) (D : List (Word × Word)) (q : ℕ) (st : AdviceLoopSemantic.State) :
     finalBit (AdviceLoopSemantic.encode X x D q st)=[st.2.2.getD false] := by
   rcases st with ⟨t,Z,mode⟩
   cases mode <;> simp [finalBit,AdviceLoopSemantic.encode,AdviceLoopData.encodeState,AdviceLoopSemantic.modeWord,field,TupleCodec.decode_tup]

end StudentTeacher976.Adaptivity.AdviceGameData
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity
open QAdvFew.PoQOracle Turing.MultiTapeTM
open OracleComputations

 theorem normalize_uniform (i : ℕ) (L : Language) (W : WitnessPresentation i L)
     (f : TupleStudent) (hf : UniformTupleStudent i f) : UniformTupleStudent i (normalize W f) := by
   obtain ⟨F,hF,hfspec⟩ := hf
   obtain ⟨O0,hO0,hF⟩ := (inFP_iff i F).mp hF
   obtain ⟨O1,M,p,hO1,htotal,hW⟩ := W.efficient
   let J := joinOracle O0 O1
   have hJ : {x | J x=true} ∈ Sigma i := join_sigma i O0 O1 hO0 hO1
   have hcontext : Computes J (fun s => tup [s,F s]) :=
     retain J F (retag false O0 J (join_false O0 O1) F hF)
   have hpos : ∀ w : Word, 0 < p.eval w.length := by
     intro w
     have ht := htotal w
     by_contra hn
     have hz : p.eval w.length = 0 := by omega
     rw [hz] at ht
     norm_num [OTM.result,OTM.runCfg,OTM.init,Fin.ext_iff,Nat.mod_eq_of_lt (show 2 < M.k+6 by omega)] at ht
   have htest : ∀ a b, NativeBatch.result M O1 p (tup [a,b])=true ↔ W.test a b := by
     intro a b
     rw [NativeBatch.result,getD_true_iff,← hW]
     constructor
     · rintro ⟨u,v,he,huv⟩
       have hh := congrArg TupleCodec.decodeTuple he
       simp only [TupleCodec.decode_tup,List.cons.injEq,and_true] at hh
       obtain ⟨rfl,rfl⟩ := hh
       exact huv
     · exact fun h => ⟨a,b,rfl,h⟩
   let G := fun s => NormalizationData.post W (s,NativeBatch.scores M O1 p (NormalizationData.prep s))
   obtain ⟨C,hC,T,B,htrace⟩ := NativeBatch.protocol M p hpos NormalizationData.prep (NormalizationData.post W)
     NormalizationData.prep_poly (NormalizationData.post_poly W)
   have hG1 : Computes O1 G := of_protocol C hC.tidy O1 G T B (htrace O1)
   have hG : Computes J G := retag true O1 J (join_true O0 O1) G hG1
   let Fnorm := fun s => G (tup [s,F s])
   refine ⟨Fnorm,(inFP_iff i _).mpr ⟨J,hJ,compose J _ G hcontext hG⟩,?_⟩
   intro X t H
   change G (tup [NormalizationData.studentInput X t H,F (NormalizationData.studentInput X t H)]) = _
   have he : F (NormalizationData.studentInput X t H) = tup ((f X t H).map tup) := hfspec X t H
   rw [he]
   exact NormalizationData.post_encoded M O1 p W f htest X t H

end StudentTeacher976.Adaptivity
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceGameUniform
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceLoopSemantic

 noncomputable def replyPolynomial {i : ℕ} {L : Language} (W : WitnessPresentation i L) : Polynomial ℕ :=
   2*Polynomial.X+4*Polynomial.X*(Polynomial.X+W.length+1)+4
 theorem replyPolynomial_eval {i : ℕ} {L : Language} (W : WitnessPresentation i L) (S : ℕ) :
     (replyPolynomial W).eval S=AdviceTeacherBounds.replyBound W S := by simp [replyPolynomial,AdviceTeacherBounds.replyBound]

 theorem uniform (i : ℕ) (L : Language) (W : WitnessPresentation i L) (f : TupleStudent)
     (hf : UniformTupleStudent i f) :
     ∃ G : Word → Word, InFP i G ∧ ∀ s : Word, G s =
       [AdviceRecognizer.recognizes W f (AdviceGameData.queries s) (AdviceGameData.inputs s) (AdviceGameData.point s)
         (AdviceTeacherData.dictWitness (AdviceGameData.dictionary s)) (AdviceGameData.budget s) 0 []] := by
   obtain ⟨F,hFi,hFspec⟩ := normalize_uniform i L W f hf
   have hF : ∀ X t H, F (NormalizationData.studentInput X t H)=tup ((normalize W f X t H).map tup) := hFspec
   obtain ⟨T,flag,hTi,hT⟩ := AdviceTeacherData.uniform_structured i L W
   let step := AdviceLoopData.step F T
   have hstepi : InFP i step := AdviceLoopData.step_inFP i F T hFi hTi
   have hcomm (s : Word) (st : State) :
       step (encode (AdviceGameData.inputs s) (AdviceGameData.point s) (AdviceGameData.dictionary s) (AdviceGameData.queries s) st)=
       encode (AdviceGameData.inputs s) (AdviceGameData.point s) (AdviceGameData.dictionary s) (AdviceGameData.queries s)
         (advance W f (AdviceGameData.queries s) (AdviceGameData.inputs s) (AdviceGameData.point s)
           (AdviceTeacherData.dictWitness (AdviceGameData.dictionary s)) st) := by
     apply step_encode W f F T flag hF (fun s => (hT s).1) (fun s => (hT s).2.2) _ _ _ _ _ (AdviceGameData.point_mem s)
     intro G a ha hax
     exact AdviceTeacherData.witness_dict _ _ G _ a
   have hiter (s : Word) (j : ℕ) :
       step^[j] (AdviceGameData.initial s)=
       encode (AdviceGameData.inputs s) (AdviceGameData.point s) (AdviceGameData.dictionary s) (AdviceGameData.queries s)
         ((advance W f (AdviceGameData.queries s) (AdviceGameData.inputs s) (AdviceGameData.point s)
           (AdviceTeacherData.dictWitness (AdviceGameData.dictionary s)))^[j] (0,[],none)) :=
     iterate_map step _ _ (hcomm s) j (0,[],none)
   obtain ⟨P,hP⟩ := AdviceGameData.prep_poly.polyBounded_length.exists_polynomial
   let B : Polynomial ℕ := 14*(P+P+2*P*((replyPolynomial W).comp P+1)+2)
   have horbit : ∀ s : Word, ∀ j ≤ (AdviceGameData.prep s).1,
       (step^[j] (AdviceGameData.prep s).2).length ≤ B.eval s.length := by
     intro s j hj
     let S := P.eval s.length
     have hp := hP s
     simp only [encPair_apply,List.length_append,length_frame,encUnary_apply,List.length_replicate,encBits_apply] at hp
     have hk : AdviceGameData.budget s ≤ S := by dsimp [AdviceGameData.prep] at hp; omega
     have hinit : (AdviceGameData.initial s).length ≤ S := by dsimp [AdviceGameData.prep] at hp; omega
     obtain ⟨hXc,hxc,hDc,hq,hX,hXa,hwit⟩ := SerializationBounds.static_bounds _ _ _ _ S hinit
     have hinv := AdviceLoopBounds.invariant_iterate W f (AdviceGameData.queries s) (AdviceGameData.inputs s) (AdviceGameData.point s)
       (AdviceTeacherData.dictWitness (AdviceGameData.dictionary s)) S hX hXa hwit j
     have hjS : j ≤ S := hj.trans hk
     have hi : AdviceLoopBounds.Invariant W S S
         ((advance W f (AdviceGameData.queries s) (AdviceGameData.inputs s) (AdviceGameData.point s)
           (AdviceTeacherData.dictWitness (AdviceGameData.dictionary s)))^[j] (0,[],none)) :=
       ⟨hinv.1.trans hjS,hinv.2.1.trans hjS,hinv.2.2⟩
     have hb := AdviceLoopBounds.encode_bound W _ _ _ _ S S S hXc hxc hDc hq _ hi
     change (step^[j] (AdviceGameData.initial s)).length ≤ _
     rw [hiter]
     have hBeval : B.eval s.length=14*(S+S+2*S*(AdviceTeacherBounds.replyBound W S+1)+2) := by
       simp [B,S,replyPolynomial_eval]
     rw [hBeval]
     exact hb
   have hloop := NativeIteration.inFP_iterate i step hstepi AdviceGameData.prep AdviceGameData.prep_poly B horbit
   let G := fun s => AdviceGameData.finalBit (step^[(AdviceGameData.prep s).1] (AdviceGameData.prep s).2)
   refine ⟨G,OracleComputations.inFP_post i _ AdviceGameData.finalBit hloop AdviceGameData.finalBit_poly,?_⟩
   intro s
   unfold G AdviceGameData.prep
   rw [hiter,AdviceGameData.finalBit_encode,iterate_recognizes]

end StudentTeacher976.Adaptivity.AdviceGameUniform
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.OracleBooleanBatch
open QAdvFew.PoQOracle Turing.MultiTapeTM

 theorem any_poly : ComputableTidilyInPolyTime (fun w : Word => w.any id) encBits encBool := by
   exact ComputableTidilyInPolyTime.anyWithEncoding (encA := encBool) (encL := encBits)
     (test := fun p : Bool × Bool => p.2) (ComputableTidilyInPolyTime.snd encBool encBool)
     (ComputableTidilyInPolyTime.const false) ComputableTidilyInPolyTime.id'
 theorem post_poly : ComputableTidilyInPolyTime (fun a : Word × Word => [a.2.any id]) (encPair encBits encBits) encBits :=
   (any_poly.comp (ComputableTidilyInPolyTime.snd encBits encBits)).bitsCons (ComputableTidilyInPolyTime.const [])
 theorem uniform (i : ℕ) (F : Word → Word) (hF : InFP i F) :
     ∃ G : Word → Word, InFP i G ∧ ∀ l : List Word, G (tup l)=[l.any fun w => (F w).headD false] := by
   obtain ⟨O,hO,M,p,hM⟩ := (OracleComputations.inFP_iff i F).mp hF
   have hpos : ∀ w : Word, 0 < p.eval w.length := by
     intro w
     have ht := (hM w).1
     by_contra hn
     have hz : p.eval w.length=0 := by omega
     rw [hz] at ht
     norm_num [OTM.result,OTM.runCfg,OTM.init,Fin.ext_iff,Nat.mod_eq_of_lt (show 2 < M.k+6 by omega),
       Nat.mod_eq_of_lt (show 1 < M.k+6 by omega)] at ht
     cases ht
   let post := fun a : Word × Word => [a.2.any id]
   let G := fun s => post (s,NativeBatch.scores M O p (TupleCodec.decodeTuple s))
   obtain ⟨C,hC,T,B,htrace⟩ := NativeBatch.protocol M p hpos TupleCodec.decodeTuple post TupleCodec.decoder_poly.tidy post_poly
   have hG : OracleComputations.Computes O G := OracleComputations.of_protocol C hC.tidy O G T B (htrace O)
   refine ⟨G,(OracleComputations.inFP_iff i G).mpr ⟨O,hO,hG⟩,?_⟩
   intro l
   have hr (w : Word) : NativeBatch.result M O p w=(F w).headD false := by
     unfold NativeBatch.result
     rw [(hM w).1]
     rfl
   have hfunc : NativeBatch.result M O p=(fun w => (F w).headD false) := funext hr
   simp [G,post,TupleCodec.decode_tup,NativeBatch.scores,hfunc,List.any_map]

end StudentTeacher976.Adaptivity.OracleBooleanBatch
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.OracleProducts
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)

 def pairPost (u : Word) : Word := tup [field (field u 0) 1,field u 1]
 theorem pairPost_poly : ComputableTidilyInPolyTime pairPost encBits encBits := by
   have h0 := field_poly 0
   have h1 := field_poly 1
   unfold pairPost
   apply TupleCodec.encode_poly.comp
   fun_prop
 theorem pair_inFP (i : ℕ) (F G : Word → Word) (hF : InFP i F) (hG : InFP i G) :
     InFP i (fun x => tup [F x,G x]) := by
   have hf := OracleComputations.inFP_retain i F hF
   have hgcall := OracleComputations.inFP_compose i (fun v : Word => field v 0) G (pure_inFP i _ (field_poly 0)) hG
   have hg := OracleComputations.inFP_retain i _ hgcall
   have hb := OracleComputations.inFP_compose i _ _ hf hg
   have hp := OracleComputations.inFP_post i _ pairPost hb pairPost_poly
   convert hp using 1
   funext x
   simp [pairPost,field,TupleCodec.decode_tup]

 def orPost (u : Word) : Word := [(field u 0).headD false || (field u 1).headD false]
 theorem orPost_poly : ComputableTidilyInPolyTime orPost encBits encBits := by
   have h0 := (ComputableTidilyInPolyTime.headD (encA := encBool) (encL := encBits) false).comp (field_poly 0)
   have h1 := (ComputableTidilyInPolyTime.headD (encA := encBool) (encL := encBits) false).comp (field_poly 1)
   unfold orPost
   apply ComputableTidilyInPolyTime.bitsCons
   · exact ComputableTidilyInPolyTime.bool_or.comp (h0.prod h1)
   · exact ComputableTidilyInPolyTime.const []
 theorem or_inFP (i : ℕ) (F G : Word → Word) (hF : InFP i F) (hG : InFP i G) :
     InFP i (fun x => [(F x).headD false || (G x).headD false]) := by
   have hp := OracleComputations.inFP_post i _ orPost (pair_inFP i F G hF hG) orPost_poly
   convert hp using 1
   funext x
   simp [orPost,field,TupleCodec.decode_tup]

end StudentTeacher976.Adaptivity.OracleProducts
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceDecisionData
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)

 def input (s : Word) : Word := field s 0
 def advice (s : Word) : Word := field s 1
 def budgetWord (s : Word) : Word := field (advice s) 0
 def covers (s : Word) : List Word := TupleCodec.decodeTuple (field (advice s) 1)
 def dictionaryWord (s : Word) : Word := field (advice s) 3
 def rawLength (s : Word) : ℕ := (input s).length*(budgetWord s).length
 def queryCount (q : ℕ → ℕ) (s : Word) : ℕ := resource q (rawLength s)
 def games (q : ℕ → ℕ) (s : Word) : List Word :=
   (covers s).map fun S => tup [budgetWord s,S,input s,dictionaryWord s,List.replicate (queryCount q s) true]
 def gameArgument (q : ℕ → ℕ) (s : Word) : Word := tup (games q s)
 def probe (s : Word) : Word := tup [tup [input s],input s,tup [],dictionaryWord s]
 def lookup (s : Word) : Word := AdviceTeacherData.witness (probe s) (input s)
 def directArgument (s : Word) : Word := tup [tup [input s],input s,tup [tup [lookup s]],dictionaryWord s]

 theorem input_poly : ComputableTidilyInPolyTime input encBits encBits := field_poly 0
 theorem advice_poly : ComputableTidilyInPolyTime advice encBits encBits := field_poly 1
 theorem budgetWord_poly : ComputableTidilyInPolyTime budgetWord encBits encBits := (field_poly 0).comp advice_poly
 theorem covers_poly : ComputableTidilyInPolyTime covers encBits (encList encBits) :=
   TupleCodec.decoder_poly.tidy.comp ((field_poly 1).comp advice_poly)
 theorem dictionaryWord_poly : ComputableTidilyInPolyTime dictionaryWord encBits encBits := (field_poly 3).comp advice_poly
 theorem rawLength_poly : ComputableTidilyInPolyTime rawLength encBits encUnary := by
   have hx := input_poly
   have hk := budgetWord_poly
   unfold rawLength
   fun_prop
 theorem queryCount_poly (q : ℕ → ℕ) (hq : PolyTimeLength q) :
     ComputableTidilyInPolyTime (queryCount q) encBits encUnary := by
   change ComputableTidilyInPolyTime (fun s : Word => queryCount q s) encBits encUnary
   have hraw : ComputableTidilyInPolyTime (fun s => List.replicate (rawLength s) true) encBits encBits :=
     (ComputableTidilyInPolyTime.encode encUnary).comp rawLength_poly
   have h := (resource_function_pure q hq).comp hraw
   simpa only [queryCount,Function.comp_def,List.length_replicate] using h
 theorem games_poly (q : ℕ → ℕ) (hq : PolyTimeLength q) : ComputableTidilyInPolyTime (games q) encBits (encList encBits) := by
   have hk := budgetWord_poly
   have hx := input_poly
   have hD := dictionaryWord_poly
   have hqword : ComputableTidilyInPolyTime (fun s => List.replicate (queryCount q s) true) encBits encBits :=
     (ComputableTidilyInPolyTime.encode encUnary).comp (queryCount_poly q hq)
   unfold games
   apply ComputableTidilyInPolyTime.mapWithInput covers_poly
   apply TupleCodec.encode_poly.comp
   let hf := ComputableTidilyInPolyTime.fst encBits encBits
   exact (hk.comp hf).cons' ((ComputableTidilyInPolyTime.snd encBits encBits).cons'
     ((hx.comp hf).cons' ((hD.comp hf).cons' ((hqword.comp hf).cons' (ComputableTidilyInPolyTime.const [])))))

 theorem gameArgument_poly (q : ℕ → ℕ) (hq : PolyTimeLength q) : ComputableTidilyInPolyTime (gameArgument q) encBits encBits :=
   TupleCodec.encode_poly.comp (games_poly q hq)
 theorem probe_poly : ComputableTidilyInPolyTime probe encBits encBits := by
   have hx := input_poly
   have hD := dictionaryWord_poly
   have htx := TupleCodec.encode_poly.comp (hx.cons' (ComputableTidilyInPolyTime.const []))
   unfold probe
   apply TupleCodec.encode_poly.comp
   exact htx.cons' (hx.cons' ((ComputableTidilyInPolyTime.const (tup [])).cons' (hD.cons' (ComputableTidilyInPolyTime.const []))))
 theorem lookup_poly : ComputableTidilyInPolyTime lookup encBits encBits :=
   AdviceTeacherData.witness_poly.comp (probe_poly.prod input_poly)
 theorem directArgument_poly : ComputableTidilyInPolyTime directArgument encBits encBits := by
   have hx := input_poly
   have hD := dictionaryWord_poly
   have hw := lookup_poly
   have htx := TupleCodec.encode_poly.comp (hx.cons' (ComputableTidilyInPolyTime.const []))
   have htw := TupleCodec.encode_poly.comp (hw.cons' (ComputableTidilyInPolyTime.const []))
   have htww := TupleCodec.encode_poly.comp (htw.cons' (ComputableTidilyInPolyTime.const []))
   unfold directArgument
   apply TupleCodec.encode_poly.comp
   exact htx.cons' (hx.cons' (htww.cons' (hD.cons' (ComputableTidilyInPolyTime.const []))))

 theorem direct_inputs (s : Word) : AdviceTeacherData.inputs (directArgument s)=[input s] := by
   simp [directArgument,AdviceTeacherData.inputs,field,TupleCodec.decode_tup]
 theorem direct_target (s : Word) : AdviceTeacherData.target (directArgument s)=input s := by
   simp [directArgument,AdviceTeacherData.target,field,TupleCodec.decode_tup]
 theorem direct_guesses (s : Word) : AdviceTeacherData.guesses (directArgument s)=[[lookup s]] := by
   simp [directArgument,AdviceTeacherData.guesses,field,TupleCodec.decode_tup]
 theorem direct_index (s : Word) : AdviceTeacherData.targetIndex (directArgument s)=0 := by
   simp [AdviceTeacherData.targetIndex,direct_inputs,direct_target]

 theorem input_encoded (x a : Word) : input (tup [x,a])=x := by simp [input,field,TupleCodec.decode_tup]
 theorem advice_encoded (x a : Word) : advice (tup [x,a])=a := by simp [advice,field,TupleCodec.decode_tup]
 theorem budgetWord_encoded {i : ℕ} {L : Language} (W : WitnessPresentation i L) (k : ℕ)
     (A : List (Finset Word)) (R : Finset Word) (x : Word) :
     budgetWord (tup [x,AdviceEncoding.encode W k A R])=List.replicate k true := by
   simp [budgetWord,advice_encoded,AdviceEncoding.encode,field,TupleCodec.decode_tup]
 theorem covers_encoded {i : ℕ} {L : Language} (W : WitnessPresentation i L) (k : ℕ)
     (A : List (Finset Word)) (R : Finset Word) (x : Word) :
     covers (tup [x,AdviceEncoding.encode W k A R])=A.map (fun S => tup (S.sort (· ≤ ·))) := by
   simp [covers,advice_encoded,AdviceEncoding.encode,field,TupleCodec.decode_tup]
 theorem dictionaryWord_encoded {i : ℕ} {L : Language} (W : WitnessPresentation i L) (k : ℕ)
     (A : List (Finset Word)) (R : Finset Word) (x : Word) :
     dictionaryWord (tup [x,AdviceEncoding.encode W k A R])=
       tup ((AdviceEncoding.keys A R).map fun a => tup [a,AdviceEncoding.wit W a]) := by
   simp [dictionaryWord,advice_encoded,AdviceEncoding.encode,field,TupleCodec.decode_tup]
 theorem games_encoded {i : ℕ} {L : Language} (W : WitnessPresentation i L) (q : ℕ → ℕ) (k : ℕ)
     (A : List (Finset Word)) (R : Finset Word) (x : Word) :
     games q (tup [x,AdviceEncoding.encode W k A R])=A.map (fun S => AdviceGameData.encodeInput k (S.sort (· ≤ ·)) x
       ((AdviceEncoding.keys A R).map fun a => (a,AdviceEncoding.wit W a)) (resource q (x.length*k))) := by
   simp [games,covers_encoded,budgetWord_encoded,input_encoded,dictionaryWord_encoded,queryCount,rawLength,
     List.map_map,Function.comp_def,AdviceGameData.encodeInput]
 theorem lookup_encoded {i : ℕ} {L : Language} (W : WitnessPresentation i L) (k : ℕ)
     (A : List (Finset Word)) (R : Finset Word) (x : Word) (hx : x ∈ AdviceEncoding.keys A R) :
     lookup (tup [x,AdviceEncoding.encode W k A R])=AdviceEncoding.wit W x := by
   have hp : probe (tup [x,AdviceEncoding.encode W k A R])=
       AdviceTeacherData.encodeInput [x] x [] ((AdviceEncoding.keys A R).map fun a => (a,AdviceEncoding.wit W a)) := by
     simp [probe,input_encoded,dictionaryWord_encoded,AdviceTeacherData.encodeInput,List.map_map,Function.comp_def]
   unfold lookup
   rw [hp,input_encoded]
   exact AdviceTeacherData.witness_encoded [x] x [] _ _ x hx

end StudentTeacher976.Adaptivity.AdviceDecisionData
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceDecisionUniform
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceDecisionData

 noncomputable def gameFlag {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent) (v : Word) : Bool :=
   AdviceRecognizer.recognizes W f (AdviceGameData.queries v) (AdviceGameData.inputs v) (AdviceGameData.point v)
     (AdviceTeacherData.dictWitness (AdviceGameData.dictionary v)) (AdviceGameData.budget v) 0 []
 theorem uniform (i : ℕ) (L : Language) (W : WitnessPresentation i L) (f : TupleStudent)
     (hf : UniformTupleStudent i f) (q : ℕ → ℕ) (hq : PolyTimeLength q) :
     ∃ F : Word → Word, InFP i F ∧ ∀ s : Word, (F s).headD false=true ↔
       (∃ v ∈ games q s, gameFlag W f v=true) ∨ ValidWitness W (input s) (lookup s) := by
   obtain ⟨G,hGi,hG⟩ := AdviceGameUniform.uniform i L W f hf
   obtain ⟨H,hHi,hH⟩ := OracleBooleanBatch.uniform i G hGi
   let cover := fun s => H (gameArgument q s)
   have hcoveri : InFP i cover := OracleComputations.inFP_compose i (gameArgument q) H (pure_inFP i _ (gameArgument_poly q hq)) hHi
   have hcover (s : Word) : cover s=[(games q s).any (gameFlag W f)] := by
     unfold cover gameArgument
     rw [hH]
     congr 1
     apply congrArg (fun p : Word → Bool => (games q s).any p)
     funext v
     rw [hG]
     rfl
   obtain ⟨T,flag,hTi,hT⟩ := AdviceTeacherData.uniform_structured i L W
   let direct := fun s => AdviceTeacherData.field (T (directArgument s)) 0
   have hcall : InFP i (fun s => T (directArgument s)) :=
     OracleComputations.inFP_compose i directArgument T (pure_inFP i _ directArgument_poly) hTi
   have hdirecti : InFP i direct := OracleComputations.inFP_post i _ (fun s => AdviceTeacherData.field s 0) hcall (AdviceTeacherData.field_poly 0)
   have hdirect (s : Word) : direct s=[flag (directArgument s)] := by
     unfold direct
     rw [(hT (directArgument s)).1]
     simp [AdviceTeacherData.field,TupleCodec.decode_tup]
   have hflag (s : Word) : flag (directArgument s)=true ↔ ValidWitness W (input s) (lookup s) := by
     have hh := (hT (directArgument s)).2.2 (by simp [direct_inputs,direct_target])
     simpa only [direct_target,direct_guesses,direct_index,List.mem_singleton,exists_eq_left,List.getD_cons_zero] using hh
   let F := fun s => [(cover s).headD false || (direct s).headD false]
   refine ⟨F,OracleProducts.or_inFP i cover direct hcoveri hdirecti,?_⟩
   intro s
   simp [F,hcover,hdirect,hflag,List.any_eq_true]

end StudentTeacher976.Adaptivity.AdviceDecisionUniform
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceDecisionSemantic
open QAdvFew.PoQOracle

 theorem game_sound {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent) (v : Word)
     (h : AdviceDecisionUniform.gameFlag W f v=true) : AdviceGameData.point v ∈ L :=
   AdviceRecognizer.sound W f _ _ _ _ _ 0 [] h
 theorem point_games (q : ℕ → ℕ) (s v : Word) (hv : v ∈ AdviceDecisionData.games q s) :
     AdviceGameData.point v=AdviceDecisionData.input s := by
   obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hv
   simp [AdviceGameData.point,AdviceTeacherData.field,TupleCodec.decode_tup]
 theorem decision_sound {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (q : ℕ → ℕ) (F : Word → Word)
     (hF : ∀ s : Word, (F s).headD false=true ↔
       (∃ v ∈ AdviceDecisionData.games q s, AdviceDecisionUniform.gameFlag W f v=true) ∨
         ValidWitness W (AdviceDecisionData.input s) (AdviceDecisionData.lookup s))
     (s : Word) (h : (F s).headD false=true) : AdviceDecisionData.input s ∈ L := by
   rcases (hF s).mp h with ⟨v,hv,hg⟩ | ⟨hlen,hw⟩
   · rw [← point_games q s v hv]
     exact game_sound W f v hg
   · exact (W.represents _).mpr ⟨_,hlen,hw⟩

 theorem game_complete {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (n k q : ℕ) (hk : 0 < k) (S : Finset Word) (x : Word)
     (hg : GoodPair W n k q f S x) (keys : List Word) (hkeys : ∀ a ∈ S, a ∈ keys)
     (hshape : TupleStudentShape W n k q f) (hwin : TupleStudentWins W n k q (normalize W f)) :
     AdviceDecisionUniform.gameFlag W f (AdviceGameData.encodeInput k (S.sort (· ≤ ·)) x
       (keys.map fun a => (a,AdviceEncoding.wit W a)) q)=true := by
   classical
   obtain ⟨hcard,hS,hx,hnot,havoid⟩ := hg
   simp only [AdviceDecisionUniform.gameFlag,AdviceGameData.queries_encoded,AdviceGameData.inputs_encoded,
     AdviceGameData.point_encoded,AdviceGameData.dictionary_encoded,AdviceGameData.budget_encoded]
   rw [WordOrder.insert_sorted_set S x hnot]
   have hX : TupleShape n k (orderedInput S x) := by
     constructor
     · simp only [orderedInput,Finset.length_sort,Finset.card_insert_of_notMem hnot,hcard]
       omega
     · intro a ha
       have hh : a=x ∨ a∈S := by simpa [orderedInput] using ha
       rcases hh with rfl | ha
       · exact hx.1
       · exact (hS a ha).1
   apply AdviceRecognizer.complete W f n k q _ x _ hX (by simp [orderedInput]) hx.2 hshape hwin havoid
   intro a ha hax
   have hSa : a ∈ S := by
     have hh : a=x ∨ a∈S := by simpa [orderedInput] using ha
     exact hh.resolve_left hax
   have hd : AdviceTeacherData.dictWitness (keys.map fun a => (a,AdviceEncoding.wit W a)) a=AdviceEncoding.wit W a :=
     (AdviceTeacherData.witness_dict [] [] [] _ a).symm.trans
       (AdviceTeacherData.witness_encoded [] [] [] keys (AdviceEncoding.wit W) a (hkeys a hSa))
   rw [hd]
   obtain ⟨w,hw,hvalid⟩ := AdviceSemantic.leastWitness_spec W (hS a hSa).2
   unfold AdviceEncoding.wit
   rw [hw]
   rfl

 theorem keys_residual (A : List (Finset Word)) (R : Finset Word) {x : Word} (hx : x ∈ R) : x ∈ AdviceEncoding.keys A R :=
   List.mem_append_right _ (by simpa using hx)
 theorem keys_cover (A : List (Finset Word)) (R S : Finset Word) (hS : S ∈ A) {x : Word} (hx : x ∈ S) : x ∈ AdviceEncoding.keys A R := by
   apply List.mem_append_left
   exact List.mem_flatMap.mpr ⟨S,hS,by simpa using hx⟩

 theorem decision_complete {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (q : ℕ → ℕ) (F : Word → Word)
     (hF : ∀ s : Word, (F s).headD false=true ↔
       (∃ v ∈ AdviceDecisionData.games q s, AdviceDecisionUniform.gameFlag W f v=true) ∨
         ValidWitness W (AdviceDecisionData.input s) (AdviceDecisionData.lookup s))
     (n k : ℕ) (hk : 0 < k) (A : List (Finset Word)) (R : Finset Word)
     (hcover : ∀ x : Word, x ∈ positiveInputs W n → x ∈ R ∨ ∃ S ∈ A, x ∈ S ∨
       GoodPair W n k (resource q (n*k)) f S x)
     (hshape : TupleStudentShape W n k (resource q (n*k)) f)
     (hwin : TupleStudentWins W n k (resource q (n*k)) (normalize W f))
     (x : Word) (hlen : x.length=n) (hx : x ∈ L) :
     (F (tup [x,AdviceEncoding.encode W k A R])).headD false=true := by
   have hpos : x ∈ positiveInputs W n := ⟨hlen,(W.represents x).mp hx⟩
   apply (hF _).mpr
   rcases hcover x hpos with hR | ⟨S,hS,hxS | hg⟩
   · right
     rw [AdviceDecisionData.input_encoded,AdviceDecisionData.lookup_encoded W k A R x (keys_residual A R hR)]
     exact AdviceEncoding.wit_valid W x hpos.2
   · right
     rw [AdviceDecisionData.input_encoded,AdviceDecisionData.lookup_encoded W k A R x (keys_cover A R S hS hxS)]
     exact AdviceEncoding.wit_valid W x hpos.2
   · left
     rw [AdviceDecisionData.games_encoded,hlen]
     refine ⟨AdviceGameData.encodeInput k (S.sort (· ≤ ·)) x
       ((AdviceEncoding.keys A R).map fun a => (a,AdviceEncoding.wit W a)) (resource q (n*k)),?_,?_⟩
     · exact List.mem_map.mpr ⟨S,hS,rfl⟩
     · exact game_complete W f n k (resource q (n*k)) hk S x hg (AdviceEncoding.keys A R)
         (fun a ha => keys_cover A R S hS ha) hshape hwin

end StudentTeacher976.Adaptivity.AdviceDecisionSemantic
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity
open QAdvFew.PoQOracle

 theorem delta_iff_uniform_boolean (i : ℕ) (L : Language) :
     L ∈ Delta i ↔ ∃ F : Word → Word, InFP i F ∧ ∀ x, x∈L ↔ (F x).headD false=true := by
   constructor
   · rintro ⟨O,M,p,hO,htotal,hL⟩
     let F := fun x => [(M.result O x (p.eval x.length)).getD false]
     obtain ⟨C,hC,B,htrace⟩ := NativeCPU.native_protocol M p true
     have hf : OracleComputations.Computes O F := by
       apply OracleComputations.of_protocol C hC.tidy O F p B
       intro x
       refine ⟨p.eval x.length,le_rfl,?_⟩
       simpa only [NativeCPU.nativeOutput,Bool.true_eq,↓reduceIte] using htrace O x
     refine ⟨F,(OracleComputations.inFP_iff i F).mpr ⟨O,hO,hf⟩,?_⟩
     intro x
     simpa only [F,List.headD_cons,getD_true_iff] using hL x
   · rintro ⟨F,hF,hL⟩
     obtain ⟨O,hO,M,p,hM⟩ := (OracleComputations.inFP_iff i F).mp hF
     refine ⟨O,M,p,hO,?_,?_⟩
     · intro s
       rw [(hM s).1]
       rfl
     · intro s
       rw [(hM s).1]
       simpa only [Option.some.injEq] using hL s

end StudentTeacher976.Adaptivity
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.OracleWordMap
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)

def encode (todo done : List Word) : Word := tup [tup todo,tup done]
def todo (s : Word) : List Word := TupleCodec.decodeTuple (field s 0)
def done (s : Word) : List Word := TupleCodec.decodeTuple (field s 1)
def arg (s : Word) : Word := (todo s).headD []
def finish (s : Word) : Word :=
  let context := field s 0
  encode (todo context).tail (field s 1 :: done context)
def step (F : Word → Word) (s : Word) : Word := finish (tup [s,F (arg s)])
def prep (s : Word) : ℕ × Word := ((TupleCodec.decodeTuple s).length,encode (TupleCodec.decodeTuple s) [])
def post (s : Word) : Word := tup (done s).reverse

theorem encode_poly : ComputableTidilyInPolyTime (fun p : List Word × List Word => encode p.1 p.2)
    (encPair (encList encBits) (encList encBits)) encBits := by
  unfold encode
  apply TupleCodec.encode_poly.comp
  have h0 := TupleCodec.encode_poly.comp (ComputableTidilyInPolyTime.fst (encList encBits) (encList encBits))
  have h1 := TupleCodec.encode_poly.comp (ComputableTidilyInPolyTime.snd (encList encBits) (encList encBits))
  fun_prop
theorem todo_poly : ComputableTidilyInPolyTime todo encBits (encList encBits) :=
  TupleCodec.decoder_poly.tidy.comp (field_poly 0)
theorem done_poly : ComputableTidilyInPolyTime done encBits (encList encBits) :=
  TupleCodec.decoder_poly.tidy.comp (field_poly 1)
theorem arg_poly : ComputableTidilyInPolyTime arg encBits encBits := by
  exact (ComputableTidilyInPolyTime.headD (encA := encBits) (encL := encList encBits) []).comp todo_poly
theorem finish_poly : ComputableTidilyInPolyTime finish encBits encBits := by
  have hctx := field_poly 0
  have htodo := todo_poly.comp hctx
  have hdone := done_poly.comp hctx
  have hval := field_poly 1
  unfold finish
  apply encode_poly.comp (g := fun s : Word => ((todo (field s 0)).tail,field s 1 :: done (field s 0)))
  fun_prop
theorem prep_poly : ComputableTidilyInPolyTime prep encBits (encPair encUnary encBits) := by
  have hd := TupleCodec.decoder_poly.tidy
  have he := encode_poly.comp (hd.prod (ComputableTidilyInPolyTime.const []))
  unfold prep
  exact ((ComputableTidilyInPolyTime.length_list encBits).comp hd).prod he
theorem post_poly : ComputableTidilyInPolyTime post encBits encBits := by
  unfold post
  apply TupleCodec.encode_poly.comp
  exact (ComputableTidilyInPolyTime.listReverse encBits).comp done_poly
theorem step_inFP (i : ℕ) (F : Word → Word) (hF : InFP i F) : InFP i (step F) := by
  have harg := OracleComputations.inFP_compose i arg F (pure_inFP i arg arg_poly) hF
  exact OracleComputations.inFP_post i _ finish (OracleComputations.inFP_retain i _ harg) finish_poly

theorem todo_encode (l d : List Word) : todo (encode l d)=l := by
  simp [todo,encode,field,TupleCodec.decode_tup]
theorem done_encode (l d : List Word) : done (encode l d)=d := by
  simp [done,encode,field,TupleCodec.decode_tup]
theorem step_encode (F : Word → Word) (w : Word) (l d : List Word) :
    step F (encode (w::l) d)=encode l (F w::d) := by
  simp [step,finish,arg,field,TupleCodec.decode_tup,todo_encode,done_encode]
theorem iterate_encode (F : Word → Word) (l d : List Word) (j : ℕ) (hj : j ≤ l.length) :
    (step F)^[j] (encode l d)=encode (l.drop j) (((l.take j).map F).reverse++d) := by
  induction j generalizing l d with
  | zero => simp
  | succ j ih =>
    cases l with
    | nil => simp at hj
    | cons w l =>
      have hrest : j ≤ l.length := by simpa using hj
      rw [Function.iterate_succ_apply,step_encode,ih l (F w::d) hrest]
      simp [List.take_succ_cons,List.drop_succ_cons,List.reverse_cons,List.append_assoc]

theorem word_output_bound (i : ℕ) (F : Word → Word) (hF : InFP i F) :
    ∃ p : Polynomial ℕ,∀ x : Word,(F x).length≤p.eval x.length := by
  obtain ⟨O,M,p,hO,hM⟩ := hF
  refine ⟨Polynomial.X+p+2,?_⟩
  intro x
  have hh := NativeCPU.output_size M false (x.length+p.eval x.length+1)
    (NativeCPU.encodeBody M (x.length+p.eval x.length+1) (M.runCfg O x (p.eval x.length)))
    (by simp [NativeCPU.encodeBody])
  rw [NativeCPU.runtime_output] at hh
  simpa [NativeCPU.nativeOutput,(hM x).2,Nat.add_assoc] using hh

theorem orbit_bound (F : Word → Word) (p : Polynomial ℕ)
    (hp : ∀ x : Word,(F x).length≤p.eval x.length) (Q : Polynomial ℕ)
    (hQ : ∀ s : Word,(encList encBits (TupleCodec.decodeTuple s)).length≤Q.eval s.length) :
    ∀ s : Word,∀ j≤(prep s).1,
      ((step F)^[j] (prep s).2).length≤
        (4*Q*(Q+p.comp Q+2)+4).eval s.length := by
  intro s j hj
  let l := TupleCodec.decodeTuple s
  let K := Q.eval s.length
  have hl : (encList encBits l).length≤K := hQ s
  have hcount : l.length≤K := (NativeBatch.count_le_code l).trans hl
  have hword : ∀ x ∈ l,x.length≤K := fun x hx => (NativeBatch.member_length_le hx).trans hl
  have hdrop : (tup (l.drop j)).length≤2*K*(K+1) := by
    apply (AdviceEncoding.tup_bound (l.drop j) K (fun x hx => hword x (List.mem_of_mem_drop hx))).trans
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (by rw [List.length_drop]; omega))
  have hdone : (tup (((l.take j).map F).reverse)).length≤2*K*(p.eval K+1) := by
    apply (AdviceEncoding.tup_bound _ (p.eval K) ?_).trans
    · simp only [List.length_reverse,List.length_map]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (by rw [List.length_take]; omega))
    · intro w hw
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hw)
      exact (hp x).trans (NativeBatch.polyEvalMono p (hword x (List.mem_of_mem_take hx)))
  change ((step F)^[j] (encode l [])).length≤_
  rw [iterate_encode F l [] j hj,List.append_nil]
  change (tup [tup (l.drop j),tup (((l.take j).map F).reverse)]).length≤_
  rw [AdviceEncoding.tup_pair_length]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  change 2*(tup (l.drop j)).length+2*(tup (((l.take j).map F).reverse)).length+4≤4*K*(K+p.eval K+2)+4
  nlinarith

theorem uniform (i : ℕ) (F : Word → Word) (hF : InFP i F) :
    InFP i (fun s => tup ((TupleCodec.decodeTuple s).map F)) := by
  obtain ⟨p,hp⟩ := word_output_bound i F hF
  obtain ⟨Q,hQ⟩ := TupleCodec.decoder_poly.tidy.polyBounded_length.exists_polynomial
  simp only [encBits_apply] at hQ
  have hi := NativeIteration.inFP_iterate i (step F) (step_inFP i F hF) prep prep_poly
    (4*Q*(Q+p.comp Q+2)+4) (orbit_bound F p hp Q hQ)
  have he : (fun s => post ((step F)^[(prep s).1] (prep s).2)) =
      (fun s => tup ((TupleCodec.decodeTuple s).map F)) := by
    funext s
    unfold prep
    rw [iterate_encode F _ [] _ le_rfl]
    simp [post,done_encode]
  rw [← he]
  exact OracleComputations.inFP_post i _ post hi post_poly

end StudentTeacher976.Adaptivity.OracleWordMap
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceComputations
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)


theorem uniform (i : ℕ) (f : Word → Word) (hf : InFP i f) : InFPAdvice i f := by
  refine ⟨fun s => f (field s 0),0,fun _ => [],?_,by simp,?_⟩
  · exact OracleComputations.inFP_compose i _ f (pure_inFP i _ (field_poly 0)) hf
  · intro x
    simp [field,TupleCodec.decode_tup]

theorem post (i : ℕ) (f h : Word → Word) (hf : InFPAdvice i f) (hh : InFP i h) :
    InFPAdvice i (fun x => h (f x)) := by
  obtain ⟨G,b,a,hG,hb,hs⟩ := hf
  exact ⟨fun s => h (G s),b,a,OracleComputations.inFP_compose i G h hG hh,hb,
    fun x => by dsimp only; rw [hs]⟩

theorem poly_mono (p : Polynomial ℕ) {n m : ℕ} (h : n ≤ m) : p.eval n ≤ p.eval m := by
  simp only [Polynomial.eval_eq_sum,Polynomial.sum]
  apply Finset.sum_le_sum
  intro j hj
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h j)

theorem output_bound (i : ℕ) (f : Word → Word) (hf : InFPAdvice i f) :
    ∃ p : Polynomial ℕ,∀ x,(f x).length ≤ p.eval x.length := by
  obtain ⟨G,b,a,hG,hb,hs⟩ := hf
  obtain ⟨p,hp⟩ := OracleWordMap.word_output_bound i G hG
  refine ⟨p.comp (2*Polynomial.X+2*b+4),?_⟩
  intro x
  rw [←hs x,Polynomial.eval_comp]
  apply (hp _).trans
  apply poly_mono
  rw [AdviceEncoding.tup_pair_length]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  have h := hb x.length
  omega


def adviceTable (a : ℕ → Word) (N : ℕ) : Word := tup ((List.range (N+1)).map a)

theorem adviceTable_bound (a : ℕ → Word) (b : Polynomial ℕ)
    (hb : ∀ n,(a n).length ≤ b.eval n) (N : ℕ) :
    (adviceTable a N).length ≤ 2*(N+1)*(b.eval N+1) := by
  have ht : ∀ w∈(List.range (N+1)).map a,w.length ≤ b.eval N := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hw
    exact (hb j).trans (poly_mono b (by have := List.mem_range.mp hj;omega))
  simpa only [adviceTable,List.length_map,List.length_range] using
    AdviceEncoding.tup_bound ((List.range (N+1)).map a) (b.eval N) ht

theorem adviceTable_get (a : ℕ → Word) (N j : ℕ) (hj : j ≤ N) :
    (TupleCodec.decodeTuple (adviceTable a N)).getD j []=a j := by
  rw [adviceTable,TupleCodec.decode_tup]
  rw [List.getD_eq_getElem _ _ (by simp;omega)]
  simp

def prepareF (s : Word) : Word := tup [field s 0,field (field s 1) 0]
def prepareG (s : Word) : Word :=
  tup [field s 1,(TupleCodec.decodeTuple (field (field (field s 0) 1) 1)).getD (field s 1).length []]

theorem prepareF_poly : ComputableTidilyInPolyTime prepareF encBits encBits := by
  have h0 := field_poly 0
  have h1 := field_poly 1
  unfold prepareF
  apply TupleCodec.encode_poly.comp
  fun_prop

theorem prepareG_poly : ComputableTidilyInPolyTime prepareG encBits encBits := by
  have h0 := field_poly 0
  have h1 := field_poly 1
  have hd := TupleCodec.decoder_poly.tidy.comp (h1.comp (h1.comp h0))
  have hn := ComputableTidilyInPolyTime.length_bits.comp h1
  have hp := (ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []).comp (hd.prod hn)
  unfold prepareG
  apply TupleCodec.encode_poly.comp
  fun_prop


theorem compose (i : ℕ) (f g : Word → Word)
    (hf : InFPAdvice i f) (hg : InFPAdvice i g) :
    InFPAdvice i (fun x => g (f x)) := by
  obtain ⟨p,hp⟩ := output_bound i f hf
  obtain ⟨F,bf,af,hF,hbf,hsf⟩ := hf
  obtain ⟨G,bg,ag,hG,hbg,hsg⟩ := hg
  let a := fun n => tup [af n,adviceTable ag (p.eval n)]
  let b := 2*bf+4*(p+1)*(bg.comp p+1)+4
  have hb (n : ℕ) : (a n).length ≤ b.eval n := by
    have ht := adviceTable_bound ag bg hbg (p.eval n)
    have ha := hbf n
    simp only [a,AdviceEncoding.tup_pair_length]
    dsimp only [b]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,
      Polynomial.eval_comp]
    nlinarith
  let call := fun s => F (prepareF s)
  have hc : InFP i call := OracleComputations.inFP_compose i prepareF F
    (pure_inFP i _ prepareF_poly) hF
  let H := fun s => G (prepareG (tup [s,call s]))
  have hH : InFP i H := OracleComputations.inFP_compose i _ G
    (OracleComputations.inFP_post i _ prepareG (OracleComputations.inFP_retain i call hc) prepareG_poly) hG
  refine ⟨H,b,a,hH,hb,?_⟩
  intro x
  have hfirst : call (tup [x,a x.length])=f x := by
    simpa only [call,prepareF,a,field,TupleCodec.decode_tup,List.getD_cons_zero,List.getD_cons_succ] using hsf x
  change G (prepareG (tup [tup [x,a x.length],call (tup [x,a x.length])]))=g (f x)
  rw [hfirst]
  have hsecond : prepareG (tup [tup [x,a x.length],f x])=tup [f x,ag (f x).length] := by
    simp only [prepareG,a,field,TupleCodec.decode_tup,List.getD_cons_zero,List.getD_cons_succ]
    rw [adviceTable_get ag (p.eval x.length) (f x).length (hp x)]
  rw [hsecond,hsg]


theorem deltaPoly_iff_advice_boolean (i : ℕ) (L : Language) :
    L∈DeltaPoly i ↔ ∃ f : Word → Word,InFPAdvice i f ∧ ∀ x,x∈L ↔ (f x).headD false=true := by
  constructor
  · rintro ⟨O,M,p,b,a,hO,htotal,hb,hL⟩
    let F := fun s => [(M.result O s (p.eval s.length)).getD false]
    obtain ⟨C,hC,B,htrace⟩ := NativeCPU.native_protocol M p true
    have hf : OracleComputations.Computes O F := by
      apply OracleComputations.of_protocol C hC.tidy O F p B
      intro s
      refine ⟨p.eval s.length,le_rfl,?_⟩
      simpa only [NativeCPU.nativeOutput,Bool.true_eq,↓reduceIte] using htrace O s
    refine ⟨fun x => F (tup [x,a x.length]),⟨F,b,a,
      (OracleComputations.inFP_iff i F).mpr ⟨O,hO,hf⟩,hb,fun _ => rfl⟩,?_⟩
    intro x
    simpa only [F,List.headD_cons,getD_true_iff] using hL x
  · rintro ⟨f,⟨G,b,a,hG,hb,hs⟩,hL⟩
    obtain ⟨O,hO,M,p,hM⟩ := (OracleComputations.inFP_iff i G).mp hG
    refine ⟨O,M,p,b,a,hO,?_,hb,?_⟩
    · intro s
      rw [(hM s).1]
      rfl
    · intro x
      rw [(hM _).1,hs x]
      simpa only [Option.some.injEq] using hL x


theorem retain (i : ℕ) (f : Word → Word) (hf : InFPAdvice i f) :
    InFPAdvice i (fun x => tup [x,f x]) := by
  obtain ⟨G,b,a,hG,hb,hs⟩ := hf
  refine ⟨fun s => tup [field s 0,G s],b,a,
    OracleProducts.pair_inFP i _ G (pure_inFP i _ (field_poly 0)) hG,hb,?_⟩
  intro x
  simp only [field,TupleCodec.decode_tup,List.getD_cons_zero,hs]

theorem pair (i : ℕ) (f g : Word → Word) (hf : InFPAdvice i f) (hg : InFPAdvice i g) :
    InFPAdvice i (fun x => tup [f x,g x]) := by
  have hcall : InFPAdvice i (fun s => g (field s 0)) := compose i _ g
    (uniform i _ (pure_inFP i _ (field_poly 0))) hg
  have hboth := compose i _ _ (retain i f hf) (retain i _ hcall)
  have h := post i _ OracleProducts.pairPost hboth
    (pure_inFP i _ OracleProducts.pairPost_poly)
  convert h using 1
  funext x
  simp [OracleProducts.pairPost,field,TupleCodec.decode_tup]

end StudentTeacher976.Adaptivity.AdviceComputations
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceDeltaBridge
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceComputations (InFPAdvice)

theorem deltaPoly_of_advice_computation (i : ℕ) (L : Language) (F : Word → Word)
    (hF : InFPAdvice i F) (b : Polynomial ℕ)
    (ha : ∀ n : ℕ,∃ a : Word,a.length ≤ b.eval n ∧
      ∀ x : Word,x.length=n → (x∈L ↔ (F (tup [x,a])).headD false=true)) : L∈DeltaPoly i := by
  classical
  choose a hlen hspec using ha
  let input := fun x => tup [x,a x.length]
  have hi : InFPAdvice i input := ⟨id,b,a,pure_inFP i id ComputableTidilyInPolyTime.id',hlen,fun _ => rfl⟩
  have hd := AdviceComputations.compose i input F hi hF
  exact (AdviceComputations.deltaPoly_iff_advice_boolean i L).mpr
    ⟨fun x => F (input x),hd,fun x => hspec x.length x rfl⟩

end StudentTeacher976.Adaptivity.AdviceDeltaBridge
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceIteration
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)
open AdviceComputations (InFPAdvice adviceTable)

def argument (s : Word) : Word :=
  tup [field s 1,(TupleCodec.decodeTuple (field (field s 0) 1)).getD (field s 1).length []]
def post (B : Polynomial ℕ) (s : Word) : Word :=
  tup [field s 0,(field s 1).take (B.eval (field (field s 0) 0).length)]
def step (G : Word → Word) (B : Polynomial ℕ) (s : Word) : Word :=
  post B (tup [field s 0,G (argument s)])
def prepare (prep : Word → ℕ × Word) (s : Word) : ℕ × Word :=
  ((prep (field s 0)).1,tup [s,(prep (field s 0)).2])

theorem argument_poly : ComputableTidilyInPolyTime argument encBits encBits := by
  have h0 := field_poly 0
  have h1 := field_poly 1
  have hd := TupleCodec.decoder_poly.tidy.comp (h1.comp h0)
  have hn := ComputableTidilyInPolyTime.length_bits.comp h1
  have hl := (ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []).comp (hd.prod hn)
  unfold argument
  apply TupleCodec.encode_poly.comp
  fun_prop

theorem post_poly (B : Polynomial ℕ) : ComputableTidilyInPolyTime (post B) encBits encBits := by
  have h0 := field_poly 0
  have h1 := field_poly 1
  have hn := ComputableTidilyInPolyTime.length_bits.comp (h0.comp h0)
  have hb := (ComputableTidilyInPolyTime.unary_eval B).comp hn
  unfold post
  apply TupleCodec.encode_poly.comp
  fun_prop

theorem step_uniform (i : ℕ) (G : Word → Word) (hG : InFP i G) (B : Polynomial ℕ) :
    InFP i (step G B) :=
  OracleComputations.inFP_post i _ (post B)
    (OracleProducts.pair_inFP i _ _ (pure_inFP i _ (field_poly 0))
      (OracleComputations.inFP_compose i argument G (pure_inFP i _ argument_poly) hG)) (post_poly B)

theorem prepare_poly (prep : Word → ℕ × Word)
    (hp : ComputableTidilyInPolyTime prep encBits (encPair encUnary encBits)) :
    ComputableTidilyInPolyTime (prepare prep) encBits (encPair encUnary encBits) := by
  have h := hp.comp (field_poly 0)
  have hs := h.snd'
  have he : ComputableTidilyInPolyTime (fun s => tup [s,(prep (field s 0)).2]) encBits encBits := by
    apply TupleCodec.encode_poly.comp
    fun_prop
  exact h.fst'.prod he

theorem step_encoded (G : Word → Word) (B : Polynomial ℕ) (c w : Word) :
    step G B (tup [c,w])=
      tup [c,(G (tup [w,(TupleCodec.decodeTuple (field c 1)).getD w.length []])).take (B.eval (field c 0).length)] := by
  simp [step,post,argument,field,TupleCodec.decode_tup]

theorem orbit_encoded (G : Word → Word) (B : Polynomial ℕ) (c w : Word)
    (hw : w.length ≤ B.eval (field c 0).length) (j : ℕ) :
    ∃ v : Word,v.length ≤ B.eval (field c 0).length ∧ (step G B)^[j] (tup [c,w])=tup [c,v] := by
  induction j with
  | zero => exact ⟨w,hw,rfl⟩
  | succ j ih =>
    obtain ⟨v,hv,he⟩ := ih
    rw [Function.iterate_succ_apply',he,step_encoded]
    exact ⟨_,by simp only [List.length_take];omega,rfl⟩

theorem iterate_correct (f G : Word → Word) (a : ℕ → Word)
    (hG : ∀ w,G (tup [w,a w.length])=f w)
    (prep : Word → ℕ × Word) (B : Polynomial ℕ)
    (horbit : ∀ x : Word,∀ j ≤ (prep x).1,(f^[j] (prep x).2).length ≤ B.eval x.length)
    (x : Word) (j : ℕ) (hj : j ≤ (prep x).1) :
    (step G B)^[j] (tup [tup [x,adviceTable a (B.eval x.length)],(prep x).2])=
      tup [tup [x,adviceTable a (B.eval x.length)],f^[j] (prep x).2] := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih (by omega),step_encoded]
    simp only [field,TupleCodec.decode_tup,List.getD_cons_zero,List.getD_cons_succ]
    rw [AdviceComputations.adviceTable_get a (B.eval x.length) _ (horbit x j (by omega)),hG]
    rw [List.take_of_length_le (by simpa only [Function.iterate_succ_apply'] using horbit x (j+1) hj)]
    rw [Function.iterate_succ_apply']

theorem bounded_iteration (i : ℕ) (f : Word → Word) (hf : InFPAdvice i f)
    (prep : Word → ℕ × Word)
    (hp : ComputableTidilyInPolyTime prep encBits (encPair encUnary encBits))
    (B : Polynomial ℕ)
    (horbit : ∀ x : Word,∀ j ≤ (prep x).1,(f^[j] (prep x).2).length ≤ B.eval x.length) :
    InFPAdvice i (fun x => f^[(prep x).1] (prep x).2) := by
  obtain ⟨G,b,a,hG,hb,hGs⟩ := hf
  obtain ⟨E,hE⟩ := (field_poly 0).polyBounded_length.exists_polynomial
  simp only [encBits_apply] at hE
  let K := 2*Polynomial.X+2*B.comp E+4
  have hbound : ∀ s : Word,∀ j ≤ (prepare prep s).1,
      ((step G B)^[j] (prepare prep s).2).length ≤ K.eval s.length := by
    intro s j hj
    obtain ⟨v,hv,he⟩ := orbit_encoded G B s (prep (field s 0)).2
      (by simpa only [Function.iterate_zero,Function.id_def] using horbit (field s 0) 0 (Nat.zero_le _)) j
    change ((step G B)^[j] (tup [s,(prep (field s 0)).2])).length ≤ _
    rw [he,AdviceEncoding.tup_pair_length]
    have hm := AdviceComputations.poly_mono B (hE s)
    simp only [K,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X,Polynomial.eval_comp]
    omega
  have hi := NativeIteration.inFP_iterate i (step G B) (step_uniform i G hG B)
    (prepare prep) (prepare_poly prep hp) K hbound
  let F := fun s => field ((step G B)^[(prepare prep s).1] (prepare prep s).2) 1
  have hF : InFP i F := OracleComputations.inFP_post i _ (fun s => field s 1) hi (field_poly 1)
  refine ⟨F,2*(B+1)*(b.comp B+1),fun n => adviceTable a (B.eval n),hF,?_,?_⟩
  · intro n
    simpa only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_ofNat,
      Polynomial.eval_one,Polynomial.eval_comp] using AdviceComputations.adviceTable_bound a b hb (B.eval n)
  · intro x
    have hfield : field (tup [x,adviceTable a (B.eval x.length)]) 0=x := by
      simp [field,TupleCodec.decode_tup]
    dsimp only [F,prepare]
    rw [hfield,iterate_correct f G a hGs prep B horbit x _ le_rfl]
    simp [field,TupleCodec.decode_tup]

end StudentTeacher976.Adaptivity.AdviceIteration
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceWordMap
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceComputations (InFPAdvice)
open OracleWordMap

theorem step_advice (i : ℕ) (F : Word → Word) (hF : InFPAdvice i F) : InFPAdvice i (step F) := by
  have ha := AdviceComputations.compose i arg F
    (AdviceComputations.uniform i _ (pure_inFP i _ arg_poly)) hF
  exact AdviceComputations.post i _ finish (AdviceComputations.retain i _ ha) (pure_inFP i _ finish_poly)

theorem uniform (i : ℕ) (F : Word → Word) (hF : InFPAdvice i F) :
    InFPAdvice i (fun s => tup ((TupleCodec.decodeTuple s).map F)) := by
  obtain ⟨p,hp⟩ := AdviceComputations.output_bound i F hF
  obtain ⟨Q,hQ⟩ := TupleCodec.decoder_poly.tidy.polyBounded_length.exists_polynomial
  simp only [encBits_apply] at hQ
  have hi := AdviceIteration.bounded_iteration i (step F) (step_advice i F hF) prep prep_poly
    (4*Q*(Q+p.comp Q+2)+4) (orbit_bound F p hp Q hQ)
  have he : (fun s => post ((step F)^[(prep s).1] (prep s).2))=
      (fun s => tup ((TupleCodec.decodeTuple s).map F)) := by
    funext s
    unfold prep
    rw [iterate_encode F _ [] _ le_rfl]
    simp [post,done_encode]
  rw [←he]
  exact AdviceComputations.post i _ post hi (pure_inFP i _ post_poly)

def anyHead (s : Word) : Word := [(TupleCodec.decodeTuple s).any (fun w => w.headD false)]

theorem anyHead_poly : ComputableTidilyInPolyTime anyHead encBits encBits := by
  have hh := ComputableTidilyInPolyTime.headD (encA := encBool) (encL := encBits) false
  have ht := hh.comp (ComputableTidilyInPolyTime.snd encBits encBits)
  have ha := ComputableTidilyInPolyTime.anyWithInput
    (test := fun (_ : Word) w => w.headD false) TupleCodec.decoder_poly.tidy ht
  unfold anyHead
  exact ha.bitsCons (ComputableTidilyInPolyTime.const [])

theorem boolean_batch (i : ℕ) (F : Word → Word) (hF : InFPAdvice i F) :
    ∃ G : Word → Word,InFPAdvice i G ∧
      ∀ l : List Word,G (tup l)=[l.any (fun w => (F w).headD false)] := by
  refine ⟨fun s => anyHead (tup ((TupleCodec.decodeTuple s).map F)),
    AdviceComputations.post i _ anyHead (uniform i F hF) (pure_inFP i _ anyHead_poly),?_⟩
  intro l
  simp [anyHead,TupleCodec.decode_tup,List.any_map,Function.comp_def]

end StudentTeacher976.Adaptivity.AdviceWordMap
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceStudents
open QAdvFew.PoQOracle
open AdviceComputations (InFPAdvice)

def UniformStudent (i : ℕ) (f : Student) : Prop :=
  ∃ F : Word → Word,InFPAdvice i F ∧ ∀ x t H,
    F (tup [x,List.replicate (t+1) true,tup (H.map tup)])=tup (f x t H)
def UniformTupleStudent (i : ℕ) (f : TupleStudent) : Prop :=
  ∃ F : Word → Word,InFPAdvice i F ∧ ∀ X t H,
    F (NormalizationData.studentInput X t H)=tup ((f X t H).map tup)

theorem of_uniform {i : ℕ} {f : Student} (hf : StudentTeacher976.Adaptivity.UniformStudent i f) :
    UniformStudent i f := by
  obtain ⟨F,hF,hFs⟩ := hf
  exact ⟨F,AdviceComputations.uniform i F hF,hFs⟩
theorem tuple_of_uniform {i : ℕ} {f : TupleStudent} (hf : StudentTeacher976.Adaptivity.UniformTupleStudent i f) :
    UniformTupleStudent i f := by
  obtain ⟨F,hF,hFs⟩ := hf
  exact ⟨F,AdviceComputations.uniform i F hF,hFs⟩

end StudentTeacher976.Adaptivity.AdviceStudents
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceNormalization
open AdviceComputations (InFPAdvice)
open AdviceStudents (UniformTupleStudent)
open QAdvFew.PoQOracle Turing.MultiTapeTM
open OracleComputations

 theorem normalize_uniform (i : ℕ) (L : Language) (W : WitnessPresentation i L)
     (f : TupleStudent) (hf : AdviceStudents.UniformTupleStudent i f) : AdviceStudents.UniformTupleStudent i (normalize W f) := by
   obtain ⟨F,hF,hfspec⟩ := hf
   obtain ⟨O1,M,p,hO1,htotal,hW⟩ := W.efficient
   have hpos : ∀ w : Word, 0 < p.eval w.length := by
     intro w
     have ht := htotal w
     by_contra hn
     have hz : p.eval w.length = 0 := by omega
     rw [hz] at ht
     norm_num [OTM.result,OTM.runCfg,OTM.init,Fin.ext_iff,Nat.mod_eq_of_lt (show 2 < M.k+6 by omega)] at ht
   have htest : ∀ a b, NativeBatch.result M O1 p (tup [a,b])=true ↔ W.test a b := by
     intro a b
     rw [NativeBatch.result,getD_true_iff,← hW]
     constructor
     · rintro ⟨u,v,he,huv⟩
       have hh := congrArg TupleCodec.decodeTuple he
       simp only [TupleCodec.decode_tup,List.cons.injEq,and_true] at hh
       obtain ⟨rfl,rfl⟩ := hh
       exact huv
     · exact fun h => ⟨a,b,rfl,h⟩
   let G := fun s => NormalizationData.post W (s,NativeBatch.scores M O1 p (NormalizationData.prep s))
   obtain ⟨C,hC,T,B,htrace⟩ := NativeBatch.protocol M p hpos NormalizationData.prep (NormalizationData.post W)
     NormalizationData.prep_poly (NormalizationData.post_poly W)
   have hG1 : Computes O1 G := of_protocol C hC.tidy O1 G T B (htrace O1)
   let Fnorm := fun s => G (tup [s,F s])
   have hGi : InFP i G := (inFP_iff i G).mpr ⟨O1,hO1,hG1⟩
   refine ⟨Fnorm,AdviceComputations.post i _ G (AdviceComputations.retain i F hF) hGi,?_⟩
   intro X t H
   change G (tup [NormalizationData.studentInput X t H,F (NormalizationData.studentInput X t H)]) = _
   have he : F (NormalizationData.studentInput X t H) = tup ((f X t H).map tup) := hfspec X t H
   rw [he]
   exact NormalizationData.post_encoded M O1 p W f htest X t H

end StudentTeacher976.Adaptivity.AdviceNormalization
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceLoopUniform
open QAdvFew.PoQOracle
open AdviceComputations (InFPAdvice)

theorem step_advice (i : ℕ) (F T : Word → Word) (hF : InFPAdvice i F) (hT : InFP i T) :
    InFPAdvice i (AdviceLoopData.step F T) := by
  have hc := AdviceComputations.compose i AdviceLoopData.studentArgument F
    (AdviceComputations.uniform i _ (pure_inFP i _ AdviceLoopData.studentArgument_poly)) hF
  have hr := AdviceComputations.retain i _ hc
  have ht := OracleComputations.inFP_compose i AdviceLoopData.teacherArgument T
    (pure_inFP i _ AdviceLoopData.teacherArgument_poly) hT
  have hrt := OracleComputations.inFP_retain i _ ht
  have hb := AdviceComputations.post i _ _ hr hrt
  exact AdviceComputations.post i _ AdviceLoopData.finish hb
    (pure_inFP i _ AdviceLoopData.finish_poly)

end StudentTeacher976.Adaptivity.AdviceLoopUniform
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceGameAdvice
open AdviceComputations (InFPAdvice)
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceLoopSemantic

 noncomputable def replyPolynomial {i : ℕ} {L : Language} (W : WitnessPresentation i L) : Polynomial ℕ :=
   2*Polynomial.X+4*Polynomial.X*(Polynomial.X+W.length+1)+4
 theorem replyPolynomial_eval {i : ℕ} {L : Language} (W : WitnessPresentation i L) (S : ℕ) :
     (replyPolynomial W).eval S=AdviceTeacherBounds.replyBound W S := by simp [replyPolynomial,AdviceTeacherBounds.replyBound]

 theorem uniform (i : ℕ) (L : Language) (W : WitnessPresentation i L) (f : TupleStudent)
     (hf : AdviceStudents.UniformTupleStudent i f) :
     ∃ G : Word → Word, InFPAdvice i G ∧ ∀ s : Word, G s =
       [AdviceRecognizer.recognizes W f (AdviceGameData.queries s) (AdviceGameData.inputs s) (AdviceGameData.point s)
         (AdviceTeacherData.dictWitness (AdviceGameData.dictionary s)) (AdviceGameData.budget s) 0 []] := by
   obtain ⟨F,hFi,hFspec⟩ := AdviceNormalization.normalize_uniform i L W f hf
   have hF : ∀ X t H, F (NormalizationData.studentInput X t H)=tup ((normalize W f X t H).map tup) := hFspec
   obtain ⟨T,flag,hTi,hT⟩ := AdviceTeacherData.uniform_structured i L W
   let step := AdviceLoopData.step F T
   have hstepi : InFPAdvice i step := AdviceLoopUniform.step_advice i F T hFi hTi
   have hcomm (s : Word) (st : State) :
       step (encode (AdviceGameData.inputs s) (AdviceGameData.point s) (AdviceGameData.dictionary s) (AdviceGameData.queries s) st)=
       encode (AdviceGameData.inputs s) (AdviceGameData.point s) (AdviceGameData.dictionary s) (AdviceGameData.queries s)
         (advance W f (AdviceGameData.queries s) (AdviceGameData.inputs s) (AdviceGameData.point s)
           (AdviceTeacherData.dictWitness (AdviceGameData.dictionary s)) st) := by
     apply step_encode W f F T flag hF (fun s => (hT s).1) (fun s => (hT s).2.2) _ _ _ _ _ (AdviceGameData.point_mem s)
     intro G a ha hax
     exact AdviceTeacherData.witness_dict _ _ G _ a
   have hiter (s : Word) (j : ℕ) :
       step^[j] (AdviceGameData.initial s)=
       encode (AdviceGameData.inputs s) (AdviceGameData.point s) (AdviceGameData.dictionary s) (AdviceGameData.queries s)
         ((advance W f (AdviceGameData.queries s) (AdviceGameData.inputs s) (AdviceGameData.point s)
           (AdviceTeacherData.dictWitness (AdviceGameData.dictionary s)))^[j] (0,[],none)) :=
     iterate_map step _ _ (hcomm s) j (0,[],none)
   obtain ⟨P,hP⟩ := AdviceGameData.prep_poly.polyBounded_length.exists_polynomial
   let B : Polynomial ℕ := 14*(P+P+2*P*((replyPolynomial W).comp P+1)+2)
   have horbit : ∀ s : Word, ∀ j ≤ (AdviceGameData.prep s).1,
       (step^[j] (AdviceGameData.prep s).2).length ≤ B.eval s.length := by
     intro s j hj
     let S := P.eval s.length
     have hp := hP s
     simp only [encPair_apply,List.length_append,length_frame,encUnary_apply,List.length_replicate,encBits_apply] at hp
     have hk : AdviceGameData.budget s ≤ S := by dsimp [AdviceGameData.prep] at hp; omega
     have hinit : (AdviceGameData.initial s).length ≤ S := by dsimp [AdviceGameData.prep] at hp; omega
     obtain ⟨hXc,hxc,hDc,hq,hX,hXa,hwit⟩ := SerializationBounds.static_bounds _ _ _ _ S hinit
     have hinv := AdviceLoopBounds.invariant_iterate W f (AdviceGameData.queries s) (AdviceGameData.inputs s) (AdviceGameData.point s)
       (AdviceTeacherData.dictWitness (AdviceGameData.dictionary s)) S hX hXa hwit j
     have hjS : j ≤ S := hj.trans hk
     have hi : AdviceLoopBounds.Invariant W S S
         ((advance W f (AdviceGameData.queries s) (AdviceGameData.inputs s) (AdviceGameData.point s)
           (AdviceTeacherData.dictWitness (AdviceGameData.dictionary s)))^[j] (0,[],none)) :=
       ⟨hinv.1.trans hjS,hinv.2.1.trans hjS,hinv.2.2⟩
     have hb := AdviceLoopBounds.encode_bound W _ _ _ _ S S S hXc hxc hDc hq _ hi
     change (step^[j] (AdviceGameData.initial s)).length ≤ _
     rw [hiter]
     have hBeval : B.eval s.length=14*(S+S+2*S*(AdviceTeacherBounds.replyBound W S+1)+2) := by
       simp [B,S,replyPolynomial_eval]
     rw [hBeval]
     exact hb
   have hloop := AdviceIteration.bounded_iteration i step hstepi AdviceGameData.prep AdviceGameData.prep_poly B horbit
   let G := fun s => AdviceGameData.finalBit (step^[(AdviceGameData.prep s).1] (AdviceGameData.prep s).2)
   refine ⟨G,AdviceComputations.post i _ AdviceGameData.finalBit hloop (pure_inFP i _ AdviceGameData.finalBit_poly),?_⟩
   intro s
   unfold G AdviceGameData.prep
   rw [hiter,AdviceGameData.finalBit_encode,iterate_recognizes]

end StudentTeacher976.Adaptivity.AdviceGameAdvice
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceDecisionAdvice
open AdviceComputations (InFPAdvice)
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceDecisionData

 noncomputable def gameFlag {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent) (v : Word) : Bool :=
   AdviceRecognizer.recognizes W f (AdviceGameData.queries v) (AdviceGameData.inputs v) (AdviceGameData.point v)
     (AdviceTeacherData.dictWitness (AdviceGameData.dictionary v)) (AdviceGameData.budget v) 0 []
 theorem uniform (i : ℕ) (L : Language) (W : WitnessPresentation i L) (f : TupleStudent)
     (hf : AdviceStudents.UniformTupleStudent i f) (q : ℕ → ℕ) (hq : PolyTimeLength q) :
     ∃ F : Word → Word, InFPAdvice i F ∧ ∀ s : Word, (F s).headD false=true ↔
       (∃ v ∈ games q s, gameFlag W f v=true) ∨ ValidWitness W (input s) (lookup s) := by
   obtain ⟨G,hGi,hG⟩ := AdviceGameAdvice.uniform i L W f hf
   obtain ⟨H,hHi,hH⟩ := AdviceWordMap.boolean_batch i G hGi
   let cover := fun s => H (gameArgument q s)
   have hcoveri : InFPAdvice i cover := AdviceComputations.compose i (gameArgument q) H (AdviceComputations.uniform i _ (pure_inFP i _ (gameArgument_poly q hq))) hHi
   have hcover (s : Word) : cover s=[(games q s).any (gameFlag W f)] := by
     unfold cover gameArgument
     rw [hH]
     congr 1
     apply congrArg (fun p : Word → Bool => (games q s).any p)
     funext v
     rw [hG]
     rfl
   obtain ⟨T,flag,hTi,hT⟩ := AdviceTeacherData.uniform_structured i L W
   let direct := fun s => AdviceTeacherData.field (T (directArgument s)) 0
   have hcall : InFP i (fun s => T (directArgument s)) :=
     OracleComputations.inFP_compose i directArgument T (pure_inFP i _ directArgument_poly) hTi
   have hdirecti : InFP i direct := OracleComputations.inFP_post i _ (fun s => AdviceTeacherData.field s 0) hcall (AdviceTeacherData.field_poly 0)
   have hdirect (s : Word) : direct s=[flag (directArgument s)] := by
     unfold direct
     rw [(hT (directArgument s)).1]
     simp [AdviceTeacherData.field,TupleCodec.decode_tup]
   have hflag (s : Word) : flag (directArgument s)=true ↔ ValidWitness W (input s) (lookup s) := by
     have hh := (hT (directArgument s)).2.2 (by simp [direct_inputs,direct_target])
     simpa only [direct_target,direct_guesses,direct_index,List.mem_singleton,exists_eq_left,List.getD_cons_zero] using hh
   let F := fun s => [(cover s).headD false || (direct s).headD false]
   have hpair := AdviceComputations.pair i cover direct hcoveri (AdviceComputations.uniform i direct hdirecti)
   have hFi := AdviceComputations.post i _ OracleProducts.orPost hpair (pure_inFP i _ OracleProducts.orPost_poly)
   have he : F=(fun s => OracleProducts.orPost (tup [cover s,direct s])) := by
     funext s
     simp [F,OracleProducts.orPost,AdviceTeacherData.field,TupleCodec.decode_tup]
   rw [←he] at hFi
   refine ⟨F,hFi,?_⟩
   intro s
   simp [F,hcover,hdirect,hflag,List.any_eq_true]

end StudentTeacher976.Adaptivity.AdviceDecisionAdvice
end

section
set_option autoImplicit false
open scoped BigOperators Classical

namespace StudentTeacher976.Adaptivity

/-- The counting step on p.20, before the iterative advice cover. -/
theorem dense_good_subset {α : Type*} [DecidableEq α] (U : Finset α)
    (k : ℕ) (hk : 0 < k) (hku : k ≤ U.card)
    (G : Finset α → α → Prop)
    (hgood : ∀ V ⊆ U, V.card = k → ∃ x ∈ V, G (V.erase x) x) :
    ∃ S ⊆ U, S.card = k - 1 ∧
      U.card - k + 1 ≤ k * (U.filter fun x => x ∉ S ∧ G S x).card := by
  classical
  let A := U.powersetCard (k - 1)
  let C := fun S : Finset α => U.filter fun x => x ∉ S ∧ G S x
  have hA : A.Nonempty := Finset.powersetCard_nonempty.mpr (by omega)
  obtain ⟨S, hS, hmax⟩ := A.exists_max_image (fun S => (C S).card) hA
  have hScard : S.card = k - 1 := (Finset.mem_powersetCard.mp hS).2
  have hSsub : S ⊆ U := (Finset.mem_powersetCard.mp hS).1
  let P := A.sigma C
  have hsurj : Set.SurjOn (fun p : (T : Finset α) × α => insert p.2 p.1)
      (P : Set ((T : Finset α) × α)) (U.powersetCard k : Set (Finset α)) := by
    intro V hV
    obtain ⟨hVU, hVk⟩ := Finset.mem_powersetCard.mp hV
    obtain ⟨x, hx, hG⟩ := hgood V hVU hVk
    refine ⟨⟨V.erase x, x⟩, ?_, Finset.insert_erase hx⟩
    simp only [P, Finset.mem_coe, Finset.mem_sigma, A, C, Finset.mem_powersetCard,
      Finset.mem_filter]
    exact ⟨⟨(Finset.erase_subset x V).trans hVU, by simp [Finset.card_erase_of_mem hx, hVk]⟩,
      hVU hx, Finset.notMem_erase x V, hG⟩
  have hcount : U.card.choose k ≤ A.card * (C S).card := by
    calc
      U.card.choose k = (U.powersetCard k).card := (Finset.card_powersetCard _ _).symm
      _ ≤ P.card := Finset.card_le_card_of_surjOn _ hsurj
      _ = ∑ T ∈ A, (C T).card := Finset.card_sigma _ _
      _ ≤ ∑ _T ∈ A, (C S).card := Finset.sum_le_sum fun T hT => hmax T hT
      _ = A.card * (C S).card := by simp
  have hidentity : U.card.choose k * k = U.card.choose (k - 1) * (U.card - k + 1) := by
    have hchoose := Nat.choose_succ_right_eq U.card (k - 1)
    rw [show U.card - (k - 1) = U.card - k + 1 by omega] at hchoose
    simpa [Nat.sub_add_cancel hk] using hchoose
  have hApos : 0 < U.card.choose (k - 1) := Nat.choose_pos (by omega)
  refine ⟨S, hSsub, hScard, ?_⟩
  have hm := Nat.mul_le_mul_right k hcount
  rw [hidentity] at hm
  have hcardA : A.card = U.card.choose (k - 1) := Finset.card_powersetCard _ _
  rw [hcardA] at hm
  nlinarith

private theorem contraction_step {α : Type*} [DecidableEq α] (U : Finset α)
    (k : ℕ) (hk : 0 < k) (hku : k ≤ U.card) (G : Finset α → α → Prop)
    (hgood : ∀ V ⊆ U, V.card = k → ∃ x ∈ V, G (V.erase x) x) :
    ∃ S D : Finset α, S ⊆ U ∧ S.card = k - 1 ∧ D ⊆ U ∧
      (∀ x ∈ D, x ∈ S ∨ G S x) ∧
      k * (U \ D).card ≤ (k - 1) * U.card := by
  classical
  obtain ⟨S, hSU, hS, hden⟩ := dense_good_subset U k hk hku G hgood
  let C := U.filter fun x => x ∉ S ∧ G S x
  let D := S ∪ C
  have hDU : D ⊆ U := Finset.union_subset hSU (Finset.filter_subset _ _)
  have hdis : Disjoint S C := by
    rw [Finset.disjoint_left]
    intro x hx hxC
    exact (Finset.mem_filter.mp hxC).2.1 hx
  have hDcard : D.card = (k - 1) + C.card := by
    rw [Finset.card_union_of_disjoint hdis, hS]
  have hsum := Finset.card_sdiff_add_card_eq_card hDU
  refine ⟨S, D, hSU, hS, hDU, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_filter.mp h).2.2
  · dsimp [C] at hDcard
    have hkadd : k - 1 + 1 = k := by omega
    have hN : U.card - k + 1 + (k - 1) = U.card := by omega
    nlinarith [Nat.zero_le ((k - 1) * (k - 1))]

private theorem ratio_pow_le_half (k : ℕ) (hk : 0 < k) :
    (((k : ℝ) - 1) / k) ^ k ≤ (1 / 2 : ℝ) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases hk1 : k = 1
  · simp [hk1]
  have hkbig : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  let a : ℝ := 1 / ((k : ℝ) - 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ a by linarith) k
  have hbig : (2 : ℝ) ≤ (1 + a) ^ k := by
    have hka : (1 : ℝ) ≤ (k : ℝ) * a := by
      dsimp [a]
      rw [← mul_div_assoc, mul_one]
      exact (le_div_iff₀ (by linarith)).mpr (by linarith)
    linarith
  have hmul : (((k : ℝ) - 1) / k) * (1 + a) = 1 := by
    dsimp [a]
    field_simp [ne_of_gt hkreal, sub_ne_zero.mpr (ne_of_gt hkbig)]
    <;> ring
  have hp := congrArg (fun x : ℝ => x ^ k) hmul
  rw [mul_pow, one_pow] at hp
  have hnon : 0 ≤ (((k : ℝ) - 1) / k) ^ k := by positivity
  nlinarith

 theorem polynomial_good_pair_cover {α : Type*} [DecidableEq α]
    (U : Finset α) (n k : ℕ) (hk : 0 < k) (hU : U.card ≤ 2 ^ n)
    (G : Finset α → α → Prop)
    (hgood : ∀ V ⊆ U, V.card = k → ∃ x ∈ V, G (V.erase x) x) :
    ∃ A : List (Finset α), ∃ R : Finset α,
      A.length ≤ k * (n + 1) ∧
      (∀ S ∈ A, S ⊆ U ∧ S.card = k - 1) ∧ R ⊆ U ∧ R.card < k ∧
      ∀ x ∈ U, x ∈ R ∨ ∃ S ∈ A, x ∈ S ∨ G S x := by
  classical
  let rho : ℝ := ((k : ℝ) - 1) / k
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hrho : 0 ≤ rho := by
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact div_nonneg (by linarith) hkreal.le
  have hind : ∀ t : ℕ, ∃ A : List (Finset α), ∃ R : Finset α,
      A.length ≤ t ∧ (∀ S ∈ A, S ⊆ U ∧ S.card = k - 1) ∧ R ⊆ U ∧
      (∀ x ∈ U, x ∈ R ∨ ∃ S ∈ A, x ∈ S ∨ G S x) ∧
      (R.card < k ∨ (R.card : ℝ) ≤ rho ^ t * U.card) := by
    intro t
    induction t with
    | zero => exact ⟨[], U, by simp, by simp, Finset.Subset.refl _,
        fun x hx => Or.inl hx, Or.inr (by simp)⟩
    | succ t ih =>
      obtain ⟨A, R, hA, hAS, hRU, hcover, hsize⟩ := ih
      by_cases hsmall : R.card < k
      · exact ⟨A, R, by omega, hAS, hRU, hcover, Or.inl hsmall⟩
      have hbound : (R.card : ℝ) ≤ rho ^ t * U.card := hsize.resolve_left hsmall
      obtain ⟨S, D, hSR, hS, hDR, hD, hcontract⟩ :=
        contraction_step R k hk (by omega) G (fun V hVR => hgood V (hVR.trans hRU))
      refine ⟨S :: A, R \ D, by simpa using (show A.length + 1 ≤ t + 1 by omega), ?_,
        (Finset.sdiff_subset).trans hRU, ?_, Or.inr ?_⟩
      · intro T hT
        rcases List.mem_cons.mp hT with rfl | hT
        · exact ⟨hSR.trans hRU, hS⟩
        · exact hAS T hT
      · intro x hx
        rcases hcover x hx with h | h
        · by_cases hxD : x ∈ D
          · exact Or.inr ⟨S, List.mem_cons_self, hD x hxD⟩
          · exact Or.inl (Finset.mem_sdiff.mpr ⟨h, hxD⟩)
        · obtain ⟨T, hT, hxT⟩ := h
          exact Or.inr ⟨T, List.mem_cons_of_mem _ hT, hxT⟩
      · have hc : (k : ℝ) * (R \ D).card ≤ ((k : ℝ) - 1) * R.card := by
          have hc' : k * (R \ D).card ≤ (k - 1) * R.card := hcontract
          have hcast : (k : ℝ) * (R \ D).card ≤ ((k - 1 : ℕ) : ℝ) * R.card := by exact_mod_cast hc'
          simpa [Nat.cast_sub (show 1 ≤ k by omega)] using hcast
        have hrnew : ((R \ D).card : ℝ) ≤ rho * R.card := by
          dsimp [rho]
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ hkreal).mpr
          nlinarith
        calc
          ((R \ D).card : ℝ) ≤ rho * R.card := hrnew
          _ ≤ rho * (rho ^ t * U.card) := mul_le_mul_of_nonneg_left hbound hrho
          _ = rho ^ (t + 1) * U.card := by rw [pow_succ]; ring
  obtain ⟨A, R, hA, hAS, hRU, hcover, hsize⟩ := hind (k * (n + 1))
  refine ⟨A, R, hA, hAS, hRU, ?_, hcover⟩
  rcases hsize with hsmall | hbound
  · exact hsmall
  · have hbase : rho ^ k ≤ (1 / 2 : ℝ) := ratio_pow_le_half k hk
    have hpow : rho ^ (k * (n + 1)) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (pow_nonneg hrho _) hbase _
    have hUreal : (U.card : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hU
    have hhalf : (R.card : ℝ) ≤ 1 / 2 := by
      calc
        (R.card : ℝ) ≤ rho ^ (k * (n + 1)) * U.card := hbound
        _ ≤ (1 / 2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n :=
          mul_le_mul hpow hUreal (by positivity) (by positivity)
        _ = 1 / 2 := by rw [pow_succ, div_pow]; field_simp; ring
    have hlt : (R.card : ℝ) < 1 := by linarith
    have : R.card < 1 := by exact_mod_cast hlt
    omega

end StudentTeacher976.Adaptivity
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.UnrestrictedGoodPair

theorem exists_good_pair {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (n k q : ℕ) (f : TupleStudent)
    (hshape : TupleStudentShape W n k q f)
    (hsolve : TupleStudentWins W n k q (normalize W f))
    (V : Finset Word) (hV : ∀ x∈V,x∈positiveInputs W n) (hcard : V.card=k) :
    ∃ x∈V,GoodPair W n k q f (V.erase x) x := by
  classical
  let X := V.sort (· ≤ ·)
  have hX : TupleShape n k X := by
    refine ⟨by simp [X, hcard], ?_⟩
    intro x hx
    exact (hV x (by simpa [X] using hx)).1
  let Z := fixedTrace W f (q) X k
  let B : Finset Word := (Z.map fun z => X.getD z.1 []).toFinset
  have hshort : Z.length < k := AdviceSemantic.trace_short W f n k _ X hX hshape hsolve
  have hBcard : B.card < V.card := by
    calc
      B.card ≤ (Z.map fun z => X.getD z.1 []).length := List.toFinset_card_le _
      _ = Z.length := by simp
      _ < V.card := by omega
  obtain ⟨x, hxV, hxB⟩ := Finset.exists_mem_notMem_of_card_lt_card hBcard
  refine ⟨x, hxV, ?_⟩
  have hinput : orderedInput (V.erase x) x = X := by
    simp [orderedInput, Finset.insert_erase hxV, X]
  refine ⟨by simp [Finset.card_erase_of_mem hxV, hcard], ?_, hV x hxV,
    Finset.notMem_erase x V, ?_⟩
  · intro y hy
    exact hV y (Finset.mem_of_mem_erase hy)
  · intro z hz heq
    rw [hinput] at hz heq
    apply hxB
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨z, hz, heq⟩)


theorem words_length (n : ℕ) : (wordsOfLength n).length=2^n := by
  induction n with
  | zero => simp [wordsOfLength]
  | succ n ih => simp [wordsOfLength,ih,pow_succ];omega

theorem cover {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (n k q : ℕ) (hk : 0 < k) (f : TupleStudent)
    (hshape : TupleStudentShape W n k q f)
    (hsolve : TupleStudentWins W n k q (normalize W f))
    (U : Finset Word) (hU : ∀ x,x∈U ↔ x∈positiveInputs W n) :
    ∃ A : List (Finset Word),∃ R : Finset Word,
      A.length ≤ k*(n+1) ∧ (∀ S∈A,S⊆U ∧ S.card=k-1) ∧ R⊆U ∧ R.card < k ∧
      ∀ x∈U,x∈R ∨ ∃ S∈A,x∈S ∨ GoodPair W n k q f S x := by
  classical
  have hcard : U.card ≤ 2^n := by
    calc
      U.card ≤ (wordsOfLength n).toFinset.card := Finset.card_le_card (by
        intro x hx
        exact List.mem_toFinset.mpr ((AdviceSemantic.words_spec n x).mpr ((hU x).mp hx).1))
      _ ≤ (wordsOfLength n).length := List.toFinset_card_le _
      _ = 2^n := words_length n
  apply polynomial_good_pair_cover U n k hk hcard
  intro V hVU hVk
  exact exists_good_pair W n k q f hshape hsolve V (fun x hx => (hU x).mp (hVU hx)) hVk

end StudentTeacher976.Adaptivity.UnrestrictedGoodPair
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CanonicalAdviceWithAdvice
open QAdvFew.PoQOracle

 noncomputable def positiveSet {i : ℕ} {L : Language} (W : WitnessPresentation i L) (n : ℕ) : Finset Word := by
   classical
   exact (wordsOfLength n).toFinset.filter (fun x => ∃ w, ValidWitness W x w)
 theorem positiveSet_spec {i : ℕ} {L : Language} (W : WitnessPresentation i L) (n : ℕ) (x : Word) :
     x ∈ positiveSet W n ↔ x ∈ positiveInputs W n := by
   classical
   simp [positiveSet,positiveInputs,AdviceSemantic.words_spec]

 theorem canonical_advice (i : ℕ) (L : Language) (W : WitnessPresentation i L)
     (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
     (f : TupleStudent) (hf : AdviceStudents.UniformTupleStudent i f)
     (hstudents : ∀ n k : ℕ, 0 < n → 0 < k → k=resource r (n*k) →
       TupleStudentShape W n k (resource q (n*k)) f ∧
       TupleStudentWins W n k (resource q (n*k)) (normalize W f))
     (hpoints : ∃ d : ℕ, ∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ k ≤ (n+1)^d ∧ k=r (n*k)) :
     L ∈ DeltaPoly i := by
   classical
   obtain ⟨d,hpoints⟩ := hpoints
   obtain ⟨F,hFi,hF⟩ := AdviceDecisionAdvice.uniform i L W f hf q hq.1
   apply AdviceDeltaBridge.deltaPoly_of_advice_computation i L F hFi (AdviceEncoding.bound W d)
   intro n
   by_cases hn0 : n=0
   · subst n
     let R := positiveSet W 0
     have hRcard : R.card ≤ 1 := by
       calc
         R.card ≤ (wordsOfLength 0).toFinset.card := Finset.card_filter_le _ _
         _ = 1 := by simp [wordsOfLength]
     have hRpos : ∀ a ∈ R, a ∈ positiveInputs W 0 := fun a ha => (positiveSet_spec W 0 a).mp ha
     refine ⟨AdviceEncoding.encode W 1 [] R,?_,?_⟩
     · exact AdviceEncoding.polynomial_size W d 0 1 (by omega) (by simp) [] R (by simp) (by simp) hRcard (by simp) hRpos
     · intro x hlen
       constructor
       · intro hx
         have hp : x ∈ positiveInputs W 0 := ⟨hlen,(W.represents x).mp hx⟩
         have hRx : x ∈ R := (positiveSet_spec W 0 x).mpr hp
         apply (hF _).mpr
         right
         rw [AdviceDecisionData.input_encoded,AdviceDecisionData.lookup_encoded W 1 [] R x
           (AdviceDecisionSemantic.keys_residual [] R hRx)]
         exact AdviceEncoding.wit_valid W x hp.2
       · intro hx
         have hh := AdviceDecisionSemantic.decision_sound W f q F hF _ hx
         simpa only [AdviceDecisionData.input_encoded] using hh
   · have hn : 0 < n := by omega
     obtain ⟨k,hk,hkd,hkeq⟩ := hpoints n hn
     have hnk : 0 < n*k := Nat.mul_pos hn hk
     have hsize : k=resource r (n*k) := by
       unfold resource
       rw [Nat.max_eq_right (show 1 ≤ n*k by omega)]
       exact hkeq
     obtain ⟨hshape,hwin⟩ := hstudents n k hn hk hsize
     let U := positiveSet W n
     have hU : ∀ x, x ∈ U ↔ x ∈ positiveInputs W n := positiveSet_spec W n
     obtain ⟨A,R,hAlen,hAS,hRU,hRcard,hcover⟩ :=
       UnrestrictedGoodPair.cover W n k (resource q (n*k)) hk f hshape hwin U hU
     have hAcard : ∀ S ∈ A, S.card ≤ k := by
       intro S hS
       rw [(hAS S hS).2]
       exact Nat.sub_le _ _
     have hApos : ∀ S ∈ A, ∀ a ∈ S, a ∈ positiveInputs W n := fun S hS a ha => (hU a).mp ((hAS S hS).1 ha)
     have hRpos : ∀ a ∈ R, a ∈ positiveInputs W n := fun a ha => (hU a).mp (hRU ha)
     refine ⟨AdviceEncoding.encode W k A R,?_,?_⟩
     · exact AdviceEncoding.polynomial_size W d n k hk hkd A R hAlen hAcard (Nat.le_of_lt hRcard) hApos hRpos
     · intro x hlen
       constructor
       · intro hx
         apply AdviceDecisionSemantic.decision_complete W f q F hF n k hk A R _ hshape hwin x hlen hx
         exact fun y hy => hcover y ((hU y).mpr hy)
       · intro hx
         have hh := AdviceDecisionSemantic.decision_sound W f q F hF _ hx
         simpa only [AdviceDecisionData.input_encoded] using hh

end StudentTeacher976.Adaptivity.CanonicalAdviceWithAdvice
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.RawTupleData
open QAdvFew.PoQOracle Turing.MultiTapeTM

 def rawInput (X : List Word) : Word := X.flatten
 def indexPrefix (X : List Word) (z : TupleReply) : Word :=
   List.replicate (min z.1 (rawInput X).length) true ++ List.replicate ((rawInput X).length-min z.1 (rawInput X).length) false
 def payload {i : ℕ} {L : Language} (W : WitnessPresentation i L) (X : List Word) (z : TupleReply) : Word :=
   let w := z.2.getD z.1 []
   let p := W.length.eval (rawInput X).length
   w.take p ++ List.replicate (p-w.length) false
 def rawReply {i : ℕ} {L : Language} (W : WitnessPresentation i L) (X : List Word) (z : TupleReply) : Word := indexPrefix X z ++ payload W X z
 def rawHistory {i : ℕ} {L : Language} (W : WitnessPresentation i L) (X : List Word) (H : List (List TupleReply)) : List (List Word) :=
   H.map fun B => B.map (rawReply W X)

 theorem prefix_length (X : List Word) (z : TupleReply) : (indexPrefix X z).length=(rawInput X).length := by
   simp only [indexPrefix,List.length_append,List.length_replicate]
   omega
 theorem payload_length {i : ℕ} {L : Language} (W : WitnessPresentation i L) (X : List Word) (z : TupleReply) :
     (payload W X z).length=W.length.eval (rawInput X).length := by
   simp only [payload,List.length_append,List.length_take,List.length_replicate]
   omega
 theorem rawReply_length {i : ℕ} {L : Language} (W : WitnessPresentation i L) (X : List Word) (z : TupleReply) :
     (rawReply W X z).length=(rawInput X).length+W.length.eval (rawInput X).length := by
   simp only [rawReply,List.length_append,prefix_length,payload_length]
 theorem rawIndex_eq {i : ℕ} {L : Language} (W : WitnessPresentation i L) (X : List Word) (z : TupleReply)
     (hz : z.1 ≤ (rawInput X).length) : rawIndex (rawInput X) (rawReply W X z)=z.1 := by
   unfold rawIndex rawReply
   rw [List.take_append_of_le_length (by rw [prefix_length]),← prefix_length X z,List.take_length]
   have ht : (indexPrefix X z).takeWhile id=List.replicate z.1 true := by
     unfold indexPrefix
     rw [Nat.min_eq_left hz,List.takeWhile_append_of_pos]
     · simp
     · intro b hb
       have he := (List.mem_replicate.mp hb).2
       simp [he]
   rw [ht,List.length_replicate]
 theorem rawWitness_eq {i : ℕ} {L : Language} (W : WitnessPresentation i L) (X : List Word) (z : TupleReply) (a : Word)
     (hw : (z.2.getD z.1 []).length=W.length.eval a.length) (ha : a.length ≤ (rawInput X).length) :
     rawWitness W (rawInput X) a (rawReply W X z)=z.2.getD z.1 [] := by
   have hwidth : (z.2.getD z.1 []).length ≤ W.length.eval (rawInput X).length := by
     rw [hw]
     exact NativeBatch.polyEvalMono W.length ha
   unfold rawWitness rawReply
   rw [← prefix_length X z,List.drop_left]
   simp only [payload,List.take_of_length_le hwidth]
   rw [← hw,List.take_left]

 theorem rawInput_length (n k : ℕ) (X : List Word) (hX : TupleShape n k X) :
     (rawInput X).length=n*k := by
   have h : (X.map List.length).sum = X.length*n := by
     calc
       (X.map List.length).sum = (X.map fun _ => n).sum := by
         congr 1
         exact List.map_congr_left (fun a ha => hX.2 a ha)
       _ = X.length*n := by simp
   simpa [rawInput,List.length_flatten,hX.1,Nat.mul_comm] using h

 theorem decodeBlocks_rawInput (n k : ℕ) (X : List Word) (hX : TupleShape n k X) :
     decodeBlocks n k (rawInput X)=X := by
   apply List.ext_getElem (by simp [decodeBlocks,hX.1])
   intro j hj hjX
   simp only [decodeBlocks,List.getElem_map,List.getElem_range]
   have h := NormalizationData.chunk_flatMap X [] id n j hjX hX.2
   simpa only [rawInput,List.flatMap_id,List.getD_eq_getElem _ _ hjX,id_eq] using h

 theorem blockInput_rawInput (r : ℕ → ℕ) (n k : ℕ) (hn : 0<n) (hk : 0<k)
     (hfixed : k=resource r (n*k)) (X : List Word) (hX : TupleShape n k X) :
     blockInput r (rawInput X)=some X := by
   have hlen := rawInput_length n k X hX
   have hmod : n*k%k=0 := Nat.mul_mod_left n k
   have hdiv : n*k/k=n := Nat.mul_div_cancel n hk
   simp only [blockInput,hlen,← hfixed]
   rw [if_pos ⟨Nat.mul_pos hn hk,hk,hmod⟩,hdiv,decodeBlocks_rawInput n k X hX]

 theorem rawHistory_shape {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (n k q t : ℕ) (H : List (List TupleReply))
     (hH : TupleHistoryShape W n k q t H) :
     HistoryShape t q ((rawInput X).length+W.length.eval (rawInput X).length) (rawHistory W X H) := by
   refine ⟨by simpa [rawHistory] using hH.1,?_⟩
   intro B hB
   change B ∈ H.map (fun B => B.map (rawReply W X)) at hB
   obtain ⟨B0,hB0,he⟩ := List.mem_map.mp hB
   subst B
   refine ⟨by simpa using (hH.2 B0 hB0).1,?_⟩
   intro z hz
   obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hz
   exact rawReply_length W X z

 theorem rawHistory_take {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (H : List (List TupleReply)) (t : ℕ) :
     rawHistory W X (H.take t)=(rawHistory W X H).take t := by
   simp [rawHistory,List.map_take]

 theorem rawInput_poly : ComputableTidilyInPolyTime rawInput (encList encBits) encBits :=
   ComputableTidilyInPolyTime.bitsFlatten ComputableTidilyInPolyTime.id'
 theorem rawReply_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (fun p : List Word × TupleReply => rawReply W p.1 p.2)
       (encPair (encList encBits) (encPair encUnary (encList encBits))) encBits := by
   have hx := rawInput_poly
   have hm : ComputableTidilyInPolyTime (fun p : List Word × TupleReply => (rawInput p.1).length)
       (encPair (encList encBits) (encPair encUnary (encList encBits))) encUnary := by
     exact ComputableTidilyInPolyTime.length_bits.comp (hx.comp (ComputableTidilyInPolyTime.fst (encList encBits) (encPair encUnary (encList encBits))))
   have hj : ComputableTidilyInPolyTime (fun p : List Word × TupleReply => p.2.1)
       (encPair (encList encBits) (encPair encUnary (encList encBits))) encUnary := by fun_prop
   have hi := ComputableTidilyInPolyTime.unary_min.comp (hj.prod hm)
   have htrue := (ComputableTidilyInPolyTime.encode encUnary).comp hi
   have hfalse : ComputableTidilyInPolyTime (fun p : List Word × TupleReply =>
       List.replicate ((rawInput p.1).length-min p.2.1 (rawInput p.1).length) false)
       (encPair (encList encBits) (encPair encUnary (encList encBits))) encBits := by
     apply (bits_encList_polyTime encBool).2.tidy.comp
     apply ComputableTidilyInPolyTime.replicate
     · exact ComputableTidilyInPolyTime.unary_sub.comp (hm.prod hi)
     · exact ComputableTidilyInPolyTime.const false
   have hp := (ComputableTidilyInPolyTime.unary_eval W.length).comp hm
   have hw : ComputableTidilyInPolyTime (fun p : List Word × TupleReply => p.2.2.getD p.2.1 [])
       (encPair (encList encBits) (encPair encUnary (encList encBits))) encBits := by
     apply (ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []).comp
       (g := fun p : List Word × TupleReply => (p.2.2,p.2.1))
     fun_prop
   have hpad : ComputableTidilyInPolyTime (fun p : List Word × TupleReply =>
       List.replicate (W.length.eval (rawInput p.1).length-(p.2.2.getD p.2.1 []).length) false)
       (encPair (encList encBits) (encPair encUnary (encList encBits))) encBits := by
     apply (bits_encList_polyTime encBool).2.tidy.comp
     apply ComputableTidilyInPolyTime.replicate
     · exact ComputableTidilyInPolyTime.unary_sub.comp (hp.prod (ComputableTidilyInPolyTime.length_bits.comp hw))
     · exact ComputableTidilyInPolyTime.const false
   unfold rawReply indexPrefix payload
   exact ComputableTidilyInPolyTime.bitsAppend (ComputableTidilyInPolyTime.bitsAppend htrue hfalse)
     (ComputableTidilyInPolyTime.bitsAppend (by fun_prop) hpad)

end StudentTeacher976.Adaptivity.RawTupleData
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.RawTupleCandidate
open QAdvFew.PoQOracle Turing.MultiTapeTM

 def shape {i : ℕ} {L : Language} (W : WitnessPresentation i L) (X Y : List Word) : Bool :=
   decide (Y.length=X.length) && (List.range X.length).all (fun j =>
     decide ((Y.getD j []).length=W.length.eval (X.getD j []).length))
 def fallback {i : ℕ} {L : Language} (W : WitnessPresentation i L) (X : List Word) : List Word :=
   X.map (fun x => List.replicate (W.length.eval x.length) false)
 def sanitize {i : ℕ} {L : Language} (W : WitnessPresentation i L) (X : List Word) (y : Word) : List Word :=
   match decodeTuple y with
   | none => fallback W X
   | some Y => if shape W X Y then Y else fallback W X

 theorem shape_spec {i : ℕ} {L : Language} (W : WitnessPresentation i L) (X Y : List Word) :
     shape W X Y=true ↔ Y.length=X.length ∧ ∀ j<X.length,
       (Y.getD j []).length=W.length.eval (X.getD j []).length := by
   simp [shape,List.all_eq_true,List.mem_range]
 theorem fallback_shape {i : ℕ} {L : Language} (W : WitnessPresentation i L) (X : List Word) :
     shape W X (fallback W X)=true := by
   rw [shape_spec]
   refine ⟨by simp [fallback],?_⟩
   intro j hj
   rw [List.getD_eq_getElem _ _ (by simpa [fallback] using hj),List.getD_eq_getElem _ _ hj]
   simp [fallback]
 theorem sanitize_shape {i : ℕ} {L : Language} (W : WitnessPresentation i L) (X : List Word) (y : Word) :
     shape W X (sanitize W X y)=true := by
   unfold sanitize
   split
   · exact fallback_shape W X
   · split
     · assumption
     · exact fallback_shape W X
 theorem sanitize_tupleShape {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (n k : ℕ) (X : List Word) (hX : TupleShape n k X) (y : Word) :
     TupleShape (W.length.eval n) k (sanitize W X y) := by
   obtain ⟨hlen,hcoord⟩ := (shape_spec W X _).mp (sanitize_shape W X y)
   refine ⟨hlen.trans hX.1,?_⟩
   intro a ha
   obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp ha
   have hjX : j<X.length := by omega
   have h := hcoord j hjX
   rw [List.getD_eq_getElem _ _ hj,List.getD_eq_getElem _ _ hjX] at h
   rw [h,hX.2 _ (List.getElem_mem hjX)]
 theorem sanitize_of_shape {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X Y : List Word) (hY : shape W X Y=true) : sanitize W X (tup Y)=Y := by
   simp [sanitize,AuxiliaryData.decodeTuple_encoded,hY]

 theorem shape_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (fun p : List Word × List Word => shape W p.1 p.2)
       (encPair (encList encBits) (encList encBits)) encBool := by
   have hp := ComputableTidilyInPolyTime.unary_eval W.length
   have hg := ComputableTidilyInPolyTime.listGetD (encA := encBits) (encL := encList encBits) []
   unfold shape
   apply ComputableTidilyInPolyTime.bool_and.comp (g := fun p : List Word × List Word =>
     (decide (p.2.length=p.1.length),(List.range p.1.length).all (fun j =>
       decide ((p.2.getD j []).length=W.length.eval (p.1.getD j []).length))))
   apply ComputableTidilyInPolyTime.prod
   · fun_prop
   · apply ComputableTidilyInPolyTime.allWithInput
     · fun_prop
     · fun_prop
 theorem fallback_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (fallback W) (encList encBits) (encList encBits) := by
   have hp := ComputableTidilyInPolyTime.unary_eval W.length
   unfold fallback
   apply ComputableTidilyInPolyTime.map
   apply (bits_encList_polyTime encBool).2.tidy.comp
   apply ComputableTidilyInPolyTime.replicate
   · fun_prop
   · exact ComputableTidilyInPolyTime.const false
 theorem sanitize_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (fun p : List Word × Word => sanitize W p.1 p.2)
       (encPair (encList encBits) encBits) (encList encBits) := by
   have hd := AuxiliaryData.decode_poly
   have hs := shape_poly W
   have hf := fallback_poly W
   have hb : ComputableTidilyInPolyTime (fun p : (List Word × Word) × List Word =>
       if shape W p.1.1 p.2 then p.2 else fallback W p.1.1)
       (encPair (encPair (encList encBits) encBits) (encList encBits)) (encList encBits) := by
     apply (hs.comp (g := fun p : (List Word × Word) × List Word => (p.1.1,p.2)) (by fun_prop)).cond
     · fun_prop
     · fun_prop
   have h := ComputableTidilyInPolyTime.optionElimWithInput
     (hd.comp (ComputableTidilyInPolyTime.snd (encList encBits) encBits))
     (fallback := fun p : List Word × Word => fallback W p.1) (by fun_prop)
     (body := fun (p : List Word × Word) Y => if shape W p.1 Y then Y else fallback W p.1) hb
   convert h using 1
   funext p
   unfold sanitize
   dsimp only [Function.comp_def]
   cases decodeTuple p.2 <;> rfl

end StudentTeacher976.Adaptivity.RawTupleCandidate
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.NormalizationSemantic

 def pool (f : TupleStudent) (X : List Word) (t : ℕ) (H : List (List TupleReply)) (j : ℕ) : List Word :=
   (H.flatten.map fun z => z.2.getD j []) ++ ((f X t H).map fun Z => Z.getD j [])
 noncomputable def selected {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word) (pool : List Word) (fallback : Word) : Word := by
   classical
   exact (pool.find? fun w => decide (ValidWitness W a w)).getD fallback
 noncomputable def row {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (X : List Word) (t : ℕ) (H : List (List TupleReply)) (Y : List Word) : List Word :=
   Y.mapIdx fun j y => selected W (X.getD j []) (pool f X t H j) y
 theorem normalize_eq {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (X : List Word) (t : ℕ) (H : List (List TupleReply)) :
     normalize W f X t H = (f X t H).map (row W f X t H) := rfl
 theorem selected_cases {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word) (l : List Word) (fallback : Word) :
     selected W a l fallback = fallback ∨ ValidWitness W a (selected W a l fallback) := by
   classical
   unfold selected
   cases hh : l.find? (fun w => decide (ValidWitness W a w)) with
   | none => exact Or.inl rfl
   | some w =>
     right
     simpa only [Option.getD_some] using (show ValidWitness W a w by simpa using List.find?_some hh)
 theorem selected_valid {i : ℕ} {L : Language} (W : WitnessPresentation i L) (a : Word) (l : List Word) (fallback : Word)
     (h : ∃ w ∈ l, ValidWitness W a w) : ValidWitness W a (selected W a l fallback) := by
   classical
   have hs : (l.find? (fun w => decide (ValidWitness W a w))).isSome := by simpa [List.find?_isSome] using h
   obtain ⟨w,hw⟩ := Option.isSome_iff_exists.mp hs
   unfold selected
   rw [hw]
   simpa using List.find?_some hw
 theorem row_length {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (X : List Word) (t : ℕ) (H : List (List TupleReply)) (Y : List Word) :
     (row W f X t H Y).length = Y.length := by simp [row]
 theorem row_getD {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (X : List Word) (t : ℕ) (H : List (List TupleReply)) (Y : List Word) (j : ℕ) (hj : j < Y.length) :
     (row W f X t H Y).getD j [] = selected W (X.getD j []) (pool f X t H j) (Y.getD j []) := by
   rw [List.getD_eq_getElem _ _ (by simpa only [row_length] using hj),List.getD_eq_getElem Y [] hj]
   simp [row]
 theorem test_mono {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (X : List Word) (t : ℕ) (H : List (List TupleReply)) (Y : List Word) (hY : Y ∈ f X t H) (z : TupleReply)
     (h : TupleTest W X Y z) : TupleTest W X (row W f X t H Y) z := by
   have hlen := h.1
   refine ⟨(row_length W f X t H Y).trans h.1,?_,?_⟩
   · intro j hj
     rw [row_getD W f X t H Y j (by omega)]
     rcases selected_cases W (X.getD j []) (pool f X t H j) (Y.getD j []) with he | hv
     · rw [he]
       exact h.2.1 j hj
     · exact hv.1
   · intro hj hz
     rw [row_getD W f X t H Y z.1 (by omega)]
     apply selected_valid
     refine ⟨Y.getD z.1 [],?_,h.2.2 hj hz⟩
     exact List.mem_append_right _ (List.mem_map.mpr ⟨Y,hY,rfl⟩)

 theorem wins_normalize {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (n k q : ℕ) (hshape : TupleStudentShape W n k q f) (hwin : TupleStudentWins W n k q f) :
     TupleStudentWins W n k q (normalize W f) := by
   intro X H hX hH
   obtain ⟨t,ht,j,hj,hraw⟩ := hwin X H hX hH
   have hHp : TupleHistoryShape W n k q t (H.take t) := by
     refine ⟨by simp [List.length_take,hH.1,Nat.min_eq_left (Nat.le_of_lt ht)],?_⟩
     exact fun B hB => hH.2 B (List.mem_of_mem_take hB)
   have hlen : (f X t (H.take t)).length = q := (hshape.1 X t (H.take t) hX ht hHp).1
   have hjf : j < (f X t (H.take t)).length := by omega
   have hmem : (f X t (H.take t)).getD j [] ∈ f X t (H.take t) := by
     rw [List.getD_eq_getElem _ _ hjf]
     exact List.getElem_mem _
   refine ⟨t,ht,j,hj,?_⟩
   have he : (normalize W f X t (H.take t)).getD j [] = row W f X t (H.take t) ((f X t (H.take t)).getD j []) := by
     rw [normalize_eq,List.getD_eq_getElem _ _ (by simpa using hjf),List.getElem_map,List.getD_eq_getElem _ _ hjf]
   rw [he]
   exact test_mono W f X t (H.take t) _ hmem _ hraw

 theorem shape_normalize {i : ℕ} {L : Language} (W : WitnessPresentation i L) (f : TupleStudent)
     (n k q : ℕ) (hshape : TupleStudentShape W n k q f) : TupleStudentShape W n k q (normalize W f) := by
   constructor
   · intro X t H hX ht hH
     obtain ⟨hlen,hYs⟩ := hshape.1 X t H hX ht hH
     constructor
     · simpa only [normalize_eq,List.length_map] using hlen
     · intro Y' hY'
       rw [normalize_eq] at hY'
       obtain ⟨Y,hY,rfl⟩ := List.mem_map.mp hY'
       have hys := hYs Y hY
       have hYlen := hys.1
       have hXlen := hX.1
       have hraw : TupleTest W X Y (X.length,[]) := by
         refine ⟨hys.1.trans hX.1.symm,?_,?_⟩
         · intro j hj
           have hjY : j < Y.length := by omega
           have hya : Y.getD j [] ∈ Y := by rw [List.getD_eq_getElem _ _ hjY]; exact List.getElem_mem _
           have hxa : X.getD j [] ∈ X := by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
           rw [hys.2 _ hya,hX.2 _ hxa]
         · intro h; omega
       have htest := test_mono W f X t H Y hY _ hraw
       refine ⟨(row_length W f X t H Y).trans hys.1,?_⟩
       intro a ha
       obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp ha
       have hjX : j < X.length := by rw [row_length,hys.1] at hj; omega
       have hxa : X.getD j [] ∈ X := by rw [List.getD_eq_getElem _ _ hjX]; exact List.getElem_mem _
       have hja := htest.2.1 j hjX
       rw [List.getD_eq_getElem _ _ hj,he,hX.2 _ hxa] at hja
       exact hja
   · intro X t H hX ht
     rw [normalize_eq,hshape.2 X t H hX ht,List.map_nil]

end StudentTeacher976.Adaptivity.NormalizationSemantic
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.RawTupleSemantic
open QAdvFew.PoQOracle
open RawTupleData RawTupleCandidate

 def student {i : ℕ} {L : Language} (W : WitnessPresentation i L) (g : Student) : TupleStudent :=
   fun X t H => (g (rawInput X) t (rawHistory W X H)).map (sanitize W X)

 theorem tuple_test {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (r : ℕ → ℕ) (n k : ℕ) (hn : 0<n) (hk : 0<k) (heq : k=resource r (n*k))
     (X : List Word) (hX : TupleShape n k X) (y : Word) (z : TupleReply)
     (hz : ReplyShape W n k z)
     (ht : auxiliaryTest W r (rawInput X) y (rawReply W X z)) :
     TupleTest W X (sanitize W X y) z := by
   have hxlen := hX.1
   have hx := blockInput_rawInput r n k hn hk heq X hX
   simp only [auxiliaryTest,hx] at ht
   cases hy : decodeTuple y with
   | none => simp [hy] at ht
   | some Y =>
     simp only [hy] at ht
     have hshape : shape W X Y=true := (shape_spec W X Y).mpr ⟨ht.1,ht.2.1⟩
     have he : sanitize W X y=Y := by simp [sanitize,hy,hshape]
     rw [he]
     refine ⟨ht.1,ht.2.1,?_⟩
     intro hj hw
     have hlen := rawInput_length n k X hX
     have hjm : z.1 ≤ (rawInput X).length := by
       rw [hlen]
       have hnk : k ≤ n*k := by nlinarith
       omega
     have hxj : (X.getD z.1 []).length=n := by
       rw [List.getD_eq_getElem _ _ (by omega)]
       exact hX.2 _ (List.getElem_mem _)
     have hzj : (z.2.getD z.1 []).length=W.length.eval (X.getD z.1 []).length := by
       rw [List.getD_eq_getElem _ _ (by rw [hz.2.1]; exact hz.1),hxj]
       exact hz.2.2 _ (List.getElem_mem _)
     have hxa : (X.getD z.1 []).length ≤ (rawInput X).length := by
       rw [hxj,hlen]
       nlinarith
     have hridx := rawIndex_eq W X z hjm
     have hrwit := rawWitness_eq W X z (X.getD z.1 []) hzj hxa
     have h := ht.2.2
     rw [hridx] at h
     exact h hj (by rwa [hrwit])

 theorem shape_transfer {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (r q : ℕ → ℕ) (g : Student)
     (hlen : ∀ x t H, t<resource r x.length →
       HistoryShape t (resource q x.length) (x.length+W.length.eval x.length) H →
       (g x t H).length=resource q x.length)
     (hterm : ∀ x t H, resource r x.length≤t → g x t H=[])
     (n k : ℕ) (heq : k=resource r (n*k)) :
     TupleStudentShape W n k (resource q (n*k)) (student W g) := by
   constructor
   · intro X t H hX ht hH
     have hlenX := rawInput_length n k X hX
     refine ⟨?_,?_⟩
     · simpa only [student,List.length_map,hlenX] using hlen (rawInput X) t (rawHistory W X H)
         (by simpa only [hlenX,← heq] using ht)
         (by simpa only [hlenX] using rawHistory_shape W X n k _ t H hH)
     · intro Y hY
       obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hY
       exact sanitize_tupleShape W n k X hX y
   · intro X t H hX ht
     simp only [student,hterm (rawInput X) t (rawHistory W X H)
       (by simpa only [rawInput_length n k X hX,← heq] using ht),List.map_nil]

 theorem wins_transfer {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (r q : ℕ → ℕ) (g : Student)
     (hlen : ∀ x t H, t<resource r x.length →
       HistoryShape t (resource q x.length) (x.length+W.length.eval x.length) H →
       (g x t H).length=resource q x.length)
     (hwin : ∀ x H, HistoryShape (resource r x.length) (resource q x.length)
       (x.length+W.length.eval x.length) H → ∃ t, t<resource r x.length ∧ ∃ j,
       j<resource q x.length ∧ auxiliaryTest W r x ((g x t (H.take t)).getD j []) ((H.getD t []).getD j []))
     (n k : ℕ) (hn : 0<n) (hk : 0<k) (heq : k=resource r (n*k)) :
     TupleStudentWins W n k (resource q (n*k)) (student W g) := by
   intro X H hX hH
   have hlenX := rawInput_length n k X hX
   have hrawH : HistoryShape (resource r (rawInput X).length) (resource q (rawInput X).length)
       ((rawInput X).length+W.length.eval (rawInput X).length) (rawHistory W X H) := by
     simpa only [hlenX,← heq] using rawHistory_shape W X n k _ k H hH
   obtain ⟨t,ht,j,hj,hTest⟩ := hwin (rawInput X) (rawHistory W X H) hrawH
   have htk : t<k := by simpa only [hlenX,← heq] using ht
   have hjq : j<resource q (n*k) := by simpa only [hlenX] using hj
   have hHp : TupleHistoryShape W n k (resource q (n*k)) t (H.take t) := by
     refine ⟨by simp [hH.1,Nat.min_eq_left (Nat.le_of_lt htk)],?_⟩
     exact fun B hB => hH.2 B (List.mem_of_mem_take hB)
   have hglen : (g (rawInput X) t (rawHistory W X (H.take t))).length=resource q (n*k) := by
     simpa only [hlenX] using hlen (rawInput X) t (rawHistory W X (H.take t)) ht
       (by simpa only [hlenX] using rawHistory_shape W X n k _ t (H.take t) hHp)
   have hHt : t<H.length := by rw [hH.1]; exact htk
   have hBlen : (H.getD t []).length=resource q (n*k) :=
     (hH.2 (H.getD t []) (by rw [List.getD_eq_getElem _ _ hHt]; exact List.getElem_mem _)).1
   have hjB : j<(H.getD t []).length := by omega
   have hz : ReplyShape W n k ((H.getD t []).getD j (0,[])) :=
     (hH.2 (H.getD t []) (by rw [List.getD_eq_getElem _ _ hHt]; exact List.getElem_mem _)).2 _
       (by rw [List.getD_eq_getElem _ _ hjB]; exact List.getElem_mem _)
   have houter : (rawHistory W X H).getD t []=(H.getD t []).map (rawReply W X) := by
     simp [rawHistory,List.getD_map,hHt]
   have hrH : ((rawHistory W X H).getD t []).getD j [] =
       rawReply W X ((H.getD t []).getD j (0,[])) := by
     rw [houter]
     conv_lhs => rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hjB)]
     rw [List.getElem_map,List.getD_eq_getElem _ _ hjB]
   rw [hrH,← rawHistory_take] at hTest
   refine ⟨t,htk,j,hjq,?_⟩
   have hjg : j<(g (rawInput X) t (rawHistory W X (H.take t))).length := by omega
   have hout : (student W g X t (H.take t)).getD j [] =
       sanitize W X ((g (rawInput X) t (rawHistory W X (H.take t))).getD j []) := by
     rw [List.getD_eq_getElem _ _ (by simpa only [student,List.length_map] using hjg)]
     simp only [student,List.getElem_map,List.getD_eq_getElem _ _ hjg]
   rw [hout]
   exact tuple_test W r n k hn hk heq X hX _ _ hz hTest

end StudentTeacher976.Adaptivity.RawTupleSemantic
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.RawTupleUniform
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)
open RawTupleData RawTupleCandidate

 def inputs (s : Word) : List Word := TupleCodec.decodeTuple (field s 0)
 def replyDecoder (s : Word) : TupleReply := ((field s 0).length,TupleCodec.decodeTuple (field s 1))
 def histories (s : Word) : List (List TupleReply) :=
   (TupleCodec.decodeTuple (field s 2)).map (fun B => (TupleCodec.decodeTuple B).map replyDecoder)
 def pre {i : ℕ} {L : Language} (W : WitnessPresentation i L) (s : Word) : Word :=
   tup [rawInput (inputs s),field s 1,tup ((rawHistory W (inputs s) (histories s)).map tup)]
 def post {i : ℕ} {L : Language} (W : WitnessPresentation i L) (s : Word) : Word :=
   tup ((TupleCodec.decodeTuple (field s 1)).map (fun y => tup (sanitize W (inputs (field s 0)) y)))

 theorem inputs_poly : ComputableTidilyInPolyTime inputs encBits (encList encBits) :=
   TupleCodec.decoder_poly.tidy.comp (field_poly 0)
 theorem replyDecoder_poly : ComputableTidilyInPolyTime replyDecoder encBits
     (encPair encUnary (encList encBits)) := by
   unfold replyDecoder
   exact ((ComputableTidilyInPolyTime.length_bits.comp (field_poly 0))).prod
     (TupleCodec.decoder_poly.tidy.comp (field_poly 1))
 theorem histories_poly : ComputableTidilyInPolyTime histories encBits
     (encList (encList (encPair encUnary (encList encBits)))) := by
   unfold histories
   exact ((ComputableTidilyInPolyTime.map replyDecoder_poly).comp TupleCodec.decoder_poly.tidy).map.comp
     (TupleCodec.decoder_poly.tidy.comp (field_poly 2))
 theorem rawHistory_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (fun p : List Word × List (List TupleReply) => rawHistory W p.1 p.2)
       (encPair (encList encBits) (encList (encList (encPair encUnary (encList encBits)))) )
       (encList (encList encBits)) := by
   unfold rawHistory
   apply ComputableTidilyInPolyTime.mapWithInput (by fun_prop)
   apply ComputableTidilyInPolyTime.mapWithInput (by fun_prop)
   apply (rawReply_poly W).comp (g := fun p : ((List Word × List (List TupleReply)) × List TupleReply) × TupleReply => (p.1.1.1,p.2))
   fun_prop
 theorem pre_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (pre W) encBits encBits := by
   have hr := (rawHistory_poly W).comp (inputs_poly.prod histories_poly)
   have hh := TupleCodec.encode_poly.comp ((ComputableTidilyInPolyTime.map TupleCodec.encode_poly).comp hr)
   have hx := rawInput_poly.comp inputs_poly
   have ht := field_poly 1
   unfold pre
   apply TupleCodec.encode_poly.comp
   fun_prop
 theorem post_poly {i : ℕ} {L : Language} (W : WitnessPresentation i L) :
     ComputableTidilyInPolyTime (post W) encBits encBits := by
   have hg := TupleCodec.decoder_poly.tidy.comp (field_poly 1)
   have hx := inputs_poly.comp (field_poly 0)
   unfold post
   apply TupleCodec.encode_poly.comp
   apply ComputableTidilyInPolyTime.mapWithInput hg
   apply TupleCodec.encode_poly.comp
   apply (sanitize_poly W).comp (g := fun p : Word × Word => (inputs (field p.1 0),p.2))
   exact (hx.comp (ComputableTidilyInPolyTime.fst encBits encBits)).prod (ComputableTidilyInPolyTime.snd encBits encBits)

 theorem replyDecoder_encoded (z : TupleReply) : replyDecoder (encodeReply z)=z := by
   simp [replyDecoder,encodeReply,field,TupleCodec.decode_tup]
 theorem inputs_encoded (X : List Word) (t : ℕ) (H : List (List TupleReply)) :
     inputs (NormalizationData.studentInput X t H)=X := by
   simp [inputs,NormalizationData.studentInput,field,TupleCodec.decode_tup]
 theorem histories_encoded (X : List Word) (t : ℕ) (H : List (List TupleReply)) :
     histories (NormalizationData.studentInput X t H)=H := by
   simp [histories,NormalizationData.studentInput,field,TupleCodec.decode_tup,List.map_map,
     Function.comp_def,replyDecoder_encoded]
 theorem pre_encoded {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (t : ℕ) (H : List (List TupleReply)) :
     pre W (NormalizationData.studentInput X t H)=
       tup [rawInput X,List.replicate (t+1) true,tup ((rawHistory W X H).map tup)] := by
   unfold pre
   rw [inputs_encoded,histories_encoded]
   simp [field,NormalizationData.studentInput,TupleCodec.decode_tup]
 theorem post_encoded {i : ℕ} {L : Language} (W : WitnessPresentation i L)
     (X : List Word) (t : ℕ) (H : List (List TupleReply)) (Y : List Word) :
     post W (tup [NormalizationData.studentInput X t H,tup Y])=
       tup ((Y.map (sanitize W X)).map tup) := by
   unfold post
   simp only [field,TupleCodec.decode_tup,List.getD_cons_zero,List.getD_cons_succ]
   rw [inputs_encoded]
   simp [List.map_map,Function.comp_def]

 theorem uniform {i : ℕ} {L : Language} (W : WitnessPresentation i L) (g : Student)
     (hg : UniformStudent i g) : UniformTupleStudent i (RawTupleSemantic.student W g) := by
   obtain ⟨F,hF,hFspec⟩ := hg
   let G := fun s => F (pre W s)
   have hG : InFP i G := OracleComputations.inFP_compose i _ F (pure_inFP i _ (pre_poly W)) hF
   let T := fun s => post W (tup [s,G s])
   have hT : InFP i T := OracleComputations.inFP_post i _ (post W)
     (OracleComputations.inFP_retain i G hG) (post_poly W)
   refine ⟨T,hT,?_⟩
   intro X t H
   change post W (tup [NormalizationData.studentInput X t H,F (pre W (NormalizationData.studentInput X t H))]) = _
   rw [pre_encoded,hFspec]
   exact post_encoded W X t H _

end StudentTeacher976.Adaptivity.RawTupleUniform
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceRawTuple
open QAdvFew.PoQOracle
open AdviceComputations (InFPAdvice)
open RawTupleUniform
 theorem uniform {i : ℕ} {L : Language} (W : WitnessPresentation i L) (g : Student)
     (hg : AdviceStudents.UniformStudent i g) : AdviceStudents.UniformTupleStudent i (RawTupleSemantic.student W g) := by
   obtain ⟨F,hF,hFspec⟩ := hg
   let G := fun s => F (pre W s)
   have hG : InFPAdvice i G := AdviceComputations.compose i _ F (AdviceComputations.uniform i _ (pure_inFP i _ (pre_poly W))) hF
   let T := fun s => post W (tup [s,G s])
   have hT : InFPAdvice i T := AdviceComputations.post i _ (post W)
     (AdviceComputations.retain i G hG) (pure_inFP i _ (post_poly W))
   refine ⟨T,hT,?_⟩
   intro X t H
   change post W (tup [NormalizationData.studentInput X t H,F (pre W (NormalizationData.studentInput X t H))]) = _
   rw [pre_encoded,hFspec]
   exact post_encoded W X t H _


end StudentTeacher976.Adaptivity.AdviceRawTuple
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CanonicalRawAdviceWithAdvice
open QAdvFew.PoQOracle

 theorem canonical_raw_advice (i : ℕ) (L : Language) (W : WitnessPresentation i L)
     (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
     (P : RefutablePresentation i (auxiliaryRelation W r))
     (hP : ∀ x y z, P.test x y z ↔ auxiliaryTest W r x y z)
     (href : P.refutationLength=Polynomial.X+W.length)
     (g : Student) (hg : AdviceStudents.UniformStudent i g) (hshape : StudentShape P r q g)
     (hwin : StudentWins P r q g)
     (hpoints : ∃ d : ℕ, ∀ n : ℕ, 0<n → ∃ k : ℕ,
       0<k ∧ k≤(n+1)^d ∧ k=r (n*k)) : L ∈ DeltaPoly i := by
   have hrefeval : ∀ x : Word, P.refutationLength.eval x.length=x.length+W.length.eval x.length := by
     intro x
     simp [href]
   have hlen : ∀ x t H, t<resource r x.length →
       HistoryShape t (resource q x.length) (x.length+W.length.eval x.length) H →
       (g x t H).length=resource q x.length := by
     intro x t H ht hH
     obtain ⟨b,hb⟩ := hshape.1
     exact (hb x t H ht (by simpa only [hrefeval] using hH)).1
   have hsolve : ∀ x H, HistoryShape (resource r x.length) (resource q x.length)
       (x.length+W.length.eval x.length) H → ∃ t, t<resource r x.length ∧ ∃ j,
       j<resource q x.length ∧ auxiliaryTest W r x ((g x t (H.take t)).getD j []) ((H.getD t []).getD j []) := by
     intro x H hH
     obtain ⟨t,ht,j,hj,h⟩ := hwin x H (by simpa only [hrefeval] using hH)
     exact ⟨t,ht,j,hj,(hP _ _ _).mp h⟩
   apply CanonicalAdviceWithAdvice.canonical_advice i L W r q hr hq (RawTupleSemantic.student W g)
     (AdviceRawTuple.uniform W g hg) _ hpoints
   intro n k hn hk heq
   have hs := RawTupleSemantic.shape_transfer W r q g hlen hshape.2 n k heq
   exact ⟨hs,NormalizationSemantic.wins_normalize W _ n k _ hs
     (RawTupleSemantic.wins_transfer W r q g hlen hsolve n k hn hk heq)⟩

end StudentTeacher976.Adaptivity.CanonicalRawAdviceWithAdvice
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceCanonicalHardness

 theorem canonical_hardness (i : ℕ) (hardness : ¬ Sigma (i+1) ⊆ DeltaPoly i)
     (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q) :
     ∃ (L : Language) (W : WitnessPresentation i L), L ∈ Sigma (i+1) ∧
       ∀ P : RefutablePresentation i (auxiliaryRelation W r),
         (∀ x y z,P.test x y z ↔ auxiliaryTest W r x y z) →
         P.refutationLength=Polynomial.X+W.length →
         ¬ ∃ g : Student,AdviceStudents.UniformStudent i g ∧ StudentShape P r q g ∧ StudentWins P r q g := by
   classical
   obtain ⟨L,hL,hLhard⟩ : ∃ L : Language,L∈Sigma (i+1) ∧ L∉DeltaPoly i := by
     simpa only [Set.not_subset] using hardness
   obtain ⟨W⟩ := sigma_witness_presentation i L hL
   refine ⟨L,W,hL,?_⟩
   intro P htest href ⟨g,hg,hshape,hwin⟩
   apply hLhard
   obtain ⟨ε,hε,hbound⟩ := hr.2.2.2
   exact CanonicalRawAdviceWithAdvice.canonical_raw_advice i L W r q hr hq P htest href g hg hshape hwin
     (FixedPoints.fixed_point_poly_bound r hr.2.1 ε hε hbound)

end StudentTeacher976.Adaptivity.AdviceCanonicalHardness
end

section
open QAdvFew.PoQOracle
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity

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

private theorem poly_eval_mono (p : Polynomial ℕ) {n m : ℕ} (h : n ≤ m) :
    p.eval n ≤ p.eval m := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

private theorem block_shape (r : ℕ → ℕ) (x : Word) (X : List Word)
    (h : blockInput r x = some X) :
    TupleShape (x.length / resource r x.length) (resource r x.length) X ∧
      0 < resource r x.length ∧ resource r x.length ≤ x.length := by
  unfold blockInput at h
  dsimp only at h
  split at h
  · rename_i hp
    simp only [Option.some.injEq] at h
    subst X
    obtain ⟨hm, hk, hmod⟩ := hp
    have hmul : x.length / resource r x.length * resource r x.length = x.length :=
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
    refine ⟨⟨by simp [decodeBlocks], ?_⟩, hk,
      Nat.le_of_dvd hm (Nat.dvd_of_mod_eq_zero hmod)⟩
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    have hjlt := List.mem_range.mp hj
    have hbound := Nat.mul_le_mul_left (x.length / resource r x.length) (Nat.succ_le_of_lt hjlt)
    rw [hmul, Nat.mul_succ, Nat.mul_comm (x.length / resource r x.length) j] at hbound
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left]
    omega
  · simp at h

private theorem tuple_total {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (X : List Word) : ∃ Y, TupleRelation W X Y := by
  classical
  let select : Word → Word := fun a =>
    if h : ∃ w, ValidWitness W a w then h.choose
    else List.replicate (W.length.eval a.length) false
  have hselect : ∀ a, (select a).length = W.length.eval a.length ∧
      ((∃ w, ValidWitness W a w) → ValidWitness W a (select a)) := by
    intro a
    dsimp [select]
    split
    · rename_i h
      exact ⟨h.choose_spec.1, fun _ => h.choose_spec⟩
    · rename_i hnot
      refine ⟨by simp, fun h => (hnot h).elim⟩
  refine ⟨X.map select, by simp, ?_, ?_⟩
  · intro j hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
      List.getD_eq_getElem _ _ hj]
    exact (hselect _).1
  · intro j hj hw
    rw [List.getD_eq_getElem (X.map select) [] (by simpa using hj), List.getElem_map]
    rw [List.getD_eq_getElem _ _ hj] at *
    exact (hselect _).2 hw

 theorem auxiliary_total {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (x : Word) : ∃ y, auxiliaryRelation W r x y := by
  unfold auxiliaryRelation
  cases h : blockInput r x with
  | none => exact ⟨[], rfl⟩
  | some X =>
    obtain ⟨Y, hY⟩ := tuple_total W X
    exact ⟨tup Y, Y, rfl, hY⟩

private theorem tuple_encoding_bound {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (x : Word) (X Y : List Word) (hx : blockInput r x = some X)
    (hY : Y.length = X.length ∧ ∀ j < X.length,
      (Y.getD j []).length = W.length.eval (X.getD j []).length) :
    (tup Y).length ≤ (2 * Polynomial.X * (W.length + 1) : Polynomial ℕ).eval x.length := by
  obtain ⟨hX, hkpos, hkle⟩ := block_shape r x X hx
  have hbound : ∀ a ∈ Y, a.length ≤ W.length.eval x.length := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    have hjX : j < X.length := by simpa [hY.1] using hj
    have hlen := hY.2 j hjX
    rw [List.getD_eq_getElem _ _ hj] at hlen
    rw [hlen]
    apply poly_eval_mono
    have hmem : X.getD j [] ∈ X := by
      rw [List.getD_eq_getElem _ _ hjX]
      exact List.getElem_mem _
    rw [hX.2 _ hmem]
    exact Nat.div_le_self _ _
  have hsum : (Y.map List.length).sum ≤ Y.length * W.length.eval x.length := by
    calc
      (Y.map List.length).sum ≤ (Y.map fun _ => W.length.eval x.length).sum :=
        List.sum_le_sum (by intro a ha; exact hbound a ha)
      _ = Y.length * W.length.eval x.length := by simp
  have hYlen : Y.length ≤ x.length := by rw [hY.1, hX.1]; exact hkle
  rw [tup_length]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat, Polynomial.eval_X,
    Polynomial.eval_one]
  nlinarith

 theorem auxiliary_bounded {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) : ∃ b : Polynomial ℕ, ∀ x y,
      auxiliaryRelation W r x y → y.length ≤ b.eval x.length := by
  refine ⟨2 * Polynomial.X * (W.length + 1), ?_⟩
  intro x y hrel
  unfold auxiliaryRelation at hrel
  cases hx : blockInput r x with
  | none => simp [hx] at hrel; subst y; simp
  | some X =>
    simp only [hx] at hrel
    obtain ⟨Y, rfl, hY⟩ := hrel
    exact tuple_encoding_bound W r x X Y hx ⟨hY.1, hY.2.1⟩

private theorem certificate_encode {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (x a w : Word) (j : ℕ) (hj : j < x.length)
    (hwlen : w.length = W.length.eval a.length)
    (ha : a.length ≤ x.length) :
    ∃ z : Word, z.length = x.length + W.length.eval x.length ∧
      rawIndex x z = j ∧ rawWitness W x a z = w := by
  let certPrefix := List.replicate j true ++ List.replicate (x.length - j) false
  let certSuffix := w ++ List.replicate (W.length.eval x.length - w.length) false
  have hplen : certPrefix.length = x.length := by simp [certPrefix]; omega
  have hwidth : w.length ≤ W.length.eval x.length := by
    rw [hwlen]
    exact poly_eval_mono W.length ha
  have hcertSuffix : certSuffix.length = W.length.eval x.length := by simp [certSuffix]; omega
  refine ⟨certPrefix ++ certSuffix, by simp [hplen, hcertSuffix], ?_, ?_⟩
  · unfold rawIndex
    rw [List.take_append_of_le_length (by omega), ← hplen, List.take_length]
    have htake : certPrefix.takeWhile id = List.replicate j true := by
      dsimp [certPrefix]
      rw [List.takeWhile_append_of_pos]
      · simp
      · intro b hb
        have : b = true := (List.mem_replicate.mp hb).2
        simp [this]
    rw [htake]
    simp
  · unfold rawWitness
    rw [← hplen, List.drop_left]
    dsimp [certSuffix]
    rw [← hwlen, List.take_left]

 theorem auxiliary_represents {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (x y : Word) :
    auxiliaryRelation W r x y ↔ ∀ z : Word,
      z.length = x.length + W.length.eval x.length → auxiliaryTest W r x y z := by
  classical
  unfold auxiliaryRelation auxiliaryTest
  cases hx : blockInput r x with
  | none =>
    constructor
    · intro hy z hz; exact hy
    · intro hall
      exact hall (List.replicate (x.length + W.length.eval x.length) false) (by simp)
  | some X =>
    obtain ⟨hX, hkpos, hkle⟩ := block_shape r x X hx
    constructor
    · rintro ⟨Y, rfl, hY⟩ z hz
      rw [decodeTuple_encoded]
      refine ⟨hY.1, hY.2.1, ?_⟩
      intro hj hw
      exact hY.2.2 _ hj ⟨_, hw⟩
    · intro hall
      have hzero := hall (List.replicate (x.length + W.length.eval x.length) false) (by simp)
      cases hy : decodeTuple y with
      | none => simp [hy] at hzero
      | some Y =>
        simp only [hy] at hzero
        refine ⟨Y, (decodeTuple_sound y Y hy).symm, hzero.1, hzero.2.1, ?_⟩
        intro j hj hw
        obtain ⟨w, hw⟩ := hw
        have hjm : j < x.length := by rw [hX.1] at hj; omega
        have hmem : X.getD j [] ∈ X := by
          rw [List.getD_eq_getElem _ _ hj]
          exact List.getElem_mem _
        have ha : (X.getD j []).length ≤ x.length := by
          rw [hX.2 _ hmem]
          exact Nat.div_le_self _ _
        obtain ⟨z, hzlen, hzidx, hzword⟩ := certificate_encode W x (X.getD j []) w j hjm hw.1 ha
        have htest := hall z hzlen
        rw [hy] at htest
        have h := htest.2.2
        rw [hzidx] at h
        apply h hj
        rw [hzword]
        exact hw

private theorem candidate_spec {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (x : Word) (X : List Word) (H : List (List Word)) :
    (auxiliaryCandidate W x X H).length = X.length ∧
      ∀ j < X.length,
        ((auxiliaryCandidate W x X H).getD j []).length = W.length.eval (X.getD j []).length ∧
        (∀ z ∈ H.flatten, ValidWitness W (X.getD j []) (rawWitness W x (X.getD j []) z) →
          ValidWitness W (X.getD j []) ((auxiliaryCandidate W x X H).getD j [])) := by
  classical
  constructor
  · simp [auxiliaryCandidate]
  · intro j hj
    rw [List.getD_eq_getElem (auxiliaryCandidate W x X H) [] (by simpa [auxiliaryCandidate] using hj),
      List.getD_eq_getElem X [] hj]
    simp only [auxiliaryCandidate, List.getElem_map]
    cases hf : ((H.flatten.map fun z => rawWitness W x X[j] z).find?
        fun w => decide (ValidWitness W X[j] w)) with
    | none =>
      simp only [Option.getD_none, List.length_replicate, true_and]
      intro z hz hv
      have hn := List.find?_eq_none.mp hf _ (List.mem_map.mpr ⟨z, hz, rfl⟩)
      simp [hv] at hn
    | some w =>
      have hw : ValidWitness W X[j] w := by simpa using List.find?_some hf
      simp only [Option.getD_some]
      exact ⟨hw.1, fun _ _ _ => hw⟩

 theorem auxiliary_student_wins_semantic {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (x : Word) (H : List (List Word))
    (hH : HistoryShape (resource (fun m => r m + 1) x.length) 1
      (x.length + W.length.eval x.length) H) :
    ∃ t, t < resource (fun m => r m + 1) x.length ∧
      auxiliaryTest W r x ((auxiliaryStudent W r x t (H.take t)).getD 0 [])
        ((H.getD t []).getD 0 []) := by
  classical
  let k := resource r x.length
  have hbudget : resource (fun m => r m + 1) x.length = k + 1 := rfl
  cases hx : blockInput r x with
  | none =>
    refine ⟨0, by rw [hbudget]; omega, ?_⟩
    simp [auxiliaryStudent, hbudget, auxiliaryTest, hx]
  | some X =>
    obtain ⟨hX, hkpos, hkle⟩ := block_shape r x X hx
    by_contra! hfail
    have hbad : ∀ t : Fin (k + 1),
        rawIndex x ((H.getD t.val []).getD 0 []) < X.length ∧
        ValidWitness W (X.getD (rawIndex x ((H.getD t.val []).getD 0 [])) [])
          (rawWitness W x (X.getD (rawIndex x ((H.getD t.val []).getD 0 [])) []) ((H.getD t.val []).getD 0 [])) ∧
        ¬ ValidWitness W (X.getD (rawIndex x ((H.getD t.val []).getD 0 [])) [])
          ((auxiliaryCandidate W x X (H.take t.val)).getD (rawIndex x ((H.getD t.val []).getD 0 [])) []) := by
      intro t
      have ht : t.val < resource (fun m => r m + 1) x.length := by simpa [hbudget] using t.isLt
      have h := hfail t.val ht
      have hc := candidate_spec W x X (H.take t.val)
      simp only [auxiliaryStudent, if_pos ht, hx, List.getD_cons_zero,
        auxiliaryTest, hx, decodeTuple_encoded] at h
      have hshape : ∀ j < X.length,
          ((auxiliaryCandidate W x X (H.take t.val)).getD j []).length = W.length.eval (X.getD j []).length :=
        fun j hj => (hc.2 j hj).1
      simp only [hc.1, hshape, true_and] at h
      push_neg at h
      exact h hshape
    let index : Fin (k + 1) → Fin k := fun t => ⟨rawIndex x ((H.getD t.val []).getD 0 []),
      by simpa [hX.1] using (hbad t).1⟩
    have hdistinct : ∀ a b : Fin (k + 1), a.val < b.val → index a ≠ index b := by
      intro a b hab heq
      have heqval : (index a).val = (index b).val := congrArg Fin.val heq
      have hmem : (H.getD a.val []).getD 0 [] ∈ (H.take b.val).flatten := by
        have haH : a.val < H.length := by rw [hH.1, hbudget]; exact a.isLt
        have hB : H.getD a.val [] ∈ H.take b.val := by
          rw [List.getD_eq_getElem H [] haH]
          have hm := List.getElem_mem (l := H.take b.val) (n := a.val) (by simp [hH.1, hbudget]; omega)
          simpa using hm
        have hBlen := (hH.2 _ (List.mem_of_mem_take hB)).1
        refine List.mem_flatten.mpr ⟨_, hB, ?_⟩
        rw [List.getD_eq_getElem (H.getD a.val []) [] (by omega)]
        exact List.getElem_mem _
      apply (hbad b).2.2
      apply (candidate_spec W x X (H.take b.val)).2 _ (hbad b).1 |>.2 _ hmem
      have hva := (hbad a).2.1
      change rawIndex x ((H.getD a.val []).getD 0 []) = rawIndex x ((H.getD b.val []).getD 0 []) at heqval
      rwa [heqval] at hva
    have hinj : Function.Injective index := by
      intro a b heq
      rcases lt_trichotomy a.val b.val with h | h | h
      · exact (hdistinct a b h heq).elim
      · exact Fin.ext h
      · exact (hdistinct b a h heq.symm).elim
    have hcard := Fintype.card_le_of_injective index hinj
    simp only [Fintype.card_fin] at hcard
    omega

 theorem auxiliary_student_shape {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (P : RefutablePresentation i (auxiliaryRelation W r)) :
    StudentShape P (fun m => r m + 1) (fun _ => 1) (auxiliaryStudent W r) := by
  classical
  constructor
  · refine ⟨2 * Polynomial.X * (W.length + 1), ?_⟩
    intro x t H ht hH
    rw [auxiliaryStudent, if_pos ht]
    constructor
    · rfl
    · intro y hy
      simp only [List.mem_singleton] at hy
      subst y
      cases hx : blockInput r x with
      | none => simp
      | some X =>
        have hc := candidate_spec W x X H
        exact tuple_encoding_bound W r x X (auxiliaryCandidate W x X H) hx
          ⟨hc.1, fun j hj => (hc.2 j hj).1⟩
  · intro x t H ht
    simp [auxiliaryStudent, Nat.not_lt.mpr ht]

end StudentTeacher976.Adaptivity
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdvicePresentedSeparation
open QAdvFew.PoQOracle

/-- The operational separation for a single fixed refutation presentation. This does not
assert the relation-only ST noninclusion: that further assertion quantifies over other
presentations of the same underlying relation. -/
theorem presented_adaptivity_separation (i : ℕ)
    (hardness : ¬ Sigma (i+1) ⊆ DeltaPoly i) (r q : ℕ → ℕ)
    (hr : AdmissibleRounds r) (hq : AdmissibleQueries q) :
    ∃ (R : SearchRelation) (P : RefutablePresentation i R),
      (∃ g : Student,UniformStudent i g ∧
        StudentShape P (fun m => r m+1) (fun _ => 1) g ∧
        StudentWins P (fun m => r m+1) (fun _ => 1) g) ∧
      ¬ ∃ g : Student,AdviceStudents.UniformStudent i g ∧ StudentShape P r q g ∧ StudentWins P r q g := by
  obtain ⟨L,W,hL,hW⟩ := AdviceCanonicalHardness.canonical_hardness i hardness r q hr hq
  obtain ⟨b,hb⟩ := auxiliary_bounded W r
  let P : RefutablePresentation i (auxiliaryRelation W r) :=
    { answerBound := b
      refutationLength := Polynomial.X+W.length
      test := auxiliaryTest W r
      efficient := auxiliary_test_efficient i L W r hr
      total := auxiliary_total W r
      bounded := hb
      represents := by
        intro x y
        simpa using auxiliary_represents W r x y }
  refine ⟨auxiliaryRelation W r,P,?_,hW P (fun _ _ _ => Iff.rfl) rfl⟩
  refine ⟨auxiliaryStudent W r,auxiliary_student_uniform i L W r hr,
    auxiliary_student_shape W r P,?_⟩
  intro x H hH
  have hH' : HistoryShape (resource (fun m => r m+1) x.length) 1
      (x.length+W.length.eval x.length) H := by
    simpa [P,resource] using hH
  obtain ⟨t,ht,htest⟩ := auxiliary_student_wins_semantic W r x H hH'
  exact ⟨t,ht,0,by simp [resource],htest⟩

end StudentTeacher976.Adaptivity.AdvicePresentedSeparation
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CertifiedReply
open QAdvFew.PoQOracle Turing.MultiTapeTM

 noncomputable def width (p b c : Polynomial ℕ) : Polynomial ℕ := p+2*b+c
 def old (p : Polynomial ℕ) (x z : Word) : Word := z.take (p.eval x.length)
 def index (p b : Polynomial ℕ) (x z : Word) : ℕ :=
   (((z.drop (p.eval x.length)).take (b.eval x.length)).takeWhile id).length
 def answer (p b : Polynomial ℕ) (x z : Word) : Word :=
   (z.drop (p.eval x.length+b.eval x.length)).take (index p b x z)
 def cert (p b c : Polynomial ℕ) (x z : Word) : Word :=
   (z.drop (p.eval x.length+2*b.eval x.length)).take (c.eval x.length)
 def code (b : Polynomial ℕ) (x z a v : Word) : Word :=
   z ++ (List.replicate a.length true ++ List.replicate (b.eval x.length-a.length) false) ++
     (a ++ List.replicate (b.eval x.length-a.length) false) ++ v

 theorem index_le (p b : Polynomial ℕ) (x z : Word) : index p b x z≤b.eval x.length := by
   unfold index
   rw [AuxiliaryData.leading_true_length]
   exact le_trans (List.idxOf_le_length) (List.length_take_le _ _)
 theorem answer_le (p b : Polynomial ℕ) (x z : Word) : (answer p b x z).length≤b.eval x.length := by
   exact le_trans (List.length_take_le _ _) (index_le p b x z)
 theorem old_length (p b c : Polynomial ℕ) (x z : Word) (hz : z.length=(width p b c).eval x.length) :
     (old p x z).length=p.eval x.length := by
   simp only [old,List.length_take]
   rw [Nat.min_eq_left]
   simp only [width,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat] at hz
   omega
 theorem code_length (p b c : Polynomial ℕ) (x z a v : Word)
     (hz : z.length=p.eval x.length) (ha : a.length≤b.eval x.length) (hv : v.length=c.eval x.length) :
     (code b x z a v).length=(width p b c).eval x.length := by
   simp only [code,List.length_append,List.length_replicate,hz,hv,width,
     Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
   omega
 theorem old_code (p b : Polynomial ℕ) (x z a v : Word) (hz : z.length=p.eval x.length) :
     old p x (code b x z a v)=z := by
   unfold old code
   rw [← hz]
   simp [List.take_append]
 theorem index_code (p b : Polynomial ℕ) (x z a v : Word)
     (hz : z.length=p.eval x.length) (ha : a.length≤b.eval x.length) :
     index p b x (code b x z a v)=a.length := by
   let u := List.replicate a.length true ++ List.replicate (b.eval x.length-a.length) false
   have hu : u.length=b.eval x.length := by simp [u]; omega
   have hcode : code b x z a v=z ++ (u ++ ((a ++ List.replicate (b.eval x.length-a.length) false) ++ v)) := by
     simp [code,u,List.append_assoc]
   unfold index
   rw [hcode,← hz,List.drop_left,← hu,List.take_left]
   have ht : u.takeWhile id=List.replicate a.length true := by
     unfold u
     rw [List.takeWhile_append_of_pos]
     · simp
     · intro t ht
       simp [(List.mem_replicate.mp ht).2]
   rw [ht,List.length_replicate]
 theorem answer_code (p b : Polynomial ℕ) (x z a v : Word)
     (hz : z.length=p.eval x.length) (ha : a.length≤b.eval x.length) :
     answer p b x (code b x z a v)=a := by
   let u := List.replicate a.length true ++ List.replicate (b.eval x.length-a.length) false
   have hu : u.length=b.eval x.length := by simp [u]; omega
   have hcode : code b x z a v=(z ++ u) ++ (a ++ (List.replicate (b.eval x.length-a.length) false ++ v)) := by
     simp [code,u,List.append_assoc]
   unfold answer
   rw [index_code p b x z a v hz ha,hcode,← hz,← hu,← List.length_append,List.drop_left,List.take_left]
 theorem cert_code (p b c : Polynomial ℕ) (x z a v : Word)
     (hz : z.length=p.eval x.length) (ha : a.length≤b.eval x.length) (hv : v.length=c.eval x.length) :
     cert p b c x (code b x z a v)=v := by
   let u := List.replicate a.length true ++ List.replicate (b.eval x.length-a.length) false
   let av := a ++ List.replicate (b.eval x.length-a.length) false
   have hu : u.length=b.eval x.length := by simp [u]; omega
   have hav : av.length=b.eval x.length := by simp [av]; omega
   have hlen : (z ++ u ++ av).length=p.eval x.length+2*b.eval x.length := by
     simp [hz,hu,hav]; omega
   have hcode : code b x z a v=(z ++ u ++ av) ++ v := by simp [code,u,av,List.append_assoc]
   unfold cert
   rw [hcode,← hlen,List.drop_left,← hv,List.take_length]

 theorem old_poly (p : Polynomial ℕ) : ComputableTidilyInPolyTime (fun q : Word × Word => old p q.1 q.2)
     (encPair encBits encBits) encBits := by
   have hp := ComputableTidilyInPolyTime.unary_eval p
   unfold old
   fun_prop
 theorem index_poly (p b : Polynomial ℕ) : ComputableTidilyInPolyTime (fun q : Word × Word => index p b q.1 q.2)
     (encPair encBits encBits) encUnary := by
   have hp := ComputableTidilyInPolyTime.unary_eval p
   have hb := ComputableTidilyInPolyTime.unary_eval b
   change ComputableTidilyInPolyTime (fun q : Word × Word => index p b q.1 q.2) _ _
   unfold index
   simp_rw [AuxiliaryData.leading_true_length]
   apply AuxiliaryData.first_false_poly.comp (g := fun q : Word × Word => (q.2.drop (p.eval q.1.length)).take (b.eval q.1.length))
   fun_prop
 theorem answer_poly (p b : Polynomial ℕ) : ComputableTidilyInPolyTime (fun q : Word × Word => answer p b q.1 q.2)
     (encPair encBits encBits) encBits := by
   have hp := ComputableTidilyInPolyTime.unary_eval p
   have hb := ComputableTidilyInPolyTime.unary_eval b
   have hi := index_poly p b
   unfold answer
   fun_prop
 theorem cert_poly (p b c : Polynomial ℕ) : ComputableTidilyInPolyTime (fun q : Word × Word => cert p b c q.1 q.2)
     (encPair encBits encBits) encBits := by
   have hp := ComputableTidilyInPolyTime.unary_eval p
   have hb := ComputableTidilyInPolyTime.unary_eval b
   have hc := ComputableTidilyInPolyTime.unary_eval c
   unfold cert
   fun_prop

end StudentTeacher976.Adaptivity.CertifiedReply
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CertifiedGame
open QAdvFew.PoQOracle
open CertifiedReply

 def test {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R) (c : Polynomial ℕ)
     (V : Word → Word → Word → Prop) (x y z : Word) : Prop :=
   P.test x y (old P.refutationLength x z) ∨
     ¬ ((cert P.refutationLength P.answerBound c x z).length=c.eval x.length ∧
       V x (answer P.refutationLength P.answerBound x z) (cert P.refutationLength P.answerBound c x z))

 theorem represents {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R) (c : Polynomial ℕ)
     (V : Word → Word → Word → Prop)
     (hV : ∀ x y, R x y ↔ ∃ v, v.length=c.eval x.length ∧ V x y v) (x y : Word) :
     R x y ↔ ∀ z, z.length=(width P.refutationLength P.answerBound c).eval x.length → test P c V x y z := by
   classical
   constructor
   · intro hxy z hz
     exact Or.inl ((P.represents x y).mp hxy _ (old_length _ _ _ x z hz))
   · intro hall
     by_contra hnot
     obtain ⟨z,hz,hbad⟩ : ∃ z : Word, z.length=P.refutationLength.eval x.length ∧ ¬ P.test x y z := by
       have hn := mt (P.represents x y).mpr hnot
       push_neg at hn
       exact hn
     obtain ⟨a,ha⟩ := P.total x
     obtain ⟨v,hv,hvalid⟩ := (hV x a).mp ha
     have hab := P.bounded x a ha
     have ht := hall (code P.answerBound x z a v) (code_length _ _ _ x z a v hz hab hv)
     simp only [test,old_code _ _ x z a v hz,cert_code _ _ _ x z a v hz hab hv,
       answer_code _ _ x z a v hz hab] at ht
     exact ht.elim hbad (fun h => h ⟨hv,hvalid⟩)

 def student (p b : Polynomial ℕ) : Student := fun x t H =>
   if t<2 then [if t=0 then [] else answer p b x ((H.getD 0 []).getD 0 [])] else []

 theorem shape {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R) :
     StudentShape Q (fun _ => 2) (fun _ => 1) (student P.refutationLength P.answerBound) := by
   constructor
   · refine ⟨P.answerBound,?_⟩
     intro x t H ht hH
     have ht2 : t<2 := ht
     simp only [student,if_pos ht2,List.length_singleton,resource]
     refine ⟨True.intro,?_⟩
     intro y hy
     simp only [List.mem_singleton] at hy
     subst y
     split
     · simp
     · exact answer_le _ _ _ _
   · intro x t H ht
     change 2≤t at ht
     exact if_neg (Nat.not_lt_of_le ht)

 theorem wins {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R) (c : Polynomial ℕ)
     (V : Word → Word → Word → Prop)
     (hV : ∀ x y, R x y ↔ ∃ v, v.length=c.eval x.length ∧ V x y v)
     (Q : RefutablePresentation i R) (hQ : ∀ x y z, Q.test x y z ↔ test P c V x y z) :
     StudentWins Q (fun _ => 2) (fun _ => 1) (student P.refutationLength P.answerBound) := by
   classical
   intro x H hH
   let z := (H.getD 0 []).getD 0 []
   by_cases hfirst : test P c V x [] z
   · refine ⟨0,by simp [resource],0,by simp [resource],?_⟩
     apply (hQ _ _ _).mpr
     simpa only [student,resource,show 0<2 from by omega,if_true,List.getD_cons_zero] using hfirst
   · have hgood : R x (answer P.refutationLength P.answerBound x z) := by
       have hcert : (cert P.refutationLength P.answerBound c x z).length=c.eval x.length ∧
           V x (answer P.refutationLength P.answerBound x z) (cert P.refutationLength P.answerBound c x z) := by
         unfold test at hfirst
         tauto
       exact (hV _ _).mpr ⟨_,hcert⟩
     refine ⟨1,by simp [resource],0,by simp [resource],?_⟩
     have hreplylen : ((H.getD 1 []).getD 0 []).length=Q.refutationLength.eval x.length := by
       have hmem : H.getD 1 [] ∈ H := by
         rw [List.getD_eq_getElem _ _ (by rw [hH.1]; simp [resource])]
         exact List.getElem_mem _
       obtain ⟨hB,hBs⟩ := hH.2 _ hmem
       apply hBs ((H.getD 1 []).getD 0 [])
       have hi : 0<(H.getD 1 []).length := by rw [hB]; exact (show 0<1 by omega)
       have he : (H.getD 1 []).getD 0 []=(H.getD 1 [])[0] := List.getD_eq_getElem _ _ hi
       rw [he]
       exact List.getElem_mem _
     have htest := (Q.represents _ _).mp hgood _ hreplylen
     have hz : ((H.take 1).getD 0 []).getD 0 []=z := by
       simp [z,List.getD_eq_getElem?_getD]
     simpa only [student,show 1<2 from by omega,if_true,show ¬1=0 from by omega,if_false,
       List.getD_cons_zero,hz] using htest

end StudentTeacher976.Adaptivity.CertifiedGame
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CertifiedGame
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)
open CertifiedReply

 def firstReply (s : Word) : Word :=
   (TupleCodec.decodeTuple ((TupleCodec.decodeTuple (field s 2)).headD [])).headD []
 def studentCPU (p b : Polynomial ℕ) (s : Word) : Word :=
   if (field s 1).length<3 then
     tup [if (field s 1).length=1 then [] else answer p b (field s 0) (firstReply s)] else tup []
 theorem firstReply_poly : ComputableTidilyInPolyTime firstReply encBits encBits := by
   have hd := TupleCodec.decoder_poly.tidy
   have hh := ComputableTidilyInPolyTime.headD (encA := encBits) (encL := encList encBits) []
   exact hh.comp (hd.comp (hh.comp (hd.comp (field_poly 2))))
 theorem studentCPU_poly (p b : Polynomial ℕ) : ComputableTidilyInPolyTime (studentCPU p b) encBits encBits := by
   have ha := (answer_poly p b).comp ((field_poly 0).prod firstReply_poly)
   have ht := field_poly 1
   unfold studentCPU
   apply ComputableTidilyInPolyTime.ite_decide
   · fun_prop
   · apply TupleCodec.encode_poly.comp
     apply ComputableTidilyInPolyTime.cons'
     · apply ComputableTidilyInPolyTime.ite_decide
       · fun_prop
       · exact ComputableTidilyInPolyTime.const []
       · exact ha
     · exact ComputableTidilyInPolyTime.const []
   · exact ComputableTidilyInPolyTime.const (tup [])
 theorem studentCPU_encoded (p b : Polynomial ℕ) (x : Word) (t : ℕ) (H : List (List Word)) :
     studentCPU p b (tup [x,List.replicate (t+1) true,tup (H.map tup)])=
       tup (student p b x t H) := by
   have hfirst : firstReply (tup [x,List.replicate (t+1) true,tup (H.map tup)])=(H.getD 0 []).getD 0 [] := by
     simp only [firstReply,field,TupleCodec.decode_tup,List.getD_cons_succ,List.getD_cons_zero,List.headD_map]
     cases H with
     | nil =>
       change (TupleCodec.decodeTuple (tup [])).headD []=[]
       rw [TupleCodec.decode_tup]
       rfl
     | cons B H =>
       simp only [List.map_cons,List.headD_cons,TupleCodec.decode_tup,List.getElem?_cons_zero,Option.getD_some]
       cases B <;> rfl
   unfold studentCPU
   rw [hfirst]
   simp only [field,TupleCodec.decode_tup,List.getD_cons_zero,List.getD_cons_succ,List.length_replicate]
   have ht : t+1<3 ↔ t<2 := by omega
   have hz : t+1=1 ↔ t=0 := by omega
   simp only [student,ht,hz]
   split <;> rfl
 theorem student_uniform (i : ℕ) (p b : Polynomial ℕ) : UniformStudent i (student p b) :=
   ⟨studentCPU p b,pure_inFP i _ (studentCPU_poly p b),studentCPU_encoded p b⟩

end StudentTeacher976.Adaptivity.CertifiedGame
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CertifiedGame
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)
open CertifiedReply

 theorem triple_mem (T : Word → Word → Word → Prop) (x y z : Word) :
     (∃ a b c, tup [x,y,z]=tup [a,b,c] ∧ T a b c) ↔ T x y z := by
   constructor
   · rintro ⟨a,b,c,he,h⟩
     have hd := congrArg TupleCodec.decodeTuple he
     simp only [TupleCodec.decode_tup,List.cons.injEq,and_true] at hd
     obtain ⟨rfl,rfl,rfl⟩ := hd
     exact h
   · exact fun h => ⟨x,y,z,rfl,h⟩

 def triple (s : Word) : Word := tup [field s 0,field s 1,field s 2]
 def oldArgument (p : Polynomial ℕ) (s : Word) : Word :=
   tup [field s 0,field s 1,old p (field s 0) (field s 2)]
 def validArgument (p b c : Polynomial ℕ) (s : Word) : Word :=
   tup [field s 0,answer p b (field s 0) (field s 2),cert p b c (field s 0) (field s 2)]
 def booleanPost (p b c : Polynomial ℕ) (s : Word) : Word :=
   let input := field s 0
   let bits := field s 1
   [decide (triple input=input) &&
     ((field bits 0).headD false || !(decide ((cert p b c (field input 0) (field input 2)).length=c.eval (field input 0).length) &&
       (field bits 1).headD false))]
 theorem triple_poly : ComputableTidilyInPolyTime triple encBits encBits := by
   have h0 := field_poly 0
   have h1 := field_poly 1
   have h2 := field_poly 2
   unfold triple
   apply TupleCodec.encode_poly.comp
   fun_prop
 theorem oldArgument_poly (p : Polynomial ℕ) : ComputableTidilyInPolyTime (oldArgument p) encBits encBits := by
   have h0 := field_poly 0
   have h1 := field_poly 1
   have h2 := field_poly 2
   have hp := (old_poly p).comp (h0.prod h2)
   unfold oldArgument
   apply TupleCodec.encode_poly.comp
   fun_prop
 theorem validArgument_poly (p b c : Polynomial ℕ) : ComputableTidilyInPolyTime (validArgument p b c) encBits encBits := by
   have h0 := field_poly 0
   have h2 := field_poly 2
   have ha := (answer_poly p b).comp (h0.prod h2)
   have hc := (cert_poly p b c).comp (h0.prod h2)
   unfold validArgument
   apply TupleCodec.encode_poly.comp
   fun_prop
 theorem booleanPost_poly (p b c : Polynomial ℕ) : ComputableTidilyInPolyTime (booleanPost p b c) encBits encBits := by
   have h0 := field_poly 0
   have h1 := field_poly 1
   have h2 := field_poly 2
   have ht := triple_poly
   have hc := cert_poly p b c
   have hp := ComputableTidilyInPolyTime.unary_eval c
   unfold booleanPost
   apply ComputableTidilyInPolyTime.bitsCons
   · fun_prop
   · exact ComputableTidilyInPolyTime.const []

 theorem test_efficient {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R)
     (c : Polynomial ℕ) (V : Word → Word → Word → Prop)
     (hV : {s | ∃ x y z, s=tup [x,y,z] ∧ V x y z} ∈ Delta i) :
     {s | ∃ x y z, s=tup [x,y,z] ∧ test P c V x y z} ∈ Delta i := by
   obtain ⟨F,hF,hFspec⟩ := (delta_iff_uniform_boolean i _).mp P.efficient
   obtain ⟨G,hG,hGspec⟩ := (delta_iff_uniform_boolean i _).mp hV
   have hFtr (x y z : Word) : (F (tup [x,y,z])).headD false=true ↔ P.test x y z := by
     rw [← hFspec]
     exact triple_mem P.test x y z
   have hGtr (x y z : Word) : (G (tup [x,y,z])).headD false=true ↔ V x y z := by
     rw [← hGspec]
     exact triple_mem V x y z
   let FO := fun s => F (oldArgument P.refutationLength s)
   let GV := fun s => G (validArgument P.refutationLength P.answerBound c s)
   have hFO : InFP i FO := OracleComputations.inFP_compose i _ F
     (pure_inFP i _ (oldArgument_poly P.refutationLength)) hF
   have hGV : InFP i GV := OracleComputations.inFP_compose i _ G
     (pure_inFP i _ (validArgument_poly P.refutationLength P.answerBound c)) hG
   let pair := fun s => tup [FO s,GV s]
   have hpair : InFP i pair := OracleProducts.pair_inFP i FO GV hFO hGV
   let H := fun s => booleanPost P.refutationLength P.answerBound c (tup [s,pair s])
   apply (delta_iff_uniform_boolean i _).mpr
   refine ⟨H,OracleComputations.inFP_post i _ _ (OracleComputations.inFP_retain i pair hpair)
     (booleanPost_poly P.refutationLength P.answerBound c),?_⟩
   intro s
   have hhead : (H s).headD false=true ↔ triple s=s ∧ test P c V (field s 0) (field s 1) (field s 2) := by
     simp only [H,booleanPost,pair,field,TupleCodec.decode_tup,List.getD_cons_zero,List.getD_cons_succ,
       List.headD_cons,Bool.and_eq_true_iff,decide_eq_true_eq,Bool.or_eq_true_iff,Bool.not_eq_true',
       Bool.eq_false_iff,ne_eq,FO,GV,oldArgument,validArgument]
     rw [hFtr,hGtr]
     simp only [test,not_and_or]
   rw [hhead]
   constructor
   · rintro ⟨x,y,z,rfl,h⟩
     simp [triple,field,TupleCodec.decode_tup,h]
   · rintro ⟨he,h⟩
     exact ⟨field s 0,field s 1,field s 2,he.symm,h⟩

end StudentTeacher976.Adaptivity.CertifiedGame
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.PresentationTranslation
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)

def history (ψ : Word → Word → Word) (x : Word) (H : List (List Word)) : List (List Word) :=
  H.map (fun B => B.map (ψ x))

def student (ψ : Word → Word → Word) (g : Student) : Student :=
  fun x t H => g x t (history ψ x H)

theorem history_take (ψ : Word → Word → Word) (x : Word) (H : List (List Word)) (t : ℕ) :
    history ψ x (H.take t) = (history ψ x H).take t := by
  simp only [history,List.map_take]

theorem history_shape (ψ : Word → Word → Word) (x : Word) (h q u v : ℕ)
    (hlen : ∀ z : Word,z.length=u → (ψ x z).length=v)
    (H : List (List Word)) (hH : HistoryShape h q u H) :
    HistoryShape h q v (history ψ x H) := by
  refine ⟨by simpa [history] using hH.1,?_⟩
  intro B hB
  change B ∈ H.map (fun C => C.map (ψ x)) at hB
  obtain ⟨C,hC,rfl⟩ := List.mem_map.mp hB
  obtain ⟨hBl,hBz⟩ := hH.2 C hC
  refine ⟨by simpa using hBl,?_⟩
  intro z hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  exact hlen w (hBz w hw)

theorem history_getD (ψ : Word → Word → Word) (x : Word) (H : List (List Word)) (t j : ℕ)
    (ht : t < H.length) (hj : j < (H.getD t []).length) :
    ((history ψ x H).getD t []).getD j [] = ψ x ((H.getD t []).getD j []) := by
  have he : (history ψ x H).getD t [] = (H.getD t []).map (ψ x) := by
    simpa only [history,List.map_nil] using
      (List.getD_map (l := H) (d := []) (n := t) (fun B => B.map (ψ x)))
  rw [he,List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map,
    List.getD_eq_getElem _ _ hj]

def rawHistories (s : Word) : List (List Word) :=
  (TupleCodec.decodeTuple (field s 2)).map TupleCodec.decodeTuple

def pre (ψ : Word → Word → Word) (s : Word) : Word :=
  tup [field s 0,field s 1,tup ((history ψ (field s 0) (rawHistories s)).map tup)]

theorem rawHistories_poly : ComputableTidilyInPolyTime rawHistories encBits
    (encList (encList encBits)) := by
  exact (ComputableTidilyInPolyTime.map TupleCodec.decoder_poly.tidy).comp
    (TupleCodec.decoder_poly.tidy.comp (field_poly 2))

theorem history_poly (ψ : Word → Word → Word)
    (hψ : ComputableTidilyInPolyTime (fun p : Word × Word => ψ p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableTidilyInPolyTime (fun p : Word × List (List Word) => history ψ p.1 p.2)
      (encPair encBits (encList (encList encBits))) (encList (encList encBits)) := by
  unfold history
  apply ComputableTidilyInPolyTime.mapWithInput (by fun_prop)
  apply ComputableTidilyInPolyTime.mapWithInput (by fun_prop)
  apply hψ.comp (g := fun p : ((Word × List (List Word)) × List Word) × Word => (p.1.1.1,p.2))
  fun_prop

theorem pre_poly (ψ : Word → Word → Word)
    (hψ : ComputableTidilyInPolyTime (fun p : Word × Word => ψ p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableTidilyInPolyTime (pre ψ) encBits encBits := by
  have hh := (history_poly ψ hψ).comp ((field_poly 0).prod rawHistories_poly)
  have he := TupleCodec.encode_poly.comp ((ComputableTidilyInPolyTime.map TupleCodec.encode_poly).comp hh)
  have h0 := field_poly 0
  have h1 := field_poly 1
  unfold pre
  apply TupleCodec.encode_poly.comp
  fun_prop

theorem pre_encoded (ψ : Word → Word → Word) (x : Word) (t : ℕ) (H : List (List Word)) :
    pre ψ (tup [x,List.replicate (t+1) true,tup (H.map tup)]) =
      tup [x,List.replicate (t+1) true,tup ((history ψ x H).map tup)] := by
  simp [pre,rawHistories,field,TupleCodec.decode_tup,List.map_map,Function.comp_def]

theorem uniform (i : ℕ) (ψ : Word → Word → Word)
    (hψ : ComputableTidilyInPolyTime (fun p : Word × Word => ψ p.1 p.2)
      (encPair encBits encBits) encBits) (g : Student) (hg : UniformStudent i g) :
    UniformStudent i (student ψ g) := by
  obtain ⟨F,hF,hFspec⟩ := hg
  refine ⟨fun s => F (pre ψ s),
    OracleComputations.inFP_compose i _ F (pure_inFP i _ (pre_poly ψ hψ)) hF,?_⟩
  intro x t H
  change F (pre ψ (tup [x,List.replicate (t+1) true,tup (H.map tup)])) = _
  rw [pre_encoded,hFspec]
  rfl

theorem shape {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (ψ : Word → Word → Word)
    (hlen : ∀ x z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x z).length=Q.refutationLength.eval x.length)
    (g : Student) (hg : StudentShape Q r q g) : StudentShape P r q (student ψ g) := by
  obtain ⟨⟨b,hb⟩,hend⟩ := hg
  refine ⟨⟨b,?_⟩,?_⟩
  · intro x t H ht hH
    exact hb x t (history ψ x H) ht (history_shape ψ x _ _ _ _ (hlen x) H hH)
  · intro x t H ht
    exact hend x t (history ψ x H) ht

theorem wins {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (ψ : Word → Word → Word)
    (hlen : ∀ x z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x z).length=Q.refutationLength.eval x.length)
    (htest : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      Q.test x y (ψ x z) → P.test x y z)
    (g : Student) (hg : StudentWins Q r q g) : StudentWins P r q (student ψ g) := by
  intro x H hH
  obtain ⟨t,ht,j,hj,haccept⟩ := hg x (history ψ x H)
    (history_shape ψ x _ _ _ _ (hlen x) H hH)
  have htH : t < H.length := by rw [hH.1]; exact ht
  have hBt : H.getD t [] ∈ H := by
    rw [List.getD_eq_getElem _ _ htH]
    exact List.getElem_mem _
  have hjB : j < (H.getD t []).length := by rw [(hH.2 _ hBt).1]; exact hj
  rw [history_getD ψ x H t j htH hjB,← history_take] at haccept
  refine ⟨t,ht,j,hj,htest x _ _ ?_ haccept⟩
  exact (hH.2 _ hBt).2 _ (by
    rw [List.getD_eq_getElem _ _ hjB]
    exact List.getElem_mem _)

theorem transfer {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (ψ : Word → Word → Word)
    (hψ : ComputableTidilyInPolyTime (fun p : Word × Word => ψ p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ x z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x z).length=Q.refutationLength.eval x.length)
    (htest : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      Q.test x y (ψ x z) → P.test x y z)
    (g : Student) (hg : UniformStudent i g) (hshape : StudentShape Q r q g)
    (hwin : StudentWins Q r q g) :
    UniformStudent i (student ψ g) ∧ StudentShape P r q (student ψ g) ∧
      StudentWins P r q (student ψ g) :=
  ⟨uniform i ψ hψ g hg,shape P Q r q ψ hlen g hshape,wins P Q r q ψ hlen htest g hwin⟩

end StudentTeacher976.Adaptivity.PresentationTranslation
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.OraclePresentationTranslation
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)
open PresentationTranslation (history student)

def mapInput (s : Word) : Word :=
  tup ((TupleCodec.decodeTuple (field s 1)).map (fun w => tup [field s 0,w]))
def contextMap (F : Word → Word) (s : Word) : Word :=
  tup ((TupleCodec.decodeTuple (field s 1)).map (fun w => F (tup [field s 0,w])))

theorem mapInput_poly : ComputableTidilyInPolyTime mapInput encBits encBits := by
  have h0 := field_poly 0
  have h1 := TupleCodec.decoder_poly.tidy.comp (field_poly 1)
  unfold mapInput
  apply TupleCodec.encode_poly.comp
  apply ComputableTidilyInPolyTime.mapWithInput h1
  apply TupleCodec.encode_poly.comp
  have hx := h0.comp (ComputableTidilyInPolyTime.fst encBits encBits)
  have hw := ComputableTidilyInPolyTime.snd encBits encBits
  fun_prop

theorem contextMap_inFP (i : ℕ) (F : Word → Word) (hF : InFP i F) :
    InFP i (contextMap F) := by
  have hm := OracleWordMap.uniform i F hF
  have hc := OracleComputations.inFP_compose i mapInput _ (pure_inFP i _ mapInput_poly) hm
  have he : (fun s => tup ((TupleCodec.decodeTuple (mapInput s)).map F))=contextMap F := by
    funext s
    simp [mapInput,contextMap,TupleCodec.decode_tup,List.map_map,Function.comp_def]
  rwa [he] at hc

theorem contextMap_encoded (F : Word → Word) (x : Word) (l : List Word) :
    contextMap F (tup [x,tup l])=tup (l.map (fun w => F (tup [x,w]))) := by
  simp [contextMap,field,TupleCodec.decode_tup]

def code (ψ : Word → Word → Word) (s : Word) : Word := ψ (field s 0) (field s 1)
def historyCode (ψ : Word → Word → Word) : Word → Word := contextMap (contextMap (code ψ))
def preInput (s : Word) : Word := tup [field s 0,field s 2]
def restore (s : Word) : Word := tup [field (field s 0) 0,field (field s 0) 1,field s 1]
def pre (ψ : Word → Word → Word) (s : Word) : Word :=
  restore (tup [s,historyCode ψ (preInput s)])

theorem historyCode_encoded (ψ : Word → Word → Word) (x : Word) (H : List (List Word)) :
    historyCode ψ (tup [x,tup (H.map tup)])=tup ((history ψ x H).map tup) := by
  simp [historyCode,contextMap_encoded,PresentationTranslation.history,List.map_map,Function.comp_def,
    code,field,TupleCodec.decode_tup]

theorem preInput_poly : ComputableTidilyInPolyTime preInput encBits encBits := by
  have h0 := field_poly 0
  have h2 := field_poly 2
  unfold preInput
  apply TupleCodec.encode_poly.comp
  fun_prop
theorem restore_poly : ComputableTidilyInPolyTime restore encBits encBits := by
  have h0 := (field_poly 0).comp (field_poly 0)
  have h1 := (field_poly 1).comp (field_poly 0)
  have h2 := field_poly 1
  unfold restore
  apply TupleCodec.encode_poly.comp
  fun_prop

theorem pre_inFP (i : ℕ) (ψ : Word → Word → Word) (hψ : InFP i (code ψ)) : InFP i (pre ψ) := by
  have hh := contextMap_inFP i (contextMap (code ψ)) (contextMap_inFP i (code ψ) hψ)
  have hi := OracleComputations.inFP_compose i preInput _ (pure_inFP i _ preInput_poly) hh
  exact OracleComputations.inFP_post i _ restore (OracleComputations.inFP_retain i _ hi) restore_poly

theorem pre_encoded (ψ : Word → Word → Word) (x : Word) (t : ℕ) (H : List (List Word)) :
    pre ψ (tup [x,List.replicate (t+1) true,tup (H.map tup)])=
      tup [x,List.replicate (t+1) true,tup ((history ψ x H).map tup)] := by
  unfold pre
  have hi : preInput (tup [x,List.replicate (t+1) true,tup (H.map tup)])=tup [x,tup (H.map tup)] := by
    simp [preInput,field,TupleCodec.decode_tup]
  rw [hi,historyCode_encoded]
  simp [restore,field,TupleCodec.decode_tup]

theorem uniform (i : ℕ) (ψ : Word → Word → Word) (hψ : InFP i (code ψ))
    (g : Student) (hg : UniformStudent i g) : UniformStudent i (student ψ g) := by
  obtain ⟨F,hF,hFspec⟩ := hg
  refine ⟨fun s => F (pre ψ s),OracleComputations.inFP_compose i _ F (pre_inFP i ψ hψ) hF,?_⟩
  intro x t H
  change F (pre ψ (tup [x,List.replicate (t+1) true,tup (H.map tup)])) = _
  rw [pre_encoded,hFspec]
  rfl

theorem transfer {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (ψ : Word → Word → Word) (hψ : InFP i (code ψ))
    (hlen : ∀ x z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x z).length=Q.refutationLength.eval x.length)
    (htest : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      Q.test x y (ψ x z) → P.test x y z)
    (g : Student) (hg : UniformStudent i g) (hshape : StudentShape Q r q g)
    (hwin : StudentWins Q r q g) :
    UniformStudent i (student ψ g) ∧ StudentShape P r q (student ψ g) ∧
      StudentWins P r q (student ψ g) :=
  ⟨uniform i ψ hψ g hg,PresentationTranslation.shape P Q r q ψ hlen g hshape,
    PresentationTranslation.wins P Q r q ψ hlen htest g hwin⟩

end StudentTeacher976.Adaptivity.OraclePresentationTranslation
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CausalPresentationTranslation
open QAdvFew.PoQOracle

def batch (ψ : Word → Word → Word → Word) (g : Student) (x : Word)
    (K : List (List Word)) (B : List Word) : List Word :=
  List.zipWith (ψ x) (g x K.length K) B
def advance (ψ : Word → Word → Word → Word) (g : Student) (x : Word)
    (K : List (List Word)) (B : List Word) : List (List Word) := K++[batch ψ g x K B]
def history (ψ : Word → Word → Word → Word) (g : Student) (x : Word)
    (H : List (List Word)) : List (List Word) := H.foldl (advance ψ g x) []
def student (ψ : Word → Word → Word → Word) (g : Student) : Student :=
  fun x t H => g x t (history ψ g x H)

theorem foldl_length (ψ : Word → Word → Word → Word) (g : Student) (x : Word)
    (H K : List (List Word)) :
    (H.foldl (advance ψ g x) K).length=K.length+H.length := by
  induction H generalizing K with
  | nil => simp
  | cons B H ih => simp [List.foldl_cons,ih,advance,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
theorem history_length (ψ : Word → Word → Word → Word) (g : Student) (x : Word)
    (H : List (List Word)) : (history ψ g x H).length=H.length := by
  simpa [history] using foldl_length ψ g x H []
theorem foldl_extends (ψ : Word → Word → Word → Word) (g : Student) (x : Word)
    (H K : List (List Word)) : ∃ T : List (List Word),H.foldl (advance ψ g x) K=K++T := by
  induction H generalizing K with
  | nil => exact ⟨[],by simp⟩
  | cons B H ih =>
    obtain ⟨T,hT⟩ := ih (advance ψ g x K B)
    refine ⟨batch ψ g x K B::T,?_⟩
    simpa [advance,List.append_assoc] using hT
theorem history_append (ψ : Word → Word → Word → Word) (g : Student) (x : Word)
    (H : List (List Word)) (B : List Word) :
    history ψ g x (H++[B])=history ψ g x H++[batch ψ g x (history ψ g x H) B] := by
  simp [history,List.foldl_append,advance]
theorem history_take (ψ : Word → Word → Word → Word) (g : Student) (x : Word)
    (H : List (List Word)) (t : ℕ) (ht : t≤H.length) :
    (history ψ g x H).take t=history ψ g x (H.take t) := by
  obtain ⟨T,hT⟩ := foldl_extends ψ g x (H.drop t) (history ψ g x (H.take t))
  have he : history ψ g x H=history ψ g x (H.take t)++T := by
    calc
      history ψ g x H = history ψ g x (H.take t++H.drop t) := by rw [List.take_append_drop]
      _ = (H.drop t).foldl (advance ψ g x) (history ψ g x (H.take t)) := by
        simp only [history,List.foldl_append]
      _ = _ := hT
  rw [he]
  have hl : (history ψ g x (H.take t)).length=t := by
    rw [history_length,List.length_take,Nat.min_eq_left ht]
  simpa only [hl] using
    (show (history ψ g x (H.take t)++T).take (history ψ g x (H.take t)).length =
      history ψ g x (H.take t) by simp)
theorem take_succ (H : List (List Word)) (t : ℕ) (ht : t<H.length) :
    H.take (t+1)=H.take t++[H.getD t []] := by
  induction H generalizing t with
  | nil => simp at ht
  | cons B H ih =>
    cases t with
    | zero => simp
    | succ t =>
      have hh : t<H.length := by simpa using ht
      simpa [List.take_succ_cons] using congrArg (fun K => B::K) (ih t hh)
theorem history_getD (ψ : Word → Word → Word → Word) (g : Student) (x : Word)
    (H : List (List Word)) (t : ℕ) (ht : t<H.length) :
    (history ψ g x H).getD t []=
      batch ψ g x (history ψ g x (H.take t)) (H.getD t []) := by
  have hh := history_take ψ g x H (t+1) (by omega)
  rw [take_succ H t ht,history_append] at hh
  have he := congrArg (fun K : List (List Word) => K.getD t []) hh
  have hk : (history ψ g x (H.take t)).length=t := by
    rw [history_length,List.length_take,Nat.min_eq_left (by omega)]
  have ht' : t<(history ψ g x H).length := by simpa [history_length] using ht
  have hleft : ((history ψ g x H).take (t+1)).getD t []=(history ψ g x H).getD t [] := by
    rw [List.getD_eq_getElem _ _ (by simp [history_length]; omega),
      List.getD_eq_getElem _ _ ht']
    simp only [List.getElem_take]
  have hright : (history ψ g x (H.take t)++[batch ψ g x (history ψ g x (H.take t)) (H.getD t [])]).getD t []=
      batch ψ g x (history ψ g x (H.take t)) (H.getD t []) := by
    simpa only [hk] using
      (show (history ψ g x (H.take t)++[batch ψ g x (history ψ g x (H.take t)) (H.getD t [])]).getD
        (history ψ g x (H.take t)).length []=batch ψ g x (history ψ g x (H.take t)) (H.getD t []) by simp)
  exact hleft.symm.trans (he.trans hright)

theorem zip_width (ψ : Word → Word → Word → Word) (x : Word) (u v : ℕ)
    (hlen : ∀ y z : Word,z.length=u → (ψ x y z).length=v)
    (C B : List Word) (hB : ∀ z∈B,z.length=u) :
    ∀ z∈List.zipWith (ψ x) C B,z.length=v := by
  induction C generalizing B with
  | nil => simp
  | cons y C ih =>
    cases B with
    | nil => simp
    | cons z B =>
      intro w hw
      simp only [List.zipWith_cons_cons,List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact hlen y z (hB z List.mem_cons_self)
      · exact ih B (fun a ha => hB a (List.mem_cons_of_mem z ha)) w hw
theorem zip_getD (ψ : Word → Word → Word → Word) (x : Word) (C B : List Word) (j : ℕ)
    (hC : j<C.length) (hB : j<B.length) :
    (List.zipWith (ψ x) C B).getD j []=ψ x (C.getD j []) (B.getD j []) := by
  induction C generalizing B j with
  | nil => simp at hC
  | cons y C ih =>
    cases B with
    | nil => simp at hB
    | cons z B =>
      cases j with
      | zero => rfl
      | succ j => simpa using ih B j (by simpa using hC) (by simpa using hB)

theorem foldl_shape {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (ψ : Word → Word → Word → Word)
    (hlen : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x y z).length=Q.refutationLength.eval x.length)
    (g : Student) (hg : StudentShape Q r q g) (x : Word) (H K : List (List Word))
    (hH : ∀ B∈H,B.length=resource q x.length ∧ ∀ z∈B,z.length=P.refutationLength.eval x.length)
    (hK : HistoryShape K.length (resource q x.length) (Q.refutationLength.eval x.length) K)
    (hbudget : K.length+H.length≤resource r x.length) :
    HistoryShape (K.length+H.length) (resource q x.length) (Q.refutationLength.eval x.length)
      (H.foldl (advance ψ g x) K) := by
  induction H generalizing K with
  | nil => simpa using hK
  | cons B H ih =>
    have hB := hH B List.mem_cons_self
    have hround : K.length<resource r x.length := by simp only [List.length_cons] at hbudget; omega
    obtain ⟨b,hgshape⟩ := hg.1
    have hC := (hgshape x K.length K hround hK).1
    have hbatch : (batch ψ g x K B).length=resource q x.length ∧
        ∀ z∈batch ψ g x K B,z.length=Q.refutationLength.eval x.length := by
      refine ⟨?_,zip_width ψ x _ _ (hlen x) _ _ hB.2⟩
      simp only [batch,List.length_zipWith,hC,hB.1,Nat.min_self]
    have hnext : HistoryShape (advance ψ g x K B).length (resource q x.length)
        (Q.refutationLength.eval x.length) (advance ψ g x K B) := by
      refine ⟨rfl,?_⟩
      intro D hD
      rcases List.mem_append.mp hD with hD | hD
      · exact hK.2 D hD
      · simpa using (List.mem_singleton.mp hD) ▸ hbatch
    have hrest := ih (advance ψ g x K B)
      (fun D hD => hH D (List.mem_cons_of_mem B hD)) hnext (by
        simp only [advance,List.length_append,List.length_singleton,List.length_cons,List.length_nil] at *
        omega)
    simpa [advance,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hrest

theorem history_shape {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (ψ : Word → Word → Word → Word)
    (hlen : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x y z).length=Q.refutationLength.eval x.length)
    (g : Student) (hg : StudentShape Q r q g) (x : Word) (t : ℕ) (H : List (List Word))
    (ht : t≤resource r x.length)
    (hH : HistoryShape t (resource q x.length) (P.refutationLength.eval x.length) H) :
    HistoryShape t (resource q x.length) (Q.refutationLength.eval x.length) (history ψ g x H) := by
  have hh := foldl_shape P Q r q ψ hlen g hg x H [] hH.2
    ⟨rfl,by simp⟩ (by simpa [hH.1] using ht)
  simpa [history,hH.1] using hh

theorem shape {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (ψ : Word → Word → Word → Word)
    (hlen : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x y z).length=Q.refutationLength.eval x.length)
    (g : Student) (hg : StudentShape Q r q g) : StudentShape P r q (student ψ g) := by
  obtain ⟨b,hb⟩ := hg.1
  refine ⟨⟨b,?_⟩,?_⟩
  · intro x t H ht hH
    exact hb x t _ ht (history_shape P Q r q ψ hlen g hg x t H (by omega) hH)
  · intro x t H ht
    exact hg.2 x t _ ht

theorem wins {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (ψ : Word → Word → Word → Word)
    (hlen : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x y z).length=Q.refutationLength.eval x.length)
    (htest : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      Q.test x y (ψ x y z) → P.test x y z)
    (g : Student) (hshape : StudentShape Q r q g) (hwin : StudentWins Q r q g) :
    StudentWins P r q (student ψ g) := by
  intro x H hH
  have hK := history_shape P Q r q ψ hlen g hshape x _ H le_rfl hH
  obtain ⟨t,ht,j,hj,haccept⟩ := hwin x (history ψ g x H) hK
  have htH : t<H.length := by rw [hH.1]; exact ht
  have hHp : HistoryShape t (resource q x.length) (P.refutationLength.eval x.length) (H.take t) :=
    ⟨by simp [hH.1,Nat.min_eq_left (by omega : t≤resource r x.length)],
      fun B hB => hH.2 B (List.mem_of_mem_take hB)⟩
  have hKp := history_shape P Q r q ψ hlen g hshape x t (H.take t) (by omega) hHp
  obtain ⟨b,hb⟩ := hshape.1
  have hC := (hb x t _ ht hKp).1
  have hBmem : H.getD t [] ∈ H := by
    rw [List.getD_eq_getElem _ _ htH]
    exact List.getElem_mem _
  have hB := hH.2 _ hBmem
  rw [history_take ψ g x H t (by omega),history_getD ψ g x H t htH] at haccept
  have he : (batch ψ g x (history ψ g x (H.take t)) (H.getD t [])).getD j []=
      ψ x ((g x t (history ψ g x (H.take t))).getD j []) ((H.getD t []).getD j []) := by
    unfold batch
    rw [history_length,hHp.1]
    exact zip_getD ψ x _ _ j (by rw [hC]; exact hj) (by rw [hB.1]; exact hj)
  rw [he] at haccept
  refine ⟨t,ht,j,hj,htest x _ _ ?_ haccept⟩
  have hjB : j<(H.getD t []).length := by rw [hB.1]; exact hj
  exact hB.2 _ (by
    rw [List.getD_eq_getElem (H.getD t []) [] hjB]
    exact List.getElem_mem _)

end StudentTeacher976.Adaptivity.CausalPresentationTranslation
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CausalTranslationData
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)

def encode (x : Word) (u : ℕ) (K H : List (List Word)) : Word :=
  tup [x,List.replicate u true,tup (K.map tup),tup (H.map tup)]
def index (s : Word) : ℕ := (field s 1).length
def converted (s : Word) : List (List Word) :=
  (TupleCodec.decodeTuple (field s 2)).map TupleCodec.decodeTuple
def original (s : Word) : List (List Word) :=
  (TupleCodec.decodeTuple (field s 3)).map TupleCodec.decodeTuple
def guessInput (s : Word) : Word :=
  tup [field s 0,List.replicate (index s+1) true,field s 2]
def reply (s : Word) : List Word := (original s).getD (index s) []
def pairArguments (s : Word) : Word :=
  let state := field s 0
  let C := TupleCodec.decodeTuple (field s 1)
  tup ((C.zip (reply state)).map (fun yz => tup [field state 0,yz.1,yz.2]))
def finish (s : Word) : Word :=
  let state := field s 0
  encode (field state 0) (index state+1)
    (converted state++[TupleCodec.decodeTuple (field s 1)]) (original state)
def step (F T : Word → Word) (s : Word) : Word :=
  finish (tup [s,T (pairArguments (tup [s,F (guessInput s)]))])
def code (ψ : Word → Word → Word → Word) (s : Word) : Word :=
  ψ (field s 0) (field s 1) (field s 2)
def mappedCode (ψ : Word → Word → Word → Word) (s : Word) : Word :=
  tup ((TupleCodec.decodeTuple s).map (code ψ))

theorem encode_poly :
    ComputableTidilyInPolyTime (fun p : Word × ℕ × List (List Word) × List (List Word) =>
      encode p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encBits (encPair encUnary (encPair (encList (encList encBits)) (encList (encList encBits))))) encBits := by
  have hK := (ComputableTidilyInPolyTime.map TupleCodec.encode_poly).comp
    (encIn := encPair encBits (encPair encUnary (encPair (encList (encList encBits)) (encList (encList encBits)))))
    (g := fun p : Word × ℕ × List (List Word) × List (List Word) => p.2.2.1) (by fun_prop)
  have hH := (ComputableTidilyInPolyTime.map TupleCodec.encode_poly).comp
    (encIn := encPair encBits (encPair encUnary (encPair (encList (encList encBits)) (encList (encList encBits)))))
    (g := fun p : Word × ℕ × List (List Word) × List (List Word) => p.2.2.2) (by fun_prop)
  have hKe := TupleCodec.encode_poly.comp hK
  have hHe := TupleCodec.encode_poly.comp hH
  unfold encode
  apply TupleCodec.encode_poly.comp
  fun_prop
theorem index_poly : ComputableTidilyInPolyTime index encBits encUnary :=
  ComputableTidilyInPolyTime.length_bits.comp (field_poly 1)
theorem converted_poly : ComputableTidilyInPolyTime converted encBits (encList (encList encBits)) :=
  (ComputableTidilyInPolyTime.map TupleCodec.decoder_poly.tidy).comp
    (TupleCodec.decoder_poly.tidy.comp (field_poly 2))
theorem original_poly : ComputableTidilyInPolyTime original encBits (encList (encList encBits)) :=
  (ComputableTidilyInPolyTime.map TupleCodec.decoder_poly.tidy).comp
    (TupleCodec.decoder_poly.tidy.comp (field_poly 3))
theorem guessInput_poly : ComputableTidilyInPolyTime guessInput encBits encBits := by
  have hx := field_poly 0
  have hi := index_poly
  have hK := field_poly 2
  unfold guessInput
  apply TupleCodec.encode_poly.comp
  fun_prop
theorem reply_poly : ComputableTidilyInPolyTime reply encBits (encList encBits) := by
  exact (ComputableTidilyInPolyTime.listGetD (encA := encList encBits)
    (encL := encList (encList encBits)) []).comp (original_poly.prod index_poly)
theorem pairArguments_poly : ComputableTidilyInPolyTime pairArguments encBits encBits := by
  have hs := field_poly 0
  have hC := TupleCodec.decoder_poly.tidy.comp (field_poly 1)
  have hB := reply_poly.comp hs
  have hz := (ComputableTidilyInPolyTime.zip encBits encBits).comp (hC.prod hB)
  unfold pairArguments
  apply TupleCodec.encode_poly.comp
  apply ComputableTidilyInPolyTime.mapWithInput hz
  apply TupleCodec.encode_poly.comp
  have hx := ((field_poly 0).comp hs).comp
    (ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits))
  fun_prop
theorem finish_poly : ComputableTidilyInPolyTime finish encBits encBits := by
  have hs := field_poly 0
  have hx := (field_poly 0).comp hs
  have hi := index_poly.comp hs
  have hK := converted_poly.comp hs
  have hH := original_poly.comp hs
  have hB := TupleCodec.decoder_poly.tidy.comp (field_poly 1)
  unfold finish
  apply encode_poly.comp (g := fun s : Word =>
    (field (field s 0) 0,index (field s 0)+1,
      converted (field s 0)++[TupleCodec.decodeTuple (field s 1)],original (field s 0)))
  fun_prop
theorem step_inFP (i : ℕ) (F T : Word → Word) (hF : InFP i F) (hT : InFP i T) :
    InFP i (step F T) := by
  have hG := OracleComputations.inFP_compose i guessInput F (pure_inFP i _ guessInput_poly) hF
  have hA := OracleComputations.inFP_post i _ pairArguments
    (OracleComputations.inFP_retain i _ hG) pairArguments_poly
  have hB := OracleComputations.inFP_compose i _ T hA hT
  exact OracleComputations.inFP_post i _ finish (OracleComputations.inFP_retain i _ hB) finish_poly
theorem mappedCode_inFP (i : ℕ) (ψ : Word → Word → Word → Word) (hψ : InFP i (code ψ)) :
    InFP i (mappedCode ψ) := OracleWordMap.uniform i _ hψ

theorem index_encode (x : Word) (u : ℕ) (K H : List (List Word)) : index (encode x u K H)=u := by
  simp [index,encode,field,TupleCodec.decode_tup]
theorem converted_encode (x : Word) (u : ℕ) (K H : List (List Word)) : converted (encode x u K H)=K := by
  simp [converted,encode,field,TupleCodec.decode_tup,List.map_map,Function.comp_def]
theorem original_encode (x : Word) (u : ℕ) (K H : List (List Word)) : original (encode x u K H)=H := by
  simp [original,encode,field,TupleCodec.decode_tup,List.map_map,Function.comp_def]
theorem guessInput_encode (x : Word) (u : ℕ) (K H : List (List Word)) :
    guessInput (encode x u K H)=tup [x,List.replicate (u+1) true,tup (K.map tup)] := by
  simp [guessInput,index,encode,field,TupleCodec.decode_tup]
theorem pairArguments_encode (x : Word) (u : ℕ) (K H : List (List Word)) (C : List Word) :
    pairArguments (tup [encode x u K H,tup C])=
      tup ((C.zip (H.getD u [])).map (fun yz => tup [x,yz.1,yz.2])) := by
  simp [pairArguments,reply,index,original,encode,field,TupleCodec.decode_tup,List.map_map,Function.comp_def]
theorem zip_map (f : Word → Word → Word) (C B : List Word) :
    (C.zip B).map (fun yz => f yz.1 yz.2)=List.zipWith f C B := by
  induction C generalizing B with
  | nil => simp
  | cons y C ih =>
    cases B with
    | nil => simp
    | cons z B => simpa using congrArg (fun l => f y z::l) (ih B)
theorem mappedCode_pairArguments (ψ : Word → Word → Word → Word)
    (x : Word) (u : ℕ) (K H : List (List Word)) (C : List Word) :
    mappedCode ψ (pairArguments (tup [encode x u K H,tup C]))=
      tup (List.zipWith (ψ x) C (H.getD u [])) := by
  rw [pairArguments_encode]
  simp [mappedCode,TupleCodec.decode_tup,List.map_map,Function.comp_def,code,field,
    zip_map]
theorem step_encode (ψ : Word → Word → Word → Word) (F : Word → Word) (g : Student)
    (hF : ∀ x t H,F (tup [x,List.replicate (t+1) true,tup (H.map tup)])=tup (g x t H))
    (x : Word) (u : ℕ) (K H : List (List Word)) :
    step F (mappedCode ψ) (encode x u K H)=
      encode x (u+1) (K++[List.zipWith (ψ x) (g x u K) (H.getD u [])]) H := by
  unfold step
  rw [guessInput_encode,hF,mappedCode_pairArguments]
  simp [finish,index,converted,original,field,TupleCodec.decode_tup,encode,List.map_map,Function.comp_def]

end StudentTeacher976.Adaptivity.CausalTranslationData
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CausalTranslationClamp
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)

def fit (w : ℕ) (z : Word) : Word := (z++List.replicate w false).take w
def batch (q w : ℕ) (B : List Word) : List Word := (List.range q).map (fun j => fit w (B.getD j []))
def histories (q w : ℕ) (H : List (List Word)) : List (List Word) := H.map (batch q w)
def parsed (s : Word) : List (List Word) :=
  (TupleCodec.decodeTuple (field s 2)).map TupleCodec.decodeTuple
def normalized (q : ℕ → ℕ) (p : Polynomial ℕ) (s : Word) : List (List Word) :=
  histories (resource q (field s 0).length) (p.eval (field s 0).length) (parsed s)
def prep (q : ℕ → ℕ) (p : Polynomial ℕ) (s : Word) : ℕ × Word :=
  ((normalized q p s).length,CausalTranslationData.encode (field s 0) 0 [] (normalized q p s))

theorem fit_length (w : ℕ) (z : Word) : (fit w z).length=w := by simp [fit]
theorem fit_eq (w : ℕ) (z : Word) (hz : z.length=w) : fit w z=z := by
  unfold fit
  rw [← hz,List.take_left]
theorem batch_shape (q w : ℕ) (B : List Word) :
    (batch q w B).length=q ∧ ∀ z∈batch q w B,z.length=w := by
  refine ⟨by simp [batch],?_⟩
  intro z hz
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
  exact fit_length w _
theorem histories_shape (q w : ℕ) (H : List (List Word)) :
    HistoryShape H.length q w (histories q w H) := by
  refine ⟨by simp [histories],?_⟩
  intro B hB
  obtain ⟨C,hC,rfl⟩ := List.mem_map.mp hB
  exact batch_shape q w C
theorem batch_eq (q w : ℕ) (B : List Word)
    (hB : B.length=q ∧ ∀ z∈B,z.length=w) : batch q w B=B := by
  apply List.ext_getElem
  · simp [batch,hB.1]
  · intro j hj hjB
    simp only [batch,List.getElem_map,List.getElem_range]
    have he := List.getD_eq_getElem B [] hjB
    rw [fit_eq w _ (hB.2 _ (by rw [he]; exact List.getElem_mem _)),he]
theorem histories_eq (q w t : ℕ) (H : List (List Word)) (hH : HistoryShape t q w H) :
    histories q w H=H := by
  apply List.ext_getElem
  · simp [histories]
  · intro j hj hjH
    simp only [histories,List.getElem_map]
    exact batch_eq q w H[j] (hH.2 _ (List.getElem_mem _))

theorem fit_poly : ComputableTidilyInPolyTime (fun p : ℕ × Word => fit p.1 p.2)
    (encPair encUnary encBits) encBits := by
  unfold fit
  fun_prop
theorem batch_poly : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × List Word => batch p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encUnary (encList encBits))) (encList encBits) := by
  unfold batch
  apply ComputableTidilyInPolyTime.mapWithInput (by fun_prop)
  apply fit_poly.comp (g := fun p : (ℕ × ℕ × List Word) × ℕ => (p.1.2.1,p.1.2.2.getD p.2 []))
  fun_prop
theorem histories_poly :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ × List (List Word) => histories p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encUnary (encList (encList encBits)))) (encList (encList encBits)) := by
  unfold histories
  apply ComputableTidilyInPolyTime.mapWithInput (by fun_prop)
  apply batch_poly.comp (g := fun p : (ℕ × ℕ × List (List Word)) × List Word => (p.1.1,p.1.2.1,p.2))
  fun_prop
theorem parsed_poly : ComputableTidilyInPolyTime parsed encBits (encList (encList encBits)) :=
  (ComputableTidilyInPolyTime.map TupleCodec.decoder_poly.tidy).comp
    (TupleCodec.decoder_poly.tidy.comp (field_poly 2))
theorem normalized_poly (q : ℕ → ℕ) (hq : PolyTimeLength q) (p : Polynomial ℕ) :
    ComputableTidilyInPolyTime (normalized q p) encBits (encList (encList encBits)) := by
  have hx := field_poly 0
  have hqv := (resource_function_pure q hq).comp hx
  have hp := (ComputableTidilyInPolyTime.unary_eval p).comp (ComputableTidilyInPolyTime.length_bits.comp hx)
  unfold normalized
  apply histories_poly.comp (g := fun s : Word =>
    (resource q (field s 0).length,p.eval (field s 0).length,parsed s))
  exact hqv.prod (hp.prod parsed_poly)
theorem prep_poly (q : ℕ → ℕ) (hq : PolyTimeLength q) (p : Polynomial ℕ) :
    ComputableTidilyInPolyTime (prep q p) encBits (encPair encUnary encBits) := by
  have hH := normalized_poly q hq p
  have hx := field_poly 0
  have he := CausalTranslationData.encode_poly.comp
    (hx.prod ((ComputableTidilyInPolyTime.const 0).prod ((ComputableTidilyInPolyTime.const []).prod hH)))
  exact ((ComputableTidilyInPolyTime.length_list (encList encBits)).comp hH).prod he

theorem normalized_encoded (q : ℕ → ℕ) (p : Polynomial ℕ)
    (x : Word) (t : ℕ) (H : List (List Word)) :
    normalized q p (tup [x,List.replicate (t+1) true,tup (H.map tup)])=
      histories (resource q x.length) (p.eval x.length) H := by
  simp [normalized,parsed,field,TupleCodec.decode_tup,List.map_map,Function.comp_def]

end StudentTeacher976.Adaptivity.CausalTranslationClamp
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CausalTranslationRuntime
open QAdvFew.PoQOracle
open CausalPresentationTranslation (history history_length)

theorem history_bounds {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (ψ : Word → Word → Word → Word)
    (hlen : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x y z).length=Q.refutationLength.eval x.length)
    (g : Student) (hg : StudentShape Q r q g) (x : Word) (H : List (List Word))
    (hH : ∀ B∈H,B.length=resource q x.length ∧ ∀ z∈B,z.length=P.refutationLength.eval x.length) :
    ∀ B∈history ψ g x H,B.length≤resource q x.length ∧
      ∀ z∈B,z.length=Q.refutationLength.eval x.length := by
  intro B hB
  obtain ⟨t,ht,hget⟩ := List.mem_iff_getElem.mp hB
  have htH : t<H.length := by simpa only [history_length] using ht
  have hAt := CausalPresentationTranslation.history_getD ψ g x H t htH
  rw [List.getD_eq_getElem _ _ ht,hget] at hAt
  rw [hAt]
  have hBmem : H.getD t []∈H := by
    rw [List.getD_eq_getElem _ _ htH]
    exact List.getElem_mem _
  have hBt := hH _ hBmem
  by_cases hround : t<resource r x.length
  · have hHp : HistoryShape t (resource q x.length) (P.refutationLength.eval x.length) (H.take t) :=
      ⟨by simp [Nat.min_eq_left (by omega : t≤H.length)],
        fun D hD => hH D (List.mem_of_mem_take hD)⟩
    have hKp := CausalPresentationTranslation.history_shape P Q r q ψ hlen g hg x t
      (H.take t) (by omega) hHp
    obtain ⟨b,hb⟩ := hg.1
    have hC := (hb x t _ hround hKp).1
    refine ⟨?_,CausalPresentationTranslation.zip_width ψ x _ _ (hlen x) _ _ hBt.2⟩
    simp only [CausalPresentationTranslation.batch,history_length,hHp.1,List.length_zipWith,hC,hBt.1,Nat.min_self]
    rfl
  · have hk : (history ψ g x (H.take t)).length=t := by
      rw [history_length,List.length_take,Nat.min_eq_left (by omega)]
    have hempty := hg.2 x t (history ψ g x (H.take t)) (by omega)
    simp [CausalPresentationTranslation.batch,hk,hempty]

theorem iterate_encode (ψ : Word → Word → Word → Word) (F : Word → Word) (g : Student)
    (hF : ∀ x t H,F (tup [x,List.replicate (t+1) true,tup (H.map tup)])=tup (g x t H))
    (x : Word) (H : List (List Word)) (j : ℕ) (hj : j≤H.length) :
    (CausalTranslationData.step F (CausalTranslationData.mappedCode ψ))^[j]
      (CausalTranslationData.encode x 0 [] H)=
        CausalTranslationData.encode x j (history ψ g x (H.take j)) H := by
  induction j with
  | zero => simp [history]
  | succ j ih =>
    have hj' : j≤H.length := by omega
    have hjlt : j<H.length := by omega
    rw [Function.iterate_succ_apply',ih hj',CausalTranslationData.step_encode ψ F g hF,
      CausalPresentationTranslation.take_succ H j hjlt,CausalPresentationTranslation.history_append]
    congr 2
    unfold CausalPresentationTranslation.batch
    have hk : (history ψ g x (H.take j)).length=j := by
      rw [history_length,List.length_take,Nat.min_eq_left hj']
    rw [hk]

theorem encode_length (x : Word) (u : ℕ) (K H : List (List Word)) :
    (CausalTranslationData.encode x u K H).length=
      2*x.length+2*u+2*(tup (K.map tup)).length+2*(tup (H.map tup)).length+8 := by
  unfold CausalTranslationData.encode
  rw [AdviceEncoding.tup_cons_length,AdviceEncoding.tup_cons_length,
    AdviceEncoding.tup_cons_length,AdviceEncoding.tup_cons_length]
  simp only [List.length_replicate,tup,List.flatMap_nil,List.length_nil]
  omega

end StudentTeacher976.Adaptivity.CausalTranslationRuntime
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CausalTranslationRuntime
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field)
open CausalPresentationTranslation (history history_length)

theorem orbit_bounds {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (hq : PolyTimeLength q) (ψ : Word → Word → Word → Word)
    (hlen : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x y z).length=Q.refutationLength.eval x.length)
    (g : Student) (hg : StudentShape Q r q g) (F : Word → Word)
    (hF : ∀ x t H,F (tup [x,List.replicate (t+1) true,tup (H.map tup)])=tup (g x t H)) :
    ∃ B : Polynomial ℕ,∀ s : Word,∀ j≤(CausalTranslationClamp.prep q P.refutationLength s).1,
      ((CausalTranslationData.step F (CausalTranslationData.mappedCode ψ))^[j]
        (CausalTranslationClamp.prep q P.refutationLength s).2).length≤B.eval s.length := by
  obtain ⟨E,hE⟩ := (CausalTranslationClamp.prep_poly q hq P.refutationLength).polyBounded_length.exists_polynomial
  obtain ⟨D,hD⟩ := (resource_function_pure q hq).polyBounded_length.exists_polynomial
  simp only [encUnary_apply,List.length_replicate,encBits_apply] at hD
  refine ⟨10*E+8*E*(D.comp E)*(Q.refutationLength.comp E+1)+8,?_⟩
  intro s j hj
  let x := field s 0
  let H := CausalTranslationClamp.normalized q P.refutationLength s
  let A := E.eval s.length
  let N := D.eval A
  let W := Q.refutationLength.eval A
  have hprep : CausalTranslationClamp.prep q P.refutationLength s=
      (H.length,CausalTranslationData.encode x 0 [] H) := rfl
  have hinit : (CausalTranslationData.encode x 0 [] H).length≤A := by
    have hh := hE s
    rw [hprep] at hh
    simp only [encPair_apply,List.length_append,length_frame,encUnary_apply,List.length_replicate,encBits_apply] at hh
    dsimp only [A]
    omega
  have hcount : H.length≤A := by
    have hh := hE s
    rw [hprep] at hh
    simp only [encPair_apply,List.length_append,length_frame,encUnary_apply,List.length_replicate,encBits_apply] at hh
    dsimp only [A]
    omega
  have hx : x.length≤A := by
    apply (SerializationBounds.word_le_tup
      [x,[],tup ([] : List Word),tup (H.map tup)] x (by simp)).trans
    exact hinit
  have hHcode : (tup (H.map tup)).length≤A := by
    apply (SerializationBounds.word_le_tup
      [x,[],tup ([] : List Word),tup (H.map tup)] (tup (H.map tup)) (by simp)).trans
    exact hinit
  have hjH : j≤H.length := by simpa only [hprep] using hj
  have hjA := hjH.trans hcount
  have hN : resource q x.length≤N := (hD x).trans (NativeBatch.polyEvalMono D hx)
  have hW : Q.refutationLength.eval x.length≤W := NativeBatch.polyEvalMono Q.refutationLength hx
  have hlegal : ∀ B∈H,B.length=resource q x.length ∧
      ∀ z∈B,z.length=P.refutationLength.eval x.length :=
    (CausalTranslationClamp.histories_shape (resource q x.length)
      (P.refutationLength.eval x.length) (CausalTranslationClamp.parsed s)).2
  have hpast := history_bounds P Q r q ψ hlen g hg x (H.take j)
    (fun B hB => hlegal B (List.mem_of_mem_take hB))
  have hk : (history ψ g x (H.take j)).length=j := by
    rw [history_length,List.length_take,Nat.min_eq_left hjH]
  have hbatch : ∀ B∈history ψ g x (H.take j),(tup B).length≤2*N*(W+1) := by
    intro B hB
    have hb := hpast B hB
    apply (AdviceEncoding.tup_bound B W (fun z hz => (hb.2 z hz).le.trans hW)).trans
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (hb.1.trans hN))
  have hK := AdviceEncoding.tup_bound ((history ψ g x (H.take j)).map tup) (2*N*(W+1)) (by
    intro w hw
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hw
    exact hbatch B hB)
  simp only [List.length_map,hk] at hK
  have hK' : (tup ((history ψ g x (H.take j)).map tup)).length≤2*A*(2*N*(W+1)+1) :=
    hK.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hjA))
  rw [hprep]
  rw [iterate_encode ψ F g hF x H j hjH,encode_length]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_comp]
  change 2*x.length+2*j+2*(tup ((history ψ g x (H.take j)).map tup)).length+
    2*(tup (H.map tup)).length+8≤10*A+8*A*N*(W+1)+8
  nlinarith

end StudentTeacher976.Adaptivity.CausalTranslationRuntime
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CausalTranslationUniform
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)

def student {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R) (q : ℕ → ℕ)
    (ψ : Word → Word → Word → Word) (g : Student) : Student :=
  fun x t H => g x t (CausalPresentationTranslation.history ψ g x
    (CausalTranslationClamp.histories (resource q x.length) (P.refutationLength.eval x.length) H))
def finalInput (s : Word) : Word :=
  tup [field (field s 0) 0,field (field s 0) 1,field (field s 1) 2]
theorem finalInput_poly : ComputableTidilyInPolyTime finalInput encBits encBits := by
  have hx := (field_poly 0).comp (field_poly 0)
  have ht := (field_poly 1).comp (field_poly 0)
  have hK := (field_poly 2).comp (field_poly 1)
  unfold finalInput
  apply TupleCodec.encode_poly.comp
  fun_prop
theorem finalInput_encoded (x : Word) (t u : ℕ) (H K A : List (List Word)) :
    finalInput (tup [tup [x,List.replicate (t+1) true,tup (H.map tup)],
      CausalTranslationData.encode x u K A])=
        tup [x,List.replicate (t+1) true,tup (K.map tup)] := by
  simp [finalInput,CausalTranslationData.encode,field,TupleCodec.decode_tup]

theorem uniform {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (hq : PolyTimeLength q) (ψ : Word → Word → Word → Word)
    (hψ : InFP i (CausalTranslationData.code ψ))
    (hlen : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x y z).length=Q.refutationLength.eval x.length)
    (g : Student) (hg : UniformStudent i g) (hshape : StudentShape Q r q g) :
    UniformStudent i (student P q ψ g) := by
  obtain ⟨F,hF,hFspec⟩ := hg
  let T := CausalTranslationData.mappedCode ψ
  have hT : InFP i T := CausalTranslationData.mappedCode_inFP i ψ hψ
  let S := CausalTranslationData.step F T
  have hS : InFP i S := CausalTranslationData.step_inFP i F T hF hT
  let prep := CausalTranslationClamp.prep q P.refutationLength
  obtain ⟨B,hB⟩ := CausalTranslationRuntime.orbit_bounds P Q r q hq ψ hlen g hshape F hFspec
  have hiter := NativeIteration.inFP_iterate i S hS prep
    (CausalTranslationClamp.prep_poly q hq P.refutationLength) B hB
  let I := fun s => S^[(prep s).1] (prep s).2
  have harg := OracleComputations.inFP_post i _ finalInput
    (OracleComputations.inFP_retain i I hiter) finalInput_poly
  refine ⟨fun s => F (finalInput (tup [s,I s])),OracleComputations.inFP_compose i _ F harg hF,?_⟩
  intro x t H
  let H' := CausalTranslationClamp.histories (resource q x.length) (P.refutationLength.eval x.length) H
  have hprep : prep (tup [x,List.replicate (t+1) true,tup (H.map tup)])=
      (H'.length,CausalTranslationData.encode x 0 [] H') := by
    unfold prep CausalTranslationClamp.prep
    rw [CausalTranslationClamp.normalized_encoded]
    simp [field,TupleCodec.decode_tup,H']
  have hI : I (tup [x,List.replicate (t+1) true,tup (H.map tup)])=
      CausalTranslationData.encode x H'.length (CausalPresentationTranslation.history ψ g x H') H' := by
    unfold I
    rw [hprep]
    change (CausalTranslationData.step F (CausalTranslationData.mappedCode ψ))^[H'.length]
      (CausalTranslationData.encode x 0 [] H')=_
    rw [CausalTranslationRuntime.iterate_encode ψ F g hFspec x H' H'.length le_rfl,List.take_length]
  change F (finalInput (tup [tup [x,List.replicate (t+1) true,tup (H.map tup)],
    I (tup [x,List.replicate (t+1) true,tup (H.map tup)])]))=_
  rw [hI,finalInput_encoded,hFspec]
  rfl

theorem shape {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (ψ : Word → Word → Word → Word)
    (hlen : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x y z).length=Q.refutationLength.eval x.length)
    (g : Student) (hg : StudentShape Q r q g) : StudentShape P r q (student P q ψ g) := by
  obtain ⟨b,hb⟩ := hg.1
  refine ⟨⟨b,?_⟩,?_⟩
  · intro x t H ht hH
    simp only [student]
    rw [CausalTranslationClamp.histories_eq _ _ _ H hH]
    exact hb x t _ ht (CausalPresentationTranslation.history_shape P Q r q ψ hlen g hg x t H (by omega) hH)
  · intro x t H ht
    exact hg.2 x t _ ht

theorem wins {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (ψ : Word → Word → Word → Word)
    (hlen : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x y z).length=Q.refutationLength.eval x.length)
    (htest : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      Q.test x y (ψ x y z) → P.test x y z)
    (g : Student) (hshape : StudentShape Q r q g) (hwin : StudentWins Q r q g) :
    StudentWins P r q (student P q ψ g) := by
  have hw := CausalPresentationTranslation.wins P Q r q ψ hlen htest g hshape hwin
  intro x H hH
  obtain ⟨t,ht,j,hj,haccept⟩ := hw x H hH
  refine ⟨t,ht,j,hj,?_⟩
  have hHp : HistoryShape t (resource q x.length) (P.refutationLength.eval x.length) (H.take t) :=
    ⟨by simp [hH.1,Nat.min_eq_left (by omega : t≤resource r x.length)],
      fun B hB => hH.2 B (List.mem_of_mem_take hB)⟩
  change P.test x ((g x t _).getD j []) _
  rw [CausalTranslationClamp.histories_eq _ _ _ _ hHp]
  exact haccept

theorem transfer {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (hq : PolyTimeLength q) (ψ : Word → Word → Word → Word)
    (hψ : InFP i (CausalTranslationData.code ψ))
    (hlen : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x y z).length=Q.refutationLength.eval x.length)
    (htest : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      Q.test x y (ψ x y z) → P.test x y z)
    (g : Student) (hg : UniformStudent i g) (hshape : StudentShape Q r q g) (hwin : StudentWins Q r q g) :
    UniformStudent i (student P q ψ g) ∧ StudentShape P r q (student P q ψ g) ∧
      StudentWins P r q (student P q ψ g) :=
  ⟨uniform P Q r q hq ψ hψ hlen g hg hshape,shape P Q r q ψ hlen g hshape,
    wins P Q r q ψ hlen htest g hshape hwin⟩

end StudentTeacher976.Adaptivity.CausalTranslationUniform
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceCausalTranslation
open QAdvFew.PoQOracle
open AdviceComputations (InFPAdvice)
open AdviceTeacherData (field)
open CausalTranslationUniform (student finalInput finalInput_poly finalInput_encoded)

theorem step_advice (i : ℕ) (F T : Word → Word) (hF : InFPAdvice i F) (hT : InFPAdvice i T) :
    InFPAdvice i (CausalTranslationData.step F T) := by
  have hG := AdviceComputations.compose i CausalTranslationData.guessInput F
    (AdviceComputations.uniform i _ (pure_inFP i _ CausalTranslationData.guessInput_poly)) hF
  have hA := AdviceComputations.post i _ CausalTranslationData.pairArguments
    (AdviceComputations.retain i _ hG) (pure_inFP i _ CausalTranslationData.pairArguments_poly)
  have hB := AdviceComputations.compose i _ T hA hT
  exact AdviceComputations.post i _ CausalTranslationData.finish (AdviceComputations.retain i _ hB)
    (pure_inFP i _ CausalTranslationData.finish_poly)

theorem uniform {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (r q : ℕ → ℕ) (hq : PolyTimeLength q) (ψ : Word → Word → Word → Word)
    (hψ : InFPAdvice i (CausalTranslationData.code ψ))
    (hlen : ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
      (ψ x y z).length=Q.refutationLength.eval x.length)
    (g : Student) (hg : AdviceStudents.UniformStudent i g) (hshape : StudentShape Q r q g) :
    AdviceStudents.UniformStudent i (student P q ψ g) := by
  obtain ⟨F,hF,hFspec⟩ := hg
  let T := CausalTranslationData.mappedCode ψ
  have hT : InFPAdvice i T := AdviceWordMap.uniform i _ hψ
  let S := CausalTranslationData.step F T
  have hS : InFPAdvice i S := step_advice i F T hF hT
  let prep := CausalTranslationClamp.prep q P.refutationLength
  obtain ⟨B,hB⟩ := CausalTranslationRuntime.orbit_bounds P Q r q hq ψ hlen g hshape F hFspec
  have hiter := AdviceIteration.bounded_iteration i S hS prep
    (CausalTranslationClamp.prep_poly q hq P.refutationLength) B hB
  let I := fun s => S^[(prep s).1] (prep s).2
  have harg := AdviceComputations.post i _ finalInput
    (AdviceComputations.retain i I hiter) (pure_inFP i _ finalInput_poly)
  refine ⟨fun s => F (finalInput (tup [s,I s])),AdviceComputations.compose i _ F harg hF,?_⟩
  intro x t H
  let H' := CausalTranslationClamp.histories (resource q x.length) (P.refutationLength.eval x.length) H
  have hprep : prep (tup [x,List.replicate (t+1) true,tup (H.map tup)])=
      (H'.length,CausalTranslationData.encode x 0 [] H') := by
    unfold prep CausalTranslationClamp.prep
    rw [CausalTranslationClamp.normalized_encoded]
    simp [field,TupleCodec.decode_tup,H']
  have hI : I (tup [x,List.replicate (t+1) true,tup (H.map tup)])=
      CausalTranslationData.encode x H'.length (CausalPresentationTranslation.history ψ g x H') H' := by
    unfold I
    rw [hprep]
    change (CausalTranslationData.step F (CausalTranslationData.mappedCode ψ))^[H'.length]
      (CausalTranslationData.encode x 0 [] H')=_
    rw [CausalTranslationRuntime.iterate_encode ψ F g hFspec x H' H'.length le_rfl,List.take_length]
  change F (finalInput (tup [tup [x,List.replicate (t+1) true,tup (H.map tup)],
    I (tup [x,List.replicate (t+1) true,tup (H.map tup)])]))=_
  rw [hI,finalInput_encoded,hFspec]
  rfl

end StudentTeacher976.Adaptivity.AdviceCausalTranslation
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CertifiedGame
open QAdvFew.PoQOracle

 theorem two_round {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R)
     (c : Polynomial ℕ) (V : Word → Word → Word → Prop)
     (heff : {s | ∃ x y z, s=tup [x,y,z] ∧ V x y z} ∈ Delta i)
     (hV : ∀ x y, R x y ↔ ∃ v, v.length=c.eval x.length ∧ V x y v) :
     R ∈ ST i (fun _ => 2) (fun _ => 1) := by
   let Q : RefutablePresentation i R :=
     { answerBound := P.answerBound
       refutationLength := CertifiedReply.width P.refutationLength P.answerBound c
       test := test P c V
       efficient := test_efficient P c V heff
       total := P.total
       bounded := P.bounded
       represents := represents P c V hV }
   refine ⟨Q,student P.refutationLength P.answerBound,
     student_uniform i P.refutationLength P.answerBound,?_,?_⟩
   · exact shape P Q
   · exact wins P c V hV Q (fun _ _ _ => Iff.rfl)

end StudentTeacher976.Adaptivity.CertifiedGame
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity
open QAdvFew.PoQOracle Turing.MultiTapeTM

 theorem finite_interpolation (f : Word → Word) (S : Finset Word) :
     ∃ F : Word → Word, ComputableTidilyInPolyTime F encBits encBits ∧ ∀ x∈S,F x=f x := by
   classical
   induction S using Finset.induction_on with
   | empty => exact ⟨fun _ => [],ComputableTidilyInPolyTime.const [],by simp⟩
   | @insert a S ha ih =>
     obtain ⟨G,hG,hspec⟩ := ih
     refine ⟨fun x => if x=a then f a else G x,?_,?_⟩
     · apply ComputableTidilyInPolyTime.ite_decide
       · exact ComputableTidilyInPolyTime.id'.decide_eq' (ComputableTidilyInPolyTime.const a)
       · exact ComputableTidilyInPolyTime.const (f a)
       · exact hG
     · intro x hx
       by_cases hxa : x=a
       · simp [hxa]
       · simp only [if_neg hxa]
         exact hspec x ((Finset.mem_insert.mp hx).resolve_left hxa)

 theorem small_interpolation (f : Word → Word) (N : ℕ) :
     ∃ F : Word → Word, ComputableTidilyInPolyTime F encBits encBits ∧ ∀ x,x.length<N → F x=f x := by
   classical
   obtain ⟨F,hF,hspec⟩ := finite_interpolation f ((List.range N).flatMap wordsOfLength).toFinset
   refine ⟨F,hF,?_⟩
   intro x hx
   apply hspec
   exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨x.length,List.mem_range.mpr hx,(AdviceSemantic.words_spec _ _).mpr rfl⟩)

end StudentTeacher976.Adaptivity
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CertifiedGame
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)
open CertifiedReply

 def extendedStudent (p b : Polynomial ℕ) (r q : ℕ → ℕ) (N : ℕ) (F : Word → Word) : Student :=
   fun x t H => if t<resource r x.length then List.replicate (resource q x.length)
     (if x.length<N then F x else if t=0 then [] else answer p b x ((H.getD 0 []).getD 0 [])) else []
 def extendedCPU (p b : Polynomial ℕ) (r q : ℕ → ℕ) (N : ℕ) (F : Word → Word) (s : Word) : Word :=
   let x := field s 0
   if (field s 1).length≤resource r x.length then tup (List.replicate (resource q x.length)
     (if x.length<N then F x else if (field s 1).length=1 then [] else answer p b x (firstReply s))) else tup []
 theorem extendedCPU_poly (p b : Polynomial ℕ) (r q : ℕ → ℕ) (hr : PolyTimeLength r) (hq : PolyTimeLength q)
     (N : ℕ) (F : Word → Word) (hF : ComputableTidilyInPolyTime F encBits encBits) :
     ComputableTidilyInPolyTime (extendedCPU p b r q N F) encBits encBits := by
   have h0 := field_poly 0
   have h1 := field_poly 1
   have hres (a : ℕ → ℕ) (ha : PolyTimeLength a) :
       ComputableTidilyInPolyTime (fun s : Word => resource a (field s 0).length) encBits encUnary := by
     have ht := (ComputableTidilyInPolyTime.length_bits.comp (resource_function_pure a ha)).comp h0
     simpa only [Function.comp_def,List.length_replicate] using ht
   have hrn := hres r hr
   have hqn := hres q hq
   have htable := hF.comp h0
   have ha := (answer_poly p b).comp (h0.prod firstReply_poly)
   unfold extendedCPU
   apply ComputableTidilyInPolyTime.ite_decide
   · fun_prop
   · apply TupleCodec.encode_poly.comp
     apply ComputableTidilyInPolyTime.replicate hqn
     apply ComputableTidilyInPolyTime.ite_decide
     · fun_prop
     · exact htable
     · apply ComputableTidilyInPolyTime.ite_decide
       · fun_prop
       · exact ComputableTidilyInPolyTime.const []
       · exact ha
   · exact ComputableTidilyInPolyTime.const (tup [])
 theorem firstReply_encoded (x : Word) (t : ℕ) (H : List (List Word)) :
     firstReply (tup [x,List.replicate (t+1) true,tup (H.map tup)])=(H.getD 0 []).getD 0 [] := by
   simp only [firstReply,field,TupleCodec.decode_tup,List.getD_cons_succ,List.getD_cons_zero]
   cases H with
   | nil =>
     change (TupleCodec.decodeTuple (tup [])).headD []=[]
     rw [TupleCodec.decode_tup]
     rfl
   | cons B H =>
     simp only [List.map_cons,List.headD_cons,TupleCodec.decode_tup,Option.getD_some]
     cases B <;> rfl
 theorem extendedCPU_encoded (p b : Polynomial ℕ) (r q : ℕ → ℕ) (N : ℕ) (F : Word → Word)
     (x : Word) (t : ℕ) (H : List (List Word)) :
     extendedCPU p b r q N F (tup [x,List.replicate (t+1) true,tup (H.map tup)])=
       tup (extendedStudent p b r q N F x t H) := by
   unfold extendedCPU
   rw [firstReply_encoded]
   simp only [field,TupleCodec.decode_tup,List.getD_cons_zero,List.getD_cons_succ,List.length_replicate]
   have ht : t+1≤resource r x.length ↔ t<resource r x.length := by omega
   have hz : t+1=1 ↔ t=0 := by omega
   simp only [extendedStudent,ht,hz]
   split <;> rfl
 theorem extended_uniform (i : ℕ) (p b : Polynomial ℕ) (r q : ℕ → ℕ)
     (hr : PolyTimeLength r) (hq : PolyTimeLength q) (N : ℕ) (F : Word → Word)
     (hF : ComputableTidilyInPolyTime F encBits encBits) :
     UniformStudent i (extendedStudent p b r q N F) :=
   ⟨extendedCPU p b r q N F,pure_inFP i _ (extendedCPU_poly p b r q hr hq N F hF),
     extendedCPU_encoded p b r q N F⟩

end StudentTeacher976.Adaptivity.CertifiedGame
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CertifiedGame
open QAdvFew.PoQOracle
open CertifiedReply

 theorem extended_shape {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
     (r q : ℕ → ℕ) (N : ℕ) (F : Word → Word) (hF : ∀ x,x.length<N → R x (F x)) :
     StudentShape Q r q (extendedStudent P.refutationLength P.answerBound r q N F) := by
   constructor
   · refine ⟨P.answerBound,?_⟩
     intro x t H ht hH
     simp only [extendedStudent,if_pos ht,List.length_replicate]
     refine ⟨True.intro,?_⟩
     intro y hy
     have he := (List.mem_replicate.mp hy).2
     subst y
     split
     · rename_i hsmall
       exact P.bounded _ _ (hF x hsmall)
     · split
       · simp
       · exact answer_le _ _ _ _
   · intro x t H ht
     exact if_neg (Nat.not_lt_of_le ht)

 theorem extended_wins {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R)
     (c : Polynomial ℕ) (V : Word → Word → Word → Prop)
     (hV : ∀ x y, R x y ↔ ∃ v, v.length=c.eval x.length ∧ V x y v)
     (Q : RefutablePresentation i R) (hQ : ∀ x y z,Q.test x y z ↔ test P c V x y z)
     (r q : ℕ → ℕ) (hr : ∀ n,1≤resource r n) (hq : ∀ n,1≤resource q n)
     (N : ℕ) (hN : ∀ n,N≤n → 2≤resource r n)
     (F : Word → Word) (hF : ∀ x,x.length<N → R x (F x)) :
     StudentWins Q r q (extendedStudent P.refutationLength P.answerBound r q N F) := by
   classical
   intro x H hH
   have hqpos : 0<resource q x.length := lt_of_lt_of_le (by omega) (hq _)
   have hrep (w : Word) : (List.replicate (resource q x.length) w).getD 0 []=w := by
     rw [List.getD_eq_getElem _ _ (by simpa only [List.length_replicate] using hqpos)]
     simp
   have hrpos : 0<resource r x.length := lt_of_lt_of_le (by omega) (hr _)
   have hreplylen (t : ℕ) (ht : t<resource r x.length) :
       ((H.getD t []).getD 0 []).length=Q.refutationLength.eval x.length := by
     have hi : t<H.length := by rwa [hH.1]
     have hmem : H.getD t [] ∈ H := by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
     obtain ⟨hB,hBs⟩ := hH.2 _ hmem
     have hj : 0<(H.getD t []).length := by rwa [hB]
     have he : (H.getD t []).getD 0 []=(H.getD t [])[0] := List.getD_eq_getElem _ _ hj
     apply hBs _
     rw [he]
     exact List.getElem_mem _
   by_cases hsmall : x.length<N
   · refine ⟨0,hrpos,0,hqpos,?_⟩
     have hg := (Q.represents _ _).mp (hF x hsmall) _ (hreplylen 0 hrpos)
     simpa only [extendedStudent,if_pos hrpos,if_pos hsmall,hrep] using hg
   · have hr2 : 1<resource r x.length := lt_of_lt_of_le (by omega) (hN _ (by omega))
     let z := (H.getD 0 []).getD 0 []
     by_cases hfirst : test P c V x [] z
     · refine ⟨0,hrpos,0,hqpos,?_⟩
       apply (hQ _ _ _).mpr
       simpa only [extendedStudent,if_pos hrpos,if_neg hsmall,if_true,hrep] using hfirst
     · have hgood : R x (answer P.refutationLength P.answerBound x z) := by
         have hcert : (cert P.refutationLength P.answerBound c x z).length=c.eval x.length ∧
             V x (answer P.refutationLength P.answerBound x z) (cert P.refutationLength P.answerBound c x z) := by
           unfold test at hfirst
           tauto
         exact (hV _ _).mpr ⟨_,hcert⟩
       refine ⟨1,hr2,0,hqpos,?_⟩
       have hg := (Q.represents _ _).mp hgood _ (hreplylen 1 hr2)
       have hz : ((H.take 1).getD 0 []).getD 0 []=z := by
         simp [z,List.getD_eq_getElem?_getD]
       simpa only [extendedStudent,if_pos hr2,if_neg hsmall,show ¬1=0 from by omega,if_false,
         hrep,hz] using hg

end StudentTeacher976.Adaptivity.CertifiedGame
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.CertifiedGame
open QAdvFew.PoQOracle

 theorem admissible_resources {i : ℕ} {R : SearchRelation} (P : RefutablePresentation i R)
     (c : Polynomial ℕ) (V : Word → Word → Word → Prop)
     (heff : {s | ∃ x y z,s=tup [x,y,z] ∧ V x y z} ∈ Delta i)
     (hV : ∀ x y,R x y ↔ ∃ v,v.length=c.eval x.length ∧ V x y v)
     (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q) : R ∈ ST i r q := by
   classical
   choose f hf using P.total
   obtain ⟨N,hN⟩ := hr.2.2.1 1
   obtain ⟨F,hF,hFspec⟩ := small_interpolation f N
   have hFvalid : ∀ x,x.length<N → R x (F x) := by
     intro x hx
     rw [hFspec x hx]
     exact hf x
   let Q : RefutablePresentation i R :=
     { answerBound := P.answerBound
       refutationLength := CertifiedReply.width P.refutationLength P.answerBound c
       test := test P c V
       efficient := test_efficient P c V heff
       total := P.total
       bounded := P.bounded
       represents := represents P c V hV }
   refine ⟨Q,extendedStudent P.refutationLength P.answerBound r q N F,
     extended_uniform i _ _ r q hr.1 hq.1 N F hF,extended_shape P Q r q N F hFvalid,?_⟩
   apply extended_wins P c V hV Q (fun _ _ _ => Iff.rfl) r q _ _ N _ F hFvalid
   · intro n
     obtain ⟨ε,hε,hbound⟩ := hr.2.2.2
     exact (hbound _ (by omega : 0 < max 1 n)).1
   · intro n
     exact hq.2.1 _ (by omega : 0 < max 1 n)
   · intro n hn
     exact Nat.succ_le_of_lt (hN _ (le_trans hn (Nat.le_max_right _ _)))

end StudentTeacher976.Adaptivity.CertifiedGame
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity
open QAdvFew.PoQOracle

 def PositiveCertificates (i : ℕ) : Prop :=
   ∀ R : SearchRelation, Nonempty (RefutablePresentation i R) →
     ∃ (c : Polynomial ℕ) (V : Word → Word → Word → Prop),
       {s | ∃ x y z,s=tup [x,y,z] ∧ V x y z} ∈ Delta i ∧
       ∀ x y,R x y ↔ ∃ v,v.length=c.eval x.length ∧ V x y v

 theorem st_inclusion_of_positiveCertificates (i : ℕ) (hc : PositiveCertificates i)
     (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
     (r' q' : ℕ → ℕ) : ST i r' q' ⊆ ST i r q := by
   rintro R ⟨P,f,hf,hshape,hwin⟩
   obtain ⟨c,V,heff,hV⟩ := hc R ⟨P⟩
   exact CertifiedGame.admissible_resources P c V heff hV r q hr hq

 theorem separation_excludes_positiveCertificates (i : ℕ) (r q : ℕ → ℕ)
     (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
     (hsep : ¬ ST i (fun m => r m+1) (fun _ => 1) ⊆ ST i r q) :
     ¬ PositiveCertificates i := by
   intro hc
   exact hsep (st_inclusion_of_positiveCertificates i hc r q hr hq _ _)

end StudentTeacher976.Adaptivity
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity
open QAdvFew.PoQOracle Turing.MultiTapeTM

 theorem pure_existential_sigma_one (F : Word → Word) (hF : ComputableTidilyInPolyTime F encBits encBits)
     (p : Polynomial ℕ) : {x | ∃ z : Word,z.length=p.eval x.length ∧ (F (tup [x,z])).headD false=true} ∈ Sigma 1 := by
   obtain ⟨M,b,hM⟩ := pure_word_machine F hF (fun _ => false)
   refine ⟨M,b,[p],rfl,?_,?_⟩
   · intro s
     rw [(hM s).1]
     rfl
   · intro x
     simp only [List.map_cons,List.map_nil,AvgPHETH.AltLen,Set.mem_setOf_eq,(hM _).1,Option.some.injEq]

 def RelationLanguage (R : SearchRelation) : Language := {s | ∃ x y,s=tup [x,y] ∧ R x y}
 theorem pair_mem_relation (R : SearchRelation) (x y : Word) : tup [x,y]∈RelationLanguage R ↔ R x y := by
   constructor
   · rintro ⟨a,b,he,h⟩
     have hd := congrArg TupleCodec.decodeTuple he
     simp only [TupleCodec.decode_tup,List.cons.injEq,and_true] at hd
     obtain ⟨rfl,rfl⟩ := hd
     exact h
   · exact fun h => ⟨x,y,rfl,h⟩

end StudentTeacher976.Adaptivity
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.SelectorPresentationTranslation
open QAdvFew.PoQOracle Turing.MultiTapeTM
open AdviceTeacherData (field field_poly)

def relation {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R)
    (s v : Word) : Prop :=
  let x := field s 0
  let y := field s 1
  let z := field s 2
  if z.length=P.refutationLength.eval x.length then
    v.length=Q.refutationLength.eval x.length ∧ (P.test x y z ∨ ¬ Q.test x y v)
  else v=[]
def oldInput (s : Word) : Word := CertifiedGame.triple (field s 0)
def newInput (s : Word) : Word := tup [field (field s 0) 0,field (field s 0) 1,field s 1]
def post (p q : Polynomial ℕ) (s : Word) : Word :=
  let input := field s 0
  let bits := field s 1
  let source := field input 0
  let v := field input 1
  let x := field source 0
  let z := field source 2
  [decide (tup [source,v]=input) &&
    (if z.length=p.eval x.length then
      decide (v.length=q.eval x.length) && ((field bits 0).headD false || !(field bits 1).headD false)
     else decide (v=[]))]

theorem total {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R) :
    ∀ s,∃ v,relation P Q s v := by
  classical
  intro s
  by_cases hz : (field s 2).length=P.refutationLength.eval (field s 0).length
  · by_cases hP : P.test (field s 0) (field s 1) (field s 2)
    · exact ⟨List.replicate (Q.refutationLength.eval (field s 0).length) false,by simp [relation,hz,hP]⟩
    · have hnotR : ¬ R (field s 0) (field s 1) := by
        intro hR
        exact hP ((P.represents _ _).mp hR _ hz)
      have hn : ¬ ∀ v,v.length=Q.refutationLength.eval (field s 0).length → Q.test (field s 0) (field s 1) v := by
        intro h
        exact hnotR ((Q.represents _ _).mpr h)
      push_neg at hn
      obtain ⟨v,hv,hvtest⟩ := hn
      exact ⟨v,by simp [relation,hz,hv,hvtest]⟩
  · exact ⟨[],by simp [relation,hz]⟩

theorem bounded {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R) :
    ∃ b : Polynomial ℕ,∀ s v,relation P Q s v → v.length≤b.eval s.length := by
  obtain ⟨E,hE⟩ := (field_poly 0).polyBounded_length.exists_polynomial
  simp only [encBits_apply] at hE
  refine ⟨Q.refutationLength.comp E,?_⟩
  intro s v hv
  unfold relation at hv
  dsimp only at hv
  split at hv
  · rw [hv.1,Polynomial.eval_comp]
    exact NativeBatch.polyEvalMono Q.refutationLength (hE s)
  · subst v
    simp

theorem oldInput_poly : ComputableTidilyInPolyTime oldInput encBits encBits :=
  CertifiedGame.triple_poly.comp (field_poly 0)
theorem newInput_poly : ComputableTidilyInPolyTime newInput encBits encBits := by
  have hx := (field_poly 0).comp (field_poly 0)
  have hy := (field_poly 1).comp (field_poly 0)
  have hv := field_poly 1
  unfold newInput
  apply TupleCodec.encode_poly.comp
  fun_prop
theorem post_poly (p q : Polynomial ℕ) : ComputableTidilyInPolyTime (post p q) encBits encBits := by
  have h0 := field_poly 0
  have h1 := field_poly 1
  have h2 := field_poly 2
  have hp := ComputableTidilyInPolyTime.unary_eval p
  have hq := ComputableTidilyInPolyTime.unary_eval q
  have hpair : ComputableTidilyInPolyTime (fun w : Word => tup [field w 0,field w 1]) encBits encBits := by
    apply TupleCodec.encode_poly.comp
    fun_prop
  have hguard := (hpair.comp h0).decide_eq' h0
  have hbody : ComputableTidilyInPolyTime (fun s : Word =>
      if (field (field (field s 0) 0) 2).length=p.eval (field (field (field s 0) 0) 0).length then
        decide ((field (field s 0) 1).length=q.eval (field (field (field s 0) 0) 0).length) &&
          ((field (field s 1) 0).headD false || !(field (field s 1) 1).headD false)
      else decide (field (field s 0) 1=[])) encBits encBool := by
    apply ComputableTidilyInPolyTime.ite_decide
    · fun_prop
    · fun_prop
    · fun_prop
  exact (hguard.bool_and' hbody).bitsCons (ComputableTidilyInPolyTime.const [])

theorem efficient {i : ℕ} {R : SearchRelation} (P Q : RefutablePresentation i R) :
    RelationLanguage (relation P Q)∈Delta i := by
  obtain ⟨F,hF,hFspec⟩ := (delta_iff_uniform_boolean i _).mp P.efficient
  obtain ⟨G,hG,hGspec⟩ := (delta_iff_uniform_boolean i _).mp Q.efficient
  have hFtr (x y z : Word) : (F (tup [x,y,z])).headD false=true ↔ P.test x y z := by
    rw [← hFspec]
    exact CertifiedGame.triple_mem P.test x y z
  have hGtr (x y z : Word) : (G (tup [x,y,z])).headD false=true ↔ Q.test x y z := by
    rw [← hGspec]
    exact CertifiedGame.triple_mem Q.test x y z
  let FO := fun s => F (oldInput s)
  let GN := fun s => G (newInput s)
  have hFO : InFP i FO := OracleComputations.inFP_compose i oldInput F (pure_inFP i _ oldInput_poly) hF
  have hGN : InFP i GN := OracleComputations.inFP_compose i newInput G (pure_inFP i _ newInput_poly) hG
  let pair := fun s => tup [FO s,GN s]
  have hpair := OracleProducts.pair_inFP i FO GN hFO hGN
  let H := fun s => post P.refutationLength Q.refutationLength (tup [s,pair s])
  apply (delta_iff_uniform_boolean i _).mpr
  refine ⟨H,OracleComputations.inFP_post i _ _ (OracleComputations.inFP_retain i pair hpair)
    (post_poly _ _),?_⟩
  intro s
  have hhead : (H s).headD false=true ↔
      tup [field s 0,field s 1]=s ∧ relation P Q (field s 0) (field s 1) := by
    simp only [H,post,pair,field,TupleCodec.decode_tup,List.getD_cons_zero,List.getD_cons_succ,
      List.headD_cons,Bool.and_eq_true_iff,decide_eq_true_eq,FO,GN,oldInput,CertifiedGame.triple,newInput]
    by_cases hz : (field (field s 0) 2).length=P.refutationLength.eval (field (field s 0) 0).length
    · simp only [field] at hz
      simp only [hz,↓reduceIte,Bool.and_eq_true_iff,decide_eq_true_eq,Bool.or_eq_true_iff,
        Bool.not_eq_true',Bool.eq_false_iff,ne_eq,hFtr,hGtr,relation,field]
    · simp only [field] at hz
      simp only [hz,↓reduceIte,decide_eq_true_eq,relation,field]
  rw [hhead]
  constructor
  · rintro ⟨a,b,rfl,h⟩
    simp [field,TupleCodec.decode_tup,h]
  · rintro ⟨he,h⟩
    exact ⟨field s 0,field s 1,he.symm,h⟩

theorem translation_of_selector_collapse (i : ℕ) (hcollapse : SelectorCollapse i)
    (R : SearchRelation) (P Q : RefutablePresentation i R) :
    ∃ ψ : Word → Word → Word → Word,InFP i (CausalTranslationData.code ψ) ∧
      (∀ x y z : Word,z.length=P.refutationLength.eval x.length →
        (ψ x y z).length=Q.refutationLength.eval x.length) ∧
      ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
        Q.test x y (ψ x y z) → P.test x y z := by
  obtain ⟨b,hb⟩ := bounded P Q
  obtain ⟨F,hF,hFspec⟩ := hcollapse (relation P Q) (efficient P Q) (total P Q) b hb
  let ψ := fun x y z => F (tup [x,y,z])
  have hψ : InFP i (CausalTranslationData.code ψ) :=
    OracleComputations.inFP_compose i CertifiedGame.triple F (pure_inFP i _ CertifiedGame.triple_poly) hF
  have htyped (x y z : Word) (hz : z.length=P.refutationLength.eval x.length) :
      (ψ x y z).length=Q.refutationLength.eval x.length ∧
        (P.test x y z ∨ ¬ Q.test x y (ψ x y z)) := by
    simpa [relation,field,TupleCodec.decode_tup,hz,ψ] using hFspec (tup [x,y,z])
  refine ⟨ψ,hψ,fun x y z hz => (htyped x y z hz).1,?_⟩
  intro x y z hz hQ
  exact (htyped x y z hz).2.resolve_right (not_not_intro hQ)

end StudentTeacher976.Adaptivity.SelectorPresentationTranslation
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceSelectorTranslation
open QAdvFew.PoQOracle
open AdviceComputations (InFPAdvice)


def TranslationComplete (i : ℕ) : Prop :=
  ∀ (R : SearchRelation) (P Q : RefutablePresentation i R),
    ∃ ψ : Word → Word → Word → Word,InFPAdvice i (CausalTranslationData.code ψ) ∧
      (∀ x y z : Word,z.length=P.refutationLength.eval x.length →
        (ψ x y z).length=Q.refutationLength.eval x.length) ∧
      ∀ x y z : Word,z.length=P.refutationLength.eval x.length →
        Q.test x y (ψ x y z) → P.test x y z

theorem translation_of_selectors (i : ℕ) (hc : SelectorCollapse i) : TranslationComplete i := by
  intro R P Q
  obtain ⟨b,hb⟩ := SelectorPresentationTranslation.bounded P Q
  obtain ⟨F,hF,hFs⟩ := hc (SelectorPresentationTranslation.relation P Q)
    (SelectorPresentationTranslation.efficient P Q) (SelectorPresentationTranslation.total P Q) b hb
  let ψ := fun x y z => F (tup [x,y,z])
  have hψ : InFPAdvice i (CausalTranslationData.code ψ) :=
    AdviceComputations.compose i CertifiedGame.triple F
      (AdviceComputations.uniform i _ (pure_inFP i _ CertifiedGame.triple_poly)) hF
  have ht (x y z : Word) (hz : z.length=P.refutationLength.eval x.length) :
      (ψ x y z).length=Q.refutationLength.eval x.length ∧
        (P.test x y z ∨ ¬Q.test x y (ψ x y z)) := by
    simpa [SelectorPresentationTranslation.relation,AdviceTeacherData.field,TupleCodec.decode_tup,hz,ψ]
      using hFs (tup [x,y,z])
  exact ⟨ψ,hψ,fun x y z hz => (ht x y z hz).1,
    fun x y z hz hQ => (ht x y z hz).2.resolve_right (not_not_intro hQ)⟩

end StudentTeacher976.Adaptivity.AdviceSelectorTranslation
end

section
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.AdviceSelectorCase

theorem separation (i : ℕ) (hardness : ¬Sigma (i+1)⊆DeltaPoly i)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
    (hselectors : AdviceSelectorTranslation.SelectorCollapse i) :
    ¬ST i (fun m => r m+1) (fun _ => 1)⊆ST i r q := by
  obtain ⟨R,P,⟨f,hf,hs,hw⟩,hno⟩ :=
    AdvicePresentedSeparation.presented_adaptivity_separation i hardness r q hr hq
  intro hinc
  obtain ⟨Q,g,hg,hshape,hwin⟩ := hinc ⟨P,f,hf,hs,hw⟩
  obtain ⟨ψ,hψ,hlen,htest⟩ := AdviceSelectorTranslation.translation_of_selectors i hselectors R P Q
  exact hno ⟨CausalTranslationUniform.student P q ψ g,
    AdviceCausalTranslation.uniform P Q r q hq.1 ψ hψ hlen g (AdviceStudents.of_uniform hg) hshape,
    CausalTranslationUniform.shape P Q r q ψ hlen g hshape,
    CausalTranslationUniform.wins P Q r q ψ hlen htest g hshape hwin⟩

theorem uniform_selectors_imply_advice_selectors (i : ℕ)
    (h : SelectorPresentationTranslation.SelectorCollapse i) : AdviceSelectorTranslation.SelectorCollapse i := by
  intro T hT ht b hb
  obtain ⟨F,hF,hFs⟩ := h T hT ht b hb
  exact ⟨F,AdviceComputations.uniform i F hF,hFs⟩

end StudentTeacher976.Adaptivity.AdviceSelectorCase
end

open StudentTeacher976.Adaptivity
theorem solution
    (i : ℕ) (hardness : ¬ StudentTeacher976.Adaptivity.Sigma (i+1) ⊆ DeltaPoly i)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
    (hselectors : AdviceSelectorTranslation.SelectorCollapse i) :
    ¬ ST i (fun m => r m+1) (fun _ => 1) ⊆ ST i r q :=
  AdviceSelectorCase.separation i hardness r q hr hq hselectors


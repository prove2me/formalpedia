-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.polynomial_transducer_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:55:29.026821+00:00
-- url     : https://prove2.me/submissions/bf843804-dd75-4fa2-a42a-c7d8f50f5b89

import Definitions.Def_StudentTeacher976_Adaptivity_FiniteControl
import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl
variable {Q A : Type}
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


end QAdvFew.PoQOracle.OTM.FiniteControl

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl
variable {A : Type}

@[simp] theorem bitTape_nil : bitTape (A := A) [] = fun _ => none := by
  funext i
  simp only [bitTape, List.length_nil]
  rw [if_neg (by omega)]

@[simp] theorem bitTape_neg (x : List Bool) (i : ℤ) (hi : i < 0) : bitTape (A := A) x i = none := by
  simp [bitTape, show ¬ 0 ≤ i by omega]

@[simp] theorem bitTape_out (x : List Bool) (i : ℤ) (hi : (x.length : ℤ) ≤ i) :
    bitTape (A := A) x i = none := by
  simp [bitTape, show ¬ i < x.length by omega]

 theorem bitTape_at (x : List Bool) (j : ℕ) (hj : j < x.length) :
    bitTape (A := A) x (j : ℤ) = bit (x.getD j false) := by
  simp [bitTape, show (j : ℤ) < x.length by exact_mod_cast hj]

 theorem bitTape_append_bit (x : List Bool) (b : Bool) :
    Function.update (bitTape (A := A) x) (x.length : ℤ) (bit b) = bitTape (x ++ [b]) := by
  funext i
  by_cases hi : i = x.length
  · subst i
    rw [Function.update_self]
    simp [bitTape, List.getD_append_right]
  · rw [Function.update_of_ne hi]
    by_cases hn : 0 ≤ i
    · by_cases hlt : i < x.length
      · simp only [bitTape, hn, hlt, and_self, ↓reduceIte]
        rw [if_pos (by simp; omega)]
        rw [List.getD_append _ _ _ _ (by omega)]
      · have hnew : ¬ i < (x ++ [b]).length := by simp only [List.length_append, List.length_singleton]; omega
        unfold bitTape
        rw [if_neg (by omega), if_neg (by omega)]
    · simp [bitTape, hn]

def markedTape (marker : Cell A) (x : List Bool) : ℤ → Cell A :=
  Function.update (bitTape x) (-1) marker

@[simp] theorem markedTape_mark (marker : Cell A) (x : List Bool) : markedTape marker x (-1) = marker := by
  simp [markedTape]

 theorem markedTape_at (marker : Cell A) (x : List Bool) (i : ℤ) (hi : 0 ≤ i) :
    markedTape marker x i = bitTape x i := by
  simp [markedTape, show i ≠ -1 by omega]

 theorem markedTape_append_bit (marker : Cell A) (x : List Bool) (b : Bool) :
    Function.update (markedTape marker x) (x.length : ℤ) (bit b) = markedTape marker (x ++ [b]) := by
  unfold markedTape
  rw [Function.update_comm (by omega : (-1 : ℤ) ≠ x.length), bitTape_append_bit]

 theorem markedTape_clear (marker : Cell A) (x : List Bool) :
    Function.update (markedTape marker x) (-1) none = bitTape x := by
  rw [markedTape, Function.update_idem, ← bitTape_neg x (-1) (by omega), Function.update_eq_self]

 theorem take_next (x : List Bool) (n : ℕ) (hn : n < x.length) :
    x.take (n+1) = x.take n ++ [x.getD n false] := by
  rw [List.take_succ_eq_append_getElem (l := x) hn]
  rw [List.getD_eq_getElem _ _ hn]

theorem iterate_cfg {α : Type} (f : α → α) (c : ℕ → α) (N : ℕ)
    (h : ∀ n < N, f (c n) = c (n+1)) : f^[N] (c 0) = c N := by
  have hh : ∀ n ≤ N, f^[n] (c 0) = c n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by omega), h n (by omega)]
  exact hh N le_rfl

theorem iterate_trans {α : Type} (f : α → α) {a b c : α} {s t : ℕ}
    (h1 : f^[s] a = b) (h2 : f^[t] b = c) : f^[t+s] a = c := by
  rw [Function.iterate_add_apply, h1, h2]

end QAdvFew.PoQOracle.OTM.FiniteControl

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl
variable {Q A : Type}

 def Instr.swap : Instr Q A → Instr Q A
  | .move q a wm b qm => .move q b qm a wm
  | .stop result a wm b qm => .stop result b qm a wm
  | .halt result => .halt result
  | .ask yes no => .ask yes no

 def Program.swap (P : Program Q A) : Program Q A where
  start := P.start
  code := fun q a b => (P.code q b a).swap

 def Core.swap (c : Core Q A) : Core Q A := ⟨c.state, c.query, c.qh, c.work, c.wh⟩

 @[simp] theorem Core.swap_swap (c : Core Q A) : c.swap.swap = c := by cases c; rfl

 theorem Instr.swap_involutive (s : Instr Q A) : s.swap.swap = s := by cases s <;> rfl

 theorem Program.swap_pure (P : Program Q A) (h : P.Pure) : P.swap.Pure := by
  intro q a b yes no heq
  have hh := congrArg Instr.swap heq
  change (P.code q b a).swap.swap = Instr.ask yes no at hh
  rw [Instr.swap_involutive] at hh
  exact h q b a yes no hh

 theorem Program.swap_coreStep (P : Program Q A) (c : Core Q A) :
    P.swap.coreStep c.swap = (P.coreStep c).swap := by
  cases hs : c.state with
  | inl b => simp [Program.coreStep, Core.swap, hs]
  | inr q =>
    cases hh : P.code q (c.work c.wh) (c.query c.qh) <;>
      simp [Program.coreStep, Program.swap, Core.swap, hs, hh, Instr.swap]

 theorem Program.swap_coreRun (P : Program Q A) (c : Core Q A) (t : ℕ) :
    P.swap.coreStep^[t] c.swap = (P.coreStep^[t] c).swap := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, P.swap_coreStep, Function.iterate_succ_apply']

end QAdvFew.PoQOracle.OTM.FiniteControl

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.DataTape
variable {Γ : Type} [Inhabited Γ]

 def data (g : Γ) : Cell (Unit ⊕ Γ) := some (.inr (.inr g))
 def marker : Cell (Unit ⊕ Γ) := some (.inr (.inl ()))
 def tape (xs : List Γ) : ℤ → Cell (Unit ⊕ Γ) := fun i =>
  if 0 ≤ i ∧ i < xs.length then data (xs.getD i.toNat default) else none
 def marked (xs : List Γ) : ℤ → Cell (Unit ⊕ Γ) := Function.update (tape xs) (-1) marker

 @[simp] theorem tape_nil : tape ([] : List Γ) = fun _ => none := by
  funext i
  unfold tape
  rw [if_neg (by simp <;> omega)]

 @[simp] theorem tape_neg (xs : List Γ) (i : ℤ) (hi : i < 0) : tape xs i = none := by
  simp [tape, show ¬ 0 ≤ i by omega]

 @[simp] theorem tape_out (xs : List Γ) (i : ℤ) (hi : (xs.length : ℤ) ≤ i) : tape xs i = none := by
  simp [tape, show ¬ i < xs.length by omega]

 theorem tape_at (xs : List Γ) (j : ℕ) (hj : j < xs.length) :
    tape xs (j : ℤ) = data (xs.getD j default) := by
  simp [tape, show (j : ℤ) < xs.length by exact_mod_cast hj]

 theorem tape_append (xs : List Γ) (g : Γ) :
    Function.update (tape xs) (xs.length : ℤ) (data g) = tape (xs ++ [g]) := by
  funext i
  by_cases hi : i = xs.length
  · subst i
    rw [Function.update_self]
    simp [tape, List.getD_append_right]
  · rw [Function.update_of_ne hi]
    by_cases hn : 0 ≤ i
    · by_cases hlt : i < xs.length
      · simp only [tape, hn, hlt, and_self, ↓reduceIte]
        rw [if_pos (by simp <;> omega)]
        rw [List.getD_append _ _ _ _ (by omega)]
      · unfold tape
        rw [if_neg (by omega), if_neg (by simp <;> omega)]
    · simp [tape, hn]

 @[simp] theorem marked_marker (xs : List Γ) : marked xs (-1) = marker := by simp [marked]

 theorem marked_at (xs : List Γ) (i : ℤ) (hi : 0 ≤ i) : marked xs i = tape xs i := by
  simp [marked, show i ≠ -1 by omega]

 theorem marked_append (xs : List Γ) (g : Γ) :
    Function.update (marked xs) (xs.length : ℤ) (data g) = marked (xs ++ [g]) := by
  unfold marked
  rw [Function.update_comm (by omega : (-1 : ℤ) ≠ xs.length), tape_append]

 theorem marked_clear (xs : List Γ) : Function.update (marked xs) (-1) none = tape xs := by
  rw [marked, Function.update_idem, ← tape_neg xs (-1) (by omega), Function.update_eq_self]

 theorem marked_nonmarker (xs : List Γ) (i : ℤ) (hi : 0 ≤ i) : marked xs i ≠ marker := by
  rw [marked_at _ _ hi]
  unfold tape
  split <;> simp [data, marker]

 def erasePrefix (xs : List Γ) (n : ℕ) : ℤ → Cell (Unit ⊕ Γ) := fun i =>
  if 0 ≤ i ∧ i < n then none else marked xs i

 @[simp] theorem erasePrefix_zero (xs : List Γ) : erasePrefix xs 0 = marked xs := by
  funext i
  unfold erasePrefix
  rw [if_neg (by omega)]

 theorem erasePrefix_update (xs : List Γ) (n : ℕ) :
    Function.update (erasePrefix xs n) (n : ℤ) none = erasePrefix xs (n+1) := by
  funext i
  by_cases hi : i = n
  · subst i; simp [erasePrefix]
  · rw [Function.update_of_ne hi]
    unfold erasePrefix
    have heq : (0 ≤ i ∧ i < (n : ℤ)) ↔ (0 ≤ i ∧ i < (n+1 : ℕ)) := by omega
    simp only [heq]

 theorem erasePrefix_at (xs : List Γ) (n : ℕ) : erasePrefix xs n (n : ℤ) = tape xs n := by
  simp [erasePrefix, marked_at]

 theorem erasePrefix_complete (xs : List Γ) : erasePrefix xs xs.length = marked [] := by
  funext i
  by_cases hi : i = -1
  · subst i; simp [erasePrefix]
  · simp only [erasePrefix, marked, Function.update_of_ne hi]
    unfold tape
    split <;> simp_all

end QAdvFew.PoQOracle.OTM.FiniteControl.DataTape

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.MapPass
open DataTape

 structure Labels (Q E Γ : Type) where
  load : E → Q
  scan : E → Γ → Γ → Q
  final : E → Γ → Q
  rewindWork : E → Q
  rewindQuery : E → Q
  done : E → Q

 structure Code {Q E Γ : Type} [Inhabited Γ] (P : Program Q (Unit ⊕ Γ))
    (S : Labels Q E Γ) (φ : E → Γ → Γ → Γ → Γ) : Prop where
  load : ∀ e g b, P.code (S.load e) (data g) b = .move (S.scan e default g) none 2 b 1
  scan_data : ∀ e l c r b, P.code (S.scan e l c) (data r) b =
    .move (S.scan e c r) none 2 (data (φ e l c r)) 2
  scan_end : ∀ e l c b, P.code (S.scan e l c) none b =
    .move (S.final e c) none 1 (data (φ e l c default)) 2
  final : ∀ e c b, P.code (S.final e c) none b =
    .move (S.rewindWork e) none 1 (data (φ e c default default)) 2
  rewind_work : ∀ e b, P.code (S.rewindWork e) none b =
    .move (S.rewindWork e) none 0 b 1
  rewind_work_marker : ∀ e b, P.code (S.rewindWork e) marker b =
    .move (S.rewindQuery e) marker 2 b 1
  rewind_query : ∀ e a b, b ≠ marker → P.code (S.rewindQuery e) a b =
    .move (S.rewindQuery e) a 1 b 0
  rewind_query_marker : ∀ e a, P.code (S.rewindQuery e) a marker =
    .move (S.done e) a 1 marker 2

 section
 variable {Q E Γ : Type} [Inhabited Γ] (P : Program Q (Unit ⊕ Γ))
   (S : Labels Q E Γ) (φ : E → Γ → Γ → Γ → Γ) (C : Code P S φ)

 def previous (xs : List Γ) (n : ℕ) : Γ := if n = 0 then default else xs.getD (n-1) default
 def outPrefix (e : E) (xs : List Γ) (n : ℕ) : List Γ :=
   (List.range n).map fun j => φ e (previous xs j) (xs.getD j default) (xs.getD (j+1) default)

 @[simp] theorem length_prefix (e : E) (xs : List Γ) (n : ℕ) : (outPrefix φ e xs n).length = n := by
   simp [outPrefix]

 theorem prefix_next (e : E) (xs : List Γ) (n : ℕ) :
     outPrefix φ e xs (n+1) = outPrefix φ e xs n ++
       [φ e (previous xs n) (xs.getD n default) (xs.getD (n+1) default)] := by
   simp [outPrefix, List.range_succ]

 def inputCfg (e : E) (xs : List Γ) : Core Q (Unit ⊕ Γ) :=
   ⟨.inr (S.load e), marked xs, 0, marked [], 0⟩

 def scanCfg (e : E) (xs : List Γ) (n : ℕ) : Core Q (Unit ⊕ Γ) where
   state := .inr (S.scan e (previous xs n) (xs.getD n default))
   work := erasePrefix xs (n+1)
   wh := n+1
   query := marked (outPrefix φ e xs n)
   qh := n

 include C in
 theorem load_step (e : E) (xs : List Γ) (hxs : 0 < xs.length) :
     P.coreStep (inputCfg S e xs) = scanCfg S φ e xs 0 := by
   have hread : marked xs 0 = data (xs.getD 0 default) := by
     rw [marked_at _ _ (by omega)]
     exact tape_at _ 0 hxs
   have hwrite : Function.update (marked xs) 0 none = erasePrefix xs 1 := by
     simpa using erasePrefix_update xs 0
   apply Core.ext <;>
     simp [Program.coreStep, inputCfg, scanCfg, hread, C.load, hwrite,
       previous, outPrefix, Function.update_eq_self]

 include C in
 theorem scan_step (e : E) (xs : List Γ) (n : ℕ) (hn : n+1 < xs.length) :
     P.coreStep (scanCfg S φ e xs n) = scanCfg S φ e xs (n+1) := by
   have hread : erasePrefix xs (n+1) ((n : ℤ)+1) = data (xs.getD (n+1) default) := by
     simpa only [Nat.cast_add, Nat.cast_one] using
       (erasePrefix_at xs (n+1)).trans (tape_at xs (n+1) hn)
   have hswrite : Function.update (erasePrefix xs (n+1)) ((n : ℤ)+1) none = erasePrefix xs ((n+1)+1) := by
     simpa only [Nat.cast_add, Nat.cast_one] using erasePrefix_update xs (n+1)
   have hquery : (outPrefix φ e xs n).length = n := length_prefix φ e xs n
   have hwrite := marked_append (outPrefix φ e xs n)
     (φ e (previous xs n) (xs.getD n default) (xs.getD (n+1) default))
   apply Core.ext <;>
     simp [Program.coreStep, scanCfg, hread, C.scan_data, hswrite, prefix_next,
       previous, Function.update_eq_self]
   all_goals first | omega | simpa [hquery, previous] using hwrite

 include C in
 theorem scan_run (e : E) (xs : List Γ) (n : ℕ) (hn : n < xs.length) :
     P.coreStep^[n] (scanCfg S φ e xs 0) = scanCfg S φ e xs n := by
   induction n with
   | zero => rfl
   | succ n ih =>
     rw [Function.iterate_succ_apply', ih (by omega)]
     exact scan_step P S φ C e xs n (by omega)


 def finalCfg (e : E) (xs : List Γ) : Core Q (Unit ⊕ Γ) where
   state := .inr (S.final e (xs.getD (xs.length-1) default))
   work := marked []
   wh := xs.length
   query := marked (outPrefix φ e xs xs.length)
   qh := xs.length

 include C in
 theorem scan_end_step (e : E) (xs : List Γ) (hxs : 0 < xs.length) :
     P.coreStep (scanCfg S φ e xs (xs.length-1)) = finalCfg S φ e xs := by
   have hN : xs.length-1+1 = xs.length := by omega
   have hWh : ((xs.length-1 : ℕ) : ℤ)+1 = xs.length := by omega
   have hread : marked ([] : List Γ) (xs.length : ℤ) = none := by
     rw [marked_at _ _ (by omega)]; simp
   have hpref : outPrefix φ e xs xs.length = outPrefix φ e xs (xs.length-1) ++
       [φ e (previous xs (xs.length-1)) (xs.getD (xs.length-1) default) default] := by
     simpa [hN] using prefix_next φ e xs (xs.length-1)
   have hwrite := marked_append (outPrefix φ e xs (xs.length-1))
     (φ e (previous xs (xs.length-1)) (xs.getD (xs.length-1) default) default)
   have hw : Function.update (marked ([] : List Γ)) (xs.length : ℤ) none = marked [] := by
     rw [← hread, Function.update_eq_self]
   apply Core.ext <;>
     simp [Program.coreStep, scanCfg, hN, hWh, erasePrefix_complete, hread, C.scan_end,
       finalCfg, hw, Function.update_eq_self]
   all_goals first | omega | simpa [hpref] using hwrite

 def rewindWorkCfg (e : E) (N : ℕ) (ys : List Γ) (n : ℕ) : Core Q (Unit ⊕ Γ) where
   state := .inr (S.rewindWork e)
   work := marked []
   wh := (N : ℤ)-n
   query := marked ys
   qh := ys.length

 include C in
 theorem final_step (e : E) (xs : List Γ) (hxs : 0 < xs.length) :
     P.coreStep (finalCfg S φ e xs) =
       rewindWorkCfg S e xs.length (outPrefix φ e xs (xs.length+1)) 0 := by
   have hread : marked ([] : List Γ) (xs.length : ℤ) = none := by
     rw [marked_at _ _ (by omega)]; simp
   have hpref : outPrefix φ e xs (xs.length+1) = outPrefix φ e xs xs.length ++
       [φ e (xs.getD (xs.length-1) default) default default] := by
     simpa [previous, show xs.length ≠ 0 by omega] using prefix_next φ e xs xs.length
   have hwrite := marked_append (outPrefix φ e xs xs.length)
     (φ e (xs.getD (xs.length-1) default) default default)
   have hw : Function.update (marked ([] : List Γ)) (xs.length : ℤ) none = marked [] := by
     rw [← hread, Function.update_eq_self]
   apply Core.ext <;>
     simp [Program.coreStep, finalCfg, rewindWorkCfg, hread, C.final, hw, Function.update_eq_self]
   all_goals first | omega | simpa [hpref] using hwrite

 include C in
 theorem rewind_work_step (e : E) (N : ℕ) (ys : List Γ) (n : ℕ) (hn : n < N+1) :
     P.coreStep (rewindWorkCfg S e N ys n) = rewindWorkCfg S e N ys (n+1) := by
   have hpos : 0 ≤ (N : ℤ)-n := by omega
   have hread : marked ([] : List Γ) ((N : ℤ)-n) = none := by rw [marked_at _ _ hpos]; simp
   have hw : Function.update (marked ([] : List Γ)) ((N : ℤ)-n) none = marked [] := by
     rw [← hread, Function.update_eq_self]
   apply Core.ext <;>
     simp [Program.coreStep, rewindWorkCfg, hread, C.rewind_work, hw, Function.update_eq_self] <;> omega

 include C in
 theorem rewind_work_run (e : E) (N : ℕ) (ys : List Γ) :
     P.coreStep^[N+1] (rewindWorkCfg S e N ys 0) = rewindWorkCfg S e N ys (N+1) :=
   iterate_cfg _ _ _ (rewind_work_step P S φ C e N ys)

 def rewindQueryCfg (e : E) (ys : List Γ) (n : ℕ) : Core Q (Unit ⊕ Γ) where
   state := .inr (S.rewindQuery e)
   work := marked []
   wh := 0
   query := marked ys
   qh := (ys.length : ℤ)-n

 include C in
 theorem reset_work (e : E) (N : ℕ) (ys : List Γ) :
     P.coreStep (rewindWorkCfg S e N ys (N+1)) = rewindQueryCfg S e ys 0 := by
   have hpos : (N : ℤ)-(N+1 : ℕ) = -1 := by omega
   apply Core.ext <;>
     simp [Program.coreStep, rewindWorkCfg, rewindQueryCfg, hpos, C.rewind_work_marker,
       Function.update_eq_self]

 include C in
 theorem rewind_query_step (e : E) (ys : List Γ) (n : ℕ) (hn : n < ys.length+1) :
     P.coreStep (rewindQueryCfg S e ys n) = rewindQueryCfg S e ys (n+1) := by
   have hpos : 0 ≤ (ys.length : ℤ)-n := by omega
   have hne := marked_nonmarker ys ((ys.length : ℤ)-n) hpos
   apply Core.ext <;>
     simp [Program.coreStep, rewindQueryCfg, C.rewind_query, hne, Function.update_eq_self] <;> omega

 include C in
 theorem rewind_query_run (e : E) (ys : List Γ) :
     P.coreStep^[ys.length+1] (rewindQueryCfg S e ys 0) = rewindQueryCfg S e ys (ys.length+1) :=
   iterate_cfg _ _ _ (rewind_query_step P S φ C e ys)

 def exitCfg (e : E) (ys : List Γ) : Core Q (Unit ⊕ Γ) :=
   ⟨.inr (S.done e), marked [], 0, marked ys, 0⟩

 include C in
 theorem reset_query (e : E) (ys : List Γ) :
     P.coreStep (rewindQueryCfg S e ys (ys.length+1)) = exitCfg S e ys := by
   have hpos : (ys.length : ℤ)-(ys.length+1 : ℕ) = -1 := by omega
   apply Core.ext <;>
     simp [Program.coreStep, rewindQueryCfg, exitCfg, hpos, C.rewind_query_marker,
       Function.update_eq_self]

 include C in
 theorem map_pass (e : E) (xs : List Γ) (hxs : 0 < xs.length) :
     P.coreStep^[3*xs.length+7] (inputCfg S e xs) =
       exitCfg S e (outPrefix φ e xs (xs.length+1)) := by
   have h0 := load_step P S φ C e xs hxs
   have h1 := iterate_trans P.coreStep
     (show P.coreStep^[1] (inputCfg S e xs) = scanCfg S φ e xs 0 from h0)
     (scan_run P S φ C e xs (xs.length-1) (by omega))
   have h2 := iterate_trans P.coreStep h1
     (show P.coreStep^[1] (scanCfg S φ e xs (xs.length-1)) = finalCfg S φ e xs from scan_end_step P S φ C e xs hxs)
   have h3 := iterate_trans P.coreStep h2
     (show P.coreStep^[1] (finalCfg S φ e xs) = rewindWorkCfg S e xs.length (outPrefix φ e xs (xs.length+1)) 0
       from final_step P S φ C e xs hxs)
   have h4 := iterate_trans P.coreStep h3 (rewind_work_run P S φ C e xs.length _)
   have h5 := iterate_trans P.coreStep h4
     (show P.coreStep^[1] (rewindWorkCfg S e xs.length _ (xs.length+1)) = rewindQueryCfg S e _ 0
       from reset_work P S φ C e xs.length _)
   have h6 := iterate_trans P.coreStep h5 (rewind_query_run P S φ C e _)
   have h7 := iterate_trans P.coreStep h6
     (show P.coreStep^[1] (rewindQueryCfg S e _ (_+1)) = exitCfg S e _ from reset_query P S φ C e _)
   convert h7 using 2 <;> simp only [length_prefix] <;> omega

 end
end QAdvFew.PoQOracle.OTM.FiniteControl.MapPass

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.ReadPass
open DataTape

 structure Labels (Q I R E : Type) where
  scan : I → R → Q
  rewind : E → Q
  done : E → Q

 structure Code {Q I R E Γ : Type} [Inhabited Γ] (P : Program Q (Unit ⊕ Γ))
    (S : Labels Q I R E) (δ : R → Γ → R) (finish : I → R → E) : Prop where
  scan_data : ∀ i r g b, P.code (S.scan i r) (data g) b =
    .move (S.scan i (δ r g)) (data g) 2 b 1
  scan_end : ∀ i r b, P.code (S.scan i r) none b =
    .move (S.rewind (finish i r)) none 0 b 1
  rewind : ∀ e a b, a ≠ marker → P.code (S.rewind e) a b =
    .move (S.rewind e) a 0 b 1
  rewind_marker : ∀ e b, P.code (S.rewind e) marker b =
    .move (S.done e) marker 2 b 1

 section
 variable {Q I R E Γ : Type} [Inhabited Γ] (P : Program Q (Unit ⊕ Γ))
   (S : Labels Q I R E) (δ : R → Γ → R) (finish : I → R → E) (C : Code P S δ finish)

 def scanCfg (i : I) (r0 : R) (xs : List Γ) (n : ℕ) : Core Q (Unit ⊕ Γ) where
   state := .inr (S.scan i ((xs.take n).foldl δ r0))
   work := marked xs
   wh := n
   query := marked []
   qh := 0

 include C in
 theorem scan_step (i : I) (r0 : R) (xs : List Γ) (n : ℕ) (hn : n < xs.length) :
     P.coreStep (scanCfg S δ i r0 xs n) = scanCfg S δ i r0 xs (n+1) := by
   have hread : marked xs (n : ℤ) = data (xs.getD n default) := by
     rw [marked_at _ _ (by omega), tape_at _ _ hn]
   have hwrite : Function.update (marked xs) (n : ℤ) (data (xs.getD n default)) = marked xs := by
     rw [← hread, Function.update_eq_self]
   have htake : xs.take (n+1) = xs.take n ++ [xs.getD n default] := by
     rw [List.take_succ_eq_append_getElem (l := xs) hn, List.getD_eq_getElem _ _ hn]
   apply Core.ext <;>
     simp [Program.coreStep, scanCfg, hread, C.scan_data, hwrite, htake,
       List.foldl_append, Function.update_eq_self] <;> omega

 include C in
 theorem scan_run (i : I) (r0 : R) (xs : List Γ) :
     P.coreStep^[xs.length] (scanCfg S δ i r0 xs 0) = scanCfg S δ i r0 xs xs.length :=
   iterate_cfg _ _ _ (scan_step P S δ finish C i r0 xs)

 def rewindCfg (e : E) (xs : List Γ) (n : ℕ) : Core Q (Unit ⊕ Γ) where
   state := .inr (S.rewind e)
   work := marked xs
   wh := (xs.length : ℤ)-1-n
   query := marked []
   qh := 0

 include C in
 theorem scan_end_step (i : I) (r0 : R) (xs : List Γ) :
     P.coreStep (scanCfg S δ i r0 xs xs.length) =
       rewindCfg S (finish i (xs.foldl δ r0)) xs 0 := by
   have hread : marked xs (xs.length : ℤ) = none := by
     rw [marked_at _ _ (by omega), tape_out _ _ le_rfl]
   have hwrite : Function.update (marked xs) (xs.length : ℤ) none = marked xs := by
     rw [← hread, Function.update_eq_self]
   apply Core.ext <;>
     simp [Program.coreStep, scanCfg, rewindCfg, hread, C.scan_end, hwrite, Function.update_eq_self]

 include C in
 theorem rewind_step (e : E) (xs : List Γ) (n : ℕ) (hn : n < xs.length) :
     P.coreStep (rewindCfg S e xs n) = rewindCfg S e xs (n+1) := by
   have hpos : 0 ≤ (xs.length : ℤ)-1-n := by omega
   have hne := marked_nonmarker xs ((xs.length : ℤ)-1-n) hpos
   apply Core.ext <;>
     simp [Program.coreStep, rewindCfg, C.rewind, hne, Function.update_eq_self] <;> omega

 include C in
 theorem rewind_run (e : E) (xs : List Γ) :
     P.coreStep^[xs.length] (rewindCfg S e xs 0) = rewindCfg S e xs xs.length :=
   iterate_cfg _ _ _ (rewind_step P S δ finish C e xs)

 def exitCfg (e : E) (xs : List Γ) : Core Q (Unit ⊕ Γ) :=
   ⟨.inr (S.done e), marked xs, 0, marked [], 0⟩

 include C in
 theorem reset (e : E) (xs : List Γ) :
     P.coreStep (rewindCfg S e xs xs.length) = exitCfg S e xs := by
   have hpos : (xs.length : ℤ)-1-xs.length = -1 := by omega
   apply Core.ext <;>
     simp [Program.coreStep, rewindCfg, exitCfg, hpos, C.rewind_marker, Function.update_eq_self]

 include C in
 theorem read_pass (i : I) (r0 : R) (xs : List Γ) :
     P.coreStep^[2*xs.length+2] (scanCfg S δ i r0 xs 0) =
       exitCfg S (finish i (xs.foldl δ r0)) xs := by
   have h0 := scan_run P S δ finish C i r0 xs
   have h1 := iterate_trans P.coreStep h0
     (show P.coreStep^[1] (scanCfg S δ i r0 xs xs.length) =
       rewindCfg S (finish i (xs.foldl δ r0)) xs 0 from scan_end_step P S δ finish C i r0 xs)
   have h2 := iterate_trans P.coreStep h1 (rewind_run P S δ finish C _ xs)
   have h3 := iterate_trans P.coreStep h2
     (show P.coreStep^[1] (rewindCfg S _ xs xs.length) = exitCfg S _ xs from reset P S δ finish C _ xs)
   convert h3 using 2 <;> omega

 end
end QAdvFew.PoQOracle.OTM.FiniteControl.ReadPass

set_option autoImplicit false
set_option synthInstance.maxSize 4096
namespace QAdvFew.PoQOracle.OTM.FiniteControl.Sweeper
open DataTape

 inductive State (I R E Γ : Type)
   | initial | mark | origin | inputScan (first : Bool)
   | read (role : Bool) (i : I) (r : R)
   | readRewind (role : Bool) (e : E)
   | mapLoad (role : Bool) (e : Option E)
   | mapScan (role : Bool) (e : Option E) (l c : Γ)
   | mapFinal (role : Bool) (e : Option E) (c : Γ)
   | mapRewindWork (role : Bool) (e : Option E)
   | mapRewindQuery (role : Bool) (e : Option E)
   | ready (role : Bool)
   | extract (role : Bool) (result : Bool)
   deriving DecidableEq, Fintype

 def State.role {I R E Γ : Type} : State I R E Γ → Bool
   | .initial | .mark | .origin | .inputScan _ => false
   | .read role _ _ | .readRewind role _ | .mapLoad role _ | .mapScan role _ _ _
   | .mapFinal role _ _ | .mapRewindWork role _ | .mapRewindQuery role _ | .ready role | .extract role _ => role

 section
 variable {I R E Γ : Type} [Inhabited Γ] [DecidableEq Γ]
   (initial : I) (r0 : R) (δ : R → Γ → R) (finish : I → R → E)
   (next : E → Option I) (φ : E → Γ → Γ → Γ → Γ)
   (origin : Γ) (input : Bool → Bool → Γ) (right : Bool → Γ) (output : Γ → Option Bool)

 def cellRule (ctx : Option E) (l c r : Γ) : Γ := match ctx with
   | none => c
   | some e => φ e l c r

 def successor (role : Bool) (ctx : Option E) : State I R E Γ :=
   match ctx with
   | none => .read (!role) initial r0
   | some e => match next e with
     | none => .ready (!role)
     | some i => .read (!role) i r0

 def sourceCode (s : State I R E Γ) (a b : Cell (Unit ⊕ Γ)) : Instr (State I R E Γ) (Unit ⊕ Γ) :=
   match s with
   | .initial => .move .mark a 0 b 0
   | .mark => .move .origin marker 2 marker 2
   | .origin => .move (.inputScan true) a 1 (data origin) 2
   | .inputScan first => match readBit a with
     | some bit => .move (.inputScan false) none 2 (data (input first bit)) 2
     | none => if a = none then .move (.mapRewindWork false none) none 1 (data (right first)) 2 else .halt false
   | .read role i r => match a with
     | some (.inr (.inr g)) => .move (.read role i (δ r g)) a 2 b 1
     | none => .move (.readRewind role (finish i r)) none 0 b 1
     | _ => .halt false
   | .readRewind role e => if a = marker then .move (.mapLoad role (some e)) marker 2 b 1
       else .move (.readRewind role e) a 0 b 1
   | .mapLoad role e => match a with
     | some (.inr (.inr g)) => .move (.mapScan role e default g) none 2 b 1
     | _ => .halt false
   | .mapScan role e l c => match a with
     | some (.inr (.inr g)) => .move (.mapScan role e c g) none 2 (data (cellRule φ e l c g)) 2
     | none => .move (.mapFinal role e c) none 1 (data (cellRule φ e l c default)) 2
     | _ => .halt false
   | .mapFinal role e c => .move (.mapRewindWork role e) none 1 (data (cellRule φ e c default default)) 2
   | .mapRewindWork role e => if a = marker then .move (.mapRewindQuery role e) marker 2 b 1
       else .move (.mapRewindWork role e) a 0 b 1
   | .mapRewindQuery role e => if b = marker then .move (successor initial r0 next role e) a 1 marker 2
       else .move (.mapRewindQuery role e) a 1 b 0
   | .ready role => match a with
     | some (.inr (.inr g)) =>
       let cell := (output g).map bit |>.getD none
       if role then .move (.extract role ((output g).getD false)) none 2 cell 2
       else .move (.extract role ((output g).getD false)) cell 2 b 1
     | _ => .halt false
   | .extract role result => match a with
     | some (.inr (.inr g)) =>
       let cell := (output g).map bit |>.getD none
       if role then .move (.extract role result) none 2 cell 2
       else .move (.extract role result) cell 2 b 1
     | none => .halt result
     | _ => .halt false

 def program : Program (State I R E Γ) (Unit ⊕ Γ) where
   start := .initial
   code := fun s a b =>
     if s.role then (sourceCode initial r0 δ finish next φ origin input right output s b a).swap
     else sourceCode initial r0 δ finish next φ origin input right output s a b

 def oriented (machine : Program (State I R E Γ) (Unit ⊕ Γ)) (role : Bool) :=
   if role then machine.swap else machine

 def readLabels (role : Bool) : ReadPass.Labels (State I R E Γ) I R E where
   scan := State.read role
   rewind := State.readRewind role
   done := fun e => State.mapLoad role (some e)

 def mapLabels (role : Bool) : MapPass.Labels (State I R E Γ) (Option E) Γ where
   load := State.mapLoad role
   scan := State.mapScan role
   final := State.mapFinal role
   rewindWork := State.mapRewindWork role
   rewindQuery := State.mapRewindQuery role
   done := successor initial r0 next role


 theorem read_code (role : Bool) : ReadPass.Code (oriented (program initial r0 δ finish next φ origin input right output) role) (readLabels role) δ finish := by
   constructor
   · intro i r g b
     cases role <;> simp [oriented, program, Program.swap, sourceCode, readLabels, State.role, data, Instr.swap, Instr.swap_involutive]
   · intro i r b
     cases role <;> simp [oriented, program, Program.swap, sourceCode, readLabels, State.role, Instr.swap, Instr.swap_involutive]
   · intro e a b ha
     cases role <;> simp [oriented, program, Program.swap, sourceCode, readLabels, State.role, ha, Instr.swap, Instr.swap_involutive]
   · intro e b
     cases role <;> simp [oriented, program, Program.swap, sourceCode, readLabels, State.role, Instr.swap, Instr.swap_involutive]

 theorem map_code (role : Bool) : MapPass.Code (oriented (program initial r0 δ finish next φ origin input right output) role) (mapLabels initial r0 next role) (cellRule φ) := by
   constructor
   · intro e g b
     cases role <;> simp [oriented, program, Program.swap, sourceCode, mapLabels, State.role, data, Instr.swap, Instr.swap_involutive]
   · intro e l c r b
     cases role <;> simp [oriented, program, Program.swap, sourceCode, mapLabels, State.role, data, Instr.swap, Instr.swap_involutive]
   · intro e l c b
     cases role <;> simp [oriented, program, Program.swap, sourceCode, mapLabels, State.role, Instr.swap, Instr.swap_involutive]
   · intro e c b
     cases role <;> simp [oriented, program, Program.swap, sourceCode, mapLabels, State.role, Instr.swap, Instr.swap_involutive]
   · intro e b
     cases role <;> simp [oriented, program, Program.swap, sourceCode, mapLabels, State.role, marker, Instr.swap, Instr.swap_involutive]
   · intro e b
     cases role <;> simp [oriented, program, Program.swap, sourceCode, mapLabels, State.role, Instr.swap, Instr.swap_involutive]
   · intro e a b hb
     cases role <;> simp [oriented, program, Program.swap, sourceCode, mapLabels, State.role, hb, Instr.swap, Instr.swap_involutive]
   · intro e a
     cases role <;> simp [oriented, program, Program.swap, sourceCode, mapLabels, State.role, Instr.swap, Instr.swap_involutive]


 theorem sourceCode_no_query (s : State I R E Γ) (a b : Cell (Unit ⊕ Γ))
     (yes no : State I R E Γ) :
     sourceCode initial r0 δ finish next φ origin input right output s a b ≠ .ask yes no := by
   cases s <;> simp only [sourceCode]
   all_goals (repeat' split) <;> simp_all

 theorem program_pure : (program initial r0 δ finish next φ origin input right output).Pure := by
   intro s a b yes no heq
   change (if s.role then (sourceCode initial r0 δ finish next φ origin input right output s b a).swap
     else sourceCode initial r0 δ finish next φ origin input right output s a b) = .ask yes no at heq
   split at heq
   · have hh := congrArg Instr.swap heq
     change (sourceCode initial r0 δ finish next φ origin input right output s b a).swap.swap = .ask yes no at hh
     rw [Instr.swap_involutive] at hh
     exact sourceCode_no_query initial r0 δ finish next φ origin input right output s b a yes no hh
   · exact sourceCode_no_query initial r0 δ finish next φ origin input right output s a b yes no heq

 def orientCfg (role : Bool) (c : Core (State I R E Γ) (Unit ⊕ Γ)) := if role then c.swap else c

 theorem oriented_run (P' : Program (State I R E Γ) (Unit ⊕ Γ)) (role : Bool)
     (c : Core (State I R E Γ) (Unit ⊕ Γ)) (t : ℕ) :
     P'.coreStep^[t] (orientCfg role c) = orientCfg role ((oriented P' role).coreStep^[t] c) := by
   cases role with
   | false => rfl
   | true =>
     have hh := congrArg Core.swap (P'.swap_coreRun c.swap t)
     simpa only [Core.swap_swap, orientCfg, oriented, ↓reduceIte] using hh.symm

 def bufferCfg (role : Bool) (i : I) (cells : List Γ) : Core (State I R E Γ) (Unit ⊕ Γ) :=
   ⟨.inr (.read role i r0), marked cells, 0, marked [], 0⟩

 def finishCfg (role : Bool) (e : E) (cells : List Γ) : Core (State I R E Γ) (Unit ⊕ Γ) :=
   ⟨.inr (successor initial r0 next role (some e)), marked cells, 0, marked [], 0⟩

 theorem sweep_step (role : Bool) (i : I) (cells : List Γ) (hpos : 0 < cells.length) :
     (program initial r0 δ finish next φ origin input right output).coreStep^[5*cells.length+9] (orientCfg role (bufferCfg r0 role i cells)) =
       orientCfg (!role) (finishCfg initial r0 next role (finish i (cells.foldl δ r0))
         (MapPass.outPrefix (cellRule φ) (some (finish i (cells.foldl δ r0))) cells (cells.length+1))) := by
   let e := finish i (cells.foldl δ r0)
   have hread := ReadPass.read_pass (oriented (program initial r0 δ finish next φ origin input right output) role) (readLabels role) δ finish
     (read_code initial r0 δ finish next φ origin input right output role) i r0 cells
   have hmap := MapPass.map_pass (oriented (program initial r0 δ finish next φ origin input right output) role) (mapLabels initial r0 next role) (cellRule φ)
     (map_code initial r0 δ finish next φ origin input right output role) (some e) cells hpos
   have hconnect : ReadPass.exitCfg (readLabels (I := I) (Γ := Γ) role) e cells =
       MapPass.inputCfg (mapLabels initial r0 next role) (some e) cells := rfl
   change (oriented (program initial r0 δ finish next φ origin input right output) role).coreStep^[2*cells.length+2]
     (bufferCfg r0 role i cells) = ReadPass.exitCfg (readLabels role) e cells at hread
   rw [hconnect] at hread
   have hcombined := iterate_trans (oriented (program initial r0 δ finish next φ origin input right output) role).coreStep hread hmap
   have hcanon : (oriented (program initial r0 δ finish next φ origin input right output) role).coreStep^[5*cells.length+9] (bufferCfg r0 role i cells) =
       MapPass.exitCfg (mapLabels initial r0 next role) (some e)
         (MapPass.outPrefix (cellRule φ) (some e) cells (cells.length+1)) := by
     convert hcombined using 2 <;> omega
   rw [oriented_run (program initial r0 δ finish next φ origin input right output) role _ _, hcanon]
   cases role <;> rfl

 end
end QAdvFew.PoQOracle.OTM.FiniteControl.Sweeper

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.Sweeper
open DataTape

 structure Settings (I R E Γ : Type) where
   initial : I
   reader : R
   accumulate : R → Γ → R
   action : I → R → E
   next : E → Option I
   update : E → Γ → Γ → Γ → Γ
   origin : Γ
   input : Bool → Bool → Γ
   right : Bool → Γ
   output : Γ → Option Bool

 def Settings.program {I R E Γ : Type} [Inhabited Γ] [DecidableEq Γ] (T : Settings I R E Γ) :=
   Sweeper.program T.initial T.reader T.accumulate T.action T.next T.update T.origin T.input T.right T.output

 section
 variable {I R E Γ : Type} [Inhabited Γ] [DecidableEq Γ] (T : Settings I R E Γ)

 def rawTape (x : List Bool) : ℤ → Cell (Unit ⊕ Γ) := markedTape marker x
 def rawErase (x : List Bool) (n : ℕ) : ℤ → Cell (Unit ⊕ Γ) := fun i =>
   if 0 ≤ i ∧ i < n then none else rawTape x i

 @[simp] theorem rawErase_zero (x : List Bool) : rawErase (Γ := Γ) x 0 = rawTape x := by
   funext i
   unfold rawErase
   rw [if_neg (by omega)]

 theorem rawErase_update (x : List Bool) (n : ℕ) :
     Function.update (rawErase (Γ := Γ) x n) (n : ℤ) none = rawErase x (n+1) := by
   funext i
   by_cases hi : i = n
   · subst i; simp [rawErase]
   · rw [Function.update_of_ne hi]
     unfold rawErase
     have heq : (0 ≤ i ∧ i < (n : ℤ)) ↔ (0 ≤ i ∧ i < (n+1 : ℕ)) := by omega
     simp only [heq]

 theorem rawErase_at (x : List Bool) (n : ℕ) (hn : n < x.length) :
     rawErase (Γ := Γ) x n (n : ℤ) = bit (x.getD n false) := by
   simp only [rawErase, lt_self_iff_false, and_false, ↓reduceIte]
   rw [rawTape, markedTape_at _ _ _ (by omega), bitTape_at _ _ hn]

 theorem rawErase_complete (x : List Bool) : rawErase (Γ := Γ) x x.length = marked [] := by
   funext i
   by_cases hi : i = -1
   · subst i; simp [rawErase, rawTape]
   · simp only [rawErase, rawTape, markedTape, marked, Function.update_of_ne hi, tape_nil]
     unfold bitTape
     split <;> simp_all

 def initPrefix (x : List Bool) (n : ℕ) : List Γ :=
   [T.origin] ++ (List.range n).map (fun j => T.input (decide (j=0)) (x.getD j false))

 @[simp] theorem initPrefix_length (x : List Bool) (n : ℕ) : (initPrefix T x n).length = n+1 := by
   simp [initPrefix]

 theorem initPrefix_next (x : List Bool) (n : ℕ) : initPrefix T x (n+1) =
     initPrefix T x n ++ [T.input (decide (n=0)) (x.getD n false)] := by
   simp [initPrefix, List.range_succ, List.append_assoc]

 def initialWord (x : List Bool) : List Γ := initPrefix T x x.length ++ [T.right (decide (x.length=0))]

 @[simp] theorem initialWord_length (x : List Bool) : (initialWord T x).length = x.length+2 := by
   simp [initialWord]

 def originCfg (x : List Bool) : Core (State I R E Γ) (Unit ⊕ Γ) :=
   ⟨.inr .origin, rawTape x, 0, marked [], 0⟩

 def markCfg (x : List Bool) : Core (State I R E Γ) (Unit ⊕ Γ) :=
   ⟨.inr .mark, bitTape x, -1, fun _ => none, -1⟩

 theorem marker_steps (x : List Bool) :
     T.program.coreStep^[2] (T.program.coreInitial x) = originCfg (I := I) (R := R) (E := E) x := by
   have hfirst : T.program.coreStep (T.program.coreInitial x) = markCfg (I := I) (R := R) (E := E) x := by
     simp only [Program.coreStep, Program.coreInitial, Settings.program, program, State.role,
       sourceCode, Bool.false_eq_true, ↓reduceIte, Function.update_eq_self]
     rfl
   change T.program.coreStep (T.program.coreStep (T.program.coreInitial x)) = _
   rw [hfirst]
   apply Core.ext <;>
     simp [Program.coreStep, markCfg, Settings.program, program, State.role, sourceCode,
       originCfg, rawTape, markedTape, marked]

 private theorem read_bit (b : Bool) : readBit (bit (A := Unit ⊕ Γ) b) = some b := rfl

 def initScanCfg (x : List Bool) (n : ℕ) : Core (State I R E Γ) (Unit ⊕ Γ) where
   state := .inr (.inputScan (decide (n=0)))
   work := rawErase x n
   wh := n
   query := marked (initPrefix T x n)
   qh := n+1

 theorem origin_step (x : List Bool) :
     T.program.coreStep (originCfg (I := I) (R := R) (E := E) x) = initScanCfg T x 0 := by
   have hquery : Function.update (marked ([] : List Γ)) 0 (data T.origin) = marked [T.origin] := by
     simpa using marked_append ([] : List Γ) T.origin
   apply Core.ext <;>
     simp [Program.coreStep, originCfg, Settings.program, program, State.role, sourceCode,
       initScanCfg, initPrefix, hquery, Function.update_eq_self]

 theorem init_scan_step (x : List Bool) (n : ℕ) (hn : n < x.length) :
     T.program.coreStep (initScanCfg T x n) = initScanCfg T x (n+1) := by
   have hread := rawErase_at (Γ := Γ) x n hn
   have hwrite := marked_append (initPrefix T x n) (T.input (decide (n=0)) (x.getD n false))
   have hbit : readBit (bit (A := Unit ⊕ Γ) (x.getD n false)) = some (x.getD n false) := rfl
   apply Core.ext <;>
     simp [Program.coreStep, initScanCfg, Settings.program, program, State.role, sourceCode,
       hread, read_bit, rawErase_update, initPrefix_next]
   all_goals first | omega | simpa using hwrite

 theorem init_scan_run (x : List Bool) :
     T.program.coreStep^[x.length] (initScanCfg T x 0) = initScanCfg T x x.length :=
   iterate_cfg _ _ _ (init_scan_step T x)

 theorem init_scan_end (x : List Bool) :
     T.program.coreStep (initScanCfg T x x.length) =
       MapPass.rewindWorkCfg (mapLabels T.initial T.reader T.next false) none x.length (initialWord T x) 0 := by
   have hread : rawErase (Γ := Γ) x x.length (x.length : ℤ) = none := by
     rw [rawErase_complete, marked_at _ _ (by omega)]; simp
   have hwrite := marked_append (initPrefix T x x.length) (T.right (decide (x.length=0)))
   have hw : Function.update (rawErase (Γ := Γ) x x.length) (x.length : ℤ) none = marked [] := by
     rw [rawErase_complete] at hread ⊢
     rw [← hread, Function.update_eq_self]
   apply Core.ext <;>
     simp [Program.coreStep, initScanCfg, Settings.program, program, State.role, sourceCode,
       hread, readBit, MapPass.rewindWorkCfg, mapLabels, initialWord, hw]
   all_goals first | omega | simpa using hwrite


 theorem initial_run (x : List Bool) :
     T.program.coreStep^[3*x.length+10] (T.program.coreInitial x) =
       orientCfg true (bufferCfg T.reader true T.initial (initialWord T x)) := by
   have hc : MapPass.Code T.program (mapLabels T.initial T.reader T.next false) (cellRule T.update) := by
     simpa only [Settings.program, oriented, Bool.false_eq_true, ↓reduceIte] using
       map_code T.initial T.reader T.accumulate T.action T.next T.update T.origin T.input T.right T.output false
   have h0 := marker_steps T x
   have h1 := iterate_trans T.program.coreStep h0
     (show T.program.coreStep^[1] (originCfg (I := I) (R := R) (E := E) x) = initScanCfg T x 0 from origin_step T x)
   have h2 := iterate_trans T.program.coreStep h1 (init_scan_run T x)
   have h3 := iterate_trans T.program.coreStep h2
     (show T.program.coreStep^[1] (initScanCfg T x x.length) =
       MapPass.rewindWorkCfg (mapLabels T.initial T.reader T.next false) none x.length (initialWord T x) 0
       from init_scan_end T x)
   have h4 := iterate_trans T.program.coreStep h3
     (MapPass.rewind_work_run T.program (mapLabels T.initial T.reader T.next false) (cellRule T.update)
       hc none x.length (initialWord T x))
   have h5 := iterate_trans T.program.coreStep h4
     (show T.program.coreStep^[1]
       (MapPass.rewindWorkCfg (mapLabels T.initial T.reader T.next false) none x.length (initialWord T x) (x.length+1)) =
       MapPass.rewindQueryCfg (mapLabels T.initial T.reader T.next false) none (initialWord T x) 0 from
         MapPass.reset_work T.program (mapLabels T.initial T.reader T.next false) (cellRule T.update)
           hc none x.length (initialWord T x))
   have h6 := iterate_trans T.program.coreStep h5
     (MapPass.rewind_query_run T.program (mapLabels T.initial T.reader T.next false) (cellRule T.update)
       hc none (initialWord T x))
   have h7 := iterate_trans T.program.coreStep h6
     (show T.program.coreStep^[1]
       (MapPass.rewindQueryCfg (mapLabels T.initial T.reader T.next false) none (initialWord T x) ((initialWord T x).length+1)) =
       MapPass.exitCfg (mapLabels T.initial T.reader T.next false) none (initialWord T x) from
         MapPass.reset_query T.program (mapLabels T.initial T.reader T.next false) (cellRule T.update)
           hc none (initialWord T x))
   have hfinal : T.program.coreStep^[3*x.length+10] (T.program.coreInitial x) =
       MapPass.exitCfg (mapLabels T.initial T.reader T.next false) none (initialWord T x) := by
     convert h7 using 2 <;> simp only [initialWord_length] <;> omega
   exact hfinal.trans rfl

 end
end QAdvFew.PoQOracle.OTM.FiniteControl.Sweeper

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.Sweeper
open DataTape
section
variable {I R E Γ : Type} [Inhabited Γ] [DecidableEq Γ] (T : Settings I R E Γ)

 def emitted (g : Γ) : Cell (Unit ⊕ Γ) := ((T.output g).map bit).getD none
 def firstBit (xs : List Γ) : Bool := (xs.head?.bind T.output).getD false

 theorem firstBit_pos (xs : List Γ) (h : 0 < xs.length) :
     firstBit T xs = (T.output (xs.getD 0 default)).getD false := by
   cases xs with
   | nil => simp at h
   | cons g xs => rfl

 def written (base : ℤ → Cell (Unit ⊕ Γ)) (xs : List Γ) (n : ℕ) : ℤ → Cell (Unit ⊕ Γ) := fun i =>
   if 0 ≤ i ∧ i < n then emitted T (xs.getD i.toNat default) else base i

 theorem written_at (base : ℤ → Cell (Unit ⊕ Γ)) (xs : List Γ) (n : ℕ) :
     written T base xs n (n : ℤ) = base n := by simp [written]

 theorem written_update (base : ℤ → Cell (Unit ⊕ Γ)) (xs : List Γ) (n : ℕ) :
     Function.update (written T base xs n) (n : ℤ) (emitted T (xs.getD n default)) = written T base xs (n+1) := by
   funext i
   by_cases hi : i = n
   · subst i; simp [written]
   · rw [Function.update_of_ne hi]
     unfold written
     have heq : (0 ≤ i ∧ i < (n : ℤ)) ↔ (0 ≤ i ∧ i < (n+1 : ℕ)) := by omega
     simp only [heq]

 @[simp] theorem written_zero (base : ℤ → Cell (Unit ⊕ Γ)) (xs : List Γ) : written T base xs 0 = base := by
   funext i
   unfold written
   rw [if_neg (by omega)]

 def extractCfg (role : Bool) (xs : List Γ) (n : ℕ) : Core (State I R E Γ) (Unit ⊕ Γ) where
   state := .inr (.extract role (firstBit T xs))
   work := written T (if role then marked [] else marked xs) xs n
   wh := n
   query := if role then erasePrefix xs n else marked []
   qh := if role then n else 0

 def readyCfg (role : Bool) (xs : List Γ) : Core (State I R E Γ) (Unit ⊕ Γ) :=
   orientCfg role ⟨.inr (.ready role), marked xs, 0, marked [], 0⟩

 theorem extract_first_step (role : Bool) (xs : List Γ) (hpos : 0 < xs.length) :
     T.program.coreStep (readyCfg role xs) = extractCfg T role xs 1 := by
   have hdata : marked xs 0 = data (xs.getD 0 default) := by
     rw [marked_at _ _ (by omega)]
     exact tape_at xs 0 hpos
   have hfirst := firstBit_pos T xs hpos
   have hw0 := written_update T (marked xs) xs 0
   have hw1 := written_update T (marked []) xs 0
   have hq : Function.update (marked xs) 0 none = erasePrefix xs 1 := by
     simpa using erasePrefix_update xs 0
   cases role <;> apply Core.ext <;>
     simp [Program.coreStep, readyCfg, orientCfg, Core.swap, extractCfg, Settings.program,
       program, State.role, sourceCode, hdata, data, Instr.swap, hfirst, emitted, hq]
   all_goals first | omega | simpa [emitted] using hw0 | simpa [emitted] using hw1

 theorem extract_step (role : Bool) (xs : List Γ) (n : ℕ) (hn : n < xs.length) :
     T.program.coreStep (extractCfg T role xs n) = extractCfg T role xs (n+1) := by
   have hdata : marked xs (n : ℤ) = data (xs.getD n default) := by
     rw [marked_at _ _ (by omega), tape_at _ _ hn]
   have herase : erasePrefix xs n (n : ℤ) = data (xs.getD n default) :=
     (erasePrefix_at xs n).trans (tape_at xs n hn)
   have hw0 := written_update T (marked xs) xs n
   have hw1 := written_update T (marked []) xs n
   cases role <;> apply Core.ext <;>
     simp [Program.coreStep, extractCfg, Settings.program, program, State.role, sourceCode,
       hdata, herase, written_at, data, Instr.swap, erasePrefix_update, emitted, Function.update_eq_self]
   all_goals first | omega | simpa [emitted] using hw0 | simpa [emitted] using hw1

 theorem extract_halt (role : Bool) (xs : List Γ) :
     T.program.coreStep (extractCfg T role xs xs.length) =
       {extractCfg T role xs xs.length with state := .inl (firstBit T xs)} := by
   have hdata : marked xs (xs.length : ℤ) = none := by
     rw [marked_at _ _ (by omega), tape_out _ _ le_rfl]
   have herase : erasePrefix xs xs.length (xs.length : ℤ) = none :=
     (erasePrefix_at xs xs.length).trans (tape_out xs xs.length le_rfl)
   cases role <;> apply Core.ext <;>
     simp [Program.coreStep, extractCfg, Settings.program, program, State.role, sourceCode,
       hdata, herase, written_at, Instr.swap]

 theorem extract_run (role : Bool) (xs : List Γ) :
     T.program.coreStep^[xs.length+1] (readyCfg role xs) =
       {extractCfg T role xs xs.length with state := .inl (firstBit T xs)} := by
   by_cases hpos : 0 < xs.length
   · have hfirst := extract_first_step T role xs hpos
     have hloop := iterate_cfg T.program.coreStep (fun n => extractCfg T role xs (n+1)) (xs.length-1)
       (fun n hn => extract_step T role xs (n+1) (by omega))
     rw [show xs.length-1+1 = xs.length by omega] at hloop
     have h1 := iterate_trans T.program.coreStep
       (show T.program.coreStep^[1] (readyCfg role xs) = extractCfg T role xs 1 from hfirst) hloop
     have h2 := iterate_trans T.program.coreStep h1
       (show T.program.coreStep^[1] (extractCfg T role xs xs.length) =
         {extractCfg T role xs xs.length with state := .inl (firstBit T xs)} from extract_halt T role xs)
     convert h2 using 2 <;> omega
   · have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
     subst xs
     change T.program.coreStep (readyCfg role []) = _
     cases role <;> apply Core.ext <;>
       simp [Program.coreStep, readyCfg, orientCfg, Core.swap, extractCfg, Settings.program,
         program, State.role, sourceCode, firstBit, marked_at, written_zero, Instr.swap]

 theorem extracted_work (role : Bool) (xs : List Γ) (j : ℕ) :
     (extractCfg T role xs xs.length).work (j : ℤ) =
       if j < xs.length then emitted T (xs.getD j default) else none := by
   have hInt : (j : ℤ) < (xs.length : ℤ) ↔ j < xs.length := by omega
   unfold extractCfg written
   simp only [Int.natCast_nonneg, true_and, hInt, Int.toNat_natCast]
   split
   · rfl
   · rename_i hj
     cases role <;> simp only [Bool.false_eq_true, Bool.not_true, ↓reduceIte]
     · rw [marked_at _ _ (by omega)]
       exact tape_out _ _ (by omega)
     · rw [marked_at _ _ (by omega)]
       simp

end
end QAdvFew.PoQOracle.OTM.FiniteControl.Sweeper

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096

namespace StudentTeacher976.Adaptivity.MultiTapeCells
open Turing

@[ext] structure Cell (k : ℕ) where
  origin : Bool
  input : Option Bool
  inputLeft : Bool
  inputRight : Bool
  inputHead : Bool
  positive : Fin k → Option Bool
  negative : Fin k → Option Bool
  positiveHead : Fin k → Bool
  negativeHead : Fin k → Bool
  output : Option Bool
  outputHead : Bool
  deriving DecidableEq

 private abbrev Tuple (k : ℕ) := Bool × Option Bool × Bool × Bool × Bool × (Fin k → Option Bool) × (Fin k → Option Bool) × (Fin k → Bool) × (Fin k → Bool) × Option Bool × Bool

 private def toTuple {k : ℕ} (c : Cell k) : Tuple k :=
  ⟨c.origin, c.input, c.inputLeft, c.inputRight, c.inputHead, c.positive, c.negative, c.positiveHead, c.negativeHead, c.output, c.outputHead⟩

 private def ofTuple {k : ℕ} (p : Tuple k) : Cell k where
  origin := p.1
  input := p.2.1
  inputLeft := p.2.2.1
  inputRight := p.2.2.2.1
  inputHead := p.2.2.2.2.1
  positive := p.2.2.2.2.2.1
  negative := p.2.2.2.2.2.2.1
  positiveHead := p.2.2.2.2.2.2.2.1
  negativeHead := p.2.2.2.2.2.2.2.2.1
  output := p.2.2.2.2.2.2.2.2.2.1
  outputHead := p.2.2.2.2.2.2.2.2.2.2

 noncomputable instance (k : ℕ) : Fintype (Cell k) :=
  Fintype.ofInjective toTuple (Function.LeftInverse.injective (f := toTuple) (g := ofTuple) (fun c => by cases c; rfl))

 def blank (k : ℕ) : Cell k where
  origin := false
  input := none
  inputLeft := false
  inputRight := false
  inputHead := false
  positive := fun _ => none
  negative := fun _ => none
  positiveHead := fun _ => false
  negativeHead := fun _ => false
  output := none
  outputHead := false

 instance (k : ℕ) : Inhabited (Cell k) := ⟨blank k⟩

 def encode {k : ℕ} {Q : Type} {x : List Bool} (c : Turing.Cfg k Bool Q x) (j : ℕ) : Cell k where
  origin := decide (j = 0)
  input := if j = 0 then none else x[j-1]?
  inputLeft := decide (j = 0)
  inputRight := decide (j = x.length+1)
  inputHead := decide (c.inputPos.val = j)
  positive := fun i => c.workTapes i (j : ℤ)
  negative := fun i => c.workTapes i (-(j : ℤ)-1)
  positiveHead := fun i => decide (c.workTapePos i = (j : ℤ))
  negativeHead := fun i => decide (c.workTapePos i = -(j : ℤ)-1)
  output := c.output[j]?
  outputHead := decide (j = c.output.length)

 def shift (move : SignType) (left here right : Bool) : Bool :=
  match move with
  | .neg => right
  | .zero => here
  | .pos => left

/-- A local update of the finite tracks. Negative work-tape positions are folded
onto a second track, with -1 and 0 sharing the origin cell. -/
 def update {k : ℕ} {Q : Type} (a : Action k Bool Q) (l c r : Cell k) : Cell k where
  origin := c.origin
  input := c.input
  inputLeft := c.inputLeft
  inputRight := c.inputRight
  inputHead :=
    (match a.inputTape with
      | .neg => (r.inputHead && !r.inputLeft) || (c.inputHead && c.inputLeft)
      | .zero => c.inputHead
      | .pos => (l.inputHead && !l.inputRight) || (c.inputHead && c.inputRight))
  positive := fun i => if c.positiveHead i then (a.workTapes i).1.getD (c.positive i) else c.positive i
  negative := fun i => if c.negativeHead i then (a.workTapes i).1.getD (c.negative i) else c.negative i
  positiveHead := fun i =>
    match (a.workTapes i).2 with
    | .neg => r.positiveHead i
    | .zero => c.positiveHead i
    | .pos => (!c.origin && l.positiveHead i) || (c.origin && c.negativeHead i)
  negativeHead := fun i =>
    match (a.workTapes i).2 with
    | .neg => (!c.origin && l.negativeHead i) || (c.origin && c.positiveHead i)
    | .zero => c.negativeHead i
    | .pos => r.negativeHead i
  output := if c.outputHead then a.output.or c.output else c.output
  outputHead := if a.output.isSome then (!c.origin && l.outputHead) else c.outputHead

 theorem update_blank {k : ℕ} {Q : Type} (a : Action k Bool Q) :
    update a (blank k) (blank k) (blank k) = blank k := by
  apply Cell.ext <;> simp [update, blank]
  · cases a.inputTape <;> rfl
  · funext i; cases (a.workTapes i).2 <;> rfl
  · funext i; cases (a.workTapes i).2 <;> rfl

 theorem output_append (ys : List Bool) (b : Option Bool) (j : ℕ) :
    (ys ++ b.toList)[j]? = if j = ys.length then b else ys[j]? := by
  cases b with
  | none => by_cases h : j = ys.length <;> simp [h]
  | some b =>
    by_cases hj : j < ys.length
    · simp [List.getElem?_append, hj, show j ≠ ys.length by omega]
    · by_cases heq : j = ys.length
      · subst j; simp
      · simp [List.getElem?_append, hj, heq, show ys.length ≤ j by omega,
          show ¬ j - ys.length = 0 by omega, List.getElem?_eq_none_iff.mpr (by omega : ys.length ≤ j)]

 theorem encoded_output_update {k : ℕ} {Q : Type} {x : List Bool}
    (a : Action k Bool Q) (c : Turing.Cfg k Bool Q x) (j : ℕ) :
    (update a (if j = 0 then blank k else encode c (j-1)) (encode c j) (encode c (j+1))).output =
      (encode (a.apply c) j).output := by
  simp only [update, encode, Action.apply, output_append]
  by_cases h : j = c.output.length <;> simp [h]

 theorem encoded_work_update {k : ℕ} {Q : Type} {x : List Bool}
    (a : Action k Bool Q) (c : Turing.Cfg k Bool Q x) (j : ℕ) :
    (update a (if j = 0 then blank k else encode c (j-1)) (encode c j) (encode c (j+1))).positive =
      (encode (a.apply c) j).positive ∧
    (update a (if j = 0 then blank k else encode c (j-1)) (encode c j) (encode c (j+1))).negative =
      (encode (a.apply c) j).negative := by
  have hpn : (j : ℤ) ≠ -(j : ℤ)-1 := by omega
  constructor <;> funext i <;>
    simp only [update, encode, Action.apply, decide_eq_true_eq]
  all_goals cases (a.workTapes i).1 <;> by_cases h : c.workTapePos i = (j : ℤ) <;>
    by_cases hn : c.workTapePos i = -(j : ℤ)-1 <;> simp (disch := omega) [h, hn, hpn, Ne.symm hpn, Function.update] <;> omega


 theorem encoded_work_heads {k : ℕ} {Q : Type} {x : List Bool}
    (a : Action k Bool Q) (c : Turing.Cfg k Bool Q x) (j : ℕ) :
    (update a (if j = 0 then blank k else encode c (j-1)) (encode c j) (encode c (j+1))).positiveHead =
      (encode (a.apply c) j).positiveHead ∧
    (update a (if j = 0 then blank k else encode c (j-1)) (encode c j) (encode c (j+1))).negativeHead =
      (encode (a.apply c) j).negativeHead := by
  constructor <;> funext i <;> apply Bool.eq_iff_iff.mpr
  all_goals cases j <;> cases hm : (a.workTapes i).2 <;>
    simp [update, encode, blank, Action.apply, hm] <;> omega

 theorem encoded_output_head {k : ℕ} {Q : Type} {x : List Bool}
    (a : Action k Bool Q) (c : Turing.Cfg k Bool Q x) (j : ℕ) :
    (update a (if j = 0 then blank k else encode c (j-1)) (encode c j) (encode c (j+1))).outputHead =
      (encode (a.apply c) j).outputHead := by
  apply Bool.eq_iff_iff.mpr
  cases ho : a.output <;> cases j <;>
    simp [update, encode, blank, Action.apply, ho] <;> omega

 theorem encoded_input_head {k : ℕ} {Q : Type} {x : List Bool}
    (a : Action k Bool Q) (c : Turing.Cfg k Bool Q x) (j : ℕ) :
    (update a (if j = 0 then blank k else encode c (j-1)) (encode c j) (encode c (j+1))).inputHead =
      (encode (a.apply c) j).inputHead := by
  have hp : (c.inputPos.val : ℤ) ≤ (x.length : ℤ)+1 := by
    exact_mod_cast Nat.le_of_lt_succ c.inputPos.isLt
  have hz : ∀ p : Fin (x.length+2), p = 0 ↔ p.val = 0 := by
    intro p
    constructor
    · intro h; subst p; rfl
    · intro h; apply Fin.ext; simpa using h
  have heq := val_moveInputPos_eq c.inputPos a.inputTape
  apply Bool.eq_iff_iff.mpr
  cases j <;> cases hm : a.inputTape
  all_goals simp [hm] at heq
  all_goals simp [update, encode, blank, Action.apply, hm, hz, -Fin.val_eq_zero, -Fin.val_eq_zero_iff]
  all_goals omega

 theorem encoded_update {k : ℕ} {Q : Type} {x : List Bool}
    (a : Action k Bool Q) (c : Turing.Cfg k Bool Q x) (j : ℕ) :
    update a (if j = 0 then blank k else encode c (j-1)) (encode c j) (encode c (j+1)) =
      encode (a.apply c) j := by
  apply Cell.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · exact encoded_input_head a c j
  · exact (encoded_work_update a c j).1
  · exact (encoded_work_update a c j).2
  · exact (encoded_work_heads a c j).1
  · exact (encoded_work_heads a c j).2
  · exact encoded_output_update a c j
  · exact encoded_output_head a c j

end StudentTeacher976.Adaptivity.MultiTapeCells

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.MultiTapeCells
open Turing

@[ext] structure Reads (k : ℕ) where
  input : Option Bool
  work : Fin k → Option Bool

 def readStep {k : ℕ} (r : Reads k) (c : Cell k) : Reads k where
  input := if c.inputHead then c.input else r.input
  work := fun i => if c.positiveHead i then c.positive i else
    if c.negativeHead i then c.negative i else r.work i

 def reads {k : ℕ} (cells : List (Cell k)) : Reads k :=
  cells.foldl readStep ⟨none, fun _ => none⟩

 theorem fold_select {β : Type} (f : ℕ → β) (initial : β) (p N : ℕ) :
    (List.range N).foldl (fun acc j => if j = p then f j else acc) initial =
      if p < N then f p else initial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih]
    by_cases hp : p = N
    · subst p; simp
    · by_cases hlt : p < N
      · simp [hlt, show p < N+1 by omega, Ne.symm hp]
      · simp [hlt, show ¬ p < N+1 by omega, Ne.symm hp]

 theorem input_fold {k : ℕ} (cells : List (Cell k)) (initial : Reads k) :
    (cells.foldl readStep initial).input =
      cells.foldl (fun acc c => if c.inputHead then c.input else acc) initial.input := by
  induction cells generalizing initial with
  | nil => rfl
  | cons c cs ih => simpa only [List.foldl_cons, readStep] using ih (readStep initial c)

 theorem work_fold {k : ℕ} (cells : List (Cell k)) (initial : Reads k) (i : Fin k) :
    (cells.foldl readStep initial).work i =
      cells.foldl (fun acc c => if c.positiveHead i then c.positive i else
        if c.negativeHead i then c.negative i else acc) (initial.work i) := by
  induction cells generalizing initial with
  | nil => rfl
  | cons c cs ih => simpa only [List.foldl_cons, readStep] using ih (readStep initial c)

 def headIndex (z : ℤ) : ℕ := if 0 ≤ z then z.toNat else (-z-1).toNat

 theorem work_select {k : ℕ} {Q : Type} {x : List Bool} (c : Turing.Cfg k Bool Q x)
    (i : Fin k) (j : ℕ) (acc : Option Bool) :
    (if (encode c j).positiveHead i then (encode c j).positive i else
      if (encode c j).negativeHead i then (encode c j).negative i else acc) =
      if j = headIndex (c.workTapePos i) then c.workTapes i (c.workTapePos i) else acc := by
  simp only [encode, decide_eq_true_eq]
  by_cases hz : 0 ≤ c.workTapePos i
  · have hi : (headIndex (c.workTapePos i) : ℤ) = c.workTapePos i := by simp [headIndex, hz]
    by_cases hj : j = headIndex (c.workTapePos i)
    · have heq : c.workTapePos i = (j : ℤ) := by omega
      rw [if_pos heq, if_pos hj, heq]
    · have hne : c.workTapePos i ≠ (j : ℤ) := by omega
      have hneg : c.workTapePos i ≠ -(j : ℤ)-1 := by omega
      rw [if_neg hne, if_neg hneg, if_neg hj]
  · have hi : (headIndex (c.workTapePos i) : ℤ) = -c.workTapePos i-1 := by
      unfold headIndex
      rw [if_neg hz]
      exact Int.toNat_of_nonneg (by omega)
    by_cases hj : j = headIndex (c.workTapePos i)
    · have heq : c.workTapePos i = -(j : ℤ)-1 := by omega
      have hne : c.workTapePos i ≠ (j : ℤ) := by omega
      rw [if_neg hne, if_pos heq, if_pos hj, heq]
    · have hne : c.workTapePos i ≠ (j : ℤ) := by omega
      have hneg : c.workTapePos i ≠ -(j : ℤ)-1 := by omega
      rw [if_neg hne, if_neg hneg, if_neg hj]

 theorem reads_work {k : ℕ} {Q : Type} {x : List Bool} (c : Turing.Cfg k Bool Q x)
    (N : ℕ) (i : Fin k) (hi : headIndex (c.workTapePos i) < N) :
    (reads ((List.range N).map (encode c))).work i = c.workTapeSymbols i := by
  unfold reads
  rw [work_fold, List.foldl_map]
  simp only [Function.comp_apply, work_select]
  rw [fold_select]
  simp only [hi, ↓reduceIte, Turing.Cfg.workTapeSymbols]

 theorem reads_input {k : ℕ} {Q : Type} {x : List Bool} (c : Turing.Cfg k Bool Q x)
    (N : ℕ) (hi : c.inputPos.val < N) :
    (reads ((List.range N).map (encode c))).input = c.inputSymbol := by
  unfold reads
  rw [input_fold, List.foldl_map]
  simp only [readStep, encode, decide_eq_true_eq]
  have hfold : (List.range N).foldl (fun acc j =>
      if c.inputPos.val = j then (if j = 0 then none else x[j-1]?) else acc) none =
        if c.inputPos.val = 0 then none else x[c.inputPos.val-1]? := by
    have hh := fold_select (fun j => if j = 0 then none else x[j-1]?) none c.inputPos.val N
    simpa only [eq_comm, hi, ↓reduceIte] using hh
  rw [hfold]
  by_cases hzero : c.inputPos.val = 0
  · rw [inputSymbol_eq_none_of_boundary (Or.inl hzero)]
    simp [hzero]
  by_cases hright : c.inputPos.val = x.length+1
  · rw [inputSymbol_eq_none_of_boundary (Or.inr hright)]
    simp [hright]
  have hpos : 0 < c.inputPos.val := by omega
  have hlt : c.inputPos.val-1 < x.length := by have hp := c.inputPos.isLt; omega
  rw [inputSymbolInner (cfg := c) (c.inputPos.val-1) (by omega) hlt]
  simp [hzero, List.getElem?_eq_getElem hlt]

end StudentTeacher976.Adaptivity.MultiTapeCells

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.MultiTapeCells
open Turing

 def Represents {k : ℕ} {Q : Type} {x : List Bool} (cells : List (Cell k))
    (c : Turing.Cfg k Bool Q x) : Prop := ∀ j : ℕ, cells.getD j (blank k) = encode c j

 def stepCells {k : ℕ} {Q : Type} (a : Action k Bool Q) (cells : List (Cell k)) : List (Cell k) :=
  (List.range (cells.length+1)).map fun j =>
    update a (if j = 0 then blank k else cells.getD (j-1) (blank k))
      (cells.getD j (blank k)) (cells.getD (j+1) (blank k))

 @[simp] theorem length_stepCells {k : ℕ} {Q : Type} (a : Action k Bool Q) (cells : List (Cell k)) :
    (stepCells a cells).length = cells.length+1 := by simp [stepCells]

 theorem stepCells_represents {k : ℕ} {Q : Type} {x : List Bool} (cells : List (Cell k))
    (c : Turing.Cfg k Bool Q x) (h : Represents cells c) (a : Action k Bool Q) :
    Represents (stepCells a cells) (a.apply c) := by
  change ∀ j, cells.getD j (blank k) = encode c j at h
  intro j
  by_cases hj : j < cells.length+1
  · unfold stepCells
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
    simp only [h]
    exact encoded_update a c j
  · have hlen : cells.length ≤ j := by omega
    have hmid : cells.getD j (blank k) = blank k := List.getD_eq_default cells (blank k) (by omega)
    have hnext : cells.getD (j+1) (blank k) = blank k := List.getD_eq_default cells (blank k) (by omega)
    have hprev : (if j = 0 then blank k else cells.getD (j-1) (blank k)) = blank k := by
      split
      · rfl
      · exact List.getD_eq_default cells (blank k) (by omega)
    have hupdate := encoded_update a c j
    have hmid' := h j
    have hnext' := h (j+1)
    have hprev' : (if j = 0 then blank k else encode c (j-1)) = blank k := by
      simpa only [h] using hprev
    rw [← hmid', ← hnext', hmid, hnext, hprev', update_blank] at hupdate
    rw [List.getD_eq_default (stepCells a cells) (blank k) (by simp; omega)]
    exact hupdate

 def initialCells {k : ℕ} {Q : Type} (q : Q) (x : List Bool) : List (Cell k) :=
  (List.range (x.length+2)).map (encode (Turing.Cfg.init q x))

 @[simp] theorem length_initialCells {k : ℕ} {Q : Type} (q : Q) (x : List Bool) :
    (initialCells (k := k) q x).length = x.length+2 := by simp [initialCells]

 theorem initialCells_represents {k : ℕ} {Q : Type} (q : Q) (x : List Bool) :
    Represents (initialCells (k := k) q x) (Turing.Cfg.init q x) := by
  intro j
  by_cases hj : j < x.length+2
  · simp only [initialCells]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  · rw [List.getD_eq_default (initialCells (k := k) q x) (blank k) (by simp; omega)]
    apply Cell.ext <;>
      simp (disch := omega) [blank, encode, Turing.Cfg.init, show j ≠ 0 by omega,
        show j ≠ x.length+1 by omega, show ¬ j-1 < x.length by omega,
        show ¬ (0 : ℤ) = (j : ℤ) by omega, show ¬ (0 : ℤ) = -(j : ℤ)-1 by omega] <;> omega

end StudentTeacher976.Adaptivity.MultiTapeCells

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.MultiTapeCells
open Turing

 theorem represented_word {k : ℕ} {Q : Type} {x : List Bool} (cells : List (Cell k))
    (c : Turing.Cfg k Bool Q x) (h : Represents cells c) :
    cells = (List.range cells.length).map (encode c) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    rw [List.getElem_map, List.getElem_range]
    exact (List.getD_eq_getElem cells (blank k) hj).symm.trans (h j)

 theorem represented_input_bound {k : ℕ} {Q : Type} {x : List Bool} (cells : List (Cell k))
    (c : Turing.Cfg k Bool Q x) (h : Represents cells c) : c.inputPos.val < cells.length := by
  by_contra hn
  have heq := h c.inputPos.val
  rw [List.getD_eq_default cells (blank k) (by omega)] at heq
  have hh := congrArg Cell.inputHead heq
  simp [blank, encode] at hh

 theorem represented_work_bound {k : ℕ} {Q : Type} {x : List Bool} (cells : List (Cell k))
    (c : Turing.Cfg k Bool Q x) (h : Represents cells c) (i : Fin k) :
    headIndex (c.workTapePos i) < cells.length := by
  by_contra hn
  have heq := h (headIndex (c.workTapePos i))
  rw [List.getD_eq_default cells (blank k) (by omega)] at heq
  by_cases hz : 0 ≤ c.workTapePos i
  · have hi : (headIndex (c.workTapePos i) : ℤ) = c.workTapePos i := by simp [headIndex, hz]
    have hb : decide (c.workTapePos i = (headIndex (c.workTapePos i) : ℤ)) = true := by
      simpa only [decide_eq_true_eq] using hi.symm
    have hh := congrArg (fun d : Cell k => d.positiveHead i) heq
    change false = decide (c.workTapePos i = (headIndex (c.workTapePos i) : ℤ)) at hh
    rw [hb] at hh
    cases hh
  · have hi : (headIndex (c.workTapePos i) : ℤ) = -c.workTapePos i-1 := by
      unfold headIndex
      rw [if_neg hz]
      exact Int.toNat_of_nonneg (by omega)
    have hb : decide (c.workTapePos i = -(headIndex (c.workTapePos i) : ℤ)-1) = true := by
      simp only [decide_eq_true_eq]
      omega
    have hh := congrArg (fun d : Cell k => d.negativeHead i) heq
    change false = decide (c.workTapePos i = -(headIndex (c.workTapePos i) : ℤ)-1) at hh
    rw [hb] at hh
    cases hh

 theorem reads_complete {k : ℕ} {Q : Type} {x : List Bool} (cells : List (Cell k))
    (c : Turing.Cfg k Bool Q x) (h : Represents cells c) :
    (reads cells).input = c.inputSymbol ∧ (reads cells).work = c.workTapeSymbols := by
  have hi := represented_input_bound cells c h
  have hw := represented_work_bound cells c h
  have heq := represented_word cells c h
  constructor
  · rw [heq]
    exact reads_input c cells.length hi
  · funext i
    rw [heq]
    exact reads_work c cells.length i (hw i)

 structure CellCfg (k : ℕ) (Q : Type) where
  state : Option Q
  cells : List (Cell k)

 noncomputable def evolve {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (s : CellCfg k Q) : CellCfg k Q :=
  match s.state with
  | none => s
  | some q =>
    let r := reads s.cells
    let a := tm.tr q r.input r.work
    ⟨a.state, stepCells a s.cells⟩

 def Models {k : ℕ} {Q : Type} {x : List Bool} (s : CellCfg k Q) (c : Turing.Cfg k Bool Q x) : Prop :=
  s.state = c.state ∧ Represents s.cells c

 theorem evolve_models {k : ℕ} {Q : Type} {x : List Bool} (tm : MultiTapeTM k Bool Q)
    (s : CellCfg k Q) (c : Turing.Cfg k Bool Q x) (h : Models s c) :
    Models (evolve tm s) (tm.step c) := by
  rcases h with ⟨hstate, hcells⟩
  cases hs : s.state with
  | none =>
    have hc : c.state = none := hstate.symm.trans hs
    rw [MultiTapeTM.step_of_halt hc]
    exact ⟨by simpa [evolve, hs] using hstate, by simpa [evolve, hs] using hcells⟩
  | some q =>
    have hc : c.state = some q := hstate.symm.trans hs
    have hr := reads_complete s.cells c hcells
    rw [MultiTapeTM.step_of_state hc]
    change Models _ ((tm.tr q c.inputSymbol c.workTapeSymbols).apply c)
    unfold evolve
    rw [hs]
    simp only [hr.1, hr.2]
    exact ⟨rfl, stepCells_represents s.cells c hcells _⟩

 def initialCfg {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (x : List Bool) : CellCfg k Q :=
  ⟨some tm.q₀, initialCells tm.q₀ x⟩

 theorem initialCfg_models {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (x : List Bool) :
    Models (initialCfg tm x) (tm.initCfg x) := ⟨rfl, initialCells_represents tm.q₀ x⟩

 theorem evolution_models {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (x : List Bool) (t : ℕ) :
    Models ((evolve tm)^[t] (initialCfg tm x)) (tm.runFrom (tm.initCfg x) t) := by
  induction t with
  | zero => exact initialCfg_models tm x
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    simpa only [MultiTapeTM.runFrom, Function.iterate_succ_apply'] using evolve_models tm _ _ ih

 theorem evolve_length {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (s : CellCfg k Q) :
    (evolve tm s).cells.length ≤ s.cells.length+1 := by
  unfold evolve
  split
  · omega
  · simp only [length_stepCells]
    rfl

 theorem evolution_length {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (x : List Bool) (t : ℕ) :
    ((evolve tm)^[t] (initialCfg tm x)).cells.length ≤ x.length+2+t := by
  induction t with
  | zero => simp [initialCfg]
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact (evolve_length tm _).trans (by omega)

end StudentTeacher976.Adaptivity.MultiTapeCells

set_option autoImplicit false
set_option synthInstance.maxSize 4096
namespace StudentTeacher976.Adaptivity.MultiTapeSimulation
open Turing
open QAdvFew.PoQOracle.OTM.FiniteControl
open StudentTeacher976.Adaptivity.MultiTapeCells

 noncomputable instance reads_fintype (k : ℕ) : Fintype (Reads k) := by
   classical
   let enc := fun r : Reads k => (r.input, r.work)
   let dec := fun p : Option Bool × (Fin k → Option Bool) => Reads.mk p.1 p.2
   exact Fintype.ofInjective enc (Function.LeftInverse.injective (f := enc) (g := dec) (fun r => by cases r; rfl))

 noncomputable instance action_fintype (k : ℕ) (Q : Type) [Fintype Q] : Fintype (Action k Bool Q) := by
   classical
   let enc := fun a : Action k Bool Q => (a.inputTape, a.workTapes, a.output, a.state)
   let dec := fun p : SignType × (Fin k → Option (Option Bool) × SignType) × Option Bool × Option Q =>
     (⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩ : Action k Bool Q)
   exact Fintype.ofInjective enc (Function.LeftInverse.injective (f := enc) (g := dec) (fun a => by cases a; rfl))

 def originCell (k : ℕ) : MultiTapeCells.Cell k :=
   {blank k with origin := true, inputLeft := true, positiveHead := fun _ => true, outputHead := true}

 def inputCell (k : ℕ) (first bit : Bool) : MultiTapeCells.Cell k :=
   {blank k with input := some bit, inputHead := first}

 def rightCell (k : ℕ) (first : Bool) : MultiTapeCells.Cell k :=
   {blank k with inputRight := true, inputHead := first}

 noncomputable def settings {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) :
     Sweeper.Settings Q (Reads k) (Action k Bool Q) (MultiTapeCells.Cell k) where
   initial := tm.q₀
   reader := ⟨none, fun _ => none⟩
   accumulate := readStep
   action := fun q r => tm.tr q r.input r.work
   next := Action.state
   update := MultiTapeCells.update
   origin := originCell k
   input := inputCell k
   right := rightCell k
   output := MultiTapeCells.Cell.output

 theorem initial_word_represents {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (x : List Bool) :
     Represents (Sweeper.initialWord (settings tm) x) (tm.initCfg x) := by
   intro j
   have hp : (Sweeper.initPrefix (settings tm) x x.length).length = x.length+1 := by simp
   have hword : Sweeper.initialWord (settings tm) x = originCell k ::
       ((List.range x.length).map (fun j => inputCell k (decide (j=0)) (x.getD j false)) ++
         [rightCell k (decide (x.length=0))]) := by
     simp [Sweeper.initialWord, Sweeper.initPrefix, settings]
   rw [hword]
   cases j with
   | zero =>
     rw [List.getD_cons_zero]
     apply MultiTapeCells.Cell.ext <;>
       simp (disch := omega) [encode, MultiTapeNTM.initCfg, Turing.Cfg.init, originCell, blank,
         Nat.mod_eq_of_lt] <;> omega
   | succ j =>
     rw [List.getD_cons_succ]
     have hpos0 : (0 : ℤ) ≠ (j : ℤ)+1 := by omega
     have hneg0 : (0 : ℤ) ≠ -1 + -(j : ℤ)-1 := by omega
     by_cases hj : j < x.length
     · rw [List.getD_append _ _ _ _ (by simpa using hj),
         List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
       apply MultiTapeCells.Cell.ext <;>
         simp (disch := omega) [inputCell, blank, encode, MultiTapeNTM.initCfg, Turing.Cfg.init,
           List.getD_eq_getElem _ _ hj, List.getElem?_eq_getElem hj, Nat.mod_eq_of_lt, hpos0, hneg0]
       all_goals first
         | omega
         | (apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, Bool.false_eq_true] <;> omega)
         | (funext i; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, Bool.false_eq_true] <;> omega)
     · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hj)]
       by_cases heq : j = x.length
       · subst j
         simp only [List.length_map, List.length_range, Nat.sub_self, List.getD_cons_zero]
         apply MultiTapeCells.Cell.ext <;>
           simp (disch := omega) [rightCell, blank, encode, MultiTapeNTM.initCfg, Turing.Cfg.init,
             Nat.mod_eq_of_lt, hpos0, hneg0]
         all_goals first
           | omega
           | (apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, Bool.false_eq_true] <;> omega)
           | (funext i; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, Bool.false_eq_true] <;> omega)
       · rw [List.getD_eq_default _ _ (by simp; omega)]
         apply MultiTapeCells.Cell.ext <;>
           simp (disch := omega) [blank, encode, MultiTapeNTM.initCfg, Turing.Cfg.init,
             Nat.mod_eq_of_lt, hpos0, hneg0, show ¬ j < x.length by omega]
         all_goals first
           | omega
           | (apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, Bool.false_eq_true] <;> omega)
           | (funext i; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq, Bool.false_eq_true] <;> omega)

end StudentTeacher976.Adaptivity.MultiTapeSimulation

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity.MultiTapeSimulation
open Turing
open QAdvFew.PoQOracle.OTM.FiniteControl
open StudentTeacher976.Adaptivity.MultiTapeCells

 abbrev Control (k : ℕ) (Q : Type) :=
   Sweeper.State Q (Reads k) (Action k Bool Q) (MultiTapeCells.Cell k)

 noncomputable def frame {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (role : Bool) (c : CellCfg k Q) :
     Core (Control k Q) (Unit ⊕ MultiTapeCells.Cell k) :=
   match c.state with
   | some q => Sweeper.orientCfg role (Sweeper.bufferCfg (settings tm).reader role q c.cells)
   | none => Sweeper.readyCfg role c.cells

 theorem initial_word_eq {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (x : List Bool) :
     Sweeper.initialWord (settings tm) x = initialCells tm.q₀ x := by
   have h := represented_word (Sweeper.initialWord (settings tm) x) (tm.initCfg x) (initial_word_represents tm x)
   rw [Sweeper.initialWord_length] at h
   exact h

 theorem initial_frame {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (x : List Bool) :
     (settings tm).program.coreStep^[3*x.length+10] ((settings tm).program.coreInitial x) =
       frame tm true (initialCfg tm x) := by
   have h := Sweeper.initial_run (settings tm) x
   rw [initial_word_eq] at h
   exact h

 theorem mapped_word {k : ℕ} {Q : Type} (a : Action k Bool Q) (cells : List (MultiTapeCells.Cell k)) :
     MapPass.outPrefix (Sweeper.cellRule MultiTapeCells.update) (some a) cells (cells.length+1) =
       stepCells a cells := rfl

 theorem finish_frame {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (role : Bool)
     (a : Action k Bool Q) (cells : List (MultiTapeCells.Cell k)) :
     Sweeper.orientCfg (!role) (Sweeper.finishCfg (settings tm).initial (settings tm).reader
       (settings tm).next role a cells) = frame tm (!role) ⟨a.state, cells⟩ := by
   cases hs : a.state <;>
     simp only [frame, Sweeper.finishCfg, Sweeper.successor, settings, hs,
       Sweeper.readyCfg, Sweeper.bufferCfg]

 theorem frame_step {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (role : Bool)
     (c : CellCfg k Q) (q : Q) (hs : c.state = some q) (hp : 0 < c.cells.length) :
     (settings tm).program.coreStep^[5*c.cells.length+9] (frame tm role c) =
       frame tm (!role) (evolve tm c) := by
   have h := Sweeper.sweep_step (settings tm).initial (settings tm).reader
     (settings tm).accumulate (settings tm).action (settings tm).next (settings tm).update
     (settings tm).origin (settings tm).input (settings tm).right (settings tm).output
     role q c.cells hp
   change (settings tm).program.coreStep^[5*c.cells.length+9]
     (Sweeper.orientCfg role (Sweeper.bufferCfg (settings tm).reader role q c.cells)) = _ at h
   rw [frame, hs]
   rw [h]
   let a := (settings tm).action q (c.cells.foldl (settings tm).accumulate (settings tm).reader)
   change Sweeper.orientCfg (!role) (Sweeper.finishCfg (settings tm).initial (settings tm).reader
     (settings tm).next role a
       (MapPass.outPrefix (Sweeper.cellRule (settings tm).update) (some a) c.cells (c.cells.length+1))) = _
   have hw : MapPass.outPrefix (Sweeper.cellRule (settings tm).update) (some a) c.cells (c.cells.length+1) =
       stepCells a c.cells := rfl
   rw [hw, finish_frame tm role a _]
   congr 1
   unfold evolve
   rw [hs]
   rfl

 theorem ready_frame {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (role : Bool)
     (c : CellCfg k Q) (hs : c.state = none) : frame tm role c = Sweeper.readyCfg role c.cells := by
   simp only [frame, hs]

 theorem first_bit {k : ℕ} {Q : Type} {x : List Bool} (tm : MultiTapeTM k Bool Q)
     (cells : List (MultiTapeCells.Cell k)) (c : Turing.Cfg k Bool Q x) (h : Represents cells c) :
     Sweeper.firstBit (settings tm) cells = c.output.head?.getD false := by
   have hp : 0 < cells.length := by have hi := represented_input_bound cells c h; omega
   rw [Sweeper.firstBit_pos _ _ hp]
   change ((cells.getD 0 (blank k)).output).getD false = _
   rw [h 0]
   change (c.output[0]?).getD false = c.output.head?.getD false
   cases c.output <;> rfl

end StudentTeacher976.Adaptivity.MultiTapeSimulation

set_option autoImplicit false
set_option synthInstance.maxSize 4096
namespace StudentTeacher976.Adaptivity.MultiTapeSimulation
open Turing
open QAdvFew.PoQOracle.OTM.FiniteControl
open StudentTeacher976.Adaptivity.MultiTapeCells

 def timeBound (n t : ℕ) : ℕ := 10*(n+t+3)^2+3*n+10

 theorem budget_step (n t : ℕ) : timeBound n t + 6*(n+2+t)+11 ≤ timeBound n (t+1) := by
   unfold timeBound
   nlinarith

 theorem budget_mono (n t : ℕ) : timeBound n t ≤ timeBound n (t+1) := by
   have h := budget_step n t
   omega

 noncomputable def terminal {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (role : Bool) (c : CellCfg k Q) :
     Core (Control k Q) (Unit ⊕ MultiTapeCells.Cell k) :=
   {Sweeper.extractCfg (settings tm) role c.cells c.cells.length with state := .inl (Sweeper.firstBit (settings tm) c.cells)}

 noncomputable def realized {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (role : Bool) (c : CellCfg k Q) :
     Core (Control k Q) (Unit ⊕ MultiTapeCells.Cell k) :=
   match c.state with
   | none => terminal tm role c
   | some _ => frame tm role c

 theorem program_run {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (x : List Bool) (t : ℕ) :
     ∃ u ≤ timeBound x.length t, ∃ role : Bool,
       (settings tm).program.coreStep^[u] ((settings tm).program.coreInitial x) =
         realized tm role ((evolve tm)^[t] (initialCfg tm x)) := by
   induction t with
   | zero =>
     refine ⟨3*x.length+10, ?_, true, ?_⟩
     · unfold timeBound; omega
     · exact initial_frame tm x
   | succ t ih =>
     obtain ⟨u, hu, role, hrun⟩ := ih
     let c := (evolve tm)^[t] (initialCfg tm x)
     have hmodel : Models c (tm.runFrom (tm.initCfg x) t) := evolution_models tm x t
     have hlen : c.cells.length ≤ x.length+2+t := evolution_length tm x t
     have hpos : 0 < c.cells.length := by
       have hh := represented_input_bound c.cells (tm.runFrom (tm.initCfg x) t) hmodel.2
       omega
     change (settings tm).program.coreStep^[u] ((settings tm).program.coreInitial x) = realized tm role c at hrun
     rw [Function.iterate_succ_apply']
     change ∃ v ≤ timeBound x.length (t+1), ∃ r : Bool,
       (settings tm).program.coreStep^[v] ((settings tm).program.coreInitial x) = realized tm r (evolve tm c)
     cases hs : c.state with
     | none =>
       have he : evolve tm c = c := by simp [evolve, hs]
       exact ⟨u, hu.trans (budget_mono x.length t), role, by rw [he]; exact hrun⟩
     | some q =>
       simp only [realized, hs] at hrun
       have hstep := iterate_trans (settings tm).program.coreStep hrun (frame_step tm role c q hs hpos)
       have hnextlen : (evolve tm c).cells.length = c.cells.length+1 := by
         simp [evolve, hs]
       cases hn : (evolve tm c).state with
       | some q' =>
         refine ⟨5*c.cells.length+9+u, ?_, !role, ?_⟩
         · apply le_trans (b := timeBound x.length t + 6*(x.length+2+t)+11)
           · omega
           · exact budget_step x.length t
         · simpa only [realized, hn] using hstep
       | none =>
         rw [ready_frame tm (!role) (evolve tm c) hn] at hstep
         have hdone := iterate_trans (settings tm).program.coreStep hstep
           (Sweeper.extract_run (settings tm) (!role) (evolve tm c).cells)
         refine ⟨(evolve tm c).cells.length+1+(5*c.cells.length+9+u), ?_, !role, ?_⟩
         · apply le_trans (b := timeBound x.length t + 6*(x.length+2+t)+11)
           · omega
           · exact budget_step x.length t
         · simpa only [realized, hn, terminal] using hdone

 theorem core_clock {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (x : List Bool) (t : ℕ)
     (hhalt : (tm.runFrom (tm.initCfg x) t).Halted) :
     ((settings tm).program.coreStep^[timeBound x.length t] ((settings tm).program.coreInitial x)).state =
       .inl ((tm.runFrom (tm.initCfg x) t).output.head?.getD false) := by
   obtain ⟨u, hu, role, hrun⟩ := program_run tm x t
   let c := (evolve tm)^[t] (initialCfg tm x)
   have hmodel : Models c (tm.runFrom (tm.initCfg x) t) := evolution_models tm x t
   have hnone : c.state = none := hmodel.1.trans hhalt
   change (settings tm).program.coreStep^[u] ((settings tm).program.coreInitial x) = realized tm role c at hrun
   simp only [realized, hnone] at hrun
   have hfixed : (settings tm).program.coreStep (terminal tm role c) = terminal tm role c := rfl
   have heq : (settings tm).program.coreStep^[timeBound x.length t] ((settings tm).program.coreInitial x) =
       terminal tm role c := by
     rw [← Nat.add_sub_of_le hu, Nat.add_comm u, Function.iterate_add_apply, hrun]
     exact Function.iterate_fixed hfixed _
   rw [heq]
   change Sum.inl (Sweeper.firstBit (settings tm) c.cells) = _
   rw [first_bit tm c.cells (tm.runFrom (tm.initCfg x) t) hmodel.2]

 noncomputable def simulationClock (clock : Polynomial ℕ) : Polynomial ℕ :=
   10*(Polynomial.X+clock+3)^2+3*Polynomial.X+10

 @[simp] theorem simulationClock_eval (clock : Polynomial ℕ) (n : ℕ) :
     (simulationClock clock).eval n = timeBound n (clock.eval n) := by simp [simulationClock, timeBound]

 theorem full_clock {k : ℕ} {Q : Type} [Fintype Q] (tm : MultiTapeTM k Bool Q) (clock : Polynomial ℕ)
     (hhalt : ∀ x, (tm.runFrom (tm.initCfg x) (clock.eval x.length)).Halted) (x : List Bool) :
     (((settings tm).program.step (fun _ => false))^[(simulationClock clock).eval x.length]
       ((settings tm).program.initial x)).state =
       .inl ((tm.runFrom (tm.initCfg x) (clock.eval x.length)).output.head?.getD false) := by
   have hp : (settings tm).program.Pure := Sweeper.program_pure
     (settings tm).initial (settings tm).reader (settings tm).accumulate (settings tm).action
     (settings tm).next (settings tm).update (settings tm).origin (settings tm).input
     (settings tm).right (settings tm).output
   have hc := (settings tm).program.core_iterate hp (fun _ => false) ((settings tm).program.initial x)
     ((simulationClock clock).eval x.length)
   change (((settings tm).program.step (fun _ => false))^[(simulationClock clock).eval x.length]
       ((settings tm).program.initial x)).core =
     (settings tm).program.coreStep^[(simulationClock clock).eval x.length] ((settings tm).program.coreInitial x) at hc
   exact (congrArg Core.state hc).trans (by simpa using core_clock tm x (clock.eval x.length) (hhalt x))

end StudentTeacher976.Adaptivity.MultiTapeSimulation

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl

 theorem read_list_prefix (ys : List Bool) (n : ℕ) :
     (((List.range n).map (fun j => ys[j]?)).takeWhile (·.isSome)).reduceOption = ys.take n := by
   induction ys generalizing n with
   | nil => cases n <;> simp
   | cons b ys ih =>
     cases n with
     | zero => rfl
     | succ n =>
       rw [List.range_succ_eq_map]
       simp only [List.map_cons, List.getElem?_cons_zero, Option.isSome_some, List.takeWhile_cons,
         Bool.true_eq, ↓reduceIte, List.reduceOption_cons_of_some, List.take_succ_cons,
         List.map_map, Function.comp_def, List.getElem?_cons_succ]
       rw [ih]

 theorem readWord_of_reads {A : Type} (tape : ℤ → Cell A) (ys : List Bool) (hi : ℤ)
     (hread : ∀ j : ℕ, readBit (tape (j : ℤ)) = ys[j]?) (hhi : (ys.length : ℤ) ≤ hi) :
     readWord tape hi = ys := by
   unfold readWord
   simp only [hread, read_list_prefix]
   exact List.take_of_length_le (by omega)

 theorem Program.wh_bound {Q A : Type} (P : Program Q A) (O : Oracle) (c : Cfg Q A)
     (h : c.wh ≤ c.whi) : (P.step O c).wh ≤ (P.step O c).whi := by
   cases hs : c.state with
   | inl b => simpa only [Program.step, hs] using h
   | inr q =>
     cases hh : P.code q (c.work c.wh) (c.query c.qh) <;>
       simp only [Program.step, hs, hh]
     · exact le_max_right _ _
     · exact le_max_right _ _
     · exact h
     · exact h

 theorem Program.wh_bound_run {Q A : Type} (P : Program Q A) (O : Oracle) (x : List Bool) (t : ℕ) :
     ((P.step O)^[t] (P.initial x)).wh ≤ ((P.step O)^[t] (P.initial x)).whi := by
   induction t with
   | zero => simp [Program.initial]
   | succ t ih => rw [Function.iterate_succ_apply']; exact P.wh_bound O _ ih

end QAdvFew.PoQOracle.OTM.FiniteControl

set_option autoImplicit false
set_option synthInstance.maxSize 4096
namespace StudentTeacher976.Adaptivity.MultiTapeSimulation
open Turing
open QAdvFew.PoQOracle.OTM.FiniteControl
open StudentTeacher976.Adaptivity.MultiTapeCells

 theorem represented_output_bound {k : ℕ} {Q : Type} {x : List Bool} (cells : List (MultiTapeCells.Cell k))
     (c : Turing.Cfg k Bool Q x) (h : Represents cells c) : c.output.length < cells.length := by
   by_contra hh
   have he := h c.output.length
   rw [List.getD_eq_default _ _ (by omega)] at he
   have he := congrArg MultiTapeCells.Cell.outputHead he
   simp [blank, encode] at he

 theorem extracted_reads {k : ℕ} {Q : Type} {x : List Bool} (tm : MultiTapeTM k Bool Q)
     (role : Bool) (cells : List (MultiTapeCells.Cell k))
     (c : Turing.Cfg k Bool Q x) (h : Represents cells c) (j : ℕ) :
     readBit ((Sweeper.extractCfg (settings tm) role cells cells.length).work (j : ℤ)) = c.output[j]? := by
   rw [Sweeper.extracted_work]
   by_cases hj : j < cells.length
   · rw [if_pos hj]
     change readBit (((cells.getD j (blank k)).output.map bit).getD none) = _
     rw [h j]
     change readBit ((c.output[j]?.map bit).getD none) = _
     cases ho : c.output[j]? <;> rfl
   · rw [if_neg hj]
     have he := h j
     rw [List.getD_eq_default _ _ (by omega)] at he
     have he := congrArg MultiTapeCells.Cell.output he
     exact he

 theorem core_complete {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (x : List Bool) (t : ℕ)
     (hhalt : (tm.runFrom (tm.initCfg x) t).Halted) :
     ∃ role : Bool,
       (settings tm).program.coreStep^[timeBound x.length t] ((settings tm).program.coreInitial x) =
         terminal tm role ((evolve tm)^[t] (initialCfg tm x)) := by
   obtain ⟨u, hu, role, hrun⟩ := program_run tm x t
   let c := (evolve tm)^[t] (initialCfg tm x)
   have hmodel := evolution_models tm x t
   have hnone : c.state = none := hmodel.1.trans hhalt
   change (settings tm).program.coreStep^[u] ((settings tm).program.coreInitial x) = realized tm role c at hrun
   simp only [realized, hnone] at hrun
   refine ⟨role, ?_⟩
   rw [← Nat.add_sub_of_le hu, Nat.add_comm u, Function.iterate_add_apply, hrun]
   exact Function.iterate_fixed (show (settings tm).program.coreStep (terminal tm role c) = terminal tm role c from rfl) _

 theorem full_output_clock {k : ℕ} {Q : Type} [Fintype Q] (tm : MultiTapeTM k Bool Q) (clock : Polynomial ℕ)
     (hhalt : ∀ x, (tm.runFrom (tm.initCfg x) (clock.eval x.length)).Halted) (x : List Bool) :
     readWord (((settings tm).program.step (fun _ => false))^[(simulationClock clock).eval x.length]
       ((settings tm).program.initial x)).work
       (((settings tm).program.step (fun _ => false))^[(simulationClock clock).eval x.length]
       ((settings tm).program.initial x)).whi =
         (tm.runFrom (tm.initCfg x) (clock.eval x.length)).output := by
   have hp : (settings tm).program.Pure := Sweeper.program_pure
     (settings tm).initial (settings tm).reader (settings tm).accumulate (settings tm).action
     (settings tm).next (settings tm).update (settings tm).origin (settings tm).input
     (settings tm).right (settings tm).output
   have hc := (settings tm).program.core_iterate hp (fun _ => false) ((settings tm).program.initial x)
     ((simulationClock clock).eval x.length)
   obtain ⟨role, hr⟩ := core_complete tm x (clock.eval x.length) (hhalt x)
   let c := (evolve tm)^[(clock.eval x.length)] (initialCfg tm x)
   have hmodel : Models c (tm.runFrom (tm.initCfg x) (clock.eval x.length)) := evolution_models tm x _
   change (((settings tm).program.step (fun _ => false))^[(simulationClock clock).eval x.length]
       ((settings tm).program.initial x)).core =
     (settings tm).program.coreStep^[(simulationClock clock).eval x.length] ((settings tm).program.coreInitial x) at hc
   rw [← simulationClock_eval clock x.length] at hr
   rw [hr] at hc
   apply readWord_of_reads
   · intro j
     have hw := congrArg (fun a => a.work (j : ℤ)) hc
     change _ = (Sweeper.extractCfg (settings tm) role c.cells c.cells.length).work (j : ℤ) at hw
     dsimp only [Cfg.core] at hw
     rw [hw]
     exact extracted_reads tm role c.cells _ hmodel.2 j
   · have hb := (settings tm).program.wh_bound_run (fun _ => false) x ((simulationClock clock).eval x.length)
     have he := congrArg Core.wh hc
     change _ = (c.cells.length : ℤ) at he
     dsimp only [Cfg.core] at he
     change _ ≤ _ at hb
     rw [he] at hb
     have ho := represented_output_bound c.cells _ hmodel.2
     omega

end StudentTeacher976.Adaptivity.MultiTapeSimulation

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.Continuation

 inductive State (Q R : Type) | body (q : Bool ⊕ Q) | post (r : R)
   deriving DecidableEq, Fintype

 def lift {Q R A : Type} : Instr Q A → Instr (State Q R) A
   | .move q a m b n => .move (.body (.inr q)) a m b n
   | .stop r a m b n => .move (.body (.inl r)) a m b n
   | .halt r => .move (.body (.inl r)) none 1 none 1
   | .ask yes no => .ask (.body (.inr yes)) (.body (.inr no))

-- The halt instruction must preserve both currently scanned symbols.
 def liftAt {Q R A : Type} (a b : Cell A) : Instr Q A → Instr (State Q R) A
   | .halt r => .move (.body (.inl r)) a 1 b 1
   | i => lift i

 def program {Q R A : Type} (P : Program Q A) (start : Bool → R)
     (post : R → Cell A → Cell A → Instr (State Q R) A) : Program (State Q R) A where
   start := .body (.inr P.start)
   code := fun s a b => match s with
     | .body (.inr q) => liftAt a b (P.code q a b)
     | .body (.inl r) => .move (.post (start r)) a 1 b 1
     | .post r => post r a b

 def embed {Q R A : Type} (c : Core Q A) : Core (State Q R) A where
   state := .inr (.body c.state)
   work := c.work
   wh := c.wh
   query := c.query
   qh := c.qh

 theorem embed_initial {Q R A : Type} (P : Program Q A) (start : Bool → R) (post) (x : List Bool) :
     (program P start post).coreInitial x = (embed (R := R) (P.coreInitial x)) := rfl

 theorem step_embed {Q R A : Type} (P : Program Q A) (start : Bool → R) (post)
     (hpure : P.Pure) (c : Core Q A) (q : Q) (hq : c.state = .inr q) :
     (program P start post).coreStep (embed c) = embed (P.coreStep c) := by
   cases hi : P.code q (c.work c.wh) (c.query c.qh) with
   | move next a m b n =>
     apply Core.ext <;> simp [Program.coreStep, program, embed, hq, hi, liftAt, lift]
     all_goals omega
   | stop r a m b n =>
     apply Core.ext <;> simp [Program.coreStep, program, embed, hq, hi, liftAt, lift]
     all_goals omega
   | halt r =>
     apply Core.ext <;> simp [Program.coreStep, program, embed, hq, hi, liftAt, lift, Function.update_eq_self]
     all_goals omega
   | ask yes no => exact False.elim (hpure q _ _ yes no hi)

 theorem hit_embed {Q R A : Type} (P : Program Q A) (start : Bool → R) (post)
     (hpure : P.Pure) (t : ℕ) (c : Core Q A)
     (h : ∃ b, (P.coreStep^[t] c).state = .inl b) :
     ∃ u ≤ t, ∃ b,
       (P.coreStep^[u] c).state = .inl b ∧
       (program P start post).coreStep^[u] (embed c) = embed (P.coreStep^[u] c) := by
   induction t generalizing c with
   | zero => obtain ⟨b, hb⟩ := h; exact ⟨0, le_rfl, b, hb, rfl⟩
   | succ t ih =>
     cases hc : c.state with
     | inl b => exact ⟨0, by omega, b, hc, rfl⟩
     | inr q =>
       have hh : ∃ b, (P.coreStep^[t] (P.coreStep c)).state = .inl b := by
         simpa only [Function.iterate_succ_apply] using h
       obtain ⟨u, hu, b, hb, hr⟩ := ih (P.coreStep c) hh
       refine ⟨u+1, by omega, b, ?_, ?_⟩
       · simpa only [Function.iterate_succ_apply] using hb
       · rw [Function.iterate_succ_apply, step_embed P start post hpure c q hc, hr,
           Function.iterate_succ_apply]

 theorem hit_terminal {Q R A : Type} (P : Program Q A) (start : Bool → R) (post)
     (hpure : P.Pure) (t : ℕ) (c : Core Q A) (terminal : Core Q A)
     (hterm : ∃ b, terminal.state = .inl b) (hr : P.coreStep^[t] c = terminal) :
     ∃ u ≤ t, (program P start post).coreStep^[u] (embed c) = embed terminal := by
   obtain ⟨b, hb⟩ := hterm
   obtain ⟨u, hu, r, hhalt, hr'⟩ := hit_embed P start post hpure t c ⟨b, by rw [hr]; exact hb⟩
   have hfixed : P.coreStep (P.coreStep^[u] c) = P.coreStep^[u] c := by
     simp only [Program.coreStep, hhalt]
   have hstable := Function.iterate_fixed hfixed (t-u)
   have he : P.coreStep^[u] c = terminal := by
     rw [← hr, ← Nat.add_sub_of_le hu, Nat.add_comm u, Function.iterate_add_apply, hstable]
   exact ⟨u, hu, by rw [hr', he]⟩

end QAdvFew.PoQOracle.OTM.FiniteControl.Continuation

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.Normalization
open DataTape
variable {Q Γ : Type} [DecidableEq Γ]

 abbrev State (Q : Type) := Continuation.State Q (Bool × Bool)
 def post (s : Bool × Bool) (a b : Cell (Unit ⊕ Γ)) : Instr (State Q) (Unit ⊕ Γ) :=
   if s.1 then
     if b = marker then .stop s.2 a 1 none 2
     else .move (.post s) a 1 b 0
   else if a = marker then .move (.post (true,s.2)) none 2 b 1
   else .move (.post s) a 0 b 1

 def program (P : Program Q (Unit ⊕ Γ)) : Program (State Q) (Unit ⊕ Γ) :=
   Continuation.program P (fun b => (false,b)) post

 theorem program_pure (P : Program Q (Unit ⊕ Γ)) (hp : P.Pure) : (program P).Pure := by
   intro s a b yes no he
   cases s with
   | body s =>
     cases s with
     | inl r => simp [program, Continuation.program] at he
     | inr q =>
       cases hi : P.code q a b with
       | move next c m d n => simp [program, Continuation.program, hi, Continuation.liftAt, Continuation.lift] at he
       | stop r c m d n => simp [program, Continuation.program, hi, Continuation.liftAt, Continuation.lift] at he
       | halt r => simp [program, Continuation.program, hi, Continuation.liftAt] at he
       | ask y n => exact hp q a b y n hi
   | post s =>
     rcases s with ⟨stage,r⟩
     cases stage <;> by_cases ha : a = marker <;> by_cases hb : b = marker <;>
       simp [program, Continuation.program, post, ha, hb] at he

 def markedBits (ys : List Bool) : ℤ → Cell (Unit ⊕ Γ) := Function.update (bitTape ys) (-1) marker

 theorem markedBits_at (ys : List Bool) (z : ℤ) (hz : 0 ≤ z) :
     markedBits (Γ := Γ) ys z = bitTape ys z := by
   simp [markedBits, show z ≠ -1 by omega]

 theorem markedBits_nonmarker (ys : List Bool) (z : ℤ) (hz : 0 ≤ z) :
     markedBits (Γ := Γ) ys z ≠ marker := by
   rw [markedBits_at _ _ hz]
   unfold bitTape
   split <;> simp [bit, marker]

 theorem markedBits_clear (ys : List Bool) :
     Function.update (markedBits (Γ := Γ) ys) (-1) none = bitTape ys := by
   unfold markedBits
   rw [Function.update_idem]
   have he : bitTape (A := Unit ⊕ Γ) ys (-1) = none := by simp [bitTape]
   rw [← he, Function.update_eq_self]

 def workCfg (b : Bool) (ys : List Bool) (z : ℤ) (h : ℕ) : Core (State Q) (Unit ⊕ Γ) where
   state := .inr (.post (false,b))
   work := markedBits ys
   wh := z
   query := markedBits []
   qh := h

 def queryCfg (b : Bool) (ys : List Bool) (z : ℤ) : Core (State Q) (Unit ⊕ Γ) where
   state := .inr (.post (true,b))
   work := bitTape ys
   wh := 0
   query := markedBits []
   qh := z

 def normal (b : Bool) (ys : List Bool) : Core (State Q) (Unit ⊕ Γ) where
   state := .inl b
   work := bitTape ys
   wh := 0
   query := fun _ => none
   qh := 0

 theorem work_step (P : Program Q (Unit ⊕ Γ)) (b : Bool) (ys : List Bool) (z : ℤ) (hz : 0 ≤ z) (h : ℕ) :
     (program P).coreStep (workCfg b ys z h) = workCfg b ys (z-1) h := by
   have hm := markedBits_nonmarker (Γ := Γ) ys z hz
   apply Core.ext <;>
     simp [Program.coreStep, program, Continuation.program, workCfg, post, hm, Function.update_eq_self]
   all_goals omega

 theorem work_clear (P : Program Q (Unit ⊕ Γ)) (b : Bool) (ys : List Bool) (h : ℕ) :
     (program P).coreStep (workCfg b ys (-1) h) = queryCfg b ys h := by
   apply Core.ext <;>
     simp [Program.coreStep, program, Continuation.program, workCfg, queryCfg, post,
       markedBits, Function.update_idem, Function.update_eq_self]

 theorem query_step (P : Program Q (Unit ⊕ Γ)) (b : Bool) (ys : List Bool) (z : ℤ) (hz : 0 ≤ z) :
     (program P).coreStep (queryCfg b ys z) = queryCfg b ys (z-1) := by
   have hm := markedBits_nonmarker (Γ := Γ) [] z hz
   apply Core.ext <;>
     simp [Program.coreStep, program, Continuation.program, queryCfg, post, hm, Function.update_eq_self]
   all_goals omega

 theorem query_clear (P : Program Q (Unit ⊕ Γ)) (b : Bool) (ys : List Bool) :
     (program P).coreStep (queryCfg b ys (-1)) = normal b ys := by
   apply Core.ext <;>
     simp [Program.coreStep, program, Continuation.program, queryCfg, normal, post,
       markedBits, Function.update_idem, Function.update_eq_self]

 theorem cleanup_run (P : Program Q (Unit ⊕ Γ)) (b : Bool) (ys : List Bool) (n h : ℕ) :
     (program P).coreStep^[n+h+4] (workCfg b ys n h) = normal b ys := by
   have hw := iterate_cfg (program P).coreStep (fun t => workCfg b ys ((n : ℤ)-t) h) (n+1)
     (fun t ht => by convert work_step P b ys ((n : ℤ)-t) (by omega) h using 1 <;> congr 1 <;> omega)
   rw [show (n : ℤ)-(n+1 : ℕ) = -1 by omega] at hw
   have hc := iterate_trans (program P).coreStep hw
     (show (program P).coreStep^[1] (workCfg b ys (-1) h) = queryCfg b ys h from work_clear P b ys h)
   have hq := iterate_cfg (program P).coreStep (fun t => queryCfg b ys ((h : ℤ)-t)) (h+1)
     (fun t ht => by convert query_step P b ys ((h : ℤ)-t) (by omega) using 1 <;> congr 1 <;> omega)
   rw [show (h : ℤ)-(h+1 : ℕ) = -1 by omega] at hq
   have hcq := iterate_trans (program P).coreStep hc hq
   have hd := iterate_trans (program P).coreStep hcq
     (show (program P).coreStep^[1] (queryCfg b ys (-1)) = normal b ys from query_clear P b ys)
   simp only [Nat.cast_zero, sub_zero] at hd
   convert hd using 2 <;> omega

end QAdvFew.PoQOracle.OTM.FiniteControl.Normalization

set_option autoImplicit false
set_option synthInstance.maxSize 4096
namespace StudentTeacher976.Adaptivity.MultiTapeSimulation
open Turing
open QAdvFew.PoQOracle.OTM.FiniteControl
open StudentTeacher976.Adaptivity.MultiTapeCells

 theorem bitTape_option {A : Type} (ys : List Bool) (j : ℕ) :
     ((ys[j]?).map (bit (A := A))).getD none = bitTape ys (j : ℤ) := by
   by_cases hj : j < ys.length
   · simp [bitTape, hj, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
   · have he : ys[j]? = none := List.getElem?_eq_none (by omega)
     simp [bitTape, hj, he]

 theorem extracted_work_bits {k : ℕ} {Q : Type} {x : List Bool} (tm : MultiTapeTM k Bool Q)
     (role : Bool) (cells : List (MultiTapeCells.Cell k))
     (c : Turing.Cfg k Bool Q x) (h : Represents cells c) :
     (Sweeper.extractCfg (settings tm) role cells cells.length).work = Normalization.markedBits c.output := by
   funext z
   by_cases hz : 0 ≤ z
   · let j := z.toNat
     have hjz : (j : ℤ) = z := Int.toNat_of_nonneg hz
     rw [← hjz, Sweeper.extracted_work, Normalization.markedBits_at _ _ (by omega)]
     by_cases hj : j < cells.length
     · rw [if_pos hj]
       change (((cells.getD j (blank k)).output.map bit).getD none) = _
       rw [h j]
       exact bitTape_option c.output j
     · rw [if_neg hj]
       have ho := represented_output_bound cells c h
       simp [bitTape, show ¬ j < c.output.length by omega]
   · by_cases hz1 : z = -1
     · subst z
       cases role <;> simp [Sweeper.extractCfg, Sweeper.written, DataTape.marked,
         Normalization.markedBits]
     · cases role <;> simp [Sweeper.extractCfg, Sweeper.written, DataTape.marked, DataTape.tape,
         Normalization.markedBits, bitTape, hz, Function.update_of_ne hz1]

 theorem marked_empty_bits {Γ : Type} [Inhabited Γ] : DataTape.marked ([] : List Γ) = Normalization.markedBits [] := by
   funext z
   simp [DataTape.marked, DataTape.tape, Normalization.markedBits, bitTape]

 theorem extracted_query_bits {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q)
     (role : Bool) (cells : List (MultiTapeCells.Cell k)) :
     (Sweeper.extractCfg (settings tm) role cells cells.length).query = Normalization.markedBits [] := by
   cases role <;> simp [Sweeper.extractCfg, DataTape.erasePrefix_complete, marked_empty_bits]

 theorem normalized_run {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q) (x : List Bool) (t : ℕ)
     (hhalt : (tm.runFrom (tm.initCfg x) t).Halted) :
     ∃ u ≤ timeBound x.length t + 2*(x.length+2+t)+5,
       (Normalization.program (settings tm).program).coreStep^[u]
         ((Normalization.program (settings tm).program).coreInitial x) =
           Normalization.normal ((tm.runFrom (tm.initCfg x) t).output.head?.getD false)
             (tm.runFrom (tm.initCfg x) t).output := by
   have hp : (settings tm).program.Pure := Sweeper.program_pure
     (settings tm).initial (settings tm).reader (settings tm).accumulate (settings tm).action
     (settings tm).next (settings tm).update (settings tm).origin (settings tm).input
     (settings tm).right (settings tm).output
   obtain ⟨role, hr⟩ := core_complete tm x t hhalt
   let c := (evolve tm)^[t] (initialCfg tm x)
   have hmodel : Models c (tm.runFrom (tm.initCfg x) t) := evolution_models tm x t
   have hlen := evolution_length tm x t
   obtain ⟨u, hu, he⟩ := Continuation.hit_terminal (settings tm).program (fun b => (false,b))
     Normalization.post hp (timeBound x.length t) ((settings tm).program.coreInitial x)
     (terminal tm role c) ⟨_, rfl⟩ hr
   let b := (tm.runFrom (tm.initCfg x) t).output.head?.getD false
   let out := (tm.runFrom (tm.initCfg x) t).output
   have hb : Sweeper.firstBit (settings tm) c.cells = b := first_bit tm c.cells _ hmodel.2
   have ht : Continuation.embed (R := Bool × Bool) (terminal tm role c) =
       { Normalization.workCfg (Q := Control k Q) b out c.cells.length (if role then c.cells.length else 0)
         with state := .inr (.body (.inl b)) } := by
     apply Core.ext <;> simp only [Continuation.embed, terminal, hb, Sweeper.extractCfg, Normalization.workCfg]
     · exact extracted_work_bits tm role c.cells _ hmodel.2
     · exact extracted_query_bits tm role c.cells
     · cases role <;> rfl
   have hentry : (Normalization.program (settings tm).program).coreStep
       (Continuation.embed (R := Bool × Bool) (terminal tm role c)) =
       Normalization.workCfg (Q := Control k Q) b out c.cells.length (if role then c.cells.length else 0) := by
     rw [ht]
     apply Core.ext <;> simp [Normalization.program, Continuation.program, Program.coreStep,
       Normalization.workCfg, Function.update_eq_self]
   have hentryrun := iterate_trans (Normalization.program (settings tm).program).coreStep he
     (show (Normalization.program (settings tm).program).coreStep^[1]
       (Continuation.embed (R := Bool × Bool) (terminal tm role c)) = _ from hentry)
   have hfinal := iterate_trans (Normalization.program (settings tm).program).coreStep hentryrun
     (Normalization.cleanup_run (settings tm).program b out c.cells.length (if role then c.cells.length else 0))
   refine ⟨c.cells.length+(if role then c.cells.length else 0)+4+(1+u), ?_, ?_⟩
   · dsimp [c] at *
     split <;> omega
   · exact hfinal

end StudentTeacher976.Adaptivity.MultiTapeSimulation
namespace StudentTeacher976.Adaptivity
open Turing.MultiTapeTM QAdvFew.PoQOracle
 theorem polytime_transducer_clock {f : List Bool → List Bool}
     (hf : ComputableInPolyTime f encBits encBits) :
     ∃ (k : ℕ) (S : Type) (_ : Fintype S), ∃ M : Turing.MultiTapeTM k Bool S,
       ∃ p : Polynomial ℕ, ∀ w : List Bool,
         (M.runFrom (M.initCfg w) (p.eval w.length)).Halted ∧
         (M.runFrom (M.initCfg w) (p.eval w.length)).output = f w := by
   classical
   obtain ⟨t, s, ht, hs, k, S, hS, M, hM⟩ := hf
   letI : Finite S := hS
   letI : Fintype S := Fintype.ofFinite S
   obtain ⟨c, d, hbound⟩ := Cslib.polynomiallyBounded_iff_le.mp ht
   let p : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1)^d
   have hp (n : ℕ) : t n ≤ p.eval n := by simpa [p] using hbound n
   refine ⟨k, S, inferInstance, M, p, fun w => ?_⟩
   have hh := runsInTime_iff_halted.mp (hM w).2.1
   rw [runFrom_eq_of_halt M (M.initCfg w) (hp w.length) hh]
   refine ⟨hh, ?_⟩
   obtain ⟨u, hu, ho⟩ := (hM w).1
   change (M.runFrom (M.initCfg w) u).output = f w at ho
   rcases le_total u (t w.length) with hl | hl
   · rw [runFrom_eq_of_halt M (M.initCfg w) hl hu]
     exact ho
   · rw [runFrom_eq_of_halt M (M.initCfg w) hl hh] at ho
     exact ho


end StudentTeacher976.Adaptivity

set_option autoImplicit false
set_option synthInstance.maxSize 4096
namespace StudentTeacher976.Adaptivity.MultiTapeSimulation
open Turing QAdvFew.PoQOracle.OTM.FiniteControl

 noncomputable def normalizedClock (p : Polynomial ℕ) : Polynomial ℕ :=
   simulationClock p+2*(Polynomial.X+2+p)+5

 theorem normalized_clock {k : ℕ} {Q : Type} (tm : MultiTapeTM k Bool Q)
     (p : Polynomial ℕ) (hhalt : ∀ x, (tm.runFrom (tm.initCfg x) (p.eval x.length)).Halted)
     (x : List Bool) :
     (Normalization.program (settings tm).program).coreStep^[(normalizedClock p).eval x.length]
       ((Normalization.program (settings tm).program).coreInitial x) =
         Normalization.normal ((tm.runFrom (tm.initCfg x) (p.eval x.length)).output.head?.getD false)
           (tm.runFrom (tm.initCfg x) (p.eval x.length)).output := by
   obtain ⟨u, hu, hr⟩ := normalized_run tm x (p.eval x.length) (hhalt x)
   have htime : u ≤ (normalizedClock p).eval x.length := by
     simpa [normalizedClock, simulationClock_eval] using hu
   rw [← Nat.add_sub_of_le htime, Nat.add_comm u, Function.iterate_add_apply, hr]
   exact Function.iterate_fixed (show (Normalization.program (settings tm).program).coreStep
     (Normalization.normal ((tm.runFrom (tm.initCfg x) (p.eval x.length)).output.head?.getD false)
       (tm.runFrom (tm.initCfg x) (p.eval x.length)).output) = _ from rfl) _

end StudentTeacher976.Adaptivity.MultiTapeSimulation
namespace QAdvFew.PoQOracle.OTM.FiniteControl

 def normalCore {Q A : Type} (b : Bool) (ys : List Bool) : Core Q A where
   state := .inl b
   work := bitTape ys
   wh := 0
   query := fun _ => none
   qh := 0

end QAdvFew.PoQOracle.OTM.FiniteControl
namespace StudentTeacher976.Adaptivity
open Turing.MultiTapeTM QAdvFew.PoQOracle.OTM.FiniteControl

 theorem polytime_normalized {f : List Bool → List Bool}
     (hf : ComputableInPolyTime f encBits encBits) :
     ∃ (Q Γ : Type) (_ : Fintype Q) (_ : Fintype Γ) (_ : DecidableEq Γ),
       ∃ P : Program Q (Unit ⊕ Γ), ∃ clock : Polynomial ℕ,
         P.Pure ∧ ∀ x : List Bool,
           P.coreStep^[clock.eval x.length] (P.coreInitial x) = normalCore ((f x).head?.getD false) (f x) := by
   classical
   obtain ⟨k, S, hS, M, p, hM⟩ := polytime_transducer_clock hf
   letI : Fintype S := hS
   let P := (MultiTapeSimulation.settings M).program
   have hp : P.Pure := Sweeper.program_pure
     (MultiTapeSimulation.settings M).initial (MultiTapeSimulation.settings M).reader
     (MultiTapeSimulation.settings M).accumulate (MultiTapeSimulation.settings M).action
     (MultiTapeSimulation.settings M).next (MultiTapeSimulation.settings M).update
     (MultiTapeSimulation.settings M).origin (MultiTapeSimulation.settings M).input
     (MultiTapeSimulation.settings M).right (MultiTapeSimulation.settings M).output
   refine ⟨Normalization.State (MultiTapeSimulation.Control k S), MultiTapeCells.Cell k,
     inferInstance, inferInstance, inferInstance, Normalization.program P,
     MultiTapeSimulation.normalizedClock p, Normalization.program_pure P hp, fun x => ?_⟩
   have hh := MultiTapeSimulation.normalized_clock M p (fun x => (hM x).1) x
   rw [(hM x).2] at hh
   exact hh


end StudentTeacher976.Adaptivity

theorem solution
    {f : List Bool → List Bool}
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits) :
    ∃ (Q Γ : Type) (_ : Fintype Q) (_ : Fintype Γ) (_ : DecidableEq Γ),
      ∃ P : QAdvFew.PoQOracle.OTM.FiniteControl.Program Q (Unit ⊕ Γ), ∃ clock : Polynomial ℕ,
        P.Pure ∧ ∀ x : List Bool,
          P.coreStep^[clock.eval x.length] (P.coreInitial x) =
            { state := Sum.inl ((f x).head?.getD false)
              work := QAdvFew.PoQOracle.OTM.FiniteControl.bitTape (f x)
              wh := 0
              query := fun _ => none
              qh := 0 } := by
  exact StudentTeacher976.Adaptivity.polytime_normalized hf

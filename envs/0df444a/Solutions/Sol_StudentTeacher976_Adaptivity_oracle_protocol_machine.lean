-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.oracle_protocol_machine
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:55:29.865903+00:00
-- url     : https://prove2.me/submissions/90d1c3b2-c0d3-4508-a90a-8edf2d94d823

import Definitions.Def_StudentTeacher976_Adaptivity_OracleProtocol
import Theorems.Thm_StudentTeacher976_Adaptivity_polynomial_transducer_normal_form
import Theorems.Thm_StudentTeacher976_Adaptivity_finite_control_compilation
set_option autoImplicit false

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
namespace QAdvFew.PoQOracle.OTM.FiniteControl
variable {Q A : Type}

 def NoAsk (P : Program Q A) (c : Core Q A) : Prop :=
   match c.state with
   | .inl _ => True
   | .inr q => ∀ yes no, P.code q (c.work c.wh) (c.query c.qh) ≠ .ask yes no

 theorem Program.run_add (P : Program Q A) (O : Oracle) (c : Cfg Q A) (s t : ℕ) :
     (P.step O)^[s+t] c = (P.step O)^[t] ((P.step O)^[s] c) := by
   rw [Nat.add_comm, Function.iterate_add_apply]

 theorem step_core_noAsk (P : Program Q A) (O : Oracle) (c : Cfg Q A) (h : NoAsk P c.core) :
     (P.step O c).core = P.coreStep c.core := by
   cases hs : c.state with
   | inl b => simp only [Program.step, Cfg.core, hs, Program.coreStep]
   | inr q =>
     cases hi : P.code q (c.work c.wh) (c.query c.qh) with
     | halt b => simp only [Program.step, Cfg.core, hs, hi, Program.coreStep]
     | move next a m b n => simp only [Program.step, Cfg.core, hs, hi, Program.coreStep]
     | stop b a m d n => simp only [Program.step, Cfg.core, hs, hi, Program.coreStep]
     | ask yes no =>
       have hh : ∀ y n, P.code q (c.work c.wh) (c.query c.qh) ≠ .ask y n := by
         simpa only [NoAsk, Cfg.core, hs] using h
       exact False.elim (hh yes no hi)

 theorem step_of_core (P : Program Q A) (O : Oracle) (d : Cfg Q A) (c c' : Core Q A)
     (hd : d.core = c) (hn : NoAsk P c) (hs : P.coreStep c = c') :
     (P.step O d).core = c' := by
   rw [step_core_noAsk]
   · rw [hd, hs]
   · rw [hd]; exact hn

 theorem iterate_core_noAsk (P : Program Q A) (O : Oracle) (c : Cfg Q A) (t : ℕ)
     (h : ∀ j < t, NoAsk P (P.coreStep^[j] c.core)) :
     ((P.step O)^[t] c).core = P.coreStep^[t] c.core := by
   induction t with
   | zero => rfl
   | succ t ih =>
     have he := ih (fun j hj => h j (by omega))
     rw [Function.iterate_succ_apply', Function.iterate_succ_apply', step_core_noAsk]
     · rw [he]
     · rw [he]
       exact h t (by omega)

 theorem iterate_core_cfg (P : Program Q A) (O : Oracle) (d : Cfg Q A)
     (C : ℕ → Core Q A) (N : ℕ) (hd : d.core = C 0)
     (hs : ∀ j < N, P.coreStep (C j) = C (j+1))
     (hn : ∀ j < N, NoAsk P (C j)) : ((P.step O)^[N] d).core = C N := by
   have hh : ∀ j ≤ N, ((P.step O)^[j] d).core = C j := by
     intro j hj
     induction j with
     | zero => exact hd
     | succ j ih =>
       have he := ih (by omega)
       rw [Function.iterate_succ_apply', step_core_noAsk]
       · rw [he, hs j (by omega)]
       · rw [he]
         exact hn j (by omega)
   exact hh N le_rfl

 theorem Program.qh_bound (P : Program Q A) (O : Oracle) (c : Cfg Q A)
     (h : c.qh ≤ c.qhi) : (P.step O c).qh ≤ (P.step O c).qhi := by
   cases hs : c.state with
   | inl b => simpa only [Program.step, hs] using h
   | inr q =>
     cases hh : P.code q (c.work c.wh) (c.query c.qh) <;>
       simp only [Program.step, hs, hh]
     · exact le_max_right _ _
     · exact le_max_right _ _
     · exact h
     · exact h

 theorem Program.qh_bound_run (P : Program Q A) (O : Oracle) (x : List Bool) (t : ℕ) :
     ((P.step O)^[t] (P.initial x)).qh ≤ ((P.step O)^[t] (P.initial x)).qhi := by
   induction t with
   | zero => simp [Program.initial]
   | succ t ih => rw [Function.iterate_succ_apply']; exact P.qh_bound O _ ih

 theorem Program.qh_bound_iterate (P : Program Q A) (O : Oracle) (c : Cfg Q A) (t : ℕ)
     (h : c.qh ≤ c.qhi) : ((P.step O)^[t] c).qh ≤ ((P.step O)^[t] c).qhi := by
   induction t with
   | zero => exact h
   | succ t ih => rw [Function.iterate_succ_apply']; exact P.qh_bound O _ ih

 theorem ask_core (P : Program Q A) (O : Oracle) (c : Cfg Q A) (q yes no : Q)
     (hs : c.state = .inr q) (hi : P.code q (c.work c.wh) (c.query c.qh) = .ask yes no)
     (query : List Bool) (hr : ∀ j : ℕ, readBit (c.query (j : ℤ)) = query[j]?)
     (hh : (query.length : ℤ) ≤ c.qhi) :
     (P.step O c).core = { c.core with state := .inr (if O query then yes else no) } := by
   have he := readWord_of_reads c.query query c.qhi hr hh
   simp only [Program.step, hs, hi, he]
   rfl

end QAdvFew.PoQOracle.OTM.FiniteControl

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.FamilyContinuation

 inductive State (I Q R : Type) | body (i : I) (q : Bool ⊕ Q) | post (r : R)
   deriving DecidableEq, Fintype

 def lift {I Q R A : Type} (i : I) : Instr Q A → Instr (State I Q R) A
   | .move q a m b n => .move (.body i (.inr q)) a m b n
   | .stop r a m b n => .move (.body i (.inl r)) a m b n
   | .halt r => .move (.body i (.inl r)) none 1 none 1
   | .ask yes no => .ask (.body i (.inr yes)) (.body i (.inr no))

-- The halt instruction must preserve both currently scanned symbols.
 def liftAt {I Q R A : Type} (i : I) (a b : Cell A) : Instr Q A → Instr (State I Q R) A
   | .halt r => .move (.body i (.inl r)) a 1 b 1
   | instr => lift i instr

 def program {I Q R A : Type} (P : Program Q A) (i : I) (start : I → Bool → R)
     (post : R → Cell A → Cell A → Instr (State I Q R) A) : Program (State I Q R) A where
   start := .body i (.inr P.start)
   code := fun s a b => match s with
     | .body i (.inr q) => liftAt i a b (P.code q a b)
     | .body i (.inl r) => .move (.post (start i r)) a 1 b 1
     | .post r => post r a b

 def embed {I Q R A : Type} (i : I) (c : Core Q A) : Core (State I Q R) A where
   state := .inr (.body i c.state)
   work := c.work
   wh := c.wh
   query := c.query
   qh := c.qh

 theorem embed_initial {I Q R A : Type} (P : Program Q A) (i : I) (start : I → Bool → R) (post) (x : List Bool) :
     (program P i start post).coreInitial x = (embed (R := R) i (P.coreInitial x)) := rfl

 theorem step_embed {I Q R A : Type} (P : Program Q A) (i : I) (start : I → Bool → R) (post)
     (hpure : P.Pure) (c : Core Q A) (q : Q) (hq : c.state = .inr q) :
     (program P i start post).coreStep (embed i c) = embed i (P.coreStep c) := by
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

 theorem hit_embed {I Q R A : Type} (P : Program Q A) (i : I) (start : I → Bool → R) (post)
     (hpure : P.Pure) (t : ℕ) (c : Core Q A)
     (h : ∃ b, (P.coreStep^[t] c).state = .inl b) :
     ∃ u ≤ t, ∃ b,
       (P.coreStep^[u] c).state = .inl b ∧
       (program P i start post).coreStep^[u] (embed i c) = embed i (P.coreStep^[u] c) := by
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
       · rw [Function.iterate_succ_apply, step_embed P i start post hpure c q hc, hr,
           Function.iterate_succ_apply]

 theorem hit_terminal {I Q R A : Type} (P : Program Q A) (i : I) (start : I → Bool → R) (post)
     (hpure : P.Pure) (t : ℕ) (c : Core Q A) (terminal : Core Q A)
     (hterm : ∃ b, terminal.state = .inl b) (hr : P.coreStep^[t] c = terminal) :
     ∃ u ≤ t, (program P i start post).coreStep^[u] (embed i c) = embed i terminal := by
   obtain ⟨b, hb⟩ := hterm
   obtain ⟨u, hu, r, hhalt, hr'⟩ := hit_embed P i start post hpure t c ⟨b, by rw [hr]; exact hb⟩
   have hfixed : P.coreStep (P.coreStep^[u] c) = P.coreStep^[u] c := by
     simp only [Program.coreStep, hhalt]
   have hstable := Function.iterate_fixed hfixed (t-u)
   have he : P.coreStep^[u] c = terminal := by
     rw [← hr, ← Nat.add_sub_of_le hu, Nat.add_comm u, Function.iterate_add_apply, hstable]
   exact ⟨u, hu, by rw [hr', he]⟩

end QAdvFew.PoQOracle.OTM.FiniteControl.FamilyContinuation

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.FamilyContinuation
variable {I Q R A : Type}

 theorem noAsk_embed (P : Program Q A) (i : I) (start : I → Bool → R) (post) (hp : P.Pure) (c : Core Q A) :
     NoAsk (program P i start post) (embed i c) := by
   cases hs : c.state with
   | inl b => simp [NoAsk, embed, program, hs]
   | inr q =>
     intro yes no
     cases hi : P.code q (c.work c.wh) (c.query c.qh) with
     | halt b => simp [embed, program, hs, hi, liftAt]
     | move n a m b k => simp [embed, program, hs, hi, liftAt, lift]
     | stop b a m d k => simp [embed, program, hs, hi, liftAt, lift]
     | ask y n => exact False.elim (hp q _ _ y n hi)

 theorem hit_prefix (P : Program Q A) (i : I) (start : I → Bool → R) (post) (hp : P.Pure)
     (t : ℕ) (c terminal : Core Q A) (hterm : ∃ b, terminal.state = .inl b)
     (hr : P.coreStep^[t] c = terminal) :
     ∃ u ≤ t, P.coreStep^[u] c = terminal ∧
       ∀ j ≤ u, (program P i start post).coreStep^[j] (embed i c) = embed i (P.coreStep^[j] c) := by
   classical
   have hex : ∃ u : ℕ, u ≤ t ∧ ∃ b, (P.coreStep^[u] c).state = .inl b :=
     ⟨t, le_rfl, by rw [hr]; exact hterm⟩
   let u := Nat.find hex
   obtain ⟨hu, b, hb⟩ := Nat.find_spec hex
   change (P.coreStep^[u] c).state = .inl b at hb
   have he : P.coreStep^[u] c = terminal := by
     have hfixed : P.coreStep (P.coreStep^[u] c) = P.coreStep^[u] c := by simp only [Program.coreStep, hb]
     have hs := Function.iterate_fixed hfixed (t-u)
     rw [← hr, ← Nat.add_sub_of_le hu, Nat.add_comm u, Function.iterate_add_apply, hs]
   refine ⟨u, hu, he, ?_⟩
   intro j hj
   induction j with
   | zero => rfl
   | succ j ih =>
     have hjlt : j < u := by omega
     have hne := Nat.find_min hex hjlt
     cases hstate : (P.coreStep^[j] c).state with
     | inl r => exact False.elim (hne ⟨by omega, r, hstate⟩)
     | inr q =>
       rw [Function.iterate_succ_apply', ih (by omega), step_embed P i start post hp _ q hstate,
         Function.iterate_succ_apply']

 theorem full_terminal (P : Program Q A) (i : I) (start : I → Bool → R) (post) (hp : P.Pure)
     (O : Oracle) (d : Cfg (State I Q R) A) (c terminal : Core Q A)
     (hd : d.core = embed i c) (t : ℕ) (hterm : ∃ b, terminal.state = .inl b)
     (hr : P.coreStep^[t] c = terminal) :
     ∃ u ≤ t, (((program P i start post).step O)^[u] d).core = embed i terminal := by
   obtain ⟨u, hu, he, hpre⟩ := hit_prefix P i start post hp t c terminal hterm hr
   refine ⟨u, hu, ?_⟩
   have htrace : ∀ j < u, NoAsk (program P i start post) ((program P i start post).coreStep^[j] d.core) := by
     intro j hj
     rw [hd, hpre j (by omega)]
     exact noAsk_embed P i start post hp _
   rw [iterate_core_noAsk _ O d u htrace, hd, hpre u le_rfl, he]

end QAdvFew.PoQOracle.OTM.FiniteControl.FamilyContinuation
namespace QAdvFew.PoQOracle.OTM.FiniteControl.Normalization
open DataTape
variable {Γ : Type}
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


end QAdvFew.PoQOracle.OTM.FiniteControl.Normalization
namespace QAdvFew.PoQOracle.OTM.FiniteControl
 def normalCore {Q A : Type} (b : Bool) (ys : List Bool) : Core Q A where
   state := .inl b
   work := bitTape ys
   wh := 0
   query := fun _ => none
   qh := 0

end QAdvFew.PoQOracle.OTM.FiniteControl

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver
open DataTape

 inductive Phase
   | initial | initialMark | initialCopy (a b : Bool) | initialFlush (b : Bool) | initialRewind
   | inspect | markBoth | readHeader | readDone | skipAnswer
   | queryMarker | queryBit | rewindWork | ask | askAdvance | askReady
   | answer (b : Bool) | answerHome | clearQuery
   | finalBack | finalMark | finalZero
   | returnResult (b : Bool)
   deriving DecidableEq, Fintype

 abbrev State (Q : Type) := FamilyContinuation.State Bool Q Phase

 def after (finalCall b : Bool) : Phase := if finalCall then .returnResult b else .inspect

 def post {Q Γ : Type} [DecidableEq Γ] (entry : Q)
     (s : Phase) (a b : Cell (Unit ⊕ Γ)) : Instr (State Q) (Unit ⊕ Γ) :=
   match s with
   | .initial => .move (.post .initialMark) a 0 b 1
   | .initialMark => .move (.post (.initialCopy false false)) marker 2 b 1
   | .initialCopy c d => match readBit a with
     | some e => .move (.post (.initialCopy d e)) (bit c) 2 b 1
     | none => .move (.post (.initialFlush d)) (bit c) 2 b 1
   | .initialFlush d => .move (.post .initialRewind) (bit d) 2 b 1
   | .initialRewind => if a = marker then .move (.body false (.inr entry)) none 2 b 1
     else .move (.post .initialRewind) a 0 b 1
   | .inspect => .move (.post .markBoth) a 0 b 0
   | .markBoth => .move (.post .readHeader) marker 2 marker 2
   | .readHeader => .move (.post .readDone) a 2 b 1
   | .readDone => if readBit a = some true then .move (.post .finalBack) a 0 b 1
     else .move (.post .skipAnswer) a 2 b 1
   | .skipAnswer => .move (.post .queryMarker) a 2 b 1
   | .queryMarker => if readBit a = some true then .move (.post .queryBit) a 2 b 1
     else .move (.post .rewindWork) a 0 b 1
   | .queryBit => match readBit a with
     | some e => .move (.post .queryMarker) a 2 (bit e) 2
     | none => .halt false
   | .rewindWork => if a = marker then .move (.post .ask) none 2 b 1
     else .move (.post .rewindWork) a 0 b 1
   -- The query head remains at the end, so its current position certifies that
   -- the bookkeeping bound contains the whole query word.
   | .ask => .move (.post .askAdvance) a 2 b 1
   | .askAdvance => .move (.post .askReady) a 2 b 1
   | .askReady => .ask (.post (.answer true)) (.post (.answer false))
   | .answer v => .move (.post .answerHome) (bit v) 0 b 1
   | .answerHome => .move (.post .clearQuery) a 0 b 1
   | .clearQuery => if b = marker then .move (.body false (.inr entry)) a 1 none 2
     else .move (.post .clearQuery) a 1 none 0
   | .finalBack => .move (.post .finalMark) a 0 b 0
   | .finalMark => .move (.post .finalZero) none 2 none 2
   | .finalZero => .move (.body true (.inr entry)) (bit false) 1 b 1
   | .returnResult v => .halt v

 def program {Q Γ : Type} [DecidableEq Γ] (P : Program Q (Unit ⊕ Γ)) : Program (State Q) (Unit ⊕ Γ) :=
   { FamilyContinuation.program P false after (post P.start) with start := .post .initial }

end QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
namespace QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver
open DataTape
variable {Q Γ : Type} [DecidableEq Γ]

 theorem post_noAsk (entry : Q) (s : Phase) (a b : Cell (Unit ⊕ Γ)) (yes no : State Q)
     (h : s ≠ .askReady) : post entry s a b ≠ .ask yes no := by
   cases s <;> simp only [post]
   all_goals (repeat' split) <;> simp_all

 theorem phase_noAsk (P : Program Q (Unit ⊕ Γ)) (c : Core (State Q) (Unit ⊕ Γ)) (s : Phase)
     (hs : c.state = .inr (.post s)) (h : s ≠ .askReady) : NoAsk (program P) c := by
   simp only [NoAsk, hs, program, FamilyContinuation.program]
   exact fun yes no => post_noAsk P.start s _ _ yes no h

 def overwrite (x y : List Bool) (n : ℕ) : ℤ → Cell (Unit ⊕ Γ) := fun z =>
   if 0 ≤ z ∧ z < n then bit (y.getD z.toNat false) else bitTape x z

 theorem overwrite_zero (x y : List Bool) : overwrite (Γ := Γ) x y 0 = bitTape x := by
   funext z
   unfold overwrite
   rw [if_neg (by omega)]

 theorem overwrite_update (x y : List Bool) (n : ℕ) :
     Function.update (overwrite (Γ := Γ) x y n) (n : ℤ) (bit (y.getD n false)) = overwrite x y (n+1) := by
   funext z
   by_cases hz : z = n
   · subst z; simp [overwrite]
   · rw [Function.update_of_ne hz]
     unfold overwrite
     have he : (0 ≤ z ∧ z < (n : ℤ)) ↔ (0 ≤ z ∧ z < (n+1 : ℕ)) := by omega
     simp only [he]

 theorem overwrite_complete (x y : List Bool) (h : x.length ≤ y.length) :
     overwrite (Γ := Γ) x y y.length = bitTape y := by
   funext z
   unfold overwrite bitTape
   by_cases hz : 0 ≤ z ∧ z < y.length
   · simp [hz]
   · have hx : ¬(0 ≤ z ∧ z < x.length) := by omega
     simp [hz, hx]

 def markedOverwrite (x y : List Bool) (n : ℕ) : ℤ → Cell (Unit ⊕ Γ) :=
   Function.update (overwrite x y n) (-1) marker

 theorem markedOverwrite_at (x y : List Bool) (n : ℕ) (z : ℤ) (hz : 0 ≤ z) :
     markedOverwrite (Γ := Γ) x y n z = overwrite x y n z := by
   simp [markedOverwrite, show z ≠ -1 by omega]

 theorem markedOverwrite_update (x y : List Bool) (n : ℕ) :
     Function.update (markedOverwrite (Γ := Γ) x y n) (n : ℤ) (bit (y.getD n false)) =
       markedOverwrite x y (n+1) := by
   unfold markedOverwrite
   rw [Function.update_comm (show (-1 : ℤ) ≠ n by omega), overwrite_update]


 theorem shifted_getD (x : List Bool) (p : ℕ) : (shifted x).getD (p+2) false = x.getD p false := by
   change (false::false::x).getD (p+1+1) false = _
   rw [List.getD_cons_succ, List.getD_cons_succ]

 def copyCfg (P : Program Q (Unit ⊕ Γ)) (x : List Bool) (p : ℕ) : Core (State Q) (Unit ⊕ Γ) where
   state := .inr (.post (.initialCopy ((shifted x).getD p false) ((shifted x).getD (p+1) false)))
   work := markedOverwrite x (shifted x) p
   wh := p
   query := fun _ => none
   qh := 0

 theorem initial_steps (P : Program Q (Unit ⊕ Γ)) (x : List Bool) :
     (program P).coreStep^[2] ((program P).coreInitial x) = copyCfg P x 0 := by
   change (program P).coreStep ((program P).coreStep ((program P).coreInitial x)) = _
   apply Core.ext <;> simp [Program.coreStep, Program.coreInitial, program, FamilyContinuation.program,
     post, copyCfg, shifted, markedOverwrite, overwrite_zero, Function.update_eq_self]

 theorem copy_step (P : Program Q (Unit ⊕ Γ)) (x : List Bool) (p : ℕ) (hp : p < x.length) :
     (program P).coreStep (copyCfg P x p) = copyCfg P x (p+1) := by
   have hwork : markedOverwrite (Γ := Γ) x (shifted x) p (p : ℤ) = bit (x.getD p false) := by
     rw [markedOverwrite_at _ _ _ _ (by omega)]
     simp [overwrite, bitTape, hp]
   have hupdate := markedOverwrite_update (Γ := Γ) x (shifted x) p
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, copyCfg, post,
     hwork, readBit, bit, shifted_getD, hupdate, Function.update_eq_self]
   all_goals first | omega | exact hupdate | exact (shifted_getD x p).symm

 def flushCfg (P : Program Q (Unit ⊕ Γ)) (x : List Bool) : Core (State Q) (Unit ⊕ Γ) where
   state := .inr (.post (.initialFlush ((shifted x).getD (x.length+1) false)))
   work := markedOverwrite x (shifted x) (x.length+1)
   wh := x.length+1
   query := fun _ => none
   qh := 0

 def rewindCfg (P : Program Q (Unit ⊕ Γ)) (y : List Bool) (t : ℕ) : Core (State Q) (Unit ⊕ Γ) where
   state := .inr (.post .initialRewind)
   work := Normalization.markedBits y
   wh := (y.length : ℤ)-t
   query := fun _ => none
   qh := 0

 theorem copy_end (P : Program Q (Unit ⊕ Γ)) (x : List Bool) :
     (program P).coreStep (copyCfg P x x.length) = flushCfg P x := by
   have hw : markedOverwrite (Γ := Γ) x (shifted x) x.length (x.length : ℤ) = none := by
     rw [markedOverwrite_at _ _ _ _ (by omega)]
     simp [overwrite, bitTape]
   have hu := markedOverwrite_update (Γ := Γ) x (shifted x) x.length
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, copyCfg, flushCfg,
     post, hw, readBit, hu, Function.update_eq_self]
   all_goals first | omega | exact hu

 theorem flush_step (P : Program Q (Unit ⊕ Γ)) (x : List Bool) :
     (program P).coreStep (flushCfg P x) = rewindCfg P (shifted x) 0 := by
   have hu := markedOverwrite_update (Γ := Γ) x (shifted x) (x.length+1)
   have hc : markedOverwrite (Γ := Γ) x (shifted x) (x.length+2) = Normalization.markedBits (shifted x) := by
     unfold markedOverwrite Normalization.markedBits
     rw [show x.length+2 = (shifted x).length by simp [shifted], overwrite_complete x (shifted x) (by simp [shifted] <;> omega)]
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, flushCfg, rewindCfg,
     post, hu, hc, Function.update_eq_self]
   all_goals first | simpa [shifted] using hu.trans hc | (simp only [shifted, List.length_cons] <;> omega)

 theorem rewind_step (P : Program Q (Unit ⊕ Γ)) (y : List Bool) (t : ℕ) (ht : t < y.length+1) :
     (program P).coreStep (rewindCfg P y t) = rewindCfg P y (t+1) := by
   have hm := Normalization.markedBits_nonmarker (Γ := Γ) y ((y.length : ℤ)-t) (by omega)
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, rewindCfg,
     post, hm, Function.update_eq_self]
   all_goals omega

 theorem rewind_clear (P : Program Q (Unit ⊕ Γ)) (y : List Bool) :
     (program P).coreStep (rewindCfg P y (y.length+1)) =
       FamilyContinuation.embed false (P.coreInitial y) := by
   have ht : (y.length : ℤ)-(y.length+1 : ℕ) = -1 := by omega
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, rewindCfg,
     post, ht, Normalization.markedBits, FamilyContinuation.embed, Program.coreInitial,
     Function.update_idem, Function.update_eq_self]

 theorem initial_run (P : Program Q (Unit ⊕ Γ)) (x : List Bool) :
     (program P).coreStep^[2*x.length+8] ((program P).coreInitial x) =
       FamilyContinuation.embed false (P.coreInitial (shifted x)) := by
   have hc := iterate_cfg (program P).coreStep (copyCfg P x) x.length (fun p hp => copy_step P x p hp)
   have h1 := iterate_trans (program P).coreStep (initial_steps P x) hc
   have h2 := iterate_trans (program P).coreStep h1
     (show (program P).coreStep^[1] (copyCfg P x x.length) = flushCfg P x from copy_end P x)
   have h3 := iterate_trans (program P).coreStep h2
     (show (program P).coreStep^[1] (flushCfg P x) = rewindCfg P (shifted x) 0 from flush_step P x)
   have hr := iterate_cfg (program P).coreStep (rewindCfg P (shifted x)) ((shifted x).length+1)
     (fun t ht => rewind_step P (shifted x) t ht)
   have h4 := iterate_trans (program P).coreStep h3 hr
   have h5 := iterate_trans (program P).coreStep h4
     (show (program P).coreStep^[1] (rewindCfg P (shifted x) ((shifted x).length+1)) = _ from rewind_clear P (shifted x))
   convert h5 using 2 <;> simp only [shifted, List.length_cons] <;> omega


 theorem initial_full_run (P : Program Q (Unit ⊕ Γ)) (O : Oracle) (x : List Bool) :
     (((program P).step O)^[2*x.length+8] ((program P).initial x)).core =
       FamilyContinuation.embed false (P.coreInitial (shifted x)) := by
   let d0 := (program P).initial x
   let d1 := ((program P).step O)^[2] d0
   let d2 := ((program P).step O)^[x.length] d1
   let d3 := (program P).step O d2
   let d4 := (program P).step O d3
   let d5 := ((program P).step O)^[(shifted x).length+1] d4
   have hn : ∀ j < 2, NoAsk (program P) ((program P).coreStep^[j] d0.core) := by
     intro j hj
     interval_cases j <;>
       simp [d0, Program.initial, Cfg.core, Program.coreStep, NoAsk, program, FamilyContinuation.program, post]
   have h1 : d1.core = copyCfg P x 0 := by
     rw [iterate_core_noAsk _ O d0 2 hn]
     exact initial_steps P x
   have h2 : d2.core = copyCfg P x x.length := iterate_core_cfg (program P) O d1 (copyCfg P x)
     x.length h1 (fun j hj => copy_step P x j hj)
     (fun j hj => phase_noAsk P (copyCfg P x j) _ rfl (by simp))
   have h3 : d3.core = flushCfg P x := step_of_core (program P) O d2 _ _ h2
     (phase_noAsk P (copyCfg P x x.length) _ rfl (by simp)) (copy_end P x)
   have h4 : d4.core = rewindCfg P (shifted x) 0 := step_of_core (program P) O d3 _ _ h3
     (phase_noAsk P (flushCfg P x) _ rfl (by simp)) (flush_step P x)
   have h5 : d5.core = rewindCfg P (shifted x) ((shifted x).length+1) :=
     iterate_core_cfg (program P) O d4 (rewindCfg P (shifted x)) ((shifted x).length+1) h4
       (fun j hj => rewind_step P (shifted x) j hj)
       (fun j hj => phase_noAsk P (rewindCfg P (shifted x) j) _ rfl (by simp))
   have h6 := step_of_core (program P) O d5 _ _ h5
     (phase_noAsk P (rewindCfg P (shifted x) ((shifted x).length+1)) _ rfl (by simp)) (rewind_clear P (shifted x))
   change ((((program P).step O)^[1]) (((program P).step O)^[(shifted x).length+1]
     (((program P).step O)^[1] (((program P).step O)^[1]
       (((program P).step O)^[x.length] (((program P).step O)^[2] ((program P).initial x))))))).core = _ at h6
   rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, ← Function.iterate_add_apply,
     ← Function.iterate_add_apply, ← Function.iterate_add_apply] at h6
   convert h6 using 3 <;> simp only [shifted, List.length_cons] <;> omega

end QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver
open DataTape Turing.MultiTapeTM
variable {Q Γ : Type} [DecidableEq Γ]


 theorem frame_even (w : List Bool) (j : ℕ) (hj : j < w.length) :
     (frame w).getD (2*j) false = true := by
   induction w generalizing j with
   | nil => simp at hj
   | cons b w ih =>
     cases j with
     | zero => rfl
     | succ j =>
       rw [show 2*(j+1) = 2*j+1+1 by omega, frame_cons, List.getD_cons_succ, List.getD_cons_succ]
       exact ih j (by simp only [List.length_cons] at hj; omega)

 theorem frame_odd (w : List Bool) (j : ℕ) (hj : j < w.length) :
     (frame w).getD (2*j+1) false = w.getD j false := by
   induction w generalizing j with
   | nil => simp at hj
   | cons b w ih =>
     cases j with
     | zero => rfl
     | succ j =>
       rw [show 2*(j+1)+1 = (2*j+1)+1+1 by omega, frame_cons, List.getD_cons_succ, List.getD_cons_succ,
         List.getD_cons_succ]
       exact ih j (by simp only [List.length_cons] at hj; omega)

 theorem frame_end (w : List Bool) : (frame w).getD (2*w.length) false = false := by
   induction w with
   | nil => rfl
   | cons b w ih =>
     rw [List.length_cons, show 2*(w.length+1) = 2*w.length+1+1 by omega, frame_cons,
       List.getD_cons_succ, List.getD_cons_succ, ih]

 theorem record_at (done answer : Bool) (q s : List Bool) (j : ℕ) (hj : j < (frame q).length) :
     (record done answer q s).getD (3+j) false = (frame q).getD j false := by
   rw [show 3+j = j+1+1+1 by omega]
   change (true::done::answer::(frame q++frame s)).getD (j+1+1+1) false = _
   rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
     List.getD_append _ _ _ _ hj]

 theorem record_read (done answer : Bool) (q s : List Bool) (j : ℕ) (hj : j < (frame q).length) :
     readBit (Normalization.markedBits (Γ := Γ) (record done answer q s) ((3+j : ℕ) : ℤ)) =
       some ((frame q).getD j false) := by
   rw [Normalization.markedBits_at _ _ (by omega)]
   have hlen : 3+j < (record done answer q s).length := by simp [record] at *; omega
   rw [bitTape_at _ _ hlen, record_at _ _ _ _ _ hj]
   rfl

 theorem markedBits_append (ys : List Bool) (b : Bool) :
     Function.update (Normalization.markedBits (Γ := Γ) ys) (ys.length : ℤ) (bit b) =
       Normalization.markedBits (ys++[b]) := by
   unfold Normalization.markedBits
   rw [Function.update_comm (show (-1 : ℤ) ≠ ys.length by omega), bitTape_append_bit]

 def queryCfg (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) (j : ℕ) : Core (State Q) (Unit ⊕ Γ) where
   state := .inr (.post .queryMarker)
   work := Normalization.markedBits (record false answer q s)
   wh := 3+2*j
   query := Normalization.markedBits (q.take j)
   qh := j

 def queryBitCfg (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) (j : ℕ) : Core (State Q) (Unit ⊕ Γ) where
   state := .inr (.post .queryBit)
   work := Normalization.markedBits (record false answer q s)
   wh := 3+2*j+1
   query := Normalization.markedBits (q.take j)
   qh := j

 theorem query_marker_step (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) (j : ℕ) (hj : j < q.length) :
     (program P).coreStep (queryCfg P answer q s j) = queryBitCfg P answer q s j := by
   have hr := (record_read (Γ := Γ) false answer q s (2*j) (by simp; omega)).trans
     (congrArg some (frame_even q j hj))
   simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hr
   have he : ((3 : ℕ)+2*j : ℤ) = ((3+2*j : ℕ) : ℤ) := by omega
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, queryCfg, queryBitCfg,
     post, hr, Function.update_eq_self]
   all_goals omega

 theorem query_bit_step (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) (j : ℕ) (hj : j < q.length) :
     (program P).coreStep (queryBitCfg P answer q s j) = queryCfg P answer q s (j+1) := by
   have hr := (record_read (Γ := Γ) false answer q s (2*j+1) (by simp; omega)).trans
     (congrArg some (frame_odd q j hj))
   simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hr
   rw [← add_assoc] at hr
   have hp : (q.take j).length = j := by simp [List.length_take, Nat.min_eq_right (by omega : j ≤ q.length)] <;> omega
   have ht : q.take (j+1) = q.take j ++ [q.getD j false] := by
     simpa only [List.getD_eq_getElem _ _ hj] using List.take_succ_eq_append_getElem hj
   have hu := markedBits_append (Γ := Γ) (q.take j) (q.getD j false)
   rw [hp, ← ht] at hu
   have he : (3 : ℤ)+2*j+1 = ((3+(2*j+1) : ℕ) : ℤ) := by omega
   have hr2 : readBit (Normalization.markedBits (Γ := Γ) (record false answer q s) ((3 : ℤ)+2*j+1)) = some (q.getD j false) := by
     rw [he]
     exact (record_read (Γ := Γ) false answer q s (2*j+1) (by simp; omega)).trans (congrArg some (frame_odd q j hj))
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, queryCfg, queryBitCfg,
     post, hr2, hu, Function.update_eq_self]
   all_goals first | omega | exact hu

 def queryRewindCfg (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) (t : ℕ) : Core (State Q) (Unit ⊕ Γ) where
   state := .inr (.post .rewindWork)
   work := Normalization.markedBits (record false answer q s)
   wh := (2+2*q.length : ℤ)-t
   query := Normalization.markedBits q
   qh := q.length

 def askCfg (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) (phase : Phase) (h : ℤ) : Core (State Q) (Unit ⊕ Γ) where
   state := .inr (.post phase)
   work := bitTape (record false answer q s)
   wh := h
   query := Normalization.markedBits q
   qh := q.length

 theorem query_end (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep (queryCfg P answer q s q.length) = queryRewindCfg P answer q s 0 := by
   have hr := (record_read (Γ := Γ) false answer q s (2*q.length) (by simp)).trans
     (congrArg some (frame_end q))
   simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hr
   have he : (3 : ℤ)+2*q.length = ((3+2*q.length : ℕ) : ℤ) := by omega
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, queryCfg, queryRewindCfg,
     post, hr, Function.update_eq_self]
   all_goals omega

 theorem query_rewind_step (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) (t : ℕ)
     (ht : t < 2*q.length+3) :
     (program P).coreStep (queryRewindCfg P answer q s t) = queryRewindCfg P answer q s (t+1) := by
   have hm := Normalization.markedBits_nonmarker (Γ := Γ) (record false answer q s)
     ((2+2*q.length : ℤ)-t) (by omega)
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, queryRewindCfg,
     post, hm, Function.update_eq_self]
   all_goals omega

 theorem query_rewind_clear (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep (queryRewindCfg P answer q s (2*q.length+3)) = askCfg P answer q s .ask 0 := by
   have he : (2+2*q.length : ℤ)-(2*q.length+3 : ℕ) = -1 := by omega
   simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at he
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, queryRewindCfg, askCfg,
     post, he, Normalization.markedBits, Function.update_idem, Function.update_eq_self]

 theorem ask_advance (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep^[2] (askCfg P answer q s .ask 0) = askCfg P answer q s .askReady 2 := by
   change (program P).coreStep ((program P).coreStep (askCfg P answer q s .ask 0)) = askCfg P answer q s .askReady 2
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, askCfg,
     post, Function.update_eq_self]

 theorem query_copy_run (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep^[2*q.length] (queryCfg P answer q s 0) = queryCfg P answer q s q.length := by
   have hh : ∀ j ≤ q.length, (program P).coreStep^[2*j] (queryCfg P answer q s 0) = queryCfg P answer q s j := by
     intro j hj
     induction j with
     | zero => rfl
     | succ j ih =>
       rw [show 2*(j+1) = 2+2*j by omega, Function.iterate_add_apply, ih (by omega)]
       change (program P).coreStep ((program P).coreStep _) = _
       rw [query_marker_step P answer q s j (by omega), query_bit_step P answer q s j (by omega)]
   exact hh q.length le_rfl

 theorem query_run_to_ask (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep^[4*q.length+7] (queryCfg P answer q s 0) = askCfg P answer q s .askReady 2 := by
   have h1 := iterate_trans (program P).coreStep (query_copy_run P answer q s)
     (show (program P).coreStep^[1] (queryCfg P answer q s q.length) = _ from query_end P answer q s)
   have hr := iterate_cfg (program P).coreStep (queryRewindCfg P answer q s) (2*q.length+3)
     (fun t ht => query_rewind_step P answer q s t ht)
   have h2 := iterate_trans (program P).coreStep h1 hr
   have h3 := iterate_trans (program P).coreStep h2
     (show (program P).coreStep^[1] (queryRewindCfg P answer q s (2*q.length+3)) = _ from query_rewind_clear P answer q s)
   have h4 := iterate_trans (program P).coreStep h3 (ask_advance P answer q s)
   convert h4 using 2 <;> omega


 def copyingCfg (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) (t : ℕ) : Core (State Q) (Unit ⊕ Γ) :=
   if t % 2 = 0 then queryCfg P answer q s (t/2) else queryBitCfg P answer q s (t/2)

 theorem copying_step (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) (t : ℕ)
     (ht : t < 2*q.length) :
     (program P).coreStep (copyingCfg P answer q s t) = copyingCfg P answer q s (t+1) := by
   have hm := Nat.mod_add_div t 2
   by_cases he : t % 2 = 0
   · have hodd : (t+1)%2 ≠ 0 := by omega
     have hdiv : (t+1)/2 = t/2 := by omega
     simp only [copyingCfg, he, hodd, ↓reduceIte, hdiv]
     exact query_marker_step P answer q s (t/2) (by omega)
   · have heven : (t+1)%2 = 0 := by omega
     have hdiv : (t+1)/2 = t/2+1 := by omega
     simp only [copyingCfg, he, heven, ↓reduceIte, hdiv]
     exact query_bit_step P answer q s (t/2) (by omega)

 theorem copying_noAsk (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) (t : ℕ) :
     NoAsk (program P) (copyingCfg P answer q s t) := by
   unfold copyingCfg
   split
   · exact phase_noAsk P _ .queryMarker rfl (by simp)
   · exact phase_noAsk P _ .queryBit rfl (by simp)

 theorem query_full_run_to_ask (P : Program Q (Unit ⊕ Γ)) (O : Oracle) (d : Cfg (State Q) (Unit ⊕ Γ))
     (answer : Bool) (q s : List Bool) (hd : d.core = queryCfg P answer q s 0) :
     (((program P).step O)^[4*q.length+7] d).core = askCfg P answer q s .askReady 2 := by
   have h1 : (((program P).step O)^[2*q.length] d).core = queryCfg P answer q s q.length := by
     have hh := iterate_core_cfg (program P) O d (copyingCfg P answer q s) (2*q.length)
       (by simpa [copyingCfg] using hd) (fun t ht => copying_step P answer q s t ht)
       (fun t ht => copying_noAsk P answer q s t)
     simpa [copyingCfg, Nat.mul_div_right] using hh
   have h2 : (((program P).step O)^[2*q.length+1] d).core = queryRewindCfg P answer q s 0 := by
     rw [(program P).run_add]
     exact step_of_core (program P) O _ _ _ h1
       (phase_noAsk P _ .queryMarker rfl (by simp)) (query_end P answer q s)
   have h3 : (((program P).step O)^[(2*q.length+1)+(2*q.length+3)] d).core =
       queryRewindCfg P answer q s (2*q.length+3) := by
     rw [(program P).run_add]
     exact iterate_core_cfg (program P) O _ (queryRewindCfg P answer q s) (2*q.length+3) h2
       (fun t ht => query_rewind_step P answer q s t ht)
       (fun t ht => phase_noAsk P _ .rewindWork rfl (by simp))
   have h4 : (((program P).step O)^[(2*q.length+1)+(2*q.length+3)+1] d).core = askCfg P answer q s .ask 0 := by
     rw [(program P).run_add]
     exact step_of_core (program P) O _ _ _ h3
       (phase_noAsk P _ .rewindWork rfl (by simp)) (query_rewind_clear P answer q s)
   have hn : ∀ j < 2, NoAsk (program P) ((program P).coreStep^[j] (askCfg P answer q s .ask 0)) := by
     intro j hj
     interval_cases j
     · exact phase_noAsk P _ .ask rfl (by simp)
     · have hs : ((program P).coreStep (askCfg P answer q s .ask 0)).state = .inr (.post .askAdvance) := by
         simp [Program.coreStep, program, FamilyContinuation.program, askCfg, post]
       exact phase_noAsk P _ .askAdvance hs (by simp)
   have h5 : (((program P).step O)^[(2*q.length+1)+(2*q.length+3)+1+2] d).core = askCfg P answer q s .askReady 2 := by
     rw [(program P).run_add, iterate_core_noAsk]
     · rw [h4, ask_advance]
     · simpa only [h4] using hn
   convert h5 using 3 <;> omega

end QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver
open DataTape Turing.MultiTapeTM
variable {Q Γ : Type} [DecidableEq Γ]

 theorem bitTape_set {A : Type} (ys : List Bool) (j : ℕ) (b : Bool) (hj : j < ys.length) :
     Function.update (bitTape (A := A) ys) (j : ℤ) (bit b) = bitTape (ys.set j b) := by
   funext z
   by_cases hz : z = j
   · subst z
     simp [bitTape, hj, List.getD, List.getElem?_set_self hj]
   · rw [Function.update_of_ne hz]
     unfold bitTape
     simp only [List.length_set]
     split
     · have hne : j ≠ z.toNat := by omega
       simp only [List.getD, List.getElem?_set_ne hne]
     · rfl

 theorem markedBits_reads (ys : List Bool) (j : ℕ) :
     readBit (Normalization.markedBits (Γ := Γ) ys (j : ℤ)) = ys[j]? := by
   rw [Normalization.markedBits_at _ _ (by omega)]
   by_cases hj : j < ys.length
   · rw [bitTape_at _ _ hj, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
     rfl
   · simp [bitTape, hj, List.getElem?_eq_none (by omega : ys.length ≤ j), readBit]

 def clearAbove (ys : List Bool) (z : ℤ) : ℤ → Cell (Unit ⊕ Γ) := fun i =>
   if z < i then none else Normalization.markedBits ys i

 theorem clearAbove_update (ys : List Bool) (z : ℤ) :
     Function.update (clearAbove (Γ := Γ) ys z) z none = clearAbove ys (z-1) := by
   funext i
   by_cases hi : i = z
   · subst i; simp [clearAbove]
   · rw [Function.update_of_ne hi]
     unfold clearAbove
     have he : z < i ↔ z-1 < i := by omega
     simp only [he]

 theorem clearAbove_start (ys : List Bool) : clearAbove (Γ := Γ) ys ys.length = Normalization.markedBits ys := by
   funext i
   unfold clearAbove
   by_cases hi : (ys.length : ℤ) < i
   · have hz : 0 ≤ i := by omega
     rw [if_pos hi, Normalization.markedBits_at _ _ hz]
     simp [bitTape, show ¬(0 ≤ i ∧ i < ys.length) by omega]
   · rw [if_neg hi]

 theorem clearAbove_end (ys : List Bool) : clearAbove (Γ := Γ) ys (-1) =
     Function.update (fun _ => none) (-1) marker := by
   funext i
   by_cases hi : i = -1
   · subst i; simp [clearAbove, Normalization.markedBits]
   · by_cases hz : -1 < i
     · simp [clearAbove, hz, Function.update_of_ne hi]
     · simp [clearAbove, hz, Normalization.markedBits, Function.update_of_ne hi, bitTape, show ¬0 ≤ i by omega]

 def homeCfg (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) : Core (State Q) (Unit ⊕ Γ) where
   state := .inr (.post .answerHome)
   work := bitTape (record false answer q s)
   wh := 1
   query := Normalization.markedBits q
   qh := q.length

 def clearCfg (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) (t : ℕ) : Core (State Q) (Unit ⊕ Γ) where
   state := .inr (.post .clearQuery)
   work := bitTape (record false answer q s)
   wh := 0
   query := clearAbove q ((q.length : ℤ)-t)
   qh := (q.length : ℤ)-t

 theorem answer_step (P : Program Q (Unit ⊕ Γ)) (answer v : Bool) (q s : List Bool) :
     (program P).coreStep (askCfg P answer q s (.answer v) 2) = homeCfg P v q s := by
   have hu := bitTape_set (A := Unit ⊕ Γ) (record false answer q s) 2 v (by simp [record])
   change Function.update (bitTape (A := Unit ⊕ Γ) (record false answer q s)) 2 (bit v) =
     bitTape (record false v q s) at hu
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, askCfg, homeCfg,
     post, hu, Function.update_eq_self]

 theorem answer_home (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep (homeCfg P answer q s) = clearCfg P answer q s 0 := by
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, homeCfg, clearCfg,
     post, clearAbove_start, Function.update_eq_self]

 theorem clear_step (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) (t : ℕ) (ht : t < q.length+1) :
     (program P).coreStep (clearCfg P answer q s t) = clearCfg P answer q s (t+1) := by
   have hm : clearAbove (Γ := Γ) q ((q.length : ℤ)-t) ((q.length : ℤ)-t) ≠ marker := by
     simpa [clearAbove] using Normalization.markedBits_nonmarker (Γ := Γ) q ((q.length : ℤ)-t) (by omega)
   have hu := clearAbove_update (Γ := Γ) q ((q.length : ℤ)-t)
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, clearCfg,
     post, hm, hu, Function.update_eq_self]
   all_goals first | (congr 1 <;> omega) | omega

 theorem clear_finish (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep (clearCfg P answer q s (q.length+1)) =
       FamilyContinuation.embed false (P.coreInitial (record false answer q s)) := by
   have he : (q.length : ℤ)-(q.length+1 : ℕ) = -1 := by omega
   simp only [Nat.cast_add, Nat.cast_one] at he
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, clearCfg,
     FamilyContinuation.embed, Program.coreInitial, post, he, clearAbove_end, Function.update_idem,
     Function.update_eq_self]

 theorem oracle_step (P : Program Q (Unit ⊕ Γ)) (O : Oracle) (d : Cfg (State Q) (Unit ⊕ Γ))
     (answer : Bool) (q s : List Bool) (hd : d.core = askCfg P answer q s .askReady 2)
     (hb : d.qh ≤ d.qhi) :
     ((program P).step O d).core = askCfg P answer q s (.answer (O q)) 2 := by
   have hs : d.state = .inr (.post .askReady) := congrArg Core.state hd
   have hi : (program P).code (.post .askReady) (d.work d.wh) (d.query d.qh) =
       .ask (.post (.answer true)) (.post (.answer false)) := rfl
   have hr : ∀ j : ℕ, readBit (d.query (j : ℤ)) = q[j]? := by
     intro j
     have he := congrArg (fun c => c.query (j : ℤ)) hd
     change d.query (j : ℤ) = Normalization.markedBits q (j : ℤ) at he
     rw [he]
     exact markedBits_reads q j
   have hq : d.qh = (q.length : ℤ) := congrArg Core.qh hd
   have ha := ask_core (program P) O d (.post .askReady) (.post (.answer true)) (.post (.answer false))
     hs hi q hr (by omega)
   rw [ha, hd]
   cases ho : O q <;> rfl

 theorem query_answer_full_run (P : Program Q (Unit ⊕ Γ)) (O : Oracle) (d : Cfg (State Q) (Unit ⊕ Γ))
     (answer : Bool) (q s : List Bool) (hd : d.core = askCfg P answer q s .askReady 2)
     (hb : d.qh ≤ d.qhi) :
     (((program P).step O)^[q.length+5] d).core =
       FamilyContinuation.embed false (P.coreInitial (record false (O q) q s)) := by
   have h1 : (((program P).step O)^[1] d).core = askCfg P answer q s (.answer (O q)) 2 :=
     oracle_step P O d answer q s hd hb
   have h2 : (((program P).step O)^[1+1] d).core = homeCfg P (O q) q s := by
     rw [(program P).run_add]
     exact step_of_core (program P) O _ _ _ h1
       (phase_noAsk P _ (.answer (O q)) rfl (by simp)) (answer_step P answer (O q) q s)
   have h3 : (((program P).step O)^[1+1+1] d).core = clearCfg P (O q) q s 0 := by
     rw [(program P).run_add]
     exact step_of_core (program P) O _ _ _ h2
       (phase_noAsk P _ .answerHome rfl (by simp)) (answer_home P (O q) q s)
   have h4 : (((program P).step O)^[1+1+1+(q.length+1)] d).core = clearCfg P (O q) q s (q.length+1) := by
     rw [(program P).run_add]
     exact iterate_core_cfg (program P) O _ (clearCfg P (O q) q s) (q.length+1) h3
       (fun t ht => clear_step P (O q) q s t ht)
       (fun t ht => phase_noAsk P _ .clearQuery rfl (by simp))
   have h5 : (((program P).step O)^[1+1+1+(q.length+1)+1] d).core =
       FamilyContinuation.embed false (P.coreInitial (record false (O q) q s)) := by
     rw [(program P).run_add]
     exact step_of_core (program P) O _ _ _ h4
       (phase_noAsk P _ .clearQuery rfl (by simp)) (clear_finish P (O q) q s)
   convert h5 using 3 <;> omega

end QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver
open DataTape Turing.MultiTapeTM
variable {Q Γ : Type} [DecidableEq Γ]

 def inspectCfg (P : Program Q (Unit ⊕ Γ)) (done answer : Bool) (q s : List Bool) : Core (State Q) (Unit ⊕ Γ) where
   state := .inr (.post .inspect)
   work := bitTape (record done answer q s)
   wh := 0
   query := fun _ => none
   qh := 0

 def prepCfg (P : Program Q (Unit ⊕ Γ)) (done answer : Bool) (q s : List Bool)
     (phase : Phase) (wh qh : ℤ) (marked : Bool) : Core (State Q) (Unit ⊕ Γ) where
   state := .inr (.post phase)
   work := if marked then Normalization.markedBits (record done answer q s) else bitTape (record done answer q s)
   wh := wh
   query := if marked then Normalization.markedBits [] else fun _ => none
   qh := qh

 theorem bitTape_nil {A : Type} : bitTape (A := A) [] = fun _ => none := by funext z; simp [bitTape]

 theorem inspect_move (P : Program Q (Unit ⊕ Γ)) (done answer : Bool) (q s : List Bool) :
     (program P).coreStep (inspectCfg P done answer q s) = prepCfg P done answer q s .markBoth (-1) (-1) false := by
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, inspectCfg, prepCfg, post,
     Function.update_eq_self]

 theorem mark_both (P : Program Q (Unit ⊕ Γ)) (done answer : Bool) (q s : List Bool) :
     (program P).coreStep (prepCfg P done answer q s .markBoth (-1) (-1) false) =
       prepCfg P done answer q s .readHeader 0 0 true := by
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, prepCfg, post,
     Normalization.markedBits, bitTape_nil]

 theorem header_move (P : Program Q (Unit ⊕ Γ)) (done answer : Bool) (q s : List Bool) :
     (program P).coreStep (prepCfg P done answer q s .readHeader 0 0 true) =
       prepCfg P done answer q s .readDone 1 0 true := by
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, prepCfg, post,
     Function.update_eq_self]

 theorem read_done (done answer : Bool) (q s : List Bool) :
     readBit (Normalization.markedBits (Γ := Γ) (record done answer q s) 1) = some done := by
   rw [Normalization.markedBits_at _ _ (by omega)]
   rw [show (1 : ℤ) = (1 : ℕ) by rfl, bitTape_at _ _ (by simp [record])]
   rfl

 theorem done_false (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep (prepCfg P false answer q s .readDone 1 0 true) =
       prepCfg P false answer q s .skipAnswer 2 0 true := by
   have hr := read_done (Γ := Γ) false answer q s
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, prepCfg, post, hr,
     Function.update_eq_self]

 theorem done_true (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep (prepCfg P true answer q s .readDone 1 0 true) =
       prepCfg P true answer q s .finalBack 0 0 true := by
   have hr := read_done (Γ := Γ) true answer q s
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, prepCfg, post, hr,
     Function.update_eq_self]

 theorem skip_answer (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep (prepCfg P false answer q s .skipAnswer 2 0 true) = queryCfg P answer q s 0 := by
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, prepCfg, queryCfg, post,
     Function.update_eq_self]

 theorem final_back (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep (prepCfg P true answer q s .finalBack 0 0 true) =
       prepCfg P true answer q s .finalMark (-1) (-1) true := by
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, prepCfg, post,
     Function.update_eq_self]

 theorem final_mark (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep (prepCfg P true answer q s .finalMark (-1) (-1) true) =
       prepCfg P true answer q s .finalZero 0 0 false := by
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, prepCfg, post,
     Normalization.markedBits_clear, bitTape_nil]


 theorem final_zero (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep (prepCfg P true answer q s .finalZero 0 0 false) =
       FamilyContinuation.embed true (P.coreInitial (finalRecord answer q s)) := by
   have hu := bitTape_set (A := Unit ⊕ Γ) (record true answer q s) 0 false (by simp [record])
   change Function.update (bitTape (A := Unit ⊕ Γ) (record true answer q s)) 0 (bit false) =
     bitTape (finalRecord answer q s) at hu
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, prepCfg, post,
     FamilyContinuation.embed, Program.coreInitial, hu, Function.update_eq_self]

 def prepareCfg (P : Program Q (Unit ⊕ Γ)) (done answer : Bool) (q s : List Bool) : ℕ → Core (State Q) (Unit ⊕ Γ)
   | 0 => inspectCfg P done answer q s
   | 1 => prepCfg P done answer q s .markBoth (-1) (-1) false
   | 2 => prepCfg P done answer q s .readHeader 0 0 true
   | 3 => prepCfg P done answer q s .readDone 1 0 true
   | 4 => if done then prepCfg P true answer q s .finalBack 0 0 true else prepCfg P false answer q s .skipAnswer 2 0 true
   | 5 => if done then prepCfg P true answer q s .finalMark (-1) (-1) true else queryCfg P answer q s 0
   | 6 => prepCfg P true answer q s .finalZero 0 0 false
   | _ => FamilyContinuation.embed true (P.coreInitial (finalRecord answer q s))

 theorem prepare_step (P : Program Q (Unit ⊕ Γ)) (done answer : Bool) (q s : List Bool) (j : ℕ)
     (hj : j < if done then 7 else 5) :
     (program P).coreStep (prepareCfg P done answer q s j) = prepareCfg P done answer q s (j+1) := by
   cases done
   · simp only [Bool.false_eq_true, ↓reduceIte] at hj
     interval_cases j
     exacts [inspect_move P false answer q s, mark_both P false answer q s, header_move P false answer q s,
       done_false P answer q s, skip_answer P answer q s]
   · simp only [↓reduceIte] at hj
     interval_cases j
     exacts [inspect_move P true answer q s, mark_both P true answer q s, header_move P true answer q s,
       done_true P answer q s, final_back P answer q s, final_mark P answer q s, final_zero P answer q s]

 theorem prepare_cfg_noAsk (P : Program Q (Unit ⊕ Γ)) (done answer : Bool) (q s : List Bool) (j : ℕ)
     (hj : j < if done then 7 else 5) : NoAsk (program P) (prepareCfg P done answer q s j) := by
   cases done
   · simp only [Bool.false_eq_true, ↓reduceIte] at hj
     interval_cases j <;> apply phase_noAsk P _ _ rfl <;> simp
   · simp only [↓reduceIte] at hj
     interval_cases j <;> apply phase_noAsk P _ _ rfl <;> simp

 theorem query_prepare (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep^[5] (inspectCfg P false answer q s) = queryCfg P answer q s 0 :=
   iterate_cfg (program P).coreStep (prepareCfg P false answer q s) 5
     (fun j hj => prepare_step P false answer q s j (by simpa using hj))

 theorem final_prepare (P : Program Q (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool) :
     (program P).coreStep^[7] (inspectCfg P true answer q s) =
       FamilyContinuation.embed true (P.coreInitial (finalRecord answer q s)) :=
   iterate_cfg (program P).coreStep (prepareCfg P true answer q s) 7
     (fun j hj => prepare_step P true answer q s j (by simpa using hj))

 theorem query_prepare_full (P : Program Q (Unit ⊕ Γ)) (O : Oracle) (d : Cfg (State Q) (Unit ⊕ Γ))
     (answer : Bool) (q s : List Bool) (hd : d.core = inspectCfg P false answer q s) :
     (((program P).step O)^[5] d).core = queryCfg P answer q s 0 :=
   iterate_core_cfg (program P) O d (prepareCfg P false answer q s) 5 hd
     (fun j hj => prepare_step P false answer q s j (by simpa using hj))
     (fun j hj => prepare_cfg_noAsk P false answer q s j (by simpa using hj))

 theorem final_prepare_full (P : Program Q (Unit ⊕ Γ)) (O : Oracle) (d : Cfg (State Q) (Unit ⊕ Γ))
     (answer : Bool) (q s : List Bool) (hd : d.core = inspectCfg P true answer q s) :
     (((program P).step O)^[7] d).core = FamilyContinuation.embed true (P.coreInitial (finalRecord answer q s)) :=
   iterate_core_cfg (program P) O d (prepareCfg P true answer q s) 7 hd
     (fun j hj => prepare_step P true answer q s j (by simpa using hj))
     (fun j hj => prepare_cfg_noAsk P true answer q s j (by simpa using hj))

end QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver
open DataTape Turing.MultiTapeTM
variable {Q Γ : Type} [DecidableEq Γ]

 theorem call_run (P : Program Q (Unit ⊕ Γ)) (hp : P.Pure) (O : Oracle)
     (d : Cfg (State Q) (Unit ⊕ Γ)) (mode : Bool) (input out : List Bool) (t : ℕ) (b : Bool)
     (hd : d.core = FamilyContinuation.embed mode (P.coreInitial input))
     (ht : P.coreStep^[t] (P.coreInitial input) = normalCore b out) :
     ∃ u ≤ t, (((program P).step O)^[u] d).core = FamilyContinuation.embed mode (normalCore b out) := by
   exact FamilyContinuation.full_terminal P mode after (post P.start) hp O d (P.coreInitial input)
     (normalCore b out) hd t ⟨b,rfl⟩ ht

 theorem inspect_step (P : Program Q (Unit ⊕ Γ)) (b done answer : Bool) (q s : List Bool) :
     (program P).coreStep (FamilyContinuation.embed false (normalCore b (record done answer q s))) =
       inspectCfg P done answer q s := by
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, FamilyContinuation.embed,
     normalCore, inspectCfg, after, Function.update_eq_self]

 theorem inspect_step_full (P : Program Q (Unit ⊕ Γ)) (O : Oracle)
     (d : Cfg (State Q) (Unit ⊕ Γ)) (b done answer : Bool) (q s : List Bool)
     (hd : d.core = FamilyContinuation.embed false (normalCore b (record done answer q s))) :
     ((program P).step O d).core = inspectCfg P done answer q s := by
   apply step_of_core (program P) O d _ _ hd
   · simp [NoAsk, program, FamilyContinuation.program, FamilyContinuation.embed, normalCore, after]
   · exact inspect_step P b done answer q s

 theorem oracle_round (P : Program Q (Unit ⊕ Γ)) (O : Oracle)
     (d : Cfg (State Q) (Unit ⊕ Γ)) (answer : Bool) (q s : List Bool)
     (hd : d.core = inspectCfg P false answer q s) (hb : d.qh ≤ d.qhi) :
     (((program P).step O)^[5*q.length+17] d).core =
       FamilyContinuation.embed false (P.coreInitial (record false (O q) q s)) := by
   have h1 : (((program P).step O)^[5] d).core = queryCfg P answer q s 0 := query_prepare_full P O d answer q s hd
   have h2 : (((program P).step O)^[5+(4*q.length+7)] d).core = askCfg P answer q s .askReady 2 := by
     rw [(program P).run_add]
     exact query_full_run_to_ask P O _ answer q s h1
   have h3 : (((program P).step O)^[5+(4*q.length+7)+(q.length+5)] d).core =
       FamilyContinuation.embed false (P.coreInitial (record false (O q) q s)) := by
     rw [(program P).run_add]
     exact query_answer_full_run P O _ answer q s h2 ((program P).qh_bound_iterate O d _ hb)
   convert h3 using 3 <;> omega

 def returnCfg (P : Program Q (Unit ⊕ Γ)) (b : Bool) (out : List Bool) : Core (State Q) (Unit ⊕ Γ) where
   state := .inr (.post (.returnResult b))
   work := bitTape out
   wh := 0
   query := fun _ => none
   qh := 0

 theorem return_enter (P : Program Q (Unit ⊕ Γ)) (b : Bool) (out : List Bool) :
     (program P).coreStep (FamilyContinuation.embed true (normalCore b out)) = returnCfg P b out := by
   apply Core.ext <;> simp [Program.coreStep, program, FamilyContinuation.program, FamilyContinuation.embed,
     normalCore, returnCfg, after, Function.update_eq_self]

 theorem return_halt (P : Program Q (Unit ⊕ Γ)) (b : Bool) (out : List Bool) :
     (program P).coreStep (returnCfg P b out) = normalCore b out := by
   rfl

 theorem return_full_run (P : Program Q (Unit ⊕ Γ)) (O : Oracle)
     (d : Cfg (State Q) (Unit ⊕ Γ)) (b : Bool) (out : List Bool)
     (hd : d.core = FamilyContinuation.embed true (normalCore b out)) :
     (((program P).step O)^[2] d).core = normalCore b out := by
   have h1 : (((program P).step O)^[1] d).core = returnCfg P b out := by
     apply step_of_core (program P) O d _ _ hd
     · simp [NoAsk, program, FamilyContinuation.program, FamilyContinuation.embed, normalCore, after]
     · exact return_enter P b out
   rw [show (2:ℕ)=1+1 by rfl, (program P).run_add]
   exact step_of_core (program P) O _ _ _ h1
     (phase_noAsk P _ (.returnResult b) rfl (by simp)) (return_halt P b out)

end QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver
open DataTape Turing.MultiTapeTM
variable {Q Γ : Type} [DecidableEq Γ]


 theorem polyEvalMono (p : Polynomial ℕ) {n m : ℕ} (h : n ≤ m) : p.eval n ≤ p.eval m := by
   simp only [Polynomial.eval_eq_sum, Polynomial.sum]
   apply Finset.sum_le_sum
   intro i hi
   exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

 def unitTime (p : Polynomial ℕ) (B : ℕ) : ℕ := p.eval B+5*B+18

 theorem bounded_run (P : Program Q (Unit ⊕ Γ)) (hp : P.Pure)
     (cpu : List Bool → List Bool) (p : Polynomial ℕ)
     (hcpu : ∀ x, P.coreStep^[p.eval x.length] (P.coreInitial x) = normalCore ((cpu x).head?.getD false) (cpu x))
     (O : Oracle) (B : ℕ) (input out : List Bool) (steps : ℕ)
     (trace : Trace cpu O B input out steps)
     (d : Cfg (State Q) (Unit ⊕ Γ))
     (hd : d.core = FamilyContinuation.embed false (P.coreInitial input)) (hb : d.qh ≤ d.qhi) :
     ∃ u ≤ (steps+2)*unitTime p B,
       (((program P).step O)^[u] d).core = normalCore (out.head?.getD false) out := by
   induction trace generalizing d with
   | done input answer q s out hinput hsize hc hf =>
     have hrun := hcpu input
     rw [hc] at hrun
     change P.coreStep^[p.eval input.length] (P.coreInitial input) = normalCore true _ at hrun
     obtain ⟨u, hu, h1⟩ := call_run P hp O d false input (record true answer q s) (p.eval input.length) true hd hrun
     have h2 : (((program P).step O)^[u+1] d).core = inspectCfg P true answer q s := by
       rw [(program P).run_add]
       exact inspect_step_full P O _ true true answer q s h1
     have h3 : (((program P).step O)^[u+1+7] d).core =
         FamilyContinuation.embed true (P.coreInitial (finalRecord answer q s)) := by
       rw [(program P).run_add]
       exact final_prepare_full P O _ answer q s h2
     have hfinal := hcpu (finalRecord answer q s)
     rw [hf] at hfinal
     obtain ⟨v, hv, h4⟩ := call_run P hp O _ true (finalRecord answer q s) out
       (p.eval (finalRecord answer q s).length) (out.head?.getD false) h3 hfinal
     have h4' : (((program P).step O)^[u+1+7+v] d).core = FamilyContinuation.embed true (normalCore (out.head?.getD false) out) := by
       rw [(program P).run_add]
       exact h4
     have h5 : (((program P).step O)^[u+1+7+v+2] d).core = normalCore (out.head?.getD false) out := by
       rw [(program P).run_add]
       exact return_full_run P O _ (out.head?.getD false) out h4'
     refine ⟨u+1+7+v+2, ?_, h5⟩
     have hi := polyEvalMono p hinput
     have hs : (finalRecord answer q s).length ≤ B := by simpa [finalRecord, record] using hsize
     have hf := polyEvalMono p hs
     dsimp [unitTime]
     omega
   | query input answer q s out steps hinput hsize hc next ih =>
     have hrun := hcpu input
     rw [hc] at hrun
     change P.coreStep^[p.eval input.length] (P.coreInitial input) = normalCore true _ at hrun
     obtain ⟨u, hu, h1⟩ := call_run P hp O d false input (record false answer q s) (p.eval input.length) true hd hrun
     have h2 : (((program P).step O)^[u+1] d).core = inspectCfg P false answer q s := by
       rw [(program P).run_add]
       exact inspect_step_full P O _ true false answer q s h1
     have h3 : (((program P).step O)^[u+1+(5*q.length+17)] d).core =
         FamilyContinuation.embed false (P.coreInitial (record false (O q) q s)) := by
       rw [(program P).run_add]
       exact oracle_round P O _ answer q s h2 ((program P).qh_bound_iterate O d _ hb)
     obtain ⟨v, hv, h4⟩ := ih _ h3 ((program P).qh_bound_iterate O d _ hb)
     have h4' : (((program P).step O)^[u+1+(5*q.length+17)+v] d).core = normalCore (out.head?.getD false) out := by
       rw [(program P).run_add]
       exact h4
     refine ⟨u+1+(5*q.length+17)+v, ?_, h4'⟩
     have hi := polyEvalMono p hinput
     have hq : q.length ≤ B := by simp [record] at hsize; omega
     dsimp [unitTime] at *
     nlinarith

end QAdvFew.PoQOracle.OTM.FiniteControl.OracleDriver

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM.FiniteControl
variable {Q A : Type}

 def WorkUpper (c : Cfg Q A) : Prop :=
   0 ≤ c.whi ∧ c.wh ≤ c.whi ∧ ∀ z : ℤ, c.whi < z → c.work z = none

 theorem upper_update (tape : ℤ → Cell A) (head hi next : ℤ) (a : Cell A)
     (h : 0 ≤ hi ∧ head ≤ hi ∧ ∀ z : ℤ, hi < z → tape z = none) :
     0 ≤ max hi next ∧ next ≤ max hi next ∧
       ∀ z : ℤ, max hi next < z → Function.update tape head a z = none := by
   refine ⟨le_trans h.1 (le_max_left _ _), le_max_right _ _, fun z hz => ?_⟩
   have hh : hi < z := lt_of_le_of_lt (le_max_left _ _) hz
   rw [Function.update_of_ne (by omega : z ≠ head)]
   exact h.2.2 z hh

 theorem Program.work_upper_step (P : Program Q A) (O : Oracle) (c : Cfg Q A) (h : WorkUpper c) :
     WorkUpper (P.step O c) := by
   cases hs : c.state with
   | inl b => simpa only [Program.step, hs] using h
   | inr q =>
     cases hi : P.code q (c.work c.wh) (c.query c.qh) with
     | halt b => simpa only [Program.step, hs, hi, WorkUpper] using h
     | ask yes no => simpa only [Program.step, hs, hi, WorkUpper] using h
     | move next a m b n =>
       change WorkUpper _
       simpa only [Program.step, hs, hi, WorkUpper] using upper_update c.work c.wh c.whi
         (c.wh+(m.val : ℤ)-1) a h
     | stop b a m d n =>
       simpa only [Program.step, hs, hi, WorkUpper] using upper_update c.work c.wh c.whi
         (c.wh+(m.val : ℤ)-1) a h

 theorem Program.work_upper_run (P : Program Q A) (O : Oracle) (x : List Bool) (t : ℕ) :
     WorkUpper ((P.step O)^[t] (P.initial x)) := by
   induction t with
   | zero =>
     refine ⟨by simp [Program.initial], by simp [Program.initial], ?_⟩
     intro z hz
     change (if 0 ≤ z ∧ z < x.length then bit (x.getD z.toNat false) else none) = none
     rw [if_neg (by dsimp [Program.initial] at hz; omega)]
   | succ t ih => rw [Function.iterate_succ_apply']; exact P.work_upper_step O _ ih

 theorem readWord_of_upper (c : Cfg Q A) (ys : List Bool) (h : WorkUpper c)
     (hw : c.work = bitTape ys) : readWord c.work c.whi = ys := by
   have hzero := h.1
   have hlen : (ys.length : ℤ) ≤ c.whi+1 := by
     by_contra hh
     have hpos : 0 < ys.length := by omega
     have he := h.2.2 ((ys.length-1 : ℕ) : ℤ) (by omega)
     rw [hw, bitTape_at _ _ (by omega)] at he
     simp [bit] at he
   unfold readWord
   have hreads (j : ℕ) : readBit (c.work (j : ℤ)) = ys[j]? := by
     rw [hw]
     by_cases hj : j < ys.length
     · rw [bitTape_at _ _ hj, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
       rfl
     · simp [bitTape, hj, List.getElem?_eq_none (by omega : ys.length ≤ j), readBit]
   simp only [hreads, read_list_prefix]
   exact List.take_of_length_le (by omega)

end QAdvFew.PoQOracle.OTM.FiniteControl

set_option autoImplicit false
namespace StudentTeacher976.Adaptivity
open QAdvFew.PoQOracle QAdvFew.PoQOracle.OTM.FiniteControl
open Turing.MultiTapeTM

 theorem oracle_protocol_machine (cpu : Word → Word)
     (hcpu : ComputableInPolyTime cpu encBits encBits) :
     ∃ M : OTM, ∀ (O : Oracle) (f : Word → Word) (T B : Polynomial ℕ),
       (∀ x : Word, ∃ steps ≤ T.eval x.length,
         OracleDriver.Trace cpu O (B.eval x.length) (OracleDriver.shifted x) (f x) steps) →
       ∃ clock : Polynomial ℕ, ∀ x : Word,
         M.result O x (clock.eval x.length) = some ((f x).head?.getD false) ∧
         M.output O x (clock.eval x.length) = f x := by
   obtain ⟨Q, Γ, hQ, hΓ, hDec, P, p, hpure, hP⟩ := polynomial_transducer_normal_form hcpu
   letI : Fintype Q := hQ
   letI : Fintype Γ := hΓ
   letI : DecidableEq Γ := hDec
   let D := OracleDriver.program P
   obtain ⟨M, hM⟩ := finite_control_compilation D
   refine ⟨M, ?_⟩
   intro O f T B htrace
   let c : Polynomial ℕ := (T+2)*(p.comp B+5*B+18)+2*Polynomial.X+8
   let clock : Polynomial ℕ := 3*c+1
   refine ⟨clock, fun x => ?_⟩
   obtain ⟨steps, hsteps, ht⟩ := htrace x
   let a := 2*x.length+8
   let d := (D.step O)^[a] (D.initial x)
   have hd : d.core = FamilyContinuation.embed false (P.coreInitial (OracleDriver.shifted x)) := by
     exact OracleDriver.initial_full_run P O x
   have hb : d.qh ≤ d.qhi := D.qh_bound_run O x a
   obtain ⟨u, hu, hr⟩ := OracleDriver.bounded_run P hpure cpu p hP O (B.eval x.length)
     (OracleDriver.shifted x) (f x) steps ht d hd hb
   have htime : a+u ≤ c.eval x.length := by
     have hm := Nat.mul_le_mul_right (OracleDriver.unitTime p (B.eval x.length)) (Nat.add_le_add_right hsteps 2)
     have hu' := hu.trans hm
     simpa [c, a, OracleDriver.unitTime, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
       Nat.add_le_add_left hu' a
   have hr' : ((D.step O)^[a+u] (D.initial x)).core = normalCore ((f x).head?.getD false) (f x) := by
     rw [D.run_add]
     exact hr
   have hs : ((D.step O)^[a+u] (D.initial x)).state = .inl ((f x).head?.getD false) := congrArg Core.state hr'
   have hfixed : D.step O ((D.step O)^[a+u] (D.initial x)) = (D.step O)^[a+u] (D.initial x) := by
     simp only [Program.step, hs]
   have hstable : (D.step O)^[c.eval x.length] (D.initial x) = (D.step O)^[a+u] (D.initial x) := by
     rw [← Nat.add_sub_of_le htime, Nat.add_comm (a+u), Function.iterate_add_apply]
     exact Function.iterate_fixed hfixed _
   have hcore : ((D.step O)^[c.eval x.length] (D.initial x)).core = normalCore ((f x).head?.getD false) (f x) := by
     rw [hstable, hr']
   have hstate := congrArg Core.state hcore
   have hwork := congrArg Core.work hcore
   have hword := readWord_of_upper ((D.step O)^[c.eval x.length] (D.initial x)) (f x)
     (D.work_upper_run O x _) hwork
   have hcompiled := hM O x (c.eval x.length) ((f x).head?.getD false) hstate
   constructor
   · simpa [clock] using hcompiled.1
   · simpa [clock, hword] using hcompiled.2

end StudentTeacher976.Adaptivity

open QAdvFew.PoQOracle QAdvFew.PoQOracle.OTM.FiniteControl Turing.MultiTapeTM StudentTeacher976.Adaptivity

theorem solution (cpu : Word → Word)
     (hcpu : ComputableInPolyTime cpu encBits encBits) :
     ∃ M : OTM, ∀ (O : Oracle) (f : Word → Word) (T B : Polynomial ℕ),
       (∀ x : Word, ∃ steps ≤ T.eval x.length,
         OracleDriver.Trace cpu O (B.eval x.length) (OracleDriver.shifted x) (f x) steps) →
       ∃ clock : Polynomial ℕ, ∀ x : Word,
         M.result O x (clock.eval x.length) = some ((f x).head?.getD false) ∧
         M.output O x (clock.eval x.length) = f x := by
  exact StudentTeacher976.Adaptivity.oracle_protocol_machine cpu hcpu

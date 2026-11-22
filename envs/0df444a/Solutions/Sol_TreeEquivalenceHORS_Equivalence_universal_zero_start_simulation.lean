-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.universal_zero_start_simulation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T19:00:44.572333+00:00
-- url     : https://prove2.me/submissions/25eaf1f9-4c7a-408e-a024-7a40e925508d

/-
Adapted from typh's accepted Prove2Me proof of DistLTLSynth.Char.section_3_2_minsky,
submission 7bdcd522-de20-4ff2-8c23-66c7e4f87fd6, published 2026-11-18.
Original proof and this adaptation are licensed under the Apache License, Version 2.0.
The source program now takes an encoded program/input pair. The final conversion to CMCode
and the undecidability corollary have been omitted.
-/
import Mathlib
import Definitions.Def_DistLTLSynth_Char_CounterMachine
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Machines


namespace DistLTLSynth.Char.Minsky

open DistLTLSynth.Char Turing StateTransition Relation

/-! ### Counter machines as partial step functions -/

section Ostep

variable {Q : Type} {k : ℕ}

open Classical in
noncomputable def ostep (M : CounterMachine Q k) (c : Config Q k) : Option (Config Q k) :=
  if c.state ∈ M.halting then none else some (M.step c)

theorem ostep_of_not {M : CounterMachine Q k} {c : Config Q k} (h : c.state ∉ M.halting) :
    ostep M c = some (M.step c) := by
  simp [ostep, h]

theorem ostep_of_mem {M : CounterMachine Q k} {c : Config Q k} (h : c.state ∈ M.halting) :
    ostep M c = none := by
  simp [ostep, h]

theorem r1 {M : CounterMachine Q k} {c c' : Config Q k} (hn : c.state ∉ M.halting)
    (hs : M.step c = c') : Reaches₁ (ostep M) c c' :=
  TransGen.single (by rw [ostep_of_not hn, hs]; rfl)

theorem step_inc {M : CounterMachine Q k} {st q' : Q} {i : Fin k} (h : M.instr st = .inc i q')
    (c : Fin k → ℕ) : M.step ⟨st, c⟩ = ⟨q', Function.update c i (c i + 1)⟩ := by
  simp [CounterMachine.step, h]

theorem step_dec_zero {M : CounterMachine Q k} {st q' q'' : Q} {i : Fin k}
    (h : M.instr st = .dec i q' q'') (c : Fin k → ℕ) (hc : c i = 0) :
    M.step ⟨st, c⟩ = ⟨q', c⟩ := by
  simp [CounterMachine.step, h, hc]

theorem step_dec_pos {M : CounterMachine Q k} {st q' q'' : Q} {i : Fin k}
    (h : M.instr st = .dec i q' q'') (c : Fin k → ℕ) (x : ℕ) (hc : c i = x + 1) :
    M.step ⟨st, c⟩ = ⟨q'', Function.update c i x⟩ := by
  simp [CounterMachine.step, h, hc]

theorem halts_iff (M : CounterMachine Q k) :
    M.Halts ↔ (eval (ostep M) ⟨M.init, fun _ => 0⟩).Dom := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    have hex : ∃ t, (M.run t).state ∈ M.halting := ⟨t, ht⟩
    have hreach : ∀ s ≤ Nat.find hex, Reaches (ostep M) ⟨M.init, fun _ => 0⟩ (M.run s) := by
      intro s hs
      induction s with
      | zero => exact ReflTransGen.refl
      | succ s ih =>
        refine (ih (by omega)).tail ?_
        have : (M.run s).state ∉ M.halting := Nat.find_min hex (by omega)
        show M.run (s + 1) ∈ ostep M (M.run s)
        rw [ostep_of_not this]
        rfl
    exact Part.dom_iff_mem.2 ⟨_, mem_eval.2 ⟨hreach _ le_rfl, ostep_of_mem (Nat.find_spec hex)⟩⟩
  · intro h
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 h
    obtain ⟨hr, hn⟩ := mem_eval.1 hb
    have : ∀ b, Reaches (ostep M) ⟨M.init, fun _ => 0⟩ b → ∃ t, M.run t = b := by
      intro b hb
      induction hb with
      | refl => exact ⟨0, rfl⟩
      | tail _ hbc ih =>
        obtain ⟨t, rfl⟩ := ih
        refine ⟨t + 1, ?_⟩
        unfold ostep at hbc
        split_ifs at hbc
        · cases hbc
        · exact Option.some_injective _ (Option.mem_def.1 hbc)
    obtain ⟨t, rfl⟩ := this b hr
    refine ⟨t, ?_⟩
    by_contra hc
    rw [ostep_of_not hc] at hn
    cases hn

end Ostep

/-! ### Binary stacks -/

section Stacks

def numL : List Bool → ℕ
  | [] => 0
  | b :: l => 2 * numL l + b.toNat

theorem numL_replicate (i : ℕ) : numL (List.replicate i false) = 0 := by
  induction i with
  | zero => rfl
  | succ i ih => simp [List.replicate_succ, numL, ih]

theorem numL_append_false (l : List Bool) (i : ℕ) :
    numL (l ++ List.replicate i false) = numL l := by
  induction l with
  | nil => simpa [numL] using numL_replicate i
  | cons b l ih => simp [numL, ih]

def numLB (L : ListBlank Bool) : ℕ :=
  L.liftOn numL (by rintro a _ ⟨i, rfl⟩; exact (numL_append_false a i).symm)

theorem numLB_mk (l : List Bool) : numLB (ListBlank.mk l) = numL l := rfl

theorem numLB_cons (b : Bool) (L : ListBlank Bool) : numLB (L.cons b) = 2 * numLB L + b.toNat := by
  refine L.induction_on fun l => ?_
  rw [ListBlank.cons_mk]
  rfl

theorem numLB_head_tail (L : ListBlank Bool) : numLB L = 2 * numLB L.tail + L.head.toNat := by
  conv_lhs => rw [← ListBlank.cons_head_tail L]
  rw [numLB_cons]

theorem numLB_tail (L : ListBlank Bool) : numLB L.tail = numLB L / 2 := by
  have := numLB_head_tail L
  cases h : L.head <;> simp only [h, Bool.toNat_false, Bool.toNat_true] at this <;> omega

theorem numLB_head (L : ListBlank Bool) : L.head = (numLB L % 2 == 1) := by
  have := numLB_head_tail L
  cases h : L.head <;> simp only [h, Bool.toNat_false, Bool.toNat_true] at this
  · rw [eq_comm, beq_eq_false_iff_ne]; omega
  · rw [eq_comm, beq_iff_eq]; omega

end Stacks

/-! ### `TM0` over `Bool` on three counters -/

section TM0toCM3

inductive Tag
  | main | pushA | pushA2 | pushA3 | pushInc | pushB | pushB2 | popA | popInc | popB | popB2

instance : DecidableEq Tag := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

instance : Fintype Tag :=
  ⟨{.main, .pushA, .pushA2, .pushA3, .pushInc, .pushB, .pushB2, .popA, .popInc, .popB, .popB2},
    by intro x; cases x <;> simp⟩

def srcI (d : Bool) : Fin 3 := if d then 0 else 1

def tgtI (d : Bool) : Fin 3 := if d then 1 else 0

/-- Counters for a transfer in direction `d`: source stack `s`, target stack `g`, scratch `t`.
Counter `0` is the left stack and counter `1` the right stack. -/
def cs (d : Bool) (s g t : ℕ) : Fin 3 → ℕ := if d then ![s, g, t] else ![g, s, t]

@[simp] theorem cs_src (d : Bool) (s g t : ℕ) : cs d s g t (srcI d) = s := by
  cases d <;> rfl
@[simp] theorem cs_tgt (d : Bool) (s g t : ℕ) : cs d s g t (tgtI d) = g := by
  cases d <;> rfl
@[simp] theorem cs_two (d : Bool) (s g t : ℕ) : cs d s g t 2 = t := by
  cases d <;> rfl
@[simp] theorem upd_src (d : Bool) (s g t x : ℕ) :
    Function.update (cs d s g t) (srcI d) x = cs d x g t := by
  cases d <;> funext i <;> fin_cases i <;> rfl
@[simp] theorem upd_tgt (d : Bool) (s g t x : ℕ) :
    Function.update (cs d s g t) (tgtI d) x = cs d s x t := by
  cases d <;> funext i <;> fin_cases i <;> rfl
@[simp] theorem upd_two (d : Bool) (s g t x : ℕ) :
    Function.update (cs d s g t) 2 x = cs d s g x := by
  cases d <;> funext i <;> fin_cases i <;> rfl
theorem cs_false (s g t : ℕ) : cs false s g t = cs true g s t := by
  funext i; fin_cases i <;> rfl

def dirB : Dir → Bool
  | .left => false
  | .right => true

variable {Λ : Type} [Inhabited Λ] (M : TM0.Machine Bool Λ) (S : Finset Λ) (h0 : default ∈ S)

open Classical in
noncomputable def lab (q : Λ) : {q // q ∈ S} := if h : q ∈ S then ⟨q, h⟩ else ⟨default, h0⟩

theorem lab_of_mem {q : Λ} (h : q ∈ S) : lab S h0 q = ⟨q, h⟩ := by
  simp [lab, h]

abbrev S3 := Tag × {q // q ∈ S} × Bool × Bool

noncomputable def instr3 : S3 S → Instr (S3 S) 3
  | (.main, q, h, _) =>
    match M q.1 h with
    | none => .dec 2 (.main, q, h, false) (.main, q, h, false)
    | some (q', .write a) => .dec 2 (.main, lab S h0 q', a, false) (.main, lab S h0 q', a, false)
    | some (q', .move d) =>
      .dec 2 (.pushA, lab S h0 q', dirB d, h) (.pushA, lab S h0 q', dirB d, h)
  | (.pushA, q, d, b) =>
    .dec (srcI d) (if b then (.pushInc, q, d, b) else (.pushB, q, d, false)) (.pushA2, q, d, b)
  | (.pushA2, q, d, b) => .inc 2 (.pushA3, q, d, b)
  | (.pushA3, q, d, b) => .inc 2 (.pushA, q, d, b)
  | (.pushInc, q, d, _) => .inc (srcI d) (.pushB, q, d, false)
  | (.pushB, q, d, _) => .dec 2 (.popA, q, d, false) (.pushB2, q, d, false)
  | (.pushB2, q, d, _) => .inc (srcI d) (.pushB, q, d, false)
  | (.popA, q, d, p) =>
    .dec (tgtI d) (.popB, q, d, p) (if p then (.popInc, q, d, false) else (.popA, q, d, true))
  | (.popInc, q, d, _) => .inc 2 (.popA, q, d, false)
  | (.popB, q, d, p) => .dec 2 (.main, q, p, false) (.popB2, q, d, p)
  | (.popB2, q, d, p) => .inc (tgtI d) (.popB, q, d, p)

noncomputable def M3 : CounterMachine (S3 S) 3 where
  init := (.popA, ⟨default, h0⟩, true, false)
  halting := {s | s.1 = .main ∧ M s.2.1.1 s.2.2.1 = none}
  instr := instr3 M S h0

variable {M S h0}

theorem nh {s : S3 S} (h : s.1 ≠ .main) : s ∉ (M3 M S h0).halting := fun hs => h hs.1

theorem pushA_loop (q : {q // q ∈ S}) (d b : Bool) (g : ℕ) :
    ∀ x y, Reaches (ostep (M3 M S h0)) ⟨(.pushA, q, d, b), cs d x g y⟩
      ⟨(.pushA, q, d, b), cs d 0 g (y + 2 * x)⟩
  | 0, y => by rw [mul_zero, add_zero]; exact ReflTransGen.refl
  | x + 1, y => by
    have h1 : Reaches₁ (ostep (M3 M S h0)) ⟨(.pushA, q, d, b), cs d (x + 1) g y⟩
        ⟨(.pushA2, q, d, b), cs d x g y⟩ :=
      r1 (nh (by simp)) (by rw [step_dec_pos (by rfl) _ x (by simp)]; simp)
    have h2 : Reaches₁ (ostep (M3 M S h0)) ⟨(.pushA2, q, d, b), cs d x g y⟩
        ⟨(.pushA3, q, d, b), cs d x g (y + 1)⟩ :=
      r1 (nh (by simp)) (by rw [step_inc (by rfl)]; simp)
    have h3 : Reaches₁ (ostep (M3 M S h0)) ⟨(.pushA3, q, d, b), cs d x g (y + 1)⟩
        ⟨(.pushA, q, d, b), cs d x g (y + 2)⟩ :=
      r1 (nh (by simp)) (by rw [step_inc (by rfl)]; simp)
    have h4 := pushA_loop q d b g x (y + 2)
    rw [show y + 2 + 2 * x = y + 2 * (x + 1) by ring] at h4
    exact (h1.to_reflTransGen.trans (h2.to_reflTransGen.trans h3.to_reflTransGen)).trans h4

theorem pushB_loop (q : {q // q ∈ S}) (d : Bool) (g : ℕ) :
    ∀ s y, Reaches (ostep (M3 M S h0)) ⟨(.pushB, q, d, false), cs d s g y⟩
      ⟨(.pushB, q, d, false), cs d (s + y) g 0⟩
  | s, 0 => by rw [add_zero]; exact ReflTransGen.refl
  | s, y + 1 => by
    have h1 : Reaches₁ (ostep (M3 M S h0)) ⟨(.pushB, q, d, false), cs d s g (y + 1)⟩
        ⟨(.pushB2, q, d, false), cs d s g y⟩ :=
      r1 (nh (by simp)) (by rw [step_dec_pos (by rfl) _ y (by simp)]; simp)
    have h2 : Reaches₁ (ostep (M3 M S h0)) ⟨(.pushB2, q, d, false), cs d s g y⟩
        ⟨(.pushB, q, d, false), cs d (s + 1) g y⟩ :=
      r1 (nh (by simp)) (by rw [step_inc (by rfl)]; simp)
    have h3 := pushB_loop q d g (s + 1) y
    rw [show s + 1 + y = s + (y + 1) by ring] at h3
    exact (h1.to_reflTransGen.trans h2.to_reflTransGen).trans h3

theorem popA_loop (q : {q // q ∈ S}) (d : Bool) (s : ℕ) :
    ∀ x p y, ∃ p' y', p.toNat + x + 2 * y = 2 * y' + p'.toNat ∧
      Reaches₁ (ostep (M3 M S h0)) ⟨(.popA, q, d, p), cs d s x y⟩
        ⟨(.popB, q, d, p'), cs d s 0 y'⟩
  | 0, p, y => ⟨p, y, by ring, r1 (nh (by simp)) (by rw [step_dec_zero (by rfl) _ (by simp)])⟩
  | x + 1, true, y => by
    have h1 : Reaches₁ (ostep (M3 M S h0)) ⟨(.popA, q, d, true), cs d s (x + 1) y⟩
        ⟨(.popInc, q, d, false), cs d s x y⟩ :=
      r1 (nh (by simp)) (by rw [step_dec_pos (by rfl) _ x (by simp)]; simp)
    have h2 : Reaches₁ (ostep (M3 M S h0)) ⟨(.popInc, q, d, false), cs d s x y⟩
        ⟨(.popA, q, d, false), cs d s x (y + 1)⟩ :=
      r1 (nh (by simp)) (by rw [step_inc (by rfl)]; simp)
    obtain ⟨p', y', he, h3⟩ := popA_loop q d s x false (y + 1)
    exact ⟨p', y', by simp at he ⊢; omega, h1.trans (h2.trans h3)⟩
  | x + 1, false, y => by
    have h1 : Reaches₁ (ostep (M3 M S h0)) ⟨(.popA, q, d, false), cs d s (x + 1) y⟩
        ⟨(.popA, q, d, true), cs d s x y⟩ :=
      r1 (nh (by simp)) (by rw [step_dec_pos (by rfl) _ x (by simp)]; simp)
    obtain ⟨p', y', he, h3⟩ := popA_loop q d s x true y
    exact ⟨p', y', by simp at he ⊢; omega, h1.trans h3⟩

theorem popB_loop (q : {q // q ∈ S}) (d p : Bool) (s : ℕ) :
    ∀ g y, Reaches₁ (ostep (M3 M S h0)) ⟨(.popB, q, d, p), cs d s g y⟩
      ⟨(.main, q, p, false), cs d s (g + y) 0⟩
  | g, 0 => r1 (nh (by simp)) (by rw [step_dec_zero (by rfl) _ (by simp)]; rfl)
  | g, y + 1 => by
    have h1 : Reaches₁ (ostep (M3 M S h0)) ⟨(.popB, q, d, p), cs d s g (y + 1)⟩
        ⟨(.popB2, q, d, p), cs d s g y⟩ :=
      r1 (nh (by simp)) (by rw [step_dec_pos (by rfl) _ y (by simp)]; simp)
    have h2 : Reaches₁ (ostep (M3 M S h0)) ⟨(.popB2, q, d, p), cs d s g y⟩
        ⟨(.popB, q, d, p), cs d s (g + 1) y⟩ :=
      r1 (nh (by simp)) (by rw [step_inc (by rfl)]; simp)
    have h3 := popB_loop q d p s (g + 1) y
    rw [show g + 1 + y = g + (y + 1) by ring] at h3
    exact h1.trans (h2.trans h3)

/-- Popping the target stack into the head and returning to `main`. -/
theorem pop_run (q : {q // q ∈ S}) (d : Bool) (s g : ℕ) :
    Reaches₁ (ostep (M3 M S h0)) ⟨(.popA, q, d, false), cs d s g 0⟩
      ⟨(.main, q, g % 2 == 1, false), cs d s (g / 2) 0⟩ := by
  obtain ⟨p', y', he, h1⟩ := popA_loop (M := M) (h0 := h0) q d s g false 0
  have h2 := popB_loop (M := M) (h0 := h0) q d p' s 0 y'
  simp only [zero_add] at h2
  have hp : p' = (g % 2 == 1) := by cases p' <;> simp at he ⊢ <;> omega
  have hy : y' = g / 2 := by cases p' <;> simp at he <;> omega
  rw [hp, hy] at h1 h2
  exact h1.trans h2

theorem move_run (q : {q // q ∈ S}) (h : Bool) (q' : Λ) (d : Dir)
    (hM : M q.1 h = some (q', .move d)) (s g : ℕ) :
    Reaches₁ (ostep (M3 M S h0)) ⟨(.main, q, h, false), cs (dirB d) s g 0⟩
      ⟨(.main, lab S h0 q', g % 2 == 1, false), cs (dirB d) (2 * s + h.toNat) (g / 2) 0⟩ := by
  have hnm : (Tag.main, q, h, false) ∉ (M3 M S h0).halting := fun hs => by
    simp [M3, hM] at hs
  have h1 : Reaches₁ (ostep (M3 M S h0)) ⟨(.main, q, h, false), cs (dirB d) s g 0⟩
      ⟨(.pushA, lab S h0 q', dirB d, h), cs (dirB d) s g 0⟩ :=
    r1 hnm (by
      rw [step_dec_zero (st := (Tag.main, q, h, false)) (q' := (.pushA, lab S h0 q', dirB d, h))
        (q'' := (.pushA, lab S h0 q', dirB d, h)) (i := 2) (by simp [M3, instr3, hM]) _ (by simp)])
  have h2 := pushA_loop (M := M) (h0 := h0) (lab S h0 q') (dirB d) h g s 0
  have h3 : Reaches (ostep (M3 M S h0)) ⟨(.pushA, lab S h0 q', dirB d, h), cs (dirB d) 0 g (2 * s)⟩
      ⟨(.pushB, lab S h0 q', dirB d, false), cs (dirB d) h.toNat g (2 * s)⟩ := by
    cases h
    · exact (r1 (nh (by simp)) (by rw [step_dec_zero (by rfl) _ (by simp)]; rfl)).to_reflTransGen
    · have a1 : Reaches₁ (ostep (M3 M S h0))
          ⟨(.pushA, lab S h0 q', dirB d, true), cs (dirB d) 0 g (2 * s)⟩
          ⟨(.pushInc, lab S h0 q', dirB d, true), cs (dirB d) 0 g (2 * s)⟩ :=
        r1 (nh (by simp)) (by rw [step_dec_zero (by rfl) _ (by simp)]; rfl)
      have a2 : Reaches₁ (ostep (M3 M S h0))
          ⟨(.pushInc, lab S h0 q', dirB d, true), cs (dirB d) 0 g (2 * s)⟩
          ⟨(.pushB, lab S h0 q', dirB d, false), cs (dirB d) 1 g (2 * s)⟩ :=
        r1 (nh (by simp)) (by rw [step_inc (by rfl)]; simp)
      exact (a1.trans a2).to_reflTransGen
  have h4 := pushB_loop (M := M) (h0 := h0) (lab S h0 q') (dirB d) g h.toNat (2 * s)
  have h5 : Reaches₁ (ostep (M3 M S h0))
      ⟨(.pushB, lab S h0 q', dirB d, false), cs (dirB d) (h.toNat + 2 * s) g 0⟩
      ⟨(.popA, lab S h0 q', dirB d, false), cs (dirB d) (h.toNat + 2 * s) g 0⟩ :=
    r1 (nh (by simp)) (by rw [step_dec_zero (by rfl) _ (by simp)])
  have h6 := pop_run (M := M) (h0 := h0) (lab S h0 q') (dirB d) (h.toNat + 2 * s) g
  rw [show h.toNat + 2 * s = 2 * s + h.toNat by ring] at h6
  rw [show h.toNat + 2 * s = 2 * s + h.toNat by ring] at h4 h5
  simp only [zero_add] at h2
  exact h1.trans_left (h2.trans (h3.trans h4)) |>.trans h5 |>.trans h6

/-- A `TM0` configuration and the counter configuration simulating it. -/
def R3 (c : TM0.Cfg Bool Λ) (c3 : Config (S3 S) 3) : Prop :=
  ∃ h : c.q ∈ S, c3 = ⟨(.main, ⟨c.q, h⟩, c.Tape.head, false),
    cs true (numLB c.Tape.left) (numLB c.Tape.right) 0⟩

theorem tr_respects3 (hS : TM0.Supports M ↑S) :
    Respects (TM0.step M) (ostep (M3 M S h0)) R3 := by
  rintro ⟨q, T⟩ c3 ⟨hq, rfl⟩
  obtain ⟨a, L, R⟩ := T
  simp only [TM0.step]
  cases hM : M q a with
  | none =>
    simp only [Option.map_none]
    exact ostep_of_mem ⟨rfl, hM⟩
  | some r =>
    obtain ⟨q', st⟩ := r
    have hq' : q' ∈ S := hS.2 hM hq
    simp only [Option.map_some]
    cases st with
    | write b =>
      refine ⟨_, ⟨hq', rfl⟩, r1 (fun hs => by simp [M3, hM] at hs) ?_⟩
      rw [step_dec_zero (st := (Tag.main, ⟨q, hq⟩, a, false))
        (q' := (.main, lab S h0 q', b, false)) (q'' := (.main, lab S h0 q', b, false)) (i := 2)
        (by simp [M3, instr3, hM]) _ (by simp), lab_of_mem S h0 hq']
      rfl
    | move d =>
      refine ⟨_, ⟨hq', rfl⟩, ?_⟩
      cases d
      · have := move_run (M := M) (h0 := h0) ⟨q, hq⟩ a q' .left hM (numLB R) (numLB L)
        rw [lab_of_mem S h0 hq'] at this
        simp only [dirB, cs_false] at this
        show Reaches₁ _ _ (⟨(.main, ⟨q', hq'⟩, L.head, false),
          cs true (numLB L.tail) (numLB (R.cons a)) 0⟩ : Config (S3 S) 3)
        rw [numLB_head L, numLB_tail, numLB_cons]
        exact this
      · have := move_run (M := M) (h0 := h0) ⟨q, hq⟩ a q' .right hM (numLB L) (numLB R)
        rw [lab_of_mem S h0 hq'] at this
        simp only [dirB] at this
        show Reaches₁ _ _ (⟨(.main, ⟨q', hq'⟩, R.head, false),
          cs true (numLB (L.cons a)) (numLB R.tail) 0⟩ : Config (S3 S) 3)
        rw [numLB_head R, numLB_tail, numLB_cons]
        exact this

theorem tm0_dom_iff3 (hS : TM0.Supports M ↑S) (w : List Bool) :
    (eval (TM0.step M) (TM0.init w)).Dom ↔
      (eval (ostep (M3 M S h0)) ⟨(M3 M S h0).init, cs true 0 (numL w) 0⟩).Dom := by
  have hpop := pop_run (M := M) (h0 := h0) ⟨default, h0⟩ true 0 (numL w)
  rw [show (M3 M S h0).init = (.popA, ⟨default, h0⟩, true, false) from rfl,
    reaches_eval hpop.to_reflTransGen]
  refine (tr_eval_dom (tr_respects3 (h0 := h0) hS) ⟨(show (TM0.init w : TM0.Cfg Bool Λ).q ∈ S from h0), ?_⟩).symm
  simp only [TM0.init, Tape.mk₁, Tape.mk₂, Tape.mk', numLB_mk, numL]
  congr 2
  · rw [numLB_head, numLB_mk]
  · rw [numLB_tail, numLB_mk]

end TM0toCM3


/-! ### Three counters on two (`2^a·3^b·5^c`) -/

section CM3toCM2

def pr : Fin 3 → ℕ := ![2, 3, 5]

theorem pr_pos (i : Fin 3) : 0 < pr i := by fin_cases i <;> decide

theorem pr_le (i : Fin 3) : pr i ≤ 5 := by fin_cases i <;> decide

def enc (c : Fin 3 → ℕ) : ℕ := 2 ^ c 0 * 3 ^ c 1 * 5 ^ c 2

theorem enc_inc (c : Fin 3 → ℕ) (i : Fin 3) :
    enc (Function.update c i (c i + 1)) = pr i * enc c := by
  fin_cases i <;> simp [enc, pr, Function.update, pow_succ] <;> ring

theorem enc_dec (c : Fin 3 → ℕ) (i : Fin 3) (x : ℕ) (h : c i = x + 1) :
    enc c = pr i * enc (Function.update c i x) := by
  have := enc_inc (Function.update c i x) i
  rw [Function.update_self, Function.update_idem, ← h, Function.update_eq_self] at this
  exact this

theorem enc_not_dvd (c : Fin 3 → ℕ) (i : Fin 3) (h : c i = 0) : ¬ pr i ∣ enc c := by
  intro hd
  fin_cases i <;> simp [enc, pr] at hd h <;> simp only [h, pow_zero, one_mul, mul_one] at hd
  · have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.mul_right (Nat.Coprime.pow_right (c 1)
      (by norm_num : Nat.Coprime 2 3)) (Nat.Coprime.pow_right (c 2) (by norm_num : Nat.Coprime 2 5))) hd
    norm_num at this
  · have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.mul_right (Nat.Coprime.pow_right (c 0)
      (by norm_num : Nat.Coprime 3 2)) (Nat.Coprime.pow_right (c 2) (by norm_num : Nat.Coprime 3 5))) hd
    norm_num at this
  · have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.mul_right (Nat.Coprime.pow_right (c 0)
      (by norm_num : Nat.Coprime 5 2)) (Nat.Coprime.pow_right (c 1) (by norm_num : Nat.Coprime 5 3))) hd
    norm_num at this

inductive Tag2
  | main | mulA | mulInc | mulB | mulB2 | divA | divInc | restA | restInc | restR

instance : DecidableEq Tag2 := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

instance : Fintype Tag2 :=
  ⟨{.main, .mulA, .mulInc, .mulB, .mulB2, .divA, .divInc, .restA, .restInc, .restR},
    by intro x; cases x <;> simp⟩

variable {Q : Type} (M : CounterMachine Q 3)

abbrev S2 (Q : Type) := Tag2 × Q × Q × Fin 3 × Fin 5 × Fin 5

def mainS (q : Q) : S2 Q := (.main, q, q, 0, 0, 0)
def mulAS (q : Q) (i : Fin 3) : S2 Q := (.mulA, q, q, i, 0, 0)
def mulIncS (q : Q) (i : Fin 3) (j : Fin 5) : S2 Q := (.mulInc, q, q, i, j, 0)
def mulBS (q : Q) : S2 Q := (.mulB, q, q, 0, 0, 0)
def mulB2S (q : Q) : S2 Q := (.mulB2, q, q, 0, 0, 0)
def divAS (q q' : Q) (i : Fin 3) (r : Fin 5) : S2 Q := (.divA, q, q', i, r, 0)
def divIncS (q q' : Q) (i : Fin 3) : S2 Q := (.divInc, q, q', i, 0, 0)
def restAS (q : Q) (i : Fin 3) (r : Fin 5) : S2 Q := (.restA, q, q, i, r, 0)
def restIncS (q : Q) (i : Fin 3) (r j : Fin 5) : S2 Q := (.restInc, q, q, i, r, j)
def restRS (q : Q) (j : Fin 5) : S2 Q := (.restR, q, q, 0, j, 0)

def instr2 : S2 Q → Instr (S2 Q) 2
  | (.main, q, _, _, _, _) =>
    match M.instr q with
    | .inc i q' => .dec 1 (mulAS q' i) (mulAS q' i)
    | .dec i q' q'' => .dec 1 (divAS q' q'' i 0) (divAS q' q'' i 0)
  | (.mulA, q, _, i, _, _) => .dec 0 (mulBS q) (mulIncS q i 0)
  | (.mulInc, q, _, i, j, _) =>
    .inc 1 (if j.val + 1 < pr i then mulIncS q i (j + 1) else mulAS q i)
  | (.mulB, q, _, _, _, _) => .dec 1 (mainS q) (mulB2S q)
  | (.mulB2, q, _, _, _, _) => .inc 0 (mulBS q)
  | (.divA, q, q', i, r, _) =>
    .dec 0 (if r.val = 0 then mulBS q' else restAS q i r)
      (if r.val + 1 < pr i then divAS q q' i (r + 1) else divIncS q q' i)
  | (.divInc, q, q', i, _, _) => .inc 1 (divAS q q' i 0)
  | (.restA, q, _, i, r, _) => .dec 1 (restRS q r) (restIncS q i r 0)
  | (.restInc, q, _, i, r, j) =>
    .inc 0 (if j.val + 1 < pr i then restIncS q i r (j + 1) else restAS q i r)
  | (.restR, q, _, _, j, _) => .inc 0 (if j.val = 1 then mainS q else restRS q (j - 1))

def M2 : CounterMachine (S2 Q) 2 where
  init := mainS M.init
  halting := {s | s.1 = .main ∧ s.2.1 ∈ M.halting}
  instr := instr2 M

variable {M}

def c2 (x y : ℕ) : Fin 2 → ℕ := ![x, y]

@[simp] theorem c2_zero (x y : ℕ) : c2 x y 0 = x := rfl
@[simp] theorem c2_one (x y : ℕ) : c2 x y 1 = y := rfl
@[simp] theorem c2_upd0 (x y z : ℕ) : Function.update (c2 x y) 0 z = c2 z y := by
  funext i; fin_cases i <;> rfl
@[simp] theorem c2_upd1 (x y z : ℕ) : Function.update (c2 x y) 1 z = c2 x z := by
  funext i; fin_cases i <;> rfl

theorem nh2 {s : S2 Q} (h : s.1 ≠ .main) : s ∉ (M2 M).halting := fun hs => h hs.1

theorem fin5_succ (j : Fin 5) (h : j.val + 1 < 5) : (j + 1).val = j.val + 1 := by
  revert h; fin_cases j <;> decide

theorem mulInc_loop (q : Q) (i : Fin 3) (x : ℕ) :
    ∀ n (j : Fin 5) y, j.val + n = pr i → j.val < pr i →
      Reaches₁ (ostep (M2 M)) ⟨mulIncS q i j, c2 x y⟩ ⟨mulAS q i, c2 x (y + n)⟩
  | 0, j, y, h1, h2 => by omega
  | n + 1, j, y, h1, h2 => by
    by_cases hj : j.val + 1 < pr i
    · have a1 : Reaches₁ (ostep (M2 M)) ⟨mulIncS q i j, c2 x y⟩ ⟨mulIncS q i (j + 1), c2 x (y + 1)⟩ :=
        r1 (nh2 (by simp [mulIncS])) (by
          rw [step_inc (i := 1) (q' := mulIncS q i (j + 1)) (by simp [M2, instr2, mulIncS, hj])]; simp)
      have hj5 : (j + 1).val = j.val + 1 := fin5_succ j (by have := pr_le i; omega)
      have a2 := mulInc_loop q i x n (j + 1) (y + 1) (by omega) (by omega)
      rw [show y + 1 + n = y + (n + 1) by ring] at a2
      exact a1.trans a2
    · have hn : n = 0 := by omega
      subst hn
      exact r1 (nh2 (by simp [mulIncS])) (by
        rw [step_inc (i := 1) (q' := mulAS q i) (by simp [M2, instr2, mulIncS, hj])]; simp)

theorem mulA_loop (q : Q) (i : Fin 3) :
    ∀ x y, Reaches (ostep (M2 M)) ⟨mulAS q i, c2 x y⟩ ⟨mulAS q i, c2 0 (y + pr i * x)⟩
  | 0, y => by rw [mul_zero, add_zero]; exact ReflTransGen.refl
  | x + 1, y => by
    have a1 : Reaches₁ (ostep (M2 M)) ⟨mulAS q i, c2 (x + 1) y⟩ ⟨mulIncS q i 0, c2 x y⟩ :=
      r1 (nh2 (by simp [mulAS])) (by rw [step_dec_pos (by rfl) _ x (by simp)]; simp)
    have a2 := mulInc_loop (M := M) q i x (pr i) 0 y (by simp) (pr_pos i)
    have a3 := mulA_loop q i x (y + pr i)
    rw [show y + pr i + pr i * x = y + pr i * (x + 1) by ring] at a3
    exact (a1.trans a2).to_reflTransGen.trans a3

theorem mulB_loop (q : Q) : ∀ y x, Reaches₁ (ostep (M2 M)) ⟨mulBS q, c2 x y⟩ ⟨mainS q, c2 (x + y) 0⟩
  | 0, x => r1 (nh2 (by simp [mulBS])) (by rw [step_dec_zero (by rfl) _ (by simp)]; rfl)
  | y + 1, x => by
    have a1 : Reaches₁ (ostep (M2 M)) ⟨mulBS q, c2 x (y + 1)⟩ ⟨mulB2S q, c2 x y⟩ :=
      r1 (nh2 (by simp [mulBS])) (by rw [step_dec_pos (by rfl) _ y (by simp)]; simp)
    have a2 : Reaches₁ (ostep (M2 M)) ⟨mulB2S q, c2 x y⟩ ⟨mulBS q, c2 (x + 1) y⟩ :=
      r1 (nh2 (by simp [mulB2S])) (by rw [step_inc (by rfl)]; simp)
    have a3 := mulB_loop q y (x + 1)
    rw [show x + 1 + y = x + (y + 1) by ring] at a3
    exact a1.trans (a2.trans a3)

theorem divA_loop (q q' : Q) (i : Fin 3) :
    ∀ x (r : Fin 5) y, r.val < pr i → ∃ r' : Fin 5, ∃ y' : ℕ, r'.val < pr i ∧
      r.val + x + pr i * y = r'.val + pr i * y' ∧
      Reaches (ostep (M2 M)) ⟨divAS q q' i r, c2 x y⟩ ⟨divAS q q' i r', c2 0 y'⟩
  | 0, r, y, hr => ⟨r, y, hr, by ring, ReflTransGen.refl⟩
  | x + 1, r, y, hr => by
    by_cases hj : r.val + 1 < pr i
    · have a1 : Reaches₁ (ostep (M2 M)) ⟨divAS q q' i r, c2 (x + 1) y⟩
          ⟨divAS q q' i (r + 1), c2 x y⟩ :=
        r1 (nh2 (by simp [divAS])) (by
          rw [step_dec_pos (i := 0) (q'' := divAS q q' i (r + 1))
            (q' := if r.val = 0 then mulBS q' else restAS q i r)
            (by simp [M2, instr2, divAS, hj]) _ x (by simp)]; simp)
      have hr5 : (r + 1).val = r.val + 1 := fin5_succ r (by have := pr_le i; omega)
      obtain ⟨r', y', h1, h2, h3⟩ := divA_loop q q' i x (r + 1) y (by omega)
      exact ⟨r', y', h1, by omega, a1.to_reflTransGen.trans h3⟩
    · have a1 : Reaches₁ (ostep (M2 M)) ⟨divAS q q' i r, c2 (x + 1) y⟩
          ⟨divIncS q q' i, c2 x y⟩ :=
        r1 (nh2 (by simp [divAS])) (by
          rw [step_dec_pos (i := 0) (q'' := divIncS q q' i)
            (q' := if r.val = 0 then mulBS q' else restAS q i r)
            (by simp [M2, instr2, divAS, hj]) _ x (by simp)]; simp)
      have a2 : Reaches₁ (ostep (M2 M)) ⟨divIncS q q' i, c2 x y⟩ ⟨divAS q q' i 0, c2 x (y + 1)⟩ :=
        r1 (nh2 (by simp [divIncS])) (by rw [step_inc (by rfl)]; simp)
      obtain ⟨r', y', h1, h2, h3⟩ := divA_loop q q' i x 0 (y + 1) (pr_pos i)
      exact ⟨r', y', h1, by simp at h2; rw [Nat.mul_add] at h2; omega,
        (a1.trans a2).to_reflTransGen.trans h3⟩

theorem restInc_loop (q : Q) (i : Fin 3) (r : Fin 5) (y : ℕ) :
    ∀ n (j : Fin 5) x, j.val + n = pr i → j.val < pr i →
      Reaches₁ (ostep (M2 M)) ⟨restIncS q i r j, c2 x y⟩ ⟨restAS q i r, c2 (x + n) y⟩
  | 0, j, x, h1, h2 => by omega
  | n + 1, j, x, h1, h2 => by
    by_cases hj : j.val + 1 < pr i
    · have a1 : Reaches₁ (ostep (M2 M)) ⟨restIncS q i r j, c2 x y⟩
          ⟨restIncS q i r (j + 1), c2 (x + 1) y⟩ :=
        r1 (nh2 (by simp [restIncS])) (by
          rw [step_inc (i := 0) (q' := restIncS q i r (j + 1)) (by simp [M2, instr2, restIncS, hj])]; simp)
      have hj5 : (j + 1).val = j.val + 1 := fin5_succ j (by have := pr_le i; omega)
      have a2 := restInc_loop q i r y n (j + 1) (x + 1) (by omega) (by omega)
      rw [show x + 1 + n = x + (n + 1) by ring] at a2
      exact a1.trans a2
    · have hn : n = 0 := by omega
      subst hn
      exact r1 (nh2 (by simp [restIncS])) (by
        rw [step_inc (i := 0) (q' := restAS q i r) (by simp [M2, instr2, restIncS, hj])]; simp)

theorem restA_loop (q : Q) (i : Fin 3) (r : Fin 5) :
    ∀ y x, Reaches (ostep (M2 M)) ⟨restAS q i r, c2 x y⟩ ⟨restAS q i r, c2 (x + pr i * y) 0⟩
  | 0, x => by rw [mul_zero, add_zero]; exact ReflTransGen.refl
  | y + 1, x => by
    have a1 : Reaches₁ (ostep (M2 M)) ⟨restAS q i r, c2 x (y + 1)⟩ ⟨restIncS q i r 0, c2 x y⟩ :=
      r1 (nh2 (by simp [restAS])) (by rw [step_dec_pos (by rfl) _ y (by simp)]; simp)
    have a2 := restInc_loop (M := M) q i r y (pr i) 0 x (by simp) (pr_pos i)
    have a3 := restA_loop q i r y (x + pr i)
    rw [show x + pr i + pr i * y = x + pr i * (y + 1) by ring] at a3
    exact (a1.trans a2).to_reflTransGen.trans a3

theorem restR_loop (q : Q) :
    ∀ n (j : Fin 5) x, j.val = n + 1 →
      Reaches₁ (ostep (M2 M)) ⟨restRS q j, c2 x 0⟩ ⟨mainS q, c2 (x + j.val) 0⟩
  | 0, j, x, h => r1 (nh2 (by simp [restRS])) (by
      rw [step_inc (i := 0) (q' := mainS q) (by simp [M2, instr2, restRS, h])]; simp [h])
  | n + 1, j, x, h => by
    have hj : (j - 1).val = n + 1 := by
      rw [Fin.sub_val_of_le (by simp [Fin.le_iff_val_le_val]; omega)]; simp; omega
    have a1 : Reaches₁ (ostep (M2 M)) ⟨restRS q j, c2 x 0⟩ ⟨restRS q (j - 1), c2 (x + 1) 0⟩ :=
      r1 (nh2 (by simp [restRS])) (by
        rw [step_inc (i := 0) (q' := restRS q (j - 1)) (by simp [M2, instr2, restRS, h])]; simp)
    have a2 := restR_loop q n (j - 1) (x + 1) hj
    rw [hj, show x + 1 + (n + 1) = x + (n + 1 + 1) by ring] at a2
    rw [h]
    exact a1.trans a2

def R2 (c : Config Q 3) (d : Config (S2 Q) 2) : Prop :=
  d = ⟨mainS c.state, c2 (enc c.counters) 0⟩

theorem tr_respects2 : Respects (ostep M) (ostep (M2 M)) R2 := by
  classical
  rintro ⟨q, c⟩ _ rfl
  by_cases hq : q ∈ M.halting
  · rw [ostep_of_mem hq]
    exact ostep_of_mem ⟨rfl, hq⟩
  rw [ostep_of_not hq]
  have hmain : mainS q ∉ (M2 M).halting := fun hs => hq hs.2
  cases hI : M.instr q with
  | inc i q' =>
    refine ⟨_, rfl, ?_⟩
    rw [step_inc hI]
    have a1 : Reaches₁ (ostep (M2 M)) ⟨mainS q, c2 (enc c) 0⟩ ⟨mulAS q' i, c2 (enc c) 0⟩ :=
      r1 hmain (by rw [step_dec_zero (i := 1) (q' := mulAS q' i) (q'' := mulAS q' i)
        (by simp [M2, instr2, mainS, hI]) _ (by simp)])
    have a2 := mulA_loop (M := M) q' i (enc c) 0
    have a3 : Reaches₁ (ostep (M2 M)) ⟨mulAS q' i, c2 0 (0 + pr i * enc c)⟩
        ⟨mulBS q', c2 0 (0 + pr i * enc c)⟩ :=
      r1 (nh2 (by simp [mulAS])) (by rw [step_dec_zero (by rfl) _ (by simp)])
    have a4 := mulB_loop (M := M) q' (0 + pr i * enc c) 0
    rw [enc_inc]
    simp only [zero_add] at a2 a3 a4 ⊢
    exact a1.trans_left (a2.trans a3.to_reflTransGen) |>.trans a4
  | dec i q' q'' =>
    have a1 : Reaches₁ (ostep (M2 M)) ⟨mainS q, c2 (enc c) 0⟩ ⟨divAS q' q'' i 0, c2 (enc c) 0⟩ :=
      r1 hmain (by rw [step_dec_zero (i := 1) (q' := divAS q' q'' i 0) (q'' := divAS q' q'' i 0)
        (by simp [M2, instr2, mainS, hI]) _ (by simp)])
    obtain ⟨r', y', hr', he, a2⟩ := divA_loop (M := M) q' q'' i (enc c) 0 0 (pr_pos i)
    simp only [Fin.val_zero, zero_add, mul_zero, add_zero] at he
    have hmod : enc c % pr i = r'.val := by
      rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr']
    have hdiv : enc c / pr i = y' := by
      rw [he, Nat.add_mul_div_left _ _ (pr_pos i), Nat.div_eq_of_lt hr', zero_add]
    rcases hci : c i with _ | x
    · have hr0 : r'.val ≠ 0 := fun h0 =>
        enc_not_dvd c i hci (Nat.dvd_of_mod_eq_zero (hmod.trans h0))
      refine ⟨_, rfl, ?_⟩
      rw [step_dec_zero hI _ hci]
      have a3 : Reaches₁ (ostep (M2 M)) ⟨divAS q' q'' i r', c2 0 y'⟩ ⟨restAS q' i r', c2 0 y'⟩ :=
        r1 (nh2 (by simp [divAS])) (by
          rw [step_dec_zero (i := 0) (q' := restAS q' i r')
            (q'' := if r'.val + 1 < pr i then divAS q' q'' i (r' + 1) else divIncS q' q'' i)
            (by simp [M2, instr2, divAS, hr0]) _ (by simp)])
      have a4 := restA_loop (M := M) q' i r' y' 0
      have a5 : Reaches₁ (ostep (M2 M)) ⟨restAS q' i r', c2 (0 + pr i * y') 0⟩
          ⟨restRS q' r', c2 (0 + pr i * y') 0⟩ :=
        r1 (nh2 (by simp [restAS])) (by rw [step_dec_zero (by rfl) _ (by simp)])
      have a6 := restR_loop (M := M) q' (r'.val - 1) r' (0 + pr i * y') (by omega)
      rw [show 0 + pr i * y' + r'.val = enc c by rw [he]; ring] at a6
      exact a1.trans_left (a2.trans (a3.to_reflTransGen.trans (a4.trans a5.to_reflTransGen)))
        |>.trans a6
    · have hd := enc_dec c i x hci
      have hr0 : r'.val = 0 := by
        rw [← hmod, hd, Nat.mul_mod_right]
      refine ⟨_, rfl, ?_⟩
      rw [step_dec_pos hI _ x hci]
      have a3 : Reaches₁ (ostep (M2 M)) ⟨divAS q' q'' i r', c2 0 y'⟩ ⟨mulBS q'', c2 0 y'⟩ :=
        r1 (nh2 (by simp [divAS])) (by
          rw [step_dec_zero (i := 0) (q' := mulBS q'')
            (q'' := if r'.val + 1 < pr i then divAS q' q'' i (r' + 1) else divIncS q' q'' i)
            (by simp [M2, instr2, divAS, hr0]) _ (by simp)])
      have hy : y' = enc (Function.update c i x) := by
        rw [← hdiv, hd, Nat.mul_div_cancel_left _ (pr_pos i)]
      have a4 := mulB_loop (M := M) q'' y' 0
      rw [zero_add] at a4
      rw [hy] at a2 a3 a4
      exact a1.trans_left (a2.trans a3.to_reflTransGen) |>.trans a4

theorem dom_iff2 (c : Config Q 3) :
    (eval (ostep M) c).Dom ↔ (eval (ostep (M2 M)) ⟨mainS c.state, c2 (enc c.counters) 0⟩).Dom :=
  (tr_eval_dom tr_respects2 rfl).symm

end CM3toCM2


/-! ### An undecidable predicate and a code reading its input in unary -/

section Source

open ToPartrec

def P (n : ℕ) : Part ℕ := Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n.unpair.1) n.unpair.2

theorem P_partrec : Partrec P :=
  Nat.Partrec.Code.eval_part.comp ((Computable.ofNat _).comp (Computable.fst.comp Computable.unpair))
    (Computable.snd.comp Computable.unpair)

theorem some_bind' {α β : Type} (a : α) (f : α →. β) : (Part.some a >>= f) = f a :=
  Part.bind_some a f

theorem pure_bind' {α β : Type} (a : α) (f : α →. β) : (pure a >>= f) = f a :=
  Part.bind_some a f

/-- On `acc :: rest`, stop with `[acc]` if `rest` starts with `0` (or is empty), and otherwise
continue with `acc + 1 :: rest.tail`. -/
def lenBody : Code :=
  Code.comp (Code.case (Code.cons Code.zero Code.head)
      (Code.cons (Code.comp Code.succ Code.zero) (Code.cons (Code.comp Code.succ Code.tail)
        (Code.comp Code.tail (Code.comp Code.tail Code.tail)))))
    (Code.cons (Code.comp Code.head Code.tail) Code.id)

theorem lenBody_zero (acc : ℕ) : lenBody.eval [acc] = pure [0, acc] := by
  simp [lenBody, some_bind', Part.bind_some]

theorem lenBody_succ (acc k : ℕ) :
    lenBody.eval (acc :: 1 :: List.replicate k 1) = pure (1 :: (acc + 1) :: List.replicate k 1) := by
  simp [lenBody, some_bind', Part.bind_some]

theorem lenFix (k : ℕ) : ∀ acc, (Code.fix lenBody).eval (acc :: List.replicate k 1) = pure [acc + k] := by
  induction k with
  | zero =>
    intro acc
    rw [Code.fix_eval, Part.pure_eq_some, Part.eq_some_iff]
    exact PFun.mem_fix_iff.2 (Or.inl (by rw [List.replicate_zero, lenBody_zero]; simp))
  | succ k ih =>
    intro acc
    rw [Code.fix_eval, Part.pure_eq_some, Part.eq_some_iff]
    refine PFun.mem_fix_iff.2 (Or.inr ⟨(acc + 1) :: List.replicate k 1, ?_, ?_⟩)
    · rw [List.replicate_succ, lenBody_succ]
      simp
    · have := ih (acc + 1)
      rw [Code.fix_eval] at this
      rw [this, Part.pure_eq_some, show acc + 1 + k = acc + (k + 1) by ring]
      exact Part.mem_some _

def lenCode : Code := Code.comp (Code.fix lenBody) Code.zero'

theorem lenCode_eval (n : ℕ) : lenCode.eval (List.replicate n 1) = pure [n] := by
  show (pure (0 :: List.replicate n 1) >>= (Code.fix lenBody).eval) = pure [n]
  rw [pure_bind', lenFix, zero_add]

end Source

/-! ### Mathlib's compiler, with halting preserved in both directions -/

section Chain

open PartrecToTM2 ToPartrec

instance instFintypeK' : Fintype K' :=
  ⟨{K'.main, K'.rev, K'.aux, K'.stack}, by intro x; cases x <;> simp⟩

theorem numL_append (a b : List Bool) : numL (a ++ b) = numL a + 2 ^ a.length * numL b := by
  induction a with
  | nil => simp [numL]
  | cons x a ih => simp only [List.cons_append, numL, ih, List.length_cons, pow_succ]; ring

theorem numL_flatMap {α : Type} {m : ℕ} (en : α → List.Vector Bool m) (l : List α) :
    numL (l.flatMap fun a => (en a).toList) =
      l.foldr (fun a acc => numL (en a).toList + 2 ^ m * acc) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, numL_append, ih]

theorem trList_rep_reverse (n : ℕ) :
    (trList (List.replicate n 1)).reverse = (List.replicate n [Γ'.cons, Γ'.bit1]).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, trList, show trNat 1 = [Γ'.bit1] from rfl, List.replicate_succ',
      List.flatten_append, ← ih]
    simp

def Tf (m c b : ℕ) (k : ℕ) : ℕ := Nat.rec 0 (fun _ acc => c + 2 ^ m * (b + 2 ^ m * acc)) k

def Nf (m b0 b1 c b : ℕ) (n : ℕ) : ℕ := Nat.rec b0 (fun k _ => b1 + 2 ^ m * (b + 2 ^ m * Tf m c b k)) n

theorem Tf_primrec (m c b : ℕ) : Primrec (Tf m c b) :=
  Primrec.nat_rec₁ 0 (Primrec.nat_add.comp (Primrec.const c) (Primrec.nat_mul.comp
    (Primrec.const _) (Primrec.nat_add.comp (Primrec.const b) (Primrec.nat_mul.comp
      (Primrec.const _) Primrec.snd))))

theorem Nf_primrec (m b0 b1 c b : ℕ) : Primrec (Nf m b0 b1 c b) :=
  Primrec.nat_rec₁ b0 (Primrec.nat_add.comp (Primrec.const b1) (Primrec.nat_mul.comp
    (Primrec.const _) (Primrec.nat_add.comp (Primrec.const b) (Primrec.nat_mul.comp
      (Primrec.const _) ((Tf_primrec m c b).comp Primrec.fst)))))

theorem foldr_rep {α β : Type} (f : α → ℕ → ℕ) (g : β → α) (x y : β) (k : ℕ) (c b m : ℕ)
    (hx : ∀ acc, f (g x) acc = c + 2 ^ m * acc) (hy : ∀ acc, f (g y) acc = b + 2 ^ m * acc) :
    ((List.replicate k [x, y]).flatten.map g).foldr f 0 = Tf m c b k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, List.map_append, List.foldr_append, ih]
    simp [hx, hy, Tf]

theorem chain : ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (U : CounterMachine Q 2) (u0 : Q)
    (N : ℕ → ℕ), Primrec N ∧ ∀ n, (P n).Dom ↔ (eval (ostep U) ⟨u0, c2 (3 ^ N n) 0⟩).Dom := by
  classical
  obtain ⟨G0, hG0⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.2 P_partrec)
  let G := Code.comp G0 lenCode
  have hG : ∀ n, (G.eval (List.replicate n 1)).Dom ↔ (P n).Dom := by
    intro n
    have h := hG0 (n ::ᵥ List.Vector.nil)
    rw [List.Vector.head_cons] at h
    show ((lenCode.eval (List.replicate n 1)) >>= G0.eval).Dom ↔ _
    rw [lenCode_eval, pure_bind']
    exact (congrArg Part.Dom h).to_iff
  let _ : Inhabited Λ' := ⟨trNormal G Cont'.halt⟩
  obtain ⟨m, en, dec, enc0, encdec⟩ :=
    TM1to1.exists_enc_dec (Γ := TM2to1.Γ' K' (fun _ : K' => Γ'))
  let M1 := TM2to1.tr (K := K') (Γ := fun _ : K' => Γ') (Λ := Λ') (σ := Option Γ') tr
  let M1b := TM1to1.tr en dec M1
  have hS2 : TM2.Supports tr (codeSupp G Cont'.halt) := tr_supports G Cont'.halt
  have hS0 := TM1to0.tr_supports M1b (TM1to1.tr_supports en dec M1 (TM2to1.tr_supports tr hS2))
  let w : List ℕ → List Bool := fun v =>
    (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main (trList v)).flatMap fun a => (en a).toList
  have hdom : ∀ v, (G.eval v).Dom ↔
      (eval (TM0.step (TM1to0.tr M1b)) (TM0.init (w v))).Dom := by
    intro v
    have e2 : (TM2.init K'.main (trList v) : Cfg') = PartrecToTM2.init G v := by
      simp only [TM2.init, PartrecToTM2.init]
      congr
      funext k
      cases k <;> rfl
    have h2 : (eval (TM2.step tr) (TM2.init K'.main (trList v))).Dom ↔ (G.eval v).Dom := by
      rw [e2, PartrecToTM2.tr_eval]
      rfl
    have h1 := StateTransition.tr_eval_dom (TM2to1.tr_respects tr)
      (TM2to1.trCfg_init (Γ := fun _ : K' => Γ') K'.main (trList v))
    have hb := StateTransition.tr_eval_dom (TM1to1.tr_respects dec M1 (enc0 := enc0) encdec)
      (a₁ := TM1.init (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main (trList v))) rfl
    have hinit : TM1to1.trCfg en enc0 (TM1.init (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main
        (trList v)) : TM1.Cfg _ (TM2to1.Λ' K' (fun _ : K' => Γ') Λ' (Option Γ')) (Option Γ')) =
        TM1.init (w v) := by
      simp only [TM1.init, TM1to1.trCfg, Tape.mk₁, Tape.mk₂, TM1to1.trTape_mk', TM1to1.trTape',
        ListBlank.flatMap_mk, Option.map_some]
      rfl
    rw [hinit] at hb
    have h0 := StateTransition.tr_eval_dom (TM1to0.tr_respects M1b) (a₁ := TM1.init (w v)) rfl
    exact h2.symm.trans (h1.symm.trans (hb.symm.trans h0.symm))
  let S0 := TM1to0.trStmts M1b (TM1to1.trSupp M1 (TM2to1.trSupp tr (codeSupp G Cont'.halt)))
  let M3' := M3 (TM1to0.tr M1b) S0 hS0.1
  let β : TM2to1.Γ' K' (fun _ : K' => Γ') → ℕ := fun a => numL (en a).toList
  let τ : Γ' → Bool × (K' → Option Γ') :=
    fun a => (false, Function.update (fun _ => none) K'.main (some a))
  refine ⟨S2 (S3 S0), inferInstance, inferInstance, M2 M3', mainS M3'.init,
    Nf m (β (true, fun _ => none)) (β (true, (τ Γ'.cons).2)) (β (τ Γ'.cons)) (β (τ Γ'.bit1)),
    Nf_primrec _ _ _ _ _, fun n => ?_⟩
  have hN : numL (w (List.replicate n 1)) =
      Nf m (β (true, fun _ => none)) (β (true, (τ Γ'.cons).2)) (β (τ Γ'.cons)) (β (τ Γ'.bit1)) n := by
    simp only [w, TM2to1.trInit, trList_rep_reverse, numL_flatMap]
    cases n with
    | zero =>
      simp only [List.replicate_zero, List.flatten_nil, List.map_nil, List.headI_nil, List.tail_nil,
        List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
      rfl
    | succ k =>
      have key := foldr_rep (α := TM2to1.Γ' K' (fun _ : K' => Γ'))
        (fun a acc => numL (en a).toList + 2 ^ m * acc) τ Γ'.cons Γ'.bit1 k (β (τ Γ'.cons))
        (β (τ Γ'.bit1)) m (fun _ => rfl) (fun _ => rfl)
      rw [List.replicate_succ, List.flatten_cons]
      show numL (en (true, (τ Γ'.cons).2)).toList + 2 ^ m * (numL (en (τ Γ'.bit1)).toList +
        2 ^ m * List.foldr (fun a acc => numL (en a).toList + 2 ^ m * acc) 0
          ((List.replicate k [Γ'.cons, Γ'.bit1]).flatten.map τ)) = _
      rw [key]
      rfl
  have e3 : enc (cs true 0 (numL (w (List.replicate n 1))) 0) = 3 ^ numL (w (List.replicate n 1)) := by
    simp [enc, cs]
  rw [← hG, hdom, tm0_dom_iff3 (h0 := hS0.1) hS0, dom_iff2]
  simp only
  rw [e3, hN]

end Chain

end DistLTLSynth.Char.Minsky

namespace TreeEquivalenceHORS.Equivalence

open StateTransition Relation
open DistLTLSynth.Char (CounterMachine)
open DistLTLSynth.Char.Minsky (ostep)

private def next (M : Machine) (u : ℕ × ℕ × ℕ) : Option (ℕ × ℕ × ℕ) :=
  let (i,a,b) := u
  (M.lookup i).map fun
    | .incA => (i+1,a+1,b)
    | .incB => (i+1,a,b+1)
    | .decA j => if a=0 then (i+1,0,b) else (j,a-1,b)
    | .decB j => if b=0 then (i+1,a,0) else (j,a,b-1)

private theorem next_iff (M : Machine) (u v : ℕ × ℕ × ℕ) : v ∈ next M u ↔ M.Step u v := by
  constructor
  · obtain ⟨i,a,b⟩ := u
    intro h
    cases he : M.lookup i with
    | none => simp [next,he] at h
    | some ins =>
      cases ins with
      | incA =>
        obtain rfl := (by simpa [next,he] using h)
        exact Machine.Step.incA he
      | incB =>
        obtain rfl := (by simpa [next,he] using h)
        exact Machine.Step.incB he
      | decA j =>
        cases a with
        | zero =>
          obtain rfl := (by simpa [next,he] using h)
          exact Machine.Step.decAZero he
        | succ a =>
          obtain rfl := (by simpa [next,he] using h)
          exact Machine.Step.decAPos he
      | decB j =>
        cases b with
        | zero =>
          obtain rfl := (by simpa [next,he] using h)
          exact Machine.Step.decBZero he
        | succ b =>
          obtain rfl := (by simpa [next,he] using h)
          exact Machine.Step.decBPos he
  · intro h
    cases h <;> simp [next, *]

private theorem halts_eval (M : Machine) : M.Halts ↔ (eval (next M) (1,0,0)).Dom := by
  have rel : (fun u v => v ∈ next M u) = M.Step := by funext u v; exact propext (next_iff _ _ _)
  have stop (i a b : ℕ) : next M (i,a,b) = none ↔ ¬ M.Active i := by
    have he : (M.lookup i).isSome ↔ M.Active i := by
      by_cases h : i=0
      · simp [Machine.lookup,Machine.Active,h]
      · simp [Machine.lookup,Machine.Active,h]; omega
    cases eq : M.lookup i <;> simp_all [next]
  rw [Part.dom_iff_mem]
  simp only [mem_eval,Reaches]
  rw [rel]
  exact ⟨fun ⟨i,a,b,reach,h⟩ => ⟨(i,a,b),reach,(stop i a b).mpr h⟩,
    fun ⟨⟨i,a,b⟩,reach,h⟩ => ⟨i,a,b,reach,(stop i a b).mp h⟩⟩

noncomputable section
open Classical

variable {Q : Type} [Fintype Q] (U : CounterMachine Q 2) (u0 : Q)

private def slot (q : Q) := 3 + 3 * (Fintype.equivFin Q q).val
private def dest (q : Q) := if q ∈ U.halting then 0 else slot q

private def block (q : Q) (k : ℕ) : Instr :=
  match U.instr q with
  | .inc i q' => if k=0 then (if i=0 then .incA else .incB)
                  else if k=1 then .incA else .decA (dest U q')
  | .dec i z p => if k=0 then (if i=0 then .decA (dest U p) else .decB (dest U p))
                  else if k=1 then .incA else .decA (dest U z)

private def row (j : ℕ) : Instr :=
  if h : j/3 < Fintype.card Q then block U ((Fintype.equivFin Q).symm ⟨j/3,h⟩) (j%3) else .incA

private def region : Machine := (List.range (3*Fintype.card Q)).map (row U)
private def entry : ℕ := 3 + 3 * Fintype.card Q
private def code (E : ℕ) : Machine :=
  [.incA,.decA (entry (Q := Q))] ++ region U ++ List.replicate E .incA ++ [.incA,.decA (dest U u0)]

private theorem at_block (E : ℕ) (q : Q) (k : ℕ) (hk : k < 3) :
    (code U u0 E).lookup (slot q+k) = some (block U q k) := by
  let j := (Fintype.equivFin Q q).val
  have hj : j < Fintype.card Q := (Fintype.equivFin Q q).isLt
  have lt : 3*j+k < 3*Fintype.card Q := by omega
  have small : (3*j+k)/3 = j := by omega
  have rem : (3*j+k)%3 = k := by omega
  have e : (Fintype.equivFin Q).symm ⟨j,hj⟩ = q := (Fintype.equivFin Q).symm_apply_apply q
  have row_ok : row U (3*j+k) = block U q k := by simp [row,small,rem,hj,e]
  change (code U u0 E).lookup (3+3*j+k) = _
  simp only [Machine.lookup, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and, if_false]
  rw [show 3+3*j+k-1 = 2+(3*j+k) by omega]
  have hr : (region U).length = 3*Fintype.card Q := by simp [region]
  simp only [code,List.append_assoc,List.cons_append,List.nil_append,Nat.add_comm 2 (3*j+k),List.getElem?_cons_succ]
  rw [List.getElem?_append_left (show 3*j+k < (region U).length by omega)]
  simp [region,lt,row_ok]

private def cfg (x : DistLTLSynth.Char.Config Q 2) : ℕ × ℕ × ℕ :=
  (dest U x.state, x.counters 0, x.counters 1)

private theorem oneStep {M : Machine} {u v} (h : M.Step u v) : Reaches₁ (next M) u v :=
  .single ((next_iff _ _ _).mpr h)

private theorem jump {M : Machine} {i j : ℕ} (a b : ℕ)
    (hi : M.lookup i = some .incA) (hj : M.lookup (i+1) = some (.decA j)) :
    Reaches₁ (next M) (i,a,b) (j,a,b) :=
  (oneStep (Machine.Step.incA (a := a) (b := b) hi)).trans (oneStep (Machine.Step.decAPos hj))

private theorem simulation (E : ℕ) :
    Respects (ostep U) (next (code U u0 E)) (fun x y => y = cfg U x) := by
  rintro ⟨q,c⟩ _ rfl
  by_cases hn : q ∈ U.halting
  · simp [ostep,hn,cfg,dest,next,Machine.lookup]
  · rw [DistLTLSynth.Char.Minsky.ostep_of_not (show (DistLTLSynth.Char.Config.mk q c).state ∉ U.halting from hn)]
    refine ⟨_,rfl,?_⟩
    have h₀ := at_block U u0 E q 0 (by decide)
    have h₁ := at_block U u0 E q 1 (by decide)
    have h₂ := at_block U u0 E q 2 (by decide)
    simp only [Nat.add_zero] at h₀
    cases h : U.instr q with
    | inc i r =>
      fin_cases i
      · simp [block,h] at h₀ h₁ h₂
        have s := (oneStep (Machine.Step.incA (a := c 0) (b := c 1) h₀)).trans
          (jump (c 0+1) (c 1) h₁ h₂)
        simpa [Reaches₁,cfg, dest, hn, CounterMachine.step,h] using s
      · simp [block,h] at h₀ h₁ h₂
        have s := (oneStep (Machine.Step.incB (a := c 0) (b := c 1) h₀)).trans
          (jump (c 0) (c 1+1) h₁ h₂)
        simpa [Reaches₁,cfg, dest, hn, CounterMachine.step,h] using s
    | dec i z p =>
      fin_cases i
      · simp [block,h] at h₀ h₁ h₂
        cases hc : c 0 with
        | zero =>
          have s := (oneStep (Machine.Step.decAZero (b := c 1) h₀)).trans
            (jump 0 (c 1) h₁ h₂)
          simpa [Reaches₁,cfg,dest,hn,CounterMachine.step,h,hc] using s
        | succ a =>
          have s := oneStep (Machine.Step.decAPos (a := a) (b := c 1) h₀)
          simpa [Reaches₁,cfg,dest,hn,CounterMachine.step,h,hc] using s
      · simp [block,h] at h₀ h₁ h₂
        cases hc : c 1 with
        | zero =>
          have s := (oneStep (Machine.Step.decBZero (a := c 0) h₀)).trans
            (jump (c 0) 0 h₁ h₂)
          simpa [Reaches₁,cfg,dest,hn,CounterMachine.step,h,hc] using s
        | succ b =>
          have s := oneStep (Machine.Step.decBPos (a := c 0) (b := b) h₀)
          simpa [Reaches₁,cfg,dest,hn,CounterMachine.step,h,hc] using s

private theorem at_init (E : ℕ) :
    (code U u0 E).lookup 1 = some .incA ∧ (code U u0 E).lookup 2 = some (.decA (entry (Q := Q))) := by
  simp [code, Machine.lookup]

private theorem at_loader (E i : ℕ) (hi : i ≤ E+1) :
    (code U u0 E).lookup (entry (Q := Q)+i) =
      if i≤E then some .incA else some (.decA (dest U u0)) := by
  have hr : (region U).length = 3*Fintype.card Q := by simp [region]
  let pre : Machine := [.incA,.decA (entry (Q := Q))] ++ region U
  have lp : pre.length = 2 + 3*Fintype.card Q := by simp [pre,hr]; omega
  have hz : entry (Q := Q)+i ≠ 0 := by unfold entry; omega
  simp only [Machine.lookup,hz,if_false]
  change ((pre ++ List.replicate E .incA) ++ [.incA,.decA (dest U u0)])[entry (Q := Q)+i-1]? = _
  rw [List.append_assoc, List.getElem?_append_right (by unfold entry; omega)]
  rw [show entry (Q := Q)+i-1-pre.length = i by unfold entry; omega]
  by_cases h : i<E
  · rw [List.getElem?_append_left (by simpa using h)]
    simp [h, h.le]
  · rw [List.getElem?_append_right (by simp; omega)]
    rcases (show i=E ∨ i=E+1 by omega) with rfl | rfl <;> simp

private theorem initialized (E : ℕ) : Reaches (next (code U u0 E)) (1,0,0)
    (cfg U ⟨u0, DistLTLSynth.Char.Minsky.c2 E 0⟩) := by
  have start : Reaches (next (code U u0 E)) (1,0,0) (entry (Q := Q),0,0) := (jump 0 0 (at_init U u0 E).1 (at_init U u0 E).2).to_reflTransGen
  have moves (i : ℕ) (hi : i≤E) : Reaches (next (code U u0 E)) (1,0,0) (entry (Q := Q)+i,i,0) := by
    induction i with
    | zero => simpa only [Nat.add_zero] using start
    | succ i ih =>
      have hx := at_loader U u0 E i (by omega)
      rw [if_pos (by omega)] at hx
      exact (ih (by omega)).tail ((next_iff _ _ _).mpr (Machine.Step.incA hx))
  have inc := at_loader U u0 E E (by omega)
  have dec := at_loader U u0 E (E+1) (by omega)
  simp only [le_refl,if_true] at inc
  rw [if_neg (by omega)] at dec
  exact (moves E le_rfl).trans (jump E 0 inc dec).to_reflTransGen

theorem fixed_machine_code_halts (E : ℕ) :
    (code U u0 E).Halts ↔ (eval (ostep U) ⟨u0, DistLTLSynth.Char.Minsky.c2 E 0⟩).Dom := by
  rw [halts_eval, reaches_eval (initialized U u0 E)]
  exact tr_eval_dom (simulation U u0 E) rfl

private theorem list_code {α : Type} [Encodable α] (l : List α) :
    Encodable.encode (l.map Encodable.encode) = Encodable.encode l := by
  induction l <;> simp [*]

private theorem code_computable : Computable (fun E => Encodable.encode (code U u0 E)) := by
  let pre : Machine := [.incA,.decA (entry (Q := Q))] ++ region U
  let post : Machine := [.incA,.decA (dest U u0)]
  have rep : Primrec fun n : ℕ => List.replicate n (Encodable.encode Instr.incA) := by
    simpa using (Primrec.list_map Primrec.list_range (Primrec₂.const (Encodable.encode Instr.incA)))
  have h := Primrec.list_append.comp
    (Primrec.list_append.comp (Primrec.const (pre.map Encodable.encode)) rep)
    (Primrec.const (post.map Encodable.encode))
  refine ((Primrec.encode.comp h).to_comp).of_eq fun E => ?_
  rw [← list_code (code U u0 E)]
  simp [code,pre,post,List.map_append]


/-- The mission's four instructions and zero initialization simulate universal partial evaluation. -/

private theorem proved_here:
    ∃ m : ℕ → Machine, Computable (fun n => Encodable.encode (m n)) ∧
      ∀ n, (¬ (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n.unpair.1) n.unpair.2).Dom) ↔
        ¬ (m n).Halts := by
  obtain ⟨Q, fq, _, U, u0, N, hN, hP⟩ := DistLTLSynth.Char.Minsky.chain
  let : Fintype Q := fq
  refine ⟨fun n => code U u0 (3 ^ N n), (code_computable U u0).comp
    (((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 3) hN).to_comp), fun n => ?_⟩
  exact not_congr ((hP n).trans (fixed_machine_code_halts U u0 (3 ^ N n)).symm)
end
end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution:
    ∃ m : ℕ → Machine, Computable (fun n => Encodable.encode (m n)) ∧
      ∀ n, (¬ (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n.unpair.1) n.unpair.2).Dom) ↔
        ¬ (m n).Halts := proved_here

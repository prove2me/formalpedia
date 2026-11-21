-- Prove2me | solution 1 for OnlineTransportation1195.Main.weighted_tree_walk_deadlines
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T21:06:33.382107+00:00
-- url     : https://prove2.me/submissions/0d420166-8f34-4884-9e59-5216f3e52361

import Definitions.Def_OnlineTransportation1195_Main_Computation
import Theorems.Thm_OnlineTransportation1195_Main_strict_red_weight_budget
import Theorems.Thm_OnlineTransportation1195_Main_root_patch_normalization_iff
import Theorems.Thm_OnlineTransportation1195_Main_detour_budget_inequality
section
/-!
A structured language with an exact-cost big-step semantics, compiled to `SmaleNinth.RAMProgram`,
with the compiler proved correct (q419; copied from RAMBlueprint + RAMPartF).
-/

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace OnlineTransportation1195.Dev.RL
open OnlineTransportation1195.Main SmaleNinth

/-! ## The structured language -/

structure Cfg where
  regs : ℕ → ℝ
  ptrs : ℕ → ℤ
  mem : ℤ → ℝ

def Cfg.init (x : ℤ → ℝ) : Cfg := ⟨fun _ => 0, fun _ => 0, x⟩

inductive Stmt : Type
  | const (dst : ℕ) (c : ℚ)
  | add (dst i j : ℕ)
  | sub (dst i j : ℕ)
  | mul (dst i j : ℕ)
  | div (dst i j : ℕ)
  | load (dst q : ℕ)
  | store (q i : ℕ)
  | pset (q : ℕ) (c : ℤ)
  | pcopy (q q' : ℕ)
  | pinc (q : ℕ)
  | pdec (q : ℕ)
  | seq (a b : Stmt)
  /-- if `regs i ≤ 0` then `a` else `b` -/
  | ifle (i : ℕ) (a b : Stmt)
  /-- if `ptrs q ≤ ptrs q'` then `a` else `b` -/
  | ifple (q q' : ℕ) (a b : Stmt)
  /-- while `0 < regs i` do `body` -/
  | whilegt (i : ℕ) (body : Stmt)
  /-- while `ptrs q' < ptrs q` do `body` -/
  | whilepgt (q q' : ℕ) (body : Stmt)

/-- Big-step semantics with the exact number of machine steps of the compiled code.
Division is only defined for a positive divisor. -/
inductive Exec : Stmt → Cfg → ℕ → Cfg → Prop
  | const (dst : ℕ) (c : ℚ) (σ : Cfg) :
      Exec (.const dst c) σ 1 ⟨Function.update σ.regs dst (c : ℝ), σ.ptrs, σ.mem⟩
  | add (dst i j : ℕ) (σ : Cfg) :
      Exec (.add dst i j) σ 1 ⟨Function.update σ.regs dst (σ.regs i + σ.regs j), σ.ptrs, σ.mem⟩
  | sub (dst i j : ℕ) (σ : Cfg) :
      Exec (.sub dst i j) σ 1 ⟨Function.update σ.regs dst (σ.regs i - σ.regs j), σ.ptrs, σ.mem⟩
  | mul (dst i j : ℕ) (σ : Cfg) :
      Exec (.mul dst i j) σ 1 ⟨Function.update σ.regs dst (σ.regs i * σ.regs j), σ.ptrs, σ.mem⟩
  | div (dst i j : ℕ) (σ : Cfg) (h : 0 < σ.regs j) :
      Exec (.div dst i j) σ 1 ⟨Function.update σ.regs dst (σ.regs i / σ.regs j), σ.ptrs, σ.mem⟩
  | load (dst q : ℕ) (σ : Cfg) :
      Exec (.load dst q) σ 1 ⟨Function.update σ.regs dst (σ.mem (σ.ptrs q)), σ.ptrs, σ.mem⟩
  | store (q i : ℕ) (σ : Cfg) :
      Exec (.store q i) σ 1 ⟨σ.regs, σ.ptrs, Function.update σ.mem (σ.ptrs q) (σ.regs i)⟩
  | pset (q : ℕ) (c : ℤ) (σ : Cfg) :
      Exec (.pset q c) σ 1 ⟨σ.regs, Function.update σ.ptrs q c, σ.mem⟩
  | pcopy (q q' : ℕ) (σ : Cfg) :
      Exec (.pcopy q q') σ 1 ⟨σ.regs, Function.update σ.ptrs q (σ.ptrs q'), σ.mem⟩
  | pinc (q : ℕ) (σ : Cfg) :
      Exec (.pinc q) σ 1 ⟨σ.regs, Function.update σ.ptrs q (σ.ptrs q + 1), σ.mem⟩
  | pdec (q : ℕ) (σ : Cfg) :
      Exec (.pdec q) σ 1 ⟨σ.regs, Function.update σ.ptrs q (σ.ptrs q - 1), σ.mem⟩
  | seq (a b : Stmt) (σ σ₁ σ₂ : Cfg) (k₁ k₂ : ℕ) (ha : Exec a σ k₁ σ₁) (hb : Exec b σ₁ k₂ σ₂) :
      Exec (.seq a b) σ (k₁ + k₂) σ₂
  | ifle_t (i : ℕ) (a b : Stmt) (σ σ' : Cfg) (k : ℕ) (h : σ.regs i ≤ 0) (ha : Exec a σ k σ') :
      Exec (.ifle i a b) σ (k + 1) σ'
  | ifle_f (i : ℕ) (a b : Stmt) (σ σ' : Cfg) (k : ℕ) (h : ¬ σ.regs i ≤ 0) (hb : Exec b σ k σ') :
      Exec (.ifle i a b) σ (k + 2) σ'
  | ifple_t (q q' : ℕ) (a b : Stmt) (σ σ' : Cfg) (k : ℕ) (h : σ.ptrs q ≤ σ.ptrs q')
      (ha : Exec a σ k σ') : Exec (.ifple q q' a b) σ (k + 1) σ'
  | ifple_f (q q' : ℕ) (a b : Stmt) (σ σ' : Cfg) (k : ℕ) (h : ¬ σ.ptrs q ≤ σ.ptrs q')
      (hb : Exec b σ k σ') : Exec (.ifple q q' a b) σ (k + 2) σ'
  | while_done (i : ℕ) (body : Stmt) (σ : Cfg) (h : σ.regs i ≤ 0) :
      Exec (.whilegt i body) σ 1 σ
  | while_step (i : ℕ) (body : Stmt) (σ σ₁ σ₂ : Cfg) (k₁ k₂ : ℕ) (h : ¬ σ.regs i ≤ 0)
      (hb : Exec body σ k₁ σ₁) (hr : Exec (.whilegt i body) σ₁ k₂ σ₂) :
      Exec (.whilegt i body) σ (k₁ + k₂ + 2) σ₂
  | pwhile_done (q q' : ℕ) (body : Stmt) (σ : Cfg) (h : σ.ptrs q ≤ σ.ptrs q') :
      Exec (.whilepgt q q' body) σ 1 σ
  | pwhile_step (q q' : ℕ) (body : Stmt) (σ σ₁ σ₂ : Cfg) (k₁ k₂ : ℕ)
      (h : ¬ σ.ptrs q ≤ σ.ptrs q') (hb : Exec body σ k₁ σ₁)
      (hr : Exec (.whilepgt q q' body) σ₁ k₂ σ₂) :
      Exec (.whilepgt q q' body) σ (k₁ + k₂ + 2) σ₂

/-! ## The compiler -/

def Stmt.size : Stmt → ℕ
  | .seq a b => a.size + b.size
  | .ifle _ a b => a.size + b.size + 2
  | .ifple _ _ a b => a.size + b.size + 2
  | .whilegt _ body => body.size + 2
  | .whilepgt _ _ body => body.size + 2
  | _ => 1

/-- Code for `s` placed at absolute address `base`. Pointer register 0 compared with itself is
the unconditional jump. -/
def Stmt.comp : ℕ → Stmt → List RAMInstr
  | _, .const dst c => [.const dst (c : ℝ)]
  | _, .add dst i j => [.add dst i j]
  | _, .sub dst i j => [.sub dst i j]
  | _, .mul dst i j => [.mul dst i j]
  | _, .div dst i j => [.div dst i j]
  | _, .load dst q => [.load dst q]
  | _, .store q i => [.store q i]
  | _, .pset q c => [.pset q c]
  | _, .pcopy q q' => [.pcopy q q']
  | _, .pinc q => [.pinc q]
  | _, .pdec q => [.pdec q]
  | base, .seq a b => a.comp base ++ b.comp (base + a.size)
  | base, .ifle i a b =>
      [.jle i (base + b.size + 2)] ++ b.comp (base + 1) ++
        [.pjle 0 0 (base + b.size + 2 + a.size)] ++ a.comp (base + b.size + 2)
  | base, .ifple q q' a b =>
      [.pjle q q' (base + b.size + 2)] ++ b.comp (base + 1) ++
        [.pjle 0 0 (base + b.size + 2 + a.size)] ++ a.comp (base + b.size + 2)
  | base, .whilegt i body =>
      [.jle i (base + body.size + 2)] ++ body.comp (base + 1) ++ [.pjle 0 0 base]
  | base, .whilepgt q q' body =>
      [.pjle q q' (base + body.size + 2)] ++ body.comp (base + 1) ++ [.pjle 0 0 base]

/-- The whole program: the statement, then `accept`. -/
def program (s : Stmt) : RAMProgram := s.comp 0 ++ [.accept]

end OnlineTransportation1195.Dev.RL

open scoped BigOperators
open Classical

namespace OnlineTransportation1195.Dev.RL.Comp
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RL SmaleNinth

/-- The machine configuration with program counter `pc` and the data of `σ`. -/
def mk (pc : ℕ) (σ : Cfg) : RAMConfig := ⟨pc, σ.regs, σ.ptrs, σ.mem⟩

/-- No division by a non-positive register at configuration `c`. -/
def DivOK (P : RAMProgram) (c : RAMConfig) : Prop :=
  ∀ a b c', P[c.pc]? = some (.div a b c') → 0 < c.regs c'

/-- `k` steps from `c` reach `c'`, with only positive divisions on the way. -/
def Reach (P : RAMProgram) (c : RAMConfig) (k : ℕ) (c' : RAMConfig) : Prop :=
  (RAMStep P)^[k] c = c' ∧ ∀ t < k, DivOK P ((RAMStep P)^[t] c)

theorem Reach.trans {P : RAMProgram} {c c₁ c₂ : RAMConfig} {k₁ k₂ : ℕ}
    (h₁ : Reach P c k₁ c₁) (h₂ : Reach P c₁ k₂ c₂) : Reach P c (k₁ + k₂) c₂ := by
  obtain ⟨e₁, d₁⟩ := h₁
  obtain ⟨e₂, d₂⟩ := h₂
  refine ⟨?_, ?_⟩
  · rw [add_comm, Function.iterate_add_apply, e₁, e₂]
  · intro t ht
    by_cases h : t < k₁
    · exact d₁ t h
    · obtain ⟨u, rfl⟩ : ∃ u, t = k₁ + u := ⟨t - k₁, by omega⟩
      have := d₂ u (by omega)
      rwa [← e₁, ← Function.iterate_add_apply, add_comm] at this

theorem Reach.one {P : RAMProgram} {c c' : RAMConfig} (hd : DivOK P c)
    (h : RAMStep P c = c') : Reach P c 1 c' := by
  refine ⟨by simpa using h, ?_⟩
  intro t ht
  obtain rfl : t = 0 := by omega
  simpa using hd

theorem comp_length (s : Stmt) : ∀ base, (s.comp base).length = s.size := by
  induction s with
  | seq a b iha ihb => intro base; simp [Stmt.comp, Stmt.size, iha, ihb]
  | ifle i a b iha ihb => intro base; simp [Stmt.comp, Stmt.size, iha, ihb]; omega
  | ifple q q' a b iha ihb => intro base; simp [Stmt.comp, Stmt.size, iha, ihb]; omega
  | whilegt i body ih => intro base; simp [Stmt.comp, Stmt.size, ih]
  | whilepgt q q' body ih => intro base; simp [Stmt.comp, Stmt.size, ih]
  | _ => intro base; simp [Stmt.comp, Stmt.size]

theorem get_at {P pre l post : RAMProgram} {base j : ℕ} (hP : P = pre ++ l ++ post)
    (hpre : pre.length = base) (hj : j < l.length) : P[base + j]? = l[j]? := by
  subst hP hpre
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hj]

theorem get_head {P pre post : RAMProgram} {base : ℕ} {ins : RAMInstr} {l : RAMProgram}
    (hP : P = pre ++ (ins :: l) ++ post) (hpre : pre.length = base) : P[base]? = some ins := by
  have := get_at (j := 0) hP hpre (by simp)
  simpa using this

theorem step_eval {P pre post : RAMProgram} {base : ℕ} {ins : RAMInstr} {l : RAMProgram}
    (hP : P = pre ++ (ins :: l) ++ post) (hpre : pre.length = base) (c : RAMConfig)
    (hc : c.pc = base) :
    RAMStep P c = match ins with
    | .const dst c' => ⟨c.pc + 1, Function.update c.regs dst c', c.ptrs, c.mem⟩
    | .add dst i j => ⟨c.pc + 1, Function.update c.regs dst (c.regs i + c.regs j), c.ptrs, c.mem⟩
    | .sub dst i j => ⟨c.pc + 1, Function.update c.regs dst (c.regs i - c.regs j), c.ptrs, c.mem⟩
    | .mul dst i j => ⟨c.pc + 1, Function.update c.regs dst (c.regs i * c.regs j), c.ptrs, c.mem⟩
    | .div dst i j => ⟨c.pc + 1, Function.update c.regs dst (c.regs i / c.regs j), c.ptrs, c.mem⟩
    | .load dst q => ⟨c.pc + 1, Function.update c.regs dst (c.mem (c.ptrs q)), c.ptrs, c.mem⟩
    | .store q i => ⟨c.pc + 1, c.regs, c.ptrs, Function.update c.mem (c.ptrs q) (c.regs i)⟩
    | .pset q c' => ⟨c.pc + 1, c.regs, Function.update c.ptrs q c', c.mem⟩
    | .pcopy q q' => ⟨c.pc + 1, c.regs, Function.update c.ptrs q (c.ptrs q'), c.mem⟩
    | .pinc q => ⟨c.pc + 1, c.regs, Function.update c.ptrs q (c.ptrs q + 1), c.mem⟩
    | .pdec q => ⟨c.pc + 1, c.regs, Function.update c.ptrs q (c.ptrs q - 1), c.mem⟩
    | .jle i target => if c.regs i ≤ 0 then ⟨target, c.regs, c.ptrs, c.mem⟩ else
        ⟨c.pc + 1, c.regs, c.ptrs, c.mem⟩
    | .pjle q q' target => if c.ptrs q ≤ c.ptrs q' then ⟨target, c.regs, c.ptrs, c.mem⟩ else
        ⟨c.pc + 1, c.regs, c.ptrs, c.mem⟩
    | .accept => c
    | .reject => c := by
  have h := get_head hP hpre
  rw [← hc] at h
  unfold RAMStep
  rw [h]
  cases ins <;> rfl

theorem divok_nondiv {P pre post : RAMProgram} {base : ℕ} {ins : RAMInstr} {l : RAMProgram}
    (hP : P = pre ++ (ins :: l) ++ post) (hpre : pre.length = base)
    (hins : ∀ a b c', ins ≠ .div a b c') (c : RAMConfig) (hc : c.pc = base) : DivOK P c := by
  intro a b c' h
  rw [hc, get_head hP hpre] at h
  exact absurd (Option.some.inj h) (hins a b c')

/-- Compiler correctness for a statement placed at `base`. -/
theorem sim {P : RAMProgram} {s : Stmt} {σ σ' : Cfg} {k : ℕ} (h : Exec s σ k σ') :
    ∀ (base : ℕ) (pre post : RAMProgram), P = pre ++ s.comp base ++ post →
      pre.length = base → Reach P (mk base σ) k (mk (base + s.size) σ') := by
  induction h with
  | const dst c σ =>
    intro base pre post hP hpre
    exact Reach.one (divok_nondiv hP hpre (by simp) _ rfl) (step_eval hP hpre _ rfl)
  | add dst i j σ =>
    intro base pre post hP hpre
    exact Reach.one (divok_nondiv hP hpre (by simp) _ rfl) (step_eval hP hpre _ rfl)
  | sub dst i j σ =>
    intro base pre post hP hpre
    exact Reach.one (divok_nondiv hP hpre (by simp) _ rfl) (step_eval hP hpre _ rfl)
  | mul dst i j σ =>
    intro base pre post hP hpre
    exact Reach.one (divok_nondiv hP hpre (by simp) _ rfl) (step_eval hP hpre _ rfl)
  | div dst i j σ hpos =>
    intro base pre post hP hpre
    refine Reach.one ?_ (step_eval hP hpre _ rfl)
    intro a b c' hc
    rw [show (mk base σ).pc = base from rfl, get_head hP hpre] at hc
    cases hc
    exact hpos
  | load dst q σ =>
    intro base pre post hP hpre
    exact Reach.one (divok_nondiv hP hpre (by simp) _ rfl) (step_eval hP hpre _ rfl)
  | store q i σ =>
    intro base pre post hP hpre
    exact Reach.one (divok_nondiv hP hpre (by simp) _ rfl) (step_eval hP hpre _ rfl)
  | pset q c σ =>
    intro base pre post hP hpre
    exact Reach.one (divok_nondiv hP hpre (by simp) _ rfl) (step_eval hP hpre _ rfl)
  | pcopy q q' σ =>
    intro base pre post hP hpre
    exact Reach.one (divok_nondiv hP hpre (by simp) _ rfl) (step_eval hP hpre _ rfl)
  | pinc q σ =>
    intro base pre post hP hpre
    exact Reach.one (divok_nondiv hP hpre (by simp) _ rfl) (step_eval hP hpre _ rfl)
  | pdec q σ =>
    intro base pre post hP hpre
    exact Reach.one (divok_nondiv hP hpre (by simp) _ rfl) (step_eval hP hpre _ rfl)
  | seq a b σ σ₁ σ₂ k₁ k₂ _ _ iha ihb =>
    intro base pre post hP hpre
    have h1 := iha base pre (b.comp (base + a.size) ++ post)
      (by rw [hP]; simp [Stmt.comp]) hpre
    have h2 := ihb (base + a.size) (pre ++ a.comp base) post
      (by rw [hP]; simp [Stmt.comp]) (by simp [hpre, comp_length])
    have := h1.trans h2
    simpa [Stmt.size, add_assoc] using this
  | ifle_t i a b σ σ' k hle _ iha =>
    intro base pre post hP hpre
    have hP0 : P = pre ++ (RAMInstr.jle i (base + b.size + 2) :: (b.comp (base + 1) ++
        [RAMInstr.pjle 0 0 (base + b.size + 2 + a.size)] ++ a.comp (base + b.size + 2))) ++
        post := by rw [hP]; simp [Stmt.comp]
    have h0 : Reach P (mk base σ) 1 (mk (base + b.size + 2) σ) := by
      refine Reach.one (divok_nondiv hP0 hpre (by simp) _ rfl) ?_
      rw [step_eval hP0 hpre _ rfl]
      simp [mk, hle]
    have h1 := iha (base + b.size + 2)
      (pre ++ [RAMInstr.jle i (base + b.size + 2)] ++ b.comp (base + 1) ++
        [RAMInstr.pjle 0 0 (base + b.size + 2 + a.size)]) post
      (by rw [hP]; simp [Stmt.comp]) (by simp [hpre, comp_length]; omega)
    have := h0.trans h1
    rw [show 1 + k = k + 1 by omega] at this
    convert this using 2
    simp [Stmt.size]; omega
  | ifle_f i a b σ σ' k hle _ ihb =>
    intro base pre post hP hpre
    have hP0 : P = pre ++ (RAMInstr.jle i (base + b.size + 2) :: (b.comp (base + 1) ++
        [RAMInstr.pjle 0 0 (base + b.size + 2 + a.size)] ++ a.comp (base + b.size + 2))) ++
        post := by rw [hP]; simp [Stmt.comp]
    have h0 : Reach P (mk base σ) 1 (mk (base + 1) σ) := by
      refine Reach.one (divok_nondiv hP0 hpre (by simp) _ rfl) ?_
      rw [step_eval hP0 hpre _ rfl]
      simp [mk, hle]
    have h1 := ihb (base + 1) (pre ++ [RAMInstr.jle i (base + b.size + 2)])
      ([RAMInstr.pjle 0 0 (base + b.size + 2 + a.size)] ++ a.comp (base + b.size + 2) ++ post)
      (by rw [hP]; simp [Stmt.comp]) (by simp [hpre])
    have hP2 : P = (pre ++ [RAMInstr.jle i (base + b.size + 2)] ++ b.comp (base + 1)) ++
        (RAMInstr.pjle 0 0 (base + b.size + 2 + a.size) :: a.comp (base + b.size + 2)) ++
        post := by
      rw [hP]; simp [Stmt.comp]
    have hl2 : (pre ++ [RAMInstr.jle i (base + b.size + 2)] ++ b.comp (base + 1)).length =
        base + 1 + b.size := by simp [hpre, comp_length]; omega
    have h2 : Reach P (mk (base + 1 + b.size) σ') 1 (mk (base + (Stmt.ifle i a b).size) σ') := by
      refine Reach.one (divok_nondiv hP2 hl2 (by simp) _ rfl) ?_
      rw [step_eval hP2 hl2 _ rfl]
      simp [mk, Stmt.size]; omega
    have := (h0.trans h1).trans h2
    rw [show 1 + k + 1 = k + 2 by omega] at this
    exact this
  | ifple_t q q' a b σ σ' k hle _ iha =>
    intro base pre post hP hpre
    have hP0 : P = pre ++ (RAMInstr.pjle q q' (base + b.size + 2) :: (b.comp (base + 1) ++
        [RAMInstr.pjle 0 0 (base + b.size + 2 + a.size)] ++ a.comp (base + b.size + 2))) ++
        post := by rw [hP]; simp [Stmt.comp]
    have h0 : Reach P (mk base σ) 1 (mk (base + b.size + 2) σ) := by
      refine Reach.one (divok_nondiv hP0 hpre (by simp) _ rfl) ?_
      rw [step_eval hP0 hpre _ rfl]
      simp [mk, hle]
    have h1 := iha (base + b.size + 2)
      (pre ++ [RAMInstr.pjle q q' (base + b.size + 2)] ++ b.comp (base + 1) ++
        [RAMInstr.pjle 0 0 (base + b.size + 2 + a.size)]) post
      (by rw [hP]; simp [Stmt.comp]) (by simp [hpre, comp_length]; omega)
    have := h0.trans h1
    rw [show 1 + k = k + 1 by omega] at this
    convert this using 2
    simp [Stmt.size]; omega
  | ifple_f q q' a b σ σ' k hle _ ihb =>
    intro base pre post hP hpre
    have hP0 : P = pre ++ (RAMInstr.pjle q q' (base + b.size + 2) :: (b.comp (base + 1) ++
        [RAMInstr.pjle 0 0 (base + b.size + 2 + a.size)] ++ a.comp (base + b.size + 2))) ++
        post := by rw [hP]; simp [Stmt.comp]
    have h0 : Reach P (mk base σ) 1 (mk (base + 1) σ) := by
      refine Reach.one (divok_nondiv hP0 hpre (by simp) _ rfl) ?_
      rw [step_eval hP0 hpre _ rfl]
      simp [mk, hle]
    have h1 := ihb (base + 1) (pre ++ [RAMInstr.pjle q q' (base + b.size + 2)])
      ([RAMInstr.pjle 0 0 (base + b.size + 2 + a.size)] ++ a.comp (base + b.size + 2) ++ post)
      (by rw [hP]; simp [Stmt.comp]) (by simp [hpre])
    have hP2 : P = (pre ++ [RAMInstr.pjle q q' (base + b.size + 2)] ++ b.comp (base + 1)) ++
        (RAMInstr.pjle 0 0 (base + b.size + 2 + a.size) :: a.comp (base + b.size + 2)) ++
        post := by
      rw [hP]; simp [Stmt.comp]
    have hl2 : (pre ++ [RAMInstr.pjle q q' (base + b.size + 2)] ++ b.comp (base + 1)).length =
        base + 1 + b.size := by simp [hpre, comp_length]; omega
    have h2 : Reach P (mk (base + 1 + b.size) σ') 1
        (mk (base + (Stmt.ifple q q' a b).size) σ') := by
      refine Reach.one (divok_nondiv hP2 hl2 (by simp) _ rfl) ?_
      rw [step_eval hP2 hl2 _ rfl]
      simp [mk, Stmt.size]; omega
    have := (h0.trans h1).trans h2
    rw [show 1 + k + 1 = k + 2 by omega] at this
    exact this
  | while_done i body σ hle =>
    intro base pre post hP hpre
    have hP0 : P = pre ++ (RAMInstr.jle i (base + body.size + 2) :: (body.comp (base + 1) ++
        [RAMInstr.pjle 0 0 base])) ++ post := by rw [hP]; simp [Stmt.comp]
    refine Reach.one (divok_nondiv hP0 hpre (by simp) _ rfl) ?_
    rw [step_eval hP0 hpre _ rfl]
    simp [mk, hle, Stmt.size]; omega
  | while_step i body σ σ₁ σ₂ k₁ k₂ hle _ _ ihb ihr =>
    intro base pre post hP hpre
    have hP0 : P = pre ++ (RAMInstr.jle i (base + body.size + 2) :: (body.comp (base + 1) ++
        [RAMInstr.pjle 0 0 base])) ++ post := by rw [hP]; simp [Stmt.comp]
    have h0 : Reach P (mk base σ) 1 (mk (base + 1) σ) := by
      refine Reach.one (divok_nondiv hP0 hpre (by simp) _ rfl) ?_
      rw [step_eval hP0 hpre _ rfl]
      simp [mk, hle]
    have h1 := ihb (base + 1) (pre ++ [RAMInstr.jle i (base + body.size + 2)])
      ([RAMInstr.pjle 0 0 base] ++ post) (by rw [hP]; simp [Stmt.comp]) (by simp [hpre])
    have hP2 : P = (pre ++ [RAMInstr.jle i (base + body.size + 2)] ++ body.comp (base + 1)) ++
        [RAMInstr.pjle 0 0 base] ++ post := by
      rw [hP]; simp [Stmt.comp]
    have hl2 : (pre ++ [RAMInstr.jle i (base + body.size + 2)] ++ body.comp (base + 1)).length =
        base + 1 + body.size := by simp [hpre, comp_length]; omega
    have h2 : Reach P (mk (base + 1 + body.size) σ₁) 1 (mk base σ₁) := by
      refine Reach.one (divok_nondiv hP2 hl2 (by simp) _ rfl) ?_
      rw [step_eval hP2 hl2 _ rfl]
      simp [mk]
    have h3 := ihr base pre post hP hpre
    have := ((h0.trans h1).trans h2).trans h3
    rw [show 1 + k₁ + 1 + k₂ = k₁ + k₂ + 2 by omega] at this
    exact this
  | pwhile_done q q' body σ hle =>
    intro base pre post hP hpre
    have hP0 : P = pre ++ (RAMInstr.pjle q q' (base + body.size + 2) :: (body.comp (base + 1) ++
        [RAMInstr.pjle 0 0 base])) ++ post := by rw [hP]; simp [Stmt.comp]
    refine Reach.one (divok_nondiv hP0 hpre (by simp) _ rfl) ?_
    rw [step_eval hP0 hpre _ rfl]
    simp [mk, hle, Stmt.size]; omega
  | pwhile_step q q' body σ σ₁ σ₂ k₁ k₂ hle _ _ ihb ihr =>
    intro base pre post hP hpre
    have hP0 : P = pre ++ (RAMInstr.pjle q q' (base + body.size + 2) :: (body.comp (base + 1) ++
        [RAMInstr.pjle 0 0 base])) ++ post := by rw [hP]; simp [Stmt.comp]
    have h0 : Reach P (mk base σ) 1 (mk (base + 1) σ) := by
      refine Reach.one (divok_nondiv hP0 hpre (by simp) _ rfl) ?_
      rw [step_eval hP0 hpre _ rfl]
      simp [mk, hle]
    have h1 := ihb (base + 1) (pre ++ [RAMInstr.pjle q q' (base + body.size + 2)])
      ([RAMInstr.pjle 0 0 base] ++ post) (by rw [hP]; simp [Stmt.comp]) (by simp [hpre])
    have hP2 : P = (pre ++ [RAMInstr.pjle q q' (base + body.size + 2)] ++ body.comp (base + 1)) ++
        [RAMInstr.pjle 0 0 base] ++ post := by
      rw [hP]; simp [Stmt.comp]
    have hl2 : (pre ++ [RAMInstr.pjle q q' (base + body.size + 2)] ++ body.comp (base + 1)).length =
        base + 1 + body.size := by simp [hpre, comp_length]; omega
    have h2 : Reach P (mk (base + 1 + body.size) σ₁) 1 (mk base σ₁) := by
      refine Reach.one (divok_nondiv hP2 hl2 (by simp) _ rfl) ?_
      rw [step_eval hP2 hl2 _ rfl]
      simp [mk]
    have h3 := ihr base pre post hP hpre
    have := ((h0.trans h1).trans h2).trans h3
    rw [show 1 + k₁ + 1 + k₂ = k₁ + k₂ + 2 by omega] at this
    exact this

theorem comp_rational (s : Stmt) : ∀ base, ∀ i ∈ s.comp base, ∀ j c,
    i = RAMInstr.const j c → ∃ q : ℚ, c = (q : ℝ) := by
  induction s with
  | const dst c =>
    intro base i hi j c' hc
    simp [Stmt.comp] at hi
    subst hi
    cases hc
    exact ⟨c, rfl⟩
  | seq a b iha ihb =>
    intro base i hi
    simp only [Stmt.comp, List.mem_append] at hi
    rcases hi with hi | hi
    · exact iha _ i hi
    · exact ihb _ i hi
  | ifle x a b iha ihb =>
    intro base i hi j c hc
    simp only [Stmt.comp, List.mem_append, List.mem_singleton] at hi
    rcases hi with ((hi | hi) | hi) | hi
    · subst hi; cases hc
    · exact ihb _ i hi j c hc
    · subst hi; cases hc
    · exact iha _ i hi j c hc
  | ifple x y a b iha ihb =>
    intro base i hi j c hc
    simp only [Stmt.comp, List.mem_append, List.mem_singleton] at hi
    rcases hi with ((hi | hi) | hi) | hi
    · subst hi; cases hc
    · exact ihb _ i hi j c hc
    · subst hi; cases hc
    · exact iha _ i hi j c hc
  | whilegt x body ih =>
    intro base i hi j c hc
    simp only [Stmt.comp, List.mem_append, List.mem_singleton] at hi
    rcases hi with (hi | hi) | hi
    · subst hi; cases hc
    · exact ih _ i hi j c hc
    · subst hi; cases hc
  | whilepgt x y body ih =>
    intro base i hi j c hc
    simp only [Stmt.comp, List.mem_append, List.mem_singleton] at hi
    rcases hi with (hi | hi) | hi
    · subst hi; cases hc
    · exact ih _ i hi j c hc
    · subst hi; cases hc
  | _ =>
    intro base i hi j c hc
    simp [Stmt.comp] at hi
    subst hi
    cases hc

theorem program_rational (s : Stmt) : RationalProgram (program s) := by
  intro i hi j c hc
  simp only [program, List.mem_append, List.mem_singleton] at hi
  rcases hi with hi | hi
  · exact comp_rational s 0 i hi j c hc
  · subst hi; cases hc

/-- A terminating execution of cost `k` is a machine run of exactly `k` steps ending at `accept`,
dividing only by positive numbers. -/
theorem program_correct (s : Stmt) (x : ℤ → ℝ) (k : ℕ) (σ : Cfg)
    (h : Exec s (Cfg.init x) k σ) :
    PositiveDivisions (program s) x k ∧
      RAMHaltedWith (program s) (RAMRun (program s) x k) true ∧
      (RAMRun (program s) x k).mem = σ.mem := by
  have hR := sim (P := program s) h 0 [] [.accept] (by simp [program]) rfl
  obtain ⟨he, hd⟩ := hR
  have hrun : ∀ t, RAMRun (program s) x t = (RAMStep (program s))^[t] (mk 0 (Cfg.init x)) :=
    fun t => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro t ht a b c hc
    rw [hrun] at hc ⊢
    exact hd t ht a b c hc
  · rw [hrun, he]
    simp [RAMHaltedWith, mk, program, comp_length]
  · rw [hrun, he]
    rfl

end OnlineTransportation1195.Dev.RL.Comp
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace OnlineTransportation1195.Dev.RL.Lib
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RL SmaleNinth

/-! ## Weakest-precondition style runs -/

open Function

/-- `s` run from `σ` terminates, after `k` steps, in a configuration `σ'` with `Q k σ'`. -/
def Runs (s : Stmt) (σ : Cfg) (Q : ℕ → Cfg → Prop) : Prop :=
  ∃ k σ', Exec s σ k σ' ∧ Q k σ'

theorem r_mono {s : Stmt} {σ : Cfg} {Q Q' : ℕ → Cfg → Prop} (h : Runs s σ Q)
    (hQ : ∀ k σ', Q k σ' → Q' k σ') : Runs s σ Q' := by
  obtain ⟨k, σ', h1, h2⟩ := h
  exact ⟨k, σ', h1, hQ _ _ h2⟩

theorem r_seq {a b : Stmt} {σ : Cfg} {Q : ℕ → Cfg → Prop}
    (h : Runs a σ (fun k1 σ1 => Runs b σ1 (fun k2 σ2 => Q (k1 + k2) σ2))) :
    Runs (.seq a b) σ Q := by
  obtain ⟨k1, σ1, h1, k2, σ2, h2, hQ⟩ := h
  exact ⟨k1 + k2, σ2, .seq _ _ _ _ _ _ _ h1 h2, hQ⟩

section basic
variable {σ : Cfg} {Q : ℕ → Cfg → Prop}

theorem r_const {d : ℕ} {q : ℚ} (h : Q 1 ⟨update σ.regs d (q : ℝ), σ.ptrs, σ.mem⟩) :
    Runs (.const d q) σ Q := ⟨1, _, .const d q σ, h⟩

theorem r_add {d i j : ℕ} (h : Q 1 ⟨update σ.regs d (σ.regs i + σ.regs j), σ.ptrs, σ.mem⟩) :
    Runs (.add d i j) σ Q := ⟨1, _, .add d i j σ, h⟩

theorem r_sub {d i j : ℕ} (h : Q 1 ⟨update σ.regs d (σ.regs i - σ.regs j), σ.ptrs, σ.mem⟩) :
    Runs (.sub d i j) σ Q := ⟨1, _, .sub d i j σ, h⟩

theorem r_mul {d i j : ℕ} (h : Q 1 ⟨update σ.regs d (σ.regs i * σ.regs j), σ.ptrs, σ.mem⟩) :
    Runs (.mul d i j) σ Q := ⟨1, _, .mul d i j σ, h⟩

theorem r_div {d i j : ℕ} (hj : 0 < σ.regs j)
    (h : Q 1 ⟨update σ.regs d (σ.regs i / σ.regs j), σ.ptrs, σ.mem⟩) :
    Runs (.div d i j) σ Q := ⟨1, _, .div d i j σ hj, h⟩

theorem r_load {d q : ℕ} (h : Q 1 ⟨update σ.regs d (σ.mem (σ.ptrs q)), σ.ptrs, σ.mem⟩) :
    Runs (.load d q) σ Q := ⟨1, _, .load d q σ, h⟩

theorem r_store {q i : ℕ} (h : Q 1 ⟨σ.regs, σ.ptrs, update σ.mem (σ.ptrs q) (σ.regs i)⟩) :
    Runs (.store q i) σ Q := ⟨1, _, .store q i σ, h⟩

theorem r_pset {q : ℕ} {c : ℤ} (h : Q 1 ⟨σ.regs, update σ.ptrs q c, σ.mem⟩) :
    Runs (.pset q c) σ Q := ⟨1, _, .pset q c σ, h⟩

theorem r_pcopy {q q' : ℕ} (h : Q 1 ⟨σ.regs, update σ.ptrs q (σ.ptrs q'), σ.mem⟩) :
    Runs (.pcopy q q') σ Q := ⟨1, _, .pcopy q q' σ, h⟩

theorem r_pinc {q : ℕ} (h : Q 1 ⟨σ.regs, update σ.ptrs q (σ.ptrs q + 1), σ.mem⟩) :
    Runs (.pinc q) σ Q := ⟨1, _, .pinc q σ, h⟩

theorem r_pdec {q : ℕ} (h : Q 1 ⟨σ.regs, update σ.ptrs q (σ.ptrs q - 1), σ.mem⟩) :
    Runs (.pdec q) σ Q := ⟨1, _, .pdec q σ, h⟩

theorem r_ifle {i : ℕ} {a b : Stmt} (ht : σ.regs i ≤ 0 → Runs a σ (fun k σ' => Q (k + 1) σ'))
    (hf : ¬ σ.regs i ≤ 0 → Runs b σ (fun k σ' => Q (k + 2) σ')) : Runs (.ifle i a b) σ Q := by
  by_cases h : σ.regs i ≤ 0
  · obtain ⟨k, σ', h1, h2⟩ := ht h
    exact ⟨k + 1, σ', .ifle_t _ _ _ _ _ _ h h1, h2⟩
  · obtain ⟨k, σ', h1, h2⟩ := hf h
    exact ⟨k + 2, σ', .ifle_f _ _ _ _ _ _ h h1, h2⟩

/-! Fresh-variable forms: the new configuration is a fresh variable described by equations. -/

end basic

/-- A `while` loop running exactly `N` iterations, with an invariant indexed by the iteration. -/
theorem r_while (i : ℕ) (body : Stmt) (N c : ℕ) (I : ℕ → Cfg → Prop) (Q : ℕ → Cfg → Prop)
    (hstep : ∀ m < N, ∀ σ, I m σ → ¬ σ.regs i ≤ 0 ∧
      Runs body σ (fun k σ' => k ≤ c ∧ I (m + 1) σ'))
    (hdone : ∀ σ, I N σ → σ.regs i ≤ 0) (σ : Cfg) (h0 : I 0 σ)
    (hQ : ∀ k σ', k ≤ N * (c + 2) + 1 → I N σ' → Q k σ') :
    Runs (.whilegt i body) σ Q := by
  have key : ∀ j, j ≤ N → ∀ σ, I (N - j) σ →
      ∃ k σ', Exec (.whilegt i body) σ k σ' ∧ k ≤ j * (c + 2) + 1 ∧ I N σ' := by
    intro j
    induction j with
    | zero =>
      intro _ σ h
      have h' : I N σ := by simpa using h
      exact ⟨1, σ, .while_done _ _ _ (hdone σ h'), by simp, h'⟩
    | succ j ih =>
      intro hj σ h
      obtain ⟨hne, k1, σ1, h1, hk1, hI⟩ := hstep (N - (j + 1)) (by omega) σ h
      have e : N - (j + 1) + 1 = N - j := by omega
      rw [e] at hI
      obtain ⟨k2, σ2, h2, hk2, hQ⟩ := ih (by omega) σ1 hI
      refine ⟨k1 + k2 + 2, σ2, .while_step _ _ _ _ _ _ _ hne h1 h2, ?_, hQ⟩
      have : (j + 1) * (c + 2) = j * (c + 2) + (c + 2) := by ring
      omega
  obtain ⟨k, σ', h1, h2, h3⟩ := key N le_rfl σ (by simpa using h0)
  exact ⟨k, σ', h1, hQ k σ' h2 h3⟩

/-- A counted `for` loop: `V` runs from `0` to `N - 1` (`N` in register `Nr`). -/
def forLoop (V Nr C K : ℕ) (body : Stmt) : Stmt :=
  .seq (.const V 0) (.seq (.sub C Nr V) (.whilegt C
    (.seq body (.seq (.const K 1) (.seq (.add V V K) (.sub C Nr V))))))

theorem r_for (V Nr C K : ℕ) (body : Stmt) (hVN : V ≠ Nr) (hVC : V ≠ C) (hVK : V ≠ K)
    (hNC : Nr ≠ C) (hNK : Nr ≠ K) (hCK : C ≠ K)
    (N c : ℕ) (I : ℕ → Cfg → Prop) (σ : Cfg) (hN : σ.regs Nr = N)
    (h0 : ∀ a b, I 0 ⟨update (update σ.regs V a) C b, σ.ptrs, σ.mem⟩)
    (hstep : ∀ m < N, ∀ σ, I m σ → σ.regs V = m → σ.regs Nr = N →
      Runs body σ (fun k σ' => k ≤ c ∧ σ'.regs V = m ∧ σ'.regs Nr = N ∧
        ∀ a b e, I (m + 1) ⟨update (update (update σ'.regs K a) V b) C e, σ'.ptrs, σ'.mem⟩))
    (Q : ℕ → Cfg → Prop) (hQ : ∀ k σ', k ≤ N * (c + 5) + 3 → I N σ' → Q k σ') :
    Runs (forLoop V Nr C K body) σ Q := by
  let J : ℕ → Cfg → Prop := fun m σ => I m σ ∧ σ.regs V = m ∧ σ.regs Nr = N ∧
    σ.regs C = (N : ℝ) - m
  refine r_seq (r_const (r_seq (r_sub (r_while C _ N (c + 3) J _ ?_ ?_ _ ⟨h0 _ _, ?_, ?_, ?_⟩ ?_))))
  · intro m hm σ ⟨hI, hV, hNr, hC⟩
    refine ⟨by rw [hC]; exact not_le.mpr (by linarith [show (m : ℝ) < N from by exact_mod_cast hm]),
      ?_⟩
    refine r_seq (r_mono (hstep m hm σ hI hV hNr) ?_)
    rintro k σ' ⟨hk, hV', hN', hI'⟩
    refine r_seq (r_const (r_seq (r_add (r_sub ⟨by omega, hI' _ _ _, ?_, ?_, ?_⟩))))
    all_goals simp [update_apply, hNK, hVN.symm, hN', hVK, hV', hCK.symm, hVC.symm, hVC, hNC]
  · intro σ ⟨_, _, _, hC⟩
    rw [hC]; simp
  · simp [update_apply, hVC]
  · simp [update_apply, hNC, hVN.symm, hN]
  · simp [update_apply, hNC, hVN.symm, hN, hVC.symm]
  · rintro k σ' hk ⟨hI, -⟩
    refine hQ _ _ ?_ hI
    have : N * (c + 3 + 2) = N * (c + 5) := by ring
    omega

/-! ## Small subroutines -/

/-- No operation. -/
def skip : Stmt := .pcopy 9 9

theorem r_skip {σ : Cfg} {Q : ℕ → Cfg → Prop} (h : Q 1 σ) : Runs skip σ Q :=
  r_pcopy (by simpa using h)

/-- `d := s`. -/
def mov (d s : ℕ) : Stmt := .seq (.const d 0) (.add d d s)

theorem r_mov {d s : ℕ} (hds : d ≠ s) {σ : Cfg} {Q : ℕ → Cfg → Prop}
    (h : Q 2 ⟨update σ.regs d (σ.regs s), σ.ptrs, σ.mem⟩) : Runs (mov d s) σ Q := by
  refine r_seq (r_const (r_add ?_))
  convert h using 2
  funext j
  simp only [update_apply]; split_ifs <;> simp_all

def mv (up : Bool) : Stmt := if up then .pinc 1 else .pdec 1

def sgn (up : Bool) (m : ℕ) : ℤ := if up then (m : ℤ) else -(m : ℤ)

/-- Move pointer `1` to `c ± m`, where `m` is the natural number in register `100`. -/
def seekCore (c : ℤ) (up : Bool) : Stmt :=
  .seq (.pset 1 c) (.seq (.const 101 1) (.whilegt 100 (.seq (mv up) (.sub 100 100 101))))

theorem r_seekCore (c : ℤ) (up : Bool) (σ : Cfg) (m : ℕ) (hm : σ.regs 100 = m)
    (Q : ℕ → Cfg → Prop)
    (hQ : ∀ k, k ≤ 4 * m + 3 → ∀ a b,
      Q k ⟨update (update σ.regs 100 a) 101 b, update σ.ptrs 1 (c + sgn up m), σ.mem⟩) :
    Runs (seekCore c up) σ Q := by
  let I : ℕ → Cfg → Prop := fun j σ' => σ' = ⟨update (update σ.regs 100 ((m : ℝ) - j)) 101 1,
    update σ.ptrs 1 (c + sgn up j), σ.mem⟩
  refine r_seq (r_pset (r_seq (r_const (r_while 100 (.seq (mv up) (.sub 100 100 101)) m 2 I _
    ?_ ?_ _ ?_ ?_))))
  · intro j hj σ' hσ'
    subst hσ'
    refine ⟨?_, ?_⟩
    · have : (j : ℝ) < m := by exact_mod_cast hj
      simp; linarith
    · cases up
      · refine r_seq (r_pdec (r_sub ⟨le_rfl, ?_⟩))
        simp only [I, Cfg.mk.injEq, and_true]
        refine ⟨?_, ?_⟩
        · funext k; simp only [update_apply]; split_ifs <;> simp_all; ring
        · funext k; simp only [update_apply, sgn]; split_ifs <;> simp_all; ring
      · refine r_seq (r_pinc (r_sub ⟨le_rfl, ?_⟩))
        simp only [I, Cfg.mk.injEq, and_true]
        refine ⟨?_, ?_⟩
        · funext k; simp only [update_apply]; split_ifs <;> simp_all; ring
        · funext k; simp only [update_apply, sgn]; split_ifs <;> simp_all; ring
  · intro σ' hσ'
    subst hσ'
    simp
  · simp only [I, Cfg.mk.injEq, and_true]
    refine ⟨?_, ?_⟩
    · funext j; simp only [update_apply]; split_ifs <;> simp_all
    · funext j; simp [update_apply, sgn]
  · intro k σ' hk hσ'
    subst hσ'
    exact hQ _ (by nlinarith) _ _

/-- `d := M[m]` where `m` is the natural number in register `r`. -/
def ld (d r : ℕ) : Stmt := .seq (mov 100 r) (.seq (seekCore 0 true) (.load d 1))

theorem r_ld (d r : ℕ) (hr : r ≠ 100) (σ : Cfg) (m : ℕ) (hm : σ.regs r = m)
    (Q : ℕ → Cfg → Prop)
    (hQ : ∀ k, k ≤ 4 * m + 6 → ∀ a b, ∀ σ' : Cfg,
      σ'.regs = update (update (update σ.regs 100 a) 101 b) d (σ.mem m) → σ'.mem = σ.mem →
      Q k σ') :
    Runs (ld d r) σ Q := by
  refine r_seq (r_mov (Ne.symm hr) (r_seq (r_seekCore 0 true _ m (by simp [hm]) _
    (fun k hk a b => r_load ?_))))
  refine hQ (2 + (k + 1)) (by omega) a b _ ?_ (by simp)
  funext j; simp only [update_apply]; split_ifs <;> simp_all [sgn]

/-- `d := M[f + 3 m]` (field `f` of vertex `m` of the input). -/
def ldIn (d f r : ℕ) : Stmt :=
  .seq (.const 101 3) (.seq (.mul 100 101 r) (.seq (.const 101 (f : ℚ)) (.seq (.add 100 100 101)
    (.seq (seekCore 0 true) (.load d 1)))))

theorem r_ldIn (d f r : ℕ) (hr : r ≠ 101) (σ : Cfg) (m : ℕ) (hm : σ.regs r = m)
    (Q : ℕ → Cfg → Prop)
    (hQ : ∀ k, k ≤ 4 * (f + 3 * m) + 8 → ∀ a b, ∀ σ' : Cfg,
      σ'.regs = update (update (update σ.regs 100 a) 101 b) d (σ.mem ((f + 3 * m : ℕ) : ℤ)) →
      σ'.mem = σ.mem → Q k σ') :
    Runs (ldIn d f r) σ Q := by
  refine r_seq (r_const (r_seq (r_mul (r_seq (r_const (r_seq (r_add (r_seq
    (r_seekCore 0 true _ (f + 3 * m) ?_ _ (fun k hk a b => r_load ?_))))))))))
  · simp [update_apply, hr, hm]; ring
  · refine hQ (1 + (1 + (1 + (1 + (k + 1))))) (by omega) a b _ ?_ (by simp)
    funext j; simp only [update_apply]; split_ifs <;> simp_all [sgn]

/-- `d := [regs a = regs b]` as `1`/`0`. -/
def eqT (d a b : ℕ) : Stmt :=
  .seq (.sub 100 a b) (.ifle 100 (.seq (.sub 100 b a) (.ifle 100 (.const d 1) (.const d 0)))
    (.const d 0))

theorem r_eqT (d a b : ℕ) (hd : d ≠ 100) (ha : a ≠ 100) (hb : b ≠ 100) (σ : Cfg)
    (Q : ℕ → Cfg → Prop)
    (hQ : ∀ k, k ≤ 7 → ∀ z, ∀ σ' : Cfg, σ'.regs = update (update σ.regs 100 z) d
      (if σ.regs a = σ.regs b then 1 else 0) → σ'.mem = σ.mem → Q k σ') :
    Runs (eqT d a b) σ Q := by
  refine r_seq (r_sub (r_ifle ?_ ?_))
  · intro h1
    refine r_seq (r_sub (r_ifle ?_ ?_))
    · intro h2
      refine r_const ?_
      simp [update_apply, ha, hb] at h1 h2
      have : σ.regs a = σ.regs b := by linarith
      refine hQ (1 + ((1 + (1 + 1)) + 1)) (by omega) (σ.regs b - σ.regs a) _ ?_ (by simp)
      funext j; simp only [update_apply]; split_ifs <;> simp_all
    · intro h2
      refine r_const ?_
      simp [update_apply, ha, hb] at h1 h2
      have : σ.regs a ≠ σ.regs b := by intro h; rw [h] at h2; simp at h2
      refine hQ (1 + ((1 + (1 + 2)) + 1)) (by omega) (σ.regs b - σ.regs a) _ ?_ (by simp)
      funext j; simp only [update_apply]; split_ifs <;> simp_all
  · intro h1
    refine r_const ?_
    simp [update_apply, ha, hb] at h1
    have : σ.regs a ≠ σ.regs b := by intro h; rw [h] at h1; simp at h1
    refine hQ (1 + (1 + 2)) (by omega) (σ.regs a - σ.regs b) _ ?_ (by simp)
    funext j; simp only [update_apply]; split_ifs <;> simp_all

/-! ## The input tape -/

section input
variable {n : ℕ}

theorem flatMap_get (g : Fin n → List ℝ) (hg : ∀ v, (g v).length = 3) (v : Fin n) (j : ℕ)
    (hj : j < 3) : ((List.finRange n).flatMap g)[3 * v.val + j]? = (g v)[j]? := by
  induction n with
  | zero => exact v.elim0
  | succ n ih =>
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
    refine Fin.cases ?_ (fun w => ?_) v
    · simp only [Fin.val_zero, mul_zero, zero_add]
      rw [List.getElem?_append_left (by rw [hg]; exact hj)]
    · rw [List.getElem?_append_right (by rw [hg]; simp; omega), hg]
      have := ih (fun w => g w.succ) (fun w => hg _) w
      simp only [Fin.val_succ] at this ⊢
      rw [show 3 * (w.val + 1) + j - 3 = 3 * w.val + j by omega]
      exact this

variable (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n))

theorem ti_cells (k : ℕ) : treeInput T d L (k : ℤ) =
    (([(n : ℝ), (T.root.val : ℝ)] ++
      (List.finRange n).flatMap (fun v => [((T.parent v).val : ℝ), T.W v, d v]) ++
      [(L.length : ℝ)] ++ L.map (fun v => (v.val : ℝ)))[k]?).getD 0 := by
  unfold treeInput
  simp only [Int.natCast_nonneg, if_true, Int.toNat_natCast, List.getD_eq_getElem?_getD]

theorem flat_len : ((List.finRange n).flatMap
    (fun v => [((T.parent v).val : ℝ), T.W v, d v])).length = 3 * n := by
  simp [List.length_flatMap]
  ring

theorem ti_zero : treeInput T d L ((0 : ℕ) : ℤ) = n := by
  rw [ti_cells]; simp

theorem ti_one : treeInput T d L ((1 : ℕ) : ℤ) = T.root.val := by
  rw [ti_cells]; simp

theorem ti_vert (v : Fin n) (j : ℕ) (hj : j < 3) :
    treeInput T d L ((j + 2 + 3 * v.val : ℕ) : ℤ) =
      ([((T.parent v).val : ℝ), T.W v, d v][j]?).getD 0 := by
  rw [ti_cells]
  have hv := v.isLt
  rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_append_left (by rw [flat_len]; simp; omega)]
  rw [show j + 2 + 3 * v.val - [(n : ℝ), (T.root.val : ℝ)].length = 3 * v.val + j by simp; omega]
  rw [flatMap_get _ (by simp) v j hj]

theorem ti_parent (v : Fin n) : treeInput T d L ((2 + 3 * v.val : ℕ) : ℤ) = (T.parent v).val := by
  have := ti_vert T d L v 0 (by norm_num); simpa using this

theorem ti_W (v : Fin n) : treeInput T d L ((3 + 3 * v.val : ℕ) : ℤ) = T.W v := by
  have := ti_vert T d L v 1 (by norm_num); simpa [show 1 + 2 = 3 by rfl] using this

end input

/-! ## Facts about DFS lists -/

section dfs
variable {n : ℕ} (T : Tree n)

theorem mem_edges_iff (e : Fin n) : e ∈ T.edges ↔ e ≠ T.root := by
  simp [Tree.edges]

end dfs

end OnlineTransportation1195.Dev.RL.Lib
end

section
/-!
Blueprint for Lemma 3.3 (`constructible_root_patch_budgets`), q419: a structured language with an
exact-cost big-step semantics, compiled to `SmaleNinth.RAMProgram`.
-/

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace OnlineTransportation1195.Dev.RAM
open OnlineTransportation1195.Main SmaleNinth

/-! ## The structured language -/

/-! ## The compiler -/

/-! ## Part F: compiler correctness -/

/-! ## Part M: the mathematics of the search -/

/-- The largest breakpoint `d e` (or `0`) at which `F` is still at most `r`. -/
noncomputable def betaLo {n : ℕ} (T : Tree n) (d : Fin n → ℝ) (r : ℝ) : ℝ :=
  (insert 0 ((T.edges.filter (fun e => T.F d (d e) ≤ r)).image d)).max' (Finset.insert_nonempty _ _)

/-- The solution of `F s = r` on the linear piece of `F` starting at `betaLo`. -/
noncomputable def sOf {n : ℕ} (T : Tree n) (d : Fin n → ℝ) (r : ℝ) : ℝ :=
  (r - ∑ e ∈ T.edges.filter (fun e => d e ≤ betaLo T d r), T.W e) /
    ∑ e ∈ T.edges.filter (fun e => betaLo T d r < d e), T.W e / d e

/-! ## Part G: the algorithm -/

end OnlineTransportation1195.Dev.RAM

namespace OnlineTransportation1195.Main

end OnlineTransportation1195.Main
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false

namespace OnlineTransportation1195.Dev.RAM.PartM
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth

variable {n : ℕ}

theorem mem_edges_iff (T : Tree n) (e : Fin n) : e ∈ T.edges ↔ e ≠ T.root := by
  simp [Tree.edges]

theorem W_pos_of_mem (T : Tree n) (e : Fin n) (he : e ∈ T.edges) : 0 < T.W e :=
  T.W_pos e ((mem_edges_iff T e).mp he)

theorem x_nonneg (T : Tree n) (L : List (Fin n)) (e : Fin n) : 0 ≤ T.x L e := by
  unfold Tree.x
  split
  · next i _ =>
    unfold Tree.downPrefix Tree.downStep
    refine Finset.sum_nonneg fun j _ => ?_
    split_ifs with h
    · exact (T.W_pos _ h.1).le
    · exact le_refl _
  · exact le_refl _

theorem F_le_self (T : Tree n) (d : Fin n → ℝ) (hD : T.Normalized d) (t : ℝ) (_ht : 0 ≤ t) :
    T.F d t ≤ t := by
  unfold Tree.F
  calc ∑ e ∈ T.edges, T.W e * min 1 (t / d e)
      ≤ ∑ e ∈ T.edges, T.W e * (t / d e) := by
        apply Finset.sum_le_sum
        intro e he
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) (W_pos_of_mem T e he).le
    _ = ∑ e ∈ T.edges, t * (T.W e / d e) := by
        apply Finset.sum_congr rfl
        intro e _
        ring
    _ = t * ∑ e ∈ T.edges, T.W e / d e := (Finset.mul_sum _ _ _).symm
    _ = t := by rw [hD.2.2, mul_one]

theorem F_le_total (T : Tree n) (d : Fin n → ℝ) (t : ℝ) :
    T.F d t ≤ ∑ e ∈ T.edges, T.W e := by
  unfold Tree.F
  apply Finset.sum_le_sum
  intro e he
  calc T.W e * min 1 (t / d e) ≤ T.W e * 1 :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (W_pos_of_mem T e he).le
    _ = T.W e := mul_one _

theorem F_mono (T : Tree n) (d : Fin n → ℝ) (hD : T.Normalized d) {s s' : ℝ} (h : s ≤ s') :
    T.F d s ≤ T.F d s' := by
  unfold Tree.F
  apply Finset.sum_le_sum
  intro e he
  apply mul_le_mul_of_nonneg_left _ (W_pos_of_mem T e he).le
  exact min_le_min_left _ (div_le_div_of_nonneg_right h (hD.1 e he).le)

theorem F_zero (T : Tree n) (d : Fin n → ℝ) : T.F d 0 = 0 := by
  simp [Tree.F]

/-- `F` equals the total weight once `s` is at least every deadline. -/
theorem F_of_ge (T : Tree n) (d : Fin n → ℝ) (hD : T.Normalized d) (s : ℝ)
    (hs : ∀ e ∈ T.edges, d e ≤ s) : T.F d s = ∑ e ∈ T.edges, T.W e := by
  unfold Tree.F
  apply Finset.sum_congr rfl
  intro e he
  rw [min_eq_left ((one_le_div (hD.1 e he)).mpr (hs e he)), mul_one]

theorem R_eq (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) :
    T.R d L t = T.Rin d L t + T.Rout d L t := by
  have hsub : T.rootPatch d L t ⊆ T.red d L t := Finset.filter_subset _ _
  have := Finset.sum_sdiff (f := T.W) hsub
  unfold Tree.R Tree.Rin Tree.Rout
  linarith

theorem Rout_nonneg (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) :
    0 ≤ T.Rout d L t := by
  unfold Tree.Rout
  apply Finset.sum_nonneg
  intro e he
  have he1 : e ∈ T.red d L t := (Finset.mem_sdiff.mp he).1
  exact (W_pos_of_mem T e (Finset.mem_filter.mp he1).1).le

theorem Rin_nonneg (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) :
    0 ≤ T.Rin d L t := by
  unfold Tree.Rin
  apply Finset.sum_nonneg
  intro e he
  have he1 : e ∈ T.red d L t := (Finset.mem_filter.mp he).1
  exact (W_pos_of_mem T e (Finset.mem_filter.mp he1).1).le

theorem Rin_pos (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ)
    (h : (T.rootPatch d L t).Nonempty) : 0 < T.Rin d L t := by
  unfold Tree.Rin
  apply Finset.sum_pos _ h
  intro e he
  have he1 : e ∈ T.red d L t := (Finset.mem_filter.mp he).1
  exact W_pos_of_mem T e (Finset.mem_filter.mp he1).1

/-- A candidate time works: one of `d e - x e` (when positive), or the large time `∑ d + 1`. -/
theorem cand_exists {n : ℕ} (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n))
    (hD : T.Normalized d) (hL : T.DFS L) (hU : T.Unequal d) :
    (∃ e ∈ T.edges, 0 < d e - T.x L e ∧
        T.R d L (d e - T.x L e) < T.F d (d e - T.x L e)) ∨
      T.R d L (∑ e ∈ T.edges, d e + 1) < T.F d (∑ e ∈ T.edges, d e + 1) := by
  obtain ⟨t₀, ht₀, hRF⟩ := strict_red_weight_budget T d L hD hL hU
  set S := T.edges.filter (fun e => t₀ ≤ d e - T.x L e) with hS
  by_cases hne : S.Nonempty
  · obtain ⟨e₁, he₁S, hmin⟩ := S.exists_min_image (fun e => d e - T.x L e) hne
    have he₁ := Finset.mem_filter.mp he₁S
    left
    refine ⟨e₁, he₁.1, by linarith [he₁.2], ?_⟩
    have hred : T.red d L (d e₁ - T.x L e₁) = T.red d L t₀ := by
      unfold Tree.red
      apply Finset.filter_congr
      intro e he
      constructor
      · intro h
        by_contra h'
        have heS : e ∈ S := Finset.mem_filter.mpr ⟨he, by linarith⟩
        have := hmin e heS
        linarith
      · intro h
        linarith [he₁.2]
    have hR : T.R d L (d e₁ - T.x L e₁) = T.R d L t₀ := by
      unfold Tree.R; rw [hred]
    rw [hR]
    exact lt_of_lt_of_le hRF (F_mono T d hD he₁.2)
  · right
    have hall : ∀ e ∈ T.edges, d e - T.x L e < t₀ := by
      intro e he
      by_contra h
      exact hne ⟨e, Finset.mem_filter.mpr ⟨he, by linarith⟩⟩
    have hdle : ∀ e ∈ T.edges, d e ≤ ∑ f ∈ T.edges, d f := fun e he =>
      Finset.single_le_sum (fun f hf => (hD.1 f hf).le) he
    have hred : T.red d L (∑ e ∈ T.edges, d e + 1) = T.red d L t₀ := by
      unfold Tree.red
      apply Finset.filter_congr
      intro e he
      constructor
      · intro _; linarith [hall e he]
      · intro _; linarith [hdle e he, x_nonneg T L e]
    have hR : T.R d L (∑ e ∈ T.edges, d e + 1) = T.R d L t₀ := by
      unfold Tree.R; rw [hred]
    rw [hR, F_of_ge T d hD _ (fun e he => by linarith [hdle e he])]
    exact lt_of_lt_of_le hRF (F_le_total T d t₀)

theorem sOf_spec {n : ℕ} (T : Tree n) (d : Fin n → ℝ) (hD : T.Normalized d) (r : ℝ)
    (hr0 : 0 < r) (hr : r < ∑ e ∈ T.edges, T.W e) :
    0 < ∑ e ∈ T.edges.filter (fun e => betaLo T d r < d e), T.W e / d e ∧
      0 < sOf T d r ∧ T.F d (sOf T d r) = r := by
  set β := betaLo T d r with hβ
  have hβmem : β ∈ insert 0 ((T.edges.filter (fun e => T.F d (d e) ≤ r)).image d) :=
    Finset.max'_mem _ _
  have hβge : ∀ e ∈ T.edges, T.F d (d e) ≤ r → d e ≤ β := by
    intro e he hFe
    apply Finset.le_max'
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem d (Finset.mem_filter.mpr ⟨he, hFe⟩))
  have hβ0 : 0 ≤ β := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  have hFβ : T.F d β ≤ r := by
    rcases Finset.mem_insert.mp hβmem with h | h
    · rw [h, F_zero]; exact hr0.le
    · obtain ⟨e, he, hde⟩ := Finset.mem_image.mp h
      rw [← hde]; exact (Finset.mem_filter.mp he).2
  set U := T.edges.filter (fun e => β < d e) with hU
  have hUne : U.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    have := F_of_ge T d hD β (fun e he => not_lt.mp (h he))
    linarith
  obtain ⟨e', he'U, hmin⟩ := U.exists_min_image d hUne
  have he' := Finset.mem_filter.mp he'U
  set A := ∑ e ∈ T.edges.filter (fun e => d e ≤ β), T.W e with hA
  set B := ∑ e ∈ U, T.W e / d e with hB
  have hBpos : 0 < B := by
    apply Finset.sum_pos _ hUne
    intro e he
    have he2 := Finset.mem_filter.mp he
    exact div_pos (W_pos_of_mem T e he2.1) (hD.1 e he2.1)
  -- `F` is affine on `[β, d e']`.
  have hlin : ∀ s, β ≤ s → s ≤ d e' → T.F d s = A + s * B := by
    intro s hs1 hs2
    unfold Tree.F
    rw [← Finset.sum_filter_add_sum_filter_not T.edges (fun e => d e ≤ β)]
    have hU' : T.edges.filter (fun e => ¬ d e ≤ β) = U := by
      rw [hU]; apply Finset.filter_congr; intro e _; exact not_le
    rw [hU', hA, hB, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro e he
      have he2 := Finset.mem_filter.mp he
      rw [min_eq_left ((one_le_div (hD.1 e he2.1)).mpr (by linarith [he2.2])), mul_one]
    · apply Finset.sum_congr rfl
      intro e he
      have he2 := Finset.mem_filter.mp he
      have hde := hD.1 e he2.1
      have : s ≤ d e := le_trans hs2 (hmin e he)
      rw [min_eq_right ((div_le_one hde).mpr this)]
      ring
  have hFβ' : r < T.F d (d e') := by
    by_contra h
    have := hβge e' he'.1 (not_lt.mp h)
    linarith [he'.2]
  have hAβ : T.F d β = A + β * B := hlin β le_rfl he'.2.le
  have hAβ' : T.F d (d e') = A + d e' * B := hlin (d e') he'.2.le le_rfl
  have hsOf : sOf T d r = (r - A) / B := rfl
  have hs1 : β ≤ (r - A) / B := by
    rw [le_div_iff₀ hBpos]; linarith
  have hs2 : (r - A) / B ≤ d e' := by
    rw [div_le_iff₀ hBpos]; linarith
  have hFs : T.F d ((r - A) / B) = r := by
    rw [hlin _ hs1 hs2]; field_simp; ring
  refine ⟨hBpos, ?_, by rw [hsOf]; exact hFs⟩
  rw [hsOf]
  rcases (le_trans hβ0 hs1).lt_or_eq with h | h
  · exact h
  · rw [← h, F_zero] at hFs; linarith

/-- A good time `t` gives the budget pair, with `s = 0` for an empty root patch. -/
theorem budget_of {n : ℕ} (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n))
    (hD : T.Normalized d) (hL : T.DFS L) (t : ℝ) (ht : 0 < t) (hRF : T.R d L t < T.F d t) :
    T.Budget d L (if T.Rin d L t = 0 then 0 else sOf T d (T.Rin d L t)) t := by
  have hFt := F_le_self T d hD t ht.le
  have hFtot := F_le_total T d t
  have hReq := R_eq T d L t
  have hRout := Rout_nonneg T d L t
  have hRin := Rin_nonneg T d L t
  have hne : T.rootPatch d L t ≠ T.edges := by
    intro h
    have hsub : T.rootPatch d L t ⊆ T.red d L t := Finset.filter_subset _ _
    have hsub2 : T.red d L t ⊆ T.edges := Finset.filter_subset _ _
    have hred : T.red d L t = T.edges := le_antisymm hsub2 (h ▸ hsub)
    have : T.R d L t = ∑ e ∈ T.edges, T.W e := by unfold Tree.R; rw [hred]
    linarith
  split_ifs with h0
  · refine ⟨ht, le_refl _, ht.le, Or.inl ?_, ?_, hne⟩
    · by_contra hc
      have := Rin_pos T d L t (Finset.nonempty_iff_ne_empty.mpr hc)
      linarith
    · linarith
  · have hr0 : 0 < T.Rin d L t := lt_of_le_of_ne hRin (Ne.symm h0)
    obtain ⟨_, hs0, hFs⟩ := sOf_spec T d hD (T.Rin d L t) hr0 (by linarith)
    set s := sOf T d (T.Rin d L t)
    have hst : s ≤ t := by
      by_contra h
      have := F_mono T d hD (not_le.mp h).le
      linarith
    have hEq : T.Rin d L t = T.F d s := hFs.symm
    refine ⟨ht, hs0.le, hst, Or.inr ?_, ?_, hne⟩
    · exact (root_patch_normalization_iff T d L hD hL s t ht hs0 hst).mpr hEq
    · exact detour_budget_inequality T d L hD hL s t ht hs0 hst hEq hRF.le

end OnlineTransportation1195.Dev.RAM.PartM
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
/-!
Blueprint for Theorem 3.1 (`normalized_downward_deadlines`), q419.
Every `sorry` below is a stub proved in a Part file.
-/
/-! ## Walk calculus (Part A) -/
/-- Consecutive vertices are adjacent (no condition on the first vertex). -/
def IsPath (T : Tree n) (L : List (Fin n)) : Prop :=
  ∀ i, i + 1 < L.length → T.Adj (T.vertexAt L i) (T.vertexAt L (i + 1))

/-- Total downward cost of a list. -/
noncomputable def dc (T : Tree n) (L : List (Fin n)) : ℝ :=
  ∑ j ∈ Finset.range (L.length - 1), T.downStep (T.vertexAt L j) (T.vertexAt L (j + 1))

/-- `e` is first crossed in `L` at downward cost at most `c`. -/
def VB (T : Tree n) (L : List (Fin n)) (e : Fin n) (c : ℝ) : Prop :=
  ∃ i, T.FirstAt L e i ∧ T.downPrefix L i ≤ c

/-- A closed path at `v`. -/
def ClosedAt (T : Tree n) (v : Fin n) (M : List (Fin n)) : Prop :=
  M.head? = some v ∧ M.getLast? = some v ∧ IsPath T M

theorem VB_mono (T : Tree n) (L : List (Fin n)) (e : Fin n) (c c' : ℝ)
    (h : VB T L e c) (hc : c ≤ c') : VB T L e c' := by
  obtain ⟨i, hi, hc0⟩ := h
  exact ⟨i, hi, hc0.trans hc⟩

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
/-! ### Basic helpers -/
/-- Prefix cost of the first `k` steps. -/
noncomputable def pc (T : Tree n) (L : List (Fin n)) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, T.downStep (T.vertexAt L j) (T.vertexAt L (j + 1))

theorem downStep_nonneg (T : Tree n) (u v : Fin n) : 0 ≤ T.downStep u v := by
  unfold Tree.downStep
  split_ifs with h
  · exact (T.W_pos v h.1).le
  · exact le_refl 0

theorem downPrefix_eq (T : Tree n) (L : List (Fin n)) (i : ℕ) :
    T.downPrefix L i = pc T L (i + 1) := rfl

theorem dc_eq (T : Tree n) (L : List (Fin n)) : dc T L = pc T L (L.length - 1) := rfl

theorem pc_mono (T : Tree n) (L : List (Fin n)) (a b : ℕ) (h : a ≤ b) :
    pc T L a ≤ pc T L b := by
  unfold pc
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
  intro j _ _
  exact downStep_nonneg T _ _

theorem pc_succ (T : Tree n) (L : List (Fin n)) (k : ℕ) :
    pc T L (k + 1) = pc T L k + T.downStep (T.vertexAt L k) (T.vertexAt L (k + 1)) := by
  unfold pc; rw [Finset.sum_range_succ]

theorem vA_append_left (T : Tree n) (A Z : List (Fin n)) (j : ℕ) (h : j < A.length) :
    T.vertexAt (A ++ Z) j = T.vertexAt A j := by
  unfold Tree.vertexAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem vA_append_right (T : Tree n) (A Z : List (Fin n)) (k : ℕ) :
    T.vertexAt (A ++ Z) (A.length + k) = T.vertexAt Z k := by
  unfold Tree.vertexAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem vA_cons_succ (T : Tree n) (a : Fin n) (Z : List (Fin n)) (k : ℕ) :
    T.vertexAt (a :: Z) (k + 1) = T.vertexAt Z k := by
  unfold Tree.vertexAt; simp

theorem vA_cons_zero (T : Tree n) (a : Fin n) (Z : List (Fin n)) :
    T.vertexAt (a :: Z) 0 = a := by
  unfold Tree.vertexAt; simp

theorem pc_append_left (T : Tree n) (A Z : List (Fin n)) (k : ℕ) (h : k < A.length) :
    pc T (A ++ Z) k = pc T A k := by
  unfold pc
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [vA_append_left T A Z j (by omega), vA_append_left T A Z (j + 1) (by omega)]

theorem shift_vA (T : Tree n) (L M : List (Fin n)) (hL : L ≠ [])
    (hLM : M.head? = L.getLast?) (k : ℕ) :
    T.vertexAt (L ++ M.tail) (L.length - 1 + k) = T.vertexAt M k := by
  have hlen : 0 < L.length := List.length_pos_iff.mpr hL
  obtain ⟨m, M', rfl⟩ : ∃ m M', M = m :: M' := by
    cases M with
    | nil => simp [List.getLast?_eq_some_getLast hL] at hLM
    | cons m M' => exact ⟨m, M', rfl⟩
  cases k with
  | zero =>
    rw [Nat.add_zero, vA_append_left T L _ _ (by omega), vA_cons_zero]
    have h1 : L.getLast? = some m := by rw [← hLM]; rfl
    rw [List.getLast?_eq_some_getLast hL] at h1
    have h2 : L.getLast hL = m := Option.some.inj h1
    unfold Tree.vertexAt
    rw [← h2, List.getLast_eq_getElem]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show L.length - 1 < L.length by omega)]
  | succ k =>
    rw [show L.length - 1 + (k + 1) = L.length + k by omega, vA_append_right, vA_cons_succ]
    rfl

theorem pc_shift (T : Tree n) (L M : List (Fin n)) (hL : L ≠ [])
    (hLM : M.head? = L.getLast?) (k : ℕ) :
    pc T (L ++ M.tail) (L.length - 1 + k) = dc T L + pc T M k := by
  have hlen : 0 < L.length := List.length_pos_iff.mpr hL
  unfold pc
  rw [Finset.sum_range_add]
  congr 1
  · rw [dc_eq]
    exact pc_append_left T L M.tail _ (by omega)
  · apply Finset.sum_congr rfl
    intro j _
    rw [shift_vA T L M hL hLM, Nat.add_assoc, shift_vA T L M hL hLM]

theorem M_ne_nil (L M : List (Fin n)) (hL : L ≠ []) (hLM : M.head? = L.getLast?) : M ≠ [] := by
  rintro rfl
  simp [List.getLast?_eq_some_getLast hL] at hLM

theorem cross_append_left (T : Tree n) (L M : List (Fin n)) (e : Fin n) (j : ℕ)
    (hj : j + 1 < L.length) : T.CrossAt (L ++ M) e j ↔ T.CrossAt L e j := by
  unfold Tree.CrossAt Tree.DownAt Tree.UpAt
  rw [vA_append_left T L M j (by omega), vA_append_left T L M (j + 1) hj]
  simp only [List.length_append]
  constructor
  · rintro (⟨a, _, c, d⟩ | ⟨a, _, c, d⟩)
    · exact Or.inl ⟨a, hj, c, d⟩
    · exact Or.inr ⟨a, hj, c, d⟩
  · rintro (⟨a, _, c, d⟩ | ⟨a, _, c, d⟩)
    · exact Or.inl ⟨a, by omega, c, d⟩
    · exact Or.inr ⟨a, by omega, c, d⟩

theorem cross_lt (T : Tree n) (L : List (Fin n)) (e : Fin n) (j : ℕ)
    (h : T.CrossAt L e j) : j + 1 < L.length := by
  rcases h with h | h
  · exact h.2.1
  · exact h.2.1

theorem cross_shift (T : Tree n) (L M : List (Fin n)) (hL : L ≠ [])
    (hLM : M.head? = L.getLast?) (e : Fin n) (i : ℕ) (h : T.CrossAt M e i) :
    T.CrossAt (L ++ M.tail) e (L.length - 1 + i) := by
  have hlen : 0 < L.length := List.length_pos_iff.mpr hL
  have hlt : (L ++ M.tail).length = L.length - 1 + M.length := by
    have := List.length_pos_iff.mpr (M_ne_nil L M hL hLM)
    simp only [List.length_append, List.length_tail]; omega
  unfold Tree.CrossAt Tree.DownAt Tree.UpAt at *
  rw [hlt, shift_vA T L M hL hLM, Nat.add_assoc, shift_vA T L M hL hLM]
  rcases h with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · exact Or.inl ⟨a, by omega, c, d⟩
  · exact Or.inr ⟨a, by omega, c, d⟩

/-! ### Part A stubs -/
theorem VB_of_cross (T : Tree n) (L : List (Fin n)) (e : Fin n) (j : ℕ) (c : ℝ)
    (h : T.CrossAt L e j) (hc : T.downPrefix L j ≤ c) : VB T L e c := by
  have hex : ∃ j, T.CrossAt L e j := ⟨j, h⟩
  refine ⟨Nat.find hex, ⟨Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩, ?_⟩
  refine le_trans ?_ hc
  rw [downPrefix_eq, downPrefix_eq]
  exact pc_mono T L _ _ (by have := Nat.find_min' hex h; omega)

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem VB_append_left (T : Tree n) (L M : List (Fin n)) (e : Fin n) (c : ℝ)
    (h : VB T L e c) : VB T (L ++ M) e c := by
  obtain ⟨i, ⟨hi, hmin⟩, hc⟩ := h
  have hlt := cross_lt T L e i hi
  refine ⟨i, ⟨(cross_append_left T L M e i hlt).mpr hi, fun j hj hcj => hmin j hj
    ((cross_append_left T L M e j (by omega)).mp hcj)⟩, ?_⟩
  rw [downPrefix_eq, pc_append_left T L M _ hlt]
  exact hc

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem VB_append_right (T : Tree n) (L M : List (Fin n)) (e : Fin n) (c : ℝ)
    (hL : L ≠ []) (hM : M.head? = L.getLast?) (h : VB T M e c) :
    VB T (L ++ M.tail) e (dc T L + c) := by
  obtain ⟨i, ⟨hi, _⟩, hc⟩ := h
  apply VB_of_cross T _ e _ _ (cross_shift T L M hL hM e i hi)
  rw [downPrefix_eq, Nat.add_assoc, pc_shift T L M hL hM, ← downPrefix_eq]
  linarith

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem isPath_append (T : Tree n) (L M : List (Fin n)) (hL : IsPath T L) (hM : IsPath T M)
    (hLM : M.head? = L.getLast?) : IsPath T (L ++ M.tail) := by
  intro j hj
  rcases eq_or_ne L [] with rfl | hL0
  · simp at hLM
    subst hLM; simp at hj
  have hlen : 0 < L.length := List.length_pos_iff.mpr hL0
  have hMl := List.length_pos_iff.mpr (M_ne_nil L M hL0 hLM)
  have hlt : (L ++ M.tail).length = L.length - 1 + M.length := by
    simp only [List.length_append, List.length_tail]; omega
  by_cases hjL : j + 1 < L.length
  · rw [vA_append_left T L _ _ (by omega), vA_append_left T L _ _ hjL]
    exact hL j hjL
  · obtain ⟨k, rfl⟩ : ∃ k, j = L.length - 1 + k := ⟨j - (L.length - 1), by omega⟩
    rw [shift_vA T L M hL0 hLM, Nat.add_assoc, shift_vA T L M hL0 hLM]
    exact hM k (by omega)

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem dc_append (T : Tree n) (L M : List (Fin n)) (hL : L ≠ [])
    (hLM : M.head? = L.getLast?) : dc T (L ++ M.tail) = dc T L + dc T M := by
  have hlen : 0 < L.length := List.length_pos_iff.mpr hL
  have hMl := List.length_pos_iff.mpr (M_ne_nil L M hL hLM)
  rw [dc_eq, dc_eq T M, ← pc_shift T L M hL hLM]
  congr 1
  simp only [List.length_append, List.length_tail]; omega

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem getLast_append_tail (L M : List (Fin n)) (hL : L ≠ [])
    (hLM : M.head? = L.getLast?) : (L ++ M.tail).getLast? = M.getLast? := by
  obtain ⟨m, M', rfl⟩ : ∃ m M', M = m :: M' := by
    cases M with
    | nil => simp [List.getLast?_eq_some_getLast hL] at hLM
    | cons m M' => exact ⟨m, M', rfl⟩
  rcases eq_or_ne M' [] with rfl | hM'
  · simp only [List.tail_cons, List.append_nil]
    rw [← hLM]; rfl
  · simp only [List.tail_cons]
    rw [List.getLast?_append_of_ne_nil _ hM', List.getLast?_cons, List.getLast?_eq_some_getLast hM']
    rfl

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem head_append (L M : List (Fin n)) (hL : L ≠ []) : (L ++ M).head? = L.head? := by
  cases L with
  | nil => exact absurd rfl hL
  | cons a L => rfl

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
/-! ### Upward path -/
theorem downStep_parent (T : Tree n) (u : Fin n) : T.downStep u (T.parent u) = 0 := by
  unfold Tree.downStep
  rw [if_neg]
  rintro ⟨h1, h2⟩
  have hu : u ≠ T.root := by
    rintro rfl; exact h1 T.parent_root
  have d1 := T.depth_parent u hu
  have d2 := T.depth_parent (T.parent u) h1
  rw [h2] at d2
  omega

theorem iter_depth (T : Tree n) : ∀ (k : ℕ) (v : Fin n), T.depth v = k →
    T.parent^[k] v = T.root := by
  intro k
  induction k with
  | zero =>
    intro v hv
    by_contra hne
    have := T.depth_parent v hne
    simp at hne
    omega
  | succ k ih =>
    intro v hv
    have hne : v ≠ T.root := by
      rintro rfl; rw [T.depth_root] at hv; omega
    have := T.depth_parent v hne
    rw [Function.iterate_succ_apply]
    exact ih _ (by omega)

theorem depth_iter (T : Tree n) (v : Fin n) : ∀ i, i ≤ T.depth v →
    T.depth (T.parent^[i] v) + i = T.depth v := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have hne : T.parent^[i] v ≠ T.root := by
      intro h; rw [h, T.depth_root] at h1; omega
    have := T.depth_parent _ hne
    rw [Function.iterate_succ_apply']
    omega

theorem iter_ne_root (T : Tree n) (v : Fin n) (i : ℕ) (hi : i < T.depth v) :
    T.parent^[i] v ≠ T.root := by
  intro h
  have := depth_iter T v i hi.le
  rw [h, T.depth_root] at this
  omega

theorem vA_up (T : Tree n) (v : Fin n) (i : ℕ) (hi : i < T.depth v + 1) :
    T.vertexAt ((List.range (T.depth v + 1)).map (fun i => T.parent^[i] v)) i =
      T.parent^[i] v := by
  unfold Tree.vertexAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

/-! ## Blocks: inserting closed detours into a path (Part A) -/
/-- Replace the `i`-th vertex of `L` by the closed path `D i` at it. -/
noncomputable def blocks (L : List (Fin n)) (D : ℕ → List (Fin n)) : List (Fin n) :=
  ((List.range L.length).map D).flatten

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
/-! ### Junctions -/
theorem vA_head (T : Tree n) (X : List (Fin n)) (x : Fin n) (h : X.head? = some x) :
    T.vertexAt X 0 = x := by
  cases X with
  | nil => simp at h
  | cons y X => simp at h; subst h; exact vA_cons_zero T _ _

theorem cons_eq_pair (a c : Fin n) (C : List (Fin n)) (hC : C.head? = some c) :
    a :: C = [a, c] ++ C.tail := by
  cases C with
  | nil => simp at hC
  | cons y C => simp at hC; subst hC; rfl

theorem dc_pair (T : Tree n) (a c : Fin n) : dc T [a, c] = T.downStep a c := by
  simp [dc, Tree.vertexAt]

theorem dc_cons (T : Tree n) (a c : Fin n) (C : List (Fin n)) (hC : C.head? = some c) :
    dc T (a :: C) = T.downStep a c + dc T C := by
  rw [cons_eq_pair a c C hC, dc_append T [a, c] C (by simp) (by rw [hC]; rfl), dc_pair]

theorem dc_junction (T : Tree n) (A C : List (Fin n)) (a c : Fin n) (hA : A ≠ [])
    (ha : A.getLast? = some a) (hc : C.head? = some c) :
    dc T (A ++ C) = dc T A + T.downStep a c + dc T C := by
  have h1 := dc_append T A (a :: C) hA (by rw [ha]; rfl)
  rw [List.tail_cons] at h1
  rw [h1, dc_cons T a c C hc, add_assoc]

theorem isPath_junction (T : Tree n) (A C : List (Fin n)) (a c : Fin n)
    (ha : A.getLast? = some a) (hc : C.head? = some c)
    (hpA : IsPath T A) (hadj : T.Adj a c) (hpC : IsPath T C) : IsPath T (A ++ C) := by
  have hp2 : IsPath T [a, c] := by
    intro i hi
    simp at hi
    subst hi
    simpa [Tree.vertexAt] using hadj
  have h1 : IsPath T (a :: C) := by
    rw [cons_eq_pair a c C hc]
    exact isPath_append T [a, c] C hp2 hpC (by rw [hc]; rfl)
  have h2 := isPath_append T A (a :: C) hpA h1 (by rw [ha]; rfl)
  rwa [List.tail_cons] at h2

theorem VB_junction (T : Tree n) (A C : List (Fin n)) (a c : Fin n) (hA : A ≠ [])
    (ha : A.getLast? = some a) (hc : C.head? = some c) (e : Fin n) (x : ℝ)
    (h : VB T C e x) : VB T (A ++ C) e (dc T A + (T.downStep a c + x)) := by
  have h1 : VB T (a :: C) e (T.downStep a c + x) := by
    have := VB_append_right T [a, c] C e x (by simp) (by rw [hc]; rfl) h
    rwa [← cons_eq_pair a c C hc, dc_pair] at this
  have h2 := VB_append_right T A (a :: C) e _ hA (by rw [ha]; rfl) h1
  rwa [List.tail_cons] at h2

/-! ### Blocks -/
noncomputable def B (D : ℕ → List (Fin n)) (k : ℕ) : List (Fin n) :=
  ((List.range k).map D).flatten

theorem B_succ (D : ℕ → List (Fin n)) (k : ℕ) : B D (k + 1) = B D k ++ D k := by
  simp [B, List.range_succ]

theorem B_one (D : ℕ → List (Fin n)) : B D 1 = D 0 := by
  simp [B]

theorem B_prefix (D : ℕ → List (Fin n)) (k m : ℕ) (h : k ≤ m) :
    ∃ Z, B D m = B D k ++ Z := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ m _ ih =>
    obtain ⟨Z, hZ⟩ := ih
    exact ⟨Z ++ D m, by rw [B_succ, hZ, List.append_assoc]⟩

theorem blocks_eq (L : List (Fin n)) (D : ℕ → List (Fin n)) : blocks L D = B D L.length := rfl

theorem closed_ne_nil (T : Tree n) (v : Fin n) (M : List (Fin n)) (h : ClosedAt T v M) :
    M ≠ [] := by
  rintro rfl; simp [ClosedAt] at h

theorem B_inv (T : Tree n) (L : List (Fin n)) (D : ℕ → List (Fin n))
    (hD : ∀ i < L.length, ClosedAt T (T.vertexAt L i) (D i)) :
    ∀ k, k + 1 ≤ L.length →
      B D (k + 1) ≠ [] ∧ (B D (k + 1)).head? = some (T.vertexAt L 0) ∧
      (B D (k + 1)).getLast? = some (T.vertexAt L k) ∧
      dc T (B D (k + 1)) = pc T L k + ∑ j ∈ Finset.range (k + 1), dc T (D j) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 := hD 0 (by omega)
    rw [B_one]
    refine ⟨closed_ne_nil T _ _ h0, h0.1, h0.2.1, ?_⟩
    simp [pc]
  | succ k ih =>
    intro hk
    obtain ⟨hne, hh, hl, hdc⟩ := ih (by omega)
    have hk1 := hD (k + 1) (by omega)
    have hCne := closed_ne_nil T _ _ hk1
    rw [B_succ]
    refine ⟨by simp [hne], by rw [head_append _ _ hne, hh], ?_, ?_⟩
    · rw [List.getLast?_append_of_ne_nil _ hCne, hk1.2.1]
    · rw [dc_junction T _ _ _ _ hne hl hk1.1, hdc, pc_succ, Finset.sum_range_succ _ (k + 1)]
      ring

theorem B_isPath (T : Tree n) (L : List (Fin n)) (D : ℕ → List (Fin n)) (hL : IsPath T L)
    (hD : ∀ i < L.length, ClosedAt T (T.vertexAt L i) (D i)) :
    ∀ k, k + 1 ≤ L.length → IsPath T (B D (k + 1)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [B_one]; exact (hD 0 (by omega)).2.2
  | succ k ih =>
    intro hk
    obtain ⟨_, _, hl, _⟩ := B_inv T L D hD k (by omega)
    have hk1 := hD (k + 1) (by omega)
    rw [B_succ]
    exact isPath_junction T _ _ _ _ hl hk1.1 (ih (by omega)) (hL k (by omega)) hk1.2.2

theorem blocks_head (T : Tree n) (L : List (Fin n)) (D : ℕ → List (Fin n))
    (hD : ∀ i < L.length, ClosedAt T (T.vertexAt L i) (D i)) :
    (blocks L D).head? = L.head? := by
  cases L with
  | nil => simp [blocks]
  | cons a L =>
    have := (B_inv T (a :: L) D hD L.length (by simp)).2.1
    rw [blocks_eq]
    simp only [List.length_cons] at this ⊢
    rw [this, vA_cons_zero]; rfl

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem blocks_isPath (T : Tree n) (L : List (Fin n)) (D : ℕ → List (Fin n))
    (hL : IsPath T L) (hD : ∀ i < L.length, ClosedAt T (T.vertexAt L i) (D i)) :
    IsPath T (blocks L D) := by
  cases L with
  | nil => intro i hi; simp [blocks] at hi
  | cons a L =>
    have := B_isPath T (a :: L) D hL hD L.length (by simp)
    rw [blocks_eq]
    simpa using this

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem blocks_step (T : Tree n) (L : List (Fin n)) (D : ℕ → List (Fin n))
    (hD : ∀ i < L.length, ClosedAt T (T.vertexAt L i) (D i)) (i : ℕ) (hi : i + 1 < L.length) :
    ∃ p, p + 1 < (blocks L D).length ∧
      T.vertexAt (blocks L D) p = T.vertexAt L i ∧
      T.vertexAt (blocks L D) (p + 1) = T.vertexAt L (i + 1) ∧
      T.downPrefix (blocks L D) p =
        T.downPrefix L i + ∑ j ∈ Finset.range (i + 1), dc T (D j) := by
  obtain ⟨hne, _, hl, hdc⟩ := B_inv T L D hD i (by omega)
  have hC := hD (i + 1) hi
  have hCne := closed_ne_nil T _ _ hC
  obtain ⟨Z, hZ⟩ := B_prefix D (i + 2) L.length (by omega)
  rw [B_succ] at hZ
  set A := B D (i + 1) with hAdef
  set a := T.vertexAt L i with hadef
  set Y := D (i + 1) ++ Z with hYdef
  have hbl : blocks L D = A ++ (a :: Y).tail := by
    rw [blocks_eq, hZ, List.tail_cons, List.append_assoc]
  have hlink : (a :: Y).head? = A.getLast? := by rw [hl]; rfl
  have hAl : 0 < A.length := List.length_pos_iff.mpr hne
  have hCl : 0 < (D (i + 1)).length := List.length_pos_iff.mpr hCne
  have hY0 : T.vertexAt Y 0 = T.vertexAt L (i + 1) := by
    rw [hYdef, vA_append_left T _ _ 0 hCl]
    exact vA_head T _ _ hC.1
  refine ⟨A.length - 1, ?_, ?_, ?_, ?_⟩
  · rw [hbl]; simp [hYdef]; omega
  · rw [hbl, ← Nat.add_zero (A.length - 1), shift_vA T A _ hne hlink, vA_cons_zero]
  · rw [hbl, shift_vA T A _ hne hlink, vA_cons_succ, hY0]
  · rw [downPrefix_eq, hbl, pc_shift T A _ hne hlink, hdc, downPrefix_eq, pc_succ T L i,
      pc_succ, vA_cons_zero, vA_cons_succ, hY0]
    simp [pc]
    ring

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartA
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem dc_take (T : Tree n) (L : List (Fin n)) (k : ℕ) (hk : k < L.length) :
    dc T (L.take (k + 1)) = pc T L k := by
  have hlen : (L.take (k + 1)).length = k + 1 := by simp; omega
  rw [dc_eq, hlen, Nat.add_sub_cancel]
  have := pc_append_left T (L.take (k + 1)) (L.drop (k + 1)) k (by omega)
  rw [List.take_append_drop] at this
  exact this.symm

theorem blocks_VB (T : Tree n) (L : List (Fin n)) (D : ℕ → List (Fin n))
    (hD : ∀ i < L.length, ClosedAt T (T.vertexAt L i) (D i)) (i : ℕ) (hi : i < L.length)
    (e : Fin n) (c : ℝ) (h : VB T (D i) e c) :
    VB T (blocks L D) e (dc T (L.take (i + 1)) + ∑ j ∈ Finset.range i, dc T (D j) + c) := by
  obtain ⟨Z, hZ⟩ := B_prefix D (i + 1) L.length (by omega)
  rw [blocks_eq, hZ, dc_take T L i hi]
  cases i with
  | zero =>
    rw [B_one]
    have := VB_append_left T (D 0) Z e c h
    refine VB_mono T _ e _ _ this (le_of_eq ?_)
    simp [pc]
  | succ i =>
    obtain ⟨hne, _, hl, hdc⟩ := B_inv T L D hD i (by omega)
    have hC := hD (i + 1) hi
    rw [B_succ]
    have := VB_append_left T _ Z e _ (VB_junction T _ _ _ _ hne hl hC.1 e c h)
    refine VB_mono T _ e _ _ this (le_of_eq ?_)
    rw [hdc, pc_succ]
    ring

end OnlineTransportation1195.Dev.T31.PartA
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

/-! ## Restricted depth-first search (Part B) -/
noncomputable def children (T : Tree n) (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun c => decide (c ≠ T.root ∧ T.parent c = v))

/-- Depth-first search from `v` using only the child edges in `S`, with fuel. -/
noncomputable def dfsF (T : Tree n) (S : Finset (Fin n)) : ℕ → Fin n → List (Fin n)
  | 0, v => [v]
  | k + 1, v => v :: ((children T v).filter (fun c => decide (c ∈ S))).flatMap
      (fun c => dfsF T S k c ++ [v])

noncomputable def dfsS (T : Tree n) (S : Finset (Fin n)) (v : Fin n) : List (Fin n) :=
  dfsF T S n v

/-- The edge `e` hangs below `v` and every edge from `v` down to `e` lies in `S`. -/
def Reach (T : Tree n) (S : Finset (Fin n)) (v e : Fin n) : Prop :=
  e ∈ S ∧ e ≠ v ∧ T.IsAnc v e ∧
    ∀ f, f ≠ T.root → f ≠ v → T.IsAnc v f → T.IsAnc f e → f ∈ S

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
/-! ## Step sums -/
/-- Sum of a function over the consecutive steps of a list. -/
noncomputable def SS {M : Type} [AddCommMonoid M] (T : Tree n) (φ : Fin n → Fin n → M)
    (L : List (Fin n)) : M :=
  ∑ j ∈ Finset.range (L.length - 1), φ (T.vertexAt L j) (T.vertexAt L (j + 1))

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
variable {M : Type} [AddCommMonoid M] (T : Tree n) (φ : Fin n → Fin n → M)
theorem SS_single (a : Fin n) : SS T φ [a] = 0 := by simp [SS]

theorem SS_cons2 (a b : Fin n) (L : List (Fin n)) :
    SS T φ (a :: b :: L) = φ a b + SS T φ (b :: L) := by
  simp only [SS, List.length_cons]
  rw [show L.length + 1 + 1 - 1 = L.length + 1 by omega, Finset.sum_range_succ',
    show L.length + 1 - 1 = L.length by omega]
  rw [add_comm]; rfl

theorem SS_append (L : List (Fin n)) (u b : Fin n) (R : List (Fin n))
    (hL : L.getLast? = some u) :
    SS T φ (L ++ b :: R) = SS T φ L + φ u b + SS T φ (b :: R) := by
  induction L with
  | nil => simp at hL
  | cons a L ih =>
    cases L with
    | nil =>
      simp at hL; subst hL
      simp [SS_cons2, SS_single]
    | cons a' L =>
      rw [List.getLast?_cons_cons] at hL
      rw [List.cons_append, List.cons_append, SS_cons2, ← List.cons_append, ih hL, SS_cons2]
      simp only [add_assoc]

theorem SS_flatMap (v : Fin n) (cs : List (Fin n)) (A : Fin n → List (Fin n))
    (hA : ∀ c ∈ cs, (A c).head? = some c ∧ (A c).getLast? = some c) :
    SS T φ (v :: cs.flatMap (fun c => A c ++ [v])) =
      (cs.map (fun c => φ v c + SS T φ (A c) + φ c v)).sum := by
  induction cs with
  | nil => simp [SS_single]
  | cons c cs ih =>
    have h1 := hA c (by simp)
    have ih' := ih (fun c' hc' => hA c' (by simp [hc']))
    obtain ⟨A', hA'⟩ : ∃ A', A c = c :: A' := by
      cases h : A c with
      | nil => rw [h] at h1; simp at h1
      | cons x A' => rw [h] at h1; simp at h1; exact ⟨A', by rw [h1.1]⟩
    have e1 : v :: (c :: cs).flatMap (fun c => A c ++ [v]) =
        (v :: A c) ++ v :: cs.flatMap (fun c => A c ++ [v]) := by simp
    have hl : (v :: A c).getLast? = some c := by
      rw [hA', List.getLast?_cons_cons, ← hA']; exact h1.2
    rw [e1, SS_append T φ _ c v _ hl, ih', List.map_cons, List.sum_cons, hA', SS_cons2]

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem getLast_flatMap (v : Fin n) (cs : List (Fin n)) (A : Fin n → List (Fin n)) :
    (v :: cs.flatMap (fun c => A c ++ [v])).getLast? = some v := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have e1 : v :: (c :: cs).flatMap (fun c => A c ++ [v]) =
        (v :: A c) ++ v :: cs.flatMap (fun c => A c ++ [v]) := by simp
    rw [e1, List.getLast?_append, ih]
    rfl

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
variable (T : Tree n) (S : Finset (Fin n))
/-! ## DFS structure -/
theorem dfsF_succ (k : ℕ) (v : Fin n) :
    dfsF T S (k + 1) v = v :: ((children T v).filter (fun c => decide (c ∈ S))).flatMap
      (fun c => dfsF T S k c ++ [v]) := rfl

theorem dfsF_head (k : ℕ) (v : Fin n) : (dfsF T S k v).head? = some v := by
  cases k <;> rfl

theorem dfsF_last (k : ℕ) (v : Fin n) : (dfsF T S k v).getLast? = some v := by
  cases k with
  | zero => rfl
  | succ k => rw [dfsF_succ]; exact getLast_flatMap v _ _

theorem mem_cs (v c : Fin n) :
    c ∈ (children T v).filter (fun c => decide (c ∈ S)) ↔
      (c ≠ T.root ∧ T.parent c = v) ∧ c ∈ S := by
  simp [children]; tauto

theorem nodup_cs (v : Fin n) : ((children T v).filter (fun c => decide (c ∈ S))).Nodup :=
  ((List.nodup_finRange n).filter _).filter _

theorem SS_dfsF_succ {M : Type} [AddCommMonoid M] (φ : Fin n → Fin n → M) (k : ℕ) (v : Fin n) :
    SS T φ (dfsF T S (k + 1) v) =
      ∑ c ∈ ((children T v).filter (fun c => decide (c ∈ S))).toFinset,
        (φ v c + SS T φ (dfsF T S k c) + φ c v) := by
  rw [dfsF_succ, SS_flatMap T φ v _ _ (fun c _ => ⟨dfsF_head T S k c, dfsF_last T S k c⟩),
    List.sum_toFinset _ (nodup_cs T S v)]

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
variable (T : Tree n)
/-! ## Tree facts -/
theorem depth_eq_zero {e : Fin n} (h : T.depth e = 0) : e = T.root := by
  by_contra hne
  have := T.depth_parent e hne
  omega

theorem depth_child {c : Fin n} (hc : c ≠ T.root) : T.depth c = T.depth (T.parent c) + 1 :=
  (T.depth_parent c hc).symm

theorem depth_iter (e : Fin n) : ∀ i, T.depth (T.parent^[i] e) = T.depth e - i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    by_cases hx : T.parent^[i] e = T.root
    · rw [hx, T.parent_root, T.depth_root]
      rw [hx, T.depth_root] at ih
      omega
    · have := T.depth_parent _ hx
      omega

theorem iter_root (i : ℕ) : T.parent^[i] T.root = T.root :=
  Function.iterate_fixed T.parent_root i

theorem iter_depth (e : Fin n) : T.parent^[T.depth e] e = T.root :=
  depth_eq_zero T (by rw [depth_iter]; simp)

theorem anc_eq {a e : Fin n} (h : T.IsAnc a e) :
    a = T.parent^[T.depth e - T.depth a] e ∧ T.depth a ≤ T.depth e := by
  obtain ⟨i, rfl⟩ := h
  rw [depth_iter]
  by_cases hi : i ≤ T.depth e
  · refine ⟨?_, by omega⟩
    congr 1; omega
  · have h1 : T.parent^[i] e = T.root := by
      rw [show i = (i - T.depth e) + T.depth e by omega, Function.iterate_add_apply,
        iter_depth, iter_root]
    refine ⟨?_, by omega⟩
    rw [h1, show T.depth e - (T.depth e - i) = T.depth e by omega, iter_depth]

theorem anc_refl (a : Fin n) : T.IsAnc a a := ⟨0, rfl⟩

theorem anc_parent {c : Fin n} : T.IsAnc (T.parent c) c := ⟨1, rfl⟩

theorem anc_trans' {a b c : Fin n} (h1 : T.IsAnc a b) (h2 : T.IsAnc b c) : T.IsAnc a c := by
  obtain ⟨i, rfl⟩ := h1
  obtain ⟨j, rfl⟩ := h2
  exact ⟨i + j, by rw [Function.iterate_add_apply]⟩

theorem anc_of_depth {a b e : Fin n} (ha : T.IsAnc a e) (hb : T.IsAnc b e)
    (hd : T.depth a ≤ T.depth b) : T.IsAnc a b := by
  obtain ⟨ha1, ha2⟩ := anc_eq T ha
  obtain ⟨hb1, hb2⟩ := anc_eq T hb
  refine ⟨T.depth b - T.depth a, ?_⟩
  have h3 : T.parent^[T.depth b - T.depth a] (T.parent^[T.depth e - T.depth b] e) =
      T.parent^[T.depth e - T.depth a] e := by
    rw [← Function.iterate_add_apply]; congr 1; omega
  rw [← hb1] at h3
  exact h3.trans ha1.symm

theorem anc_eq_of_depth {a b e : Fin n} (ha : T.IsAnc a e) (hb : T.IsAnc b e)
    (hd : T.depth a = T.depth b) : a = b := by
  rw [(anc_eq T ha).1, (anc_eq T hb).1, hd]

theorem anc_lt {a e : Fin n} (h : T.IsAnc a e) (hne : a ≠ e) : T.depth a < T.depth e := by
  rcases lt_or_eq_of_le (anc_eq T h).2 with h1 | h1
  · exact h1
  · exact absurd (anc_eq_of_depth T h (anc_refl T e) h1) hne

theorem no2cycle {c : Fin n} (hc : c ≠ T.root) : T.parent (T.parent c) ≠ c := by
  intro h
  by_cases hp : T.parent c = T.root
  · rw [hp, T.parent_root] at h; exact hc h.symm
  · have h1 := T.depth_parent _ hp
    have h2 := T.depth_parent _ hc
    rw [h] at h1
    omega

theorem depth_lt (e : Fin n) : T.depth e < n := by
  have hinj : Function.Injective (fun i : Fin (T.depth e + 1) => T.parent^[i] e) := by
    intro i j hij
    have := congrArg T.depth hij
    simp only [depth_iter] at this
    ext; omega
  have := Fintype.card_le_of_injective _ hinj
  simp at this
  omega

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
variable (T : Tree n) (S : Finset (Fin n))
/-! ## Reachability decomposition -/
theorem reach_depth {v e : Fin n} (h : Reach T S v e) : T.depth v < T.depth e :=
  anc_lt T h.2.2.1 (fun h' => h.2.1 h'.symm)

theorem reach_iff (v e : Fin n) :
    Reach T S v e ↔ ∃ c, ((c ≠ T.root ∧ T.parent c = v) ∧ c ∈ S) ∧ (c = e ∨ Reach T S c e) := by
  constructor
  · rintro ⟨heS, hev, hve, hpath⟩
    have hd := anc_lt T hve (fun h => hev h.symm)
    set c := T.parent^[T.depth e - T.depth v - 1] e with hcdef
    have hce : T.IsAnc c e := ⟨_, rfl⟩
    have hdc : T.depth c = T.depth v + 1 := by rw [hcdef, depth_iter]; omega
    have hcr : c ≠ T.root := by
      intro h; rw [h, T.depth_root] at hdc; omega
    have hvc : T.IsAnc v c := anc_of_depth T hve hce (by omega)
    have hpc : T.parent c = v := by
      refine anc_eq_of_depth T (anc_trans' T (anc_parent T) hce) hve ?_
      have := depth_child T hcr; omega
    have hcv : c ≠ v := by intro h; rw [h] at hdc; omega
    refine ⟨c, ⟨⟨hcr, hpc⟩, hpath c hcr hcv hvc hce⟩, ?_⟩
    by_cases hc : c = e
    · exact Or.inl hc
    · refine Or.inr ⟨heS, fun h => hc h.symm, hce, ?_⟩
      intro f hfr hfc hcf hfe
      refine hpath f hfr ?_ (anc_trans' T hvc hcf) hfe
      intro h; rw [h] at hcf; have := anc_lt T hcf (fun h' => hcv h'); omega
  · rintro ⟨c, ⟨⟨hcr, hpc⟩, hcS⟩, hce⟩
    have hce' : T.IsAnc c e := by
      rcases hce with h | h
      · rw [h]; exact anc_refl T e
      · exact h.2.2.1
    have heS : e ∈ S := by
      rcases hce with h | h
      · rw [← h]; exact hcS
      · exact h.1
    have hdc := depth_child T hcr
    rw [hpc] at hdc
    have hdce := (anc_eq T hce').2
    have hvc : T.IsAnc v c := by rw [← hpc]; exact anc_parent T
    refine ⟨heS, ?_, anc_trans' T hvc hce', ?_⟩
    · intro h; rw [h] at hdce; omega
    · intro f hfr hfv hvf hfe
      have hdf := anc_lt T hvf (fun h => hfv h.symm)
      by_cases hle : T.depth f ≤ T.depth c
      · have : f = c := anc_eq_of_depth T hfe hce' (by omega)
        rw [this]; exact hcS
      · have hcf := anc_of_depth T hce' hfe (by omega)
        rcases hce with h | h
        · have := (anc_eq T hfe).2; rw [← h] at this; omega
        · exact h.2.2.2 f hfr (fun h' => by rw [h'] at hle; omega) hcf hfe

theorem child_unique {v c c' e : Fin n} (hc : c ≠ T.root ∧ T.parent c = v)
    (hc' : c' ≠ T.root ∧ T.parent c' = v) (he : T.IsAnc c e) (he' : T.IsAnc c' e) : c = c' := by
  refine anc_eq_of_depth T he he' ?_
  rw [depth_child T hc.1, depth_child T hc'.1, hc.2, hc'.2]

theorem cond_anc {c e : Fin n} (h : c = e ∨ Reach T S c e) : T.IsAnc c e := by
  rcases h with h | h
  · rw [h]; exact anc_refl T e
  · exact h.2.2.1

/-- The per-edge count of a step pattern along a DFS. -/
theorem count_dfsF (e : Fin n) (φ : Fin n → Fin n → ℕ)
    (hφ : ∀ c, c ≠ T.root → φ (T.parent c) c + φ c (T.parent c) = if c = e then 1 else 0) :
    ∀ k v, T.depth e < T.depth v + k →
      SS T φ (dfsF T S k v) = if Reach T S v e then 1 else 0 := by
  intro k
  induction k with
  | zero =>
    intro v hk
    have : ¬ Reach T S v e := fun h => by have := reach_depth T S h; omega
    rw [if_neg this]
    exact SS_single T φ v
  | succ k ih =>
    intro v hk
    rw [SS_dfsF_succ]
    have hterm : ∀ c ∈ ((children T v).filter (fun c => decide (c ∈ S))).toFinset,
        φ v c + SS T φ (dfsF T S k c) + φ c v = if (c = e ∨ Reach T S c e) then 1 else 0 := by
      intro c hc
      rw [List.mem_toFinset, mem_cs] at hc
      obtain ⟨⟨hcr, hpc⟩, _⟩ := hc
      have hd := depth_child T hcr
      rw [ih c (by rw [hpc] at hd; omega)]
      have h1 := hφ c hcr
      rw [hpc] at h1
      by_cases hce : c = e
      · have : ¬ Reach T S c e := fun h => h.2.1 hce.symm
        simp only [if_neg this, if_pos (Or.inl hce : c = e ∨ Reach T S c e)]
        rw [if_pos hce] at h1; omega
      · rw [if_neg hce] at h1
        by_cases hr : Reach T S c e
        · simp only [if_pos hr, if_pos (Or.inr hr : c = e ∨ Reach T S c e)]; omega
        · have : ¬ (c = e ∨ Reach T S c e) := by tauto
          simp only [if_neg hr, if_neg this]; omega
    rw [Finset.sum_congr rfl hterm]
    by_cases hR : Reach T S v e
    · rw [if_pos hR]
      obtain ⟨c, hc, hce⟩ := (reach_iff T S v e).mp hR
      rw [Finset.sum_eq_single c]
      · rw [if_pos hce]
      · intro b hb hbc
        rw [List.mem_toFinset, mem_cs] at hb
        rw [if_neg]
        intro hbe
        exact hbc (child_unique T hb.1 hc.1 (cond_anc T S hbe) (cond_anc T S hce))
      · intro hc'
        exact absurd (by rw [List.mem_toFinset, mem_cs]; exact hc) hc'
    · rw [if_neg hR]
      refine Finset.sum_eq_zero ?_
      intro c hc
      rw [List.mem_toFinset, mem_cs] at hc
      rw [if_neg]
      intro hce
      exact hR ((reach_iff T S v e).mpr ⟨c, hc, hce⟩)

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
variable (T : Tree n)
/-! ## Applications -/
/-- Indicator of a non-adjacent step. -/
noncomputable def bad (T : Tree n) (u w : Fin n) : ℕ := if T.Adj u w then 0 else 1

/-- Indicator of a downward step across `e`. -/
noncomputable def dφ (T : Tree n) (e u w : Fin n) : ℕ := if u = T.parent e ∧ w = e then 1 else 0

/-- Indicator of an upward step across `e`. -/
noncomputable def uφ (T : Tree n) (e u w : Fin n) : ℕ := if u = e ∧ w = T.parent e then 1 else 0

theorem isPath_iff (L : List (Fin n)) : IsPath T L ↔ SS T (bad T) L = 0 := by
  unfold SS IsPath
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h j hj
    rw [Finset.mem_range] at hj
    simp [bad, h j (by omega)]
  · intro h i hi
    have := h i (Finset.mem_range.mpr (by omega))
    simp only [bad] at this
    by_contra hc
    rw [if_neg hc] at this
    exact one_ne_zero this

theorem SS_bad_dfsF (S : Finset (Fin n)) : ∀ k v, SS T (bad T) (dfsF T S k v) = 0 := by
  intro k
  induction k with
  | zero => intro v; exact SS_single T _ v
  | succ k ih =>
    intro v
    rw [SS_dfsF_succ]
    refine Finset.sum_eq_zero ?_
    intro c hc
    rw [List.mem_toFinset, mem_cs] at hc
    obtain ⟨⟨hcr, hpc⟩, _⟩ := hc
    have h1 : T.Adj v c := Or.inl ⟨hcr, hpc⟩
    have h2 : T.Adj c v := Or.inr ⟨hcr, hpc⟩
    simp [bad, h1, h2, ih c]

theorem dφ_spec (e : Fin n) (he : e ≠ T.root) :
    ∀ c, c ≠ T.root → dφ T e (T.parent c) c + dφ T e c (T.parent c) = if c = e then 1 else 0 := by
  intro c hc
  have h2 : ¬ (c = T.parent e ∧ T.parent c = e) := by
    rintro ⟨h1, h2⟩
    exact no2cycle T he (by rw [← h1, h2])
  unfold dφ
  rw [if_neg h2]
  by_cases hce : c = e
  · subst hce; simp
  · simp [hce]

theorem uφ_spec (e : Fin n) (he : e ≠ T.root) :
    ∀ c, c ≠ T.root → uφ T e (T.parent c) c + uφ T e c (T.parent c) = if c = e then 1 else 0 := by
  intro c hc
  have h2 : ¬ (T.parent c = e ∧ c = T.parent e) := by
    rintro ⟨h1, h2⟩
    exact no2cycle T he (by rw [← h2, h1])
  unfold uφ
  rw [if_neg h2]
  by_cases hce : c = e
  · subst hce; simp
  · simp [hce]

theorem card_eq_SS (L : List (Fin n)) (P : Fin n → Fin n → Prop) :
    (Finset.univ.filter (fun i : Fin L.length =>
      (i : ℕ) + 1 < L.length ∧ P (T.vertexAt L i) (T.vertexAt L (i + 1)))).card =
      SS T (fun u w => if P u w then 1 else 0) L := by
  rw [Finset.card_filter]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 < L.length ∧
    P (T.vertexAt L i) (T.vertexAt L (i + 1)) then 1 else 0)]
  unfold SS
  rcases Nat.eq_zero_or_eq_succ_pred L.length with h | h
  · rw [h]; simp
  · rw [h, Finset.sum_range_succ, Nat.succ_sub_one]
    rw [if_neg (by omega), add_zero]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_range] at hj
    have : j + 1 < L.length.pred.succ := by omega
    simp only [this, true_and]

theorem card_down (L : List (Fin n)) (e : Fin n) (he : e ≠ T.root) :
    (Finset.univ.filter (fun i : Fin L.length => T.DownAt L e i)).card = SS T (dφ T e) L := by
  have : (Finset.univ.filter (fun i : Fin L.length => T.DownAt L e i)) =
      Finset.univ.filter (fun i : Fin L.length =>
        (i : ℕ) + 1 < L.length ∧ (fun u w => u = T.parent e ∧ w = e)
          (T.vertexAt L i) (T.vertexAt L (i + 1))) := by
    ext i; simp [Tree.DownAt, he]
  rw [this]
  convert card_eq_SS T L (fun u w => u = T.parent e ∧ w = e) using 1
  · congr 1; ext i; simp
  · unfold SS dφ; refine Finset.sum_congr rfl ?_; intro j _; split_ifs <;> simp_all

theorem card_up (L : List (Fin n)) (e : Fin n) (he : e ≠ T.root) :
    (Finset.univ.filter (fun i : Fin L.length => T.UpAt L e i)).card = SS T (uφ T e) L := by
  have : (Finset.univ.filter (fun i : Fin L.length => T.UpAt L e i)) =
      Finset.univ.filter (fun i : Fin L.length =>
        (i : ℕ) + 1 < L.length ∧ (fun u w => u = e ∧ w = T.parent e)
          (T.vertexAt L i) (T.vertexAt L (i + 1))) := by
    ext i; simp [Tree.UpAt, he]
  rw [this]
  convert card_eq_SS T L (fun u w => u = e ∧ w = T.parent e) using 1
  · congr 1; ext i; simp
  · unfold SS uφ; refine Finset.sum_congr rfl ?_; intro j _; split_ifs <;> simp_all

theorem downStep_eq (u w : Fin n) :
    T.downStep u w = ∑ e ∈ T.edges, T.W e * ((dφ T e u w : ℕ) : ℝ) := by
  unfold Tree.downStep
  split_ifs with h
  · rw [Finset.sum_eq_single w]
    · simp [dφ, h.2]
    · intro b _ hb
      simp [dφ, Ne.symm hb]
    · intro hw
      exact absurd (Finset.mem_erase.mpr ⟨h.1, Finset.mem_univ _⟩) hw
  · refine (Finset.sum_eq_zero ?_).symm
    intro e he
    have her : e ≠ T.root := (Finset.mem_erase.mp he).1
    unfold dφ
    rw [if_neg]
    · simp
    · rintro ⟨h1, h2⟩
      subst h2
      exact h ⟨her, h1.symm⟩

theorem dc_eq (L : List (Fin n)) :
    dc T L = ∑ e ∈ T.edges, T.W e * ((SS T (dφ T e) L : ℕ) : ℝ) := by
  unfold dc SS
  simp_rw [downStep_eq T]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro e _
  rw [Nat.cast_sum, Finset.mul_sum]

theorem downStep_nonneg (u w : Fin n) : 0 ≤ T.downStep u w := by
  unfold Tree.downStep
  split_ifs with h
  · exact (T.W_pos w h.1).le
  · exact le_refl _

theorem count_dfsS_down (S : Finset (Fin n)) (v e : Fin n) (he : e ≠ T.root) :
    SS T (dφ T e) (dfsS T S v) = if Reach T S v e then 1 else 0 :=
  count_dfsF T S e (dφ T e) (dφ_spec T e he) n v (by have := depth_lt T e; omega)

theorem count_dfsS_up (S : Finset (Fin n)) (v e : Fin n) (he : e ≠ T.root) :
    SS T (uφ T e) (dfsS T S v) = if Reach T S v e then 1 else 0 :=
  count_dfsF T S e (uφ T e) (uφ_spec T e he) n v (by have := depth_lt T e; omega)

theorem reach_ne_root {S : Finset (Fin n)} {v e : Fin n} (h : Reach T S v e) : e ≠ T.root := by
  intro her
  have := reach_depth T S h
  rw [her, T.depth_root] at this
  omega

/-- A reachable edge is crossed downward somewhere in the DFS. -/
theorem dfsS_cross (S : Finset (Fin n)) (v e : Fin n) (h : Reach T S v e) :
    ∃ j, T.CrossAt (dfsS T S v) e j := by
  have he := reach_ne_root T h
  have h1 := count_dfsS_down T S v e he
  rw [if_pos h] at h1
  by_contra hno
  simp only [not_exists] at hno
  have : SS T (dφ T e) (dfsS T S v) = 0 := by
    unfold SS
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [Finset.mem_range] at hj
    unfold dφ
    rw [if_neg]
    rintro ⟨h2, h3⟩
    exact hno j (Or.inl ⟨he, by omega, h2, h3⟩)
  omega

theorem VB_of_cross_dc (L : List (Fin n)) (e : Fin n) (h : ∃ j, T.CrossAt L e j) :
    VB T L e (dc T L) := by
  refine ⟨Nat.find h, ⟨Nat.find_spec h, fun j hj => Nat.find_min h hj⟩, ?_⟩
  have hlen : Nat.find h + 1 < L.length := by
    rcases Nat.find_spec h with h1 | h1
    · exact h1.2.1
    · exact h1.2.1
  unfold Tree.downPrefix dc
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro j; simp only [Finset.mem_range]; omega
  · intro j _ _; exact downStep_nonneg T _ _

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
/-! ## The stubs -/
theorem dfsS_closed (T : Tree n) (S : Finset (Fin n)) (v : Fin n) :
    ClosedAt T v (dfsS T S v) :=
  ⟨dfsF_head T S n v, dfsF_last T S n v, (isPath_iff T _).mpr (SS_bad_dfsF T S n v)⟩

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem dfsS_VB (T : Tree n) (S : Finset (Fin n)) (hS : S ⊆ T.edges) (v e : Fin n)
    (he : Reach T S v e) : VB T (dfsS T S v) e (dc T (dfsS T S v)) :=
  VB_of_cross_dc T _ e (dfsS_cross T S v e he)

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem dfsS_dc (T : Tree n) (S : Finset (Fin n)) (hS : S ⊆ T.edges) (v : Fin n) :
    dc T (dfsS T S v) = ∑ e ∈ T.edges.filter (fun e => Reach T S v e), T.W e := by
  rw [dc_eq, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro e he
  rw [count_dfsS_down T S v e (Finset.mem_erase.mp he).1]
  split_ifs <;> simp

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartB
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31.PartB
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartD
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}

theorem isAnc_total (T : Tree n) (u u' e : Fin n) (h : T.IsAnc u e) (h' : T.IsAnc u' e) :
    T.IsAnc u u' ∨ T.IsAnc u' u := by
  obtain ⟨i, rfl⟩ := h
  obtain ⟨i', rfl⟩ := h'
  rcases le_total i i' with hii | hii
  · right
    refine ⟨i' - i, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hii]
  · left
    refine ⟨i - i', ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hii]

theorem depth_iterate_le (T : Tree n) (k : ℕ) (x : Fin n) :
    T.depth (T.parent^[k] x) ≤ T.depth x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    refine (ih _).trans ?_
    by_cases hx : x = T.root
    · rw [hx, T.parent_root]
    · have := T.depth_parent x hx; omega

theorem depth_lt_of_isAnc (T : Tree n) (a f : Fin n) (h : T.IsAnc a f) (hne : a ≠ f) :
    T.depth a < T.depth f := by
  obtain ⟨k, rfl⟩ := h
  cases k with
  | zero => exact absurd rfl hne
  | succ k =>
    have hf : f ≠ T.root := by
      rintro rfl
      apply hne
      rw [Function.iterate_fixed T.parent_root]
    rw [Function.iterate_succ_apply]
    have h1 := depth_iterate_le T k (T.parent f)
    have h2 := T.depth_parent f hf
    omega

theorem dc_take (T : Tree n) (L : List (Fin n)) (i : ℕ) (hi : i + 1 < L.length) :
    dc T (L.take (i + 2)) = T.downPrefix L i := by
  unfold dc Tree.downPrefix
  have hlen : (L.take (i + 2)).length - 1 = i + 1 := by simp; omega
  rw [hlen]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hv : ∀ m, m < i + 2 → T.vertexAt (L.take (i + 2)) m = T.vertexAt L m := by
    intro m hm
    simp [Tree.vertexAt, List.getD_eq_getElem?_getD, hm]
  rw [hv j (by omega), hv (j + 1) (by omega)]

end OnlineTransportation1195.Dev.T31.PartD
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
/-! ## The patch-detour walk (Part D) -/

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartC
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
/-! ## The subtree on a parent-closed vertex set -/
noncomputable def embV (V : Finset (Fin n)) (i : Fin V.card) : Fin n := (V.equivFin.symm i).1

noncomputable def backV (T : Tree n) (V : Finset (Fin n)) (hr : T.root ∈ V) (v : Fin n) :
    Fin V.card :=
  if hv : v ∈ V then V.equivFin ⟨v, hv⟩ else V.equivFin ⟨T.root, hr⟩

theorem embV_mem (V : Finset (Fin n)) (i : Fin V.card) : embV V i ∈ V :=
  (V.equivFin.symm i).2

theorem embV_backV (T : Tree n) (V : Finset (Fin n)) (hr : T.root ∈ V) (v : Fin n)
    (hv : v ∈ V) : embV V (backV T V hr v) = v := by
  simp [embV, backV, hv]

theorem backV_embV (T : Tree n) (V : Finset (Fin n)) (hr : T.root ∈ V) (i : Fin V.card) :
    backV T V hr (embV V i) = i := by
  simp [embV, backV]

theorem embV_inj (V : Finset (Fin n)) : Function.Injective (embV V) := by
  intro a b h
  exact V.equivFin.symm.injective (Subtype.ext h)

noncomputable def subT (T : Tree n) (V : Finset (Fin n)) (hr : T.root ∈ V)
    (hp : ∀ v ∈ V, T.parent v ∈ V) : Tree V.card where
  root := backV T V hr T.root
  parent := fun i => backV T V hr (T.parent (embV V i))
  depth := fun i => T.depth (embV V i)
  parent_root := by
    simp only [embV_backV T V hr _ hr, T.parent_root]
  depth_root := by
    simp only [embV_backV T V hr _ hr, T.depth_root]
  depth_parent := by
    intro v hv
    have hne : embV V v ≠ T.root := fun h => hv (by rw [← h, backV_embV])
    simp only [embV_backV T V hr _ (hp _ (embV_mem V v))]
    exact T.depth_parent _ hne
  W := fun i => T.W (embV V i)
  W_pos := by
    intro v hv
    have hne : embV V v ≠ T.root := fun h => hv (by rw [← h, backV_embV])
    exact T.W_pos _ hne

end OnlineTransportation1195.Dev.T31.PartC
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartC
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
variable (T : Tree n) (V : Finset (Fin n)) (hr : T.root ∈ V) (hp : ∀ v ∈ V, T.parent v ∈ V)
theorem emb_root : embV V (subT T V hr hp).root = T.root := embV_backV T V hr _ hr

theorem emb_parent (i : Fin V.card) :
    embV V ((subT T V hr hp).parent i) = T.parent (embV V i) :=
  embV_backV T V hr _ (hp _ (embV_mem V i))

theorem emb_eq_root_iff (i : Fin V.card) :
    embV V i = T.root ↔ i = (subT T V hr hp).root := by
  rw [← emb_root T V hr hp]; exact (embV_inj V).eq_iff

theorem emb_parent_iff (u v : Fin V.card) :
    (subT T V hr hp).parent v = u ↔ T.parent (embV V v) = embV V u := by
  rw [← emb_parent T V hr hp]; exact (embV_inj V).eq_iff.symm

theorem emb_iterate (k : ℕ) (b : Fin V.card) :
    embV V ((subT T V hr hp).parent^[k] b) = T.parent^[k] (embV V b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', emb_parent, ih]

theorem emb_isAnc (a b : Fin V.card) :
    (subT T V hr hp).IsAnc a b ↔ T.IsAnc (embV V a) (embV V b) := by
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [← emb_iterate T V hr hp, hk]⟩
  · rintro ⟨k, hk⟩; exact ⟨k, embV_inj V (by rw [emb_iterate T V hr hp, hk])⟩

theorem emb_vertexAt (L : List (Fin V.card)) (j : ℕ) :
    T.vertexAt (L.map (embV V)) j = embV V ((subT T V hr hp).vertexAt L j) := by
  unfold Tree.vertexAt
  rw [← emb_root T V hr hp, List.getD_map]

theorem emb_downStep (u v : Fin V.card) :
    T.downStep (embV V u) (embV V v) = (subT T V hr hp).downStep u v := by
  unfold Tree.downStep
  simp only [Ne, emb_eq_root_iff T V hr hp, ← emb_parent_iff T V hr hp]
  rfl

theorem emb_adj (u v : Fin V.card) :
    (subT T V hr hp).Adj u v ↔ T.Adj (embV V u) (embV V v) := by
  unfold Tree.Adj
  simp only [Ne, emb_eq_root_iff T V hr hp, ← emb_parent_iff T V hr hp]

theorem emb_downPrefix (L : List (Fin V.card)) (i : ℕ) :
    T.downPrefix (L.map (embV V)) i = (subT T V hr hp).downPrefix L i := by
  unfold Tree.downPrefix
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [emb_vertexAt T V hr hp, emb_vertexAt T V hr hp, emb_downStep]

theorem emb_downAt (L : List (Fin V.card)) (e : Fin V.card) (i : ℕ) :
    T.DownAt (L.map (embV V)) (embV V e) i ↔ (subT T V hr hp).DownAt L e i := by
  unfold Tree.DownAt
  rw [List.length_map, emb_vertexAt T V hr hp, emb_vertexAt T V hr hp, ← emb_parent T V hr hp,
    (embV_inj V).eq_iff, (embV_inj V).eq_iff, Ne, emb_eq_root_iff T V hr hp]

theorem emb_upAt (L : List (Fin V.card)) (e : Fin V.card) (i : ℕ) :
    T.UpAt (L.map (embV V)) (embV V e) i ↔ (subT T V hr hp).UpAt L e i := by
  unfold Tree.UpAt
  rw [List.length_map, emb_vertexAt T V hr hp, emb_vertexAt T V hr hp, ← emb_parent T V hr hp,
    (embV_inj V).eq_iff, (embV_inj V).eq_iff, Ne, emb_eq_root_iff T V hr hp]

theorem mem_edges_iff (i : Fin V.card) :
    i ∈ (subT T V hr hp).edges ↔ embV V i ≠ T.root := by
  rw [Ne, emb_eq_root_iff T V hr hp]
  exact ⟨fun h => (Finset.mem_erase.mp h).1,
    fun h => Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩⟩

end OnlineTransportation1195.Dev.T31.PartC
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartC
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
/-! ## Truncation -/
theorem vertexAt_take (T : Tree n) (L : List (Fin n)) (k j : ℕ) (hj : j < k) :
    T.vertexAt (L.take k) j = T.vertexAt L j := by
  unfold Tree.vertexAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj]

theorem crossAt_take (T : Tree n) (L : List (Fin n)) (k : ℕ) (e : Fin n) (j : ℕ) :
    T.CrossAt (L.take k) e j ↔ T.CrossAt L e j ∧ j + 1 < k := by
  unfold Tree.CrossAt Tree.DownAt Tree.UpAt
  constructor
  · intro h
    have hlen : j + 1 < (L.take k).length := by rcases h with h | h <;> exact h.2.1
    rw [List.length_take] at hlen
    have hk : j + 1 < k := by omega
    rw [vertexAt_take T L k j (by omega), vertexAt_take T L k (j + 1) hk] at h
    refine ⟨?_, hk⟩
    rcases h with h | h
    · exact Or.inl ⟨h.1, by omega, h.2.2⟩
    · exact Or.inr ⟨h.1, by omega, h.2.2⟩
  · rintro ⟨h, hk⟩
    have hlen : j + 1 < L.length := by rcases h with h | h <;> exact h.2.1
    rw [vertexAt_take T L k j (by omega), vertexAt_take T L k (j + 1) hk, List.length_take]
    rcases h with h | h
    · exact Or.inl ⟨h.1, by omega, h.2.2⟩
    · exact Or.inr ⟨h.1, by omega, h.2.2⟩

theorem downPrefix_take (T : Tree n) (L : List (Fin n)) (k i : ℕ) (hi : i + 1 < k) :
    T.downPrefix (L.take k) i = T.downPrefix L i := by
  unfold Tree.downPrefix
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [vertexAt_take T L k j (by omega), vertexAt_take T L k (j + 1) (by omega)]

/-! ## The stub -/

end OnlineTransportation1195.Dev.T31.PartC
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
/-! ## The root patch as a smaller tree (Part C) -/

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
/-! ## Real-analysis facts (Part E) -/

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem isAnc_trans (T : Tree n) (a b c : Fin n) (h1 : T.IsAnc a b) (h2 : T.IsAnc b c) :
    T.IsAnc a c := by
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := h2
  exact ⟨i + j, by rw [Function.iterate_add_apply, hj, hi]⟩

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31.PartE
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31
variable {n : ℕ}
theorem edges_card (T : Tree n) : T.edges.card = n - 1 := by
  unfold Tree.edges
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

end OnlineTransportation1195.Dev.T31.PartE
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T31
open OnlineTransportation1195.Main
variable {n : ℕ}
alias edges_card := OnlineTransportation1195.Dev.T31.PartE.edges_card

/-! ## Assembly -/

end OnlineTransportation1195.Dev.T31
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Main

end OnlineTransportation1195.Main
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T13
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
variable {n : ℕ}
variable (T : Tree n) (S : Finset (Fin n)) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ)
/-!
Blueprint for Theorem 1.3 (`weighted_tree_walk_deadlines`), q419.
`walkFn` is the walk of Theorem 3.1's proof, computed on an upward-closed edge set `S` of the
whole tree (no relabelling), with every choice made explicit and every division total.
Every `sorry` below is a stub proved in a Part file.
-/
/-! ## The construction -/
/-- Red edges of `S` at time `t` (Definition 3.2 restricted to `S`). -/
noncomputable def redS : Finset (Fin n) := S.filter (fun e => d e < T.x L e + t)

/-- The root patch inside `S`: red edges whose ancestor edges are all red. -/
noncomputable def patchS : Finset (Fin n) :=
  (redS T S d L t).filter (fun e => ∀ a ∈ T.edges, T.IsAnc a e → a ∈ redS T S d L t)

noncomputable def RS : ℝ := ∑ e ∈ redS T S d L t, T.W e

noncomputable def RinS : ℝ := ∑ e ∈ patchS T S d L t, T.W e

noncomputable def FS (s : ℝ) : ℝ := ∑ e ∈ S, T.W e * min 1 (s / d e)

/-- Candidate edges for the time budget (`d e - x e > 0` and `R < F` there). -/
noncomputable def goodCands : Finset (Fin n) :=
  S.filter (fun e => 0 < d e - T.x L e ∧
    RS T S d L (d e - T.x L e) < FS T S d (d e - T.x L e))

/-- The time `t`: the candidate of least index, else `∑ d + 1`. -/
noncomputable def pickT : ℝ :=
  if h : (goodCands T S d L).Nonempty then
    d ((goodCands T S d L).min' h) - T.x L ((goodCands T S d L).min' h)
  else ∑ e ∈ S, d e + 1

noncomputable def betaLoS (r : ℝ) : ℝ :=
  (insert 0 ((S.filter (fun e => FS T S d (d e) ≤ r)).image d)).max' (Finset.insert_nonempty _ _)

noncomputable def sAS (r : ℝ) : ℝ := ∑ e ∈ S.filter (fun e => d e ≤ betaLoS T S d r), T.W e

noncomputable def sBS (r : ℝ) : ℝ :=
  ∑ e ∈ S.filter (fun e => betaLoS T S d r < d e), T.W e / d e

/-- The `s` solving `F s = r` (`0` when `r = 0`). -/
noncomputable def pickS (r : ℝ) : ℝ := if r = 0 then 0 else (r - sAS T S d r) / sBS T S d r

/-- The detour at index `j` of `L`: a red depth-first search from a vertex entered through a black
edge. -/
noncomputable def detS (j : ℕ) : List (Fin n) :=
  if 0 < j ∧ T.vertexAt L j ∉ redS T S d L t ∧ T.vertexAt L j ≠ T.root ∧
      T.DownAt L (T.vertexAt L j) (j - 1)
  then dfsS T (redS T S d L t) (T.vertexAt L j) else [T.vertexAt L j]

/-- The path from `v` up to the root. -/
def upPath (v : Fin n) : List (Fin n) :=
  (List.range (T.depth v + 1)).map (fun i => T.parent^[i] v)

/-- First crossing index of `e` in `M` (`0` if none). -/
noncomputable def firstIdx (M : List (Fin n)) (e : Fin n) : ℕ :=
  ((List.range M.length).find? (fun i => decide (T.CrossAt M e i))).getD 0

/-- Cut `M` right after the last first crossing of an edge of `P`. -/
noncomputable def trunc (P : Finset (Fin n)) (M : List (Fin n)) : List (Fin n) :=
  M.take (P.sup (firstIdx T M) + 2)

end OnlineTransportation1195.Dev.T13
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T13
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
variable {n : ℕ}
/-- The walk of Theorem 3.1 on the upward-closed edge set `S` with deadlines `d`. -/
noncomputable def walkFn (T : Tree n) (S : Finset (Fin n)) (d : Fin n → ℝ) : List (Fin n) :=
  if S = ∅ then [T.root]
  else if ∀ e ∈ S, ∀ f ∈ S, d e = d f then dfsS T S T.root
  else
    let L := dfsS T S T.root
    let t := pickT T S d L
    let P := patchS T S d L t
    let s := pickS T S d (RinS T S d L t)
    let M : List (Fin n) :=
      if hP : P.card < S.card then
        (if P = ∅ then [T.root] else trunc T P (walkFn T P (fun e => min (d e) s)))
      else [T.root]
    let U := upPath T (M.getLast?.getD T.root)
    M ++ U.tail ++ (blocks L (detS T S d L t)).tail
termination_by S.card
decreasing_by exact hP

end OnlineTransportation1195.Dev.T13
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T13.PartLT
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL OnlineTransportation1195.Dev.T13
variable {n : ℕ}
/-! ## Lengths of depth-first searches -/
theorem step_one (T : Tree n) (u w : Fin n) (h : T.Adj u w) :
    ∑ e ∈ T.edges, (PartB.dφ T e u w + PartB.uφ T e u w) = 1 := by
  rw [Finset.sum_add_distrib]
  have hd : ∑ e ∈ T.edges, PartB.dφ T e u w = if w ≠ T.root ∧ T.parent w = u then 1 else 0 := by
    split_ifs with hw
    · rw [Finset.sum_eq_single w]
      · simp [PartB.dφ, hw.2]
      · intro b _ hb; simp [PartB.dφ, Ne.symm hb]
      · intro hw'; exact absurd (Finset.mem_erase.mpr ⟨hw.1, Finset.mem_univ _⟩) hw'
    · refine Finset.sum_eq_zero (fun e he => ?_)
      have her : e ≠ T.root := (Finset.mem_erase.mp he).1
      unfold PartB.dφ; rw [if_neg]; rintro ⟨h1, rfl⟩; exact hw ⟨her, h1.symm⟩
  have hu : ∑ e ∈ T.edges, PartB.uφ T e u w = if u ≠ T.root ∧ T.parent u = w then 1 else 0 := by
    split_ifs with hu
    · rw [Finset.sum_eq_single u]
      · simp [PartB.uφ, hu.2]
      · intro b _ hb; simp [PartB.uφ, Ne.symm hb]
      · intro hu'; exact absurd (Finset.mem_erase.mpr ⟨hu.1, Finset.mem_univ _⟩) hu'
    · refine Finset.sum_eq_zero (fun e he => ?_)
      have her : e ≠ T.root := (Finset.mem_erase.mp he).1
      unfold PartB.uφ; rw [if_neg]; rintro ⟨rfl, h1⟩; exact hu ⟨her, h1.symm⟩
  rw [hd, hu]
  rcases h with h | h
  · have : ¬ (u ≠ T.root ∧ T.parent u = w) := by
      rintro ⟨_, h2⟩; exact PartB.no2cycle T h.1 (by rw [h.2, h2])
    rw [if_pos h, if_neg this]
  · have : ¬ (w ≠ T.root ∧ T.parent w = u) := by
      rintro ⟨_, h2⟩; exact PartB.no2cycle T h.1 (by rw [h.2, h2])
    rw [if_neg this, if_pos h]

theorem length_eq_steps (T : Tree n) (L : List (Fin n)) (hL : IsPath T L) :
    L.length - 1 = ∑ e ∈ T.edges,
      (PartB.SS T (PartB.dφ T e) L + PartB.SS T (PartB.uφ T e) L) := by
  unfold PartB.SS
  simp_rw [← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun j hj => step_one T _ _ (hL j (by rw [Finset.mem_range] at hj; omega)))]
  simp

theorem dfsS_length (T : Tree n) (S : Finset (Fin n)) (v : Fin n) :
    (dfsS T S v).length = 1 + 2 * (T.edges.filter (fun e => Reach T S v e)).card := by
  have hc := PartB.dfsS_closed T S v
  have h1 := length_eq_steps T _ hc.2.2
  have hpos : 0 < (dfsS T S v).length := by
    have := hc.1
    cases h : dfsS T S v with
    | nil => rw [h] at this; simp at this
    | cons _ _ => simp
  have h2 : ∑ e ∈ T.edges, (PartB.SS T (PartB.dφ T e) (dfsS T S v) +
      PartB.SS T (PartB.uφ T e) (dfsS T S v)) =
      2 * (T.edges.filter (fun e => Reach T S v e)).card := by
    rw [Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e he => ?_)
    have her : e ≠ T.root := (Finset.mem_erase.mp he).1
    rw [PartB.count_dfsS_down T S v e her, PartB.count_dfsS_up T S v e her]
    split_ifs <;> simp
  omega

theorem downAt_unique_dfsS (T : Tree n) (S : Finset (Fin n)) (v e : Fin n) (he : e ≠ T.root)
    (i i' : ℕ) (hi : T.DownAt (dfsS T S v) e i) (hi' : T.DownAt (dfsS T S v) e i') : i = i' := by
  have h1 := PartB.card_down T (dfsS T S v) e he
  rw [PartB.count_dfsS_down T S v e he] at h1
  have h1' : (Finset.univ.filter (fun i : Fin (dfsS T S v).length =>
      T.DownAt (dfsS T S v) e i)).card ≤ 1 := by rw [h1]; split_ifs <;> simp
  have h2 := Finset.card_le_one.mp h1' ⟨i, by have := hi.2.1; omega⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) ⟨i', by have := hi'.2.1; omega⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩)
  exact congrArg Fin.val h2

/-! ## Blocks and detours -/
theorem sum_map_range (f : ℕ → ℕ) (k : ℕ) :
    ((List.range k).map f).sum = ∑ j ∈ Finset.range k, f j := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem blocks_length (L : List (Fin n)) (D : ℕ → List (Fin n)) :
    (blocks L D).length = ∑ j ∈ Finset.range L.length, (D j).length := by
  unfold blocks
  rw [List.length_flatten, List.map_map]
  exact sum_map_range _ _

/-- Detour reach set at index `j` (empty when no detour is inserted). -/
noncomputable def Aset (T : Tree n) (S : Finset (Fin n)) (d : Fin n → ℝ) (L : List (Fin n))
    (t : ℝ) (j : ℕ) : Finset (Fin n) :=
  if 0 < j ∧ T.vertexAt L j ∉ redS T S d L t ∧ T.vertexAt L j ≠ T.root ∧
      T.DownAt L (T.vertexAt L j) (j - 1)
  then T.edges.filter (fun e => Reach T (redS T S d L t) (T.vertexAt L j) e) else ∅

theorem detS_length (T : Tree n) (S : Finset (Fin n)) (d : Fin n → ℝ) (L : List (Fin n))
    (t : ℝ) (j : ℕ) : (detS T S d L t j).length = 1 + 2 * (Aset T S d L t j).card := by
  unfold detS Aset
  split_ifs
  · exact dfsS_length _ _ _
  · simp

theorem sum_Aset_le (T : Tree n) (S : Finset (Fin n)) (d : Fin n → ℝ) (L : List (Fin n))
    (hU : ∀ e, e ≠ T.root → ∀ i i', T.DownAt L e i → T.DownAt L e i' → i = i')
    (t : ℝ) (k : ℕ) : ∑ j ∈ Finset.range k, (Aset T S d L t j).card ≤ T.edges.card := by
  have hdisj : (↑(Finset.range k) : Set ℕ).PairwiseDisjoint (Aset T S d L t) := by
    intro j _ j' _ hjj
    refine Finset.disjoint_left.mpr ?_
    intro e he he'
    unfold Aset at he he'
    split_ifs at he he' with hj hj'
    · obtain ⟨hj0, hjS, hjr, hjD⟩ := hj
      obtain ⟨hj0', hjS', hjr', hjD'⟩ := hj'
      have hR := (Finset.mem_filter.mp he).2
      have hR' := (Finset.mem_filter.mp he').2
      by_cases huu : T.vertexAt L j = T.vertexAt L j'
      · rw [← huu] at hjD'
        have := hU _ hjr _ _ hjD hjD'
        omega
      · rcases PartD.isAnc_total T _ _ e hR.2.2.1 hR'.2.2.1 with h | h
        · exact hjS' (hR.2.2.2 _ hjr' (Ne.symm huu) h hR'.2.2.1)
        · exact hjS (hR'.2.2.2 _ hjr huu h hR.2.2.1)
    all_goals simp at he he'
  rw [← Finset.card_biUnion hdisj]
  refine Finset.card_le_card ?_
  intro e he
  obtain ⟨j, _, he⟩ := Finset.mem_biUnion.mp he
  unfold Aset at he
  split_ifs at he
  · exact (Finset.mem_filter.mp he).1
  · simp at he

theorem blocks_detS_length (T : Tree n) (S : Finset (Fin n)) (d : Fin n → ℝ) (t : ℝ) :
    (blocks (dfsS T S T.root) (detS T S d (dfsS T S T.root) t)).length ≤ 4 * n := by
  rw [blocks_length]
  simp_rw [detS_length]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := sum_Aset_le T S d (dfsS T S T.root)
    (fun e he i i' hi hi' => downAt_unique_dfsS T S T.root e he i i' hi hi') t
    (dfsS T S T.root).length
  have h2 := dfsS_length T S T.root
  have h3 : (T.edges.filter (fun e => Reach T S T.root e)).card ≤ T.edges.card :=
    Finset.card_filter_le _ _
  have h4 := PartE.edges_card T
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have : 0 < n := T.root.pos
  omega

theorem upPath_length (T : Tree n) (v : Fin n) : (upPath T v).length = T.depth v + 1 := by
  simp [upPath]

/-! ## The length bound -/
theorem walkFn_length (T : Tree n) (S : Finset (Fin n)) (hS : S ⊆ T.edges) (d : Fin n → ℝ) :
    (walkFn T S d).length ≤ (S.card + 1) * (5 * n + 2) := by
  induction hk : S.card using Nat.strong_induction_on generalizing S d with
  | _ k ih =>
  have hn : 0 < n := T.root.pos
  rw [walkFn]
  split_ifs with h0 h1
  · simp; nlinarith
  · rw [dfsS_length]
    have h3 : (T.edges.filter (fun e => Reach T S T.root e)).card ≤ T.edges.card :=
      Finset.card_filter_le _ _
    have h4 := PartE.edges_card T
    have h5 : (T.edges.filter (fun e => Reach T S T.root e)).card ≤ n := by omega
    nlinarith
  · simp only [List.length_append]
    set L := dfsS T S T.root
    set t := pickT T S d L
    set P := patchS T S d L t
    set s := pickS T S d (RinS T S d L t)
    have hPS : P ⊆ S := fun e he =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
    set M : List (Fin n) :=
      if hP : P.card < S.card then
        (if P = ∅ then [T.root] else trunc T P (walkFn T P (fun e => min (d e) s)))
      else [T.root] with hMdef
    have hM : M.length ≤ k * (5 * n + 2) := by
      rw [hMdef]
      split_ifs with hP hPe
      · simp; nlinarith [show 1 ≤ k by
          rw [← hk]; exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)]
      · unfold trunc
        rw [List.length_take]
        refine (min_le_right _ _).trans ?_
        have := ih P.card (hk ▸ hP) P (hPS.trans hS) (fun e => min (d e) s) rfl
        refine this.trans ?_
        rw [← hk] at *
        exact Nat.mul_le_mul_right _ hP
      · simp; nlinarith [show 1 ≤ k by
          rw [← hk]; exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)]
    have hU := upPath_length T (M.getLast?.getD T.root)
    have hd := PartB.depth_lt T (M.getLast?.getD T.root)
    have hB : (blocks L (detS T S d L t)).length ≤ 4 * n := blocks_detS_length T S d t
    simp only [List.length_tail]
    have : (upPath T (M.getLast?.getD T.root)).length - 1 ≤ n := by omega
    have : (blocks L (detS T S d L t)).length - 1 ≤ 4 * n := by omega
    nlinarith

end OnlineTransportation1195.Dev.T13.PartLT
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T13
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
variable {n : ℕ}
/-! ## Part LT: length, and from downward to total deadlines -/
alias walkFn_length := OnlineTransportation1195.Dev.T13.PartLT.walkFn_length

end OnlineTransportation1195.Dev.T13
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T13.PartLT
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL OnlineTransportation1195.Dev.T13
variable {n : ℕ}
variable (T : Tree n)
/-! ## From downward to total deadlines (as in `T12PartW`) -/
noncomputable def phi (v : Fin n) : ℝ :=
  ∑ i ∈ Finset.range (T.depth v), T.W (T.parent^[i] v)

theorem phi_root : phi T T.root = 0 := by
  simp [phi, T.depth_root]

theorem phi_parent (v : Fin n) (hv : v ≠ T.root) : phi T v = T.W v + phi T (T.parent v) := by
  unfold phi
  rw [← T.depth_parent v hv, Finset.sum_range_succ']
  simp only [Function.iterate_succ_apply, Function.iterate_zero, id]
  ring

theorem phi_nonneg (v : Fin n) : 0 ≤ phi T v :=
  Finset.sum_nonneg (fun i hi =>
    (T.W_pos _ (PartA.iter_ne_root T v i (Finset.mem_range.mp hi))).le)

theorem step_identity (a c : Fin n) (hac : T.Adj a c) :
    T.totalStep a c = 2 * T.downStep a c - (phi T c - phi T a) := by
  unfold Tree.totalStep Tree.downStep
  by_cases h1 : c ≠ T.root ∧ T.parent c = a
  · rw [if_pos h1, if_pos h1, phi_parent T c h1.1, h1.2]; ring
  · have h2 : a ≠ T.root ∧ T.parent a = c := by
      rcases hac with h | h
      · exact absurd h h1
      · exact h
    rw [if_neg h1, if_neg h1, if_pos h2, phi_parent T a h2.1, h2.2]; ring

theorem vertexAt_zero (L : List (Fin n)) (hL : L.head? = some T.root) :
    T.vertexAt L 0 = T.root := by
  unfold Tree.vertexAt
  cases L with
  | nil => simp at hL
  | cons x xs => simp at hL; simp [hL]

theorem totalPrefix_eq (L : List (Fin n)) (hL : T.Walk L) (i : ℕ) (hi : i + 1 < L.length) :
    T.totalPrefix L i = 2 * T.downPrefix L i - phi T (T.vertexAt L (i + 1)) := by
  induction i with
  | zero =>
    simp only [Tree.totalPrefix, Tree.downPrefix, zero_add, Finset.sum_range_one]
    rw [step_identity T _ _ (hL.2 0 hi), vertexAt_zero T L hL.1, phi_root]
    simp only [zero_add, sub_zero]
  | succ i ih =>
    have hi' : i + 1 < L.length := by omega
    have e1 : T.totalPrefix L (i + 1) = T.totalPrefix L i +
        T.totalStep (T.vertexAt L (i + 1)) (T.vertexAt L (i + 1 + 1)) :=
      Finset.sum_range_succ _ _
    have e2 : T.downPrefix L (i + 1) = T.downPrefix L i +
        T.downStep (T.vertexAt L (i + 1)) (T.vertexAt L (i + 1 + 1)) :=
      Finset.sum_range_succ _ _
    rw [e1, e2, ih hi', step_identity T _ _ (hL.2 (i + 1) hi)]
    ring

theorem isAnc_iff (x v : Fin n) :
    T.IsAnc x v ↔ x = v ∨ T.IsAnc x (T.parent v) := by
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | zero => left; simpa using hi.symm
    | succ i => right; exact ⟨i, by rwa [Function.iterate_succ_apply] at hi⟩
  · rintro (h | ⟨i, hi⟩)
    · exact ⟨0, by simp [h]⟩
    · exact ⟨i + 1, by rwa [Function.iterate_succ_apply]⟩

theorem isAnc_of_parent (x v : Fin n) (h : T.IsAnc x (T.parent v)) : T.IsAnc x v := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i + 1, by rwa [Function.iterate_succ_apply]⟩

theorem not_isAnc_root (u : Fin n) (hu : u ≠ T.root) : ¬ T.IsAnc u T.root := by
  rintro ⟨i, hi⟩
  have key : ∀ k : ℕ, T.parent^[k] T.root = T.root := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, T.parent_root]
  exact hu (hi ▸ key i)

theorem outside_subtree (L : List (Fin n)) (hL : T.Walk L) (u : Fin n) (hu : u ≠ T.root)
    (i : ℕ) (hfirst : ∀ j, j < i → ¬ T.CrossAt L u j) (hi : i < L.length) :
    ¬ T.IsAnc u (T.vertexAt L i) := by
  induction i with
  | zero => rw [vertexAt_zero T L hL.1]; exact not_isAnc_root T u hu
  | succ m ih =>
    have ihm := ih (fun j hj => hfirst j (by omega)) (by omega)
    have hadj := hL.2 m hi
    intro hA
    rcases hadj with ⟨hc, hp⟩ | ⟨ha, hp⟩
    · rcases (isAnc_iff T u _).1 hA with h | h
      · exact hfirst m (by omega) (Or.inl ⟨hu, hi, by rw [← hp, ← h], h.symm⟩)
      · rw [hp] at h; exact ihm h
    · rw [← hp] at hA
      exact ihm (isAnc_of_parent T _ _ hA)

end OnlineTransportation1195.Dev.T13.PartLT
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T13.PartLT
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL OnlineTransportation1195.Dev.T13
variable {n : ℕ}
theorem total_of_down (T : Tree n) (hM : T.Monotone T.W) (L : List (Fin n))
    (hh : L.head? = some T.root) (hp : IsPath T L)
    (hV : ∀ e ∈ T.edges, VB T L e (((n : ℝ) - 1) * T.W e)) :
    T.TotalDeadlines L (fun e => (2 * (n : ℝ) - 3) * T.W e) := by
  have hW : T.Walk L := ⟨hh, hp⟩
  refine ⟨hW, ?_, ?_⟩
  · intro e he
    obtain ⟨i, hi, _⟩ := hV e he
    exact ⟨i, hi.1⟩
  · intro e he
    obtain ⟨i, ⟨hcross, hfirst⟩, hdl⟩ := hV e he
    have her : e ≠ T.root := (Finset.mem_erase.mp he).1
    have hdown : T.DownAt L e i := by
      rcases hcross with h | h
      · exact h
      · exfalso
        have := outside_subtree T L hW e her i hfirst (by have := h.2.1; omega)
        exact this (by rw [h.2.2.1]; exact ⟨0, rfl⟩)
    refine ⟨i, ⟨hcross, hfirst⟩, ?_⟩
    obtain ⟨-, hi, -, hv⟩ := hdown
    rw [totalPrefix_eq T L hW i hi, hv, phi_parent T e her]
    have := phi_nonneg T (T.parent e)
    linarith

end OnlineTransportation1195.Dev.T13.PartLT
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T13
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
variable {n : ℕ}
alias total_of_down := OnlineTransportation1195.Dev.T13.PartLT.total_of_down

/-! ## Part PR: the program computes `walkFn` -/
/-- The deadlines `(n-1) w` of Theorem 1.3's reduction. -/
noncomputable def d0 (T : Tree n) : Fin n → ℝ := fun e => ((n : ℝ) - 1) * T.W e

end OnlineTransportation1195.Dev.T13
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T13.PartMS
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL OnlineTransportation1195.Dev.T13
variable {n : ℕ}
/-!
Part MS, file 1: relabelling the upward-closed edge set `S` to the tree `sT T S`, where
`dfsS T S root` is a DFS, and the budget pair `(pickT, pickS)` of `walkFn`.
-/
/-- Outer detour weight inside `S`. -/
noncomputable def RoutS (T : Tree n) (S : Finset (Fin n)) (d : Fin n → ℝ) (L : List (Fin n))
    (t : ℝ) : ℝ :=
  ∑ e ∈ redS T S d L t \ patchS T S d L t, T.W e

theorem root_nmem (T : Tree n) (S : Finset (Fin n)) (hS : S ⊆ T.edges) : T.root ∉ S :=
  fun h => by have := hS h; simp [Tree.edges] at this

theorem ne_root_of_mem (T : Tree n) (S : Finset (Fin n)) (hS : S ⊆ T.edges) (e : Fin n)
    (he : e ∈ S) : e ≠ T.root := fun h => root_nmem T S hS (h ▸ he)

theorem hpS (T : Tree n) (S : Finset (Fin n))
    (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) :
    ∀ v ∈ insert T.root S, T.parent v ∈ insert T.root S := by
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hvS
  · rw [T.parent_root]; exact Finset.mem_insert_self _ _
  · by_cases h : T.parent v = T.root
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hup v hvS _ (by simp [Tree.edges, h]) ⟨1, rfl⟩)

/-- The relabelled tree on `insert root S`. -/
noncomputable def sT (T : Tree n) (S : Finset (Fin n))
    (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) : Tree (insert T.root S).card :=
  PartC.subT T (insert T.root S) (Finset.mem_insert_self _ _) (hpS T S hup)

noncomputable abbrev em (T : Tree n) (S : Finset (Fin n)) (i : Fin (insert T.root S).card) :
    Fin n := PartC.embV (insert T.root S) i

noncomputable abbrev bk (T : Tree n) (S : Finset (Fin n)) (v : Fin n) :
    Fin (insert T.root S).card :=
  PartC.backV T (insert T.root S) (Finset.mem_insert_self _ _) v

theorem em_bk (T : Tree n) (S : Finset (Fin n)) (v : Fin n) (hv : v ∈ insert T.root S) :
    em T S (bk T S v) = v := PartC.embV_backV T _ _ v hv

theorem em_mem (T : Tree n) (S : Finset (Fin n)) (i : Fin (insert T.root S).card) :
    em T S i ∈ insert T.root S := PartC.embV_mem _ i

end OnlineTransportation1195.Dev.T13.PartMS
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T13.PartMS
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL OnlineTransportation1195.Dev.T13
variable {n : ℕ}
variable (T : Tree n) (S : Finset (Fin n))
theorem mem_sT_edges (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) (i : Fin (insert T.root S).card) :
    i ∈ (sT T S hup).edges ↔ em T S i ∈ S := by
  rw [sT, PartC.mem_edges_iff]
  constructor
  · intro h
    rcases Finset.mem_insert.mp (em_mem T S i) with h' | h'
    · exact absurd h' h
    · exact h'
  · exact ne_root_of_mem T S hS _

theorem sum_tr (A' : Finset (Fin (insert T.root S).card)) (A : Finset (Fin n))
    (hA : A ⊆ insert T.root S) (h : ∀ i, i ∈ A' ↔ em T S i ∈ A) (f : Fin n → ℝ) :
    ∑ i ∈ A', f (em T S i) = ∑ e ∈ A, f e := by
  have hm := Finset.sum_map A' ⟨PartC.embV (insert T.root S), PartC.embV_inj _⟩ f
  simp only [Function.Embedding.coeFn_mk] at hm
  rw [← hm]
  congr 1
  ext e
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact (h i).mp hi
  · intro he
    refine ⟨bk T S e, (h _).mpr ?_, em_bk T S e (hA he)⟩
    rw [em_bk T S e (hA he)]; exact he

theorem isAnc_tr (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) (a b : Fin (insert T.root S).card) :
    (sT T S hup).IsAnc a b ↔ T.IsAnc (em T S a) (em T S b) :=
  PartC.emb_isAnc T _ _ _ a b

/-! ### The DFS list -/
theorem dfsF_mem : ∀ (k : ℕ) (v x : Fin n), x ∈ dfsF T S k v → x = v ∨ x ∈ S := by
  intro k
  induction k with
  | zero => intro v x hx; simp [dfsF] at hx; exact Or.inl hx
  | succ k ih =>
    intro v x hx
    rw [PartB.dfsF_succ] at hx
    rcases List.mem_cons.mp hx with h | h
    · exact Or.inl h
    · obtain ⟨c, hc, hxc⟩ := List.mem_flatMap.mp h
      rw [PartB.mem_cs] at hc
      rcases List.mem_append.mp hxc with h1 | h1
      · rcases ih c x h1 with h2 | h2
        · exact Or.inr (h2 ▸ hc.2)
        · exact Or.inr h2
      · simp at h1; exact Or.inl h1

theorem reach_root_S (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) (e : Fin n) (he : e ∈ S) : Reach T S T.root e := by
  refine ⟨he, Ne.symm (Ne.symm (ne_root_of_mem T S hS e he)), ⟨T.depth e, PartB.iter_depth T e⟩, ?_⟩
  intro f hf _ _ hfe
  exact hup e he f (by simp [Tree.edges, hf]) hfe

theorem reach_root_iff (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) (e : Fin n) : Reach T S T.root e ↔ e ∈ S :=
  ⟨fun h => h.1, reach_root_S T S hS hup e⟩

theorem upAt_unique_dfsS (v e : Fin n) (he : e ≠ T.root)
    (i i' : ℕ) (hi : T.UpAt (dfsS T S v) e i) (hi' : T.UpAt (dfsS T S v) e i') : i = i' := by
  have h1 := PartB.card_up T (dfsS T S v) e he
  rw [PartB.count_dfsS_up T S v e he] at h1
  have h1' : (Finset.univ.filter (fun i : Fin (dfsS T S v).length =>
      T.UpAt (dfsS T S v) e i)).card ≤ 1 := by rw [h1]; split_ifs <;> simp
  have h2 := Finset.card_le_one.mp h1' ⟨i, by have := hi.2.1; omega⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) ⟨i', by have := hi'.2.1; omega⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩)
  exact congrArg Fin.val h2

theorem downAt_exists (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) (e : Fin n) (he : e ∈ S) : ∃ i, T.DownAt (dfsS T S T.root) e i := by
  have her := ne_root_of_mem T S hS e he
  have h1 := PartB.card_down T (dfsS T S T.root) e her
  rw [PartB.count_dfsS_down T S _ e her, if_pos (reach_root_S T S hS hup e he)] at h1
  obtain ⟨⟨i, _⟩, hi⟩ := Finset.card_pos.mp (by rw [h1]; norm_num :
    0 < (Finset.univ.filter (fun i : Fin (dfsS T S T.root).length =>
      T.DownAt (dfsS T S T.root) e i)).card)
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

theorem upAt_exists (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) (e : Fin n) (he : e ∈ S) : ∃ i, T.UpAt (dfsS T S T.root) e i := by
  have her := ne_root_of_mem T S hS e he
  have h1 := PartB.card_up T (dfsS T S T.root) e her
  rw [PartB.count_dfsS_up T S _ e her, if_pos (reach_root_S T S hS hup e he)] at h1
  obtain ⟨⟨i, _⟩, hi⟩ := Finset.card_pos.mp (by rw [h1]; norm_num :
    0 < (Finset.univ.filter (fun i : Fin (dfsS T S T.root).length =>
      T.UpAt (dfsS T S T.root) e i)).card)
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

/-- The relabelled DFS list. -/
noncomputable def Ls : List (Fin (insert T.root S).card) := (dfsS T S T.root).map (bk T S)

theorem map_Ls : (Ls T S).map (em T S) = dfsS T S T.root := by
  rw [Ls, List.map_map]
  conv_rhs => rw [← List.map_id (dfsS T S T.root)]
  refine List.map_congr_left (fun x hx => ?_)
  simp only [Function.comp_apply, id]
  apply em_bk
  rcases dfsF_mem T S n T.root x hx with h | h
  · rw [h]; exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem h

theorem length_Ls : (Ls T S).length = (dfsS T S T.root).length := by simp [Ls]

theorem card_fin_one (k : ℕ) (Q : ℕ → Prop) (i : ℕ) (hi : i < k) (hQ : Q i)
    (hu : ∀ j, j < k → Q j → j = i) :
    (Finset.univ.filter (fun j : Fin k => Q j)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨⟨i, hi⟩, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h; exact Fin.ext (hu j j.2 h)
  · rintro rfl; exact hQ

theorem vertexAt_tr (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) (j : ℕ) :
    T.vertexAt (dfsS T S T.root) j = em T S ((sT T S hup).vertexAt (Ls T S) j) := by
  have := PartC.emb_vertexAt T (insert T.root S) (Finset.mem_insert_self _ _) (hpS T S hup) (Ls T S) j
  rw [map_Ls] at this
  exact this

theorem downAt_tr (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) (e : Fin (insert T.root S).card) (i : ℕ) :
    (sT T S hup).DownAt (Ls T S) e i ↔ T.DownAt (dfsS T S T.root) (em T S e) i := by
  rw [sT, ← PartC.emb_downAt, map_Ls]

theorem upAt_tr (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) (e : Fin (insert T.root S).card) (i : ℕ) :
    (sT T S hup).UpAt (Ls T S) e i ↔ T.UpAt (dfsS T S T.root) (em T S e) i := by
  rw [sT, ← PartC.emb_upAt, map_Ls]

theorem downPrefix_tr (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) (i : ℕ) :
    (sT T S hup).downPrefix (Ls T S) i = T.downPrefix (dfsS T S T.root) i := by
  rw [sT, ← PartC.emb_downPrefix, map_Ls]

theorem dfs_Ls (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) : (sT T S hup).DFS (Ls T S) := by
  have hc := PartB.dfsS_closed T S T.root
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Ls, List.head?_map, hc.1]; rfl
  · intro i hi
    rw [length_Ls] at hi
    have := hc.2.2 i hi
    rw [vertexAt_tr T S hup, vertexAt_tr T S hup] at this
    rw [sT, PartC.emb_adj]
    exact this
  · rw [Ls, List.getLast?_map, hc.2.1]; rfl
  · intro e he
    have heS := (mem_sT_edges T S hS hup e).mp he
    have her := ne_root_of_mem T S hS _ heS
    obtain ⟨i, hi⟩ := downAt_exists T S hS hup _ heS
    obtain ⟨i', hi'⟩ := upAt_exists T S hS hup _ heS
    refine ⟨card_fin_one _ (fun j => (sT T S hup).DownAt (Ls T S) e j) i
        (by rw [length_Ls]; have := hi.2.1; omega) ((downAt_tr T S hup e i).mpr hi) ?_,
      card_fin_one _ (fun j => (sT T S hup).UpAt (Ls T S) e j) i'
        (by rw [length_Ls]; have := hi'.2.1; omega) ((upAt_tr T S hup e i').mpr hi') ?_⟩
    · intro j _ hj
      exact PartLT.downAt_unique_dfsS T S T.root _ her j i ((downAt_tr T S hup e j).mp hj) hi
    · intro j _ hj
      exact upAt_unique_dfsS T S T.root _ her j i' ((upAt_tr T S hup e j).mp hj) hi'

theorem x_tr (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) (e : Fin (insert T.root S).card) :
    (sT T S hup).x (Ls T S) e = T.x (dfsS T S T.root) (em T S e) := by
  have hf : (fun i => decide (T.DownAt (dfsS T S T.root) (em T S e) i)) =
      fun i => decide ((sT T S hup).DownAt (Ls T S) e i) := by
    funext i; simp only [downAt_tr]
  unfold Tree.x
  rw [hf, ← length_Ls T S]
  split
  · exact downPrefix_tr T S hup _
  · rfl

/-! ### Deadlines and red sets -/
noncomputable abbrev ds (T : Tree n) (S : Finset (Fin n)) (d : Fin n → ℝ) :
    Fin (insert T.root S).card → ℝ := fun i => d (em T S i)

theorem sum_edges_tr (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (f : Fin n → ℝ) : ∑ i ∈ (sT T S hup).edges, f (em T S i) = ∑ e ∈ S, f e :=
  sum_tr T S _ S (Finset.subset_insert _ _) (mem_sT_edges T S hS hup) f

theorem norm_tr (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (d : Fin n → ℝ) (hpos : ∀ e ∈ S, 0 < d e)
    (hmono : ∀ a ∈ S, ∀ b ∈ S, T.IsAnc a b → d a ≤ d b)
    (hsum : ∑ e ∈ S, T.W e / d e = 1) : (sT T S hup).Normalized (ds T S d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi; exact hpos _ ((mem_sT_edges T S hS hup i).mp hi)
  · intro a ha b hb hab
    exact hmono _ ((mem_sT_edges T S hS hup a).mp ha) _ ((mem_sT_edges T S hS hup b).mp hb)
      ((isAnc_tr T S hup a b).mp hab)
  · exact (sum_edges_tr T S hS hup (fun e => T.W e / d e)).trans hsum

theorem unequal_tr (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (d : Fin n → ℝ) (hne : ¬ ∀ e ∈ S, ∀ f ∈ S, d e = d f) : (sT T S hup).Unequal (ds T S d) := by
  push Not at hne
  obtain ⟨e, he, f, hf, hef⟩ := hne
  have he' : e ∈ insert T.root S := Finset.mem_insert_of_mem he
  have hf' : f ∈ insert T.root S := Finset.mem_insert_of_mem hf
  refine ⟨bk T S e, (mem_sT_edges T S hS hup _).mpr (by rw [em_bk T S e he']; exact he),
    bk T S f, (mem_sT_edges T S hS hup _).mpr (by rw [em_bk T S f hf']; exact hf), ?_⟩
  show d (em T S (bk T S e)) ≠ d (em T S (bk T S f))
  rw [em_bk T S e he', em_bk T S f hf']
  exact hef

theorem redS_sub (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) : redS T S d L t ⊆ S :=
  Finset.filter_subset _ _

theorem patchS_sub (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) :
    patchS T S d L t ⊆ redS T S d L t :=
  Finset.filter_subset _ _

theorem red_mem (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (d : Fin n → ℝ) (t : ℝ) (i : Fin (insert T.root S).card) :
    i ∈ (sT T S hup).red (ds T S d) (Ls T S) t ↔ em T S i ∈ redS T S d (dfsS T S T.root) t := by
  unfold Tree.red redS
  rw [Finset.mem_filter, Finset.mem_filter, mem_sT_edges T S hS hup, x_tr T S hup]

theorem patch_mem (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (d : Fin n → ℝ) (t : ℝ) (i : Fin (insert T.root S).card) :
    i ∈ (sT T S hup).rootPatch (ds T S d) (Ls T S) t ↔
      em T S i ∈ patchS T S d (dfsS T S T.root) t := by
  unfold Tree.rootPatch patchS
  rw [Finset.mem_filter, Finset.mem_filter, red_mem T S hS hup]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a ha hae => ?_⟩
    have haS : a ∈ S := hup _ (redS_sub T S d _ t h1) a ha hae
    have ha' : a ∈ insert T.root S := Finset.mem_insert_of_mem haS
    have hb : bk T S a ∈ (sT T S hup).edges :=
      (mem_sT_edges T S hS hup _).mpr (by rw [em_bk T S a ha']; exact haS)
    have hbi : (sT T S hup).IsAnc (bk T S a) i := by
      rw [isAnc_tr T S hup, em_bk T S a ha']; exact hae
    have := (red_mem T S hS hup d t _).mp (h2 _ hb hbi)
    rwa [em_bk T S a ha'] at this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a' ha' hai => (red_mem T S hS hup d t _).mpr ?_⟩
    exact h2 _ (hS ((mem_sT_edges T S hS hup a').mp ha')) ((isAnc_tr T S hup a' i).mp hai)

theorem R_tr (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (d : Fin n → ℝ) (t : ℝ) :
    (sT T S hup).R (ds T S d) (Ls T S) t = RS T S d (dfsS T S T.root) t :=
  sum_tr T S _ _ ((redS_sub T S d _ t).trans (Finset.subset_insert _ _))
    (red_mem T S hS hup d t) T.W

theorem Rin_tr (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (d : Fin n → ℝ) (t : ℝ) :
    (sT T S hup).Rin (ds T S d) (Ls T S) t = RinS T S d (dfsS T S T.root) t :=
  sum_tr T S _ _ (((patchS_sub T S d _ t).trans (redS_sub T S d _ t)).trans
    (Finset.subset_insert _ _)) (patch_mem T S hS hup d t) T.W

theorem Rout_tr (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (d : Fin n → ℝ) (t : ℝ) :
    (sT T S hup).Rout (ds T S d) (Ls T S) t = RoutS T S d (dfsS T S T.root) t :=
  sum_tr T S _ _ ((Finset.sdiff_subset.trans (redS_sub T S d _ t)).trans
    (Finset.subset_insert _ _))
    (fun i => by rw [Finset.mem_sdiff, Finset.mem_sdiff, red_mem T S hS hup, patch_mem T S hS hup])
    T.W

theorem F_tr (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (d : Fin n → ℝ) (s : ℝ) : (sT T S hup).F (ds T S d) s = FS T S d s :=
  sum_edges_tr T S hS hup (fun e => T.W e * min 1 (s / d e))

theorem patchNorm_tr (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (d : Fin n → ℝ) (s t : ℝ) :
    (sT T S hup).patchNormalization (ds T S d) (Ls T S) s t =
      ∑ e ∈ patchS T S d (dfsS T S T.root) t, T.W e / min (d e) s :=
  sum_tr T S _ _ (((patchS_sub T S d _ t).trans (redS_sub T S d _ t)).trans
    (Finset.subset_insert _ _)) (patch_mem T S hS hup d t) (fun e => T.W e / min (d e) s)

/-! ### The budget pair -/
theorem pickT_good (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (d : Fin n → ℝ) (hpos : ∀ e ∈ S, 0 < d e)
    (hmono : ∀ a ∈ S, ∀ b ∈ S, T.IsAnc a b → d a ≤ d b)
    (hsum : ∑ e ∈ S, T.W e / d e = 1) (hne : ¬ ∀ e ∈ S, ∀ f ∈ S, d e = d f) :
    0 < pickT T S d (dfsS T S T.root) ∧
      (sT T S hup).R (ds T S d) (Ls T S) (pickT T S d (dfsS T S T.root)) <
        (sT T S hup).F (ds T S d) (pickT T S d (dfsS T S T.root)) := by
  rw [R_tr T S hS hup, F_tr T S hS hup]
  unfold pickT
  split_ifs with h
  · have hm := Finset.mem_filter.mp ((goodCands T S d (dfsS T S T.root)).min'_mem h)
    exact hm.2
  · rcases RAM.PartM.cand_exists (sT T S hup) (ds T S d) (Ls T S)
      (norm_tr T S hS hup d hpos hmono hsum) (dfs_Ls T S hS hup)
      (unequal_tr T S hS hup d hne) with ⟨e', he', h1, h2⟩ | h2
    · exfalso
      apply h
      refine ⟨em T S e', Finset.mem_filter.mpr ⟨(mem_sT_edges T S hS hup e').mp he', ?_⟩⟩
      rw [x_tr T S hup] at h1 h2
      rw [R_tr T S hS hup, F_tr T S hS hup] at h2
      exact ⟨h1, h2⟩
    · rw [R_tr T S hS hup, F_tr T S hS hup] at h2
      have hsd := sum_edges_tr T S hS hup d
      simp only [ds] at h2
      rw [hsd] at h2
      refine ⟨?_, h2⟩
      have : 0 ≤ ∑ e ∈ S, d e := Finset.sum_nonneg (fun e he => (hpos e he).le)
      linarith

theorem betaLo_tr (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (d : Fin n → ℝ) (r : ℝ) : betaLoS T S d r = RAM.betaLo (sT T S hup) (ds T S d) r := by
  unfold betaLoS RAM.betaLo
  congr 1
  ext x
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_filter, F_tr T S hS hup]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨e, ⟨he, hF⟩, rfl⟩
    have he' : e ∈ insert T.root S := Finset.mem_insert_of_mem he
    refine ⟨bk T S e, ⟨(mem_sT_edges T S hS hup _).mpr (by rw [em_bk T S e he']; exact he), ?_⟩,
      ?_⟩
    · simp only [ds]; rw [em_bk T S e he']; exact hF
    · simp only [ds]; rw [em_bk T S e he']
  · rintro ⟨i, ⟨hi, hF⟩, rfl⟩
    exact ⟨em T S i, ⟨(mem_sT_edges T S hS hup i).mp hi, hF⟩, rfl⟩

theorem pickS_tr (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (d : Fin n → ℝ) (r : ℝ) :
    pickS T S d r = if r = 0 then 0 else RAM.sOf (sT T S hup) (ds T S d) r := by
  unfold pickS sAS sBS RAM.sOf
  split_ifs
  · rfl
  · rw [betaLo_tr T S hS hup]
    congr 1
    · congr 1
      refine (sum_tr T S _ _ ((Finset.filter_subset _ _).trans (Finset.subset_insert _ _))
        (fun i => ?_) T.W).symm
      rw [Finset.mem_filter, Finset.mem_filter, mem_sT_edges T S hS hup]
    · refine (sum_tr T S _ _ ((Finset.filter_subset _ _).trans (Finset.subset_insert _ _))
        (fun i => ?_) (fun e => T.W e / d e)).symm
      rw [Finset.mem_filter, Finset.mem_filter, mem_sT_edges T S hS hup]

theorem budgetS (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (d : Fin n → ℝ) (hpos : ∀ e ∈ S, 0 < d e)
    (hmono : ∀ a ∈ S, ∀ b ∈ S, T.IsAnc a b → d a ≤ d b)
    (hsum : ∑ e ∈ S, T.W e / d e = 1) (hne : ¬ ∀ e ∈ S, ∀ f ∈ S, d e = d f) :
    0 < pickT T S d (dfsS T S T.root) ∧
      0 ≤ pickS T S d (RinS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root))) ∧
      (patchS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root)) = ∅ ∨
        (0 < pickS T S d (RinS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root))) ∧
         ∑ e ∈ patchS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root)),
          T.W e / min (d e)
            (pickS T S d (RinS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root)))) = 1)) ∧
      pickS T S d (RinS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root))) +
        RoutS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root)) ≤
          pickT T S d (dfsS T S T.root) ∧
      (patchS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root))).card < S.card := by
  obtain ⟨ht, hRF⟩ := pickT_good T S hS hup d hpos hmono hsum hne
  set t := pickT T S d (dfsS T S T.root) with htdef
  have hB := RAM.PartM.budget_of (sT T S hup) (ds T S d) (Ls T S)
    (norm_tr T S hS hup d hpos hmono hsum) (dfs_Ls T S hS hup) t ht hRF
  rw [Rin_tr T S hS hup, ← pickS_tr T S hS hup] at hB
  set s := pickS T S d (RinS T S d (dfsS T S T.root) t) with hsdef
  set P := patchS T S d (dfsS T S T.root) t with hPdef
  obtain ⟨-, hs0, -, hPn, hbud, hPE⟩ := hB
  rw [Rout_tr T S hS hup] at hbud
  have hPS : P ⊆ S := (patchS_sub T S d _ t).trans (redS_sub T S d _ t)
  refine ⟨ht, hs0, ?_, hbud, ?_⟩
  · rcases hPn with h | h
    · left
      refine Finset.eq_empty_of_forall_notMem (fun e he => ?_)
      have he' : e ∈ insert T.root S := Finset.mem_insert_of_mem (hPS he)
      have : bk T S e ∈ (sT T S hup).rootPatch (ds T S d) (Ls T S) t := by
        rw [patch_mem T S hS hup, em_bk T S e he']; exact he
      rw [h] at this; simp at this
    · right
      rw [patchNorm_tr T S hS hup] at h
      refine ⟨?_, h⟩
      by_contra hs
      push Not at hs
      have : ∑ e ∈ P, T.W e / min (d e) s ≤ 0 := by
        refine Finset.sum_nonpos (fun e he => ?_)
        have hw : 0 ≤ T.W e := (T.W_pos e (ne_root_of_mem T S hS e (hPS he))).le
        exact div_nonpos_of_nonneg_of_nonpos hw ((min_le_right _ _).trans hs)
      linarith
  · refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hPS, fun hPeq => hPE ?_⟩)
    ext i
    constructor
    · intro hi; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
    · intro hi
      rw [patch_mem T S hS hup, ← hPdef, hPeq]
      exact (mem_sT_edges T S hS hup i).mp hi

end OnlineTransportation1195.Dev.T13.PartMS
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T13.PartMS
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL OnlineTransportation1195.Dev.T13
variable {n : ℕ}
/-!
Part MS, file 2: truncation, the upward path, and the detour blocks on `dfsS T S root`.
-/
/-! ### Truncation -/
theorem firstIdx_eq (T : Tree n) (W : List (Fin n)) (e : Fin n) (i : ℕ) (hi : T.FirstAt W e i) :
    firstIdx T W e = i := by
  have hlen : i < W.length := by
    rcases hi.1 with h | h
    · have := h.2.1; omega
    · have := h.2.1; omega
  unfold firstIdx
  rw [(List.find?_range_eq_some).mpr ⟨by simpa using hi.1, List.mem_range.mpr hlen,
    fun j hj => by simpa using hi.2 j hj⟩]
  rfl

theorem trunc_spec (T : Tree n) (P : Finset (Fin n)) (hne : P.Nonempty) (W : List (Fin n))
    (hh : W.head? = some T.root) (hp : IsPath T W) (c : Fin n → ℝ)
    (hV : ∀ e ∈ P, VB T W e (c e)) (s : ℝ) (hs : ∀ e ∈ P, c e ≤ s) :
    (trunc T P W).head? = some T.root ∧ IsPath T (trunc T P W) ∧
      (∀ e ∈ P, VB T (trunc T P W) e (c e)) ∧ dc T (trunc T P W) ≤ s := by
  have hfi : ∀ e ∈ P, T.FirstAt W e (firstIdx T W e) ∧
      T.downPrefix W (firstIdx T W e) ≤ c e := by
    intro e he
    obtain ⟨i, hi, hc⟩ := hV e he
    rw [firstIdx_eq T W e i hi]
    exact ⟨hi, hc⟩
  obtain ⟨e0, he0, hsup⟩ := Finset.exists_mem_eq_sup P hne (firstIdx T W)
  set f := firstIdx T W with hfdef
  have htr : trunc T P W = W.take (f e0 + 2) := by
    unfold trunc; rw [← hfdef, hsup]
  rw [htr]
  have hmax : ∀ e ∈ P, f e ≤ f e0 := fun e he => by
    rw [← hsup]; exact Finset.le_sup he
  have hL0 : f e0 + 1 < W.length := by
    rcases (hfi e0 he0).1.1 with h | h <;> exact h.2.1
  have hlenM : (W.take (f e0 + 2)).length = f e0 + 2 := by
    rw [List.length_take]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.head?_take, if_neg (by omega), hh]
  · intro i hi
    rw [hlenM] at hi
    rw [PartC.vertexAt_take T W _ i (by omega), PartC.vertexAt_take T W _ (i + 1) hi]
    exact hp i (by omega)
  · intro e he
    have hfe : f e ≤ f e0 := hmax e he
    refine ⟨f e, ⟨(PartC.crossAt_take T W _ e _).mpr ⟨(hfi e he).1.1, by omega⟩, ?_⟩, ?_⟩
    · intro j hj hc
      exact (hfi e he).1.2 j hj ((PartC.crossAt_take T W _ e _).mp hc).1
    · rw [PartC.downPrefix_take T W _ _ (by omega)]; exact (hfi e he).2
  · have : dc T (W.take (f e0 + 2)) = T.downPrefix (W.take (f e0 + 2)) (f e0) := by
      unfold dc Tree.downPrefix
      rw [hlenM, show f e0 + 2 - 1 = f e0 + 1 by omega]
    rw [this, PartC.downPrefix_take T W _ _ (by omega)]
    exact ((hfi e0 he0).2).trans (hs e0 he0)

/-! ### The upward path -/
theorem upPath_spec (T : Tree n) (v : Fin n) :
    (upPath T v).head? = some v ∧ (upPath T v).getLast? = some T.root ∧
      IsPath T (upPath T v) ∧ dc T (upPath T v) = 0 := by
  unfold upPath
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [List.range_succ_eq_map]
  · rw [List.range_succ]
    simp [PartA.iter_depth T _ v rfl]
  · intro i hi
    simp only [List.length_map, List.length_range] at hi
    rw [PartA.vA_up T v i (by omega), PartA.vA_up T v (i + 1) hi, Function.iterate_succ_apply']
    exact Or.inr ⟨PartA.iter_ne_root T v i (by omega), rfl⟩
  · unfold dc
    apply Finset.sum_eq_zero
    intro i hi
    simp only [List.length_map, List.length_range, Finset.mem_range] at hi
    rw [PartA.vA_up T v i (by omega), PartA.vA_up T v (i + 1) (by omega),
      Function.iterate_succ_apply']
    exact PartA.downStep_parent T _

end OnlineTransportation1195.Dev.T13.PartMS
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T13.PartMS
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL OnlineTransportation1195.Dev.T13
variable {n : ℕ}
variable (T : Tree n) (S : Finset (Fin n))
/-! ### Detours on `dfsS T S root` -/
theorem redS_edges (hS : S ⊆ T.edges) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) :
    redS T S d L t ⊆ T.edges := (redS_sub T S d L t).trans hS

theorem detS_closed (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) (j : ℕ) :
    ClosedAt T (T.vertexAt L j) (detS T S d L t j) := by
  unfold detS
  split_ifs
  · exact PartB.dfsS_closed _ _ _
  · refine ⟨rfl, rfl, ?_⟩
    intro i hi; simp at hi

theorem dc_detS (hS : S ⊆ T.edges) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) (j : ℕ) :
    dc T (detS T S d L t j) = ∑ e ∈ PartLT.Aset T S d L t j, T.W e := by
  unfold detS PartLT.Aset
  split_ifs
  · exact PartB.dfsS_dc _ _ (redS_edges T S hS d L t) _
  · simp [dc]

theorem x_spec_S (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (e : Fin n) (he : e ∈ S) :
    ∃ i, T.DownAt (dfsS T S T.root) e i ∧
      T.x (dfsS T S T.root) e = T.downPrefix (dfsS T S T.root) i := by
  obtain ⟨i, hdi⟩ := downAt_exists T S hS hup e he
  have hi := hdi.2.1
  unfold Tree.x
  split
  · next j hj =>
    have := List.find?_some hj
    exact ⟨j, by simpa using this, rfl⟩
  · next hj =>
    exfalso
    rw [List.find?_eq_none] at hj
    exact hj i (List.mem_range.mpr (by omega)) (by simpa using hdi)

theorem sum_dc_le_S (hS : S ⊆ T.edges) (d : Fin n → ℝ) (t : ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range k, dc T (detS T S d (dfsS T S T.root) t j) ≤
      RoutS T S d (dfsS T S T.root) t := by
  set L := dfsS T S T.root with hLdef
  simp_rw [dc_detS T S hS]
  have hdisj : (↑(Finset.range k) : Set ℕ).PairwiseDisjoint (PartLT.Aset T S d L t) := by
    intro j _ j' _ hjj
    refine Finset.disjoint_left.mpr ?_
    intro e he he'
    unfold PartLT.Aset at he he'
    split_ifs at he he' with hj hj'
    · obtain ⟨hj0, hjS, hjr, hjD⟩ := hj
      obtain ⟨hj0', hjS', hjr', hjD'⟩ := hj'
      have hR := (Finset.mem_filter.mp he).2
      have hR' := (Finset.mem_filter.mp he').2
      by_cases huu : T.vertexAt L j = T.vertexAt L j'
      · rw [← huu] at hjD'
        have := PartLT.downAt_unique_dfsS T S T.root _ hjr _ _ hjD hjD'
        omega
      · rcases PartD.isAnc_total T _ _ e hR.2.2.1 hR'.2.2.1 with h | h
        · exact hjS' (hR.2.2.2 _ hjr' (Ne.symm huu) h hR'.2.2.1)
        · exact hjS (hR'.2.2.2 _ hjr huu h hR.2.2.1)
    all_goals simp at he he'
  rw [← Finset.sum_biUnion hdisj]
  unfold RoutS
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨j, _, he⟩ := Finset.mem_biUnion.mp he
    unfold PartLT.Aset at he
    split_ifs at he with hj
    · obtain ⟨_, hjS, hjr, _⟩ := hj
      have hR := (Finset.mem_filter.mp he).2
      refine Finset.mem_sdiff.mpr ⟨hR.1, ?_⟩
      intro hP
      exact hjS ((Finset.mem_filter.mp hP).2 _ (by simp [Tree.edges, hjr]) hR.2.2.1)
    · simp at he
  · intro e he _
    have : e ≠ T.root := (Finset.mem_erase.mp
      (redS_edges T S hS d L t (Finset.mem_sdiff.mp he).1)).1
    exact (T.W_pos e this).le

theorem detour_S (hS : S ⊆ T.edges) (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S)
    (d : Fin n → ℝ) (t : ℝ) :
    (blocks (dfsS T S T.root) (detS T S d (dfsS T S T.root) t)).head? = some T.root ∧
      IsPath T (blocks (dfsS T S T.root) (detS T S d (dfsS T S T.root) t)) ∧
      ∀ e ∈ S, e ∉ patchS T S d (dfsS T S T.root) t →
        ∃ a ∈ S, T.IsAnc a e ∧ a ∉ redS T S d (dfsS T S T.root) t ∧
          VB T (blocks (dfsS T S T.root) (detS T S d (dfsS T S T.root) t)) e
            (T.x (dfsS T S T.root) a + RoutS T S d (dfsS T S T.root) t) := by
  set L := dfsS T S T.root with hLdef
  have hc := PartB.dfsS_closed T S T.root
  have hD : ∀ i < L.length, ClosedAt T (T.vertexAt L i) (detS T S d L t i) :=
    fun i _ => detS_closed T S d L t i
  refine ⟨?_, PartA.blocks_isPath T L _ hc.2.2 hD, ?_⟩
  · rw [PartA.blocks_head T L _ hD]; exact hc.1
  intro e he hnP
  by_cases heS : e ∈ redS T S d L t
  · -- red edge with a black ancestor: take the deepest one
    have hB : (T.edges.filter (fun a => T.IsAnc a e ∧ a ∉ redS T S d L t)).Nonempty := by
      by_contra hne
      apply hnP
      refine Finset.mem_filter.mpr ⟨heS, ?_⟩
      intro a ha hae
      by_contra haS
      exact hne ⟨a, Finset.mem_filter.mpr ⟨ha, hae, haS⟩⟩
    obtain ⟨a, haB, hamax⟩ := Finset.exists_max_image _ T.depth hB
    obtain ⟨ha, hae, haS⟩ := Finset.mem_filter.mp haB
    have haSS : a ∈ S := hup e he a ha hae
    have har : a ≠ T.root := ne_root_of_mem T S hS a haSS
    have hReach : Reach T (redS T S d L t) a e := by
      refine ⟨heS, ?_, hae, ?_⟩
      · rintro rfl; exact haS heS
      · intro f hfr hfa haf hfe
        by_contra hfS
        have h1 := hamax f (Finset.mem_filter.mpr ⟨by simp [Tree.edges, hfr], hfe, hfS⟩)
        have h2 := PartD.depth_lt_of_isAnc T a f haf (Ne.symm hfa)
        omega
    obtain ⟨i, hDi, hxi⟩ := x_spec_S T S hS hup a haSS
    have hva : T.vertexAt L (i + 1) = a := hDi.2.2.2
    have hcond : 0 < i + 1 ∧ T.vertexAt L (i + 1) ∉ redS T S d L t ∧
        T.vertexAt L (i + 1) ≠ T.root ∧
        T.DownAt L (T.vertexAt L (i + 1)) (i + 1 - 1) := by
      refine ⟨Nat.succ_pos _, ?_, ?_, ?_⟩
      · rw [hva]; exact haS
      · rw [hva]; exact har
      · rw [hva]; simpa using hDi
    have hDeq : detS T S d L t (i + 1) = dfsS T (redS T S d L t) a := by
      unfold detS; rw [if_pos hcond, hva]
    have hV := PartB.dfsS_VB T (redS T S d L t) (redS_edges T S hS d L t) a e hReach
    rw [← hDeq] at hV
    have hB2 := PartA.blocks_VB T L _ hD (i + 1) hDi.2.1 e _ hV
    refine ⟨a, haSS, hae, haS, VB_mono T _ e _ _ hB2 ?_⟩
    rw [PartD.dc_take T L i hDi.2.1, ← hxi, add_assoc, ← Finset.sum_range_succ]
    have := sum_dc_le_S T S hS d t (i + 1 + 1)
    linarith
  · -- black edge
    obtain ⟨i, hDi, hxi⟩ := x_spec_S T S hS hup e he
    obtain ⟨p, hp, hp1, hp2, hpc⟩ := PartA.blocks_step T L _ hD i hDi.2.1
    refine ⟨e, he, ⟨0, rfl⟩, heS, ?_⟩
    refine PartA.VB_of_cross T _ e p _ (Or.inl ⟨hDi.1, hp, ?_, ?_⟩) ?_
    · rw [hp1]; exact hDi.2.2.1
    · rw [hp2]; exact hDi.2.2.2
    · rw [hpc, hxi]
      have := sum_dc_le_S T S hS d t (i + 1)
      linarith

end OnlineTransportation1195.Dev.T13.PartMS
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T13.PartMS
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL OnlineTransportation1195.Dev.T13
variable {n : ℕ}
/-!
Part MS: `walkFn_spec` (Theorem 3.1 for `walkFn` on an upward-closed edge set).
-/
/-- Theorem 3.1 for `walkFn` on an upward-closed edge set. -/
theorem walkFn_spec (T : Tree n) (S : Finset (Fin n)) (hS : S ⊆ T.edges)
    (hup : ∀ e ∈ S, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ S) (d : Fin n → ℝ)
    (hpos : ∀ e ∈ S, 0 < d e) (hmono : ∀ a ∈ S, ∀ b ∈ S, T.IsAnc a b → d a ≤ d b)
    (hsum : S = ∅ ∨ ∑ e ∈ S, T.W e / d e = 1) :
    (walkFn T S d).head? = some T.root ∧ IsPath T (walkFn T S d) ∧
      ∀ e ∈ S, VB T (walkFn T S d) e (d e) := by
  induction hk : S.card using Nat.strong_induction_on generalizing S d with
  | _ k ih =>
  rw [walkFn]
  split_ifs with h0 h1
  · refine ⟨rfl, ?_, ?_⟩
    · intro i hi; simp at hi
    · intro e he; rw [h0] at he; simp at he
  · have hc := PartB.dfsS_closed T S T.root
    have hs1 : ∑ e ∈ S, T.W e / d e = 1 := by
      rcases hsum with h | h
      · exact absurd h h0
      · exact h
    refine ⟨hc.1, hc.2.2, fun e he => ?_⟩
    have hV := PartB.dfsS_VB T S hS T.root e (reach_root_S T S hS hup e he)
    refine VB_mono T _ e _ _ hV (le_of_eq ?_)
    rw [PartB.dfsS_dc T S hS T.root]
    have hfil : T.edges.filter (fun e => Reach T S T.root e) = S := by
      ext f
      rw [Finset.mem_filter, reach_root_iff T S hS hup]
      exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
    rw [hfil]
    have hde := hpos e he
    have : ∑ f ∈ S, T.W f / d f = (∑ f ∈ S, T.W f) / d e := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intro f hf; rw [h1 f hf e he]
    rw [this, div_eq_one_iff_eq hde.ne'] at hs1
    exact hs1
  · have hs1 : ∑ e ∈ S, T.W e / d e = 1 := by
      rcases hsum with h | h
      · exact absurd h h0
      · exact h
    obtain ⟨ht, hs0, hPn, hbud, hcard⟩ := budgetS T S hS hup d hpos hmono hs1 h1
    dsimp only
    set L := dfsS T S T.root with hLdef
    set t := pickT T S d L with htdef
    set P := patchS T S d L t with hPdef
    set s := pickS T S d (RinS T S d L t) with hsdef
    have hPS : P ⊆ S := (patchS_sub T S d _ t).trans (redS_sub T S d _ t)
    have hPsub : P ⊆ T.edges := hPS.trans hS
    rw [dif_pos hcard]
    -- the root-patch walk
    have hM : ∃ M : List (Fin n),
        M = (if P = ∅ then [T.root] else trunc T P (walkFn T P (fun e => min (d e) s))) ∧
        M.head? = some T.root ∧ IsPath T M ∧ (∀ e ∈ P, VB T M e (d e)) ∧ dc T M ≤ s := by
      by_cases hPe : P = ∅
      · refine ⟨[T.root], by rw [if_pos hPe], rfl, ?_, ?_, ?_⟩
        · intro i hi; simp at hi
        · intro e he; rw [hPe] at he; simp at he
        · simp [dc]; exact hs0
      · rw [if_neg hPe]
        obtain ⟨hs0', hnorm⟩ : 0 < s ∧ ∑ e ∈ P, T.W e / min (d e) s = 1 := by
          rcases hPn with h | h
          · exact absurd h hPe
          · exact h
        have hupP : ∀ e ∈ P, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ P := by
          intro e he a ha hae
          have he' := Finset.mem_filter.mp he
          refine Finset.mem_filter.mpr ⟨he'.2 a ha hae, ?_⟩
          intro b hb hba
          exact he'.2 b hb (PartE.isAnc_trans T b a e hba hae)
        obtain ⟨hWh, hWp, hWV⟩ := ih P.card (hk ▸ hcard) P hPsub hupP (fun e => min (d e) s)
          (fun e he => lt_min (hpos e (hPS he)) hs0')
          (fun a ha b hb hab => min_le_min_right s (hmono a (hPS ha) b (hPS hb) hab))
          (Or.inr hnorm) rfl
        obtain ⟨h1', h2', h3', h4'⟩ := trunc_spec T P (Finset.nonempty_iff_ne_empty.mpr hPe) _
          hWh hWp (fun e => min (d e) s) hWV s (fun e _ => min_le_right _ _)
        exact ⟨_, rfl, h1', h2', fun e he => VB_mono T _ e _ _ (h3' e he) (min_le_left _ _), h4'⟩
    obtain ⟨M, hMdef, hMh, hMp, hMV, hMc⟩ := hM
    rw [← hMdef]
    have hMne : M ≠ [] := by rintro rfl; simp at hMh
    obtain ⟨v, hv⟩ : ∃ v, M.getLast? = some v := by
      cases h : M.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h) hMne
      | some v => exact ⟨v, rfl⟩
    rw [hv]
    simp only [Option.getD_some]
    obtain ⟨hUh, hUl, hUp, hUc⟩ := upPath_spec T v
    set U := upPath T v with hUdef
    obtain ⟨hWh, hWp, hWV⟩ := detour_S T S hS hup d t
    set W := blocks L (detS T S d L t) with hWdef
    have hMU : U.head? = M.getLast? := by rw [hUh, hv]
    set MU := M ++ U.tail with hMUdef
    have hMUne : MU ≠ [] := by simp [hMUdef, hMne]
    have hMUl : MU.getLast? = some T.root := by
      rw [hMUdef, PartA.getLast_append_tail M U hMne hMU, hUl]
    have hWMU : W.head? = MU.getLast? := by rw [hWh, hMUl]
    have hMUp : IsPath T MU := PartA.isPath_append T M U hMp hUp hMU
    have hMUc : dc T MU = dc T M := by
      rw [hMUdef, PartA.dc_append T M U hMne hMU, hUc, add_zero]
    have hMUh : MU.head? = some T.root := by rw [hMUdef, PartA.head_append M _ hMne, hMh]
    refine ⟨?_, PartA.isPath_append T MU W hMUp hWp hWMU, ?_⟩
    · rw [PartA.head_append MU _ hMUne, hMUh]
    · intro e he
      by_cases heP : e ∈ P
      · exact PartA.VB_append_left T MU W.tail e _
          (PartA.VB_append_left T M U.tail e _ (hMV e heP))
      · obtain ⟨a, ha, hae, hared, hVa⟩ := hWV e he heP
        have h1 := PartA.VB_append_right T MU W e _ hMUne hWMU hVa
        refine VB_mono T _ e _ _ h1 ?_
        have hxa : T.x L a + t ≤ d a := by
          by_contra hc
          exact hared (Finset.mem_filter.mpr ⟨ha, not_le.mp hc⟩)
        have hda : d a ≤ d e := hmono a ha e he hae
        rw [hMUc]
        linarith

end OnlineTransportation1195.Dev.T13.PartMS
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T13
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
variable {n : ℕ}
/-! ## Part MS: the construction meets the deadlines -/
alias walkFn_spec := OnlineTransportation1195.Dev.T13.PartMS.walkFn_spec

/-! ## Assembly -/
theorem walk_ok (T : Tree n) (hM : T.Monotone T.W) :
    T.TotalDeadlines (walkFn T T.edges (d0 T)) (fun e => (2 * (n : ℝ) - 3) * T.W e) := by
  have hE : T.edges ⊆ T.edges := le_refl _
  have hup : ∀ e ∈ T.edges, ∀ a ∈ T.edges, T.IsAnc a e → a ∈ T.edges := fun _ _ a ha _ => ha
  by_cases hn : T.edges = ∅
  · have h := walkFn_spec T T.edges hE hup (d0 T) (by simp [hn]) (by simp [hn]) (Or.inl hn)
    exact total_of_down T hM _ h.1 h.2.1 (by simp [hn])
  · have hcard : T.edges.card = n - 1 := edges_card T
    have hn2 : 2 ≤ n := by
      have : 0 < T.edges.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn)
      omega
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    have hpos : ∀ e ∈ T.edges, 0 < d0 T e := fun e he =>
      mul_pos hn1 (T.W_pos e (Finset.ne_of_mem_erase he))
    have hmono : ∀ a ∈ T.edges, ∀ b ∈ T.edges, T.IsAnc a b → d0 T a ≤ d0 T b :=
      fun a ha b hb hab => mul_le_mul_of_nonneg_left (hM a ha b hb hab) hn1.le
    have hsum : ∑ e ∈ T.edges, T.W e / d0 T e = 1 := by
      have : ∀ e ∈ T.edges, T.W e / d0 T e = 1 / ((n : ℝ) - 1) := by
        intro e he
        have hw := T.W_pos e (Finset.ne_of_mem_erase he)
        unfold d0
        field_simp
      rw [Finset.sum_congr rfl this, Finset.sum_const, hcard, nsmul_eq_mul]
      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this]; field_simp
    have h := walkFn_spec T T.edges hE hup (d0 T) hpos hmono (Or.inr hsum)
    exact total_of_down T hM _ h.1 h.2.1 h.2.2

end OnlineTransportation1195.Dev.T13
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.T13.PartPR
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
  OnlineTransportation1195.Dev.T13 OnlineTransportation1195.Dev.RL.Lib Function
/-!
Part PR, file 1: frames, small subroutines with frame specifications, and generic loops
(sum, find-first, conditional max, array fill).
-/
/-! ## Frames -/
/-- Only the registers in `S` may change. -/
def Fr (S : List ℕ) (σ σ' : Cfg) : Prop := ∀ r, r ∉ S → σ'.regs r = σ.regs r

theorem Fr.rfl' (S : List ℕ) (σ : Cfg) : Fr S σ σ := fun _ _ => rfl

theorem Fr.tr {S : List ℕ} {σ σ1 σ2 : Cfg} (h1 : Fr S σ σ1) (h2 : Fr S σ1 σ2) : Fr S σ σ2 :=
  fun r hr => (h2 r hr).trans (h1 r hr)

theorem Fr.mono {S S' : List ℕ} {σ σ' : Cfg} (h : Fr S σ σ') (hS : S ⊆ S') : Fr S' σ σ' :=
  fun r hr => h r (fun h' => hr (hS h'))

theorem Fr.trm {S1 S2 S : List ℕ} {σ σ1 σ2 : Cfg} (h1 : Fr S1 σ σ1) (h2 : Fr S2 σ1 σ2)
    (hS1 : S1 ⊆ S) (hS2 : S2 ⊆ S) : Fr S σ σ2 :=
  Fr.tr (h1.mono hS1) (h2.mono hS2)

theorem Fr.upd {S : List ℕ} {σ : Cfg} {d : ℕ} (hd : d ∈ S) (x : ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ) :
    Fr S σ ⟨update σ.regs d x, p, m⟩ :=
  fun r hr => update_of_ne (fun (h : r = d) => hr (h ▸ hd)) _ _

end OnlineTransportation1195.Dev.T13.PartPR
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.T13.PartPR
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
  OnlineTransportation1195.Dev.T13 OnlineTransportation1195.Dev.RL.Lib Function
variable (σ : Cfg)
/-! ## Primitive statements -/
theorem h_const (d : ℕ) (q : ℚ) :
    Runs (.const d q) σ (fun k σ' => k = 1 ∧ σ'.mem = σ.mem ∧ Fr [d] σ σ' ∧
      σ'.regs d = (q : ℝ)) :=
  r_const ⟨rfl, rfl, Fr.upd (by simp) _ _ _, by simp⟩

theorem h_add (d i j : ℕ) :
    Runs (.add d i j) σ (fun k σ' => k = 1 ∧ σ'.mem = σ.mem ∧ Fr [d] σ σ' ∧
      σ'.regs d = σ.regs i + σ.regs j) :=
  r_add ⟨rfl, rfl, Fr.upd (by simp) _ _ _, by simp⟩

theorem h_sub (d i j : ℕ) :
    Runs (.sub d i j) σ (fun k σ' => k = 1 ∧ σ'.mem = σ.mem ∧ Fr [d] σ σ' ∧
      σ'.regs d = σ.regs i - σ.regs j) :=
  r_sub ⟨rfl, rfl, Fr.upd (by simp) _ _ _, by simp⟩

theorem h_mul (d i j : ℕ) :
    Runs (.mul d i j) σ (fun k σ' => k = 1 ∧ σ'.mem = σ.mem ∧ Fr [d] σ σ' ∧
      σ'.regs d = σ.regs i * σ.regs j) :=
  r_mul ⟨rfl, rfl, Fr.upd (by simp) _ _ _, by simp⟩

theorem h_mov (d s : ℕ) (hds : d ≠ s) :
    Runs (mov d s) σ (fun k σ' => k = 2 ∧ σ'.mem = σ.mem ∧ Fr [d] σ σ' ∧
      σ'.regs d = σ.regs s) :=
  r_mov hds ⟨rfl, rfl, Fr.upd (by simp) _ _ _, by simp⟩

theorem h_skip : Runs skip σ (fun k σ' => k = 1 ∧ σ'.mem = σ.mem ∧ Fr [] σ σ') :=
  r_skip ⟨rfl, rfl, Fr.rfl' _ _⟩

/-- `d := M[m]`, `m` the natural number in register `r`. -/
theorem h_ld (d r : ℕ) (hr : r ≠ 100) (m : ℕ) (hm : σ.regs r = m) :
    Runs (ld d r) σ (fun k σ' => k ≤ 4 * m + 6 ∧ σ'.mem = σ.mem ∧ Fr [100, 101, d] σ σ' ∧
      σ'.regs d = σ.mem m) := by
  refine r_ld d r hr σ m hm _ (fun k hk a b σ' h1 h2 => ⟨hk, h2, ?_, by rw [h1]; simp⟩)
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  rw [h1]; simp [update_apply, hj.1, hj.2.1, hj.2.2]

/-- `M[m] := s`, `m` the natural number in register `r`. -/
def stA (r s : ℕ) : Stmt := .seq (mov 100 r) (.seq (seekCore 0 true) (.store 1 s))

theorem h_stA (r s : ℕ) (hr : r ≠ 100) (hs0 : s ≠ 100) (hs1 : s ≠ 101) (m : ℕ)
    (hm : σ.regs r = m) :
    Runs (stA r s) σ (fun k σ' => k ≤ 4 * m + 6 ∧ σ'.mem = update σ.mem (m : ℤ) (σ.regs s) ∧
      Fr [100, 101] σ σ') := by
  refine r_seq (r_mov (Ne.symm hr) (r_seq (r_seekCore 0 true _ m (by simp [hm]) _
    (fun k hk a b => r_store ?_))))
  refine ⟨by omega, ?_, ?_⟩
  · simp [update_apply, hs0, hs1, sgn]
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp [update_apply, hj.1, hj.2]

/-- `d := M[-2 - m]`. -/
def ldO (d r : ℕ) : Stmt := .seq (mov 100 r) (.seq (seekCore (-2) false) (.load d 1))

theorem h_ldO (d r : ℕ) (hr : r ≠ 100) (m : ℕ) (hm : σ.regs r = m) :
    Runs (ldO d r) σ (fun k σ' => k ≤ 4 * m + 6 ∧ σ'.mem = σ.mem ∧ Fr [100, 101, d] σ σ' ∧
      σ'.regs d = σ.mem (-2 - (m : ℤ))) := by
  refine r_seq (r_mov (Ne.symm hr) (r_seq (r_seekCore _ false _ m (by simp [hm]) _
    (fun k hk a b => r_load ?_))))
  refine ⟨by omega, rfl, ?_, ?_⟩
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp [update_apply, hj.1, hj.2.1, hj.2.2]
  · simp [sgn, sub_eq_add_neg]

/-- `M[-2 - m] := s`. -/
def stO (r s : ℕ) : Stmt := .seq (mov 100 r) (.seq (seekCore (-2) false) (.store 1 s))

theorem h_stO (r s : ℕ) (hr : r ≠ 100) (hs0 : s ≠ 100) (hs1 : s ≠ 101) (m : ℕ)
    (hm : σ.regs r = m) :
    Runs (stO r s) σ (fun k σ' => k ≤ 4 * m + 6 ∧
      σ'.mem = update σ.mem (-2 - (m : ℤ)) (σ.regs s) ∧ Fr [100, 101] σ σ') := by
  refine r_seq (r_mov (Ne.symm hr) (r_seq (r_seekCore _ false _ m (by simp [hm]) _
    (fun k hk a b => r_store ?_))))
  refine ⟨by omega, ?_, ?_⟩
  · simp [update_apply, hs0, hs1, sgn, sub_eq_add_neg]
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp [update_apply, hj.1, hj.2]

theorem h_ldIn (d f r : ℕ) (hr : r ≠ 101) (m : ℕ) (hm : σ.regs r = m) :
    Runs (ldIn d f r) σ (fun k σ' => k ≤ 4 * (f + 3 * m) + 8 ∧ σ'.mem = σ.mem ∧
      Fr [100, 101, d] σ σ' ∧ σ'.regs d = σ.mem ((f + 3 * m : ℕ) : ℤ)) := by
  refine r_ldIn d f r hr σ m hm _ (fun k hk a b σ' h1 h2 => ⟨hk, h2, ?_, by rw [h1]; simp⟩)
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  rw [h1]; simp [update_apply, hj.1, hj.2.1, hj.2.2]

/-- `d := [regs a = regs b]`. -/
theorem h_eqT (d a b : ℕ) (hd : d ≠ 100) (ha : a ≠ 100) (hb : b ≠ 100) :
    Runs (eqT d a b) σ (fun k σ' => k ≤ 7 ∧ σ'.mem = σ.mem ∧ Fr [100, d] σ σ' ∧
      σ'.regs d = if σ.regs a = σ.regs b then 1 else 0) := by
  refine r_eqT d a b hd ha hb σ _ (fun k hk z σ' h1 h2 => ⟨hk, h2, ?_, by rw [h1]; simp⟩)
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  rw [h1]; simp [update_apply, hj.1, hj.2]

end OnlineTransportation1195.Dev.T13.PartPR
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.T13.PartPR
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
  OnlineTransportation1195.Dev.T13 OnlineTransportation1195.Dev.RL.Lib Function
/-! ## Comparisons, total division, min and max -/
/-- `d := [regs a ≤ regs b]`. -/
def leF (d a b : ℕ) : Stmt := .seq (.sub 102 a b) (.ifle 102 (.const d 1) (.const d 0))

theorem h_leF (σ : Cfg) (d a b : ℕ) :
    Runs (leF d a b) σ (fun k σ' => k ≤ 4 ∧ σ'.mem = σ.mem ∧ Fr [102, d] σ σ' ∧
      σ'.regs d = if σ.regs a ≤ σ.regs b then 1 else 0) := by
  refine r_seq (r_mono (h_sub σ 102 a b) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => r_ifle ?_ ?_)
  · intro h
    refine r_mono (h_const σ1 d 1) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
      ⟨by omega, hm2.trans hm1, Fr.trm hf1 hf2 (by simp) (by simp), ?_⟩
    rw [hv1] at h
    rw [if_pos (by linarith), hv2]; simp
  · intro h
    refine r_mono (h_const σ1 d 0) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
      ⟨by omega, hm2.trans hm1, Fr.trm hf1 hf2 (by simp) (by simp), ?_⟩
    rw [hv1] at h
    rw [if_neg (by intro h'; exact h (by linarith)), hv2]; simp

/-- `d := [regs a < regs b]`. -/
def ltF (d a b : ℕ) : Stmt := .seq (.sub 102 b a) (.ifle 102 (.const d 0) (.const d 1))

theorem h_ltF (σ : Cfg) (d a b : ℕ) :
    Runs (ltF d a b) σ (fun k σ' => k ≤ 4 ∧ σ'.mem = σ.mem ∧ Fr [102, d] σ σ' ∧
      σ'.regs d = if σ.regs a < σ.regs b then 1 else 0) := by
  refine r_seq (r_mono (h_sub σ 102 b a) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => r_ifle ?_ ?_)
  · intro h
    refine r_mono (h_const σ1 d 0) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
      ⟨by omega, hm2.trans hm1, Fr.trm hf1 hf2 (by simp) (by simp), ?_⟩
    rw [hv1] at h
    rw [if_neg (by intro h'; linarith), hv2]; simp
  · intro h
    refine r_mono (h_const σ1 d 1) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
      ⟨by omega, hm2.trans hm1, Fr.trm hf1 hf2 (by simp) (by simp), ?_⟩
    rw [hv1] at h
    rw [if_pos (by linarith), hv2]; simp

/-- `d := 1 - regs a`. -/
def notF (d a : ℕ) : Stmt := .seq (.const 102 1) (.sub d 102 a)

theorem h_notF (σ : Cfg) (d a : ℕ) (ha : a ≠ 102) :
    Runs (notF d a) σ (fun k σ' => k ≤ 2 ∧ σ'.mem = σ.mem ∧ Fr [102, d] σ σ' ∧
      σ'.regs d = 1 - σ.regs a) := by
  refine r_seq (r_mono (h_const σ 102 1) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ =>
    r_mono (h_sub σ1 d 102 a) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
      ⟨by omega, hm2.trans hm1, Fr.trm hf1 hf2 (by simp) (by simp), ?_⟩)
  rw [hv2, hv1, hf1 a (by simpa using ha)]; simp

/-- Total division, as Lean's: `d := regs a / regs b`. -/
def tdv (d a b : ℕ) : Stmt :=
  .ifle b (.seq (.const 103 0) (.seq (.sub 102 103 b)
    (.ifle 102 (.const d 0) (.seq (.div 104 a 102) (.sub d 103 104))))) (.div d a b)

theorem h_tdv (σ : Cfg) (d a b : ℕ) (ha : a ∉ [102, 103, 104]) (hb : b ∉ [102, 103, 104]) :
    Runs (tdv d a b) σ (fun k σ' => k ≤ 8 ∧ σ'.mem = σ.mem ∧ Fr [102, 103, 104, d] σ σ' ∧
      σ'.regs d = σ.regs a / σ.regs b) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hb
  refine r_ifle ?_ ?_
  · intro hb0
    refine r_seq (r_mono (h_const σ 103 0) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => r_seq
      (r_mono (h_sub σ1 102 103 b) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => r_ifle ?_ ?_))
    · intro h
      refine r_mono (h_const σ2 d 0) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ =>
        ⟨by omega, by rw [hm3, hm2, hm1], Fr.tr (Fr.tr (hf1.mono (by simp)) (hf2.mono (by simp)))
          (hf3.mono (by simp)), ?_⟩
      rw [hv2, hv1, hf1 b (by simp [hb.2.1])] at h
      have : σ.regs b = 0 := by push_cast at h; linarith
      rw [hv3, this]; simp
    · intro h
      refine r_seq (r_div ?_ (r_mono (h_sub _ d 103 104) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ =>
        ⟨by omega, ?_, ?_, ?_⟩))
      · exact lt_of_not_ge h
      · rw [hm3]; simp [hm2, hm1]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [hf3 r (by simp [hr.2.2.2])]
        simp only [update_apply, if_neg hr.2.2.1]
        rw [hf2 r (by simp [hr.1]), hf1 r (by simp [hr.2.1])]
      · rw [hv3]
        simp only [update_apply, reduceIte, Nat.reduceEqDiff]
        rw [hv2, hf2 103 (by simp), hv1, hf2 a (by simp [ha.1]),
          hf1 a (by simp [ha.2.1]), hf1 b (by simp [hb.2.1])]
        have hb' : σ.regs b < 0 := by
          rw [hv2, hv1, hf1 b (by simp [hb.2.1])] at h; push_cast at h; push Not at h; linarith
        push_cast
        ring
  · intro h
    refine r_div (lt_of_not_ge h) ⟨by omega, rfl, Fr.upd (by simp) _ _ _, by simp⟩

/-- `d := min (regs a) (regs b)`. -/
def mnS (d a b : ℕ) : Stmt := .seq (.sub 102 a b) (.ifle 102 (mov d a) (mov d b))

theorem h_mnS (σ : Cfg) (d a b : ℕ) (hda : d ≠ a) (hdb : d ≠ b) (ha : a ≠ 102) (hb : b ≠ 102) :
    Runs (mnS d a b) σ (fun k σ' => k ≤ 5 ∧ σ'.mem = σ.mem ∧ Fr [102, d] σ σ' ∧
      σ'.regs d = min (σ.regs a) (σ.regs b)) := by
  refine r_seq (r_mono (h_sub σ 102 a b) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => r_ifle ?_ ?_)
  · intro h
    refine r_mono (h_mov σ1 d a hda) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
      ⟨by omega, hm2.trans hm1, Fr.trm hf1 hf2 (by simp) (by simp), ?_⟩
    rw [hv1] at h
    rw [hv2, hf1 a (by simpa using ha), min_eq_left (by linarith)]
  · intro h
    refine r_mono (h_mov σ1 d b hdb) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
      ⟨by omega, hm2.trans hm1, Fr.trm hf1 hf2 (by simp) (by simp), ?_⟩
    rw [hv1] at h
    rw [hv2, hf1 b (by simpa using hb), min_eq_right (by linarith)]

/-- `d := max (regs a) (regs b)` (with `d = a` allowed). -/
def mxS (d a b : ℕ) : Stmt :=
  Stmt.seq (Stmt.seq (.sub 102 a b) (.ifle 102 (mov 103 b) (mov 103 a))) (mov d 103)

theorem h_mxS (σ : Cfg) (d a b : ℕ) (ha : a ∉ [102, 103]) (hb : b ∉ [102, 103]) (hd : d ≠ 103) :
    Runs (mxS d a b) σ (fun k σ' => k ≤ 8 ∧ σ'.mem = σ.mem ∧ Fr [102, 103, d] σ σ' ∧
      σ'.regs d = max (σ.regs a) (σ.regs b)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hb
  refine r_seq (r_seq (r_mono (h_sub σ 102 a b) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => r_ifle ?_ ?_))
  · intro h
    refine r_mono (h_mov σ1 103 b (by omega)) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
      r_mono (h_mov σ2 d 103 hd) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ =>
      ⟨by omega, by rw [hm3, hm2, hm1], Fr.tr (Fr.trm hf1 hf2 (by simp) (by simp))
        (hf3.mono (by simp)), ?_⟩
    rw [hv1] at h
    rw [hv3, hv2, hf1 b (by simp [hb.1]), max_eq_right (by linarith)]
  · intro h
    refine r_mono (h_mov σ1 103 a (by omega)) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
      r_mono (h_mov σ2 d 103 hd) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ =>
      ⟨by omega, by rw [hm3, hm2, hm1], Fr.tr (Fr.trm hf1 hf2 (by simp) (by simp))
        (hf3.mono (by simp)), ?_⟩
    rw [hv1] at h
    rw [hv3, hv2, hf1 a (by simp [ha.1]), max_eq_left (by linarith)]

/-! ## Generic loops -/
/-- `A := ∑_{m < N} X(m)`, the body computing `X` from `V = m`. -/
def sumLoop (V Nr C K A X : ℕ) (body : Stmt) : Stmt :=
  .seq (.const A 0) (forLoop V Nr C K (.seq body (.add A A X)))

/-- Register conditions of a loop combinator. -/
def LoopOK (V Nr C K A X : ℕ) (Sb Sc : List ℕ) : Prop :=
  V ∉ Sb ∧ Nr ∉ Sb ∧ A ∉ Sb ∧ X ∈ Sb ∧ Sb ⊆ Sc ∧ V ∈ Sc ∧ C ∈ Sc ∧ K ∈ Sc ∧ A ∈ Sc ∧
    Nr ∉ Sc ∧ [V, Nr, C, K, A].Nodup

theorem h_sumLoop (V Nr C K A X : ℕ) (body : Stmt) (Sb Sc : List ℕ)
    (hok : LoopOK V Nr C K A X Sb Sc) (N c : ℕ) (g : ℕ → ℝ) (σ0 : Cfg) (hN : σ0.regs Nr = N)
    (hbody : ∀ m < N, ∀ σ : Cfg, σ.mem = σ0.mem → Fr Sc σ0 σ → σ.regs V = m →
      Runs body σ (fun k σ' => k ≤ c ∧ σ'.mem = σ.mem ∧ Fr Sb σ σ' ∧ σ'.regs X = g m)) :
    Runs (sumLoop V Nr C K A X body) σ0 (fun k σ' => k ≤ N * (c + 6) + 4 ∧
      σ'.mem = σ0.mem ∧ Fr Sc σ0 σ' ∧ σ'.regs A = ∑ m ∈ Finset.range N, g m) := by
  obtain ⟨hV, hNb, hA, hX, hSb, hVc, hCc, hKc, hAc, hNc, hnd⟩ := hok
  have hVN : V ≠ Nr := fun h => by simp [h] at hnd
  have hVC : V ≠ C := fun h => by simp [h] at hnd
  have hVK : V ≠ K := fun h => by simp [h] at hnd
  have hVA : V ≠ A := fun h => by simp [h] at hnd
  have hNC : Nr ≠ C := fun h => by simp [h] at hnd
  have hNK : Nr ≠ K := fun h => by simp [h] at hnd
  have hNA : Nr ≠ A := fun h => by simp [h] at hnd
  have hCK : C ≠ K := fun h => by simp [h] at hnd
  have hCA : C ≠ A := fun h => by simp [h] at hnd
  have hKA : K ≠ A := fun h => by simp [h] at hnd
  let I : ℕ → Cfg → Prop := fun m σ => σ.mem = σ0.mem ∧ Fr Sc σ0 σ ∧
    σ.regs A = ∑ j ∈ Finset.range m, g j
  refine r_seq (r_mono (h_const σ0 A 0) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_for V Nr C K _ hVN hVC hVK hNC hNK hCK N (c + 1) I σ1
    (by rw [hf1 Nr (by simp; omega), hN]) ?_ ?_ _ ?_
  · intro a b
    refine ⟨hm1, ?_, ?_⟩
    · intro r hr
      have h1 : r ≠ C := fun h => hr (h ▸ hCc)
      have h2 : r ≠ V := fun h => hr (h ▸ hVc)
      simp only [update_apply, h1, h2, if_false]
      exact hf1 r (by simp; intro h; exact hr (h ▸ hAc))
    · simp [update_apply, Ne.symm hCA, Ne.symm hVA, hv1]
  · intro m hm σ ⟨hmσ, hfσ, hAσ⟩ hVm hNm
    refine r_seq (r_mono (hbody m hm σ hmσ hfσ hVm) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
      r_mono (h_add σ2 A A X) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ⟨by omega, ?_, ?_, ?_⟩)
    · rw [hf3 V (by simp; omega), hf2 V hV, hVm]
    · rw [hf3 Nr (by simp; omega), hf2 Nr hNb, hNm]
    · intro a b e
      refine ⟨by rw [hm3, hm2, hmσ], ?_, ?_⟩
      · intro r hr
        have h1 : r ≠ C := fun h => hr (h ▸ hCc)
        have h2 : r ≠ V := fun h => hr (h ▸ hVc)
        have h3 : r ≠ K := fun h => hr (h ▸ hKc)
        simp only [update_apply, h1, h2, h3, if_false]
        rw [hf3 r (by simp; intro h; exact hr (h ▸ hAc)), hf2 r (fun h => hr (hSb h))]
        exact hfσ r hr
      · simp only [update_apply, Ne.symm hCA, Ne.symm hVA, Ne.symm hKA, if_false]
        rw [hv3, hf2 A hA, hAσ, hv2, Finset.sum_range_succ]
  · intro k σ' hk ⟨hm', hf', hA'⟩
    exact ⟨by
      have : N * (c + 1 + 5) = N * (c + 6) := by ring
      omega, hm', hf', hA'⟩

/-- `find?` over `[0, m)`. -/
noncomputable def ffind (p : ℕ → Prop) (m : ℕ) : Option ℕ :=
  (List.range m).find? (fun j => decide (p j))

theorem ffind_succ (p : ℕ → Prop) (m : ℕ) :
    ffind p (m + 1) = (ffind p m).or (if p m then some m else none) := by
  unfold ffind
  rw [List.range_succ, List.find?_append, List.find?_singleton]
  by_cases h : p m <;> simp [h]

theorem ffind_zero (p : ℕ → Prop) : ffind p 0 = none := by simp [ffind]

theorem ffind_isSome (p : ℕ → Prop) (m : ℕ) : (ffind p m).isSome ↔ ∃ j < m, p j := by
  unfold ffind
  rw [List.find?_isSome]
  simp

theorem ffind_some (p : ℕ → Prop) (m j : ℕ) : ffind p m = some j ↔ j < m ∧ p j ∧ ∀ i < j, ¬ p i := by
  induction m generalizing j with
  | zero => simp [ffind_zero]
  | succ m ih =>
    rw [ffind_succ]
    rcases h : ffind p m with _ | i
    · rw [h] at ih
      simp only [Option.none_or]
      have hno : ∀ i < m, ¬ p i := by
        intro i hi hp
        have := (ffind_isSome p m).mpr ⟨i, hi, hp⟩
        rw [h] at this; simp at this
      constructor
      · intro h2
        by_cases hpm : p m
        · rw [if_pos hpm] at h2; cases h2; exact ⟨by omega, hpm, hno⟩
        · rw [if_neg hpm] at h2; cases h2
      · rintro ⟨h1, h2, h3⟩
        have hjm : j = m := by
          by_contra hne
          exact hno j (by omega) h2
        subst hjm
        rw [if_pos h2]
    · rw [h] at ih
      simp only [Option.some_or]
      constructor
      · intro h2; cases h2
        obtain ⟨a, b, c⟩ := (ih _).mp rfl
        exact ⟨by omega, b, c⟩
      · rintro ⟨h1, h2, h3⟩
        obtain ⟨a, b, c⟩ := (ih _).mp rfl
        rcases lt_trichotomy i j with hij | hij | hij
        · exact absurd b (h3 i hij)
        · rw [hij]
        · exact absurd h2 (c j hij)

/-- First `m < N` with `X(m) > 0`: flag in `F`, index in `R` (`0` if none). -/
def findLoop (V Nr C K F R X Y Z : ℕ) (body : Stmt) : Stmt :=
  .seq (.const F 0) (.seq (.const R 0) (forLoop V Nr C K (.seq body
    (.seq (.const Z 1) (.seq (.sub Z Z F) (.seq (.mul Y X Z) (.ifle Y skip
      (.seq (mov R V) (.const F 1)))))))))

def FindOK (V Nr C K F R X Y Z : ℕ) (Sb Sc : List ℕ) : Prop :=
  V ∉ Sb ∧ Nr ∉ Sb ∧ F ∉ Sb ∧ R ∉ Sb ∧ X ∈ Sb ∧ Sb ⊆ Sc ∧ V ∈ Sc ∧ C ∈ Sc ∧ K ∈ Sc ∧
    F ∈ Sc ∧ R ∈ Sc ∧ Y ∈ Sc ∧ Z ∈ Sc ∧ Nr ∉ Sc ∧ [V, Nr, C, K, F, R, Y, Z].Nodup ∧
    X ≠ Y ∧ X ≠ Z ∧ 9 ∉ Sc

theorem h_findLoop (V Nr C K F R X Y Z : ℕ) (body : Stmt) (Sb Sc : List ℕ)
    (hok : FindOK V Nr C K F R X Y Z Sb Sc) (N c : ℕ) (p : ℕ → Prop) (σ0 : Cfg)
    (hN : σ0.regs Nr = N)
    (hbody : ∀ m < N, ∀ σ : Cfg, σ.mem = σ0.mem → Fr Sc σ0 σ → σ.regs V = m →
      Runs body σ (fun k σ' => k ≤ c ∧ σ'.mem = σ.mem ∧ Fr Sb σ σ' ∧
        σ'.regs X = if p m then 1 else 0)) :
    Runs (findLoop V Nr C K F R X Y Z body) σ0 (fun k σ' => k ≤ N * (c + 15) + 5 ∧
      σ'.mem = σ0.mem ∧ Fr Sc σ0 σ' ∧
      σ'.regs F = (if (ffind p N).isSome then 1 else 0) ∧
      σ'.regs R = (((ffind p N).getD 0 : ℕ) : ℝ)) := by
  obtain ⟨hV, hNb, hFb, hRb, hX, hSb, hVc, hCc, hKc, hFc, hRc, hYc, hZc, hNc, hnd, hXY, hXZ,
    h9⟩ := hok
  have hVN : V ≠ Nr := fun h => by simp [h] at hnd
  have hVC : V ≠ C := fun h => by simp [h] at hnd
  have hVK : V ≠ K := fun h => by simp [h] at hnd
  have hVF : V ≠ F := fun h => by simp [h] at hnd
  have hVR : V ≠ R := fun h => by simp [h] at hnd
  have hNC : Nr ≠ C := fun h => by simp [h] at hnd
  have hNK : Nr ≠ K := fun h => by simp [h] at hnd
  have hCK : C ≠ K := fun h => by simp [h] at hnd
  have hCF : C ≠ F := fun h => by simp [h] at hnd
  have hCR : C ≠ R := fun h => by simp [h] at hnd
  have hKF : K ≠ F := fun h => by simp [h] at hnd
  have hKR : K ≠ R := fun h => by simp [h] at hnd
  have hFR : F ≠ R := fun h => by simp [h] at hnd
  have hVY : V ≠ Y := fun h => by simp [h] at hnd
  have hVZ : V ≠ Z := fun h => by simp [h] at hnd
  have hNY : Nr ≠ Y := fun h => by simp [h] at hnd
  have hNZ : Nr ≠ Z := fun h => by simp [h] at hnd
  have hFY : F ≠ Y := fun h => by simp [h] at hnd
  have hFZ : F ≠ Z := fun h => by simp [h] at hnd
  have hRY : R ≠ Y := fun h => by simp [h] at hnd
  have hRZ : R ≠ Z := fun h => by simp [h] at hnd
  have hYZ : Y ≠ Z := fun h => by simp [h] at hnd
  have hNF : Nr ≠ F := fun h => by simp [h] at hnd
  have hNR : Nr ≠ R := fun h => by simp [h] at hnd
  let I : ℕ → Cfg → Prop := fun m σ => σ.mem = σ0.mem ∧ Fr Sc σ0 σ ∧
    σ.regs F = (if (ffind p m).isSome then 1 else 0) ∧
    σ.regs R = (((ffind p m).getD 0 : ℕ) : ℝ)
  refine r_seq (r_mono (h_const σ0 F 0) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => r_seq
    (r_mono (h_const σ1 R 0) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_))
  have hf12 : Fr Sc σ0 σ2 := Fr.trm hf1 hf2 (by simpa using hFc) (by simpa using hRc)
  refine r_for V Nr C K _ hVN hVC hVK hNC hNK hCK N (c + 10) I σ2
    (by rw [hf12 Nr hNc, hN]) ?_ ?_ _ ?_
  · intro a b
    refine ⟨by rw [hm2, hm1], ?_, ?_, ?_⟩
    · intro r hr
      have h1 : r ≠ C := fun h => hr (h ▸ hCc)
      have h2 : r ≠ V := fun h => hr (h ▸ hVc)
      simp only [update_apply, h1, h2, if_false]
      exact hf12 r hr
    · simp [update_apply, Ne.symm hCF, Ne.symm hVF, ffind_zero, hf2 F (by simpa using hFR), hv1]
    · simp [update_apply, Ne.symm hCR, Ne.symm hVR, ffind_zero, hv2]
  · intro m hm σ ⟨hmσ, hfσ, hFσ, hRσ⟩ hVm hNm
    refine r_seq (r_mono (hbody m hm σ hmσ hfσ hVm) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
    have hF3 : σ3.regs F = σ.regs F := hf3 F hFb
    have hR3 : σ3.regs R = σ.regs R := hf3 R hRb
    have hV3 : σ3.regs V = m := by rw [hf3 V hV, hVm]
    have hN3 : σ3.regs Nr = N := by rw [hf3 Nr hNb, hNm]
    refine r_seq (r_mono (h_const σ3 Z 1) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => r_seq
      (r_mono (h_sub σ4 Z Z F) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => r_seq
      (r_mono (h_mul σ5 Y X Z) fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)))
    have hf36 : Fr [Z, Y] σ3 σ6 := Fr.trm (Fr.tr hf4 hf5) hf6 (by simp) (by simp)
    have hY6 : σ6.regs Y = (if p m then 1 else 0) * (1 - σ.regs F) := by
      rw [hv6, hv5, hv4, hf5 X (by simp [hXZ]), hf4 X (by simp [hXZ]), hv3,
        hf4 F (by simp [hFZ]), hF3]; simp
    have hF6 : σ6.regs F = σ.regs F := by rw [hf36 F (by simp [hFZ, hFY]), hF3]
    have hR6 : σ6.regs R = σ.regs R := by rw [hf36 R (by simp [hRZ, hRY]), hR3]
    have hV6 : σ6.regs V = m := by rw [hf36 V (by simp [hVZ, hVY]), hV3]
    have hN6 : σ6.regs Nr = N := by rw [hf36 Nr (by simp [hNZ, hNY]), hN3]
    have hfc6 : Fr Sc σ0 σ6 := Fr.tr hfσ (Fr.tr (hf3.mono hSb) (hf36.mono (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hZc
      · exact hYc)))
    have hm6 : σ6.mem = σ0.mem := by rw [hm6, hm5, hm4, hm3, hmσ]
    -- the post-condition of the iteration, for the final configuration
    have fin : ∀ σ7 : Cfg, σ7.mem = σ0.mem → Fr Sc σ0 σ7 → σ7.regs V = m → σ7.regs Nr = N →
        σ7.regs F = (if (ffind p (m + 1)).isSome then 1 else 0) →
        σ7.regs R = (((ffind p (m + 1)).getD 0 : ℕ) : ℝ) →
        σ7.regs V = m ∧ σ7.regs Nr = N ∧ ∀ a b e, I (m + 1)
          ⟨update (update (update σ7.regs K a) V b) C e, σ7.ptrs, σ7.mem⟩ := by
      intro σ7 h7m h7f h7V h7N h7F h7R
      refine ⟨h7V, h7N, fun a b e => ⟨h7m, ?_, ?_, ?_⟩⟩
      · intro r hr
        have h1 : r ≠ C := fun h => hr (h ▸ hCc)
        have h2 : r ≠ V := fun h => hr (h ▸ hVc)
        have h3 : r ≠ K := fun h => hr (h ▸ hKc)
        simp only [update_apply, h1, h2, h3, if_false]
        exact h7f r hr
      · simp only [update_apply, Ne.symm hCF, Ne.symm hVF, Ne.symm hKF, if_false]; exact h7F
      · simp only [update_apply, Ne.symm hCR, Ne.symm hVR, Ne.symm hKR, if_false]; exact h7R
    refine r_ifle ?_ ?_
    · intro hY
      refine r_mono (h_skip σ6) fun k7 σ7 ⟨hk7, hm7, hf7⟩ => ⟨by omega, ?_⟩
      have hσ7 : σ7.regs = σ6.regs := funext fun r => hf7 r (by simp)
      refine fin σ7 (by rw [hm7, hm6]) (fun r hr => by rw [hσ7]; exact hfc6 r hr)
        (by rw [hσ7, hV6]) (by rw [hσ7, hN6]) ?_ ?_
      · rw [hσ7, hF6, hFσ, ffind_succ]
        rcases hfm : ffind p m with _ | i
        · rw [hY6, hFσ, hfm] at hY
          by_cases hpm : p m
          · norm_num [hpm] at hY
          · simp [hpm]
        · simp
      · rw [hσ7, hR6, hRσ, ffind_succ]
        rcases hfm : ffind p m with _ | i
        · rw [hY6, hFσ, hfm] at hY
          by_cases hpm : p m
          · norm_num [hpm] at hY
          · simp [hpm]
        · simp
    · intro hY
      have hpm : p m := by
        by_contra hpm; rw [hY6] at hY; simp [hpm] at hY
      have hfm : ffind p m = none := by
        rcases hfm : ffind p m with _ | i
        · rfl
        · rw [hY6, hFσ, hfm] at hY; simp at hY
      refine r_seq (r_mono (h_mov σ6 R V (Ne.symm hVR)) fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ =>
        r_mono (h_const σ7 F 1) fun k8 σ8 ⟨hk8, hm8, hf8, hv8⟩ => ⟨by omega, ?_⟩)
      have hf78 : Fr [R, F] σ6 σ8 := Fr.trm hf7 hf8 (by simp) (by simp)
      refine fin σ8 (by rw [hm8, hm7, hm6]) (Fr.tr hfc6 (hf78.mono (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hRc
          · exact hFc))) (by rw [hf78 V (by simp [hVR, hVF]), hV6])
        (by rw [hf78 Nr (by simp [hNR, hNF]), hN6]) ?_ ?_
      · rw [hv8, ffind_succ, hfm, if_pos hpm]; simp
      · rw [hf8 R (by simp [hFR.symm]), hv7, hV6, ffind_succ, hfm, if_pos hpm]; simp
  · intro k σ' hk ⟨hm', hf', hF', hR'⟩
    exact ⟨by
      have : N * (c + 10 + 5) = N * (c + 15) := by ring
      omega, hm', hf', hF', hR'⟩

/-- Conditional running maximum, starting from `0`. -/
noncomputable def fmax (p : ℕ → Prop) (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => if p m then max (fmax p g m) (g m) else fmax p g m

/-- `B := max {0} ∪ {Y(m) : m < N, X(m) > 0}`. -/
def maxLoop (V Nr C K B X Y : ℕ) (body : Stmt) : Stmt :=
  .seq (.const B 0) (forLoop V Nr C K (.seq body (.ifle X skip (mxS B B Y))))

def MaxOK (V Nr C K B X Y : ℕ) (Sb Sc : List ℕ) : Prop :=
  V ∉ Sb ∧ Nr ∉ Sb ∧ B ∉ Sb ∧ X ∈ Sb ∧ Y ∈ Sb ∧ Sb ⊆ Sc ∧ V ∈ Sc ∧ C ∈ Sc ∧ K ∈ Sc ∧
    B ∈ Sc ∧ Nr ∉ Sc ∧ [V, Nr, C, K, B].Nodup ∧ 102 ∈ Sc ∧ 103 ∈ Sc ∧ B ∉ [102, 103] ∧
    Y ∉ [102, 103] ∧ V ∉ [102, 103] ∧ Nr ∉ [102, 103] ∧ 9 ∉ Sc

theorem h_maxLoop (V Nr C K B X Y : ℕ) (body : Stmt) (Sb Sc : List ℕ)
    (hok : MaxOK V Nr C K B X Y Sb Sc) (N c : ℕ) (p : ℕ → Prop) (g : ℕ → ℝ) (σ0 : Cfg)
    (hN : σ0.regs Nr = N)
    (hbody : ∀ m < N, ∀ σ : Cfg, σ.mem = σ0.mem → Fr Sc σ0 σ → σ.regs V = m →
      Runs body σ (fun k σ' => k ≤ c ∧ σ'.mem = σ.mem ∧ Fr Sb σ σ' ∧
        σ'.regs X = (if p m then 1 else 0) ∧ (p m → σ'.regs Y = g m))) :
    Runs (maxLoop V Nr C K B X Y body) σ0 (fun k σ' => k ≤ N * (c + 15) + 4 ∧
      σ'.mem = σ0.mem ∧ Fr Sc σ0 σ' ∧ σ'.regs B = fmax p g N) := by
  obtain ⟨hV, hNb, hBb, hX, hY, hSb, hVc, hCc, hKc, hBc, hNc, hnd, h102, h103, hB23, hY23,
    hV23, hN23, h9⟩ := hok
  have hVN : V ≠ Nr := fun h => by simp [h] at hnd
  have hVC : V ≠ C := fun h => by simp [h] at hnd
  have hVK : V ≠ K := fun h => by simp [h] at hnd
  have hVB : V ≠ B := fun h => by simp [h] at hnd
  have hNC : Nr ≠ C := fun h => by simp [h] at hnd
  have hNK : Nr ≠ K := fun h => by simp [h] at hnd
  have hNB : Nr ≠ B := fun h => by simp [h] at hnd
  have hCK : C ≠ K := fun h => by simp [h] at hnd
  have hCB : C ≠ B := fun h => by simp [h] at hnd
  have hKB : K ≠ B := fun h => by simp [h] at hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hB23 hY23 hV23 hN23
  let I : ℕ → Cfg → Prop := fun m σ => σ.mem = σ0.mem ∧ Fr Sc σ0 σ ∧ σ.regs B = fmax p g m
  refine r_seq (r_mono (h_const σ0 B 0) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_for V Nr C K _ hVN hVC hVK hNC hNK hCK N (c + 10) I σ1
    (by rw [hf1 Nr (by simp [hNB]), hN]) ?_ ?_ _ ?_
  · intro a b
    refine ⟨hm1, ?_, ?_⟩
    · intro r hr
      have h1 : r ≠ C := fun h => hr (h ▸ hCc)
      have h2 : r ≠ V := fun h => hr (h ▸ hVc)
      simp only [update_apply, h1, h2, if_false]
      exact hf1 r (by simp; intro h; exact hr (h ▸ hBc))
    · simp [update_apply, Ne.symm hCB, Ne.symm hVB, hv1, fmax]
  · intro m hm σ ⟨hmσ, hfσ, hBσ⟩ hVm hNm
    refine r_seq (r_mono (hbody m hm σ hmσ hfσ hVm) fun k2 σ2 ⟨hk2, hm2, hf2, hX2, hY2⟩ => ?_)
    have fin : ∀ σ7 : Cfg, σ7.mem = σ0.mem → Fr Sc σ0 σ7 → σ7.regs V = m → σ7.regs Nr = N →
        σ7.regs B = fmax p g (m + 1) →
        σ7.regs V = m ∧ σ7.regs Nr = N ∧ ∀ a b e, I (m + 1)
          ⟨update (update (update σ7.regs K a) V b) C e, σ7.ptrs, σ7.mem⟩ := by
      intro σ7 h7m h7f h7V h7N h7B
      refine ⟨h7V, h7N, fun a b e => ⟨h7m, ?_, ?_⟩⟩
      · intro r hr
        have h1 : r ≠ C := fun h => hr (h ▸ hCc)
        have h2 : r ≠ V := fun h => hr (h ▸ hVc)
        have h3 : r ≠ K := fun h => hr (h ▸ hKc)
        simp only [update_apply, h1, h2, h3, if_false]
        exact h7f r hr
      · simp only [update_apply, Ne.symm hCB, Ne.symm hVB, Ne.symm hKB, if_false]; exact h7B
    have hfc2 : Fr Sc σ0 σ2 := Fr.tr hfσ (hf2.mono hSb)
    refine r_ifle ?_ ?_
    · intro hX0
      refine r_mono (h_skip σ2) fun k3 σ3 ⟨hk3, hm3, hf3⟩ => ⟨by omega, ?_⟩
      have hσ3 : σ3.regs = σ2.regs := funext fun r => hf3 r (by simp)
      have hpm : ¬ p m := by intro hp; rw [hX2, if_pos hp] at hX0; norm_num at hX0
      refine fin σ3 (by rw [hm3, hm2, hmσ]) (fun r hr => by rw [hσ3]; exact hfc2 r hr)
        (by rw [hσ3, hf2 V hV, hVm]) (by rw [hσ3, hf2 Nr hNb, hNm]) ?_
      rw [hσ3, hf2 B hBb, hBσ]; simp [fmax, hpm]
    · intro hX0
      have hpm : p m := by by_contra hp; rw [hX2, if_neg hp] at hX0; norm_num at hX0
      refine r_mono (h_mxS σ2 B B Y (by simp [hB23.1, hB23.2]) (by simp [hY23.1, hY23.2])
        hB23.2) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ⟨by omega, ?_⟩
      have hS3 : [102, 103, B] ⊆ Sc := by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h102
        · exact h103
        · exact hBc
      refine fin σ3 (by rw [hm3, hm2, hmσ]) (Fr.tr hfc2 (hf3.mono hS3))
        (by rw [hf3 V (by simp [hV23.1, hV23.2, hVB]), hf2 V hV, hVm])
        (by rw [hf3 Nr (by simp [hN23.1, hN23.2, hNB]), hf2 Nr hNb, hNm]) ?_
      rw [hv3, hf2 B hBb, hBσ, hY2 hpm]; simp [fmax, hpm]
  · intro k σ' hk ⟨hm', hf', hB'⟩
    exact ⟨by
      have : N * (c + 10 + 5) = N * (c + 15) := by ring
      omega, hm', hf', hB'⟩

/-- `M[b + m] := X(m)` for `m < N` (`b` in register `Br`, address in `Ad`). -/
def fillLoop (V Nr C K Br Ad X : ℕ) (body : Stmt) : Stmt :=
  forLoop V Nr C K (.seq body (.seq (.add Ad Br V) (stA Ad X)))

def FillOK (V Nr C K Br Ad X : ℕ) (Sb Sc : List ℕ) : Prop :=
  V ∉ Sb ∧ Nr ∉ Sb ∧ Br ∉ Sb ∧ X ∈ Sb ∧ Sb ⊆ Sc ∧ V ∈ Sc ∧ C ∈ Sc ∧ K ∈ Sc ∧ Ad ∈ Sc ∧
    100 ∈ Sc ∧ 101 ∈ Sc ∧ Nr ∉ Sc ∧ Br ∉ Sc ∧ [V, Nr, C, K, Ad].Nodup ∧ Br ≠ Ad ∧
    X ≠ Ad ∧ Ad ≠ 100 ∧ X ≠ 100 ∧ X ≠ 101 ∧ V ∉ [100, 101] ∧ Nr ∉ [100, 101] ∧ Br ≠ V

theorem h_fillLoop (V Nr C K Br Ad X : ℕ) (body : Stmt) (Sb Sc : List ℕ)
    (hok : FillOK V Nr C K Br Ad X Sb Sc) (N c b : ℕ) (g : ℕ → ℝ) (σ0 : Cfg)
    (hN : σ0.regs Nr = N) (hb : σ0.regs Br = b)
    (hbody : ∀ m < N, ∀ σ : Cfg, (∀ z : ℤ, ¬ ((b : ℤ) ≤ z ∧ z < b + m) → σ.mem z = σ0.mem z) →
      Fr Sc σ0 σ → σ.regs V = m →
      Runs body σ (fun k σ' => k ≤ c ∧ σ'.mem = σ.mem ∧ Fr Sb σ σ' ∧ σ'.regs X = g m)) :
    Runs (fillLoop V Nr C K Br Ad X body) σ0 (fun k σ' => k ≤ N * (c + 4 * (b + N) + 13) + 3 ∧
      Fr Sc σ0 σ' ∧ (∀ z : ℤ, ¬ ((b : ℤ) ≤ z ∧ z < b + N) → σ'.mem z = σ0.mem z) ∧
      ∀ m < N, σ'.mem ((b + m : ℕ) : ℤ) = g m) := by
  obtain ⟨hV, hNb, hBb, hX, hSb, hVc, hCc, hKc, hAc, h100, h101, hNc, hBc, hnd, hBA, hXA,
    hA0, hX0, hX1, hV01, hN01, hBV⟩ := hok
  have hVN : V ≠ Nr := fun h => by simp [h] at hnd
  have hVC : V ≠ C := fun h => by simp [h] at hnd
  have hVK : V ≠ K := fun h => by simp [h] at hnd
  have hVA : V ≠ Ad := fun h => by simp [h] at hnd
  have hNC : Nr ≠ C := fun h => by simp [h] at hnd
  have hNK : Nr ≠ K := fun h => by simp [h] at hnd
  have hNA : Nr ≠ Ad := fun h => by simp [h] at hnd
  have hCK : C ≠ K := fun h => by simp [h] at hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hV01 hN01
  let I : ℕ → Cfg → Prop := fun m σ => Fr Sc σ0 σ ∧
    (∀ z : ℤ, ¬ ((b : ℤ) ≤ z ∧ z < b + m) → σ.mem z = σ0.mem z) ∧
    ∀ j < m, σ.mem ((b + j : ℕ) : ℤ) = g j
  refine r_for V Nr C K _ hVN hVC hVK hNC hNK hCK N (c + 4 * (b + N) + 8) I σ0 hN ?_ ?_ _ ?_
  · intro a e
    refine ⟨?_, fun z _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    intro r hr
    have h1 : r ≠ C := fun h => hr (h ▸ hCc)
    have h2 : r ≠ V := fun h => hr (h ▸ hVc)
    simp only [update_apply, h1, h2, if_false]
  · intro m hm σ ⟨hfσ, hmσ, hgσ⟩ hVm hNm
    refine r_seq (r_mono (hbody m hm σ hmσ hfσ hVm) fun k2 σ2 ⟨hk2, hm2, hf2, hX2⟩ => ?_)
    refine r_seq (r_mono (h_add σ2 Ad Br V) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
    have hA3 : σ3.regs Ad = ((b + m : ℕ) : ℝ) := by
      rw [hv3, hf2 Br hBb, hf2 V hV, hfσ Br hBc, hb, hVm]; push_cast; ring
    refine r_mono (h_stA σ3 Ad X hA0 hX0 hX1 (b + m) hA3) fun k4 σ4 ⟨hk4, hm4, hf4⟩ =>
      ⟨?_, ?_, ?_, fun a e f => ⟨?_, ?_, ?_⟩⟩
    · have : b + m ≤ b + N := by omega
      omega
    · rw [hf4 V (by simp [hV01.1, hV01.2]), hf3 V (by simp [hVA]), hf2 V hV, hVm]
    · rw [hf4 Nr (by simp [hN01.1, hN01.2]), hf3 Nr (by simp [hNA]), hf2 Nr hNb, hNm]
    · intro r hr
      have h1 : r ≠ C := fun h => hr (h ▸ hCc)
      have h2 : r ≠ V := fun h => hr (h ▸ hVc)
      have h3 : r ≠ K := fun h => hr (h ▸ hKc)
      simp only [update_apply, h1, h2, h3, if_false]
      have h4 : r ∉ [100, 101] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun h => hr (h ▸ h100), fun h => hr (h ▸ h101)⟩
      rw [hf4 r h4, hf3 r (by simp; intro h; exact hr (h ▸ hAc)), hf2 r (fun h => hr (hSb h))]
      exact hfσ r hr
    · intro z hz
      show σ4.mem z = σ0.mem z
      rw [hm4, hm3]
      have hz' : z ≠ ((b + m : ℕ) : ℤ) := by push_cast; intro h; apply hz; omega
      rw [update_of_ne hz', hm2]
      exact hmσ z (by intro h; apply hz; push_cast at h ⊢; omega)
    · intro j hj
      show σ4.mem _ = g j
      rw [hm4, hm3]
      by_cases hjm : j = m
      · subst hjm
        rw [update_self, hf3 X (by simp [hXA]), hX2]
      · rw [update_of_ne (by push_cast; omega), hm2]
        exact hgσ j (by omega)
  · intro k σ' hk ⟨hf', hm', hg'⟩
    exact ⟨by
      have : N * (c + 4 * (b + N) + 8 + 5) = N * (c + 4 * (b + N) + 13) := by ring
      omega, hf', hm', hg'⟩

end OnlineTransportation1195.Dev.T13.PartPR
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.T13.PartPR
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
  OnlineTransportation1195.Dev.T13 OnlineTransportation1195.Dev.RL.Lib Function
variable {n : ℕ} (T : Tree n) (S : Finset (Fin n))
/-!
Part PR, file 2: the iterative depth-first search (a state machine) computes `dfsS`, and
`dfsS` has at most `2n - 1` entries.
-/
/-- The child predicate of the scan: `w` is a child of `u` in `S` with index at least `c`. -/
def ChildP (u : Fin n) (c : ℕ) (w : ℕ) : Prop :=
  ∃ h : w < n, (⟨w, h⟩ : Fin n) ∈ S ∧ (⟨w, h⟩ : Fin n) ≠ T.root ∧ T.parent ⟨w, h⟩ = u ∧ c ≤ w

/-- Least child of `u` in `S` with index at least `c`. -/
noncomputable def nextC (u : Fin n) (c : ℕ) : Option ℕ := ffind (ChildP T S u c) n

/-- One step of the machine for the search from `v`. -/
noncomputable def mstep (v : Fin n) (st : Fin n × ℕ) : Option (Fin n × ℕ) :=
  match nextC T S st.1 st.2 with
  | some w => if h : w < n then some (⟨w, h⟩, 0) else none
  | none => if st.1 = v then none else some (T.parent st.1, st.1.val + 1)

/-- The machine emits `L` going from `st` to `st'`. -/
inductive MR (v : Fin n) : Fin n × ℕ → List (Fin n) → Fin n × ℕ → Prop
  | nil (st : Fin n × ℕ) : MR v st [] st
  | cons (st st' st'' : Fin n × ℕ) (L : List (Fin n)) :
      mstep T S v st = some st' → MR v st' L st'' → MR v st (st'.1 :: L) st''

theorem MR_append (v : Fin n) {s1 s2 s3 : Fin n × ℕ} {L1 L2 : List (Fin n)}
    (h1 : MR T S v s1 L1 s2) (h2 : MR T S v s2 L2 s3) : MR T S v s1 (L1 ++ L2) s3 := by
  induction h1 with
  | nil st => exact h2
  | cons st st' st'' L h hr ih => exact MR.cons _ _ _ _ h (ih h2)

/-- The children of `u` in `S`, in increasing order. -/
noncomputable def csOf (u : Fin n) : List (Fin n) :=
  (children T u).filter (fun c => decide (c ∈ S))

theorem csOf_pairwise (u : Fin n) : (csOf T S u).Pairwise (fun a b => a.val < b.val) := by
  unfold csOf children
  refine List.Pairwise.filter _ (List.Pairwise.filter _ ?_)
  exact List.pairwise_lt_finRange n

theorem nextC_eq (u : Fin n) (c : ℕ) :
    nextC T S u c = (((csOf T S u).filter (fun w => decide (c ≤ w.val))).head?).map Fin.val := by
  unfold nextC ffind csOf children
  rw [List.filter_filter, List.filter_filter, ← List.map_coe_finRange_eq_range, List.find?_map,
    List.head?_filter]
  congr 1
  congr 1
  funext w
  simp only [Function.comp, ChildP, Fin.eta]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨h, h1, h2, h3, h4⟩
    exact ⟨⟨h4, h1⟩, h2, h3⟩
  · rintro ⟨⟨h4, h1⟩, h2, h3⟩
    exact ⟨w.isLt, h1, h2, h3, h4⟩

theorem filter_sorted_next (l : List (Fin n)) (hl : l.Pairwise (fun a b => a.val < b.val))
    (c : ℕ) (w : Fin n) (r : List (Fin n))
    (h : l.filter (fun x => decide (c ≤ x.val)) = w :: r) :
    l.filter (fun x => decide (w.val + 1 ≤ x.val)) = r := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    by_cases hca : c ≤ a.val
    · rw [List.filter_cons_of_pos (by simpa using hca)] at h
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      rw [List.filter_cons_of_neg (by simp)]
      rw [List.filter_eq_self.mpr, List.filter_eq_self.mpr]
      · intro x hx; have := hl.1 x hx; simp; omega
      · intro x hx; have := hl.1 x hx; simp; omega
    · rw [List.filter_cons_of_neg (by simpa using hca)] at h
      have hw : w ∈ l := by
        have : w ∈ l.filter (fun x => decide (c ≤ x.val)) := by rw [h]; simp
        exact (List.mem_filter.mp this).1
      have := hl.1 w hw
      rw [List.filter_cons_of_neg (by simp; omega)]
      exact ih hl.2 h

theorem isAnc_child {u w : Fin n} (hw : w ≠ T.root) (hp : T.parent w = u) : T.IsAnc u w :=
  ⟨1, by simp [hp]⟩

/-- The machine run over the subtree of `u`. -/
theorem machine_sub (v : Fin n) :
    ∀ k : ℕ, ∀ u : Fin n, (∀ w, T.IsAnc u w → T.depth w ≤ T.depth u + k) →
      (u = v ∨ ¬ T.IsAnc u v) →
      ∃ c', MR T S v (u, 0) (dfsF T S k u).tail (u, c') ∧ nextC T S u c' = none := by
  intro k
  induction k with
  | zero =>
    intro u hk _
    refine ⟨0, MR.nil _, ?_⟩
    rw [nextC_eq]
    cases h : ((csOf T S u).filter (fun w => decide (0 ≤ w.val))).head? with
    | none => rfl
    | some w =>
      exfalso
      have hw := List.mem_of_mem_head? h
      rw [List.mem_filter, csOf, PartB.mem_cs] at hw
      obtain ⟨⟨⟨hwr, hwp⟩, -⟩, -⟩ := hw
      have h1 := hk w (isAnc_child T hwr hwp)
      have h2 := PartB.depth_child T hwr
      rw [hwp] at h2
      omega
  | succ k ih =>
    intro u hk hu
    -- the inner induction over the remaining children
    have inner : ∀ (rest : List (Fin n)) (c : ℕ),
        (csOf T S u).filter (fun w => decide (c ≤ w.val)) = rest →
        ∃ c', MR T S v (u, c) (rest.flatMap (fun w => dfsF T S k w ++ [u])) (u, c') ∧
          nextC T S u c' = none := by
      intro rest
      induction rest with
      | nil =>
        intro c hc
        refine ⟨c, MR.nil _, ?_⟩
        rw [nextC_eq, hc]; rfl
      | cons w rest' ihr =>
        intro c hc
        have hwmem : w ∈ csOf T S u := by
          have : w ∈ (csOf T S u).filter (fun w => decide (c ≤ w.val)) := by rw [hc]; simp
          exact (List.mem_filter.mp this).1
        rw [csOf, PartB.mem_cs] at hwmem
        obtain ⟨⟨hwr, hwp⟩, hwS⟩ := hwmem
        have hdw := PartB.depth_child T hwr
        rw [hwp] at hdw
        have huw : T.IsAnc u w := isAnc_child T hwr hwp
        have hnotw : ¬ T.IsAnc w v := by
          intro hwv
          rcases hu with rfl | hu
          · have := (PartB.anc_eq T hwv).2; omega
          · exact hu (PartB.anc_trans' T huw hwv)
        have hwv : w ≠ v := by intro h; exact hnotw (h ▸ PartB.anc_refl T w)
        obtain ⟨c1, hM1, hn1⟩ := ih w (by
          intro x hx
          have := hk x (PartB.anc_trans' T huw hx); omega) (Or.inr hnotw)
        obtain ⟨c2, hM2, hn2⟩ := ihr (w.val + 1)
          (filter_sorted_next (csOf T S u) (csOf_pairwise T S u) c w rest' hc)
        refine ⟨c2, ?_, hn2⟩
        have hstep1 : mstep T S v (u, c) = some (w, 0) := by
          unfold mstep
          simp only
          rw [nextC_eq, hc]
          simp [w.isLt]
        have hstep2 : mstep T S v (w, c1) = some (u, w.val + 1) := by
          unfold mstep
          simp only
          rw [hn1]
          simp [hwv, hwp]
        have hD : dfsF T S k w = w :: (dfsF T S k w).tail := by
          have := PartB.dfsF_head T S k w
          cases h : dfsF T S k w with
          | nil => rw [h] at this; simp at this
          | cons a l => rw [h] at this; simp at this; rw [this]; rfl
        rw [List.flatMap_cons, hD, List.cons_append, List.cons_append]
        refine MR.cons _ (w, 0) _ _ hstep1 ?_
        rw [List.append_assoc]
        refine MR_append T S v hM1 ?_
        rw [List.singleton_append]
        exact MR.cons _ (u, w.val + 1) _ _ hstep2 hM2
    obtain ⟨c', h1, h2⟩ := inner (csOf T S u) 0 (by
      rw [List.filter_eq_self.mpr]; intro x _; simp)
    refine ⟨c', ?_, h2⟩
    rw [PartB.dfsF_succ]
    exact h1

/-- The whole search from `v`. -/
theorem machine_dfs (v : Fin n) :
    ∃ c', MR T S v (v, 0) (dfsS T S v).tail (v, c') ∧ mstep T S v (v, c') = none := by
  obtain ⟨c', h1, h2⟩ := machine_sub T S v n v (by
    intro w _; have := PartB.depth_lt T w; omega) (Or.inl rfl)
  refine ⟨c', h1, ?_⟩
  unfold mstep
  simp only
  rw [h2]
  simp

/-- The deterministic step (staying put when stopped). -/
noncomputable def fstep (v : Fin n) (st : Fin n × ℕ) : Fin n × ℕ := (mstep T S v st).getD st

theorem MR_iter (v : Fin n) {st st' : Fin n × ℕ} {L : List (Fin n)} (h : MR T S v st L st') :
    (∀ m < L.length, mstep T S v ((fstep T S v)^[m] st) = some ((fstep T S v)^[m + 1] st) ∧
      ((fstep T S v)^[m + 1] st).1 = T.vertexAt L m) ∧ (fstep T S v)^[L.length] st = st' := by
  induction h with
  | nil st => exact ⟨fun m hm => absurd hm (Nat.not_lt_zero _), rfl⟩
  | cons st st' st'' L h hr ih =>
    have hf : fstep T S v st = st' := by unfold fstep; rw [h]; rfl
    refine ⟨?_, ?_⟩
    · intro m hm
      cases m with
      | zero => simp [h, hf, Tree.vertexAt]
      | succ m =>
        obtain ⟨h1, h2⟩ := ih.1 m (by simpa using hm)
        rw [Function.iterate_succ_apply, hf, Function.iterate_succ_apply, hf]
        exact ⟨h1, by rw [h2]; simp [Tree.vertexAt]⟩
    · rw [List.length_cons, Function.iterate_succ_apply, hf]
      exact ih.2

/-- The iterate characterization of `dfsS`. -/
theorem dfs_iter (v : Fin n) :
    (dfsS T S v).length ≥ 1 ∧ T.vertexAt (dfsS T S v) 0 = v ∧
      (∀ m, m + 1 < (dfsS T S v).length →
        mstep T S v ((fstep T S v)^[m] (v, 0)) = some ((fstep T S v)^[m + 1] (v, 0)) ∧
        ((fstep T S v)^[m + 1] (v, 0)).1 = T.vertexAt (dfsS T S v) (m + 1)) ∧
      mstep T S v ((fstep T S v)^[(dfsS T S v).length - 1] (v, 0)) = none := by
  obtain ⟨c', hM, hn⟩ := machine_dfs T S v
  obtain ⟨h1, h2⟩ := MR_iter T S v hM
  have hD : dfsS T S v = v :: (dfsS T S v).tail := by
    have := PartB.dfsF_head T S n v
    unfold dfsS
    cases h : dfsF T S n v with
    | nil => rw [h] at this; simp at this
    | cons a l => rw [h] at this; simp at this; rw [this]; rfl
  have hlen : (dfsS T S v).length = (dfsS T S v).tail.length + 1 := by
    conv_lhs => rw [hD]
    simp
  refine ⟨by omega, by rw [hD]; simp [Tree.vertexAt], ?_, ?_⟩
  · intro m hm
    obtain ⟨h3, h4⟩ := h1 m (by omega)
    refine ⟨h3, ?_⟩
    rw [h4]
    conv_rhs => rw [hD]
    simp [Tree.vertexAt]
  · rw [show (dfsS T S v).length - 1 = (dfsS T S v).tail.length by omega, h2]
    exact hn

/-! ## The length of a restricted search -/
theorem dfsS_length (v : Fin n) : (dfsS T S v).length ≤ 2 * n - 1 := by
  set D := dfsS T S v with hDdef
  have hpath : IsPath T D := (PartB.isPath_iff T _).mpr (PartB.SS_bad_dfsF T S n v)
  have hstep : ∀ j ∈ Finset.range (D.length - 1),
      1 ≤ ∑ e ∈ T.edges, (PartB.dφ T e (T.vertexAt D j) (T.vertexAt D (j + 1)) +
        PartB.uφ T e (T.vertexAt D j) (T.vertexAt D (j + 1))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hadj := hpath j (by omega)
    rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hmem : T.vertexAt D (j + 1) ∈ T.edges := (mem_edges_iff T _).mpr h1
      refine le_trans ?_ (Finset.single_le_sum (f := fun e => PartB.dφ T e (T.vertexAt D j)
        (T.vertexAt D (j + 1)) + PartB.uφ T e (T.vertexAt D j) (T.vertexAt D (j + 1)))
        (fun _ _ => Nat.zero_le _) hmem)
      simp [PartB.dφ, h2]
    · have hmem : T.vertexAt D j ∈ T.edges := (mem_edges_iff T _).mpr h1
      refine le_trans ?_ (Finset.single_le_sum (f := fun e => PartB.dφ T e (T.vertexAt D j)
        (T.vertexAt D (j + 1)) + PartB.uφ T e (T.vertexAt D j) (T.vertexAt D (j + 1)))
        (fun _ _ => Nat.zero_le _) hmem)
      simp [PartB.uφ, h2]
  have h1 : D.length - 1 ≤ ∑ e ∈ T.edges, (PartB.SS T (PartB.dφ T e) D +
      PartB.SS T (PartB.uφ T e) D) := by
    have := Finset.sum_le_sum hstep
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at this
    refine this.trans (le_of_eq ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    unfold PartB.SS
    rw [Finset.sum_add_distrib]
  have h2 : ∑ e ∈ T.edges, (PartB.SS T (PartB.dφ T e) D + PartB.SS T (PartB.uφ T e) D) ≤
      ∑ e ∈ T.edges, 2 := by
    refine Finset.sum_le_sum fun e he => ?_
    have her : e ≠ T.root := (mem_edges_iff T e).mp he
    rw [hDdef, PartB.count_dfsS_down T S v e her, PartB.count_dfsS_up T S v e her]
    split_ifs <;> omega
  have h3 : T.edges.card = n - 1 := by
    unfold Tree.edges
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_const, h3, smul_eq_mul] at h2
  have hn : 0 < n := Fin.pos T.root
  omega

end OnlineTransportation1195.Dev.T13.PartPR
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.T13.PartPR
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
  OnlineTransportation1195.Dev.T13 OnlineTransportation1195.Dev.RL.Lib Function
/-!
Part PR, file 3: the program of the restricted depth-first search.
Registers: `1 = n`, `2 = root`, `110` = flag base, `111` = output base, `112` = start vertex;
result length in `135`.
-/
theorem cval_eq {n : ℕ} (a b : Fin n) : ((a.val : ℝ) = (b.val : ℝ)) ↔ a = b := by
  rw [Nat.cast_inj, Fin.val_inj]

theorem castv_eq {n : ℕ} (w : ℕ) (hw : w < n) (a : Fin n) :
    ((w : ℝ) = (a.val : ℝ)) ↔ (⟨w, hw⟩ : Fin n) = a := by
  rw [Nat.cast_inj, Fin.ext_iff]

/-- `X := [w is a child of u in S with index ≥ c]` (`w` in `117`). -/
def nextBody : Stmt :=
  .seq (.add 125 110 117) (.seq (ld 126 125) (.seq (eqT 127 117 2) (.seq (notF 127 127)
    (.seq (ldIn 128 2 117) (.seq (eqT 129 128 113) (.seq (leF 130 114 117)
    (.seq (.mul 122 126 127) (.seq (.mul 122 122 129) (.mul 122 122 130)))))))))

def SNB : List ℕ := [100, 101, 102, 122, 125, 126, 127, 128, 129, 130]

end OnlineTransportation1195.Dev.T13.PartPR
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.T13.PartPR
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
  OnlineTransportation1195.Dev.T13 OnlineTransportation1195.Dev.RL.Lib Function
variable {n : ℕ} (T : Tree n) (S : Finset (Fin n))
theorem childP_iff (u : Fin n) (c w : ℕ) (hw : w < n) :
    ChildP T S u c w ↔ (⟨w, hw⟩ : Fin n) ∈ S ∧ (⟨w, hw⟩ : Fin n) ≠ T.root ∧
      T.parent ⟨w, hw⟩ = u ∧ c ≤ w := by
  unfold ChildP
  constructor
  · rintro ⟨h, h1⟩; exact h1
  · intro h1; exact ⟨hw, h1⟩

theorem h_nextBody (σ : Cfg) (fb : ℕ) (u : Fin n) (c w : ℕ) (hw : w < n)
    (h2 : σ.regs 2 = T.root.val) (h110 : σ.regs 110 = fb) (h113 : σ.regs 113 = u.val)
    (h114 : σ.regs 114 = c) (h117 : σ.regs 117 = w)
    (hflag : σ.mem ((fb + w : ℕ) : ℤ) = if (⟨w, hw⟩ : Fin n) ∈ S then 1 else 0)
    (hpar : σ.mem ((2 + 3 * w : ℕ) : ℤ) = (T.parent ⟨w, hw⟩).val) :
    Runs nextBody σ (fun k σ' => k ≤ 4 * fb + 16 * n + 46 ∧ σ'.mem = σ.mem ∧ Fr SNB σ σ' ∧
      σ'.regs 122 = if ChildP T S u c w then 1 else 0) := by
  refine r_seq (r_mono (h_add σ 125 110 117) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  have e1 : σ1.regs 125 = ((fb + w : ℕ) : ℝ) := by rw [hv1, h110, h117]; push_cast; ring
  refine r_seq (r_mono (h_ld σ1 126 125 (by decide) _ e1) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_eqT σ2 127 117 2 (by decide) (by decide) (by decide))
    fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  refine r_seq (r_mono (h_notF σ3 127 127 (by decide)) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
  have e117 : σ4.regs 117 = (w : ℝ) := by
    rw [hf4 117 (by decide), hf3 117 (by decide), hf2 117 (by decide), hf1 117 (by decide), h117]
  refine r_seq (r_mono (h_ldIn σ4 128 2 117 (by decide) w e117) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
  refine r_seq (r_mono (h_eqT σ5 129 128 113 (by decide) (by decide) (by decide))
    fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)
  refine r_seq (r_mono (h_leF σ6 130 114 117) fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ => ?_)
  refine r_seq (r_mono (h_mul σ7 122 126 127) fun k8 σ8 ⟨hk8, hm8, hf8, hv8⟩ => ?_)
  refine r_seq (r_mono (h_mul σ8 122 122 129) fun k9 σ9 ⟨hk9, hm9, hf9, hv9⟩ => ?_)
  refine r_mono (h_mul σ9 122 122 130) fun k10 σ10 ⟨hk10, hm10, hf10, hv10⟩ => ⟨?_, ?_, ?_, ?_⟩
  · have : w ≤ n := hw.le
    omega
  · rw [hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]
  · intro r hr
    simp only [SNB, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hf10 r (by simp [hr]), hf9 r (by simp [hr]), hf8 r (by simp [hr]),
      hf7 r (by simp [hr]), hf6 r (by simp [hr]), hf5 r (by simp [hr]), hf4 r (by simp [hr]),
      hf3 r (by simp [hr]), hf2 r (by simp [hr]), hf1 r (by simp [hr])]
  · -- the value
    have v126 : σ9.regs 126 = if (⟨w, hw⟩ : Fin n) ∈ S then 1 else 0 := by
      rw [hf9 126 (by decide), hf8 126 (by decide), hf7 126 (by decide), hf6 126 (by decide),
        hf5 126 (by decide), hf4 126 (by decide), hf3 126 (by decide), hv2, hm1, hflag]
    have v127 : σ9.regs 127 = if (⟨w, hw⟩ : Fin n) = T.root then 0 else 1 := by
      rw [hf9 127 (by decide), hf8 127 (by decide), hf7 127 (by decide), hf6 127 (by decide),
        hf5 127 (by decide), hv4, hv3, hf2 117 (by decide), hf1 117 (by decide), h117,
        hf2 2 (by decide), hf1 2 (by decide), h2]
      simp only [castv_eq w hw]
      split_ifs <;> norm_num
    have v129 : σ9.regs 129 = if T.parent ⟨w, hw⟩ = u then 1 else 0 := by
      rw [hf9 129 (by decide), hf8 129 (by decide), hf7 129 (by decide), hv6, hv5,
        hf5 113 (by decide), hf4 113 (by decide), hf3 113 (by decide), hf2 113 (by decide),
        hf1 113 (by decide), h113, hm4, hm3, hm2, hm1, hpar]
      simp only [cval_eq]
    have v130 : σ9.regs 130 = if c ≤ w then 1 else 0 := by
      rw [hf9 130 (by decide), hf8 130 (by decide), hv7, hf6 114 (by decide),
        hf5 114 (by decide), hf4 114 (by decide), hf3 114 (by decide), hf2 114 (by decide),
        hf1 114 (by decide), h114, hf6 117 (by decide), hf5 117 (by decide), e117]
      simp only [Nat.cast_le]
    rw [hv10, hv9, hf8 129 (by decide), hv8,
      show σ7.regs 126 = σ9.regs 126 by rw [hf9 126 (by decide), hf8 126 (by decide)],
      show σ7.regs 127 = σ9.regs 127 by rw [hf9 127 (by decide), hf8 127 (by decide)],
      show σ7.regs 129 = σ9.regs 129 by rw [hf9 129 (by decide), hf8 129 (by decide)],
      v126, v127, v129, v130, childP_iff T S u c w hw]
    by_cases a1 : (⟨w, hw⟩ : Fin n) ∈ S <;> by_cases a2 : (⟨w, hw⟩ : Fin n) = T.root <;>
      by_cases a3 : T.parent ⟨w, hw⟩ = u <;> by_cases a4 : c ≤ w <;> simp [a1, a2, a3, a4]

/-- One step of the search. -/
def dfsFound : Stmt :=
  .seq (.const 131 1) (.seq (.add 115 115 131) (.seq (.add 132 111 115) (.seq (stA 132 121)
    (.seq (mov 113 121) (.const 114 0)))))

def dfsUp : Stmt :=
  .seq (.const 131 1) (.seq (.add 115 115 131) (.seq (.add 132 111 115) (.seq (ldIn 134 2 113)
    (.seq (stA 132 134) (.seq (.add 114 113 131) (mov 113 134))))))

def dfsBody : Stmt :=
  .seq (findLoop 117 1 118 119 120 121 122 123 124 nextBody)
    (.ifle 120 (.seq (eqT 133 113 112) (.ifle 133 dfsUp (.const 116 0))) dfsFound)

/-- The search: start vertex in `112`, flags at base `110`, output at base `111`. -/
def dfsProg : Stmt :=
  .seq (mov 113 112) (.seq (.const 114 0) (.seq (.const 115 0) (.seq (stA 111 112)
    (.seq (.const 116 1) (.seq (.whilegt 116 dfsBody) (.seq (.const 131 1) (.add 135 115 131)))))))

def SFind : List ℕ := [100, 101, 102, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
  128, 129, 130]

def SD : List ℕ := [100, 101, 102, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124,
  125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]

theorem h_dfsBody (σ : Cfg) (fb ob : ℕ) (v u : Fin n) (c i : ℕ)
    (h1 : σ.regs 1 = n) (h2 : σ.regs 2 = T.root.val) (h110 : σ.regs 110 = fb)
    (h111 : σ.regs 111 = ob) (h112 : σ.regs 112 = v.val) (h113 : σ.regs 113 = u.val)
    (h114 : σ.regs 114 = c) (h115 : σ.regs 115 = i)
    (hflag : ∀ w : Fin n, σ.mem ((fb + w.val : ℕ) : ℤ) = if w ∈ S then 1 else 0)
    (hpar : ∀ w : Fin n, σ.mem ((2 + 3 * w.val : ℕ) : ℤ) = (T.parent w).val) :
    Runs dfsBody σ (fun k σ' => k ≤ n * (4 * fb + 16 * n + 61) + 12 * n + 4 * ob + 4 * i + 46 ∧
      Fr SD σ σ' ∧
      (∀ st', mstep T S v (u, c) = some st' → σ'.regs 115 = ((i + 1 : ℕ) : ℝ) ∧
        σ'.regs 113 = st'.1.val ∧ σ'.regs 114 = st'.2 ∧ σ'.regs 116 = σ.regs 116 ∧
        σ'.mem = update σ.mem ((ob + (i + 1) : ℕ) : ℤ) (st'.1.val : ℝ)) ∧
      (mstep T S v (u, c) = none → σ'.regs 115 = i ∧ σ'.regs 116 = 0 ∧ σ'.mem = σ.mem)) := by
  refine r_seq (r_mono (h_findLoop 117 1 118 119 120 121 122 123 124 nextBody SNB SFind
    (by unfold FindOK SNB SFind; decide) n (4 * fb + 16 * n + 46) (ChildP T S u c) σ h1 ?_)
    fun k1 σ1 ⟨hk1, hm1, hf1, hF1, hR1⟩ => ?_)
  · intro m hm σ' hm' hf' hV'
    refine h_nextBody T S σ' fb u c m hm (by rw [hf' 2 (by decide), h2])
      (by rw [hf' 110 (by decide), h110]) (by rw [hf' 113 (by decide), h113])
      (by rw [hf' 114 (by decide), h114]) hV' (by rw [hm']; exact hflag ⟨m, hm⟩)
      (by rw [hm']; exact hpar ⟨m, hm⟩)
  have hfr1 : Fr SD σ σ1 := hf1.mono (by unfold SFind SD; decide)
  have g : ∀ r, r ∉ SFind → σ1.regs r = σ.regs r := hf1
  have hk1' : k1 ≤ n * (4 * fb + 16 * n + 61) + 5 := by
    have : n * (4 * fb + 16 * n + 46 + 15) = n * (4 * fb + 16 * n + 61) := by ring
    omega
  rcases hnc : nextC T S u c with _ | w
  · -- no child left
    have hF : σ1.regs 120 = 0 := by rw [hF1]; unfold nextC at hnc; simp [hnc]
    refine r_ifle (fun _ => ?_) (fun h => absurd (le_of_eq hF) h)
    refine r_seq (r_mono (h_eqT σ1 133 113 112 (by decide) (by decide) (by decide))
      fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
    by_cases huv : u = v
    · -- stop
      have hv2' : σ2.regs 133 = 1 := by
        rw [hv2, g 113 (by decide), g 112 (by decide), h113, h112, huv]; simp
      refine r_ifle (fun h => absurd h (by rw [hv2']; norm_num)) (fun _ => ?_)
      refine r_mono (h_const σ2 116 0) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ⟨?_, ?_, ?_, ?_⟩
      · omega
      · exact Fr.tr hfr1 (Fr.trm hf2 hf3 (by unfold SD; decide) (by unfold SD; decide))
      · intro st' hst
        unfold mstep at hst
        simp only at hst
        rw [hnc] at hst
        simp [huv] at hst
      · intro _
        refine ⟨?_, by rw [hv3]; simp, by rw [hm3, hm2, hm1]⟩
        rw [hf3 115 (by decide), hf2 115 (by decide), g 115 (by decide), h115]
    · -- go up
      have hv2' : σ2.regs 133 = 0 := by
        rw [hv2, g 113 (by decide), g 112 (by decide), h113, h112]; simp only [cval_eq]; simp [huv]
      refine r_ifle (fun _ => ?_) (fun h => absurd (le_of_eq hv2') h)
      have e113 : σ2.regs 113 = u.val := by rw [hf2 113 (by decide), g 113 (by decide), h113]
      refine r_seq (r_mono (h_const σ2 131 1) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
      refine r_seq (r_mono (h_add σ3 115 115 131) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
      refine r_seq (r_mono (h_add σ4 132 111 115) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
      have e115 : σ4.regs 115 = ((i + 1 : ℕ) : ℝ) := by
        rw [hv4, hv3, hf3 115 (by decide), hf2 115 (by decide), g 115 (by decide), h115]
        push_cast; ring
      have e132 : σ5.regs 132 = ((ob + (i + 1) : ℕ) : ℝ) := by
        rw [hv5, e115, hf4 111 (by decide), hf3 111 (by decide), hf2 111 (by decide),
          g 111 (by decide), h111]
        push_cast; ring
      have e113' : σ5.regs 113 = u.val := by
        rw [hf5 113 (by decide), hf4 113 (by decide), hf3 113 (by decide), e113]
      refine r_seq (r_mono (h_ldIn σ5 134 2 113 (by decide) u.val e113')
        fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)
      have e134 : σ6.regs 134 = (T.parent u).val := by
        rw [hv6, hm5, hm4, hm3, hm2, hm1]; exact hpar u
      refine r_seq (r_mono (h_stA σ6 132 134 (by decide) (by decide) (by decide) (ob + (i + 1))
        (by rw [hf6 132 (by decide), e132])) fun k7 σ7 ⟨hk7, hm7, hf7⟩ => ?_)
      refine r_seq (r_mono (h_add σ7 114 113 131) fun k8 σ8 ⟨hk8, hm8, hf8, hv8⟩ => ?_)
      refine r_mono (h_mov σ8 113 134 (by decide)) fun k9 σ9 ⟨hk9, hm9, hf9, hv9⟩ =>
        ⟨?_, ?_, ?_, ?_⟩
      · have : u.val < n := u.isLt
        omega
      · refine Fr.tr hfr1 (Fr.tr (hf2.mono (by unfold SD; decide)) (Fr.tr (hf3.mono
          (by unfold SD; decide)) (Fr.tr (hf4.mono (by unfold SD; decide)) (Fr.tr
          (hf5.mono (by unfold SD; decide)) (Fr.tr (hf6.mono (by unfold SD; decide))
          (Fr.tr (hf7.mono (by unfold SD; decide)) (Fr.tr (hf8.mono (by unfold SD; decide))
          (hf9.mono (by unfold SD; decide)))))))))
      · intro st' hst
        unfold mstep at hst
        simp only at hst
        rw [hnc] at hst
        simp only [huv, if_false, Option.some.injEq] at hst
        subst hst
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hf9 115 (by decide), hf8 115 (by decide), hf7 115 (by decide),
            hf6 115 (by decide), hf5 115 (by decide), e115]
        · rw [hv9, hf8 134 (by decide), hf7 134 (by decide), e134]
        · rw [hf9 114 (by decide), hv8, hf7 113 (by decide), hf6 113 (by decide), e113',
            hf7 131 (by decide), hf6 131 (by decide), hf5 131 (by decide), hf4 131 (by decide),
            hv3]
          push_cast; ring
        · rw [hf9 116 (by decide), hf8 116 (by decide), hf7 116 (by decide), hf6 116 (by decide),
            hf5 116 (by decide), hf4 116 (by decide), hf3 116 (by decide), hf2 116 (by decide),
            g 116 (by decide)]
        · rw [hm9, hm8, hm7, e134, hm6, hm5, hm4, hm3, hm2, hm1]
      · intro hst
        unfold mstep at hst
        simp only at hst
        rw [hnc] at hst
        simp [huv] at hst
  · -- a child found
    have hsome := (ffind_some _ _ _).mp hnc
    obtain ⟨hwn, hcp, -⟩ := hsome
    have hF : σ1.regs 120 = 1 := by rw [hF1]; unfold nextC at hnc; simp [hnc]
    have hR : σ1.regs 121 = (w : ℝ) := by rw [hR1]; unfold nextC at hnc; simp [hnc]
    refine r_ifle (fun h => absurd h (by rw [hF]; norm_num)) (fun _ => ?_)
    refine r_seq (r_mono (h_const σ1 131 1) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
    refine r_seq (r_mono (h_add σ3 115 115 131) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
    refine r_seq (r_mono (h_add σ4 132 111 115) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
    have e115 : σ4.regs 115 = ((i + 1 : ℕ) : ℝ) := by
      rw [hv4, hv3, hf3 115 (by decide), g 115 (by decide), h115]
      push_cast; ring
    have e132 : σ5.regs 132 = ((ob + (i + 1) : ℕ) : ℝ) := by
      rw [hv5, e115, hf4 111 (by decide), hf3 111 (by decide), g 111 (by decide), h111]
      push_cast; ring
    refine r_seq (r_mono (h_stA σ5 132 121 (by decide) (by decide) (by decide) (ob + (i + 1))
      e132) fun k6 σ6 ⟨hk6, hm6, hf6⟩ => ?_)
    refine r_seq (r_mono (h_mov σ6 113 121 (by decide)) fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ => ?_)
    refine r_mono (h_const σ7 114 0) fun k8 σ8 ⟨hk8, hm8, hf8, hv8⟩ => ⟨?_, ?_, ?_, ?_⟩
    · omega
    · refine Fr.tr hfr1 (Fr.tr (hf3.mono (by unfold SD; decide)) (Fr.tr (hf4.mono
        (by unfold SD; decide)) (Fr.tr (hf5.mono (by unfold SD; decide)) (Fr.tr
        (hf6.mono (by unfold SD; decide)) (Fr.tr (hf7.mono (by unfold SD; decide))
        (hf8.mono (by unfold SD; decide)))))))
    · intro st' hst
      unfold mstep at hst
      simp only at hst
      rw [hnc] at hst
      simp only [hwn, dif_pos, Option.some.injEq] at hst
      subst hst
      have e121 : σ5.regs 121 = (w : ℝ) := by
        rw [hf5 121 (by decide), hf4 121 (by decide), hf3 121 (by decide), hR]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hf8 115 (by decide), hf7 115 (by decide), hf6 115 (by decide), hf5 115 (by decide),
          e115]
      · rw [hf8 113 (by decide), hv7, hf6 121 (by decide), e121]
      · rw [hv8]; simp
      · rw [hf8 116 (by decide), hf7 116 (by decide), hf6 116 (by decide), hf5 116 (by decide),
          hf4 116 (by decide), hf3 116 (by decide), g 116 (by decide)]
      · rw [hm8, hm7, hm6, e121, hm5, hm4, hm3, hm1]
    · intro hst
      unfold mstep at hst
      simp only at hst
      rw [hnc] at hst
      simp [hwn] at hst

def dfsCost (n fb ob : ℕ) : ℕ :=
  4 * ob + 14 + 2 * n * (n * (4 * fb + 16 * n + 61) + 20 * n + 4 * ob + 48)

/-- The search program writes `dfsS T S v` at `ob`, its length in register `135`. -/
theorem h_dfs (v : Fin n) (σ0 : Cfg) (fb ob : ℕ)
    (h1 : σ0.regs 1 = n) (h2 : σ0.regs 2 = T.root.val) (h110 : σ0.regs 110 = fb)
    (h111 : σ0.regs 111 = ob) (h112 : σ0.regs 112 = v.val)
    (hflag : ∀ w : Fin n, σ0.mem ((fb + w.val : ℕ) : ℤ) = if w ∈ S then 1 else 0)
    (hpar : ∀ w : Fin n, σ0.mem ((2 + 3 * w.val : ℕ) : ℤ) = (T.parent w).val)
    (hob1 : fb + n ≤ ob) (hob2 : 3 * n + 3 ≤ ob) :
    Runs dfsProg σ0 (fun k σ' => k ≤ dfsCost n fb ob ∧ Fr SD σ0 σ' ∧
      σ'.regs 135 = (dfsS T S v).length ∧
      (∀ j < (dfsS T S v).length,
        σ'.mem ((ob + j : ℕ) : ℤ) = (T.vertexAt (dfsS T S v) j).val) ∧
      (∀ z : ℤ, ¬ ((ob : ℤ) ≤ z ∧ z < ob + (dfsS T S v).length) → σ'.mem z = σ0.mem z)) := by
  obtain ⟨hL1, hL0, hLs, hLn⟩ := dfs_iter T S v
  have hLb := dfsS_length T S v
  set D := dfsS T S v with hD
  set Ld := D.length with hLd
  set f := fstep T S v with hf
  have hread : ∀ M : ℤ → ℝ, (∀ z : ℤ, z < ob → M z = σ0.mem z) →
      (∀ w : Fin n, M ((fb + w.val : ℕ) : ℤ) = if w ∈ S then 1 else 0) ∧
      (∀ w : Fin n, M ((2 + 3 * w.val : ℕ) : ℤ) = (T.parent w).val) := by
    intro M hM
    refine ⟨fun w => ?_, fun w => ?_⟩
    · rw [hM _ (by have := w.isLt; push_cast; omega)]; exact hflag w
    · rw [hM _ (by have := w.isLt; push_cast; omega)]; exact hpar w
  let I : ℕ → Cfg → Prop := fun m σ =>
    Fr SD σ0 σ ∧
    (∀ z : ℤ, ¬ ((ob : ℤ) ≤ z ∧ z ≤ ob + (min m (Ld - 1) : ℕ)) → σ.mem z = σ0.mem z) ∧
    (∀ j ≤ min m (Ld - 1), σ.mem ((ob + j : ℕ) : ℤ) = (T.vertexAt D j).val) ∧
    σ.regs 115 = ((min m (Ld - 1) : ℕ) : ℝ) ∧
    σ.regs 116 = (if m < Ld then 1 else 0) ∧
    (m < Ld → σ.regs 113 = ((f^[m] (v, 0)).1.val : ℝ) ∧
      σ.regs 114 = (((f^[m] (v, 0)).2 : ℕ) : ℝ))
  set cIt := n * (4 * fb + 16 * n + 61) + 12 * n + 4 * ob + 4 * (2 * n) + 46 with hcIt
  refine r_seq (r_mono (h_mov σ0 113 112 (by decide)) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_const σ1 114 0) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_const σ2 115 0) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  refine r_seq (r_mono (h_stA σ3 111 112 (by decide) (by decide) (by decide) ob (by
    rw [hf3 111 (by decide), hf2 111 (by decide), hf1 111 (by decide), h111]))
    fun k4 σ4 ⟨hk4, hm4, hf4⟩ => ?_)
  refine r_seq (r_mono (h_const σ4 116 1) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
  have hf05 : Fr SD σ0 σ5 := Fr.tr (hf1.mono (by unfold SD; decide)) (Fr.tr
    (hf2.mono (by unfold SD; decide)) (Fr.tr (hf3.mono (by unfold SD; decide))
    (Fr.tr (hf4.mono (by unfold SD; decide)) (hf5.mono (by unfold SD; decide)))))
  refine r_seq (r_while 116 dfsBody Ld cIt I _ ?_ ?_ σ5 ?_ ?_)
  · -- one iteration
    intro m hm σ ⟨hfσ, hmσ, hentσ, h115σ, h116σ, hstσ⟩
    obtain ⟨h113σ, h114σ⟩ := hstσ hm
    have hmin : min m (Ld - 1) = m := by omega
    rw [hmin] at h115σ hentσ hmσ
    refine ⟨by rw [h116σ, if_pos hm]; norm_num, ?_⟩
    obtain ⟨hrf, hrp⟩ := hread σ.mem (fun z hz => hmσ z (by omega))
    refine r_mono (h_dfsBody T S σ fb ob v (f^[m] (v, 0)).1 (f^[m] (v, 0)).2 m
      (by rw [hfσ 1 (by decide), h1]) (by rw [hfσ 2 (by decide), h2])
      (by rw [hfσ 110 (by decide), h110]) (by rw [hfσ 111 (by decide), h111])
      (by rw [hfσ 112 (by decide), h112]) h113σ h114σ h115σ hrf hrp)
      fun k σ' ⟨hk, hf', hsome, hnone⟩ => ⟨?_, Fr.tr hfσ hf', ?_⟩
    · have : 4 * m ≤ 4 * (2 * n) := by omega
      omega
    rcases hms : mstep T S v (f^[m] (v, 0)) with _ | st'
    · -- the last step
      have hmL : m = Ld - 1 := by
        by_contra hne
        have := (hLs m (by omega)).1
        rw [hms] at this; cases this
      obtain ⟨e115, e116, em⟩ := hnone hms
      have hmin' : min (m + 1) (Ld - 1) = m := by omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hmin', em]; exact hmσ
      · rw [hmin', em]; exact hentσ
      · rw [hmin', e115]
      · rw [e116, if_neg (by omega)]
      · intro h; omega
    · -- a regular step
      have hmL : m + 1 < Ld := by
        by_contra hne
        have hm' : m = Ld - 1 := by omega
        rw [hm'] at hms; rw [hLn] at hms; cases hms
      obtain ⟨hs1, hs2⟩ := hLs m hmL
      rw [hms] at hs1
      obtain rfl : st' = f^[m + 1] (v, 0) := Option.some.inj hs1
      obtain ⟨e115, e113, e114, e116, em⟩ := hsome _ hms
      have hmin' : min (m + 1) (Ld - 1) = m + 1 := by omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hmin', em]
        intro z hz
        rw [update_of_ne (by push_cast; omega)]
        exact hmσ z (by omega)
      · rw [hmin', em]
        intro j hj
        by_cases hjm : j = m + 1
        · subst hjm; rw [update_self, hs2]
        · rw [update_of_ne (by push_cast; omega)]; exact hentσ j (by omega)
      · rw [hmin', e115]
      · rw [e116, h116σ, if_pos hm, if_pos hmL]
      · intro _
        exact ⟨e113, e114⟩
  · intro σ ⟨_, _, _, _, h116, _⟩
    rw [h116, if_neg (lt_irrefl _)]
  · -- the initial state
    have hmin0 : min 0 (Ld - 1) = 0 := by omega
    refine ⟨hf05, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmin0]
      intro z hz
      rw [hm5, hm4, update_of_ne (by omega), hm3, hm2, hm1]
    · rw [hmin0]
      intro j hj
      obtain rfl : j = 0 := by omega
      rw [hm5, hm4]
      simp only [Nat.add_zero]
      rw [update_self, hf3 112 (by decide), hf2 112 (by decide), hf1 112 (by decide), h112, hL0]
    · rw [hmin0, hf5 115 (by decide), hf4 115 (by decide), hv3]; simp
    · rw [hv5, if_pos (by omega)]; simp
    · intro _
      refine ⟨?_, ?_⟩
      · rw [hf5 113 (by decide), hf4 113 (by decide), hf3 113 (by decide), hf2 113 (by decide),
          hv1, h112]
        rfl
      · rw [hf5 114 (by decide), hf4 114 (by decide), hf3 114 (by decide), hv2]
        simp
  · -- after the loop
    intro k6 σ6 hk6 ⟨hf6, hm6, hent6, h1156, _, _⟩
    refine r_seq (r_mono (h_const σ6 131 1) fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ =>
      r_mono (h_add σ7 135 115 131) fun k8 σ8 ⟨hk8, hm8, hf8, hv8⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · unfold dfsCost
      have hmul : Ld * (cIt + 2) ≤ 2 * n * (cIt + 2) := Nat.mul_le_mul_right _ (by omega)
      have hc : cIt + 2 = n * (4 * fb + 16 * n + 61) + 20 * n + 4 * ob + 48 := by
        rw [hcIt]; ring
      have hc2 : 2 * n * (cIt + 2) =
          2 * n * (n * (4 * fb + 16 * n + 61) + 20 * n + 4 * ob + 48) := by rw [hc]
      omega
    · exact Fr.tr hf6 (Fr.trm hf7 hf8 (by unfold SD; decide) (by unfold SD; decide))
    · rw [hv8, hf7 115 (by decide), h1156, hv7]
      have : min Ld (Ld - 1) = Ld - 1 := by omega
      rw [this]; push_cast [Nat.cast_sub hL1]; ring
    · intro j hj
      rw [hm8, hm7]
      exact hent6 j (by omega)
    · intro z hz
      rw [hm8, hm7]
      exact hm6 z (by omega)

end OnlineTransportation1195.Dev.T13.PartPR
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.T13.PartPR
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
  OnlineTransportation1195.Dev.T13 OnlineTransportation1195.Dev.RL.Lib Function
/-!
Part PR, file 4: memory layout, and the phase computing `x` from the stored list `L`.
Region `r` starts at `rb n r = (3 + 2 r)(n + 1)` (its base is kept in register `200 + r`):
`0` flags of `S`, `1` deadlines `d`, `2` the list `L`, `3` the values `x`, `4` red flags,
`5` patch flags, `6` scratch list of a detour.
-/
/-- Base of region `r`. -/
def rb (n r : ℕ) : ℕ := (3 + 2 * r) * (n + 1)

/-- `d := M[regs b + regs i]`. -/
def ldAt (d b i : ℕ) : Stmt := .seq (.add 109 b i) (ld d 109)

theorem h_ldAt (σ : Cfg) (d b i : ℕ) (B I : ℕ) (hb : σ.regs b = B) (hi : σ.regs i = I) :
    Runs (ldAt d b i) σ (fun k σ' => k ≤ 4 * (B + I) + 7 ∧ σ'.mem = σ.mem ∧
      Fr [100, 101, 109, d] σ σ' ∧ σ'.regs d = σ.mem ((B + I : ℕ) : ℤ)) := by
  refine r_seq (r_mono (h_add σ 109 b i) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  have e : σ1.regs 109 = ((B + I : ℕ) : ℝ) := by rw [hv1, hb, hi]; push_cast; ring
  refine r_mono (h_ld σ1 d 109 (by decide) _ e) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
    ⟨by omega, by rw [hm2, hm1], Fr.trm hf1 hf2 (by simp) (by simp), by rw [hv2, hm1]⟩

end OnlineTransportation1195.Dev.T13.PartPR
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.T13.PartPR
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
  OnlineTransportation1195.Dev.T13 OnlineTransportation1195.Dev.RL.Lib Function
variable {n : ℕ} (T : Tree n)
/-- `150 := [DownAt L v i]` (`v` in `140`, `i` in `145`, `L` at base `202`, length `212`). -/
def downBody : Stmt :=
  .seq (eqT 159 140 2) (.seq (notF 159 159) (.seq (.const 160 1) (.seq (.add 161 145 160)
  (.seq (ltF 162 161 212) (.seq (ldAt 164 202 145) (.seq (ldIn 165 2 140) (.seq (eqT 166 164 165)
  (.seq (ldAt 167 202 161) (.seq (eqT 168 167 140) (.seq (.mul 150 159 162)
  (.seq (.mul 150 150 166) (.mul 150 150 168))))))))))))

def SDB : List ℕ := [100, 101, 102, 109, 150, 159, 160, 161, 162, 164, 165, 166, 167, 168]

/-- The stored list. -/
def LOK (M : ℤ → ℝ) (b : ℕ) (L : List (Fin n)) : Prop :=
  ∀ j < L.length, M ((b + j : ℕ) : ℤ) = (T.vertexAt L j).val

def ParOK (M : ℤ → ℝ) : Prop :=
  ∀ w : Fin n, M ((2 + 3 * w.val : ℕ) : ℤ) = (T.parent w).val ∧
    M ((3 + 3 * w.val : ℕ) : ℤ) = T.W w

theorem h_downBody (σ : Cfg) (L : List (Fin n)) (b : ℕ) (v : Fin n) (i : ℕ)
    (h2 : σ.regs 2 = T.root.val) (h140 : σ.regs 140 = v.val) (h145 : σ.regs 145 = i)
    (h202 : σ.regs 202 = b) (h212 : σ.regs 212 = L.length) (hL : LOK T σ.mem b L)
    (hP : ParOK T σ.mem) :
    Runs downBody σ (fun k σ' => k ≤ 8 * b + 8 * i + 12 * n + 70 ∧ σ'.mem = σ.mem ∧
      Fr SDB σ σ' ∧ σ'.regs 150 = if T.DownAt L v i then 1 else 0) := by
  refine r_seq (r_mono (h_eqT σ 159 140 2 (by decide) (by decide) (by decide))
    fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_notF σ1 159 159 (by decide)) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_const σ2 160 1) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  refine r_seq (r_mono (h_add σ3 161 145 160) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
  refine r_seq (r_mono (h_ltF σ4 162 161 212) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
  have e145 : σ5.regs 145 = i := by
    rw [hf5 145 (by decide), hf4 145 (by decide), hf3 145 (by decide), hf2 145 (by decide),
      hf1 145 (by decide), h145]
  have e202 : σ5.regs 202 = b := by
    rw [hf5 202 (by decide), hf4 202 (by decide), hf3 202 (by decide), hf2 202 (by decide),
      hf1 202 (by decide), h202]
  have e161 : σ4.regs 161 = ((i + 1 : ℕ) : ℝ) := by
    rw [hv4, hv3, hf3 145 (by decide), hf2 145 (by decide), hf1 145 (by decide), h145]
    push_cast; ring
  refine r_seq (r_mono (h_ldAt σ5 164 202 145 b i e202 e145) fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)
  have e140 : σ6.regs 140 = (v.val : ℕ) := by
    rw [hf6 140 (by decide), hf5 140 (by decide), hf4 140 (by decide), hf3 140 (by decide),
      hf2 140 (by decide), hf1 140 (by decide), h140]
  refine r_seq (r_mono (h_ldIn σ6 165 2 140 (by decide) v.val e140)
    fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ => ?_)
  refine r_seq (r_mono (h_eqT σ7 166 164 165 (by decide) (by decide) (by decide))
    fun k8 σ8 ⟨hk8, hm8, hf8, hv8⟩ => ?_)
  have e161' : σ8.regs 161 = ((i + 1 : ℕ) : ℝ) := by
    rw [hf8 161 (by decide), hf7 161 (by decide), hf6 161 (by decide), hf5 161 (by decide),
      e161]
  have e202' : σ8.regs 202 = b := by
    rw [hf8 202 (by decide), hf7 202 (by decide), hf6 202 (by decide), e202]
  refine r_seq (r_mono (h_ldAt σ8 167 202 161 b (i + 1) e202' e161')
    fun k9 σ9 ⟨hk9, hm9, hf9, hv9⟩ => ?_)
  refine r_seq (r_mono (h_eqT σ9 168 167 140 (by decide) (by decide) (by decide))
    fun k10 σ10 ⟨hk10, hm10, hf10, hv10⟩ => ?_)
  refine r_seq (r_mono (h_mul σ10 150 159 162) fun k11 σ11 ⟨hk11, hm11, hf11, hv11⟩ => ?_)
  refine r_seq (r_mono (h_mul σ11 150 150 166) fun k12 σ12 ⟨hk12, hm12, hf12, hv12⟩ => ?_)
  refine r_mono (h_mul σ12 150 150 168) fun k13 σ13 ⟨hk13, hm13, hf13, hv13⟩ =>
    ⟨?_, ?_, ?_, ?_⟩
  · have := v.isLt
    omega
  · rw [hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]
  · intro r hr
    simp only [SDB, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hf13 r (by simp [hr]), hf12 r (by simp [hr]), hf11 r (by simp [hr]),
      hf10 r (by simp [hr]), hf9 r (by simp [hr]), hf8 r (by simp [hr]), hf7 r (by simp [hr]),
      hf6 r (by simp [hr]), hf5 r (by simp [hr]), hf4 r (by simp [hr]), hf3 r (by simp [hr]),
      hf2 r (by simp [hr]), hf1 r (by simp [hr])]
  · have hM : σ9.mem = σ.mem := by rw [hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]
    have a159 : σ10.regs 159 = if v = T.root then 0 else 1 := by
      rw [hf10 159 (by decide), hf9 159 (by decide), hf8 159 (by decide), hf7 159 (by decide),
        hf6 159 (by decide), hf5 159 (by decide), hf4 159 (by decide), hf3 159 (by decide), hv2,
        hv1, h140, h2]
      simp only [cval_eq]; split_ifs <;> norm_num
    have a162 : σ10.regs 162 = if i + 1 < L.length then 1 else 0 := by
      rw [hf10 162 (by decide), hf9 162 (by decide), hf8 162 (by decide), hf7 162 (by decide),
        hf6 162 (by decide), hv5, e161, hf4 212 (by decide), hf3 212 (by decide),
        hf2 212 (by decide), hf1 212 (by decide), h212]
      simp only [Nat.cast_lt]
    have hpv : σ.mem ((2 + 3 * v.val : ℕ) : ℤ) = (T.parent v).val := (hP v).1
    by_cases hi : i + 1 < L.length
    · have a166 : σ10.regs 166 = if T.vertexAt L i = T.parent v then 1 else 0 := by
        have hM5 : σ5.mem = σ.mem := by rw [hm5, hm4, hm3, hm2, hm1]
        have hM6 : σ6.mem = σ.mem := by rw [hm6, hM5]
        rw [hf10 166 (by decide), hf9 166 (by decide), hv8, hf7 164 (by decide), hv6, hv7,
          hM5, hM6, hL i (by omega), hpv]
        simp only [cval_eq]
      have a168 : σ10.regs 168 = if T.vertexAt L (i + 1) = v then 1 else 0 := by
        rw [hv10, hv9, hf9 140 (by decide), hf8 140 (by decide), hf7 140 (by decide), e140,
          hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1, hL (i + 1) hi]
        simp only [cval_eq]
      rw [hv13, hf12 168 (by decide), hf11 168 (by decide), hv12, hf11 166 (by decide), hv11,
        a159, a162, a166, a168]
      unfold Tree.DownAt
      by_cases c1 : v = T.root <;> by_cases c2 : T.vertexAt L i = T.parent v <;>
        by_cases c3 : T.vertexAt L (i + 1) = v <;> simp [c1, c2, c3, hi]
    · have h168 : σ12.regs 168 = 0 ∨ σ12.regs 168 = 1 := by
        rw [hf12 168 (by decide), hf11 168 (by decide), hv10]; split_ifs <;> simp
      have h166 : σ11.regs 166 = 0 ∨ σ11.regs 166 = 1 := by
        rw [hf11 166 (by decide), hf10 166 (by decide), hf9 166 (by decide), hv8]
        split_ifs <;> simp
      rw [hv13, hv12, hv11, a159, a162, if_neg hi]
      have : ¬ T.DownAt L v i := fun h => hi h.2.1
      rw [if_neg this]
      simp

/-- `158 := downStep (L j) (L (j+1))` (`j` in `153`). -/
def dsBody : Stmt :=
  .seq (ldAt 164 202 153) (.seq (.const 160 1) (.seq (.add 161 153 160) (.seq (ldAt 167 202 161)
  (.seq (eqT 159 167 2) (.seq (notF 159 159) (.seq (ldIn 165 2 167) (.seq (eqT 166 165 164)
  (.seq (ldIn 169 3 167) (.seq (.mul 158 159 166) (.mul 158 158 169))))))))))

def SDS : List ℕ := [100, 101, 102, 109, 158, 159, 160, 161, 164, 165, 166, 167, 169]

theorem h_dsBody (σ : Cfg) (L : List (Fin n)) (b : ℕ) (j : ℕ) (hj : j + 1 < L.length)
    (h2 : σ.regs 2 = T.root.val) (h153 : σ.regs 153 = j)
    (h202 : σ.regs 202 = b) (hL : LOK T σ.mem b L) (hP : ParOK T σ.mem) :
    Runs dsBody σ (fun k σ' => k ≤ 8 * b + 8 * j + 24 * n + 80 ∧ σ'.mem = σ.mem ∧
      Fr SDS σ σ' ∧
      σ'.regs 158 = T.downStep (T.vertexAt L j) (T.vertexAt L (j + 1))) := by
  refine r_seq (r_mono (h_ldAt σ 164 202 153 b j h202 h153) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_const σ1 160 1) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_add σ2 161 153 160) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  have e161 : σ3.regs 161 = ((j + 1 : ℕ) : ℝ) := by
    rw [hv3, hv2, hf2 153 (by decide), hf1 153 (by decide), h153]; push_cast; ring
  have e202 : σ3.regs 202 = b := by
    rw [hf3 202 (by decide), hf2 202 (by decide), hf1 202 (by decide), h202]
  refine r_seq (r_mono (h_ldAt σ3 167 202 161 b (j + 1) e202 e161)
    fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
  set w := T.vertexAt L (j + 1) with hw
  set u := T.vertexAt L j with hu
  have hM3 : σ3.mem = σ.mem := by rw [hm3, hm2, hm1]
  have e167 : σ4.regs 167 = (w.val : ℕ) := by rw [hv4, hM3, hL (j + 1) hj]
  refine r_seq (r_mono (h_eqT σ4 159 167 2 (by decide) (by decide) (by decide))
    fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
  refine r_seq (r_mono (h_notF σ5 159 159 (by decide)) fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)
  have e167' : σ6.regs 167 = (w.val : ℕ) := by
    rw [hf6 167 (by decide), hf5 167 (by decide), e167]
  refine r_seq (r_mono (h_ldIn σ6 165 2 167 (by decide) w.val e167')
    fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ => ?_)
  refine r_seq (r_mono (h_eqT σ7 166 165 164 (by decide) (by decide) (by decide))
    fun k8 σ8 ⟨hk8, hm8, hf8, hv8⟩ => ?_)
  have e167'' : σ8.regs 167 = (w.val : ℕ) := by
    rw [hf8 167 (by decide), hf7 167 (by decide), e167']
  refine r_seq (r_mono (h_ldIn σ8 169 3 167 (by decide) w.val e167'')
    fun k9 σ9 ⟨hk9, hm9, hf9, hv9⟩ => ?_)
  refine r_seq (r_mono (h_mul σ9 158 159 166) fun k10 σ10 ⟨hk10, hm10, hf10, hv10⟩ => ?_)
  refine r_mono (h_mul σ10 158 158 169) fun k11 σ11 ⟨hk11, hm11, hf11, hv11⟩ =>
    ⟨?_, ?_, ?_, ?_⟩
  · have := w.isLt
    omega
  · rw [hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]
  · intro r hr
    simp only [SDS, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hf11 r (by simp [hr]), hf10 r (by simp [hr]), hf9 r (by simp [hr]),
      hf8 r (by simp [hr]), hf7 r (by simp [hr]), hf6 r (by simp [hr]), hf5 r (by simp [hr]),
      hf4 r (by simp [hr]), hf3 r (by simp [hr]), hf2 r (by simp [hr]), hf1 r (by simp [hr])]
  · have hM8 : σ8.mem = σ.mem := by rw [hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]
    have a159 : σ9.regs 159 = if w = T.root then 0 else 1 := by
      rw [hf9 159 (by decide), hf8 159 (by decide), hf7 159 (by decide), hv6, hv5, e167,
        hf4 2 (by decide), hf3 2 (by decide), hf2 2 (by decide), hf1 2 (by decide), h2]
      simp only [cval_eq]; split_ifs <;> norm_num
    have a166 : σ9.regs 166 = if T.parent w = u then 1 else 0 := by
      rw [hf9 166 (by decide), hv8, hv7, hf7 164 (by decide), hf6 164 (by decide),
        hf5 164 (by decide), hf4 164 (by decide), hf3 164 (by decide), hf2 164 (by decide), hv1,
        hm6, hm5, hm4, hM3, (hP w).1, hL j (by omega)]
      simp only [cval_eq]
      rw [← hu]
    have a169 : σ10.regs 169 = T.W w := by
      rw [hf10 169 (by decide), hv9, hM8, (hP w).2]
    rw [hv11, hv10, a159, a166, a169]
    unfold Tree.downStep
    by_cases c1 : w = T.root <;> by_cases c2 : T.parent w = u <;> simp [c1, c2]

/-- `144 := x v` (`v` in `140`). -/
def xBody : Stmt :=
  .seq (findLoop 145 212 146 147 148 149 150 151 152 downBody)
    (.ifle 148 (.const 144 0) (.seq (.const 154 1) (.seq (.add 155 149 154)
      (sumLoop 153 155 156 157 144 158 dsBody))))

def SXF : List ℕ := [100, 101, 102, 109, 145, 146, 147, 148, 149, 150, 151, 152, 159, 160, 161,
  162, 164, 165, 166, 167, 168]

def SXS : List ℕ := [100, 101, 102, 109, 144, 153, 156, 157, 158, 159, 160, 161, 164, 165, 166,
  167, 169]

def SXB : List ℕ := [100, 101, 102, 109, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154,
  155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]

def xbCost (n b len : ℕ) : ℕ :=
  len * (8 * b + 8 * len + 12 * n + 85) + 5 + 4 + len * (8 * b + 8 * len + 24 * n + 86) + 4

theorem h_xBody (σ : Cfg) (L : List (Fin n)) (b : ℕ) (v : Fin n)
    (h2 : σ.regs 2 = T.root.val) (h140 : σ.regs 140 = v.val)
    (h202 : σ.regs 202 = b) (h212 : σ.regs 212 = L.length) (hL : LOK T σ.mem b L)
    (hP : ParOK T σ.mem) :
    Runs xBody σ (fun k σ' => k ≤ xbCost n b L.length ∧ σ'.mem = σ.mem ∧
      Fr SXB σ σ' ∧ σ'.regs 144 = T.x L v) := by
  refine r_seq (r_mono (h_findLoop 145 212 146 147 148 149 150 151 152 downBody SDB SXF
    (by unfold FindOK SDB SXF; decide) L.length (8 * b + 8 * L.length + 12 * n + 70)
    (T.DownAt L v) σ h212 ?_) fun k1 σ1 ⟨hk1, hm1, hf1, hF1, hR1⟩ => ?_)
  · intro m hm σ' hm' hf' hV'
    refine r_mono (h_downBody T σ' L b v m (by rw [hf' 2 (by decide), h2])
      (by rw [hf' 140 (by decide), h140]) hV' (by rw [hf' 202 (by decide), h202])
      (by rw [hf' 212 (by decide), h212]) (by rw [hm']; exact hL) (by rw [hm']; exact hP))
      fun k σ'' ⟨hk, h1, h2, h3⟩ => ⟨by omega, h1, h2, h3⟩
  have hx : T.x L v = match ffind (T.DownAt L v) L.length with
      | some i => T.downPrefix L i
      | none => 0 := rfl
  rcases hfd : ffind (T.DownAt L v) L.length with _ | i
  · have hF : σ1.regs 148 = 0 := by rw [hF1, hfd]; simp
    refine r_ifle (fun _ => ?_) (fun h => absurd (le_of_eq hF) h)
    refine r_mono (h_const σ1 144 0) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ⟨?_, ?_, ?_, ?_⟩
    · unfold xbCost
      have : L.length * (8 * b + 8 * L.length + 12 * n + 70 + 15) =
          L.length * (8 * b + 8 * L.length + 12 * n + 85) := by ring
      omega
    · rw [hm2, hm1]
    · exact Fr.trm hf1 hf2 (by unfold SXF SXB; decide) (by unfold SXB; decide)
    · rw [hv2, hx, hfd]; simp
  · obtain ⟨hi, hdi, -⟩ := (ffind_some _ _ _).mp hfd
    have hF : σ1.regs 148 = 1 := by rw [hF1, hfd]; simp
    have hR : σ1.regs 149 = (i : ℝ) := by rw [hR1, hfd]; simp
    refine r_ifle (fun h => absurd h (by rw [hF]; norm_num)) (fun _ => ?_)
    refine r_seq (r_mono (h_const σ1 154 1) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
    refine r_seq (r_mono (h_add σ2 155 149 154) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
    have e155 : σ3.regs 155 = ((i + 1 : ℕ) : ℝ) := by
      rw [hv3, hv2, hf2 149 (by decide), hR]; push_cast; ring
    have hM3 : σ3.mem = σ.mem := by rw [hm3, hm2, hm1]
    have g : ∀ r, r ∉ SXF → r ∉ [154] → r ∉ [155] → σ3.regs r = σ.regs r := by
      intro r h1 h2 h3; rw [hf3 r h3, hf2 r h2, hf1 r h1]
    refine r_mono (h_sumLoop 153 155 156 157 144 158 dsBody SDS SXS
      (by unfold LoopOK SDS SXS; decide) (i + 1) (8 * b + 8 * L.length + 24 * n + 80)
      (fun j => T.downStep (T.vertexAt L j) (T.vertexAt L (j + 1))) σ3 e155 ?_)
      fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ⟨?_, ?_, ?_, ?_⟩
    · intro m hm σ' hm' hf' hV'
      have hj : m + 1 < L.length := by have := hdi.2.1; omega
      refine r_mono (h_dsBody T σ' L b m hj
        (by rw [hf' 2 (by decide), g 2 (by decide) (by decide) (by decide), h2]) hV'
        (by rw [hf' 202 (by decide), g 202 (by decide) (by decide) (by decide), h202])
        (by rw [hm', hM3]; exact hL) (by rw [hm', hM3]; exact hP))
        fun k σ'' ⟨hk, h1, h2, h3⟩ => ⟨by omega, h1, h2, h3⟩
    · unfold xbCost
      have h1 : L.length * (8 * b + 8 * L.length + 12 * n + 70 + 15) =
          L.length * (8 * b + 8 * L.length + 12 * n + 85) := by ring
      have h2 : (i + 1) * (8 * b + 8 * L.length + 24 * n + 80 + 6) ≤
          L.length * (8 * b + 8 * L.length + 24 * n + 86) :=
        Nat.mul_le_mul (by have := hdi.2.1; omega) (by omega)
      omega
    · rw [hm4, hM3]
    · exact Fr.tr (Fr.trm hf1 (Fr.trm (S := [154, 155]) hf2 hf3 (by simp) (by simp)) (by unfold SXF SXB; decide)
        (by unfold SXB; decide)) (hf4.mono (by unfold SXS SXB; decide))
    · rw [hv4, hx, hfd]
      rfl

def SXP : List ℕ := [100, 101, 102, 109, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150,
  151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]

/-- Fill region `3` with `x`. -/
def xPhase : Stmt := fillLoop 140 1 141 142 203 143 144 xBody

theorem h_xPhase (σ : Cfg) (L : List (Fin n)) (b bx : ℕ)
    (h1 : σ.regs 1 = n) (h2 : σ.regs 2 = T.root.val) (h202 : σ.regs 202 = b)
    (h203 : σ.regs 203 = bx) (h212 : σ.regs 212 = L.length) (hL : LOK T σ.mem b L)
    (hP : ParOK T σ.mem) (hLb : b + L.length ≤ bx) (hPb : 3 * n + 3 ≤ bx) :
    Runs xPhase σ (fun k σ' => k ≤ n * (xbCost n b L.length + 4 * (bx + n) + 13) + 3 ∧
      Fr SXP σ σ' ∧
      (∀ z : ℤ, ¬ ((bx : ℤ) ≤ z ∧ z < bx + n) → σ'.mem z = σ.mem z) ∧
      ∀ v : Fin n, σ'.mem ((bx + v.val : ℕ) : ℤ) = T.x L v) := by
  refine r_mono (h_fillLoop 140 1 141 142 203 143 144 xBody SXB SXP
    (by unfold FillOK SXB SXP; decide) n (xbCost n b L.length) bx
    (fun m => if h : m < n then T.x L ⟨m, h⟩ else 0) σ h1 h203 ?_)
    fun k σ' ⟨hk, hf, hm, hv⟩ => ⟨hk, hf, hm, fun v => by rw [hv v.val v.isLt]; simp⟩
  intro m hm σ' hm' hf' hV'
  have hL' : LOK T σ'.mem b L := by
    intro j hj
    rw [hm' _ (by push_cast; omega)]; exact hL j hj
  have hP' : ParOK T σ'.mem := by
    intro w
    have := w.isLt
    rw [hm' _ (by push_cast; omega), hm' _ (by push_cast; omega)]; exact hP w
  refine r_mono (h_xBody T σ' L b ⟨m, hm⟩ (by rw [hf' 2 (by decide), h2]) hV'
    (by rw [hf' 202 (by decide), h202]) (by rw [hf' 212 (by decide), h212]) hL' hP')
    fun k σ'' ⟨hk, h1, h2, h3⟩ => ⟨hk, h1, h2, by rw [h3]; simp [hm]⟩

/-!
Part PR, file 5: evaluating `RS`, `FS` at a time `τ`, and the time `t = pickT`.
Flags of `S` at base `200`, deadlines at `201`, `x` at `203`; `t` goes to register `213`.
-/
/-- A vertex-indexed array at base `b`. -/
def VOK (M : ℤ → ℝ) (b : ℕ) (g : Fin n → ℝ) : Prop := ∀ v : Fin n, M ((b + v.val : ℕ) : ℤ) = g v

noncomputable def ind (S : Finset (Fin n)) (v : Fin n) : ℝ := if v ∈ S then 1 else 0

theorem sum_fin_range (g : Fin n → ℝ) :
    ∑ m ∈ Finset.range n, (if h : m < n then g ⟨m, h⟩ else 0) = ∑ v, g v := by
  rw [← Fin.sum_univ_eq_sum_range (fun m => if h : m < n then g ⟨m, h⟩ else 0) n]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp

/-- Register facts used by the level phases. -/
structure Lay (σ : Cfg) : Prop where
  h1 : σ.regs 1 = n
  h2 : σ.regs 2 = T.root.val
  b0 : σ.regs 200 = rb n 0
  b1 : σ.regs 201 = rb n 1
  b2 : σ.regs 202 = rb n 2
  b3 : σ.regs 203 = rb n 3
  b4 : σ.regs 204 = rb n 4
  b5 : σ.regs 205 = rb n 5
  b6 : σ.regs 206 = rb n 6

def LayRegs : List ℕ := [1, 2, 200, 201, 202, 203, 204, 205, 206]

theorem Lay.fr {σ σ' : Cfg} {Sc : List ℕ} (h : Lay T σ) (hf : Fr Sc σ σ')
    (hS : ∀ r ∈ LayRegs, r ∉ Sc) : Lay T σ' := by
  unfold LayRegs at hS
  exact ⟨by rw [hf 1 (hS 1 (by simp)), h.h1], by rw [hf 2 (hS 2 (by simp)), h.h2],
    by rw [hf 200 (hS 200 (by simp)), h.b0], by rw [hf 201 (hS 201 (by simp)), h.b1],
    by rw [hf 202 (hS 202 (by simp)), h.b2], by rw [hf 203 (hS 203 (by simp)), h.b3],
    by rw [hf 204 (hS 204 (by simp)), h.b4], by rw [hf 205 (hS 205 (by simp)), h.b5],
    by rw [hf 206 (hS 206 (by simp)), h.b6]⟩

/-- `308 := [f ∈ S ∧ d f < x f + τ] W f` (`f` in `301`, `τ` in `300`). -/
def rsBody : Stmt :=
  .seq (ldAt 302 200 301) (.seq (ldAt 303 201 301) (.seq (ldAt 304 203 301)
  (.seq (.add 305 304 300) (.seq (ltF 306 303 305) (.seq (ldIn 307 3 301)
  (.seq (.mul 308 302 306) (.mul 308 308 307)))))))

def SRS : List ℕ := [100, 101, 102, 109, 302, 303, 304, 305, 306, 307, 308]

theorem h_rsBody (σ : Cfg) (hl : Lay T σ) (S : Finset (Fin n)) (d xv : Fin n → ℝ) (τ : ℝ)
    (f : Fin n) (h300 : σ.regs 300 = τ) (h301 : σ.regs 301 = f.val)
    (hS : VOK σ.mem (rb n 0) (ind S)) (hd : VOK σ.mem (rb n 1) d)
    (hx : VOK σ.mem (rb n 3) xv) (hP : ParOK T σ.mem) :
    Runs rsBody σ (fun k σ' => k ≤ 300 * (n + 1) ∧ σ'.mem = σ.mem ∧ Fr SRS σ σ' ∧
      σ'.regs 308 = if f ∈ S ∧ d f < xv f + τ then T.W f else 0) := by
  have hf := f.isLt
  refine r_seq (r_mono (h_ldAt σ 302 200 301 _ _ hl.b0 h301) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_ldAt σ1 303 201 301 (rb n 1) f.val (by rw [hf1 201 (by decide), hl.b1])
    (by rw [hf1 301 (by decide), h301])) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_ldAt σ2 304 203 301 (rb n 3) f.val
    (by rw [hf2 203 (by decide), hf1 203 (by decide), hl.b3])
    (by rw [hf2 301 (by decide), hf1 301 (by decide), h301])) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  refine r_seq (r_mono (h_add σ3 305 304 300) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
  refine r_seq (r_mono (h_ltF σ4 306 303 305) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
  refine r_seq (r_mono (h_ldIn σ5 307 3 301 (by decide) f.val (by
    rw [hf5 301 (by decide), hf4 301 (by decide), hf3 301 (by decide), hf2 301 (by decide),
      hf1 301 (by decide), h301])) fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)
  refine r_seq (r_mono (h_mul σ6 308 302 306) fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ => ?_)
  refine r_mono (h_mul σ7 308 308 307) fun k8 σ8 ⟨hk8, hm8, hf8, hv8⟩ => ⟨?_, ?_, ?_, ?_⟩
  · unfold rb at hk1 hk2 hk3; omega
  · rw [hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]
  · intro r hr
    simp only [SRS, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hf8 r (by simp [hr]), hf7 r (by simp [hr]), hf6 r (by simp [hr]), hf5 r (by simp [hr]),
      hf4 r (by simp [hr]), hf3 r (by simp [hr]), hf2 r (by simp [hr]), hf1 r (by simp [hr])]
  · have v302 : σ6.regs 302 = ind S f := by
      rw [hf6 302 (by decide), hf5 302 (by decide), hf4 302 (by decide),
        hf3 302 (by decide), hf2 302 (by decide), hv1, hS f]
    have hM2 : σ2.mem = σ.mem := by rw [hm2, hm1]
    have v306 : σ6.regs 306 = if d f < xv f + τ then 1 else 0 := by
      rw [hf6 306 (by decide), hv5, hv4, hf4 303 (by decide),
        hf3 303 (by decide), hv2, hv3, hf3 300 (by decide), hf2 300 (by decide),
        hf1 300 (by decide), h300, hM2, hm1, hd f, hx f]
    have v307 : σ7.regs 307 = T.W f := by
      rw [hf7 307 (by decide), hv6, hm5, hm4, hm3, hm2, hm1, (hP f).2]
    rw [hv8, hv7, v302, v306, v307]
    unfold ind
    by_cases c1 : f ∈ S <;> by_cases c2 : d f < xv f + τ <;> simp [c1, c2]

/-- `312 := [f ∈ S] W f min 1 (τ / d f)`. -/
def fsBody : Stmt :=
  .seq (ldAt 302 200 301) (.seq (ldAt 303 201 301) (.seq (tdv 309 300 303) (.seq (.const 310 1)
  (.seq (mnS 311 310 309) (.seq (ldIn 307 3 301) (.seq (.mul 312 307 311) (.mul 312 312 302)))))))

def SFS : List ℕ := [100, 101, 102, 103, 104, 109, 302, 303, 307, 309, 310, 311, 312]

theorem h_fsBody (σ : Cfg) (hl : Lay T σ) (S : Finset (Fin n)) (d : Fin n → ℝ) (τ : ℝ)
    (f : Fin n) (h300 : σ.regs 300 = τ) (h301 : σ.regs 301 = f.val)
    (hS : VOK σ.mem (rb n 0) (ind S)) (hd : VOK σ.mem (rb n 1) d) (hP : ParOK T σ.mem) :
    Runs fsBody σ (fun k σ' => k ≤ 300 * (n + 1) ∧ σ'.mem = σ.mem ∧ Fr SFS σ σ' ∧
      σ'.regs 312 = if f ∈ S then T.W f * min 1 (τ / d f) else 0) := by
  have hf := f.isLt
  refine r_seq (r_mono (h_ldAt σ 302 200 301 _ _ hl.b0 h301) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_ldAt σ1 303 201 301 (rb n 1) f.val (by rw [hf1 201 (by decide), hl.b1])
    (by rw [hf1 301 (by decide), h301])) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_tdv σ2 309 300 303 (by decide) (by decide))
    fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  refine r_seq (r_mono (h_const σ3 310 1) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
  refine r_seq (r_mono (h_mnS σ4 311 310 309 (by decide) (by decide) (by decide) (by decide))
    fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
  refine r_seq (r_mono (h_ldIn σ5 307 3 301 (by decide) f.val (by
    rw [hf5 301 (by decide), hf4 301 (by decide), hf3 301 (by decide), hf2 301 (by decide),
      hf1 301 (by decide), h301])) fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)
  refine r_seq (r_mono (h_mul σ6 312 307 311) fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ => ?_)
  refine r_mono (h_mul σ7 312 312 302) fun k8 σ8 ⟨hk8, hm8, hf8, hv8⟩ => ⟨?_, ?_, ?_, ?_⟩
  · unfold rb at hk1 hk2; omega
  · rw [hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]
  · intro r hr
    simp only [SFS, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hf8 r (by simp [hr]), hf7 r (by simp [hr]), hf6 r (by simp [hr]), hf5 r (by simp [hr]),
      hf4 r (by simp [hr]), hf3 r (by simp [hr]), hf2 r (by simp [hr]), hf1 r (by simp [hr])]
  · have v302 : σ7.regs 302 = ind S f := by
      rw [hf7 302 (by decide), hf6 302 (by decide), hf5 302 (by decide), hf4 302 (by decide),
        hf3 302 (by decide), hf2 302 (by decide), hv1, hS f]
    have v311 : σ6.regs 311 = min 1 (τ / d f) := by
      rw [hf6 311 (by decide), hv5, hf4 309 (by decide), hv4, hv3, hf2 300 (by decide),
        hf1 300 (by decide), h300, hv2, hm1, hd f]
      simp
    have v307 : σ6.regs 307 = T.W f := by
      rw [hv6, hm5, hm4, hm3, hm2, hm1, (hP f).2]
    rw [hv8, hv7, v302, v307, v311]
    unfold ind
    by_cases c1 : f ∈ S <;> simp [c1]

theorem cost_rf (n : ℕ) : n * (300 * (n + 1) + 6) + 4 + (n * (300 * (n + 1) + 6) + 4) ≤
    700 * (n + 1) ^ 2 := by nlinarith

theorem cost_cand (n : ℕ) : 4 * ((3 + 2 * 1) * (n + 1) + n) + 7 + (4 * ((3 + 2 * 3) * (n + 1) + n)
    + 7) + 1 + (4 * ((3 + 2 * 0) * (n + 1) + n) + 7) + 1 + 4 + 700 * (n + 1) ^ 2 + 4 + 1 + 1
    ≤ 900 * (n + 1) ^ 2 := by nlinarith

theorem cost_t1 (n : ℕ) : n * (900 * (n + 1) ^ 2 + 15) + 5 + 2 + (4 * ((3 + 2 * 1) * (n + 1) + n)
    + 7 + (4 * ((3 + 2 * 3) * (n + 1) + n) + 7 + 1)) ≤ 1000 * (n + 1) ^ 3 := by nlinarith

theorem cost_t2 (n : ℕ) : n * (900 * (n + 1) ^ 2 + 15) + 5 + 1 + (n * (100 * (n + 1) + 6) + 4 +
    (1 + 1)) ≤ 1000 * (n + 1) ^ 3 := by nlinarith

/-- `315 := RS τ`, `316 := FS τ` (`τ` in `300`). -/
def evalRF : Stmt :=
  .seq (sumLoop 301 1 313 314 315 308 rsBody) (sumLoop 301 1 313 314 316 312 fsBody)

def SRF : List ℕ := [100, 101, 102, 103, 104, 109, 301, 302, 303, 304, 305, 306, 307, 308, 309,
  310, 311, 312, 313, 314, 315, 316]

theorem h_evalRF (σ : Cfg) (hl : Lay T σ) (S : Finset (Fin n)) (d : Fin n → ℝ)
    (L : List (Fin n)) (τ : ℝ) (h300 : σ.regs 300 = τ)
    (hS : VOK σ.mem (rb n 0) (ind S)) (hd : VOK σ.mem (rb n 1) d)
    (hx : VOK σ.mem (rb n 3) (T.x L)) (hP : ParOK T σ.mem) :
    Runs evalRF σ (fun k σ' => k ≤ 700 * (n + 1) ^ 2 ∧ σ'.mem = σ.mem ∧ Fr SRF σ σ' ∧
      σ'.regs 315 = RS T S d L τ ∧ σ'.regs 316 = FS T S d τ) := by
  refine r_seq (r_mono (h_sumLoop 301 1 313 314 315 308 rsBody SRS
    (SRS ++ [301, 313, 314, 315]) (by unfold LoopOK SRS; decide) n (300 * (n + 1))
    (fun m => if h : m < n then (if (⟨m, h⟩ : Fin n) ∈ S ∧ d ⟨m, h⟩ < T.x L ⟨m, h⟩ + τ then
      T.W ⟨m, h⟩ else 0) else 0) σ hl.h1 ?_) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  · intro m hm σ' hm' hf' hV'
    have hl' := hl.fr T hf' (by unfold LayRegs SRS; decide)
    refine r_mono (h_rsBody T σ' hl' S d (T.x L) τ ⟨m, hm⟩
      (by rw [hf' 300 (by decide), h300]) hV' (by rw [hm']; exact hS) (by rw [hm']; exact hd)
      (by rw [hm']; exact hx) (by rw [hm']; exact hP)) fun k σ'' ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, h3, by rw [h4]; simp [hm]⟩
  have hl1 := hl.fr T hf1 (by unfold LayRegs SRS; decide)
  refine r_mono (h_sumLoop 301 1 313 314 316 312 fsBody SFS
    (SFS ++ [301, 313, 314, 316]) (by unfold LoopOK SFS; decide) n (300 * (n + 1))
    (fun m => if h : m < n then (if (⟨m, h⟩ : Fin n) ∈ S then
      T.W ⟨m, h⟩ * min 1 (τ / d ⟨m, h⟩) else 0) else 0) σ1 hl1.h1 ?_)
    fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ⟨?_, by rw [hm2, hm1], ?_, ?_, ?_⟩
  · intro m hm σ' hm' hf' hV'
    have hl' := hl1.fr T hf' (by unfold LayRegs SFS; decide)
    refine r_mono (h_fsBody T σ' hl' S d τ ⟨m, hm⟩
      (by rw [hf' 300 (by decide), hf1 300 (by decide), h300]) hV'
      (by rw [hm', hm1]; exact hS) (by rw [hm', hm1]; exact hd) (by rw [hm', hm1]; exact hP))
      fun k σ'' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, by rw [h4]; simp [hm]⟩
  · have hc := cost_rf n
    omega
  · exact Fr.trm hf1 hf2 (by unfold SRS SRF; decide) (by unfold SFS SRF; decide)
  · rw [hf2 315 (by unfold SFS; decide), hv1, sum_fin_range (fun f =>
      if f ∈ S ∧ d f < T.x L f + τ then T.W f else 0)]
    unfold RS redS
    rw [Finset.sum_filter, ← Finset.sum_ite_mem_eq S]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases c1 : f ∈ S <;> simp [c1]
  · rw [hv2, sum_fin_range (fun f => if f ∈ S then T.W f * min 1 (τ / d f) else 0)]
    unfold FS
    rw [← Finset.sum_ite_mem_eq S]

/-! ### The time `t` -/
/-- `327 := [e ∈ goodCands]` (`e` in `320`). -/
def candBody : Stmt :=
  .seq (ldAt 321 201 320) (.seq (ldAt 322 203 320) (.seq (.sub 300 321 322)
  (.seq (ldAt 323 200 320) (.seq (.const 324 0) (.seq (ltF 325 324 300) (.seq evalRF
  (.seq (ltF 326 315 316) (.seq (.mul 327 323 325) (.mul 327 327 326)))))))))

def SCB : List ℕ := [100, 101, 102, 103, 104, 109, 300, 301, 302, 303, 304, 305, 306, 307, 308,
  309, 310, 311, 312, 313, 314, 315, 316, 321, 322, 323, 324, 325, 326, 327]

theorem h_candBody (σ : Cfg) (hl : Lay T σ) (S : Finset (Fin n)) (d : Fin n → ℝ)
    (L : List (Fin n)) (e : Fin n) (h320 : σ.regs 320 = e.val)
    (hS : VOK σ.mem (rb n 0) (ind S)) (hd : VOK σ.mem (rb n 1) d)
    (hx : VOK σ.mem (rb n 3) (T.x L)) (hP : ParOK T σ.mem) :
    Runs candBody σ (fun k σ' => k ≤ 900 * (n + 1) ^ 2 ∧ σ'.mem = σ.mem ∧ Fr SCB σ σ' ∧
      σ'.regs 327 = if e ∈ goodCands T S d L then 1 else 0) := by
  have he := e.isLt
  refine r_seq (r_mono (h_ldAt σ 321 201 320 _ _ hl.b1 h320) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_ldAt σ1 322 203 320 (rb n 3) e.val (by rw [hf1 203 (by decide), hl.b3])
    (by rw [hf1 320 (by decide), h320])) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_sub σ2 300 321 322) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  have e300 : σ3.regs 300 = d e - T.x L e := by
    rw [hv3, hf2 321 (by decide), hv1, hv2, hm1, hd e, hx e]
  refine r_seq (r_mono (h_ldAt σ3 323 200 320 (rb n 0) e.val
    (by rw [hf3 200 (by decide), hf2 200 (by decide), hf1 200 (by decide), hl.b0])
    (by rw [hf3 320 (by decide), hf2 320 (by decide), hf1 320 (by decide), h320]))
    fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
  refine r_seq (r_mono (h_const σ4 324 0) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
  refine r_seq (r_mono (h_ltF σ5 325 324 300) fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)
  have hM6 : σ6.mem = σ.mem := by rw [hm6, hm5, hm4, hm3, hm2, hm1]
  have hf06 : Fr [100, 101, 102, 109, 321, 322, 300, 323, 324, 325] σ σ6 :=
    Fr.tr (hf1.mono (by decide)) (Fr.tr (hf2.mono (by decide)) (Fr.tr (hf3.mono (by decide))
      (Fr.tr (hf4.mono (by decide)) (Fr.tr (hf5.mono (by decide)) (hf6.mono (by decide))))))
  have hl6 := hl.fr T hf06 (by unfold LayRegs; decide)
  refine r_seq (r_mono (h_evalRF T σ6 hl6 S d L (d e - T.x L e)
    (by rw [hf6 300 (by decide), hf5 300 (by decide), hf4 300 (by decide), e300])
    (by rw [hM6]; exact hS) (by rw [hM6]; exact hd) (by rw [hM6]; exact hx)
    (by rw [hM6]; exact hP)) fun k7 σ7 ⟨hk7, hm7, hf7, hv7R, hv7F⟩ => ?_)
  refine r_seq (r_mono (h_ltF σ7 326 315 316) fun k8 σ8 ⟨hk8, hm8, hf8, hv8⟩ => ?_)
  refine r_seq (r_mono (h_mul σ8 327 323 325) fun k9 σ9 ⟨hk9, hm9, hf9, hv9⟩ => ?_)
  refine r_mono (h_mul σ9 327 327 326) fun k10 σ10 ⟨hk10, hm10, hf10, hv10⟩ =>
    ⟨?_, ?_, ?_, ?_⟩
  · have hc := cost_cand n
    unfold rb at hk1 hk2 hk4; omega
  · rw [hm10, hm9, hm8, hm7, hM6]
  · exact Fr.tr (hf06.mono (by unfold SCB; decide)) (Fr.tr (hf7.mono (by unfold SRF SCB; decide))
      (Fr.tr (hf8.mono (by unfold SCB; decide)) (Fr.tr (hf9.mono (by unfold SCB; decide))
        (hf10.mono (by unfold SCB; decide)))))
  · have v323 : σ8.regs 323 = ind S e := by
      rw [hf8 323 (by decide), hf7 323 (by decide), hf6 323 (by decide),
        hf5 323 (by decide), hv4, hm3, hm2, hm1, hS e]
    have v325 : σ8.regs 325 = if 0 < d e - T.x L e then 1 else 0 := by
      rw [hf8 325 (by decide), hf7 325 (by decide), hv6,
        hf5 300 (by decide), hf4 300 (by decide), e300, hv5]; simp
    have v326 : σ9.regs 326 = if RS T S d L (d e - T.x L e) < FS T S d (d e - T.x L e)
        then 1 else 0 := by
      rw [hf9 326 (by decide), hv8, hv7R, hv7F]
    rw [hv10, hv9, v323, v325, v326]
    unfold ind goodCands
    simp only [Finset.mem_filter]
    by_cases c1 : e ∈ S <;> by_cases c2 : 0 < d e - T.x L e <;>
      by_cases c3 : RS T S d L (d e - T.x L e) < FS T S d (d e - T.x L e) <;> simp [c1, c2, c3]

theorem ffind_min (A : Finset (Fin n)) :
    ffind (fun e => ∃ h : e < n, (⟨e, h⟩ : Fin n) ∈ A) n =
      if h : A.Nonempty then some (A.min' h).val else none := by
  split_ifs with hA
  · rw [ffind_some]
    refine ⟨(A.min' hA).isLt, ⟨(A.min' hA).isLt, by simpa using A.min'_mem hA⟩, ?_⟩
    rintro i hi ⟨hin, hiA⟩
    have := A.min'_le _ hiA
    rw [Fin.le_def] at this
    simp at this
    omega
  · cases h : ffind (fun e => ∃ h : e < n, (⟨e, h⟩ : Fin n) ∈ A) n with
    | none => rfl
    | some j =>
      obtain ⟨-, ⟨hj, hjA⟩, -⟩ := (ffind_some _ _ _).mp h
      exact absurd ⟨_, hjA⟩ hA

/-- `335 := [f ∈ S] d f`. -/
def sdBody : Stmt := .seq (ldAt 302 200 301) (.seq (ldAt 303 201 301) (.mul 335 302 303))

/-- `213 := pickT`. -/
def tPhase : Stmt :=
  .seq (findLoop 320 1 328 329 330 331 327 332 333 candBody)
    (.ifle 330 (.seq (sumLoop 301 1 313 314 334 335 sdBody) (.seq (.const 336 1)
      (.add 213 334 336)))
      (.seq (ldAt 321 201 331) (.seq (ldAt 322 203 331) (.sub 213 321 322))))

def SCF : List ℕ := SCB ++ [320, 328, 329, 330, 331, 332, 333]

def STP : List ℕ := SCF ++ [334, 335, 336, 213]

theorem h_tPhase (σ : Cfg) (hl : Lay T σ) (S : Finset (Fin n)) (d : Fin n → ℝ)
    (L : List (Fin n)) (hS : VOK σ.mem (rb n 0) (ind S)) (hd : VOK σ.mem (rb n 1) d)
    (hx : VOK σ.mem (rb n 3) (T.x L)) (hP : ParOK T σ.mem) :
    Runs tPhase σ (fun k σ' => k ≤ 1000 * (n + 1) ^ 3 ∧ σ'.mem = σ.mem ∧ Fr STP σ σ' ∧
      σ'.regs 213 = pickT T S d L) := by
  refine r_seq (r_mono (h_findLoop 320 1 328 329 330 331 327 332 333 candBody SCB SCF
    (by unfold FindOK SCB SCF; decide) n (900 * (n + 1) ^ 2)
    (fun e => ∃ h : e < n, (⟨e, h⟩ : Fin n) ∈ goodCands T S d L) σ hl.h1 ?_)
    fun k1 σ1 ⟨hk1, hm1, hf1, hF1, hR1⟩ => ?_)
  · intro m hm σ' hm' hf' hV'
    have hl' := hl.fr T hf' (by unfold LayRegs SCF SCB; decide)
    refine r_mono (h_candBody T σ' hl' S d L ⟨m, hm⟩ hV' (by rw [hm']; exact hS)
      (by rw [hm']; exact hd) (by rw [hm']; exact hx) (by rw [hm']; exact hP))
      fun k σ'' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, ?_⟩
    rw [h4]
    by_cases hc : (⟨m, hm⟩ : Fin n) ∈ goodCands T S d L
    · rw [if_pos hc, if_pos ⟨hm, hc⟩]
    · rw [if_neg hc, if_neg (fun ⟨_, h⟩ => hc h)]
  have hl1 := hl.fr T hf1 (by unfold LayRegs SCF SCB; decide)
  rw [ffind_min] at hF1 hR1
  have hpk : pickT T S d L = if h : (goodCands T S d L).Nonempty then
      d ((goodCands T S d L).min' h) - T.x L ((goodCands T S d L).min' h)
      else ∑ e ∈ S, d e + 1 := rfl
  by_cases hne : (goodCands T S d L).Nonempty
  · rw [dif_pos hne] at hF1 hR1
    simp only [Option.isSome_some, if_true, Option.getD_some] at hF1 hR1
    refine r_ifle (fun h => absurd h (by rw [hF1]; norm_num)) (fun _ => ?_)
    set e := (goodCands T S d L).min' hne
    refine r_seq (r_mono (h_ldAt σ1 321 201 331 _ _ hl1.b1 hR1)
      fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
    refine r_seq (r_mono (h_ldAt σ2 322 203 331 (rb n 3) e.val (by rw [hf2 203 (by decide), hl1.b3])
      (by rw [hf2 331 (by decide), hR1])) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
    refine r_mono (h_sub σ3 213 321 322) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ⟨?_, ?_, ?_, ?_⟩
    · have := e.isLt
      have hc := cost_t1 n
      unfold rb at hk2 hk3
      omega
    · rw [hm4, hm3, hm2, hm1]
    · exact Fr.tr (hf1.mono (by unfold SCF STP; decide)) (Fr.tr (hf2.mono
        (by unfold STP SCF SCB; decide)) (Fr.tr (hf3.mono (by unfold STP SCF SCB; decide))
        (hf4.mono (by unfold STP; decide))))
    · rw [hv4, hf3 321 (by decide), hv2, hv3, hm2, hm1, hd e, hx e, hpk, dif_pos hne]
  · rw [dif_neg hne] at hF1 hR1
    simp only [Option.isSome_none, Bool.false_eq_true, if_false] at hF1
    refine r_ifle (fun _ => ?_) (fun h => absurd (le_of_eq hF1) h)
    refine r_seq (r_mono (h_sumLoop 301 1 313 314 334 335 sdBody
      [100, 101, 109, 302, 303, 335] [100, 101, 109, 301, 302, 303, 313, 314, 334, 335]
      (by unfold LoopOK; decide) n (100 * (n + 1))
      (fun m => if h : m < n then (if (⟨m, h⟩ : Fin n) ∈ S then d ⟨m, h⟩ else 0) else 0) σ1
      hl1.h1 ?_) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
    · intro m hm σ' hm' hf' hV'
      have hl' := hl1.fr T hf' (by unfold LayRegs; decide)
      refine r_seq (r_mono (h_ldAt σ' 302 200 301 _ _ hl'.b0 hV')
        fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
      refine r_seq (r_mono (h_ldAt σ3 303 201 301 (rb n 1) m (by rw [hf3 201 (by decide), hl'.b1])
        (by rw [hf3 301 (by decide), hV'])) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
      refine r_mono (h_mul σ4 335 302 303) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ =>
        ⟨?_, by rw [hm5, hm4, hm3], ?_, ?_⟩
      · unfold rb at hk3 hk4; omega
      · exact Fr.tr (hf3.mono (by decide)) (Fr.tr (hf4.mono (by decide)) (hf5.mono (by decide)))
      · rw [hv5, hf4 302 (by decide), hv3, hv4, hm3, hm', hm1]
        have h1 := hS ⟨m, hm⟩
        have h2 := hd ⟨m, hm⟩
        simp only at h1 h2
        rw [h1, h2]
        unfold ind
        by_cases c : (⟨m, hm⟩ : Fin n) ∈ S <;> simp [c, hm]
    refine r_seq (r_mono (h_const σ2 336 1) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ =>
      r_mono (h_add σ3 213 334 336) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ⟨?_, ?_, ?_, ?_⟩)
    · have hc := cost_t2 n
      omega
    · rw [hm4, hm3, hm2, hm1]
    · exact Fr.tr (hf1.mono (by unfold SCF STP; decide)) (Fr.tr (hf2.mono
        (by unfold STP SCF SCB; decide)) (Fr.trm hf3 hf4 (by unfold STP; decide)
        (by unfold STP; decide)))
    · rw [hv4, hf3 334 (by decide), hv2, hv3, sum_fin_range (fun f => if f ∈ S then d f else 0),
        hpk, dif_neg hne]
      rw [← Finset.sum_ite_mem_eq S]
      push_cast; ring

/-!
Part PR, file 6: red flags (region 4), root-patch flags (region 5), `|P|` (register `214`) and
`RinS` (register `215`), for the time `t` in register `213`.
-/
theorem iter_ne_root' (f : Fin n) (i : ℕ) (hi : i < T.depth f) : T.parent^[i] f ≠ T.root := by
  intro h
  have := PartB.depth_iter T f i
  rw [h, T.depth_root] at this
  omega

theorem anc_iff' (P : Fin n → Prop) (f : Fin n) :
    (∀ i < T.depth f, P (T.parent^[i] f)) ↔ (∀ a ∈ T.edges, T.IsAnc a f → P a) := by
  constructor
  · rintro h a ha ⟨i, rfl⟩
    by_cases hi : i < T.depth f
    · exact h i hi
    · exfalso
      have : T.parent^[i] f = T.root := by
        obtain ⟨j, rfl⟩ : ∃ j, i = j + T.depth f := ⟨i - T.depth f, by omega⟩
        rw [Function.iterate_add_apply, PartB.iter_depth, PartB.iter_root]
      exact (mem_edges_iff T _).mp ha this
  · intro h i hi
    exact h _ ((mem_edges_iff T _).mpr (iter_ne_root' T f i hi)) ⟨i, rfl⟩

theorem mem_patchS (S : Finset (Fin n)) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) (v : Fin n) :
    v ∈ patchS T S d L t ↔ v ∈ redS T S d L t ∧
      ∀ i < T.depth v, T.parent^[i] v ∈ redS T S d L t := by
  unfold patchS
  rw [Finset.mem_filter, anc_iff' T (fun a => a ∈ redS T S d L t) v]

theorem cost_red (n : ℕ) :
    n * (300 * (n + 1) + 4 * ((3 + 2 * 4) * (n + 1) + n) + 13) + 3 ≤ 400 * (n + 1) ^ 2 := by
  nlinarith

theorem cost_patch (n : ℕ) :
    n * (400 * (n + 1) ^ 2 + 4 * ((3 + 2 * 5) * (n + 1) + n) + 13) + 3 ≤ 500 * (n + 1) ^ 3 := by
  nlinarith

theorem cost_pb (n : ℕ) : n * (100 * (n + 1) + 2) + 1 + 4 * ((3 + 2 * 4) * (n + 1) + n) + 7 +
    2 + 1 + 7 + 2 + 1 ≤ 400 * (n + 1) ^ 2 := by nlinarith

/-- `344 := [v ∈ redS]` (`v` in `340`, `t` in `213`). -/
def redBody : Stmt :=
  .seq (ldAt 345 200 340) (.seq (ldAt 346 201 340) (.seq (ldAt 347 203 340)
  (.seq (.add 348 347 213) (.seq (ltF 349 346 348) (.mul 344 345 349)))))

def SRB : List ℕ := [100, 101, 102, 109, 344, 345, 346, 347, 348, 349]

theorem h_redBody (σ : Cfg) (hl : Lay T σ) (S : Finset (Fin n)) (d : Fin n → ℝ)
    (L : List (Fin n)) (t : ℝ) (v : Fin n) (h213 : σ.regs 213 = t) (h340 : σ.regs 340 = v.val)
    (hS : VOK σ.mem (rb n 0) (ind S)) (hd : VOK σ.mem (rb n 1) d)
    (hx : VOK σ.mem (rb n 3) (T.x L)) :
    Runs redBody σ (fun k σ' => k ≤ 300 * (n + 1) ∧ σ'.mem = σ.mem ∧ Fr SRB σ σ' ∧
      σ'.regs 344 = ind (redS T S d L t) v) := by
  have hv := v.isLt
  refine r_seq (r_mono (h_ldAt σ 345 200 340 _ _ hl.b0 h340) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_ldAt σ1 346 201 340 (rb n 1) v.val (by rw [hf1 201 (by decide), hl.b1])
    (by rw [hf1 340 (by decide), h340])) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_ldAt σ2 347 203 340 (rb n 3) v.val
    (by rw [hf2 203 (by decide), hf1 203 (by decide), hl.b3])
    (by rw [hf2 340 (by decide), hf1 340 (by decide), h340])) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  refine r_seq (r_mono (h_add σ3 348 347 213) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
  refine r_seq (r_mono (h_ltF σ4 349 346 348) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
  refine r_mono (h_mul σ5 344 345 349) fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ⟨?_, ?_, ?_, ?_⟩
  · unfold rb at hk1 hk2 hk3; omega
  · rw [hm6, hm5, hm4, hm3, hm2, hm1]
  · exact Fr.tr (hf1.mono (by decide)) (Fr.tr (hf2.mono (by decide)) (Fr.tr (hf3.mono
      (by decide)) (Fr.tr (hf4.mono (by decide)) (Fr.tr (hf5.mono (by decide))
      (hf6.mono (by decide))))))
  · have hM2 : σ2.mem = σ.mem := by rw [hm2, hm1]
    rw [hv6, hf5 345 (by decide), hf4 345 (by decide), hf3 345 (by decide), hf2 345 (by decide),
      hv1, hS v, hv5, hv4, hf4 346 (by decide), hf3 346 (by decide), hv2, hv3, hM2, hm1, hd v,
      hx v, hf3 213 (by decide), hf2 213 (by decide), hf1 213 (by decide), h213]
    unfold ind redS
    simp only [Finset.mem_filter]
    by_cases c1 : v ∈ S <;> by_cases c2 : d v < T.x L v + t <;> simp [c1, c2]

def SRP : List ℕ := SRB ++ [340, 341, 342, 343]

def redPhase : Stmt := fillLoop 340 1 341 342 204 343 344 redBody

theorem h_redPhase (σ : Cfg) (hl : Lay T σ) (S : Finset (Fin n)) (d : Fin n → ℝ)
    (L : List (Fin n)) (t : ℝ) (h213 : σ.regs 213 = t)
    (hS : VOK σ.mem (rb n 0) (ind S)) (hd : VOK σ.mem (rb n 1) d)
    (hx : VOK σ.mem (rb n 3) (T.x L)) :
    Runs redPhase σ (fun k σ' => k ≤ 400 * (n + 1) ^ 2 ∧ Fr SRP σ σ' ∧
      (∀ z : ℤ, ¬ (((rb n 4 : ℕ) : ℤ) ≤ z ∧ z < rb n 4 + n) → σ'.mem z = σ.mem z) ∧
      VOK σ'.mem (rb n 4) (ind (redS T S d L t))) := by
  have hc := cost_red n
  have hm3 : ∀ M : ℤ → ℝ, (∀ z : ℤ, z < ((rb n 4 : ℕ) : ℤ) → M z = σ.mem z) →
      VOK M (rb n 0) (ind S) ∧ VOK M (rb n 1) d ∧ VOK M (rb n 3) (T.x L) := by
    intro M hM
    refine ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩ <;>
    · rw [hM _ (by have := v.isLt; unfold rb; push_cast; omega)]
      first | exact hS v | exact hd v | exact hx v
  refine r_mono (h_fillLoop 340 1 341 342 204 343 344 redBody SRB SRP
    (by unfold FillOK SRB SRP; decide) n (300 * (n + 1)) (rb n 4)
    (fun m => if h : m < n then ind (redS T S d L t) ⟨m, h⟩ else 0) σ hl.h1 hl.b4 ?_)
    fun k σ' ⟨hk, hf, hm, hv⟩ => ⟨?_, hf, hm, fun v => by rw [hv v.val v.isLt]; simp⟩
  · intro m hm σ' hm' hf' hV'
    have hl' := hl.fr T hf' (by unfold LayRegs SRP SRB; decide)
    obtain ⟨a, b, c⟩ := hm3 σ'.mem (fun z hz => hm' z (by omega))
    refine r_mono (h_redBody T σ' hl' S d L t ⟨m, hm⟩ (by rw [hf' 213 (by decide), h213]) hV'
      a b c) fun k σ'' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, by rw [h4]; simp [hm]⟩
  · unfold rb at hk; omega

/-! ### Root patch flags -/
def chainBody : Stmt :=
  .seq (ldAt 359 204 355) (.seq (.mul 354 354 359) (.seq (ldIn 360 2 355) (.seq (mov 355 360)
    (.seq (eqT 357 355 2) (notF 358 357)))))

/-- `354 := [v ∈ patchS]` (`v` in `350`). -/
def patchBody : Stmt :=
  .seq (ldAt 356 204 350) (.seq (mov 355 350) (.seq (.const 354 1) (.seq (eqT 357 355 2)
    (.seq (notF 358 357) (.seq (.whilegt 358 chainBody) (.mul 354 354 356))))))

def SCH : List ℕ := [100, 101, 102, 109, 354, 355, 357, 358, 359, 360]

def SPB : List ℕ := [100, 101, 102, 109, 354, 355, 356, 357, 358, 359, 360]

theorem h_patchBody (σ : Cfg) (hl : Lay T σ) (R : Finset (Fin n)) (v : Fin n)
    (h350 : σ.regs 350 = v.val) (hR : VOK σ.mem (rb n 4) (ind R)) (hP : ParOK T σ.mem) :
    Runs patchBody σ (fun k σ' => k ≤ 400 * (n + 1) ^ 2 ∧ σ'.mem = σ.mem ∧ Fr SPB σ σ' ∧
      σ'.regs 354 = if v ∈ R ∧ ∀ i < T.depth v, T.parent^[i] v ∈ R then 1 else 0) := by
  have hv := v.isLt
  refine r_seq (r_mono (h_ldAt σ 356 204 350 _ _ hl.b4 h350) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_mov σ1 355 350 (by decide)) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_const σ2 354 1) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  refine r_seq (r_mono (h_eqT σ3 357 355 2 (by decide) (by decide) (by decide))
    fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
  refine r_seq (r_mono (h_notF σ4 358 357 (by decide)) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
  have hf05 : Fr SPB σ σ5 := Fr.tr (hf1.mono (by decide)) (Fr.tr (hf2.mono (by decide))
    (Fr.tr (hf3.mono (by decide)) (Fr.tr (hf4.mono (by decide)) (hf5.mono (by decide)))))
  have hM5 : σ5.mem = σ.mem := by rw [hm5, hm4, hm3, hm2, hm1]
  have hl5 := hl.fr T hf05 (by unfold LayRegs SPB; decide)
  have e356 : σ5.regs 356 = ind R v := by
    rw [hf5 356 (by decide), hf4 356 (by decide), hf3 356 (by decide), hf2 356 (by decide), hv1,
      hR v]
  let I : ℕ → Cfg → Prop := fun j σ' => σ'.mem = σ.mem ∧ Fr SCH σ5 σ' ∧
    σ'.regs 355 = (T.parent^[j] v).val ∧
    σ'.regs 354 = (if ∀ i < j, T.parent^[i] v ∈ R then 1 else 0) ∧
    σ'.regs 358 = (if T.parent^[j] v = T.root then 0 else 1)
  refine r_seq (r_while 358 chainBody (T.depth v) (100 * (n + 1)) I _ ?_ ?_ σ5 ?_ ?_)
  · intro j hj σ' ⟨hm', hf', h355, h354, h358⟩
    have hne := iter_ne_root' T v j hj
    refine ⟨by rw [h358, if_neg hne]; norm_num, ?_⟩
    set a := T.parent^[j] v with ha
    have hl' := hl5.fr T hf' (by unfold LayRegs SCH; decide)
    have hav := a.isLt
    refine r_seq (r_mono (h_ldAt σ' 359 204 355 _ _ hl'.b4 h355)
      fun k1 σ6 ⟨hk1, hm6, hf6, hv6⟩ => ?_)
    refine r_seq (r_mono (h_mul σ6 354 354 359) fun k2 σ7 ⟨hk2, hm7, hf7, hv7⟩ => ?_)
    refine r_seq (r_mono (h_ldIn σ7 360 2 355 (by decide) a.val (by
      rw [hf7 355 (by decide), hf6 355 (by decide), h355])) fun k3 σ8 ⟨hk3, hm8, hf8, hv8⟩ => ?_)
    refine r_seq (r_mono (h_mov σ8 355 360 (by decide)) fun k4 σ9 ⟨hk4, hm9, hf9, hv9⟩ => ?_)
    refine r_seq (r_mono (h_eqT σ9 357 355 2 (by decide) (by decide) (by decide))
      fun k5 σ10 ⟨hk5, hm10, hf10, hv10⟩ => ?_)
    refine r_mono (h_notF σ10 358 357 (by decide)) fun k6 σ11 ⟨hk6, hm11, hf11, hv11⟩ =>
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold rb at hk1; omega
    · rw [hm11, hm10, hm9, hm8, hm7, hm6, hm']
    · exact Fr.tr hf' (Fr.tr (hf6.mono (by decide)) (Fr.tr (hf7.mono (by decide))
        (Fr.tr (hf8.mono (by decide)) (Fr.tr (hf9.mono (by decide)) (Fr.tr (hf10.mono
        (by decide)) (hf11.mono (by decide)))))))
    · have e : σ9.regs 355 = (T.parent a).val := by
        rw [hv9, hv8, hm7, hm6, hm', (hP a).1]
      rw [hf11 355 (by decide), hf10 355 (by decide), e, Function.iterate_succ_apply']
    · rw [hf11 354 (by decide), hf10 354 (by decide), hf9 354 (by decide), hf8 354 (by decide),
        hv7, hf6 354 (by decide), h354, hv6, hm', hR a]
      unfold ind
      have key : (∀ i < j + 1, T.parent^[i] v ∈ R) ↔ (∀ i < j, T.parent^[i] v ∈ R) ∧ a ∈ R :=
        ⟨fun h => ⟨fun i hi => h i (by omega), h j (by omega)⟩, fun ⟨h1, h2⟩ i hi => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
          · exact h1 i hi
          · rw [hi]; exact h2⟩
      by_cases c1 : ∀ i < j, T.parent^[i] v ∈ R <;> by_cases c2 : a ∈ R
      · rw [if_pos c1, if_pos c2, if_pos (key.mpr ⟨c1, c2⟩)]; norm_num
      · rw [if_pos c1, if_neg c2, if_neg (fun h => c2 (key.mp h).2)]; norm_num
      · rw [if_neg c1, if_pos c2, if_neg (fun h => c1 (key.mp h).1)]; norm_num
      · rw [if_neg c1, if_neg c2, if_neg (fun h => c1 (key.mp h).1)]; norm_num
    · have e : σ9.regs 355 = (T.parent a).val := by
        rw [hv9, hv8, hm7, hm6, hm', (hP a).1]
      rw [hv11, hv10, e, hf9 2 (by decide), hf8 2 (by decide), hf7 2 (by decide),
        hf6 2 (by decide), hl'.h2, Function.iterate_succ_apply']
      by_cases c : T.parent a = T.root
      · rw [if_pos (by rw [c]), if_pos c]; norm_num
      · rw [if_neg (fun h => c ((cval_eq _ _).mp h)), if_neg c]; norm_num
  · intro σ' ⟨_, _, _, _, h358⟩
    rw [h358, PartB.iter_depth, if_pos rfl]
  · refine ⟨hM5, Fr.rfl' _ _, ?_, ?_, ?_⟩
    · rw [hf5 355 (by decide), hf4 355 (by decide), hf3 355 (by decide), hv2, hf1 350 (by decide),
        h350]; rfl
    · rw [hf5 354 (by decide), hf4 354 (by decide), hv3]; simp
    · rw [hv5, hv4, hf3 355 (by decide), hv2, hf1 350 (by decide), h350, hf3 2 (by decide),
        hf2 2 (by decide), hf1 2 (by decide), hl.h2]
      rw [Function.iterate_zero_apply]
      by_cases c : v = T.root
      · rw [if_pos (by rw [c]), if_pos c]; norm_num
      · rw [if_neg (fun h => c ((cval_eq _ _).mp h)), if_neg c]; norm_num
  · intro k6 σ6 hk6 ⟨hm6, hf6, _, h354, _⟩
    refine r_mono (h_mul σ6 354 354 356) fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ => ⟨?_, ?_, ?_, ?_⟩
    · have hd := PartB.depth_lt T v
      have h1 : T.depth v * (100 * (n + 1) + 2) ≤ n * (100 * (n + 1) + 2) :=
        Nat.mul_le_mul_right _ hd.le
      have := cost_pb n
      unfold rb at hk1
      omega
    · rw [hm7, hm6]
    · exact Fr.tr hf05 (Fr.tr (hf6.mono (by unfold SCH SPB; decide)) (hf7.mono (by decide)))
    · rw [hv7, h354, hf6 356 (by decide), e356]
      unfold ind
      by_cases c1 : v ∈ R <;> by_cases c2 : ∀ i < T.depth v, T.parent^[i] v ∈ R <;>
        simp [c1, c2]

def SPP : List ℕ := SPB ++ [350, 351, 352, 353]

def patchPhase : Stmt := fillLoop 350 1 351 352 205 353 354 patchBody

theorem h_patchPhase (σ : Cfg) (hl : Lay T σ) (S : Finset (Fin n)) (d : Fin n → ℝ)
    (L : List (Fin n)) (t : ℝ) (hR : VOK σ.mem (rb n 4) (ind (redS T S d L t)))
    (hP : ParOK T σ.mem) :
    Runs patchPhase σ (fun k σ' => k ≤ 500 * (n + 1) ^ 3 ∧ Fr SPP σ σ' ∧
      (∀ z : ℤ, ¬ (((rb n 5 : ℕ) : ℤ) ≤ z ∧ z < rb n 5 + n) → σ'.mem z = σ.mem z) ∧
      VOK σ'.mem (rb n 5) (ind (patchS T S d L t))) := by
  refine r_mono (h_fillLoop 350 1 351 352 205 353 354 patchBody SPB SPP
    (by unfold FillOK SPB SPP; decide) n (400 * (n + 1) ^ 2) (rb n 5)
    (fun m => if h : m < n then ind (patchS T S d L t) ⟨m, h⟩ else 0) σ hl.h1 hl.b5 ?_)
    fun k σ' ⟨hk, hf, hm, hv⟩ => ⟨?_, hf, hm, fun v => by rw [hv v.val v.isLt]; simp⟩
  · intro m hm σ' hm' hf' hV'
    have hl' := hl.fr T hf' (by unfold LayRegs SPP SPB; decide)
    have hR' : VOK σ'.mem (rb n 4) (ind (redS T S d L t)) := by
      intro v; rw [hm' _ (by have := v.isLt; unfold rb; push_cast; omega)]; exact hR v
    have hP' : ParOK T σ'.mem := by
      intro w
      have := w.isLt
      rw [hm' _ (by unfold rb; push_cast; omega), hm' _ (by unfold rb; push_cast; omega)]
      exact hP w
    refine r_mono (h_patchBody T σ' hl' (redS T S d L t) ⟨m, hm⟩ hV' hR' hP')
      fun k σ'' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, ?_⟩
    rw [h4]
    simp only [hm, dif_pos, ind]
    by_cases c : (⟨m, hm⟩ : Fin n) ∈ patchS T S d L t
    · rw [if_pos ((mem_patchS T S d L t _).mp c), if_pos c]
    · rw [if_neg (fun h => c ((mem_patchS T S d L t _).mpr h)), if_neg c]
  · have := cost_patch n
    unfold rb at hk; omega

/-! ### `|P|` and `RinS` -/
def cardBody : Stmt := ldAt 364 205 361

def rinBody : Stmt := .seq (ldAt 364 205 361) (.seq (ldIn 365 3 361) (.mul 366 364 365))

def pSums : Stmt :=
  .seq (sumLoop 361 1 362 363 214 364 cardBody) (sumLoop 361 1 362 363 215 366 rinBody)

def SPS : List ℕ := [100, 101, 109, 214, 215, 361, 362, 363, 364, 365, 366]

theorem h_pSums (σ : Cfg) (hl : Lay T σ) (P : Finset (Fin n))
    (hPv : VOK σ.mem (rb n 5) (ind P)) (hP : ParOK T σ.mem) :
    Runs pSums σ (fun k σ' => k ≤ 300 * (n + 1) ^ 2 ∧ σ'.mem = σ.mem ∧ Fr SPS σ σ' ∧
      σ'.regs 214 = (P.card : ℝ) ∧ σ'.regs 215 = ∑ e ∈ P, T.W e) := by
  refine r_seq (r_mono (h_sumLoop 361 1 362 363 214 364 cardBody [100, 101, 109, 364]
    [100, 101, 109, 361, 362, 363, 214, 364] (by unfold LoopOK; decide) n (100 * (n + 1))
    (fun m => if h : m < n then ind P ⟨m, h⟩ else 0) σ hl.h1 ?_)
    fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  · intro m hm σ' hm' hf' hV'
    have hl' := hl.fr T hf' (by unfold LayRegs; decide)
    refine r_mono (h_ldAt σ' 364 205 361 _ _ hl'.b5 hV') fun k σ'' ⟨h1, h2, h3, h4⟩ =>
      ⟨by unfold rb at h1; omega, h2, h3, ?_⟩
    rw [h4, hm']
    have := hPv ⟨m, hm⟩
    simp only at this
    rw [this]; simp [hm]
  have hl1 := hl.fr T hf1 (by unfold LayRegs; decide)
  refine r_mono (h_sumLoop 361 1 362 363 215 366 rinBody [100, 101, 109, 364, 365, 366]
    [100, 101, 109, 361, 362, 363, 215, 364, 365, 366] (by unfold LoopOK; decide) n
    (100 * (n + 1)) (fun m => if h : m < n then ind P ⟨m, h⟩ * T.W ⟨m, h⟩ else 0) σ1 hl1.h1 ?_)
    fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ⟨?_, by rw [hm2, hm1], ?_, ?_, ?_⟩
  · intro m hm σ' hm' hf' hV'
    have hl' := hl1.fr T hf' (by unfold LayRegs; decide)
    refine r_seq (r_mono (h_ldAt σ' 364 205 361 _ _ hl'.b5 hV') fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ =>
      r_seq (r_mono (h_ldIn σ3 365 3 361 (by decide) m (by rw [hf3 361 (by decide), hV']))
      fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => r_mono (h_mul σ4 366 364 365)
      fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ⟨?_, by rw [hm5, hm4, hm3], ?_, ?_⟩))
    · unfold rb at hk3; omega
    · exact Fr.tr (hf3.mono (by decide)) (Fr.tr (hf4.mono (by decide)) (hf5.mono (by decide)))
    · rw [hv5, hf4 364 (by decide), hv3, hv4, hm3, hm', hm1]
      have h1 := hPv ⟨m, hm⟩
      have h2 := (hP ⟨m, hm⟩).2
      simp only at h1 h2
      rw [h1, h2]; simp [hm]
  · nlinarith
  · exact Fr.trm hf1 hf2 (by unfold SPS; decide) (by unfold SPS; decide)
  · rw [hf2 214 (by decide), hv1, sum_fin_range (fun v => ind P v)]
    unfold ind
    rw [Finset.sum_boole]
    simp
  · rw [hv2, sum_fin_range (fun v => ind P v * T.W v)]
    unfold ind
    rw [← Finset.sum_ite_mem_eq P]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp

end OnlineTransportation1195.Dev.T13.PartPR
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.T13.PartPR
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
  OnlineTransportation1195.Dev.T13 OnlineTransportation1195.Dev.RL.Lib Function
/-!
Part PR, file 7: `s = pickS (RinS)` into register `216` (`RinS` in register `215`).
-/
theorem fmax_eq (p : ℕ → Prop) (g : ℕ → ℝ) (m : ℕ) :
    fmax p g m = (insert 0 (((Finset.range m).filter p).image g)).max'
      (Finset.insert_nonempty _ _) := by
  induction m with
  | zero => simp [fmax]
  | succ m ih =>
    simp only [fmax]
    have e : ∀ (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty), A = B → A.max' hA = B.max' hB :=
      by intro A B hA hB h; subst h; rfl
    by_cases hp : p m
    · rw [if_pos hp, ih]
      have hset : insert (0 : ℝ) (((Finset.range (m + 1)).filter p).image g) =
          insert (g m) (insert 0 (((Finset.range m).filter p).image g)) := by
        rw [Finset.range_add_one, Finset.filter_insert, if_pos hp, Finset.image_insert,
          Finset.insert_comm]
      rw [e _ _ _ (Finset.insert_nonempty _ _) hset,
        Finset.max'_insert (g m) _ (Finset.insert_nonempty _ _)]
      exact max_comm _ _
    · rw [if_neg hp, ih]
      refine e _ _ _ _ ?_
      rw [Finset.range_add_one, Finset.filter_insert, if_neg hp]

end OnlineTransportation1195.Dev.T13.PartPR
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.T13.PartPR
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
  OnlineTransportation1195.Dev.T13 OnlineTransportation1195.Dev.RL.Lib Function
variable {n : ℕ} (T : Tree n)
theorem betaLoS_eq (S : Finset (Fin n)) (d : Fin n → ℝ) (r : ℝ) :
    fmax (fun m => ∃ h : m < n, (⟨m, h⟩ : Fin n) ∈ S ∧ FS T S d (d ⟨m, h⟩) ≤ r)
      (fun m => if h : m < n then d ⟨m, h⟩ else 0) n = betaLoS T S d r := by
  rw [fmax_eq]
  unfold betaLoS
  congr 2
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨m, ⟨hm, h, hS, hF⟩, rfl⟩
    exact ⟨⟨m, h⟩, ⟨hS, hF⟩, by simp [h]⟩
  · rintro ⟨e, ⟨hS, hF⟩, rfl⟩
    exact ⟨e.val, ⟨e.isLt, e.isLt, hS, hF⟩, by simp⟩

/-- `374 := [e ∈ S ∧ FS (d e) ≤ r]`, `375 := d e` (`e` in `370`). -/
def betaBody : Stmt :=
  .seq (ldAt 376 200 370) (.seq (ldAt 375 201 370) (.seq (mov 300 375) (.seq evalRF
    (.seq (leF 377 316 215) (.mul 374 376 377)))))

def SBB : List ℕ := SRF ++ [300, 374, 375, 376, 377]

theorem h_betaBody (σ : Cfg) (hl : Lay T σ) (S : Finset (Fin n)) (d : Fin n → ℝ)
    (L : List (Fin n)) (r : ℝ) (e : Fin n) (h215 : σ.regs 215 = r) (h370 : σ.regs 370 = e.val)
    (hS : VOK σ.mem (rb n 0) (ind S)) (hd : VOK σ.mem (rb n 1) d)
    (hx : VOK σ.mem (rb n 3) (T.x L)) (hP : ParOK T σ.mem) :
    Runs betaBody σ (fun k σ' => k ≤ 800 * (n + 1) ^ 2 ∧ σ'.mem = σ.mem ∧ Fr SBB σ σ' ∧
      σ'.regs 374 = (if e ∈ S ∧ FS T S d (d e) ≤ r then 1 else 0) ∧ σ'.regs 375 = d e) := by
  have he := e.isLt
  refine r_seq (r_mono (h_ldAt σ 376 200 370 _ _ hl.b0 h370) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_ldAt σ1 375 201 370 (rb n 1) e.val (by rw [hf1 201 (by decide), hl.b1])
    (by rw [hf1 370 (by decide), h370])) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_mov σ2 300 375 (by decide)) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  have hM3 : σ3.mem = σ.mem := by rw [hm3, hm2, hm1]
  have hf03 : Fr [100, 101, 109, 376, 375, 300] σ σ3 := Fr.tr (hf1.mono (by decide))
    (Fr.tr (hf2.mono (by decide)) (hf3.mono (by decide)))
  have hl3 := hl.fr T hf03 (by unfold LayRegs; decide)
  have e375 : σ3.regs 375 = d e := by rw [hf3 375 (by decide), hv2, hm1, hd e]
  refine r_seq (r_mono (h_evalRF T σ3 hl3 S d L (d e) (by rw [hv3, hv2, hm1, hd e])
    (by rw [hM3]; exact hS) (by rw [hM3]; exact hd) (by rw [hM3]; exact hx)
    (by rw [hM3]; exact hP)) fun k4 σ4 ⟨hk4, hm4, hf4, hv4R, hv4F⟩ => ?_)
  refine r_seq (r_mono (h_leF σ4 377 316 215) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
  refine r_mono (h_mul σ5 374 376 377) fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold rb at hk1 hk2; nlinarith
  · rw [hm6, hm5, hm4, hM3]
  · exact Fr.tr (hf03.mono (by unfold SBB SRF; decide)) (Fr.tr (hf4.mono (by unfold SBB; decide))
      (Fr.tr (hf5.mono (by unfold SBB SRF; decide)) (hf6.mono (by unfold SBB SRF; decide))))
  · rw [hv6, hf5 376 (by decide), hf4 376 (by unfold SRF; decide), hf3 376 (by decide),
      hf2 376 (by decide), hv1, hS e, hv5, hv4F, hf4 215 (by unfold SRF; decide),
      hf03 215 (by decide), h215]
    unfold ind
    by_cases c1 : e ∈ S <;> by_cases c2 : FS T S d (d e) ≤ r <;> simp [c1, c2]
  · rw [hf6 375 (by decide), hf5 375 (by decide), hf4 375 (by unfold SRF; decide), e375]

/-- `385 := [e ∈ S ∧ d e ≤ β] W e` (`β` in `373`, `e` in `380`). -/
def aBody : Stmt :=
  .seq (ldAt 381 200 380) (.seq (ldAt 382 201 380) (.seq (leF 383 382 373)
    (.seq (ldIn 384 3 380) (.seq (.mul 385 381 383) (.mul 385 385 384)))))

/-- `385 := [e ∈ S ∧ β < d e] W e / d e`. -/
def bBody : Stmt :=
  .seq (ldAt 381 200 380) (.seq (ldAt 382 201 380) (.seq (ltF 383 373 382)
    (.seq (ldIn 384 3 380) (.seq (tdv 389 384 382) (.seq (.mul 385 381 383)
    (.mul 385 385 389))))))

def SAB : List ℕ := [100, 101, 102, 103, 104, 109, 381, 382, 383, 384, 385, 389]

theorem h_abBody (σ : Cfg) (hl : Lay T σ) (S : Finset (Fin n)) (d : Fin n → ℝ) (β : ℝ)
    (e : Fin n) (h373 : σ.regs 373 = β) (h380 : σ.regs 380 = e.val)
    (hS : VOK σ.mem (rb n 0) (ind S)) (hd : VOK σ.mem (rb n 1) d) (hP : ParOK T σ.mem) :
    Runs aBody σ (fun k σ' => k ≤ 200 * (n + 1) ∧ σ'.mem = σ.mem ∧ Fr SAB σ σ' ∧
      σ'.regs 385 = if e ∈ S ∧ d e ≤ β then T.W e else 0) ∧
    Runs bBody σ (fun k σ' => k ≤ 200 * (n + 1) ∧ σ'.mem = σ.mem ∧ Fr SAB σ σ' ∧
      σ'.regs 385 = if e ∈ S ∧ β < d e then T.W e / d e else 0) := by
  have he := e.isLt
  constructor
  · refine r_seq (r_mono (h_ldAt σ 381 200 380 _ _ hl.b0 h380)
      fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
    refine r_seq (r_mono (h_ldAt σ1 382 201 380 (rb n 1) e.val
      (by rw [hf1 201 (by decide), hl.b1]) (by rw [hf1 380 (by decide), h380]))
      fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
    refine r_seq (r_mono (h_leF σ2 383 382 373) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
    refine r_seq (r_mono (h_ldIn σ3 384 3 380 (by decide) e.val (by
      rw [hf3 380 (by decide), hf2 380 (by decide), hf1 380 (by decide), h380]))
      fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
    refine r_seq (r_mono (h_mul σ4 385 381 383) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
    refine r_mono (h_mul σ5 385 385 384) fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ⟨?_, ?_, ?_, ?_⟩
    · unfold rb at hk1 hk2; omega
    · rw [hm6, hm5, hm4, hm3, hm2, hm1]
    · exact Fr.tr (hf1.mono (by decide)) (Fr.tr (hf2.mono (by decide)) (Fr.tr (hf3.mono
        (by decide)) (Fr.tr (hf4.mono (by decide)) (Fr.tr (hf5.mono (by decide))
        (hf6.mono (by decide))))))
    · rw [hv6, hv5, hf4 381 (by decide), hf3 381 (by decide), hf2 381 (by decide), hv1, hS e,
        hf4 383 (by decide), hv3, hv2, hm1, hd e, hf2 373 (by decide), hf1 373 (by decide), h373,
        hf5 384 (by decide), hv4, hm3, hm2, hm1, (hP e).2]
      unfold ind
      by_cases c1 : e ∈ S <;> by_cases c2 : d e ≤ β <;> simp [c1, c2]
  · refine r_seq (r_mono (h_ldAt σ 381 200 380 _ _ hl.b0 h380)
      fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
    refine r_seq (r_mono (h_ldAt σ1 382 201 380 (rb n 1) e.val
      (by rw [hf1 201 (by decide), hl.b1]) (by rw [hf1 380 (by decide), h380]))
      fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
    refine r_seq (r_mono (h_ltF σ2 383 373 382) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
    refine r_seq (r_mono (h_ldIn σ3 384 3 380 (by decide) e.val (by
      rw [hf3 380 (by decide), hf2 380 (by decide), hf1 380 (by decide), h380]))
      fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
    refine r_seq (r_mono (h_tdv σ4 389 384 382 (by decide) (by decide))
      fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
    refine r_seq (r_mono (h_mul σ5 385 381 383) fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)
    refine r_mono (h_mul σ6 385 385 389) fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ => ⟨?_, ?_, ?_, ?_⟩
    · unfold rb at hk1 hk2; omega
    · rw [hm7, hm6, hm5, hm4, hm3, hm2, hm1]
    · exact Fr.tr (hf1.mono (by decide)) (Fr.tr (hf2.mono (by decide)) (Fr.tr (hf3.mono
        (by decide)) (Fr.tr (hf4.mono (by decide)) (Fr.tr (hf5.mono (by decide))
        (Fr.tr (hf6.mono (by decide)) (hf7.mono (by decide)))))))
    · have e382 : σ4.regs 382 = d e := by
        rw [hf4 382 (by decide), hf3 382 (by decide), hv2, hm1, hd e]
      rw [hv7, hv6, hf5 381 (by decide), hf4 381 (by decide), hf3 381 (by decide),
        hf2 381 (by decide), hv1, hS e, hf5 383 (by decide), hf4 383 (by decide), hv3,
        hf2 373 (by decide), hf1 373 (by decide), h373, hv2, hm1, hd e,
        hf6 389 (by decide), hv5, e382, hv4, hm3, hm2, hm1, (hP e).2]
      unfold ind
      by_cases c1 : e ∈ S <;> by_cases c2 : β < d e <;> simp [c1, c2]

/-- `216 := pickS r` (`r` in `215`). -/
def sCompute : Stmt :=
  .seq (maxLoop 370 1 371 372 373 374 375 betaBody) (.seq (sumLoop 380 1 386 387 388 385 aBody)
    (.seq (sumLoop 380 1 386 387 390 385 bBody) (.seq (.sub 391 215 388) (tdv 216 391 390))))

def sPhase : Stmt :=
  .seq (.const 392 0) (.seq (eqT 393 215 392) (.ifle 393 sCompute (.const 216 0)))

def SMX : List ℕ := SBB ++ [370, 371, 372, 373]

def SSP : List ℕ := SMX ++ SAB ++ [380, 386, 387, 388, 390, 391, 392, 393, 216]

theorem cost_s (n : ℕ) : 1 + (7 + (n * (800 * (n + 1) ^ 2 + 15) + 4 +
    (n * (200 * (n + 1) + 6) + 4 + (n * (200 * (n + 1) + 6) + 4 + (1 + 8))) + 1)) ≤
    1000 * (n + 1) ^ 3 := by nlinarith

theorem h_sPhase (σ : Cfg) (hl : Lay T σ) (S : Finset (Fin n)) (d : Fin n → ℝ)
    (L : List (Fin n)) (r : ℝ) (h215 : σ.regs 215 = r)
    (hS : VOK σ.mem (rb n 0) (ind S)) (hd : VOK σ.mem (rb n 1) d)
    (hx : VOK σ.mem (rb n 3) (T.x L)) (hP : ParOK T σ.mem) :
    Runs sPhase σ (fun k σ' => k ≤ 1000 * (n + 1) ^ 3 ∧ σ'.mem = σ.mem ∧ Fr SSP σ σ' ∧
      σ'.regs 216 = pickS T S d r) := by
  have hc := cost_s n
  refine r_seq (r_mono (h_const σ 392 0) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_eqT σ1 393 215 392 (by decide) (by decide) (by decide))
    fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  have hf02 : Fr [100, 392, 393] σ σ2 := Fr.trm hf1 hf2 (by decide) (by decide)
  have hl2 := hl.fr T hf02 (by unfold LayRegs; decide)
  have hM2 : σ2.mem = σ.mem := by rw [hm2, hm1]
  have e215 : σ2.regs 215 = r := by rw [hf02 215 (by decide), h215]
  have hpick : pickS T S d r = if r = 0 then 0 else (r - sAS T S d r) / sBS T S d r := rfl
  refine r_ifle ?_ ?_
  · intro hne
    have hr : r ≠ 0 := by
      intro h0; rw [hv2, hf1 215 (by decide), h215, hv1, h0] at hne; norm_num at hne
    refine r_seq (r_mono (h_maxLoop 370 1 371 372 373 374 375 betaBody SBB SMX
      (by unfold MaxOK SBB SMX SRF; decide) n (800 * (n + 1) ^ 2)
      (fun m => ∃ h : m < n, (⟨m, h⟩ : Fin n) ∈ S ∧ FS T S d (d ⟨m, h⟩) ≤ r)
      (fun m => if h : m < n then d ⟨m, h⟩ else 0) σ2 hl2.h1 ?_)
      fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
    · intro m hm σ' hm' hf' hV'
      have hl' := hl2.fr T hf' (by unfold LayRegs SMX SBB SRF; decide)
      refine r_mono (h_betaBody T σ' hl' S d L r ⟨m, hm⟩
        (by rw [hf' 215 (by unfold SMX SBB SRF; decide), e215]) hV'
        (by rw [hm', hM2]; exact hS) (by rw [hm', hM2]; exact hd) (by rw [hm', hM2]; exact hx)
        (by rw [hm', hM2]; exact hP)) fun k σ'' ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, ?_, ?_⟩
      · rw [h4]
        by_cases c : (⟨m, hm⟩ : Fin n) ∈ S ∧ FS T S d (d ⟨m, hm⟩) ≤ r
        · rw [if_pos c, if_pos ⟨hm, c⟩]
        · rw [if_neg c, if_neg (fun ⟨_, h⟩ => c h)]
      · intro _; rw [h5]; simp [hm]
    rw [betaLoS_eq] at hv3
    set β := betaLoS T S d r with hβ
    have hl3 := hl2.fr T hf3 (by unfold LayRegs SMX SBB SRF; decide)
    have hM3 : σ3.mem = σ.mem := by rw [hm3, hM2]
    refine r_seq (r_mono (h_sumLoop 380 1 386 387 388 385 aBody SAB
      (SAB ++ [380, 386, 387, 388]) (by unfold LoopOK SAB; decide) n (200 * (n + 1))
      (fun m => if h : m < n then (if (⟨m, h⟩ : Fin n) ∈ S ∧ d ⟨m, h⟩ ≤ β then T.W ⟨m, h⟩
        else 0) else 0) σ3 hl3.h1 ?_) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
    · intro m hm σ' hm' hf' hV'
      have hl' := hl3.fr T hf' (by unfold LayRegs SAB; decide)
      refine r_mono (h_abBody T σ' hl' S d β ⟨m, hm⟩
        (by rw [hf' 373 (by unfold SAB; decide), hv3]) hV' (by rw [hm', hM3]; exact hS)
        (by rw [hm', hM3]; exact hd) (by rw [hm', hM3]; exact hP)).1
        fun k σ'' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, by rw [h4]; simp [hm]⟩
    have hl4 := hl3.fr T hf4 (by unfold LayRegs SAB; decide)
    have hM4 : σ4.mem = σ.mem := by rw [hm4, hM3]
    refine r_seq (r_mono (h_sumLoop 380 1 386 387 390 385 bBody SAB
      (SAB ++ [380, 386, 387, 390]) (by unfold LoopOK SAB; decide) n (200 * (n + 1))
      (fun m => if h : m < n then (if (⟨m, h⟩ : Fin n) ∈ S ∧ β < d ⟨m, h⟩ then
        T.W ⟨m, h⟩ / d ⟨m, h⟩ else 0) else 0) σ4 hl4.h1 ?_)
      fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
    · intro m hm σ' hm' hf' hV'
      have hl' := hl4.fr T hf' (by unfold LayRegs SAB; decide)
      refine r_mono (h_abBody T σ' hl' S d β ⟨m, hm⟩
        (by rw [hf' 373 (by unfold SAB; decide), hf4 373 (by unfold SAB; decide), hv3]) hV'
        (by rw [hm', hM4]; exact hS) (by rw [hm', hM4]; exact hd)
        (by rw [hm', hM4]; exact hP)).2
        fun k σ'' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, by rw [h4]; simp [hm]⟩
    refine r_seq (r_mono (h_sub σ5 391 215 388) fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)
    refine r_mono (h_tdv σ6 216 391 390 (by decide) (by decide))
      fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ => ⟨?_, ?_, ?_, ?_⟩
    · omega
    · rw [hm7, hm6, hm5, hM4]
    · exact Fr.tr (hf02.mono (by unfold SSP SMX SBB SRF; decide)) (Fr.tr (hf3.mono (by unfold SMX SSP; decide)) (Fr.tr
        (hf4.mono (by unfold SSP; decide)) (Fr.tr (hf5.mono (by unfold SSP; decide))
        (Fr.tr (hf6.mono (by unfold SSP; decide)) (hf7.mono (by unfold SSP; decide))))))
    · have eA : σ5.regs 388 = sAS T S d r := by
        rw [hf5 388 (by unfold SAB; decide), hv4,
          sum_fin_range (fun v => if v ∈ S ∧ d v ≤ β then T.W v else 0)]
        unfold sAS
        rw [← hβ, Finset.sum_filter, ← Finset.sum_ite_mem_eq S]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases c1 : v ∈ S <;> simp [c1]
      have eB : σ5.regs 390 = sBS T S d r := by
        rw [hv5, sum_fin_range (fun v => if v ∈ S ∧ β < d v then T.W v / d v else 0)]
        unfold sBS
        rw [← hβ, Finset.sum_filter, ← Finset.sum_ite_mem_eq S]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases c1 : v ∈ S <;> simp [c1]
      rw [hv7, hv6, hf6 390 (by decide), eB, eA, hpick, if_neg hr,
        hf5 215 (by unfold SAB; decide), hf4 215 (by unfold SAB; decide),
        hf3 215 (by unfold SMX SBB SRF; decide), e215]
  · intro heq
    have hr : r = 0 := by
      by_contra hne
      rw [hv2, hf1 215 (by decide), h215, hv1] at heq
      simp [hne] at heq
    refine r_mono (h_const σ2 216 0) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ⟨?_, ?_, ?_, ?_⟩
    · omega
    · rw [hm3, hM2]
    · exact Fr.trm hf02 hf3 (by unfold SSP SMX SBB SRF; decide) (by unfold SSP; decide)
    · rw [hv3, hpick, if_pos hr]; simp

/-!
Part PR, file 8: the levels of the recursion of `walkFn`, the program computing all the data
of one level, and the step to the next level.
-/
/-- The level recurses. -/
def recP (S : Finset (Fin n)) (d : Fin n → ℝ) : Prop :=
  S ≠ ∅ ∧ ¬ (∀ e ∈ S, ∀ f ∈ S, d e = d f) ∧
    patchS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root)) ≠ ∅ ∧
    (patchS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root))).card < S.card

/-- One level of `walkFn`, given the walk `Wn` of the next level. -/
noncomputable def Gstep (S : Finset (Fin n)) (d : Fin n → ℝ) (Wn : List (Fin n)) :
    List (Fin n) :=
  if S = ∅ then [T.root] else if ∀ e ∈ S, ∀ f ∈ S, d e = d f then dfsS T S T.root else
    let L := dfsS T S T.root
    let t := pickT T S d L
    let M := if recP T S d then trunc T (patchS T S d L t) Wn else [T.root]
    M ++ (upPath T (M.getLast?.getD T.root)).tail ++ (blocks L (detS T S d L t)).tail

/-- The next level. -/
noncomputable def adv (Sd : Finset (Fin n) × (Fin n → ℝ)) : Finset (Fin n) × (Fin n → ℝ) :=
  (if recP T Sd.1 Sd.2 then
      patchS T Sd.1 Sd.2 (dfsS T Sd.1 T.root) (pickT T Sd.1 Sd.2 (dfsS T Sd.1 T.root)) else ∅,
    fun e => min (Sd.2 e) (pickS T Sd.1 Sd.2 (RinS T Sd.1 Sd.2 (dfsS T Sd.1 T.root)
      (pickT T Sd.1 Sd.2 (dfsS T Sd.1 T.root)))))

noncomputable def lev : ℕ → Finset (Fin n) × (Fin n → ℝ)
  | 0 => (T.edges, d0 T)
  | j + 1 => adv T (lev j)

theorem walkFn_eq (S : Finset (Fin n)) (d : Fin n → ℝ) :
    walkFn T S d = Gstep T S d (walkFn T
      (patchS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root)))
      (fun e => min (d e) (pickS T S d (RinS T S d (dfsS T S T.root)
        (pickT T S d (dfsS T S T.root)))))) := by
  rw [walkFn]
  unfold Gstep recP
  split_ifs <;> simp_all
  rename_i h3
  split_ifs with h1 h2 <;> simp_all
  omega

theorem Gstep_indep (S : Finset (Fin n)) (d : Fin n → ℝ) (h : ¬ recP T S d)
    (W1 W2 : List (Fin n)) : Gstep T S d W1 = Gstep T S d W2 := by
  unfold Gstep
  simp only [if_neg h]

theorem walkFn_lev (j : ℕ) :
    walkFn T (lev T j).1 (lev T j).2 = Gstep T (lev T j).1 (lev T j).2
      (walkFn T (lev T (j + 1)).1 (lev T (j + 1)).2) := by
  rw [walkFn_eq]
  show Gstep T _ _ _ = Gstep T _ _ (walkFn T (adv T (lev T j)).1 (adv T (lev T j)).2)
  unfold adv
  by_cases h : recP T (lev T j).1 (lev T j).2
  · simp only [if_pos h]
  · exact Gstep_indep T _ _ h _ _

theorem patchS_sub (S : Finset (Fin n)) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) :
    patchS T S d L t ⊆ S := fun e he =>
  (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1

theorem lev_sub (j : ℕ) : (lev T j).1 ⊆ T.edges := by
  induction j with
  | zero => exact le_refl _
  | succ j ih =>
    show (adv T (lev T j)).1 ⊆ T.edges
    unfold adv
    split_ifs
    · exact (patchS_sub T _ _ _ _).trans ih
    · exact Finset.empty_subset _

theorem lev_card (j : ℕ) : (lev T j).1.card + j ≤ n - 1 ∨ (lev T j).1 = ∅ := by
  induction j with
  | zero =>
    left
    show T.edges.card + 0 ≤ n - 1
    rw [edges_card]; omega
  | succ j ih =>
    show (adv T (lev T j)).1.card + (j + 1) ≤ n - 1 ∨ (adv T (lev T j)).1 = ∅
    unfold adv
    split_ifs with h
    · left
      rcases ih with ih | ih
      · have := h.2.2.2
        dsimp only
        omega
      · exact absurd ih h.1
    · right; rfl

theorem lev_last (hn : 0 < n) : (lev T (n - 1)).1 = ∅ := by
  rcases lev_card T (n - 1) with h | h
  · exact Finset.card_eq_zero.mp (by omega)
  · exact h

/-! ## The level program -/
/-- `411 := [f ∈ S ∧ d e ≠ d f]` (`f` in `407`, `d e` in `406`). -/
def badIn : Stmt :=
  .seq (ldAt 413 200 407) (.seq (ldAt 414 201 407) (.seq (eqT 415 406 414)
    (.seq (notF 415 415) (.mul 411 413 415))))

/-- `412 := [e ∈ S] #{f ∈ S : d e ≠ d f}` (`e` in `404`). -/
def badOut : Stmt :=
  .seq (ldAt 405 200 404) (.seq (ldAt 406 201 404) (.seq (sumLoop 407 1 408 409 410 411 badIn)
    (.mul 412 405 410)))

def SBI : List ℕ := [100, 101, 102, 109, 411, 413, 414, 415]

def SBO : List ℕ := [100, 101, 102, 109, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415]

/-- `210 := |S|`, `211 := #{(e, f) ∈ S × S : d e ≠ d f}`. -/
def cardBad : Stmt :=
  .seq (sumLoop 400 1 401 402 210 403 (ldAt 403 200 400))
    (sumLoop 404 1 416 417 211 412 badOut)

def SCBd : List ℕ := SBO ++ [210, 211, 400, 401, 402, 403, 404, 416, 417]

noncomputable def badCount (S : Finset (Fin n)) (d : Fin n → ℝ) : ℝ :=
  ∑ e, ∑ f, (if e ∈ S ∧ f ∈ S ∧ d e ≠ d f then (1 : ℝ) else 0)

theorem badCount_nonneg (S : Finset (Fin n)) (d : Fin n → ℝ) : 0 ≤ badCount S d :=
  Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun f _ => by split_ifs <;> norm_num

theorem badCount_eq_zero (S : Finset (Fin n)) (d : Fin n → ℝ) :
    badCount S d = 0 ↔ ∀ e ∈ S, ∀ f ∈ S, d e = d f := by
  unfold badCount
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun e _ => Finset.sum_nonneg fun f _ => by
    split_ifs <;> norm_num)]
  constructor
  · intro h e he f hf
    have h1 := h e (Finset.mem_univ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun f _ => by split_ifs <;> norm_num)] at h1
    have h2 := h1 f (Finset.mem_univ _)
    by_contra hne
    rw [if_pos ⟨he, hf, hne⟩] at h2
    norm_num at h2
  · intro h e _
    refine Finset.sum_eq_zero fun f _ => ?_
    rw [if_neg]
    rintro ⟨he, hf, hne⟩
    exact hne (h e he f hf)

theorem cost_cb (n : ℕ) : n * (100 * (n + 1) + 6) + 4 + (n * (n * (100 * (n + 1) + 6) + 4 +
    4 * ((3 + 2 * 0) * (n + 1) + n) + 7 + (4 * ((3 + 2 * 1) * (n + 1) + n) + 7) + 1 + 6) + 4) ≤
    400 * (n + 1) ^ 3 := by ring_nf; nlinarith [Nat.zero_le (n * n), Nat.zero_le (n * n * n)]

theorem h_cardBad (σ : Cfg) (hl : Lay T σ) (S : Finset (Fin n)) (d : Fin n → ℝ)
    (hS : VOK σ.mem (rb n 0) (ind S)) (hd : VOK σ.mem (rb n 1) d) :
    Runs cardBad σ (fun k σ' => k ≤ 400 * (n + 1) ^ 3 ∧ σ'.mem = σ.mem ∧ Fr SCBd σ σ' ∧
      σ'.regs 210 = (S.card : ℝ) ∧ σ'.regs 211 = badCount S d) := by
  refine r_seq (r_mono (h_sumLoop 400 1 401 402 210 403 (ldAt 403 200 400) [100, 101, 109, 403]
    [100, 101, 109, 403, 400, 401, 402, 210] (by unfold LoopOK; decide) n (100 * (n + 1))
    (fun m => if h : m < n then ind S ⟨m, h⟩ else 0) σ hl.h1 ?_)
    fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  · intro m hm σ' hm' hf' hV'
    have hl' := hl.fr T hf' (by unfold LayRegs; decide)
    refine r_mono (h_ldAt σ' 403 200 400 _ _ hl'.b0 hV') fun k σ'' ⟨h1, h2, h3, h4⟩ =>
      ⟨by unfold rb at h1; omega, h2, h3, ?_⟩
    rw [h4, hm']
    have := hS ⟨m, hm⟩
    simp only at this
    rw [this]; simp [hm]
  have hl1 := hl.fr T hf1 (by unfold LayRegs; decide)
  refine r_mono (h_sumLoop 404 1 416 417 211 412 badOut SBO (SBO ++ [404, 416, 417, 211])
    (by unfold LoopOK SBO; decide) n (n * (100 * (n + 1) + 6) + 4 + 4 * ((3 + 2 * 0) * (n + 1) + n)
      + 7 + (4 * ((3 + 2 * 1) * (n + 1) + n) + 7) + 1)
    (fun m => if h : m < n then ind S ⟨m, h⟩ * ∑ f, (if f ∈ S ∧ d ⟨m, h⟩ ≠ d f then 1 else 0)
      else 0) σ1 hl1.h1 ?_) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
    ⟨?_, by rw [hm2, hm1], ?_, ?_, ?_⟩
  · intro m hm σ' hm' hf' hV'
    have hl' := hl1.fr T hf' (by unfold LayRegs SBO; decide)
    have hM : σ'.mem = σ.mem := by rw [hm', hm1]
    refine r_seq (r_mono (h_ldAt σ' 405 200 404 _ _ hl'.b0 hV') fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
    refine r_seq (r_mono (h_ldAt σ3 406 201 404 (rb n 1) m (by rw [hf3 201 (by decide), hl'.b1])
      (by rw [hf3 404 (by decide), hV'])) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
    have hl4 := hl'.fr T (Fr.trm hf3 hf4 (by simp) (by simp) : Fr [100, 101, 109, 405, 406] σ' σ4)
      (by unfold LayRegs; decide)
    have hM4 : σ4.mem = σ.mem := by rw [hm4, hm3, hM]
    have e406 : σ4.regs 406 = d ⟨m, hm⟩ := by
      rw [hv4, hm3, hM]; have := hd ⟨m, hm⟩; simpa using this
    refine r_seq (r_mono (h_sumLoop 407 1 408 409 410 411 badIn SBI (SBI ++ [407, 408, 409, 410])
      (by unfold LoopOK SBI; decide) n (100 * (n + 1))
      (fun j => if h : j < n then (if (⟨j, h⟩ : Fin n) ∈ S ∧ d ⟨m, hm⟩ ≠ d ⟨j, h⟩ then 1 else 0)
        else 0) σ4 hl4.h1 ?_) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
    · intro j hj σ'' hm'' hf'' hV''
      have hl'' := hl4.fr T hf'' (by unfold LayRegs SBI; decide)
      have hM'' : σ''.mem = σ.mem := by rw [hm'', hM4]
      have he406 : σ''.regs 406 = d ⟨m, hm⟩ := by rw [hf'' 406 (by decide), e406]
      refine r_seq (r_mono (h_ldAt σ'' 413 200 407 _ _ hl''.b0 hV'')
        fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)
      refine r_seq (r_mono (h_ldAt σ6 414 201 407 (rb n 1) j
        (by rw [hf6 201 (by decide), hl''.b1]) (by rw [hf6 407 (by decide), hV'']))
        fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ => ?_)
      refine r_seq (r_mono (h_eqT σ7 415 406 414 (by decide) (by decide) (by decide))
        fun k8 σ8 ⟨hk8, hm8, hf8, hv8⟩ => ?_)
      refine r_seq (r_mono (h_notF σ8 415 415 (by decide)) fun k9 σ9 ⟨hk9, hm9, hf9, hv9⟩ => ?_)
      refine r_mono (h_mul σ9 411 413 415) fun k10 σ10 ⟨hk10, hm10, hf10, hv10⟩ =>
        ⟨?_, by rw [hm10, hm9, hm8, hm7, hm6], ?_, ?_⟩
      · unfold rb at hk6 hk7; omega
      · exact Fr.tr (hf6.mono (by decide)) (Fr.tr (hf7.mono (by decide)) (Fr.tr (hf8.mono
          (by decide)) (Fr.tr (hf9.mono (by decide)) (hf10.mono (by decide)))))
      · rw [hv10, hf9 413 (by decide), hf8 413 (by decide), hf7 413 (by decide), hv6, hv9, hv8,
          hf7 406 (by decide), hf6 406 (by decide), he406, hv7, hm6, hM'']
        have h1 := hS ⟨j, hj⟩
        have h2 := hd ⟨j, hj⟩
        simp only at h1 h2
        rw [h1, h2]
        unfold ind
        by_cases c1 : (⟨j, hj⟩ : Fin n) ∈ S <;> by_cases c2 : d ⟨m, hm⟩ = d ⟨j, hj⟩ <;>
          simp [c1, c2, hj]
    refine r_mono (h_mul σ5 412 405 410) fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ =>
      ⟨?_, by rw [hm6, hm5, hm4, hm3], ?_, ?_⟩
    · unfold rb at hk3 hk4; omega
    · exact Fr.tr (hf3.mono (by unfold SBO; decide)) (Fr.tr (hf4.mono (by unfold SBO; decide))
        (Fr.tr (hf5.mono (by unfold SBO SBI; decide)) (hf6.mono (by unfold SBO; decide))))
    · rw [hv6, hf5 405 (by unfold SBI; decide), hf4 405 (by decide), hv3, hv5, hm',
        hm1, sum_fin_range (fun f => if f ∈ S ∧ d ⟨m, hm⟩ ≠ d f then (1 : ℝ) else 0)]
      have := hS ⟨m, hm⟩
      simp only at this
      rw [this]; simp [hm]
  · have := cost_cb n
    omega
  · exact Fr.trm hf1 hf2 (by unfold SCBd SBO; decide) (by unfold SCBd SBO; decide)
  · rw [hf2 210 (by unfold SBO; decide), hv1, sum_fin_range (fun v => ind S v)]
    unfold ind
    rw [Finset.sum_boole]
    simp
  · rw [hv2, sum_fin_range (fun e => ind S e * ∑ f, (if f ∈ S ∧ d e ≠ d f then (1 : ℝ) else 0))]
    unfold badCount ind
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : e ∈ S
    · simp only [he, if_true, one_mul, true_and]
    · simp only [he, if_false, zero_mul, false_and]
      simp

theorem cost_dfs0 (n : ℕ) : dfsCost n (rb n 0) (rb n 2) ≤ 200 * (n + 1) ^ 3 := by
  unfold dfsCost rb; ring_nf; nlinarith [Nat.zero_le (n * n), Nat.zero_le (n * n * n)]

theorem cost_x (n len : ℕ) (h : len ≤ 2 * n) :
    n * (xbCost n (rb n 2) len + 4 * (rb n 3 + n) + 13) + 3 ≤ 1000 * (n + 1) ^ 3 := by
  have h1 : xbCost n (rb n 2) len ≤ xbCost n (rb n 2) (2 * n) := by unfold xbCost; gcongr
  calc _ ≤ n * (xbCost n (rb n 2) (2 * n) + 4 * (rb n 3 + n) + 13) + 3 := by gcongr
    _ ≤ 1000 * (n + 1) ^ 3 := by
      unfold xbCost rb; ring_nf; nlinarith [Nat.zero_le (n * n), Nat.zero_le (n * n * n)]

theorem flag4 (a b c e : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable e] :
    (if a then (1 : ℝ) else 0) * (1 - if b then 1 else 0) * (if c then 1 else 0) *
      (if e then 1 else 0) = if a ∧ ¬ b ∧ c ∧ e then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases he : e <;> simp [*]

/-- `217 := [recP]`. -/
def recFlag : Stmt :=
  .seq (.const 418 0) (.seq (ltF 419 418 210) (.seq (eqT 420 211 418) (.seq (notF 420 420)
  (.seq (ltF 421 418 214) (.seq (ltF 422 214 210) (.seq (.mul 217 419 420)
  (.seq (.mul 217 217 421) (.mul 217 217 422))))))))

/-- All the data of a level. -/
def levelProg : Stmt :=
  .seq cardBad (.seq (mov 110 200) (.seq (mov 111 202) (.seq (mov 112 2) (.seq dfsProg
  (.seq (mov 212 135) (.seq xPhase (.seq tPhase (.seq redPhase (.seq patchPhase (.seq pSums
  (.seq sPhase recFlag)))))))))))

def SLev : List ℕ := List.range' 100 100 ++ List.range' 207 13 ++ List.range' 221 286

theorem mem_SLev (r : ℕ) :
    r ∈ SLev ↔ (100 ≤ r ∧ r < 200) ∨ (207 ≤ r ∧ r < 220) ∨ (221 ≤ r ∧ r < 507) := by
  unfold SLev
  simp only [List.mem_append, List.mem_range'_1]
  omega

theorem toSLev {S : List ℕ}
    (h : ∀ r ∈ S, (100 ≤ r ∧ r < 200) ∨ (207 ≤ r ∧ r < 220) ∨ (221 ≤ r ∧ r < 507)) :
    S ⊆ SLev :=
  fun r hr => (mem_SLev r).mpr (h r hr)

/-- The outcome of `levelProg` for the level `(S, d)`. -/
structure LevOK (S : Finset (Fin n)) (d : Fin n → ℝ) (σ : Cfg) : Prop where
  lay : Lay T σ
  fl : VOK σ.mem (rb n 0) (ind S)
  dd : VOK σ.mem (rb n 1) d
  par : ParOK T σ.mem
  cS : σ.regs 210 = (S.card : ℝ)
  bad : σ.regs 211 = badCount S d
  lenL : σ.regs 212 = ((dfsS T S T.root).length : ℝ)
  LL : LOK T σ.mem (rb n 2) (dfsS T S T.root)
  red : VOK σ.mem (rb n 4)
    (ind (redS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root))))
  pat : VOK σ.mem (rb n 5)
    (ind (patchS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root))))
  ss : σ.regs 216 = pickS T S d (RinS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root)))
  rc : σ.regs 217 = if recP T S d then 1 else 0

theorem cost_lev (n : ℕ) : 400 * (n + 1) ^ 3 + 6 + 200 * (n + 1) ^ 3 + 2 + 1000 * (n + 1) ^ 3 +
    1000 * (n + 1) ^ 3 + 400 * (n + 1) ^ 2 + 500 * (n + 1) ^ 3 + 300 * (n + 1) ^ 2 +
    1000 * (n + 1) ^ 3 + 30 ≤ 5000 * (n + 1) ^ 3 := by
  ring_nf; nlinarith [Nat.zero_le (n * n), Nat.zero_le (n * n * n)]

theorem h_levelProg (σ : Cfg) (hl : Lay T σ) (S : Finset (Fin n)) (d : Fin n → ℝ)
    (hS : VOK σ.mem (rb n 0) (ind S)) (hd : VOK σ.mem (rb n 1) d) (hP : ParOK T σ.mem) :
    Runs levelProg σ (fun k σ' => k ≤ 5000 * (n + 1) ^ 3 ∧ Fr SLev σ σ' ∧
      (∀ z : ℤ, ¬ (((rb n 2 : ℕ) : ℤ) ≤ z ∧ z < rb n 6) → σ'.mem z = σ.mem z) ∧
      LevOK T S d σ') := by
  have hn : 0 < n := Fin.pos T.root
  have hLb : (dfsS T S T.root).length ≤ 2 * n - 1 := dfsS_length T S T.root
  set L := dfsS T S T.root with hLdef
  -- reads below `rb n 2` survive
  have keep2 : ∀ M : ℤ → ℝ, (∀ z : ℤ, z < ((rb n 2 : ℕ) : ℤ) → M z = σ.mem z) →
      VOK M (rb n 0) (ind S) ∧ VOK M (rb n 1) d ∧ ParOK T M := by
    intro M hM
    refine ⟨fun v => ?_, fun v => ?_, fun w => ?_⟩
    · rw [hM _ (by have := v.isLt; unfold rb; push_cast; omega)]; exact hS v
    · rw [hM _ (by have := v.isLt; unfold rb; push_cast; omega)]; exact hd v
    · have := w.isLt
      rw [hM _ (by unfold rb; push_cast; omega), hM _ (by unfold rb; push_cast; omega)]
      exact hP w
  -- cardBad
  refine r_seq (r_mono (h_cardBad T σ hl S d hS hd) fun k1 σ1 ⟨hk1, hm1, hf1, h210, h211⟩ => ?_)
  have hl1 := hl.fr T hf1 (by unfold LayRegs SCBd SBO; decide)
  refine r_seq (r_mono (h_mov σ1 110 200 (by decide)) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_mov σ2 111 202 (by decide)) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  refine r_seq (r_mono (h_mov σ3 112 2 (by decide)) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
  have hf14 : Fr [110, 111, 112] σ1 σ4 := Fr.tr (hf2.mono (by decide)) (Fr.tr (hf3.mono
    (by decide)) (hf4.mono (by decide)))
  have hl4 := hl1.fr T hf14 (by unfold LayRegs; decide)
  have hM4 : σ4.mem = σ.mem := by rw [hm4, hm3, hm2, hm1]
  -- the search
  refine r_seq (r_mono (h_dfs T S T.root σ4 (rb n 0) (rb n 2) hl4.h1 hl4.h2
    (by rw [hf4 110 (by decide), hf3 110 (by decide), hv2, hl1.b0])
    (by rw [hf4 111 (by decide), hv3, hf2 202 (by decide), hl1.b2])
    (by rw [hv4, hf3 2 (by decide), hf2 2 (by decide), hl1.h2])
    (fun w => by rw [hM4]; exact hS w) (fun w => by rw [hM4]; exact (hP w).1)
    (by unfold rb; omega) (by unfold rb; omega))
    fun k5 σ5 ⟨hk5, hf5, h135, hL5, hm5⟩ => ?_)
  rw [← hLdef] at h135 hL5 hm5
  have hl5 := hl4.fr T hf5 (by unfold LayRegs SD; decide)
  refine r_seq (r_mono (h_mov σ5 212 135 (by decide)) fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)
  have hl6 := hl5.fr T hf6 (by unfold LayRegs; decide)
  have hm06 : ∀ z : ℤ, ¬ (((rb n 2 : ℕ) : ℤ) ≤ z ∧ z < rb n 3) → σ6.mem z = σ.mem z := by
    intro z hz
    rw [hm6, hm5 z (by unfold rb at hz ⊢; push_cast at hz ⊢; omega), hM4]
  obtain ⟨hS6, hd6, hP6⟩ := keep2 σ6.mem (fun z hz => hm06 z (by omega))
  have hLok6 : LOK T σ6.mem (rb n 2) L := fun j hj => by rw [hm6]; exact hL5 j hj
  -- x
  refine r_seq (r_mono (h_xPhase T σ6 L (rb n 2) (rb n 3) hl6.h1 hl6.h2 hl6.b2 hl6.b3
    (by rw [hv6, h135]) hLok6 hP6 (by unfold rb; omega) (by unfold rb; omega))
    fun k7 σ7 ⟨hk7, hf7, hm7, hx7⟩ => ?_)
  have hl7 := hl6.fr T hf7 (by unfold LayRegs SXP; decide)
  have hm07 : ∀ z : ℤ, ¬ (((rb n 2 : ℕ) : ℤ) ≤ z ∧ z < rb n 4) → σ7.mem z = σ.mem z := by
    intro z hz
    rw [hm7 z (by unfold rb at hz ⊢; push_cast at hz ⊢; omega), hm06 z (by
      unfold rb at hz ⊢; push_cast at hz ⊢; omega)]
  obtain ⟨hS7, hd7, hP7⟩ := keep2 σ7.mem (fun z hz => hm07 z (by omega))
  have hLok7 : LOK T σ7.mem (rb n 2) L := fun j hj => by
    rw [hm7 _ (by unfold rb; push_cast; omega)]; exact hLok6 j hj
  -- t
  refine r_seq (r_mono (h_tPhase T σ7 hl7 S d L hS7 hd7 hx7 hP7)
    fun k8 σ8 ⟨hk8, hm8, hf8, h213⟩ => ?_)
  have hl8 := hl7.fr T hf8 (by unfold LayRegs STP SCF SCB; decide)
  set t := pickT T S d L with ht
  -- red
  refine r_seq (r_mono (h_redPhase T σ8 hl8 S d L t h213 (by rw [hm8]; exact hS7)
    (by rw [hm8]; exact hd7) (by rw [hm8]; exact hx7)) fun k9 σ9 ⟨hk9, hf9, hm9, hR9⟩ => ?_)
  have hl9 := hl8.fr T hf9 (by unfold LayRegs SRP SRB; decide)
  have hm09 : ∀ z : ℤ, ¬ (((rb n 2 : ℕ) : ℤ) ≤ z ∧ z < rb n 5) → σ9.mem z = σ.mem z := by
    intro z hz
    rw [hm9 z (by unfold rb at hz ⊢; push_cast at hz ⊢; omega), hm8, hm07 z (by
      unfold rb at hz ⊢; push_cast at hz ⊢; omega)]
  obtain ⟨hS9, hd9, hP9⟩ := keep2 σ9.mem (fun z hz => hm09 z (by omega))
  -- patch
  refine r_seq (r_mono (h_patchPhase T σ9 hl9 S d L t hR9 hP9)
    fun k10 σ10 ⟨hk10, hf10, hm10, hPa10⟩ => ?_)
  have hl10 := hl9.fr T hf10 (by unfold LayRegs SPP SPB; decide)
  have hm010 : ∀ z : ℤ, ¬ (((rb n 2 : ℕ) : ℤ) ≤ z ∧ z < rb n 6) → σ10.mem z = σ.mem z := by
    intro z hz
    rw [hm10 z (by unfold rb at hz ⊢; push_cast at hz ⊢; omega), hm09 z (by
      unfold rb at hz ⊢; push_cast at hz ⊢; omega)]
  obtain ⟨hS10, hd10, hP10⟩ := keep2 σ10.mem (fun z hz => hm010 z (by omega))
  set P := patchS T S d L t with hPdef
  -- sums over the patch
  refine r_seq (r_mono (h_pSums T σ10 hl10 P hPa10 hP10)
    fun k11 σ11 ⟨hk11, hm11, hf11, h214, h215⟩ => ?_)
  have hl11 := hl10.fr T hf11 (by unfold LayRegs SPS; decide)
  -- s
  refine r_seq (r_mono (h_sPhase T σ11 hl11 S d L (RinS T S d L t) (by rw [h215]; rfl)
    (by rw [hm11]; exact hS10) (by rw [hm11]; exact hd10) (by
      rw [hm11]; intro v; rw [hm10 _ (by have := v.isLt; unfold rb; push_cast; omega),
        hm9 _ (by have := v.isLt; unfold rb; push_cast; omega), hm8]; exact hx7 v)
    (by rw [hm11]; exact hP10)) fun k12 σ12 ⟨hk12, hm12, hf12, h216⟩ => ?_)
  have hl12 := hl11.fr T hf12 (by unfold LayRegs SSP SMX SBB SRF SAB; decide)
  -- the flag
  refine r_seq (r_mono (h_const σ12 418 0) fun k13 σ13 ⟨hk13, hm13, hf13, hv13⟩ => ?_)
  refine r_seq (r_mono (h_ltF σ13 419 418 210) fun k14 σ14 ⟨hk14, hm14, hf14', hv14⟩ => ?_)
  refine r_seq (r_mono (h_eqT σ14 420 211 418 (by decide) (by decide) (by decide))
    fun k15 σ15 ⟨hk15, hm15, hf15, hv15⟩ => ?_)
  refine r_seq (r_mono (h_notF σ15 420 420 (by decide)) fun k16 σ16 ⟨hk16, hm16, hf16, hv16⟩ => ?_)
  refine r_seq (r_mono (h_ltF σ16 421 418 214) fun k17 σ17 ⟨hk17, hm17, hf17, hv17⟩ => ?_)
  refine r_seq (r_mono (h_ltF σ17 422 214 210) fun k18 σ18 ⟨hk18, hm18, hf18, hv18⟩ => ?_)
  refine r_seq (r_mono (h_mul σ18 217 419 420) fun k19 σ19 ⟨hk19, hm19, hf19, hv19⟩ => ?_)
  refine r_seq (r_mono (h_mul σ19 217 217 421) fun k20 σ20 ⟨hk20, hm20, hf20, hv20⟩ => ?_)
  refine r_mono (h_mul σ20 217 217 422) fun k21 σ21 ⟨hk21, hm21, hf21, hv21⟩ =>
    ⟨?_, ?_, ?_, ?_⟩
  · have c1 := cost_lev n
    have c2 := cost_dfs0 n
    have c3 := cost_x n L.length (by omega)
    clear * - c1 c2 c3 hk1 hk2 hk3 hk4 hk5 hk6 hk7 hk8 hk9 hk10 hk11 hk12 hk13 hk14 hk15 hk16
      hk17 hk18 hk19 hk20 hk21
    linarith
  · have hf1221 : Fr [100, 102, 217, 418, 419, 420, 421, 422] σ12 σ21 := Fr.tr (hf13.mono
      (by decide)) (Fr.tr (hf14'.mono (by decide)) (Fr.tr (hf15.mono (by decide)) (Fr.tr
      (hf16.mono (by decide)) (Fr.tr (hf17.mono (by decide)) (Fr.tr (hf18.mono (by decide))
      (Fr.tr (hf19.mono (by decide)) (Fr.tr (hf20.mono (by decide))
      (hf21.mono (by decide)))))))))
    exact Fr.tr (hf1.mono (toSLev (by unfold SCBd SBO; decide))) (Fr.tr (hf14.mono
      (toSLev (by decide))) (Fr.tr (hf5.mono (toSLev (by unfold SD; decide)))
      (Fr.tr (hf6.mono (toSLev (by decide))) (Fr.tr (hf7.mono (toSLev (by unfold SXP; decide)))
      (Fr.tr (hf8.mono (toSLev (by unfold STP SCF SCB; decide)))
      (Fr.tr (hf9.mono (toSLev (by unfold SRP SRB; decide)))
      (Fr.tr (hf10.mono (toSLev (by unfold SPP SPB; decide)))
      (Fr.tr (hf11.mono (toSLev (by unfold SPS; decide)))
      (Fr.tr (hf12.mono (toSLev (by unfold SSP SMX SBB SRF SAB; decide)))
      (hf1221.mono (toSLev (by decide))))))))))))
  · intro z hz
    rw [hm21, hm20, hm19, hm18, hm17, hm16, hm15, hm14, hm13, hm12, hm11]
    exact hm010 z hz
  · have hM21 : σ21.mem = σ10.mem := by
      rw [hm21, hm20, hm19, hm18, hm17, hm16, hm15, hm14, hm13, hm12, hm11]
    have hf1221 : Fr [100, 102, 217, 418, 419, 420, 421, 422] σ12 σ21 := Fr.tr (hf13.mono
      (by decide)) (Fr.tr (hf14'.mono (by decide)) (Fr.tr (hf15.mono (by decide)) (Fr.tr
      (hf16.mono (by decide)) (Fr.tr (hf17.mono (by decide)) (Fr.tr (hf18.mono (by decide))
      (Fr.tr (hf19.mono (by decide)) (Fr.tr (hf20.mono (by decide))
      (hf21.mono (by decide)))))))))
    -- registers 210 … 216 survive the later phases
    have c210 : σ12.regs 210 = (S.card : ℝ) := by
      rw [hf12 210 (by unfold SSP SMX SBB SRF SAB; decide),
        hf11 210 (by unfold SPS; decide), hf10 210 (by unfold SPP SPB; decide),
        hf9 210 (by unfold SRP SRB; decide), hf8 210 (by unfold STP SCF SCB; decide),
        hf7 210 (by unfold SXP; decide), hf6 210 (by decide), hf5 210 (by unfold SD; decide),
        hf14 210 (by decide), h210]
    have c211 : σ12.regs 211 = badCount S d := by
      rw [hf12 211 (by unfold SSP SMX SBB SRF SAB; decide),
        hf11 211 (by unfold SPS; decide), hf10 211 (by unfold SPP SPB; decide),
        hf9 211 (by unfold SRP SRB; decide), hf8 211 (by unfold STP SCF SCB; decide),
        hf7 211 (by unfold SXP; decide), hf6 211 (by decide), hf5 211 (by unfold SD; decide),
        hf14 211 (by decide), h211]
    have g212 : σ21.regs 212 = (L.length : ℝ) := by
      rw [hf1221 212 (by decide), hf12 212 (by unfold SSP SMX SBB SRF SAB; decide),
        hf11 212 (by unfold SPS; decide), hf10 212 (by unfold SPP SPB; decide),
        hf9 212 (by unfold SRP SRB; decide), hf8 212 (by unfold STP SCF SCB; decide),
        hf7 212 (by unfold SXP; decide), hv6, h135]
    have c214 : σ12.regs 214 = (P.card : ℝ) := by
      rw [hf12 214 (by unfold SSP SMX SBB SRF SAB; decide), h214]
    have g216 : σ21.regs 216 = pickS T S d (RinS T S d L t) := by
      rw [hf1221 216 (by decide), h216]
    refine ⟨hl12.fr T hf1221 (by unfold LayRegs; decide), by rw [hM21]; exact hS10,
      by rw [hM21]; exact hd10, by rw [hM21]; exact hP10,
      by rw [hf1221 210 (by decide), c210], by rw [hf1221 211 (by decide), c211], g212, ?_, ?_,
      ?_, g216, ?_⟩
    · intro j hj
      rw [← hLdef] at hj
      rw [hM21, hm10 _ (by unfold rb; push_cast; omega), hm9 _ (by unfold rb; push_cast; omega),
        hm8]
      exact hLok7 j hj
    · intro v
      rw [hM21, hm10 _ (by have := v.isLt; unfold rb; push_cast; omega)]
      exact hR9 v
    · rw [hM21]; exact hPa10
    · -- the recursion flag
      have v419 : σ18.regs 419 = if 0 < (S.card : ℝ) then 1 else 0 := by
        rw [hf18 419 (by decide), hf17 419 (by decide), hf16 419 (by decide),
          hf15 419 (by decide), hv14, hv13, hf13 210 (by decide), c210]
        simp
      have v420 : σ18.regs 420 = 1 - if badCount S d = 0 then 1 else 0 := by
        rw [hf18 420 (by decide), hf17 420 (by decide), hv16, hv15, hf14' 211 (by decide),
          hf13 211 (by decide), c211, hf14' 418 (by decide), hv13]
        simp
      have v421 : σ18.regs 421 = if 0 < (P.card : ℝ) then 1 else 0 := by
        rw [hf18 421 (by decide), hv17, hf16 214 (by decide), hf15 214 (by decide),
          hf14' 214 (by decide), hf13 214 (by decide), c214, hf16 418 (by decide),
          hf15 418 (by decide), hf14' 418 (by decide), hv13]
        simp
      have v422 : σ18.regs 422 = if (P.card : ℝ) < (S.card : ℝ) then 1 else 0 := by
        rw [hv18, hf17 214 (by decide), hf16 214 (by decide), hf15 214 (by decide),
          hf14' 214 (by decide), hf13 214 (by decide), c214, hf17 210 (by decide),
          hf16 210 (by decide), hf15 210 (by decide), hf14' 210 (by decide),
          hf13 210 (by decide), c210]
      rw [hv21, hv20, hv19, hf20 422 (by decide), hf19 422 (by decide), hf19 421 (by decide),
        v419, v420, v421, v422]
      have e1 : (0 < (S.card : ℝ)) ↔ S ≠ ∅ := by
        rw [Nat.cast_pos, Finset.card_pos, Finset.nonempty_iff_ne_empty]
      have e3 : (0 < (P.card : ℝ)) ↔ P ≠ ∅ := by
        rw [Nat.cast_pos, Finset.card_pos, Finset.nonempty_iff_ne_empty]
      have e4 : ((P.card : ℝ) < (S.card : ℝ)) ↔ P.card < S.card := Nat.cast_lt
      have e2 := badCount_eq_zero S d
      simp only [e1, e2, e3, e4]
      rw [flag4]
      unfold recP
      rw [← hLdef, ← ht, ← hPdef]
      by_cases hX : S ≠ ∅ ∧ ¬(∀ e ∈ S, ∀ f ∈ S, d e = d f) ∧ P ≠ ∅ ∧ P.card < S.card
      · rw [if_pos hX, if_pos hX]
      · rw [if_neg hX, if_neg hX]

/-! ## The step to the next level -/
def advFlag : Stmt := .seq (ldAt 435 205 430) (.mul 434 217 435)

def advD : Stmt := .seq (ldAt 435 201 430) (mnS 434 435 216)

def advProg : Stmt :=
  .seq (fillLoop 430 1 431 432 200 433 434 advFlag) (fillLoop 430 1 431 432 201 433 434 advD)

def SAF : List ℕ := [100, 101, 102, 109, 434, 435]

def SAdv : List ℕ := SAF ++ [430, 431, 432, 433]

theorem cost_adv (n : ℕ) : n * (100 * (n + 1) + 4 * ((3 + 2 * 0) * (n + 1) + n) + 13) + 3 +
    (n * (100 * (n + 1) + 4 * ((3 + 2 * 1) * (n + 1) + n) + 13) + 3) ≤ 300 * (n + 1) ^ 2 := by
  ring_nf; nlinarith [Nat.zero_le (n * n)]

theorem h_advProg (σ : Cfg) (S : Finset (Fin n)) (d : Fin n → ℝ) (h : LevOK T S d σ) :
    Runs advProg σ (fun k σ' => k ≤ 300 * (n + 1) ^ 2 ∧ Fr SAdv σ σ' ∧
      (∀ z : ℤ, ¬ (((rb n 0 : ℕ) : ℤ) ≤ z ∧ z < rb n 2) → σ'.mem z = σ.mem z) ∧
      VOK σ'.mem (rb n 0) (ind (adv T (S, d)).1) ∧ VOK σ'.mem (rb n 1) (adv T (S, d)).2) := by
  have hl := h.lay
  refine r_seq (r_mono (h_fillLoop 430 1 431 432 200 433 434 advFlag SAF SAdv
    (by unfold FillOK SAF SAdv; decide) n (100 * (n + 1)) (rb n 0)
    (fun m => if hm : m < n then ind (adv T (S, d)).1 ⟨m, hm⟩ else 0) σ hl.h1 hl.b0 ?_)
    fun k1 σ1 ⟨hk1, hf1, hm1, hv1⟩ => ?_)
  · intro m hm σ' hm' hf' hV'
    have hl' := hl.fr T hf' (by unfold LayRegs SAdv SAF; decide)
    refine r_seq (r_mono (h_ldAt σ' 435 205 430 _ _ hl'.b5 hV') fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
      r_mono (h_mul σ2 434 217 435) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ =>
      ⟨?_, by rw [hm3, hm2], Fr.trm hf2 hf3 (by decide) (by decide), ?_⟩)
    · unfold rb at hk2; omega
    · rw [hv3, hf2 217 (by decide), hf' 217 (by unfold SAdv SAF; decide), h.rc, hv2,
        hm' _ (by unfold rb; push_cast; omega)]
      have := h.pat ⟨m, hm⟩
      simp only at this
      rw [this]
      simp only [hm, dif_pos]
      unfold adv ind
      dsimp only
      by_cases c : recP T S d
      · simp [c]
      · simp [c]
  have hl1 := hl.fr T hf1 (by unfold LayRegs SAdv SAF; decide)
  refine r_mono (h_fillLoop 430 1 431 432 201 433 434 advD SAF SAdv
    (by unfold FillOK SAF SAdv; decide) n (100 * (n + 1)) (rb n 1)
    (fun m => if hm : m < n then (adv T (S, d)).2 ⟨m, hm⟩ else 0) σ1 hl1.h1 hl1.b1 ?_)
    fun k2 σ2 ⟨hk2, hf2, hm2, hv2⟩ => ⟨?_, Fr.tr hf1 hf2, ?_, ?_, ?_⟩
  · intro m hm σ' hm' hf' hV'
    have hl' := hl1.fr T hf' (by unfold LayRegs SAdv SAF; decide)
    refine r_seq (r_mono (h_ldAt σ' 435 201 430 _ _ hl'.b1 hV') fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ =>
      r_mono (h_mnS σ3 434 435 216 (by decide) (by decide) (by decide) (by decide))
      fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ =>
      ⟨?_, by rw [hm4, hm3], Fr.trm hf3 hf4 (by decide) (by decide), ?_⟩)
    · unfold rb at hk3; omega
    · rw [hv4, hv3, hf3 216 (by decide), hf' 216 (by unfold SAdv SAF; decide),
        hf1 216 (by unfold SAdv SAF; decide), h.ss, hm' _ (by push_cast; omega),
        hm1 _ (by unfold rb; push_cast; omega)]
      have := h.dd ⟨m, hm⟩
      simp only at this
      rw [this]
      simp [hm, adv]
  · have := cost_adv n
    unfold rb at hk1 hk2; omega
  · intro z hz
    rw [hm2 z (by unfold rb at hz ⊢; push_cast at hz ⊢; omega),
      hm1 z (by unfold rb at hz ⊢; push_cast at hz ⊢; omega)]
  · intro v
    rw [hm2 _ (by have := v.isLt; unfold rb; push_cast; omega), hv1 v.val v.isLt]
    simp
  · intro v
    rw [hv2 v.val v.isLt]
    simp

/-!
Part PR, file 9: the output buffer (cell `-2 - i` holds entry `i`, the length in register `220`),
appending, the path up to the root, and the truncation `trunc`.
-/
/-- The buffer holds `B`. -/
def BufOK (M : ℤ → ℝ) (B : List (Fin n)) : Prop :=
  ∀ i < B.length, M (-2 - (i : ℤ)) = (T.vertexAt B i).val

theorem bufOK_append (M : ℤ → ℝ) (B X : List (Fin n)) (hB : BufOK T M B)
    (hX : ∀ j < X.length, M (-2 - ((B.length + j : ℕ) : ℤ)) = (T.vertexAt X j).val) :
    BufOK T M (B ++ X) := by
  intro i hi
  rw [List.length_append] at hi
  by_cases h : i < B.length
  · rw [PartA.vA_append_left T B X i h]; exact hB i h
  · obtain ⟨j, rfl⟩ : ∃ j, i = B.length + j := ⟨i - B.length, by omega⟩
    rw [PartA.vA_append_right]
    exact hX j (by omega)

/-- Append the vertex in register `s`. -/
def push (s : ℕ) : Stmt := .seq (stO 220 s) (.seq (.const 227 1) (.add 220 220 227))

theorem h_push (σ : Cfg) (s : ℕ) (hs : s ∉ [100, 101, 220, 227]) (B : List (Fin n)) (v : Fin n)
    (hv : σ.regs s = v.val) (h220 : σ.regs 220 = B.length) (hB : BufOK T σ.mem B) :
    Runs (push s) σ (fun k σ' => k ≤ 4 * B.length + 10 ∧ Fr [100, 101, 220, 227] σ σ' ∧
      BufOK T σ'.mem (B ++ [v]) ∧ σ'.regs 220 = ((B ++ [v]).length : ℝ) ∧
      ∀ z : ℤ, z ≠ -2 - (B.length : ℤ) → σ'.mem z = σ.mem z) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
  refine r_seq (r_mono (h_stO σ 220 s (by decide) hs.1 hs.2.1 B.length h220)
    fun k1 σ1 ⟨hk1, hm1, hf1⟩ => ?_)
  refine r_seq (r_mono (h_const σ1 227 1) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
    r_mono (h_add σ2 220 220 227) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ⟨by omega, ?_, ?_, ?_, ?_⟩)
  · exact Fr.tr (hf1.mono (by decide)) (Fr.tr (hf2.mono (by decide)) (hf3.mono (by decide)))
  · rw [hm3, hm2, hm1]
    refine bufOK_append T _ B [v] (fun i hi => ?_) (fun j hj => ?_)
    · rw [update_of_ne (by omega)]; exact hB i hi
    · simp at hj; subst hj
      simp [Tree.vertexAt, hv]
  · rw [hv3, hf2 220 (by decide), hf1 220 (by decide), h220, hv2]; simp
  · intro z hz
    rw [hm3, hm2, hm1, update_of_ne hz]

/-- Append the array at base `regs Bs` of length `regs Ln`. -/
def appendArr (Bs Ln : ℕ) : Stmt :=
  .seq (forLoop 222 Ln 223 224 (.seq (ldAt 225 Bs 222) (.seq (.add 226 220 222) (stO 226 225))))
    (.add 220 220 Ln)

def SAL : List ℕ := [100, 101, 109, 222, 223, 224, 225, 226]

def SAA : List ℕ := [100, 101, 109, 220, 222, 223, 224, 225, 226]

theorem h_appendArr (σ : Cfg) (Bs Ln : ℕ) (hBs : Bs ∉ SAA) (hLn : Ln ∉ SAA) (hBL : Bs ≠ Ln)
    (B X : List (Fin n)) (b : ℕ) (hb : σ.regs Bs = b) (hl : σ.regs Ln = X.length)
    (h220 : σ.regs 220 = B.length) (hB : BufOK T σ.mem B) (hX : LOK T σ.mem b X) :
    Runs (appendArr Bs Ln) σ (fun k σ' =>
      k ≤ X.length * (4 * (b + X.length) + 4 * (B.length + X.length) + 30) + 5 ∧
      Fr SAA σ σ' ∧ BufOK T σ'.mem (B ++ X) ∧ σ'.regs 220 = ((B ++ X).length : ℝ) ∧
      ∀ z : ℤ, (-2 - (B.length : ℤ) < z ∨ z < -2 - ((B.length + X.length : ℕ) : ℤ) ∨ 0 ≤ z) →
        σ'.mem z = σ.mem z) := by
  unfold SAA at hBs hLn
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hBs hLn
  let I : ℕ → Cfg → Prop := fun m σ' => Fr SAL σ σ' ∧
    (∀ z : ℤ, (-2 - (B.length : ℤ) < z ∨ z < -2 - ((B.length + m : ℕ) : ℤ) + 1 ∨ 0 ≤ z) →
      σ'.mem z = σ.mem z) ∧
    BufOK T σ'.mem (B ++ X.take m)
  refine r_seq (r_for 222 Ln 223 224 _ (by omega) (by decide) (by decide) (by omega) (by omega)
    (by decide) X.length (4 * (b + X.length) + 4 * (B.length + X.length) + 20) I σ hl ?_ ?_ _
    (fun k1 σ1 hk1 hI => ?_))
  · intro a e
    refine ⟨fun r hr => ?_, fun z _ => rfl, by simpa using hB⟩
    unfold SAL at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [update_apply, hr]
  · intro m hm σ' ⟨hf', hm', hB'⟩ hV hN
    have hb' : σ'.regs Bs = b := by rw [hf' Bs (by unfold SAL; simp; omega), hb]
    have h220' : σ'.regs 220 = B.length := by rw [hf' 220 (by unfold SAL; decide), h220]
    refine r_seq (r_mono (h_ldAt σ' 225 Bs 222 b m hb' hV) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
    refine r_seq (r_mono (h_add σ2 226 220 222) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
    have e226 : σ3.regs 226 = ((B.length + m : ℕ) : ℝ) := by
      rw [hv3, hf2 220 (by decide), hf2 222 (by decide), h220', hV]; push_cast; ring
    refine r_mono (h_stO σ3 226 225 (by decide) (by decide) (by decide) (B.length + m) e226)
      fun k4 σ4 ⟨hk4, hm4, hf4⟩ => ⟨?_, ?_, ?_, fun a e f => ⟨?_, ?_, ?_⟩⟩
    · have : m ≤ X.length := hm.le
      omega
    · rw [hf4 222 (by decide), hf3 222 (by decide), hf2 222 (by decide), hV]
    · rw [hf4 Ln (by simp; omega), hf3 Ln (by simp; omega), hf2 Ln (by simp; omega), hN]
    · intro r hr
      have h1 : r ≠ 223 := fun h => hr (by unfold SAL; simp [h])
      have h2 : r ≠ 222 := fun h => hr (by unfold SAL; simp [h])
      have h3 : r ≠ 224 := fun h => hr (by unfold SAL; simp [h])
      simp only [update_apply, h1, h2, h3, if_false]
      rw [hf4 r (fun h => hr (by unfold SAL; simp at h ⊢; omega)),
        hf3 r (fun h => hr (by unfold SAL; simp at h ⊢; omega)),
        hf2 r (fun h => hr (by unfold SAL; simp at h ⊢; omega))]
      exact hf' r hr
    · intro z hz
      show σ4.mem z = σ.mem z
      rw [hm4, update_of_ne (by push_cast at hz ⊢; omega), hm3, hm2]
      exact hm' z (by push_cast at hz ⊢; omega)
    · show BufOK T σ4.mem (B ++ X.take (m + 1))
      rw [hm4, hm3, hm2]
      have hXm : X.take (m + 1) = X.take m ++ [T.vertexAt X m] := by
        rw [List.take_add_one]
        congr 1
        simp [Tree.vertexAt, List.getD_eq_getElem?_getD, hm]
      rw [hXm, ← List.append_assoc]
      refine bufOK_append T _ _ _ (fun i hi => ?_) (fun j hj => ?_)
      · rw [update_of_ne]
        · exact hB' i hi
        · simp only [List.length_append, List.length_take] at hi
          push_cast; omega
      · simp at hj; subst hj
        simp only [List.length_append, List.length_take, min_eq_left hm.le]
        push_cast
        simp only [add_zero]
        rw [update_self, hf3 225 (by decide), hv2, hm', hX m hm]
        · simp [Tree.vertexAt]
        · right; right; push_cast; omega
  · have hc := Nat.mul_le_mul_left X.length (show 4 * (b + X.length) + 4 * (B.length + X.length)
      + 20 + 5 ≤ 4 * (b + X.length) + 4 * (B.length + X.length) + 30 by omega)
    refine r_mono (h_add σ1 220 220 Ln) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ =>
      ⟨by omega, ?_, ?_, ?_, ?_⟩
    · exact Fr.tr (hI.1.mono (by unfold SAL SAA; decide)) (hf2.mono (by unfold SAA; decide))
    · rw [hm2]; have := hI.2.2; rwa [List.take_of_length_le le_rfl] at this
    · rw [hv2, hI.1 220 (by unfold SAL; decide), hI.1 Ln (by unfold SAL; simp; omega), h220, hl]
      simp
    · intro z hz
      rw [hm2]
      exact hI.2.1 z (by push_cast at hz ⊢; omega)

theorem getLast_eq_vA (M : List (Fin n)) (hM : M ≠ []) :
    M.getLast?.getD T.root = T.vertexAt M (M.length - 1) := by
  rw [List.getLast?_eq_getLast hM, Option.getD_some, List.getLast_eq_getElem]
  simp [Tree.vertexAt, List.getD_eq_getElem?_getD, List.length_pos_of_ne_nil hM]

theorem upPath_tail (v : Fin n) :
    (upPath T v).tail = (List.range (T.depth v)).map (fun i => T.parent^[i + 1] v) := by
  unfold upPath
  rw [List.range_succ_eq_map]
  simp [List.map_map, Function.comp_def]

/-! ### The path up to the root -/
def upBody : Stmt :=
  .seq (ldIn 476 2 473) (.seq (mov 473 476) (.seq (push 473) (.seq (eqT 474 473 2)
    (notF 475 474))))

def upPhase : Stmt :=
  .seq (.const 471 1) (.seq (.sub 472 220 471) (.seq (ldO 473 472) (.seq (eqT 474 473 2)
    (.seq (notF 475 474) (.whilegt 475 upBody)))))

def SUP : List ℕ := [100, 101, 102, 220, 227, 471, 472, 473, 474, 475, 476]

theorem h_upPhase (σ : Cfg) (hl : Lay T σ) (hP : ParOK T σ.mem) (M : List (Fin n))
    (hM : M ≠ []) (h220 : σ.regs 220 = M.length) (hB : BufOK T σ.mem M) :
    Runs upPhase σ (fun k σ' => k ≤ (n + 1) * (4 * M.length + 16 * n + 70) ∧ Fr SUP σ σ' ∧
      BufOK T σ'.mem (M ++ (upPath T (M.getLast?.getD T.root)).tail) ∧
      σ'.regs 220 = ((M ++ (upPath T (M.getLast?.getD T.root)).tail).length : ℝ) ∧
      ∀ z : ℤ, (-2 - (M.length : ℤ) < z ∨ 0 ≤ z) → σ'.mem z = σ.mem z) := by
  have hlen : 0 < M.length := List.length_pos_of_ne_nil hM
  rw [getLast_eq_vA T M hM, upPath_tail]
  set v := T.vertexAt M (M.length - 1) with hv
  refine r_seq (r_mono (h_const σ 471 1) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_sub σ1 472 220 471) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  have e472 : σ2.regs 472 = ((M.length - 1 : ℕ) : ℝ) := by
    rw [hv2, hf1 220 (by decide), h220, hv1]; push_cast [Nat.cast_sub hlen]; ring
  refine r_seq (r_mono (h_ldO σ2 473 472 (by decide) _ e472) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  have e473 : σ3.regs 473 = v.val := by
    rw [hv3, hm2, hm1]
    have := hB (M.length - 1) (by omega)
    push_cast [Nat.cast_sub hlen] at this ⊢
    rw [← this]
  refine r_seq (r_mono (h_eqT σ3 474 473 2 (by decide) (by decide) (by decide))
    fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
  refine r_seq (r_mono (h_notF σ4 475 474 (by decide)) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
  have hf05 : Fr SUP σ σ5 := Fr.tr (hf1.mono (by decide)) (Fr.tr (hf2.mono (by decide))
    (Fr.tr (hf3.mono (by decide)) (Fr.tr (hf4.mono (by decide)) (hf5.mono (by decide)))))
  have hM5 : σ5.mem = σ.mem := by rw [hm5, hm4, hm3, hm2, hm1]
  let f := fun i => T.parent^[i + 1] v
  let I : ℕ → Cfg → Prop := fun j σ' => Fr SUP σ σ' ∧
    (∀ z : ℤ, (-2 - (M.length : ℤ) < z ∨ 0 ≤ z) → σ'.mem z = σ.mem z) ∧
    σ'.regs 473 = (T.parent^[j] v).val ∧
    BufOK T σ'.mem (M ++ (List.range j).map f) ∧ σ'.regs 220 = ((M.length + j : ℕ) : ℝ) ∧
    σ'.regs 475 = (if T.parent^[j] v = T.root then 0 else 1)
  refine r_while 475 upBody (T.depth v) (4 * M.length + 16 * n + 60) I _ ?_ ?_ σ5 ?_ ?_
  · intro j hj σ' ⟨hf', hm', h473, hB', h220', h475⟩
    have hne := iter_ne_root' T v j hj
    refine ⟨by rw [h475, if_neg hne]; norm_num, ?_⟩
    set a := T.parent^[j] v with ha
    have hav := a.isLt
    have hl' := hl.fr T hf' (by unfold LayRegs SUP; decide)
    refine r_seq (r_mono (h_ldIn σ' 476 2 473 (by decide) a.val h473)
      fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)
    have e476 : σ6.regs 476 = (T.parent a).val := by
      rw [hv6, hm' _ (by right; positivity), (hP a).1]
    refine r_seq (r_mono (h_mov σ6 473 476 (by decide)) fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ => ?_)
    have hdj := PartB.depth_lt T v
    refine r_seq (r_mono (h_push T σ7 473 (by decide) (M ++ (List.range j).map f) (T.parent a)
      (by rw [hv7, e476]) (by rw [hf7 220 (by decide), hf6 220 (by decide), h220']; simp)
      (by rw [hm7, hm6]; exact hB')) fun k8 σ8 ⟨hk8, hf8, hB8, h2208, hm8⟩ => ?_)
    refine r_seq (r_mono (h_eqT σ8 474 473 2 (by decide) (by decide) (by decide))
      fun k9 σ9 ⟨hk9, hm9, hf9, hv9⟩ => ?_)
    refine r_mono (h_notF σ9 475 474 (by decide)) fun k10 σ10 ⟨hk10, hm10, hf10, hv10⟩ =>
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, List.length_range] at hk8
      have := a.isLt
      omega
    · exact Fr.tr hf' (Fr.tr (hf6.mono (by decide)) (Fr.tr (hf7.mono (by decide)) (Fr.tr
        (hf8.mono (by decide)) (Fr.tr (hf9.mono (by decide)) (hf10.mono (by decide))))))
    · intro z hz
      rw [hm10, hm9, hm8 z (by simp; omega), hm7, hm6]
      exact hm' z hz
    · rw [hf10 473 (by decide), hf9 473 (by decide), hf8 473 (by decide), hv7, e476,
        Function.iterate_succ_apply']
    · rw [hm10, hm9, List.range_succ, List.map_append, ← List.append_assoc]
      simpa [f, Function.iterate_succ_apply'] using hB8
    · rw [hf10 220 (by decide), hf9 220 (by decide), h2208]; simp
    · rw [hv10, hv9, hf8 473 (by decide), hv7, e476, hf8 2 (by decide), hf7 2 (by decide),
        hf6 2 (by decide), hl'.h2, Function.iterate_succ_apply']
      by_cases c : T.parent a = T.root
      · rw [if_pos (by rw [c]), if_pos c]; norm_num
      · rw [if_neg (fun h => c ((cval_eq _ _).mp h)), if_neg c]; norm_num
  · intro σ' ⟨_, _, _, _, _, h475⟩
    rw [h475, PartB.iter_depth, if_pos rfl]
  · refine ⟨hf05, fun z _ => by rw [hM5], ?_, ?_, ?_, ?_⟩
    · rw [hf5 473 (by decide), hf4 473 (by decide), e473]; rfl
    · rw [hM5]; simpa using hB
    · rw [hf5 220 (by decide), hf4 220 (by decide), hf3 220 (by decide), hf2 220 (by decide),
        hf1 220 (by decide), h220]; simp
    · rw [hv5, hv4, e473, hf3 2 (by decide), hf2 2 (by decide), hf1 2 (by decide), hl.h2]
      rw [Function.iterate_zero_apply]
      by_cases c : v = T.root
      · rw [if_pos (by rw [c]), if_pos c]; norm_num
      · rw [if_neg (fun h => c ((cval_eq _ _).mp h)), if_neg c]; norm_num
  · intro k σ' hk ⟨hf', hm', _, hB', h220', _⟩
    refine ⟨?_, hf', hB', ?_, hm'⟩
    · have hdv := PartB.depth_lt T v
      have : T.depth v * (4 * M.length + 16 * n + 60 + 2) ≤ n * (4 * M.length + 16 * n + 62) :=
        Nat.mul_le_mul hdv.le (by omega)
      have h2 : (n + 1) * (4 * M.length + 16 * n + 70) = n * (4 * M.length + 16 * n + 62) +
          8 * n + 4 * M.length + 16 * n + 70 := by ring
      omega
    · rw [h220']; simp

/-! ### Truncation -/
theorem fmax_sup (P : Finset (Fin n)) (f : Fin n → ℕ) :
    fmax (fun m => ∃ h : m < n, (⟨m, h⟩ : Fin n) ∈ P)
      (fun m => if h : m < n then (f ⟨m, h⟩ : ℝ) else 0) n = ((P.sup f : ℕ) : ℝ) := by
  rw [fmax_eq]
  apply le_antisymm
  · refine Finset.max'_le _ _ _ fun y hy => ?_
    rw [Finset.mem_insert, Finset.mem_image] at hy
    rcases hy with rfl | ⟨m, hm, rfl⟩
    · positivity
    · simp only [Finset.mem_filter] at hm
      obtain ⟨-, h, hP⟩ := hm
      simp only [h, dif_pos]
      exact_mod_cast Finset.le_sup (f := f) hP
  · by_cases hne : P.Nonempty
    · obtain ⟨e, he, hsup⟩ := Finset.exists_mem_eq_sup P hne f
      rw [hsup]
      refine Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨e.val, by simp [e.isLt, he], by simp⟩))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.sup_empty, bot_eq_zero', Nat.cast_zero]
      exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem ind_mul (A B : Prop) [Decidable A] [Decidable B] :
    (if A then (1 : ℝ) else 0) * (if B then 1 else 0) = if A ∧ B then 1 else 0 := by
  by_cases a : A <;> by_cases b : B <;> simp [a, b]

theorem ind_or (A B : Prop) [Decidable A] [Decidable B] :
    (if A then (1 : ℝ) else 0) + (if B then 1 else 0) - (if A then 1 else 0) * (if B then 1 else 0)
      = if A ∨ B then 1 else 0 := by
  by_cases a : A <;> by_cases b : B <;> simp [a, b]

theorem cross_final (a b c X : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable X]
    (hX : X ↔ ¬ a ∧ b ∧ c) :
    (if a then (0 : ℝ) else 1) * (if b then 1 else 0) * (if c then 1 else 0) =
      if X then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> simp [ha, hb, hc, hX]

/-- `450 := [CrossAt M e i]` (`e` in `440`, `i` in `446`). -/
def crossBody : Stmt :=
  .seq (eqT 453 440 2) (.seq (notF 453 453) (.seq (.const 454 1) (.seq (.add 455 446 454)
  (.seq (ltF 456 455 220) (.seq (ldO 457 446) (.seq (ldO 458 455) (.seq (ldIn 459 2 440)
  (.seq (eqT 460 457 459) (.seq (eqT 461 458 440) (.seq (.mul 462 460 461)
  (.seq (eqT 463 457 440) (.seq (eqT 464 458 459) (.seq (.mul 465 463 464)
  (.seq (.add 466 462 465) (.seq (.mul 467 462 465) (.seq (.sub 466 466 467)
  (.seq (.mul 450 453 456) (.mul 450 450 466))))))))))))))))))

def SCR : List ℕ := [100, 101, 102, 450, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463,
  464, 465, 466, 467]

theorem h_crossBody (σ : Cfg) (M : List (Fin n)) (e : Fin n) (i : ℕ) (hi : i < M.length)
    (h2 : σ.regs 2 = T.root.val) (h440 : σ.regs 440 = e.val) (h446 : σ.regs 446 = i)
    (h220 : σ.regs 220 = M.length) (hB : BufOK T σ.mem M) (hP : ParOK T σ.mem) :
    Runs crossBody σ (fun k σ' => k ≤ 8 * M.length + 12 * n + 120 ∧ σ'.mem = σ.mem ∧
      Fr SCR σ σ' ∧ σ'.regs 450 = if T.CrossAt M e i then 1 else 0) := by
  have he := e.isLt
  refine r_seq (r_mono (h_eqT σ 453 440 2 (by decide) (by decide) (by decide))
    fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_notF σ1 453 453 (by decide)) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_const σ2 454 1) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  refine r_seq (r_mono (h_add σ3 455 446 454) fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
  have e455 : σ4.regs 455 = ((i + 1 : ℕ) : ℝ) := by
    rw [hv4, hv3, hf3 446 (by decide), hf2 446 (by decide), hf1 446 (by decide), h446]
    push_cast; ring
  refine r_seq (r_mono (h_ltF σ4 456 455 220) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
  refine r_seq (r_mono (h_ldO σ5 457 446 (by decide) i (by
    rw [hf5 446 (by decide), hf4 446 (by decide), hf3 446 (by decide), hf2 446 (by decide),
      hf1 446 (by decide), h446])) fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)
  refine r_seq (r_mono (h_ldO σ6 458 455 (by decide) (i + 1) (by
    rw [hf6 455 (by decide), hf5 455 (by decide), e455])) fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ => ?_)
  refine r_seq (r_mono (h_ldIn σ7 459 2 440 (by decide) e.val (by
    rw [hf7 440 (by decide), hf6 440 (by decide), hf5 440 (by decide), hf4 440 (by decide),
      hf3 440 (by decide), hf2 440 (by decide), hf1 440 (by decide), h440]))
    fun k8 σ8 ⟨hk8, hm8, hf8, hv8⟩ => ?_)
  refine r_seq (r_mono (h_eqT σ8 460 457 459 (by decide) (by decide) (by decide))
    fun k9 σ9 ⟨hk9, hm9, hf9, hv9⟩ => ?_)
  refine r_seq (r_mono (h_eqT σ9 461 458 440 (by decide) (by decide) (by decide))
    fun k10 σ10 ⟨hk10, hm10, hf10, hv10⟩ => ?_)
  refine r_seq (r_mono (h_mul σ10 462 460 461) fun k11 σ11 ⟨hk11, hm11, hf11, hv11⟩ => ?_)
  refine r_seq (r_mono (h_eqT σ11 463 457 440 (by decide) (by decide) (by decide))
    fun k12 σ12 ⟨hk12, hm12, hf12, hv12⟩ => ?_)
  refine r_seq (r_mono (h_eqT σ12 464 458 459 (by decide) (by decide) (by decide))
    fun k13 σ13 ⟨hk13, hm13, hf13, hv13⟩ => ?_)
  refine r_seq (r_mono (h_mul σ13 465 463 464) fun k14 σ14 ⟨hk14, hm14, hf14, hv14⟩ => ?_)
  refine r_seq (r_mono (h_add σ14 466 462 465) fun k15 σ15 ⟨hk15, hm15, hf15, hv15⟩ => ?_)
  refine r_seq (r_mono (h_mul σ15 467 462 465) fun k16 σ16 ⟨hk16, hm16, hf16, hv16⟩ => ?_)
  refine r_seq (r_mono (h_sub σ16 466 466 467) fun k17 σ17 ⟨hk17, hm17, hf17, hv17⟩ => ?_)
  refine r_seq (r_mono (h_mul σ17 450 453 456) fun k18 σ18 ⟨hk18, hm18, hf18, hv18⟩ => ?_)
  refine r_mono (h_mul σ18 450 450 466) fun k19 σ19 ⟨hk19, hm19, hf19, hv19⟩ => ⟨?_, ?_, ?_, ?_⟩
  · have := e.isLt
    linarith
  · rw [hm19, hm18, hm17, hm16, hm15, hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4,
      hm3, hm2, hm1]
  · exact Fr.tr (hf1.mono (by decide)) (Fr.tr (hf2.mono (by decide)) (Fr.tr (hf3.mono
      (by decide)) (Fr.tr (hf4.mono (by decide)) (Fr.tr (hf5.mono (by decide)) (Fr.tr
      (hf6.mono (by decide)) (Fr.tr (hf7.mono (by decide)) (Fr.tr (hf8.mono (by decide))
      (Fr.tr (hf9.mono (by decide)) (Fr.tr (hf10.mono (by decide)) (Fr.tr (hf11.mono
      (by decide)) (Fr.tr (hf12.mono (by decide)) (Fr.tr (hf13.mono (by decide)) (Fr.tr
      (hf14.mono (by decide)) (Fr.tr (hf15.mono (by decide)) (Fr.tr (hf16.mono (by decide))
      (Fr.tr (hf17.mono (by decide)) (Fr.tr (hf18.mono (by decide))
      (hf19.mono (by decide)))))))))))))))))))
  · -- the values, as indicators
    have hM5 : σ5.mem = σ.mem := by rw [hm5, hm4, hm3, hm2, hm1]
    have hM7 : σ7.mem = σ.mem := by rw [hm7, hm6, hM5]
    have a453 : σ17.regs 453 = if e = T.root then 0 else 1 := by
      rw [hf17 453 (by decide), hf16 453 (by decide), hf15 453 (by decide), hf14 453 (by decide),
        hf13 453 (by decide), hf12 453 (by decide), hf11 453 (by decide), hf10 453 (by decide),
        hf9 453 (by decide), hf8 453 (by decide), hf7 453 (by decide), hf6 453 (by decide),
        hf5 453 (by decide), hf4 453 (by decide), hf3 453 (by decide), hv2, hv1, h440, h2]
      by_cases c : e = T.root
      · rw [if_pos (by rw [c]), if_pos c]; norm_num
      · rw [if_neg (fun h => c ((cval_eq _ _).mp h)), if_neg c]; norm_num
    have a456 : σ17.regs 456 = if i + 1 < M.length then 1 else 0 := by
      rw [hf17 456 (by decide), hf16 456 (by decide), hf15 456 (by decide), hf14 456 (by decide),
        hf13 456 (by decide), hf12 456 (by decide), hf11 456 (by decide), hf10 456 (by decide),
        hf9 456 (by decide), hf8 456 (by decide), hf7 456 (by decide), hf6 456 (by decide), hv5,
        e455, hf4 220 (by decide), hf3 220 (by decide), hf2 220 (by decide), hf1 220 (by decide),
        h220]
      simp only [Nat.cast_lt]
    rw [hv19, hv18, a453, a456, hf18 466 (by decide), hv17, hf16 466 (by decide), hv15, hv16,
      hf15 462 (by decide), hf15 465 (by decide)]
    by_cases hi1 : i + 1 < M.length
    · have r457 : σ8.regs 457 = (T.vertexAt M i).val := by
        rw [hf8 457 (by decide), hf7 457 (by decide), hv6, hM5]
        exact hB i hi
      have r458 : σ8.regs 458 = (T.vertexAt M (i + 1)).val := by
        rw [hf8 458 (by decide), hv7, hm6, hM5]
        have := hB (i + 1) hi1
        push_cast at this ⊢
        exact this
      have r459 : σ8.regs 459 = (T.parent e).val := by rw [hv8, hM7, (hP e).1]
      have r440 : σ8.regs 440 = e.val := by
        rw [hf8 440 (by decide), hf7 440 (by decide), hf6 440 (by decide), hf5 440 (by decide),
          hf4 440 (by decide), hf3 440 (by decide), hf2 440 (by decide), hf1 440 (by decide),
          h440]
      have d462 : σ14.regs 462 = if T.vertexAt M i = T.parent e ∧ T.vertexAt M (i + 1) = e
          then 1 else 0 := by
        rw [hf14 462 (by decide), hf13 462 (by decide), hf12 462 (by decide), hv11,
          hf10 460 (by decide), hv9, hv10, hf9 458 (by decide), hf9 440 (by decide), r457, r458,
          r459, r440]
        simp only [cval_eq]
        exact ind_mul _ _
      have d465 : σ14.regs 465 = if T.vertexAt M i = e ∧ T.vertexAt M (i + 1) = T.parent e
          then 1 else 0 := by
        rw [hv14, hf13 463 (by decide), hv12, hv13, hf12 458 (by decide), hf12 459 (by decide),
          hf11 457 (by decide), hf11 440 (by decide), hf11 458 (by decide), hf11 459 (by decide),
          hf10 457 (by decide), hf10 440 (by decide), hf10 458 (by decide), hf10 459 (by decide),
          hf9 457 (by decide), hf9 440 (by decide), hf9 458 (by decide), hf9 459 (by decide),
          r457, r458, r459, r440]
        simp only [cval_eq]
        exact ind_mul _ _
      rw [d462, d465, ind_or]
      refine cross_final _ _ _ _ ?_
      unfold Tree.CrossAt Tree.DownAt Tree.UpAt
      constructor
      · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
        · exact ⟨h1, h2, Or.inl ⟨h3, h4⟩⟩
        · exact ⟨h1, h2, Or.inr ⟨h3, h4⟩⟩
      · rintro ⟨h1, h2, (⟨h3, h4⟩ | ⟨h3, h4⟩)⟩
        · exact Or.inl ⟨h1, h2, h3, h4⟩
        · exact Or.inr ⟨h1, h2, h3, h4⟩
    · rw [if_neg hi1, mul_zero, zero_mul, if_neg (show ¬ T.CrossAt M e i from
        fun h => Or.elim h (fun h => hi1 h.2.1) (fun h => hi1 h.2.1))]

def SFI : List ℕ := SCR ++ [445, 446, 447, 448, 449, 451, 452]

def STB : List ℕ := [100, 101, 109, 444] ++ SFI

/-- `444 := [e ∈ P]`, `445 := firstIdx M e` (`e` in `440`). -/
def truncBody : Stmt :=
  .seq (ldAt 444 205 440) (findLoop 446 220 447 448 449 445 450 451 452 crossBody)

theorem firstIdx_eq (M : List (Fin n)) (e : Fin n) :
    firstIdx T M e = (ffind (T.CrossAt M e) M.length).getD 0 := rfl

theorem h_truncBody (σ : Cfg) (hl : Lay T σ) (P : Finset (Fin n)) (M : List (Fin n)) (e : Fin n)
    (h440 : σ.regs 440 = e.val) (h220 : σ.regs 220 = M.length) (hB : BufOK T σ.mem M)
    (hPv : VOK σ.mem (rb n 5) (ind P)) (hP : ParOK T σ.mem) :
    Runs truncBody σ (fun k σ' => k ≤ M.length * (8 * M.length + 12 * n + 135) + 60 * n + 70 ∧
      σ'.mem = σ.mem ∧ Fr STB σ σ' ∧ σ'.regs 444 = (if e ∈ P then 1 else 0) ∧
      σ'.regs 445 = (firstIdx T M e : ℝ)) := by
  have he := e.isLt
  refine r_seq (r_mono (h_ldAt σ 444 205 440 _ _ hl.b5 h440) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_mono (h_findLoop 446 220 447 448 449 445 450 451 452 crossBody SCR
    (SCR ++ [445, 446, 447, 448, 449, 451, 452]) (by unfold FindOK SCR; decide) M.length
    (8 * M.length + 12 * n + 120) (T.CrossAt M e) σ1 (by rw [hf1 220 (by decide), h220]) ?_)
    fun k2 σ2 ⟨hk2, hm2, hf2, hF2, hR2⟩ => ⟨?_, by rw [hm2, hm1], ?_, ?_, ?_⟩
  · intro m hm σ' hm' hf' hV'
    have hl' := hl.fr T (Fr.tr (hf1.mono (by decide)) (hf'.mono (by unfold SCR; decide)) :
      Fr ([100, 101, 109, 444] ++ SCR ++ [445, 446, 447, 448, 449, 451, 452]) σ σ')
      (by unfold LayRegs SCR; decide)
    refine h_crossBody T σ' M e m hm hl'.h2 (by rw [hf' 440 (by unfold SCR; decide),
      hf1 440 (by decide), h440]) hV' (by rw [hf' 220 (by unfold SCR; decide),
      hf1 220 (by decide), h220]) (by rw [hm', hm1]; exact hB) (by rw [hm', hm1]; exact hP)
  · have : M.length * (8 * M.length + 12 * n + 120 + 15) =
        M.length * (8 * M.length + 12 * n + 135) := by ring
    unfold rb at hk1
    omega
  · exact Fr.trm hf1 hf2 (by unfold STB SFI; decide) (by unfold STB SFI; decide)
  · rw [hf2 444 (by unfold SCR; decide), hv1, hPv e]; rfl
  · rw [hR2, firstIdx_eq]

def STR : List ℕ := STB ++ [102, 103, 440, 441, 442, 443, 468, 469, 470, 220]

def truncPhase : Stmt :=
  .seq (maxLoop 440 1 441 442 443 444 445 truncBody) (.seq (.const 468 2) (.seq (.add 469 443 468)
    (.seq (mnS 470 220 469) (mov 220 470))))

theorem bufOK_take (M : ℤ → ℝ) (B : List (Fin n)) (k : ℕ) (hB : BufOK T M B) :
    BufOK T M (B.take k) := by
  intro i hi
  rw [List.length_take] at hi
  rw [hB i (by omega)]
  simp [Tree.vertexAt, List.getD_eq_getElem?_getD, List.getElem?_take, show i < k by omega]

theorem h_truncPhase (σ : Cfg) (hl : Lay T σ) (P : Finset (Fin n)) (M : List (Fin n))
    (h220 : σ.regs 220 = M.length) (hB : BufOK T σ.mem M)
    (hPv : VOK σ.mem (rb n 5) (ind P)) (hP : ParOK T σ.mem) :
    Runs truncPhase σ (fun k σ' =>
      k ≤ (n + 1) * (M.length * (8 * M.length + 12 * n + 135) + 60 * n + 100) ∧
      σ'.mem = σ.mem ∧ Fr STR σ σ' ∧ BufOK T σ'.mem (trunc T P M) ∧
      σ'.regs 220 = ((trunc T P M).length : ℝ)) := by
  refine r_seq (r_mono (h_maxLoop 440 1 441 442 443 444 445 truncBody STB
    (STB ++ [440, 441, 442, 443, 103]) (by unfold MaxOK STB SFI SCR; decide) n
    (M.length * (8 * M.length + 12 * n + 135) + 60 * n + 70)
    (fun m => ∃ h : m < n, (⟨m, h⟩ : Fin n) ∈ P)
    (fun m => if h : m < n then (firstIdx T M ⟨m, h⟩ : ℝ) else 0) σ hl.h1 ?_)
    fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  · intro m hm σ' hm' hf' hV'
    have hl' := hl.fr T hf' (by unfold LayRegs STB SFI SCR; decide)
    refine r_mono (h_truncBody T σ' hl' P M ⟨m, hm⟩ hV'
      (by rw [hf' 220 (by unfold STB SFI SCR; decide), h220]) (by rw [hm']; exact hB)
      (by rw [hm']; exact hPv) (by rw [hm']; exact hP))
      fun k σ'' ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, ?_, fun _ => by rw [h5]; simp [hm]⟩
    rw [h4]
    by_cases c : (⟨m, hm⟩ : Fin n) ∈ P
    · rw [if_pos c, if_pos ⟨hm, c⟩]
    · rw [if_neg c, if_neg (fun ⟨_, h⟩ => c h)]
  rw [fmax_sup] at hv1
  refine r_seq (r_mono (h_const σ1 468 2) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_add σ2 469 443 468) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  refine r_seq (r_mono (h_mnS σ3 470 220 469 (by decide) (by decide) (by decide) (by decide))
    fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
  refine r_mono (h_mov σ4 220 470 (by decide)) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ =>
    ⟨?_, ?_, ?_, ?_, ?_⟩
  · generalize M.length * (8 * M.length + 12 * n + 135) + 60 * n + 70 = c at hk1 ⊢
    nlinarith
  · rw [hm5, hm4, hm3, hm2, hm1]
  · exact Fr.tr (hf1.mono (by unfold STR; simp)) (Fr.tr (hf2.mono (by unfold STR; simp))
      (Fr.tr (hf3.mono (by unfold STR; simp)) (Fr.tr (hf4.mono (by unfold STR; simp))
      (hf5.mono (by unfold STR; simp)))))
  · rw [hm5, hm4, hm3, hm2, hm1]
    exact bufOK_take T _ M _ hB
  · rw [hv5, hv4, hf3 220 (by decide), hf2 220 (by decide), hf1 220 (by unfold STB SFI SCR; decide),
      h220, hv3, hf2 443 (by decide), hv1, hv2]
    unfold trunc
    rw [List.length_take]
    push_cast
    rw [min_comm]

/-!
Part PR, file 10: the detour blocks appended to the buffer.
-/
theorem blocks_tail (L : List (Fin n)) (D : ℕ → List (Fin n)) (hL : L ≠ [])
    (hD : D 0 = [T.vertexAt L 0]) :
    (blocks L D).tail = ((List.range (L.length - 1)).map (fun i => D (i + 1))).flatten := by
  unfold blocks
  obtain ⟨m, hm⟩ : ∃ m, L.length = m + 1 :=
    ⟨L.length - 1, by have := List.length_pos_of_ne_nil hL; omega⟩
  rw [hm, List.range_succ_eq_map, List.map_cons, List.flatten_cons, hD, List.map_map]
  simp [Function.comp_def]

/-- The block at index `i` of `L` for the red set `R`. -/
noncomputable def blk (R : Finset (Fin n)) (L : List (Fin n)) (i : ℕ) : List (Fin n) :=
  if T.vertexAt L (i + 1) ∉ R ∧ T.vertexAt L (i + 1) ≠ T.root ∧
      T.vertexAt L i = T.parent (T.vertexAt L (i + 1))
  then dfsS T R (T.vertexAt L (i + 1)) else [T.vertexAt L (i + 1)]

theorem detS_succ (S : Finset (Fin n)) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) (i : ℕ)
    (hi : i + 1 < L.length) : detS T S d L t (i + 1) = blk T (redS T S d L t) L i := by
  unfold detS blk Tree.DownAt
  simp only [Nat.add_sub_cancel]
  by_cases c : T.vertexAt L (i + 1) ∉ redS T S d L t ∧ T.vertexAt L (i + 1) ≠ T.root ∧
      T.vertexAt L i = T.parent (T.vertexAt L (i + 1))
  · rw [if_pos c, if_pos ⟨Nat.succ_pos i, c.1, c.2.1, c.2.1, hi, c.2.2, trivial⟩]
  · rw [if_neg c, if_neg (fun h => c ⟨h.2.1, h.2.2.1, h.2.2.2.2.2.1⟩)]

theorem detS_zero (S : Finset (Fin n)) (d : Fin n → ℝ) (L : List (Fin n)) (t : ℝ) :
    detS T S d L t 0 = [T.vertexAt L 0] := by
  unfold detS
  rw [if_neg (fun h => lt_irrefl 0 h.1)]

/-- Append the block of index `i + 1` (`i` in `479`). -/
def detour : Stmt :=
  .seq (mov 110 204) (.seq (mov 111 206) (.seq (mov 112 484) (.seq dfsProg (appendArr 206 135))))

def blockBody : Stmt :=
  .seq (.const 483 1) (.seq (.add 482 479 483) (.seq (ldAt 484 202 482) (.seq (ldAt 485 204 484)
  (.seq (notF 486 485) (.seq (eqT 487 484 2) (.seq (notF 487 487) (.seq (ldAt 488 202 479)
  (.seq (ldIn 489 2 484) (.seq (eqT 490 488 489) (.seq (.mul 491 486 487) (.seq (.mul 491 491 490)
  (.ifle 491 (push 484) detour))))))))))))

def SBK : List ℕ := SD ++ SAA ++ [100, 101, 102, 109, 110, 111, 112, 220, 227, 482, 483, 484, 485,
  486, 487, 488, 489, 490, 491]

def cBlk (n Lm : ℕ) : ℕ := 2000 * (n + 1) ^ 3 + 10 * ((n + 1) * Lm)

theorem cost_det (n Lm x b : ℕ) (hx : x ≤ 2 * n) (hbx : b + x ≤ Lm) :
    16 * (11 * (n + 1)) + 100 + 2 + 6 + 1000 * (n + 1) ^ 3 +
      (x * (4 * (15 * (n + 1) + x) + 4 * (b + x) + 30) + 5) ≤
      2000 * (n + 1) ^ 3 + 10 * ((n + 1) * Lm) := by
  have h1 : x * (4 * (b + x)) ≤ (2 * n) * (4 * Lm) := Nat.mul_le_mul hx (by omega)
  have h2 : x * (4 * (15 * (n + 1) + x) + 30) ≤ (2 * n) * (4 * (15 * (n + 1) + 2 * n) + 30) :=
    Nat.mul_le_mul hx (by omega)
  have h3 : x * (4 * (15 * (n + 1) + x) + 4 * (b + x) + 30) =
      x * (4 * (15 * (n + 1) + x) + 30) + x * (4 * (b + x)) := by ring
  have h4 : (2 * n) * (4 * Lm) ≤ 10 * ((n + 1) * Lm) := by nlinarith
  have h5 : 16 * (11 * (n + 1)) + 100 + 2 + 6 + 1000 * (n + 1) ^ 3 +
      (2 * n) * (4 * (15 * (n + 1) + 2 * n) + 30) + 5 ≤ 2000 * (n + 1) ^ 3 := by
    ring_nf; nlinarith [Nat.zero_le (n * n), Nat.zero_le (n * n * n)]
  omega

theorem cost_push (n Lm b : ℕ) (hb : b ≤ Lm) :
    16 * (11 * (n + 1)) + 100 + 2 + (4 * b + 10) ≤ 2000 * (n + 1) ^ 3 + 10 * ((n + 1) * Lm) := by
  have h1 : b ≤ (n + 1) * Lm := le_trans hb (Nat.le_mul_of_pos_left _ (by omega))
  have h2 : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  omega

theorem cost_dfs4 (n : ℕ) : dfsCost n (rb n 4) (rb n 6) ≤ 1000 * (n + 1) ^ 3 := by
  unfold dfsCost rb; ring_nf; nlinarith [Nat.zero_le (n * n), Nat.zero_le (n * n * n)]

theorem h_blockBody (σ : Cfg) (hl : Lay T σ) (hP : ParOK T σ.mem) (R : Finset (Fin n))
    (L : List (Fin n)) (hLR : VOK σ.mem (rb n 4) (ind R)) (hL : LOK T σ.mem (rb n 2) L)
    (hLlen : L.length ≤ 2 * n) (i : ℕ) (hi : i + 1 < L.length) (h479 : σ.regs 479 = i)
    (B : List (Fin n)) (h220 : σ.regs 220 = B.length) (hB : BufOK T σ.mem B) (Lm : ℕ)
    (hLm : (B ++ blk T R L i).length ≤ Lm) :
    Runs blockBody σ (fun k σ' => k ≤ cBlk n Lm ∧ Fr SBK σ σ' ∧
      BufOK T σ'.mem (B ++ blk T R L i) ∧ σ'.regs 220 = ((B ++ blk T R L i).length : ℝ) ∧
      ∀ z : ℤ, ((0 ≤ z ∧ z < rb n 6) ∨ (-2 - (B.length : ℤ) < z ∧ z < 0)) →
        σ'.mem z = σ.mem z) := by
  set u := T.vertexAt L (i + 1) with hu
  set w := T.vertexAt L i with hw
  have hun := u.isLt
  refine r_seq (r_mono (h_const σ 483 1) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_add σ1 482 479 483) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  have e482 : σ2.regs 482 = ((i + 1 : ℕ) : ℝ) := by
    rw [hv2, hv1, hf1 479 (by decide), h479]; push_cast; ring
  refine r_seq (r_mono (h_ldAt σ2 484 202 482 (rb n 2) (i + 1)
    (by rw [hf2 202 (by decide), hf1 202 (by decide), hl.b2]) e482)
    fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  have hM2 : σ2.mem = σ.mem := by rw [hm2, hm1]
  have e484 : σ3.regs 484 = u.val := by rw [hv3, hM2, hL (i + 1) hi]
  refine r_seq (r_mono (h_ldAt σ3 485 204 484 (rb n 4) u.val
    (by rw [hf3 204 (by decide), hf2 204 (by decide), hf1 204 (by decide), hl.b4]) e484)
    fun k4 σ4 ⟨hk4, hm4, hf4, hv4⟩ => ?_)
  refine r_seq (r_mono (h_notF σ4 486 485 (by decide)) fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => ?_)
  refine r_seq (r_mono (h_eqT σ5 487 484 2 (by decide) (by decide) (by decide))
    fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ?_)
  refine r_seq (r_mono (h_notF σ6 487 487 (by decide)) fun k7 σ7 ⟨hk7, hm7, hf7, hv7⟩ => ?_)
  refine r_seq (r_mono (h_ldAt σ7 488 202 479 (rb n 2) i
    (by rw [hf7 202 (by decide), hf6 202 (by decide), hf5 202 (by decide), hf4 202 (by decide),
      hf3 202 (by decide), hf2 202 (by decide), hf1 202 (by decide), hl.b2])
    (by rw [hf7 479 (by decide), hf6 479 (by decide), hf5 479 (by decide), hf4 479 (by decide),
      hf3 479 (by decide), hf2 479 (by decide), hf1 479 (by decide), h479]))
    fun k8 σ8 ⟨hk8, hm8, hf8, hv8⟩ => ?_)
  have e484' : σ8.regs 484 = u.val := by
    rw [hf8 484 (by decide), hf7 484 (by decide), hf6 484 (by decide), hf5 484 (by decide),
      hf4 484 (by decide), e484]
  refine r_seq (r_mono (h_ldIn σ8 489 2 484 (by decide) u.val e484')
    fun k9 σ9 ⟨hk9, hm9, hf9, hv9⟩ => ?_)
  refine r_seq (r_mono (h_eqT σ9 490 488 489 (by decide) (by decide) (by decide))
    fun k10 σ10 ⟨hk10, hm10, hf10, hv10⟩ => ?_)
  refine r_seq (r_mono (h_mul σ10 491 486 487) fun k11 σ11 ⟨hk11, hm11, hf11, hv11⟩ => ?_)
  refine r_seq (r_mono (h_mul σ11 491 491 490) fun k12 σ12 ⟨hk12, hm12, hf12, hv12⟩ => ?_)
  have hM12 : σ12.mem = σ.mem := by
    rw [hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hM2]
  have hf012 : Fr [100, 101, 102, 109, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491] σ σ12 :=
    Fr.tr (hf1.mono (by decide)) (Fr.tr (hf2.mono (by decide)) (Fr.tr (hf3.mono (by decide))
    (Fr.tr (hf4.mono (by decide)) (Fr.tr (hf5.mono (by decide)) (Fr.tr (hf6.mono (by decide))
    (Fr.tr (hf7.mono (by decide)) (Fr.tr (hf8.mono (by decide)) (Fr.tr (hf9.mono (by decide))
    (Fr.tr (hf10.mono (by decide)) (Fr.tr (hf11.mono (by decide))
    (hf12.mono (by decide))))))))))))
  have hl12 := hl.fr T hf012 (by unfold LayRegs; decide)
  have e484'' : σ12.regs 484 = u.val := by
    rw [hf12 484 (by decide), hf11 484 (by decide), hf10 484 (by decide), hf9 484 (by decide),
      e484']
  have k12le : k1 + (k2 + (k3 + (k4 + (k5 + (k6 + (k7 + (k8 + (k9 + (k10 + (k11 + k12))))))))))
      ≤ 16 * rb n 4 + 100 := by
    unfold rb at hk3 hk4 hk8 ⊢
    have := hi; omega
  -- the flag of the condition
  have hflag : σ12.regs 491 = if u ∉ R ∧ u ≠ T.root ∧ w = T.parent u then 1 else 0 := by
    have a486 : σ10.regs 486 = if u ∉ R then 1 else 0 := by
      rw [hf10 486 (by decide), hf9 486 (by decide), hf8 486 (by decide),
        hf7 486 (by decide), hf6 486 (by decide), hv5, hv4, hm3, hM2, hLR u]
      unfold ind; split_ifs <;> norm_num
    have a487 : σ10.regs 487 = if u ≠ T.root then 1 else 0 := by
      rw [hf10 487 (by decide), hf9 487 (by decide), hf8 487 (by decide),
        hv7, hv6, hf5 484 (by decide), hf4 484 (by decide), e484, hf5 2 (by decide),
        hf4 2 (by decide), hf3 2 (by decide), hf2 2 (by decide), hf1 2 (by decide), hl.h2]
      by_cases c : u = T.root
      · rw [if_pos (by rw [c]), if_neg (not_not.mpr c)]; norm_num
      · rw [if_neg (fun h => c ((cval_eq _ _).mp h)), if_pos c]; norm_num
    have r488 : σ9.regs 488 = w.val := by
      rw [hf9 488 (by decide), hv8, hm7, hm6, hm5, hm4, hm3, hM2, hL i (by omega)]
    have r489 : σ9.regs 489 = (T.parent u).val := by
      rw [hv9, hm8, hm7, hm6, hm5, hm4, hm3, hM2, (hP u).1]
    have a490 : σ11.regs 490 = if w = T.parent u then 1 else 0 := by
      rw [hf11 490 (by decide), hv10, r488, r489]
      simp only [cval_eq]
    rw [hv12, hv11, a486, a487, a490]
    by_cases c1 : u ∉ R <;> by_cases c2 : u ≠ T.root <;> by_cases c3 : w = T.parent u <;>
      simp [c1, c2, c3]
  have hBlen : B.length ≤ Lm := by rw [List.length_append] at hLm; omega
  refine r_ifle (fun hle => ?_) (fun hgt => ?_)
  · -- a single vertex
    have hc : ¬ (u ∉ R ∧ u ≠ T.root ∧ w = T.parent u) := by
      intro c; rw [hflag, if_pos c] at hle; norm_num at hle
    have hblk : blk T R L i = [u] := by unfold blk; rw [← hu, ← hw, if_neg hc]
    rw [hblk]
    refine r_mono (h_push T σ12 484 (by decide) B u e484'' (by rw [hf012 220 (by decide), h220])
      (by rw [hM12]; exact hB)) fun k13 σ13 ⟨hk13, hf13, hB13, h22013, hm13⟩ =>
      ⟨?_, ?_, hB13, h22013, ?_⟩
    · unfold cBlk
      have h4 : rb n 4 = 11 * (n + 1) := by unfold rb; ring
      rw [h4] at k12le
      have := cost_push n Lm B.length hBlen
      omega
    · exact Fr.tr (hf012.mono (by unfold SBK SD SAA; decide)) (hf13.mono (by unfold SBK; decide))
    · intro z hz
      rw [hm13 z (by omega), hM12]
  · -- a detour
    have hc : u ∉ R ∧ u ≠ T.root ∧ w = T.parent u := by
      by_contra c; rw [hflag, if_neg c] at hgt; norm_num at hgt
    have hblk : blk T R L i = dfsS T R u := by unfold blk; rw [← hu, ← hw, if_pos hc]
    rw [hblk] at hLm ⊢
    refine r_seq (r_mono (h_mov σ12 110 204 (by decide)) fun k13 σ13 ⟨hk13, hm13, hf13, hv13⟩ => ?_)
    refine r_seq (r_mono (h_mov σ13 111 206 (by decide)) fun k14 σ14 ⟨hk14, hm14, hf14, hv14⟩ => ?_)
    refine r_seq (r_mono (h_mov σ14 112 484 (by decide)) fun k15 σ15 ⟨hk15, hm15, hf15, hv15⟩ => ?_)
    have hM15 : σ15.mem = σ.mem := by rw [hm15, hm14, hm13, hM12]
    have hf1215 : Fr [110, 111, 112] σ12 σ15 := Fr.tr (hf13.mono (by decide))
      (Fr.tr (hf14.mono (by decide)) (hf15.mono (by decide)))
    have hl15 := hl12.fr T hf1215 (by unfold LayRegs; decide)
    have hXlen := dfsS_length T R u
    refine r_seq (r_mono (h_dfs T R u σ15 (rb n 4) (rb n 6) hl15.h1 hl15.h2
      (by rw [hf15 110 (by decide), hf14 110 (by decide), hv13, hl12.b4])
      (by rw [hf15 111 (by decide), hv14, hf13 206 (by decide), hl12.b6])
      (by rw [hv15, hf14 484 (by decide), hf13 484 (by decide), e484''])
      (fun v => by rw [hM15]; exact hLR v) (fun v => by rw [hM15]; exact (hP v).1)
      (by unfold rb; omega) (by unfold rb; omega)) fun k16 σ16 ⟨hk16, hf16, h135, hX16, hm16⟩ => ?_)
    have hl16 := hl15.fr T hf16 (by unfold LayRegs SD; decide)
    have hB16 : BufOK T σ16.mem B := by
      intro j hj
      rw [hm16 _ (by unfold rb; push_cast; omega), hM15]
      exact hB j hj
    refine r_mono (h_appendArr T σ16 206 135 (by unfold SAA; decide) (by unfold SAA; decide)
      (by decide) B (dfsS T R u) (rb n 6) hl16.b6 h135
      (by rw [hf16 220 (by unfold SD; decide), hf1215 220 (by decide), hf012 220 (by decide), h220])
      hB16 hX16) fun k17 σ17 ⟨hk17, hf17, hB17, h22017, hm17⟩ =>
      ⟨?_, ?_, hB17, h22017, ?_⟩
    · unfold cBlk
      have c1 := cost_dfs4 n
      have h6 : rb n 6 = 15 * (n + 1) := by unfold rb; ring
      have h4 : rb n 4 = 11 * (n + 1) := by unfold rb; ring
      rw [List.length_append] at hLm
      rw [h4] at k12le
      rw [h6] at hk17
      have := cost_det n Lm (dfsS T R u).length B.length (by omega) hLm
      linarith
    · exact Fr.tr (hf012.mono (by unfold SBK SD SAA; decide)) (Fr.tr (hf1215.mono
        (by unfold SBK SD SAA; decide)) (Fr.tr (hf16.mono (fun r h => by
          unfold SBK; exact List.mem_append_left _ (List.mem_append_left _ h)))
        (hf17.mono (fun r h => by
          unfold SBK; exact List.mem_append_left _ (List.mem_append_right _ h)))))
    · intro z hz
      rw [hm17 z (by rcases hz with h | h; exact Or.inr (Or.inr h.1); exact Or.inl h.1),
        hm16 z (fun h => by
          rcases hz with h' | h'
          · exact absurd h.1 (not_le.mpr h'.2)
          · exact absurd h.1 (not_le.mpr (lt_of_lt_of_le h'.2 (Int.natCast_nonneg _)))),
        hM15]

def blocksPhase : Stmt :=
  .seq (.const 477 1) (.seq (.sub 478 212 477) (forLoop 479 478 480 481 blockBody))

def SBP : List ℕ := SBK ++ [477, 478, 479, 480, 481]

theorem len_flat_le (f : ℕ → List (Fin n)) (a b : ℕ) (h : a ≤ b) :
    ((List.range a).map f).flatten.length ≤ ((List.range b).map f).flatten.length := by
  obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
  rw [List.range_add, List.map_append, List.flatten_append, List.length_append]
  omega

theorem h_blocksPhase (σ : Cfg) (hl : Lay T σ) (hP : ParOK T σ.mem) (R : Finset (Fin n))
    (L : List (Fin n)) (hLR : VOK σ.mem (rb n 4) (ind R)) (hL : LOK T σ.mem (rb n 2) L)
    (hLlen : L.length ≤ 2 * n) (hL0 : L ≠ []) (h212 : σ.regs 212 = L.length)
    (B : List (Fin n)) (h220 : σ.regs 220 = B.length) (hB : BufOK T σ.mem B) (Lm : ℕ)
    (hLm : (B ++ ((List.range (L.length - 1)).map (blk T R L)).flatten).length ≤ Lm) :
    Runs blocksPhase σ (fun k σ' => k ≤ 2 * n * (cBlk n Lm + 5) + 6 ∧ Fr SBP σ σ' ∧
      BufOK T σ'.mem (B ++ ((List.range (L.length - 1)).map (blk T R L)).flatten) ∧
      σ'.regs 220 = ((B ++ ((List.range (L.length - 1)).map (blk T R L)).flatten).length : ℝ) ∧
      ∀ z : ℤ, ((0 ≤ z ∧ z < rb n 6) ∨ (-2 - (B.length : ℤ) < z ∧ z < 0)) →
        σ'.mem z = σ.mem z) := by
  have hLpos : 0 < L.length := List.length_pos_of_ne_nil hL0
  refine r_seq (r_mono (h_const σ 477 1) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_sub σ1 478 212 477) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  have hf02 : Fr [477, 478] σ σ2 := Fr.trm hf1 hf2 (by decide) (by decide)
  have hM2 : σ2.mem = σ.mem := by rw [hm2, hm1]
  have e478 : σ2.regs 478 = ((L.length - 1 : ℕ) : ℝ) := by
    rw [hv2, hf1 212 (by decide), h212, hv1]; push_cast [Nat.cast_sub hLpos]; ring
  let F := fun m => ((List.range m).map (blk T R L)).flatten
  let I : ℕ → Cfg → Prop := fun m σ' => Fr SBP σ σ' ∧
    (∀ z : ℤ, ((0 ≤ z ∧ z < rb n 6) ∨ (-2 - (B.length : ℤ) < z ∧ z < 0)) →
      σ'.mem z = σ.mem z) ∧
    BufOK T σ'.mem (B ++ F m) ∧ σ'.regs 220 = ((B ++ F m).length : ℝ)
  refine r_mono (r_for 479 478 480 481 blockBody (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (L.length - 1) (cBlk n Lm) I σ2 e478 ?_ ?_
    (fun k σ' => k ≤ (L.length - 1) * (cBlk n Lm + 5) + 3 ∧ I (L.length - 1) σ')
    (fun k σ' hk hI => ⟨hk, hI⟩)) fun k3 σ3 ⟨hk3, hf3, hm3, hB3, h2203⟩ => ?_
  · intro a b
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      have h1 : r ≠ 480 := fun h => hr (by unfold SBP; simp [h])
      have h2 : r ≠ 479 := fun h => hr (by unfold SBP; simp [h])
      simp only [update_apply, h1, h2, if_false]
      exact hf02 r (fun h => hr (by unfold SBP; simp at h ⊢; omega))
    · intro z _; rw [hM2]
    · simp [F, hM2, hB]
    · simp only [update_apply, show (220 : ℕ) ≠ 480 by decide, show (220 : ℕ) ≠ 479 by decide,
        if_false]
      rw [hf02 220 (by decide), h220]; simp [F]
  · intro m hm σ' ⟨hf', hm', hB', h220'⟩ hV hN
    have hl' := hl.fr T hf' (by unfold LayRegs SBP SBK SD SAA; decide)
    have hP' : ParOK T σ'.mem := by
      intro w
      have := w.isLt
      rw [hm' _ (Or.inl ⟨by positivity, by unfold rb; push_cast; omega⟩),
        hm' _ (Or.inl ⟨by positivity, by unfold rb; push_cast; omega⟩)]
      exact hP w
    have hLR' : VOK σ'.mem (rb n 4) (ind R) := by
      intro v
      rw [hm' _ (Or.inl ⟨by positivity, by have := v.isLt; unfold rb; push_cast; omega⟩)]
      exact hLR v
    have hL' : LOK T σ'.mem (rb n 2) L := by
      intro j hj
      rw [hm' _ (Or.inl ⟨by positivity, by unfold rb; push_cast; omega⟩)]
      exact hL j hj
    have hFm : F (m + 1) = F m ++ blk T R L m := by
      simp only [F, List.range_succ, List.map_append, List.flatten_append, List.map_cons,
        List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    have hlen : (B ++ F m ++ blk T R L m).length ≤ Lm := by
      refine le_trans ?_ hLm
      rw [List.append_assoc, ← hFm, List.length_append, List.length_append]
      have := len_flat_le (blk T R L) (m + 1) (L.length - 1) (by omega)
      simp only [F]
      omega
    refine r_mono (h_blockBody T σ' hl' hP' R L hLR' hL' hLlen m (by omega) hV (B ++ F m)
      (by rw [h220']) hB' Lm hlen) fun k σ'' ⟨hk, hf'', hB'', h220'', hm''⟩ =>
      ⟨hk, ?_, ?_, fun a b c => ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [hf'' 479 (by unfold SBK SD SAA; decide), hV]
    · rw [hf'' 478 (by unfold SBK SD SAA; decide), hN]
    · intro r hr
      have h1 : r ≠ 480 := fun h => hr (by unfold SBP; simp [h])
      have h2 : r ≠ 479 := fun h => hr (by unfold SBP; simp [h])
      have h3 : r ≠ 481 := fun h => hr (by unfold SBP; simp [h])
      simp only [update_apply, h1, h2, h3, if_false]
      rw [hf'' r (fun h => hr (by unfold SBP; exact List.mem_append_left _ h))]
      exact hf' r hr
    · intro z hz
      show σ''.mem z = σ.mem z
      rw [hm'' z (by
        rcases hz with h | h
        · exact Or.inl h
        · refine Or.inr ⟨?_, h.2⟩
          have := h.1
          simp only [List.length_append] at this ⊢
          push_cast at this ⊢
          omega)]
      exact hm' z hz
    · show BufOK T σ''.mem (B ++ F (m + 1))
      rw [hFm, ← List.append_assoc]; exact hB''
    · show σ''.regs 220 = _
      rw [h220'', hFm, ← List.append_assoc]
  · refine ⟨?_, hf3, hB3, h2203, hm3⟩
    have h1 : (L.length - 1) * (cBlk n Lm + 5) ≤ 2 * n * (cBlk n Lm + 5) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

end OnlineTransportation1195.Dev.T13.PartPR
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.T13.PartPR
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
  OnlineTransportation1195.Dev.T13 OnlineTransportation1195.Dev.RL.Lib Function
/-!
Part PR, file 11: building the walk of a level, `Gstep`, in the buffer from the walk `Wn` of
the next level.
-/
theorem poly_bound (N Q : ℕ) (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    N * (Q * (8 * Q + 12 * N + 135) + 60 * N + 100) + N * (4 * Q + 16 * N + 70) +
      (2 * N * (2000 * N ^ 3 + 10 * (N * Q) + 5) + 6) + 30 ≤ 10000 * (N ^ 4 * Q ^ 2) := by
  have hP1 : 1 ≤ N ^ 4 * Q ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have m1 : N ≤ N ^ 4 * Q ^ 2 := by
    calc N = N * 1 * 1 * 1 * 1 * 1 := by ring
      _ ≤ N * N * N * N * Q * Q := by gcongr
      _ = N ^ 4 * Q ^ 2 := by ring
  have m2 : N * Q ≤ N ^ 4 * Q ^ 2 := by
    calc N * Q = N * 1 * 1 * 1 * Q * 1 := by ring
      _ ≤ N * N * N * N * Q * Q := by gcongr
      _ = N ^ 4 * Q ^ 2 := by ring
  have m3 : N * Q ^ 2 ≤ N ^ 4 * Q ^ 2 := by
    calc N * Q ^ 2 = N * 1 * 1 * 1 * Q * Q := by ring
      _ ≤ N * N * N * N * Q * Q := by gcongr
      _ = N ^ 4 * Q ^ 2 := by ring
  have m4 : N ^ 2 ≤ N ^ 4 * Q ^ 2 := by
    calc N ^ 2 = N * N * 1 * 1 * 1 * 1 := by ring
      _ ≤ N * N * N * N * Q * Q := by gcongr
      _ = N ^ 4 * Q ^ 2 := by ring
  have m5 : N ^ 2 * Q ≤ N ^ 4 * Q ^ 2 := by
    calc N ^ 2 * Q = N * N * 1 * 1 * Q * 1 := by ring
      _ ≤ N * N * N * N * Q * Q := by gcongr
      _ = N ^ 4 * Q ^ 2 := by ring
  have m6 : N ^ 4 ≤ N ^ 4 * Q ^ 2 := by
    calc N ^ 4 = N * N * N * N * 1 * 1 := by ring
      _ ≤ N * N * N * N * Q * Q := by gcongr
      _ = N ^ 4 * Q ^ 2 := by ring
  have e : N * (Q * (8 * Q + 12 * N + 135) + 60 * N + 100) + N * (4 * Q + 16 * N + 70) +
      (2 * N * (2000 * N ^ 3 + 10 * (N * Q) + 5) + 6) + 30 =
      8 * (N * Q ^ 2) + 32 * (N ^ 2 * Q) + 139 * (N * Q) + 76 * N ^ 2 + 180 * N +
        4000 * N ^ 4 + 36 := by ring
  rw [e]
  omega

def cBuild (n Lm : ℕ) : ℕ := 10000 * ((n + 1) ^ 4 * (Lm + 1) ^ 2)

theorem cost_build (n Lm w m : ℕ) (hw : w ≤ Lm) (hm : m ≤ Lm) :
    (n + 1) * (w * (8 * w + 12 * n + 135) + 60 * n + 100) + (n + 1) * (4 * m + 16 * n + 70) +
      (2 * n * (cBlk n Lm + 5) + 6) + 30 ≤ cBuild n Lm := by
  have h := poly_bound (n + 1) (Lm + 1) (by omega) (by omega)
  have h1 : w * (8 * w + 12 * n + 135) ≤ (Lm + 1) * (8 * (Lm + 1) + 12 * (n + 1) + 135) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (n + 1) * (w * (8 * w + 12 * n + 135) + 60 * n + 100) ≤ (n + 1) *
      ((Lm + 1) * (8 * (Lm + 1) + 12 * (n + 1) + 135) + 60 * (n + 1) + 100) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : (n + 1) * (4 * m + 16 * n + 70) ≤ (n + 1) * (4 * (Lm + 1) + 16 * (n + 1) + 70) :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 : 2 * n * (cBlk n Lm + 5) ≤
      2 * (n + 1) * (2000 * (n + 1) ^ 3 + 10 * ((n + 1) * (Lm + 1)) + 5) := by
    have a : (n + 1) * Lm ≤ (n + 1) * (Lm + 1) := Nat.mul_le_mul_left _ (by omega)
    exact Nat.mul_le_mul (by omega) (by unfold cBlk; omega)
  unfold cBuild
  exact le_trans (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add h2 h3)
    (Nat.add_le_add_right h4 6)) 30) h

theorem cost_small (n Lm x : ℕ) (hx : x ≤ 2 * n) :
    x * (4 * (rb n 2 + x) + 4 * (0 + x) + 30) + 5 + 30 ≤ cBuild n Lm := by
  have h1 : x * (4 * (rb n 2 + x) + 4 * (0 + x) + 30) ≤ (2 * n) * (4 * (7 * (n + 1) + 2 * n) +
      4 * (2 * n) + 30) := Nat.mul_le_mul hx (by unfold rb; omega)
  have h2 : (2 * n) * (4 * (7 * (n + 1) + 2 * n) + 4 * (2 * n) + 30) + 35 ≤
      10000 * (n + 1) ^ 2 := by nlinarith
  have h3 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 * (Lm + 1) ^ 2 := by
    calc (n + 1) ^ 2 = (n + 1) * (n + 1) * 1 * 1 * 1 * 1 := by ring
      _ ≤ (n + 1) * (n + 1) * (n + 1) * (n + 1) * (Lm + 1) * (Lm + 1) := by
        gcongr <;> omega
      _ = (n + 1) ^ 4 * (Lm + 1) ^ 2 := by ring
  unfold cBuild
  omega

end OnlineTransportation1195.Dev.T13.PartPR
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.T13.PartPR
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
  OnlineTransportation1195.Dev.T13 OnlineTransportation1195.Dev.RL.Lib Function
variable {n : ℕ} (T : Tree n)
def setRoot : Stmt := .seq (.const 220 0) (push 2)

def copyL : Stmt := .seq (.const 220 0) (appendArr 202 212)

def mPhase : Stmt := .ifle 217 setRoot truncPhase

def general : Stmt := .seq mPhase (.seq upPhase blocksPhase)

def buildProg : Stmt := .ifle 210 setRoot (.ifle 211 copyL general)

def SBuild : List ℕ := STR ++ SUP ++ SBP ++ SAA ++ [220, 227]

theorem h_setRoot (σ : Cfg) (hl : Lay T σ) :
    Runs setRoot σ (fun k σ' => k ≤ 11 ∧ Fr [100, 101, 220, 227] σ σ' ∧
      BufOK T σ'.mem [T.root] ∧ σ'.regs 220 = 1 ∧ ∀ z : ℤ, z ≠ -2 → σ'.mem z = σ.mem z) := by
  refine r_seq (r_mono (h_const σ 220 0) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_mono (h_push T σ1 2 (by decide) [] T.root (by rw [hf1 2 (by decide), hl.h2])
    (by rw [hv1]; simp) (fun i hi => by simp at hi)) fun k2 σ2 ⟨hk2, hf2, hB2, h2202, hm2⟩ =>
    ⟨by simp at hk2; omega, Fr.trm hf1 hf2 (by decide) (by decide), by simpa using hB2,
      by rw [h2202]; simp, fun z hz => by rw [hm2 z (by simpa using hz), hm1]⟩

theorem h_mPhase (σ : Cfg) (S : Finset (Fin n)) (d : Fin n → ℝ) (h : LevOK T S d σ)
    (Wn : List (Fin n)) (h220 : σ.regs 220 = Wn.length) (hB : BufOK T σ.mem Wn) :
    let M := if recP T S d then trunc T (patchS T S d (dfsS T S T.root)
      (pickT T S d (dfsS T S T.root))) Wn else [T.root]
    Runs mPhase σ (fun k σ' =>
      k ≤ (n + 1) * (Wn.length * (8 * Wn.length + 12 * n + 135) + 60 * n + 100) + 13 ∧
      Fr SBuild σ σ' ∧ BufOK T σ'.mem M ∧ σ'.regs 220 = (M.length : ℝ) ∧
      ∀ z : ℤ, (0 ≤ z ∨ -2 < z) → σ'.mem z = σ.mem z) := by
  intro M
  have hl := h.lay
  refine r_ifle (fun h0 => ?_) (fun h0 => ?_)
  · have hr : ¬ recP T S d := by
      intro hr; rw [h.rc, if_pos hr] at h0; norm_num at h0
    have hM : M = [T.root] := by simp only [M, if_neg hr]
    rw [hM]
    refine r_mono (h_setRoot T σ hl) fun k σ' ⟨hk, hf, hB', h220', hm⟩ =>
      ⟨by omega, hf.mono (by unfold SBuild STR STB SFI SCR SUP SBP SBK SD SAA; decide), hB',
        by rw [h220']; simp,
        fun z hz => hm z (by omega)⟩
  · have hr : recP T S d := by
      by_contra hr; rw [h.rc, if_neg hr] at h0; norm_num at h0
    have hM : M = trunc T (patchS T S d (dfsS T S T.root) (pickT T S d (dfsS T S T.root))) Wn := by
      simp only [M, if_pos hr]
    rw [hM]
    refine r_mono (h_truncPhase T σ hl _ Wn h220 hB h.pat h.par)
      fun k σ' ⟨hk, hm, hf, hB', h220'⟩ =>
      ⟨by omega, hf.mono (fun r hr => by unfold SBuild; simp [hr]), hB', h220',
        fun z _ => by rw [hm]⟩

theorem dfsS_ne_nil (S : Finset (Fin n)) (v : Fin n) : dfsS T S v ≠ [] := by
  have := PartB.dfsF_head T S n v
  intro h
  unfold dfsS at h
  rw [h] at this
  simp at this

/-!
Part PR (`algo13`): the program computing `walkFn T T.edges (d0 T)`.
For `o = 0, …, n - 1` it recomputes the level `j = n - 1 - o` from level `0` and builds the walk
of level `j` in the output buffer from the walk of level `j + 1` already there.
-/
/-! ## Facts about the walks -/
theorem Gstep_ne_nil (S : Finset (Fin n)) (d : Fin n → ℝ) (Wn : List (Fin n))
    (hWn : recP T S d → Wn ≠ []) : Gstep T S d Wn ≠ [] := by
  unfold Gstep
  split_ifs with h1 h2 hr
  · simp
  · exact dfsS_ne_nil T S T.root
  · dsimp only
    intro h
    rw [List.append_assoc, List.append_eq_nil_iff] at h
    have hW := hWn hr
    have h3 := h.1
    unfold trunc at h3
    rw [List.take_eq_nil_iff] at h3
    rcases h3 with h' | h'
    · omega
    · exact hW h'
  · dsimp only
    simp

theorem walkFn_ne_nil : ∀ (k : ℕ) (S : Finset (Fin n)) (d : Fin n → ℝ), S.card ≤ k →
    walkFn T S d ≠ [] := by
  intro k
  induction k with
  | zero =>
    intro S d hS
    have : S = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [walkFn, if_pos this]; simp
  | succ k ih =>
    intro S d hS
    rw [walkFn_eq]
    refine Gstep_ne_nil T S d _ fun hr => ih _ _ (by have := hr.2.2.2; omega)

theorem walkFn_empty (d : Fin n → ℝ) : walkFn T ∅ d = [T.root] := by
  rw [walkFn, if_pos rfl]

/-- The buffer before iteration `o`. -/
noncomputable def cur (o : ℕ) : List (Fin n) :=
  if o = 0 then [] else walkFn T (lev T (n - o)).1 (lev T (n - o)).2

def Lm0 (n : ℕ) : ℕ := n * (5 * n + 2)

theorem walk_lev_len (j : ℕ) : (walkFn T (lev T j).1 (lev T j).2).length ≤ Lm0 n := by
  have h := walkFn_length T (lev T j).1 (lev_sub T j) (lev T j).2
  have hc : (lev T j).1.card ≤ n - 1 := by
    have := Finset.card_le_card (lev_sub T j)
    rw [edges_card] at this; exact this
  have hn : 0 < n := Fin.pos T.root
  have : ((lev T j).1.card + 1) * (5 * n + 2) ≤ n * (5 * n + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  unfold Lm0; omega

theorem cur_len (o : ℕ) : (cur T o).length ≤ Lm0 n := by
  unfold cur
  split_ifs
  · simp
  · exact walk_lev_len T _

theorem gstep_cur (o : ℕ) (ho : o < n) :
    Gstep T (lev T (n - 1 - o)).1 (lev T (n - 1 - o)).2 (cur T o) = cur T (o + 1) ∧
      (recP T (lev T (n - 1 - o)).1 (lev T (n - 1 - o)).2 → cur T o ≠ []) := by
  have hn : 0 < n := Fin.pos T.root
  by_cases h0 : o = 0
  · subst h0
    have he : (lev T (n - 1)).1 = ∅ := lev_last T hn
    have hc1 : cur T (0 + 1) = walkFn T (lev T (n - 1)).1 (lev T (n - 1)).2 := by
      unfold cur; rw [if_neg (Nat.succ_ne_zero 0)]
    rw [Nat.sub_zero, hc1]
    refine ⟨?_, fun hr => absurd he hr.1⟩
    unfold Gstep
    rw [if_pos he, he, walkFn_empty]
  · have hj : n - 1 - o + 1 = n - o := by omega
    have hc0 : cur T o = walkFn T (lev T (n - o)).1 (lev T (n - o)).2 := by
      unfold cur; rw [if_neg h0]
    have hc1 : cur T (o + 1) = walkFn T (lev T (n - 1 - o)).1 (lev T (n - 1 - o)).2 := by
      unfold cur; rw [if_neg (Nat.succ_ne_zero o), show n - (o + 1) = n - 1 - o by omega]
    rw [hc0, hc1, walkFn_lev T (n - 1 - o), hj]
    exact ⟨rfl, fun _ => walkFn_ne_nil T _ _ _ le_rfl⟩

/-! ## The program -/
def loadPart : Stmt := .seq (.pset 1 0) (.seq (.load 1 1) (.seq (.pinc 1) (.load 2 1)))

def baseStep (m : ℕ) : Stmt := .seq (.const 104 ((3 + 2 * m : ℕ) : ℚ)) (.mul (200 + m) 104 103)

def initProg : Stmt :=
  .seq loadPart (.seq (.const 102 1) (.seq (.add 103 1 102) (.seq (baseStep 0) (.seq (baseStep 1)
  (.seq (baseStep 2) (.seq (baseStep 3) (.seq (baseStep 4) (.seq (baseStep 5) (.seq (baseStep 6)
  (.const 220 0))))))))))

def resetProg : Stmt :=
  .seq (fillLoop 600 1 601 602 200 603 604 (.seq (eqT 605 600 2) (notF 604 605)))
    (.seq (.const 606 1) (.seq (.sub 607 1 606)
      (fillLoop 600 1 601 602 201 603 604 (.seq (ldIn 608 3 600) (.mul 604 607 608)))))

def outerBody : Stmt :=
  .seq (.const 614 1) (.seq (.sub 613 1 614) (.seq (.sub 613 613 610) (.seq resetProg
    (.seq (forLoop 615 613 616 617 (.seq levelProg advProg)) (.seq levelProg buildProg)))))

def prog13 : Stmt :=
  .seq initProg (.seq (forLoop 610 1 611 612 outerBody) (.seq (.pset 1 (-1)) (.store 1 220)))

def SRes : List ℕ := [100, 101, 102, 600, 601, 602, 603, 604, 605, 606, 607, 608]

theorem h_reset (σ : Cfg) (hl : Lay T σ) (hP : ParOK T σ.mem) :
    Runs resetProg σ (fun k σ' => k ≤ 200 * (n + 1) ^ 2 ∧ Fr SRes σ σ' ∧
      (∀ z : ℤ, ¬ (((rb n 0 : ℕ) : ℤ) ≤ z ∧ z < rb n 2) → σ'.mem z = σ.mem z) ∧
      VOK σ'.mem (rb n 0) (ind (lev T 0).1) ∧ VOK σ'.mem (rb n 1) (lev T 0).2) := by
  refine r_seq (r_mono (h_fillLoop 600 1 601 602 200 603 604 (.seq (eqT 605 600 2) (notF 604 605))
    [100, 102, 604, 605] [100, 102, 604, 605, 600, 601, 602, 603, 101]
    (by unfold FillOK; decide) n 10 (rb n 0)
    (fun m => if h : m < n then ind (lev T 0).1 ⟨m, h⟩ else 0) σ hl.h1 hl.b0 ?_)
    fun k1 σ1 ⟨hk1, hf1, hm1, hv1⟩ => ?_)
  · intro m hm σ' hm' hf' hV'
    refine r_seq (r_mono (h_eqT σ' 605 600 2 (by decide) (by decide) (by decide))
      fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => r_mono (h_notF σ2 604 605 (by decide))
      fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ⟨by omega, by rw [hm3, hm2], Fr.trm hf2 hf3 (by decide)
        (by decide), ?_⟩)
    rw [hv3, hv2, hV', hf' 2 (by decide), hl.h2]
    simp only [hm, dif_pos]
    show _ = ind T.edges _
    unfold ind
    by_cases c : (⟨m, hm⟩ : Fin n) = T.root
    · rw [if_pos (by rw [← c]), if_neg (by rw [mem_edges_iff]; exact not_not.mpr c)]; norm_num
    · rw [if_neg (fun h => c (Fin.ext (by exact_mod_cast h))),
        if_pos (by rw [mem_edges_iff]; exact c)]; norm_num
  have hl1 := hl.fr T hf1 (by unfold LayRegs; decide)
  refine r_seq (r_mono (h_const σ1 606 1) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_sub σ2 607 1 606) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  have hf13 : Fr [606, 607] σ1 σ3 := Fr.trm hf2 hf3 (by decide) (by decide)
  have hl3 := hl1.fr T hf13 (by unfold LayRegs; decide)
  have e607 : σ3.regs 607 = (n : ℝ) - 1 := by
    rw [hv3, hf2 1 (by decide), hl1.h1, hv2]; simp
  refine r_mono (h_fillLoop 600 1 601 602 201 603 604 (.seq (ldIn 608 3 600) (.mul 604 607 608))
    [100, 101, 604, 608] [100, 101, 604, 608, 600, 601, 602, 603]
    (by unfold FillOK; decide) n (16 * n + 30) (rb n 1)
    (fun m => if h : m < n then (lev T 0).2 ⟨m, h⟩ else 0) σ3 hl3.h1 hl3.b1 ?_)
    fun k4 σ4 ⟨hk4, hf4, hm4, hv4⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m hm σ' hm' hf' hV'
    refine r_seq (r_mono (h_ldIn σ' 608 3 600 (by decide) m hV')
      fun k5 σ5 ⟨hk5, hm5, hf5, hv5⟩ => r_mono (h_mul σ5 604 607 608)
      fun k6 σ6 ⟨hk6, hm6, hf6, hv6⟩ => ⟨by omega, by rw [hm6, hm5], Fr.trm hf5 hf6 (by decide)
        (by decide), ?_⟩)
    rw [hv6, hf5 607 (by decide), hf' 607 (by decide), e607, hv5, hm' _ (by
      unfold rb; push_cast; omega), hm3, hm2, hm1 _ (by unfold rb; push_cast; omega)]
    have := (hP ⟨m, hm⟩).2
    simp only at this
    rw [this]
    simp only [hm, dif_pos]
    rfl
  · have c1 : n * (10 + 4 * ((3 + 2 * 0) * (n + 1) + n) + 13) + 3 + 2 +
        (n * (16 * n + 30 + 4 * ((3 + 2 * 1) * (n + 1) + n) + 13) + 3) ≤ 200 * (n + 1) ^ 2 := by
      ring_nf; nlinarith
    unfold rb at hk1 hk4
    omega
  · exact Fr.tr (hf1.mono (by unfold SRes; decide)) (Fr.tr (hf13.mono (by unfold SRes; decide))
      (hf4.mono (by unfold SRes; decide)))
  · intro z hz
    rw [hm4 z (by unfold rb at hz ⊢; push_cast at hz ⊢; omega), hm3, hm2,
      hm1 z (by unfold rb at hz ⊢; push_cast at hz ⊢; omega)]
  · intro v
    rw [hm4 _ (by have := v.isLt; unfold rb; push_cast; omega), hm3, hm2, hv1 v.val v.isLt]
    simp
  · intro v
    rw [hv4 v.val v.isLt]
    simp

theorem cost_outer (n j : ℕ) (hj : j ≤ n) :
    1 + (1 + (1 + (200 * (n + 1) ^ 2 + ((j * (5000 * (n + 1) ^ 3 + 300 * (n + 1) ^ 2 + 5) + 3) +
      (5000 * (n + 1) ^ 3 + cBuild n (Lm0 n)))))) ≤ 300000 * (n + 1) ^ 8 := by
  have hN : 1 ≤ n + 1 := by omega
  have e1 : Lm0 n + 1 ≤ 5 * (n + 1) ^ 2 := by unfold Lm0; nlinarith
  have e2 : (Lm0 n + 1) ^ 2 ≤ 25 * (n + 1) ^ 4 := by
    calc (Lm0 n + 1) ^ 2 ≤ (5 * (n + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left e1 2
      _ = 25 * (n + 1) ^ 4 := by ring
  have e3 : cBuild n (Lm0 n) ≤ 250000 * (n + 1) ^ 8 := by
    unfold cBuild
    calc 10000 * ((n + 1) ^ 4 * (Lm0 n + 1) ^ 2) ≤ 10000 * ((n + 1) ^ 4 * (25 * (n + 1) ^ 4)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e2)
      _ = 250000 * (n + 1) ^ 8 := by ring
  have e4 : j * (5000 * (n + 1) ^ 3 + 300 * (n + 1) ^ 2 + 5) ≤
      (n + 1) * (5000 * (n + 1) ^ 3 + 300 * (n + 1) ^ 2 + 5) := Nat.mul_le_mul_right _ (by omega)
  have p2 : (n + 1) ^ 2 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right hN (by norm_num)
  have p3 : (n + 1) ^ 3 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right hN (by norm_num)
  have p4 : (n + 1) ^ 4 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right hN (by norm_num)
  have p1 : (n + 1) ≤ (n + 1) ^ 8 := by
    calc n + 1 = (n + 1) ^ 1 := by ring
      _ ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right hN (by norm_num)
  have e5 : (n + 1) * (5000 * (n + 1) ^ 3 + 300 * (n + 1) ^ 2 + 5) =
      5000 * (n + 1) ^ 4 + 300 * (n + 1) ^ 3 + 5 * (n + 1) := by ring
  omega

theorem cost_total (n c : ℕ) (hc : c ≤ 300000 * (n + 1) ^ 8) :
    30 + (n * (c + 5) + 3 + 2) ≤ 400000 * (n + 1) ^ 9 := by
  have hN : 1 ≤ n + 1 := by omega
  have h1 : n * (c + 5) ≤ (n + 1) * (300000 * (n + 1) ^ 8 + 5) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : (n + 1) * (300000 * (n + 1) ^ 8 + 5) = 300000 * (n + 1) ^ 9 + 5 * (n + 1) := by ring
  have p : n + 1 ≤ (n + 1) ^ 9 := by
    calc n + 1 = (n + 1) ^ 1 := by ring
      _ ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right hN (by norm_num)
  omega

/-- The state during the initialization. -/
def IP (M : ℤ → ℝ) (m : ℕ) (σ : Cfg) : Prop :=
  σ.regs 1 = n ∧ σ.regs 2 = T.root.val ∧ σ.regs 103 = (n : ℝ) + 1 ∧ σ.mem = M ∧
    ∀ i < m, σ.regs (200 + i) = rb n i

theorem h_baseStep (M : ℤ → ℝ) (m : ℕ) (hm : m < 7) (σ : Cfg) (h : IP T M m σ) :
    Runs (baseStep m) σ (fun k σ' => k = 2 ∧ IP T M (m + 1) σ') := by
  obtain ⟨h1, h2, h103, hM, hb⟩ := h
  refine r_seq (r_mono (h_const σ 104 _) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ =>
    r_mono (h_mul σ1 (200 + m) 104 103) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩)
  · rw [hf2 1 (by simp; omega), hf1 1 (by decide), h1]
  · rw [hf2 2 (by simp; omega), hf1 2 (by decide), h2]
  · rw [hf2 103 (by simp; omega), hf1 103 (by decide), h103]
  · rw [hm2, hm1, hM]
  · intro i hi
    by_cases hi' : i = m
    · subst hi'
      rw [hv2, hv1, hf1 103 (by decide), h103]
      unfold rb; push_cast; ring
    · rw [hf2 (200 + i) (by simp; omega), hf1 (200 + i) (by simp; omega), hb i (by omega)]

theorem h_init :
    Runs initProg (Cfg.init (treeInput T (fun _ => 0) [])) (fun k σ' => k ≤ 30 ∧ Lay T σ' ∧
      σ'.mem = treeInput T (fun _ => 0) [] ∧ σ'.regs 220 = 0) := by
  have t0 : treeInput T (fun _ => 0) [] 0 = n := by simpa using ti_zero T (fun _ => 0) []
  have t1 : treeInput T (fun _ => 0) [] 1 = T.root.val := by
    simpa using ti_one T (fun _ => 0) []
  set M := treeInput T (fun _ => 0) [] with hMdef
  unfold initProg loadPart
  refine r_seq (r_seq (r_pset (r_seq (r_load (r_seq (r_pinc (r_load ?_)))))))
  refine r_seq (r_mono (h_const _ 102 1) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_add σ1 103 1 102) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  have h0 : IP T M 0 σ2 := by
    refine ⟨?_, ?_, ?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · rw [hf2 1 (by decide), hf1 1 (by decide)]; simp [update_apply, Cfg.init, t0]
    · rw [hf2 2 (by decide), hf1 2 (by decide)]; simp [update_apply, Cfg.init, t1]
    · rw [hv2, hv1, hf1 1 (by decide)]; simp [update_apply, Cfg.init, t0]
    · rw [hm2, hm1]; rfl
  refine r_seq (r_mono (h_baseStep T M 0 (by norm_num) σ2 h0) fun k3 σ3 ⟨hk3, h3⟩ => ?_)
  refine r_seq (r_mono (h_baseStep T M 1 (by norm_num) σ3 h3) fun k4 σ4 ⟨hk4, h4⟩ => ?_)
  refine r_seq (r_mono (h_baseStep T M 2 (by norm_num) σ4 h4) fun k5 σ5 ⟨hk5, h5⟩ => ?_)
  refine r_seq (r_mono (h_baseStep T M 3 (by norm_num) σ5 h5) fun k6 σ6 ⟨hk6, h6⟩ => ?_)
  refine r_seq (r_mono (h_baseStep T M 4 (by norm_num) σ6 h6) fun k7 σ7 ⟨hk7, h7⟩ => ?_)
  refine r_seq (r_mono (h_baseStep T M 5 (by norm_num) σ7 h7) fun k8 σ8 ⟨hk8, h8⟩ => ?_)
  refine r_seq (r_mono (h_baseStep T M 6 (by norm_num) σ8 h8) fun k9 σ9 ⟨hk9, h9⟩ => ?_)
  refine r_mono (h_const σ9 220 0) fun k10 σ10 ⟨hk10, hm10, hf10, hv10⟩ =>
    ⟨by omega, ?_, by rw [hm10, h9.2.2.2.1], by rw [hv10]; simp⟩
  obtain ⟨g1, g2, -, -, gb⟩ := h9
  exact ⟨by rw [hf10 1 (by decide), g1], by rw [hf10 2 (by decide), g2],
    by rw [hf10 200 (by decide)]; exact gb 0 (by norm_num),
    by rw [hf10 201 (by decide)]; exact gb 1 (by norm_num),
    by rw [hf10 202 (by decide)]; exact gb 2 (by norm_num),
    by rw [hf10 203 (by decide)]; exact gb 3 (by norm_num),
    by rw [hf10 204 (by decide)]; exact gb 4 (by norm_num),
    by rw [hf10 205 (by decide)]; exact gb 5 (by norm_num),
    by rw [hf10 206 (by decide)]; exact gb 6 (by norm_num)⟩

theorem h_build (σ : Cfg) (S : Finset (Fin n)) (d : Fin n → ℝ) (h : LevOK T S d σ)
    (Wn : List (Fin n)) (h220 : σ.regs 220 = Wn.length) (hB : BufOK T σ.mem Wn)
    (hWn : recP T S d → Wn ≠ []) (Lm : ℕ) (hLm1 : Wn.length ≤ Lm)
    (hLm2 : (Gstep T S d Wn).length ≤ Lm) :
    Runs buildProg σ (fun k σ' => k ≤ cBuild n Lm ∧ Fr SBuild σ σ' ∧
      BufOK T σ'.mem (Gstep T S d Wn) ∧ σ'.regs 220 = ((Gstep T S d Wn).length : ℝ) ∧
      ∀ z : ℤ, 0 ≤ z → z < rb n 6 → σ'.mem z = σ.mem z) := by
  have hl := h.lay
  have hn : 0 < n := Fin.pos T.root
  have hcb : 10000 ≤ cBuild n Lm := by
    unfold cBuild
    have : 1 ≤ (n + 1) ^ 4 * (Lm + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hLlen : (dfsS T S T.root).length ≤ 2 * n := by
    have := dfsS_length T S T.root; omega
  have hL0 := dfsS_ne_nil T S T.root
  refine r_ifle (fun h0 => ?_) (fun h0 => ?_)
  · -- the empty level
    have hS : S = ∅ := by
      rw [h.cS] at h0
      have : S.card = 0 := by
        have h' : (S.card : ℝ) ≤ 0 := h0
        exact_mod_cast le_antisymm (by exact_mod_cast h') (Nat.zero_le S.card)
      exact Finset.card_eq_zero.mp this
    have hG : Gstep T S d Wn = [T.root] := by unfold Gstep; rw [if_pos hS]
    rw [hG]
    refine r_mono (h_setRoot T σ hl) fun k σ' ⟨hk, hf, hB', h220', hm⟩ =>
      ⟨by omega, hf.mono (by unfold SBuild STR STB SFI SCR SUP SBP SBK SD SAA; decide), hB',
        by rw [h220']; simp, fun z hz _ => hm z (by omega)⟩
  have hS : S ≠ ∅ := by
    intro hS
    rw [h.cS, hS] at h0
    exact h0 (by simp)
  refine r_ifle (fun h1 => ?_) (fun h1 => ?_)
  · -- all deadlines equal
    have hE : ∀ e ∈ S, ∀ f ∈ S, d e = d f :=
      (badCount_eq_zero S d).mp (le_antisymm (by rw [← h.bad]; exact h1) (badCount_nonneg S d))
    have hG : Gstep T S d Wn = dfsS T S T.root := by unfold Gstep; rw [if_neg hS, if_pos hE]
    rw [hG]
    refine r_seq (r_mono (h_const σ 220 0) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
    have hl1 := hl.fr T hf1 (by unfold LayRegs; decide)
    refine r_mono (h_appendArr T σ1 202 212 (by unfold SAA; decide) (by unfold SAA; decide)
      (by decide) [] (dfsS T S T.root) (rb n 2) hl1.b2 (by rw [hf1 212 (by decide), h.lenL])
      (by rw [hv1]; simp) (fun i hi => by simp at hi) (by rw [hm1]; exact h.LL))
      fun k2 σ2 ⟨hk2, hf2, hB2, h2202, hm2⟩ => ⟨?_, ?_, by simpa using hB2,
        by rw [h2202]; simp, fun z hz _ => by rw [hm2 z (Or.inr (Or.inr hz)), hm1]⟩
    · have := cost_small n Lm (dfsS T S T.root).length hLlen
      simp only [List.length_nil] at hk2
      omega
    · exact Fr.trm hf1 hf2 (by unfold SBuild; simp) (fun r hr => by
        unfold SBuild; exact List.mem_append_left _ (List.mem_append_right _ hr))
  · -- the general level
    have hE : ¬ ∀ e ∈ S, ∀ f ∈ S, d e = d f := by
      intro hE
      have := (badCount_eq_zero S d).mpr hE
      rw [h.bad, this] at h1
      exact h1 le_rfl
    set L := dfsS T S T.root with hLdef
    set t := pickT T S d L with htdef
    set M := if recP T S d then trunc T (patchS T S d L t) Wn else [T.root] with hMdef
    have hG : Gstep T S d Wn = M ++ (upPath T (M.getLast?.getD T.root)).tail ++
        (blocks L (detS T S d L t)).tail := by
      unfold Gstep; rw [if_neg hS, if_neg hE]
    have hM0 : M ≠ [] := by
      by_cases hr : recP T S d
      · simp only [hMdef, if_pos hr]
        unfold trunc
        intro h'
        rw [List.take_eq_nil_iff] at h'
        rcases h' with h' | h'
        · omega
        · exact hWn hr h'
      · simp only [hMdef, if_neg hr]; simp
    have hbt : (blocks L (detS T S d L t)).tail =
        ((List.range (L.length - 1)).map (blk T (redS T S d L t) L)).flatten := by
      rw [blocks_tail T L _ hL0 (detS_zero T S d L t)]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      exact detS_succ T S d L t i (by omega)
    rw [hG, hbt] at hLm2 ⊢
    unfold general
    refine r_seq (r_mono (h_mPhase T σ S d h Wn h220 hB) fun k1 σ1 ⟨hk1, hf1, hB1, h2201, hm1⟩ => ?_)
    have hl1 := hl.fr T hf1 (by unfold LayRegs SBuild STR STB SFI SCR SUP SBP SBK SD SAA; decide)
    have hP1 : ParOK T σ1.mem := by
      intro w; rw [hm1 _ (Or.inl (by positivity)), hm1 _ (Or.inl (by positivity))]; exact h.par w
    refine r_seq (r_mono (h_upPhase T σ1 hl1 hP1 M hM0 h2201 hB1)
      fun k2 σ2 ⟨hk2, hf2, hB2, h2202, hm2⟩ => ?_)
    have hl2 := hl1.fr T hf2 (by unfold LayRegs SUP; decide)
    have hm02 : ∀ z : ℤ, 0 ≤ z → σ2.mem z = σ.mem z := fun z hz => by
      rw [hm2 z (Or.inr hz), hm1 z (Or.inl hz)]
    have hP2 : ParOK T σ2.mem := by
      intro w; rw [hm02 _ (by positivity), hm02 _ (by positivity)]; exact h.par w
    have h212 : σ2.regs 212 = (L.length : ℝ) := by
      have e1 : (212 : ℕ) ∉ SBuild := by
        unfold SBuild STR STB SFI SCR SUP SBP SBK SD SAA; decide
      rw [hf2 212 (by unfold SUP; decide), hf1 212 e1, h.lenL]
    refine r_mono (h_blocksPhase T σ2 hl2 hP2 (redS T S d L t) L
      (fun v => by rw [hm02 _ (by positivity)]; exact h.red v)
      (fun j hj => by rw [hm02 _ (by positivity)]; exact h.LL j hj) hLlen hL0
      h212 _ h2202 hB2 Lm hLm2)
      fun k3 σ3 ⟨hk3, hf3, hB3, h2203, hm3⟩ => ⟨?_, ?_, hB3, h2203, ?_⟩
    · have hMl : M.length ≤ Lm := by
        simp only [List.length_append] at hLm2; omega
      have := cost_build n Lm Wn.length M.length hLm1 hMl
      omega
    · exact Fr.tr hf1 (Fr.tr (hf2.mono (fun r hr => by
        unfold SBuild; simp only [List.mem_append]; tauto)) (hf3.mono (fun r hr => by
        unfold SBuild; simp only [List.mem_append]; tauto)))
    · intro z hz hz'
      rw [hm3 z (Or.inl ⟨hz, hz'⟩), hm02 z hz]

/-- One outer iteration. -/
theorem h_outerBody (σ : Cfg) (hl : Lay T σ) (hP : ParOK T σ.mem) (o : ℕ) (ho : o < n)
    (h610 : σ.regs 610 = o) (hB : BufOK T σ.mem (cur T o))
    (h220 : σ.regs 220 = (cur T o).length) :
    Runs outerBody σ (fun k σ' => k ≤ 300000 * (n + 1) ^ 8 ∧ Lay T σ' ∧ ParOK T σ'.mem ∧
      σ'.regs 610 = o ∧ BufOK T σ'.mem (cur T (o + 1)) ∧
      σ'.regs 220 = (cur T (o + 1)).length) := by
  have hn : 0 < n := Fin.pos T.root
  set j := n - 1 - o with hj
  refine r_seq (r_mono (h_const σ 614 1) fun k1 σ1 ⟨hk1, hm1, hf1, hv1⟩ => ?_)
  refine r_seq (r_mono (h_sub σ1 613 1 614) fun k2 σ2 ⟨hk2, hm2, hf2, hv2⟩ => ?_)
  refine r_seq (r_mono (h_sub σ2 613 613 610) fun k3 σ3 ⟨hk3, hm3, hf3, hv3⟩ => ?_)
  have hf03 : Fr [613, 614] σ σ3 := Fr.tr (hf1.mono (by decide)) (Fr.tr (hf2.mono (by decide))
    (hf3.mono (by decide)))
  have hl3 := hl.fr T hf03 (by unfold LayRegs; decide)
  have hM3 : σ3.mem = σ.mem := by rw [hm3, hm2, hm1]
  have e613 : σ3.regs 613 = (j : ℝ) := by
    rw [hv3, hv2, hv1, hf2 610 (by decide), hf1 610 (by decide), h610, hf1 1 (by decide), hl.h1,
      hj, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  refine r_seq (r_mono (h_reset T σ3 hl3 (by rw [hM3]; exact hP))
    fun k4 σ4 ⟨hk4, hf4, hm4, hS4, hd4⟩ => ?_)
  have hl4 := hl3.fr T hf4 (by unfold LayRegs SRes; decide)
  have hlow : ∀ M : ℤ → ℝ, (∀ z : ℤ, (z < ((rb n 0 : ℕ) : ℤ)) → M z = σ.mem z) →
      ParOK T M ∧ BufOK T M (cur T o) := by
    intro M hM
    refine ⟨fun w => ?_, fun i hi => ?_⟩
    · have := w.isLt
      rw [hM _ (by unfold rb; push_cast; omega), hM _ (by unfold rb; push_cast; omega)]
      exact hP w
    · rw [hM _ (by unfold rb; push_cast; omega)]; exact hB i hi
  -- the inner loop: from level `0` to level `j`
  let I : ℕ → Cfg → Prop := fun q σ' => Lay T σ' ∧
    (∀ z : ℤ, (z < ((rb n 0 : ℕ) : ℤ)) → σ'.mem z = σ.mem z) ∧
    VOK σ'.mem (rb n 0) (ind (lev T q).1) ∧ VOK σ'.mem (rb n 1) (lev T q).2 ∧
    σ'.regs 610 = o ∧ σ'.regs 220 = (cur T o).length
  have hSLev : ∀ r ∈ [1, 2, 200, 201, 202, 203, 204, 205, 206, 220, 610, 613, 615], r ∉ SLev := by
    intro r hr hm
    rw [mem_SLev] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    omega
  refine r_seq (r_mono (r_for 615 613 616 617 (.seq levelProg advProg) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) j (5000 * (n + 1) ^ 3 + 300 * (n + 1) ^ 2)
    I σ4 (by rw [hf4 613 (by unfold SRes; decide), e613]) ?_ ?_
    (fun k σ' => k ≤ j * (5000 * (n + 1) ^ 3 + 300 * (n + 1) ^ 2 + 5) + 3 ∧ I j σ')
    (fun k σ' hk hI => ⟨hk, hI⟩)) fun k5 σ5 ⟨hk5, hl5, hm5, hS5, hd5, h6105, h2205⟩ => ?_)
  · intro a b
    refine ⟨hl4.fr (Sc := [615, 616, 617]) T (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [update_apply, hr.1, hr.2.1, hr.2.2, if_false]) (by unfold LayRegs; decide),
      fun z hz => by
        show σ4.mem z = σ.mem z
        rw [hm4 z (by omega), hM3], hS4, hd4, ?_, ?_⟩
    · simp only [update_apply, show (610 : ℕ) ≠ 616 by decide, show (610 : ℕ) ≠ 615 by decide,
        if_false]
      rw [hf4 610 (by unfold SRes; decide), hf03 610 (by decide), h610]
    · simp only [update_apply, show (220 : ℕ) ≠ 616 by decide, show (220 : ℕ) ≠ 615 by decide,
        if_false]
      rw [hf4 220 (by unfold SRes; decide), hf03 220 (by decide), h220]
  · intro q hq σ' ⟨hl', hm', hS', hd', h610', h220'⟩ hV hN
    obtain ⟨hP', -⟩ := hlow σ'.mem hm'
    refine r_seq (r_mono (h_levelProg T σ' hl' (lev T q).1 (lev T q).2 hS' hd' hP')
      fun k6 σ6 ⟨hk6, hf6, hm6, hLev⟩ => ?_)
    refine r_mono (h_advProg T σ6 (lev T q).1 (lev T q).2 hLev)
      fun k7 σ7 ⟨hk7, hf7, hm7, hS7, hd7⟩ => ⟨by omega, ?_, ?_, fun a b e => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [hf7 615 (by unfold SAdv SAF; decide), hf6 615 (hSLev 615 (by simp)), hV]
    · rw [hf7 613 (by unfold SAdv SAF; decide), hf6 613 (hSLev 613 (by simp)), hN]
    · refine (hLev.lay.fr T hf7 (by unfold LayRegs SAdv SAF; decide)).fr (Sc := [615, 616, 617]) T
        (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [update_apply, hr.1, hr.2.1, hr.2.2, if_false])
        (by unfold LayRegs; decide)
    · intro z hz
      show σ7.mem z = σ.mem z
      rw [hm7 z (by unfold rb at hz ⊢; push_cast at hz ⊢; omega),
        hm6 z (by unfold rb at hz ⊢; push_cast at hz ⊢; omega), hm' z hz]
    · show VOK σ7.mem (rb n 0) (ind (lev T (q + 1)).1)
      exact hS7
    · show VOK σ7.mem (rb n 1) (lev T (q + 1)).2
      exact hd7
    · simp only [update_apply, show (610 : ℕ) ≠ 616 by decide, show (610 : ℕ) ≠ 615 by decide,
        show (610 : ℕ) ≠ 617 by decide, if_false]
      rw [hf7 610 (by unfold SAdv SAF; decide), hf6 610 (hSLev 610 (by simp)), h610']
    · simp only [update_apply, show (220 : ℕ) ≠ 616 by decide, show (220 : ℕ) ≠ 615 by decide,
        show (220 : ℕ) ≠ 617 by decide, if_false]
      rw [hf7 220 (by unfold SAdv SAF; decide), hf6 220 (hSLev 220 (by simp)), h220']
  -- the level `j`, then the walk
  obtain ⟨hP5, hB5⟩ := hlow σ5.mem hm5
  refine r_seq (r_mono (h_levelProg T σ5 hl5 (lev T j).1 (lev T j).2 hS5 hd5 hP5)
    fun k6 σ6 ⟨hk6, hf6, hm6, hLev⟩ => ?_)
  obtain ⟨hG, hWn⟩ := gstep_cur T o ho
  rw [← hj] at hG hWn
  refine r_mono (h_build T σ6 (lev T j).1 (lev T j).2 hLev (cur T o)
    (by rw [hf6 220 (hSLev 220 (by simp)), h2205])
    (fun i hi => by rw [hm6 _ (by unfold rb; push_cast; omega)]; exact hB5 i hi) hWn (Lm0 n)
    (cur_len T o) (by rw [hG]; exact cur_len T (o + 1)))
    fun k7 σ7 ⟨hk7, hf7, hB7, h2207, hm7⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := cost_outer n j (by omega)
    have hkb : k6 ≤ 5000 * (n + 1) ^ 3 := hk6
    omega
  · exact hLev.lay.fr T hf7 (by unfold LayRegs SBuild STR STB SFI SCR SUP SBP SBK SD SAA; decide)
  · intro w
    have := w.isLt
    have e1 : ∀ z : ℤ, 0 ≤ z → z < ((rb n 0 : ℕ) : ℤ) → σ7.mem z = σ5.mem z := fun z hz hz' => by
      rw [hm7 z hz (by unfold rb at hz' ⊢; push_cast at hz' ⊢; omega),
        hm6 z (by unfold rb at hz' ⊢; push_cast at hz' ⊢; omega)]
    rw [e1 _ (by positivity) (by unfold rb; push_cast; omega),
      e1 _ (by positivity) (by unfold rb; push_cast; omega)]
    exact hP5 w
  · have e1 : (610 : ℕ) ∉ SBuild := by
      unfold SBuild STR STB SFI SCR SUP SBP SBK SD SAA; decide
    rw [hf7 610 e1, hf6 610 (hSLev 610 (by simp)), h6105]
  · rw [← hG]; exact hB7
  · rw [h2207, hG]

/-- The whole program. -/
theorem h_prog :
    Runs prog13 (Cfg.init (treeInput T (fun _ => 0) [])) (fun k σ' =>
      k ≤ 400000 * (n + 1) ^ 9 ∧
      σ'.mem (-1) = ((walkFn T T.edges (d0 T)).length : ℝ) ∧
      ∀ i : Fin (walkFn T T.edges (d0 T)).length,
        σ'.mem (-2 - (i.val : ℤ)) = (((walkFn T T.edges (d0 T)).get i).val : ℝ)) := by
  have hn : 0 < n := Fin.pos T.root
  refine r_seq (r_mono (h_init T) fun k1 σ1 ⟨hk1, hl1, hm1, h2201⟩ => ?_)
  let I : ℕ → Cfg → Prop := fun o σ' => Lay T σ' ∧ ParOK T σ'.mem ∧
    BufOK T σ'.mem (cur T o) ∧ σ'.regs 220 = (cur T o).length
  refine r_seq (r_mono (r_for 610 1 611 612 outerBody (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) n (300000 * (n + 1) ^ 8) I σ1 hl1.h1 ?_ ?_
    (fun k σ' => k ≤ n * (300000 * (n + 1) ^ 8 + 5) + 3 ∧ I n σ')
    (fun k σ' hk hI => ⟨hk, hI⟩)) fun k2 σ2 ⟨hk2, hl2, hP2, hB2, h2202⟩ => ?_)
  · intro a b
    refine ⟨hl1.fr (Sc := [610, 611, 612]) T (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [update_apply, hr.1, hr.2.1, hr.2.2, if_false]) (by unfold LayRegs; decide),
      fun w => by
        have := w.isLt
        simp only [hm1]
        exact ⟨ti_parent T _ _ w, ti_W T _ _ w⟩, fun i hi => by simp [cur] at hi, ?_⟩
    simp only [update_apply, show (220 : ℕ) ≠ 611 by decide, show (220 : ℕ) ≠ 610 by decide,
      if_false, h2201]
    simp [cur]
  · intro o ho σ ⟨hl, hP, hB, h220⟩ hV hN
    refine r_mono (h_outerBody T σ hl hP o ho hV hB h220)
      fun k σ' ⟨hk, hl', hP', h610', hB', h220'⟩ => ⟨hk, h610', hl'.h1, fun a b e => ⟨?_, ?_, ?_, ?_⟩⟩
    · exact hl'.fr (Sc := [610, 611, 612]) T (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [update_apply, hr.1, hr.2.1, hr.2.2, if_false]) (by unfold LayRegs; decide)
    · exact hP'
    · exact hB'
    · simp only [update_apply, show (220 : ℕ) ≠ 611 by decide, show (220 : ℕ) ≠ 610 by decide,
        show (220 : ℕ) ≠ 612 by decide, if_false]
      exact h220'
  -- output the length
  have hcn : cur T n = walkFn T T.edges (d0 T) := by
    unfold cur; rw [if_neg (by omega), Nat.sub_self]; rfl
  rw [hcn] at hB2 h2202
  refine r_seq (r_pset (r_store ⟨?_, ?_, ?_⟩))
  · have := cost_total n (300000 * (n + 1) ^ 8) le_rfl
    omega
  · simp only [update_apply]
    simp [h2202]
  · intro i
    simp only [update_apply]
    rw [if_neg (by simp; omega)]
    rw [hB2 i.val i.isLt]
    simp [Tree.vertexAt, List.getD_eq_getElem?_getD]

end OnlineTransportation1195.Dev.T13.PartPR
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.T13.PartPR
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
  OnlineTransportation1195.Dev.T13 OnlineTransportation1195.Dev.RL.Lib Function
/-! ## The stub -/
theorem algo13 : ∃ (prog : Stmt) (C p : ℕ), 0 < C ∧
    ∀ (n : ℕ) (T : Tree n),
      ∃ (k : ℕ) (σ : Cfg), Exec prog (Cfg.init (treeInput T (fun _ => 0) [])) k σ ∧
        k ≤ C * (n + 1) ^ p ∧
        σ.mem (-1) = ((walkFn T T.edges (d0 T)).length : ℝ) ∧
        ∀ i : Fin (walkFn T T.edges (d0 T)).length,
          σ.mem (-2 - (i.val : ℤ)) = (((walkFn T T.edges (d0 T)).get i).val : ℝ) := by
  refine ⟨prog13, 400000, 9, by norm_num, fun n T => ?_⟩
  obtain ⟨k, σ, hE, hk, h1, h2⟩ := h_prog T
  exact ⟨k, σ, hE, hk, h1, h2⟩

end OnlineTransportation1195.Dev.T13.PartPR
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.T13
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.T31 OnlineTransportation1195.Dev.RL
variable {n : ℕ}
alias algo13 := OnlineTransportation1195.Dev.T13.PartPR.algo13

theorem main : ∃ (P : SmaleNinth.RAMProgram) (C power : ℕ),
      RationalProgram P ∧ 0 < C ∧
      ∀ (n : ℕ) (T : Tree n), T.Monotone T.W →
        ∃ (fuel : ℕ) (L : List (Fin n)),
          fuel ≤ C * (n + 1) ^ power ∧ L.length ≤ C * (n + 1) ^ power ∧
          PositiveDivisions P (treeInput T (fun _ => 0) []) fuel ∧
          SmaleNinth.RAMHaltedWith P
            (SmaleNinth.RAMRun P (treeInput T (fun _ => 0) []) fuel) true ∧
          OutputsWalk (SmaleNinth.RAMRun P (treeInput T (fun _ => 0) []) fuel) L ∧
          T.TotalDeadlines L (fun e => (2 * (n : ℝ) - 3) * T.W e) := by
  obtain ⟨prog, C, p, hC, h⟩ := algo13
  refine ⟨program prog, C * 8, max p 2, Comp.program_rational prog, by omega, ?_⟩
  intro n T hM
  obtain ⟨k, σ, hE, hk, hlen, hout⟩ := h n T
  obtain ⟨h1, h2, h3⟩ := Comp.program_correct prog _ k σ hE
  have hpow : (n + 1) ^ p ≤ (n + 1) ^ max p 2 := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have hpow2 : (n + 1) ^ 2 ≤ (n + 1) ^ max p 2 := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  refine ⟨k, walkFn T T.edges (d0 T), ?_, ?_, h1, h2, ?_, walk_ok T hM⟩
  · calc k ≤ C * (n + 1) ^ p := hk
      _ ≤ C * 8 * (n + 1) ^ max p 2 := by
        have := Nat.mul_le_mul_left C hpow
        nlinarith
  · have hl := walkFn_length T T.edges (le_refl _) (d0 T)
    have hc : T.edges.card ≤ n := by rw [edges_card]; omega
    calc (walkFn T T.edges (d0 T)).length ≤ (T.edges.card + 1) * (5 * n + 2) := hl
      _ ≤ 8 * (n + 1) ^ 2 := by nlinarith
      _ ≤ C * 8 * (n + 1) ^ max p 2 := by nlinarith
  · refine ⟨by rw [h3]; exact hlen, fun i => by rw [h3]; exact hout i⟩

end OnlineTransportation1195.Dev.T13
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Main
theorem chk_weighted_tree_walk_deadlines :
    ∃ (P : SmaleNinth.RAMProgram) (C power : ℕ),
      RationalProgram P ∧ 0 < C ∧
      ∀ (n : ℕ) (T : Tree n), T.Monotone T.W →
        ∃ (fuel : ℕ) (L : List (Fin n)),
          fuel ≤ C * (n + 1) ^ power ∧ L.length ≤ C * (n + 1) ^ power ∧
          PositiveDivisions P (treeInput T (fun _ => 0) []) fuel ∧
          SmaleNinth.RAMHaltedWith P
            (SmaleNinth.RAMRun P (treeInput T (fun _ => 0) []) fuel) true ∧
          OutputsWalk (SmaleNinth.RAMRun P (treeInput T (fun _ => 0) []) fuel) L ∧
          T.TotalDeadlines L (fun e => (2 * (n : ℝ) - 3) * T.W e) :=
  OnlineTransportation1195.Dev.T13.main

end OnlineTransportation1195.Main
end

theorem solution : type_of% @OnlineTransportation1195.Main.chk_weighted_tree_walk_deadlines := @OnlineTransportation1195.Main.chk_weighted_tree_walk_deadlines

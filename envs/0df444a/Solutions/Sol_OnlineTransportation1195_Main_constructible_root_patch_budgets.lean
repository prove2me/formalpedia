-- Prove2me | solution 1 for OnlineTransportation1195.Main.constructible_root_patch_budgets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T19:12:06.379709+00:00
-- url     : https://prove2.me/submissions/1b1d1b66-5d6e-4b03-8fb1-48def32b4f0d

import Theorems.Thm_OnlineTransportation1195_Main_strict_red_weight_budget
import Theorems.Thm_OnlineTransportation1195_Main_root_patch_normalization_iff
import Theorems.Thm_OnlineTransportation1195_Main_detour_budget_inequality
import Definitions.Def_OnlineTransportation1195_Main_Computation

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.RAM
open OnlineTransportation1195.Main SmaleNinth
/-!
Blueprint for Lemma 3.3 (`constructible_root_patch_budgets`), q419: a structured language with an
exact-cost big-step semantics, compiled to `SmaleNinth.RAMProgram`.
-/
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

end OnlineTransportation1195.Dev.RAM
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.RAM.PartF
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth
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

end OnlineTransportation1195.Dev.RAM.PartF
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.RAM
open OnlineTransportation1195.Main SmaleNinth
/-! ## Part F: compiler correctness -/
alias program_rational := OnlineTransportation1195.Dev.RAM.PartF.program_rational

end OnlineTransportation1195.Dev.RAM
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.RAM.PartF
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth
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

end OnlineTransportation1195.Dev.RAM.PartF
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.RAM
open OnlineTransportation1195.Main SmaleNinth
alias program_correct := OnlineTransportation1195.Dev.RAM.PartF.program_correct

end OnlineTransportation1195.Dev.RAM
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

end OnlineTransportation1195.Dev.RAM.PartM
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.RAM
open OnlineTransportation1195.Main SmaleNinth
/-! ## Part M: the mathematics of the search -/
alias cand_exists := OnlineTransportation1195.Dev.RAM.PartM.cand_exists

/-- The largest breakpoint `d e` (or `0`) at which `F` is still at most `r`. -/
noncomputable def betaLo {n : ℕ} (T : Tree n) (d : Fin n → ℝ) (r : ℝ) : ℝ :=
  (insert 0 ((T.edges.filter (fun e => T.F d (d e) ≤ r)).image d)).max' (Finset.insert_nonempty _ _)

/-- The solution of `F s = r` on the linear piece of `F` starting at `betaLo`. -/
noncomputable def sOf {n : ℕ} (T : Tree n) (d : Fin n → ℝ) (r : ℝ) : ℝ :=
  (r - ∑ e ∈ T.edges.filter (fun e => d e ≤ betaLo T d r), T.W e) /
    ∑ e ∈ T.edges.filter (fun e => betaLo T d r < d e), T.W e / d e

end OnlineTransportation1195.Dev.RAM
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.RAM.PartM
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth
variable {n : ℕ}
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

end OnlineTransportation1195.Dev.RAM.PartM
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.RAM
open OnlineTransportation1195.Main SmaleNinth
alias sOf_spec := OnlineTransportation1195.Dev.RAM.PartM.sOf_spec

end OnlineTransportation1195.Dev.RAM
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.RAM.PartM
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth
variable {n : ℕ}
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
namespace OnlineTransportation1195.Dev.RAM
open OnlineTransportation1195.Main SmaleNinth
alias budget_of := OnlineTransportation1195.Dev.RAM.PartM.budget_of

end OnlineTransportation1195.Dev.RAM
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
/-! ## The whole program -/
/-- `M[-1] := s`, `M[-2] := t`. -/
def output : Stmt :=
  .seq (.pset 1 (-1)) (.seq (.store 1 91) (.seq (.pset 1 (-2)) (.store 1 70)))

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth
open Function
/-! ## Weakest-precondition style runs -/
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

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth
open Function
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
theorem f_const {d : ℕ} {q : ℚ}
    (h : ∀ σ' : Cfg, σ'.regs = update σ.regs d (q : ℝ) → σ'.mem = σ.mem → Q 1 σ') :
    Runs (.const d q) σ Q := r_const (h _ rfl rfl)

theorem f_add {d i j : ℕ}
    (h : ∀ σ' : Cfg, σ'.regs = update σ.regs d (σ.regs i + σ.regs j) → σ'.mem = σ.mem → Q 1 σ') :
    Runs (.add d i j) σ Q := r_add (h _ rfl rfl)

theorem f_sub {d i j : ℕ}
    (h : ∀ σ' : Cfg, σ'.regs = update σ.regs d (σ.regs i - σ.regs j) → σ'.mem = σ.mem → Q 1 σ') :
    Runs (.sub d i j) σ Q := r_sub (h _ rfl rfl)

theorem f_mul {d i j : ℕ}
    (h : ∀ σ' : Cfg, σ'.regs = update σ.regs d (σ.regs i * σ.regs j) → σ'.mem = σ.mem → Q 1 σ') :
    Runs (.mul d i j) σ Q := r_mul (h _ rfl rfl)

theorem f_div {d i j : ℕ} (hj : 0 < σ.regs j)
    (h : ∀ σ' : Cfg, σ'.regs = update σ.regs d (σ.regs i / σ.regs j) → σ'.mem = σ.mem → Q 1 σ') :
    Runs (.div d i j) σ Q := r_div hj (h _ rfl rfl)

theorem f_ifle {i : ℕ} {a b : Stmt} (ht : σ.regs i ≤ 0 → Runs a σ (fun k σ' => Q (k + 1) σ'))
    (hf : ¬ σ.regs i ≤ 0 → Runs b σ (fun k σ' => Q (k + 2) σ')) : Runs (.ifle i a b) σ Q :=
  r_ifle ht hf

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth
open Function
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

/-- `d := M[-3 - m]`. -/
def ldx (d r : ℕ) : Stmt := .seq (mov 100 r) (.seq (seekCore (-3) false) (.load d 1))

theorem r_ldx (d r : ℕ) (hr : r ≠ 100) (σ : Cfg) (m : ℕ) (hm : σ.regs r = m)
    (Q : ℕ → Cfg → Prop)
    (hQ : ∀ k, k ≤ 4 * m + 6 → ∀ a b, ∀ σ' : Cfg,
      σ'.regs = update (update (update σ.regs 100 a) 101 b) d (σ.mem (-3 - m)) →
      σ'.mem = σ.mem → Q k σ') :
    Runs (ldx d r) σ Q := by
  refine r_seq (r_mov (Ne.symm hr) (r_seq (r_seekCore _ false _ m (by simp [hm]) _
    (fun k hk a b => r_load ?_))))
  refine hQ (2 + (k + 1)) (by omega) a b _ ?_ (by simp)
  funext j; simp only [update_apply]; split_ifs <;> simp_all [sgn, sub_eq_add_neg]

/-- `M[-3 - m] := s`. -/
def stx (r s : ℕ) : Stmt := .seq (mov 100 r) (.seq (seekCore (-3) false) (.store 1 s))

theorem r_stx (r s : ℕ) (hr : r ≠ 100) (hs0 : s ≠ 100) (hs1 : s ≠ 101) (σ : Cfg) (m : ℕ)
    (hm : σ.regs r = m) (Q : ℕ → Cfg → Prop)
    (hQ : ∀ k, k ≤ 4 * m + 6 → ∀ a b, ∀ σ' : Cfg,
      σ'.regs = update (update σ.regs 100 a) 101 b →
      σ'.mem = update σ.mem (-3 - m) (σ.regs s) → Q k σ') :
    Runs (stx r s) σ Q := by
  refine r_seq (r_mov (Ne.symm hr) (r_seq (r_seekCore _ false _ m (by simp [hm]) _
    (fun k hk a b => r_store ?_))))
  refine hQ (2 + (k + 1)) (by omega) a b _ ?_ ?_
  · funext j; simp only [update_apply]; split_ifs <;> simp_all
  · simp [update_apply, hs0, hs1, sgn, sub_eq_add_neg]

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

/-- `d := M[3 + 3 N + m]` (entry `m` of the list; `N` in register `rn`). -/
def ldL (d rn r : ℕ) : Stmt :=
  .seq (.const 101 3) (.seq (.mul 100 101 rn) (.seq (.add 100 100 r) (.seq (.add 100 100 101)
    (.seq (seekCore 0 true) (.load d 1)))))

theorem r_ldL (d rn r : ℕ) (hr0 : r ≠ 100) (hr : r ≠ 101) (hrn : rn ≠ 101) (σ : Cfg) (N m : ℕ)
    (hN : σ.regs rn = N) (hm : σ.regs r = m)
    (Q : ℕ → Cfg → Prop)
    (hQ : ∀ k, k ≤ 4 * (3 + 3 * N + m) + 8 → ∀ a b, ∀ σ' : Cfg,
      σ'.regs = update (update (update σ.regs 100 a) 101 b) d (σ.mem ((3 + 3 * N + m : ℕ) : ℤ)) →
      σ'.mem = σ.mem → Q k σ') :
    Runs (ldL d rn r) σ Q := by
  refine r_seq (r_const (r_seq (r_mul (r_seq (r_add (r_seq (r_add (r_seq
    (r_seekCore 0 true _ (3 + 3 * N + m) ?_ _ (fun k hk a b => r_load ?_))))))))))
  · simp [update_apply, hr, hm, hrn, hN, hr0]; ring
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

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth
open Function
variable {n : ℕ}
/-! ## The input tape -/
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

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth
open Function
variable {n : ℕ}
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

theorem ti_d (v : Fin n) : treeInput T d L ((4 + 3 * v.val : ℕ) : ℤ) = d v := by
  have := ti_vert T d L v 2 (by norm_num); simpa [show 2 + 2 = 4 by rfl] using this

theorem ti_len : treeInput T d L ((2 + 3 * n : ℕ) : ℤ) = L.length := by
  rw [ti_cells]
  rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by simp),
    List.getElem?_append_right (by rw [flat_len]; simp)]
  simp only [flat_len, List.length_cons, List.length_nil]
  rw [show 2 + 3 * n - 2 - 3 * n = 0 by omega]
  simp

theorem ti_L (i : ℕ) (hi : i < L.length) :
    treeInput T d L ((3 + 3 * n + i : ℕ) : ℤ) = (T.vertexAt L i).val := by
  rw [ti_cells]
  rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_right (by rw [flat_len]; simp; omega)]
  simp only [flat_len, List.length_cons, List.length_nil]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_cons, List.length_nil]
  rw [show 3 + 3 * n + i - 2 - 3 * n - 1 = i by omega]
  simp [Tree.vertexAt, List.getD_eq_getElem?_getD, hi]

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth
open Function
variable {n : ℕ} (T : Tree n)
/-! ## Facts about DFS lists -/
theorem mem_edges_iff (e : Fin n) : e ∈ T.edges ↔ e ≠ T.root := by
  simp [Tree.edges]

theorem downAt_unique (L : List (Fin n)) (hL : T.DFS L) (e : Fin n)
    (he : e ∈ T.edges) (i i' : ℕ) (hi : T.DownAt L e i) (hi' : T.DownAt L e i') : i = i' := by
  have h1 := (hL.2.2 e he).1
  have h2 := Finset.card_le_one.mp h1.le ⟨i, by have := hi.2.1; omega⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) ⟨i', by have := hi'.2.1; omega⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩)
  exact congrArg Fin.val h2

theorem upAt_unique (L : List (Fin n)) (hL : T.DFS L) (e : Fin n)
    (he : e ∈ T.edges) (i i' : ℕ) (hi : T.UpAt L e i) (hi' : T.UpAt L e i') : i = i' := by
  have h1 := (hL.2.2 e he).2
  have h2 := Finset.card_le_one.mp h1.le ⟨i, by have := hi.2.1; omega⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) ⟨i', by have := hi'.2.1; omega⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩)
  exact congrArg Fin.val h2

theorem dfs_len (L : List (Fin n)) (hL : T.DFS L) : 1 ≤ L.length ∧ L.length ≤ 2 * n := by
  have hne : L ≠ [] := by
    intro h; have := hL.1.1; rw [h] at this; simp at this
  have h1 : 1 ≤ L.length := by
    cases L with
    | nil => exact absurd rfl hne
    | cons a l => simp
  refine ⟨h1, ?_⟩
  let φ : ℕ → Fin n × Bool := fun i =>
    if T.vertexAt L (i + 1) ≠ T.root ∧ T.parent (T.vertexAt L (i + 1)) = T.vertexAt L i
    then (T.vertexAt L (i + 1), true) else (T.vertexAt L i, false)
  have hmap : ∀ i ∈ Finset.range (L.length - 1), φ i ∈ T.edges ×ˢ (Finset.univ : Finset Bool) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hadj := hL.1.2 i (by omega)
    simp only [φ]
    split_ifs with h
    · simp [mem_edges_iff, h.1]
    · rcases hadj with h' | h'
      · exact absurd h' h
      · simp [mem_edges_iff, h'.1]
  have hinj : Set.InjOn φ (Finset.range (L.length - 1)) := by
    intro i hi i' hi' heq
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    have hadj := hL.1.2 i (by omega)
    have hadj' := hL.1.2 i' (by omega)
    simp only [φ] at heq
    by_cases h : T.vertexAt L (i + 1) ≠ T.root ∧ T.parent (T.vertexAt L (i + 1)) = T.vertexAt L i <;>
      by_cases h' : T.vertexAt L (i' + 1) ≠ T.root ∧
        T.parent (T.vertexAt L (i' + 1)) = T.vertexAt L i' <;>
      first
        | rw [if_pos h, if_pos h'] at heq | rw [if_pos h, if_neg h'] at heq
        | rw [if_neg h, if_pos h'] at heq | rw [if_neg h, if_neg h'] at heq
    · simp only [Prod.mk.injEq, and_true] at heq
      have he : T.vertexAt L (i + 1) ∈ T.edges := (mem_edges_iff T _).mpr h.1
      exact downAt_unique T L hL _ he i i' ⟨h.1, by omega, h.2.symm, rfl⟩
        ⟨h.1, by omega, by rw [heq]; exact h'.2.symm, heq.symm⟩
    · simp at heq
    · simp at heq
    · simp only [Prod.mk.injEq, and_true] at heq
      have hu : T.Adj (T.vertexAt L i) (T.vertexAt L (i + 1)) := hadj
      have hu' : T.Adj (T.vertexAt L i') (T.vertexAt L (i' + 1)) := hadj'
      rcases hu with hu | hu
      · exact absurd hu h
      rcases hu' with hu' | hu'
      · exact absurd hu' h'
      have he : T.vertexAt L i ∈ T.edges := (mem_edges_iff T _).mpr hu.1
      exact upAt_unique T L hL _ he i i' ⟨hu.1, by omega, rfl, hu.2.symm⟩
        ⟨hu.1, by omega, heq.symm, by rw [heq]; exact hu'.2.symm⟩
  have := Finset.card_le_card_of_injOn φ hmap hinj
  rw [Finset.card_range, Finset.card_product, Finset.card_univ, Fintype.card_bool] at this
  have hc : T.edges.card = n - 1 := by
    unfold Tree.edges
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  rw [hc] at this
  have : 0 < n := Fin.pos T.root
  omega

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
variable {n : ℕ} (T : Tree n) (L : List (Fin n))
/-! ## Phase X: the first downward prefix costs `x` -/
/-- First down-crossing of `e` among the indices `< m`. -/
noncomputable def fd (e : Fin n) (m : ℕ) : Option ℕ :=
  (List.range m).find? (fun i => decide (T.DownAt L e i))

/-- The value of `x e` after scanning the indices `< m`. -/
noncomputable def xUp (e : Fin n) (m : ℕ) : ℝ :=
  match fd T L e m with
  | some i => T.downPrefix L i
  | none => 0

/-- Running downward cost over the first `m` steps. -/
noncomputable def accu (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, T.downStep (T.vertexAt L j) (T.vertexAt L (j + 1))

theorem fd_succ (e : Fin n) (m : ℕ) : fd T L e (m + 1) =
    (fd T L e m).or (if T.DownAt L e m then some m else none) := by
  unfold fd
  rw [List.range_succ, List.find?_append, List.find?_singleton]
  simp

theorem fd_zero (e : Fin n) : fd T L e 0 = none := by simp [fd]

theorem x_eq_xUp (e : Fin n) : T.x L e = xUp T L e (L.length - 1) := by
  unfold Tree.x xUp
  have : (List.range L.length).find? (fun i => decide (T.DownAt L e i)) = fd T L e (L.length - 1) := by
    rcases Nat.eq_zero_or_pos L.length with h | h
    · rw [h]; rfl
    · have e1 : L.length = L.length - 1 + 1 := by omega
      conv_lhs => rw [e1]
      rw [← fd, fd_succ, if_neg]
      · simp
      · intro hd; have := hd.2.1; omega
  rw [this]
  cases fd T L e (L.length - 1) <;> rfl

theorem cast_val_eq (a b : Fin n) : ((a.val : ℝ) = (b.val : ℝ)) ↔ a = b := by
  rw [Nat.cast_inj, Fin.val_inj]

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
/-! ### The program -/

/-- One step `m` of the scan of the list for the vertex `v` (in register `10`). -/
def xInner : Stmt :=
  .seq (ldL 20 1 13) (.seq (.const 21 1) (.seq (.add 22 13 21) (.seq (ldL 23 1 22)
  (.seq (eqT 24 23 2) (.seq (ldIn 25 2 23) (.seq (eqT 26 25 20) (.seq (ldIn 27 3 23)
  (.seq (.const 21 1) (.seq (.sub 29 21 24) (.seq (.mul 29 29 26)
  (.seq (.mul 30 29 27) (.seq (.add 16 16 30)
  (.seq (eqT 28 23 10) (.seq (.mul 31 29 28)
  (.seq (.sub 32 21 17) (.seq (.mul 31 31 32)
  (.seq (.sub 33 16 18) (.seq (.mul 33 33 31) (.seq (.add 18 18 33)
  (.add 17 17 31))))))))))))))))))))

/-- Compute `x v` for the vertex `v` in register `10` and store it. -/
def xOuter : Stmt :=
  .seq (.const 16 0) (.seq (.const 17 0) (.seq (.const 18 0)
    (.seq (forLoop 13 19 14 15 xInner) (stx 10 18))))

/-- Load `n`, the root and `|L| - 1`, then compute all `x v`. -/
def phaseX : Stmt :=
  .seq (.pset 1 0) (.seq (.load 1 1) (.seq (.pinc 1) (.seq (.load 2 1)
    (.seq (ldIn 3 2 1) (.seq (.const 21 1) (.seq (.sub 19 3 21)
    (forLoop 10 1 11 12 xOuter)))))))

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
variable {n : ℕ} (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n))
/-- The invariant of the inner loop. -/
def IXi (M : ℤ → ℝ) (v : Fin n) (j : ℕ) (σ : Cfg) : Prop :=
  σ.mem = M ∧ σ.regs 1 = n ∧ σ.regs 2 = T.root.val ∧ σ.regs 10 = v.val ∧
    σ.regs 19 = ((L.length - 1 : ℕ) : ℝ) ∧
    σ.regs 16 = accu T L j ∧ σ.regs 17 = (if (fd T L v j).isSome then 1 else 0) ∧
    σ.regs 18 = xUp T L v j

theorem xInner_spec (hL : T.DFS L) (M : ℤ → ℝ)
    (hM : ∀ z : ℤ, 0 ≤ z → M z = treeInput T d L z) (v : Fin n) (m : ℕ)
    (hm : m < L.length - 1) (σ : Cfg) (hI : IXi T L M v m σ) (h13 : σ.regs 13 = m) :
    Runs xInner σ (fun k σ' => k ≤ 16 * (3 + 3 * n + L.length) + 80 ∧
      σ'.regs 13 = m ∧ σ'.regs 19 = ((L.length - 1 : ℕ) : ℝ) ∧
      ∀ a b e, IXi T L M v (m + 1)
        ⟨update (update (update σ'.regs 15 a) 13 b) 14 e, σ'.ptrs, σ'.mem⟩) := by
  obtain ⟨hmem, h1, h2, h10, h19, h16, h17, h18⟩ := hI
  set u := T.vertexAt L m with hu_def
  set w := T.vertexAt L (m + 1) with hw_def
  have hu : M ((3 + 3 * n + m : ℕ) : ℤ) = (u.val : ℝ) := by
    rw [hM _ (by positivity), ti_L T d L m (by omega)]
  have hw : M ((3 + 3 * n + (m + 1) : ℕ) : ℤ) = (w.val : ℝ) := by
    rw [hM _ (by positivity), ti_L T d L (m + 1) (by omega)]
  have hpw : M ((2 + 3 * w.val : ℕ) : ℤ) = ((T.parent w).val : ℝ) := by
    rw [hM _ (by positivity), ti_parent]
  have hWw : M ((3 + 3 * w.val : ℕ) : ℤ) = T.W w := by
    rw [hM _ (by positivity), ti_W]
  have hwn := w.isLt
  clear_value u w
  have hw' : M (3 + 3 * (n : ℤ) + ((m : ℤ) + 1)) = (w.val : ℝ) := by
    rw [← hw]; push_cast; rfl
  refine r_seq (r_ldL 20 1 13 (by decide) (by decide) (by decide) σ n m h1 h13 _
    (fun k1 hk1 a1 b1 σ1 r1 m1 => ?_))
  refine r_seq (f_const fun σ2 r2 m2 => r_seq (f_add fun σ3 r3 m3 => r_seq ?_))
  refine r_ldL 23 1 22 (by decide) (by decide) (by decide) _ n (m + 1)
    (by simp [r1, r2, r3, h1]) (by simp [r1, r2, r3, h13]) _ (fun k2 hk2 a2 b2 σ4 r4 m4 => ?_)
  refine r_seq (r_eqT 24 23 2 (by decide) (by decide) (by decide) _ _
    (fun k3 hk3 z3 σ5 r5 m5 => ?_))
  have e23 : σ5.regs 23 = (w.val : ℝ) := by simp [r1, r2, r3, r4, r5, m1, m2, m3, hmem, hw, hw']
  refine r_seq (r_ldIn 25 2 23 (by decide) _ w.val e23 _ (fun k4 hk4 a4 b4 σ6 r6 m6 => ?_))
  refine r_seq (r_eqT 26 25 20 (by decide) (by decide) (by decide) _ _
    (fun k5 hk5 z5 σ7 r7 m7 => ?_))
  refine r_seq (r_ldIn 27 3 23 (by decide) _ w.val (by simp [r6, r7, e23]) _
    (fun k6 hk6 a6 b6 σ8 r8 m8 => ?_))
  refine r_seq (f_const fun σ9 r9 m9 => r_seq (f_sub fun σ10 r10 m10 => r_seq (f_mul
    fun σ11 r11 m11 => r_seq (f_mul fun σ12 r12 m12 => r_seq (f_add fun σ13 r13 m13 => ?_)))))
  refine r_seq (r_eqT 28 23 10 (by decide) (by decide) (by decide) _ _
    (fun k7 hk7 z7 σ14 r14 m14 => ?_))
  refine r_seq (f_mul fun σ15 r15 m15 => r_seq (f_sub fun σ16 r16 m16 => r_seq (f_mul
    fun σ17 r17 m17 => r_seq (f_sub fun σ18 r18 m18 => r_seq (f_mul fun σ19 r19 m19 =>
    r_seq (f_add fun σ20 r20 m20 => f_add fun σ21 r21 m21 => ?_))))))
  refine ⟨?_, ?_, ?_, fun a b e => ?_⟩
  · have : w.val < n := hwn
    clear * - hk1 hk2 hk3 hk4 hk5 hk6 hk7 hm this
    ring_nf; ring_nf at hk1 hk2 hk4 hk6
    omega
  · simp [r21, r20, r19, r18, r17, r16, r15, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4,
      r3, r2, r1, h13]
  · simp [r21, r20, r19, r18, r17, r16, r15, r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4,
      r3, r2, r1, h19]
  have hacc : accu T L (m + 1) = accu T L m +
      ((1 - if w = T.root then 1 else 0) * if T.parent w = u then 1 else 0) * T.W w := by
    rw [accu, Finset.sum_range_succ, ← accu, ← hu_def, ← hw_def]
    unfold Tree.downStep
    by_cases hr : w = T.root <;> by_cases hp : T.parent w = u <;> simp [hr, hp]
  have hDA : T.DownAt L v m ↔ w ≠ T.root ∧ T.parent w = u ∧ w = v := by
    unfold Tree.DownAt
    rw [← hu_def, ← hw_def]
    constructor
    · rintro ⟨h1, -, h3, h4⟩; subst h4; exact ⟨h1, h3.symm, rfl⟩
    · rintro ⟨h1, h3, h4⟩; subst h4; exact ⟨h1, by omega, h3.symm, rfl⟩
  have hfd := fd_succ T L v m
  simp only [IXi, update_apply, reduceIte, Nat.reduceEqDiff, r21, r20, r19, r18, r17, r16, r15,
    r14, r13, r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, m1, m2, m3, m4, m5, m6, m7, m8,
    m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, hmem, hu, hw, hw', hpw, hWw,
    h1, h2, h10, h16, h17, h18, h19, cast_val_eq, Rat.cast_one, true_and]
  refine ⟨hacc.symm, ?_⟩
  unfold xUp
  rw [hfd]
  rcases hf : fd T L v m with _ | i
  · simp only [Option.isSome_none, Bool.false_eq_true, reduceIte, Option.none_or]
    by_cases hd : T.DownAt L v m
    · obtain ⟨hd1, hd2, rfl⟩ := hDA.mp hd
      simp only [hd, reduceIte, Option.isSome_some]
      rw [show T.downPrefix L m = accu T L (m + 1) from rfl, hacc]
      simp [hd1, hd2]
    · simp only [hd, reduceIte, Option.isSome_none]
      rw [hDA] at hd
      by_cases hr : w = T.root
      · simp [hr]
      · by_cases hp : T.parent w = u
        · have : w ≠ v := fun h => hd ⟨hr, hp, h⟩
          simp [hr, hp, this]
        · simp [hr, hp]
  · simp

/-- The invariant of the outer loop. -/
def IXo (m : ℕ) (σ : Cfg) : Prop :=
  σ.regs 1 = n ∧ σ.regs 2 = T.root.val ∧ σ.regs 19 = ((L.length - 1 : ℕ) : ℝ) ∧
    (∀ z : ℤ, 0 ≤ z → σ.mem z = treeInput T d L z) ∧
    ∀ v : Fin n, v.val < m → σ.mem (-3 - (v.val : ℤ)) = T.x L v

/-- Cost bound of one outer iteration, in terms of `A = 3 + 3 n + |L|`. -/
def cOut (A : ℕ) : ℕ := A * (16 * A + 85) + 4 * A + 12

theorem xOuter_spec (hL : T.DFS L) (m : ℕ) (hm : m < n) (σ : Cfg) (hI : IXo T d L m σ)
    (h10 : σ.regs 10 = m) :
    Runs xOuter σ (fun k σ' => k ≤ cOut (3 + 3 * n + L.length) ∧ σ'.regs 10 = m ∧
      σ'.regs 1 = n ∧ ∀ a b e, IXo T d L (m + 1)
        ⟨update (update (update σ'.regs 12 a) 10 b) 11 e, σ'.ptrs, σ'.mem⟩) := by
  obtain ⟨h1, h2, h19, hin, hx⟩ := hI
  have hlen := dfs_len T L hL
  set v : Fin n := ⟨m, hm⟩ with hv
  refine r_seq (f_const fun σ1 r1 m1 => r_seq (f_const fun σ2 r2 m2 => r_seq (f_const
    fun σ3 r3 m3 => r_seq ?_)))
  have hM3 : ∀ z : ℤ, 0 ≤ z → σ3.mem z = treeInput T d L z := by
    intro z hz; rw [m3, m2, m1]; exact hin z hz
  refine r_for 13 19 14 15 xInner (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (L.length - 1) (16 * (3 + 3 * n + L.length) + 80) (IXi T L σ3.mem v) σ3
    (by simp [r3, r2, r1, h19]) ?_ ?_ _ (fun k1 σ4 hk1 hI4 => ?_)
  · intro a b
    simp [IXi, update_apply, r3, r2, r1, h1, h2, h10, h19, accu, fd_zero, xUp, hv]
  · intro j hj σ' hI' h13 h19'
    exact xInner_spec T d L hL σ3.mem hM3 v j hj σ' hI' h13
  obtain ⟨hm4, h41, h42, h410, h419, -, -, h418⟩ := hI4
  refine r_stx 10 18 (by decide) (by decide) (by decide) σ4 m (by rw [h410, hv]) _
    (fun k2 hk2 a2 b2 σ5 r5 m5 => ⟨?_, ?_, ?_, fun a b e => ⟨?_, ?_, ?_, ?_, ?_⟩⟩)
  · have hmul : (L.length - 1) * (16 * (3 + 3 * n + L.length) + 80 + 5) ≤
        (3 + 3 * n + L.length) * (16 * (3 + 3 * n + L.length) + 85) :=
      Nat.mul_le_mul (by omega) le_rfl
    unfold cOut
    clear * - hk1 hk2 hmul hm
    omega
  · simp [r5, h410, hv]
  · simp [r5, h41]
  · simp [update_apply, r5, h41]
  · simp [update_apply, r5, h42]
  · simp [update_apply, r5, h419]
  · intro z hz
    simp only [m5, hm4]
    rw [update_of_ne (by omega), hM3 z hz]
  · intro u hu
    rw [m5, hm4, h418]
    by_cases hum : u.val = m
    · have hu' : u = v := by rw [hv]; exact Fin.ext hum
      rw [hu', show ((v.val : ℕ) : ℤ) = (m : ℤ) by rw [hv], update_self, x_eq_xUp]
    · rw [update_of_ne (by omega), m3, m2, m1]
      exact hx u (by omega)

/-- Total cost bound of phase X. -/
def cX (A : ℕ) : ℕ := A * (cOut A + 5) + 4 * A + 30

theorem phaseX_spec (hL : T.DFS L) (σ : Cfg) (hmem : σ.mem = treeInput T d L)
    (Q : ℕ → Cfg → Prop)
    (hQ : ∀ k σ', k ≤ cX (3 + 3 * n + L.length) → σ'.regs 1 = (n : ℝ) →
      σ'.regs 2 = (T.root.val : ℝ) →
      (∀ z : ℤ, 0 ≤ z → σ'.mem z = treeInput T d L z) →
      (∀ v : Fin n, σ'.mem (-3 - (v.val : ℤ)) = T.x L v) → Q k σ') :
    Runs phaseX σ Q := by
  have hlen := dfs_len T L hL
  have t0 : treeInput T d L 0 = n := by simpa using ti_zero T d L
  have t1 : treeInput T d L 1 = T.root.val := by simpa using ti_one T d L
  refine r_seq (r_pset (r_seq (r_load (r_seq (r_pinc (r_seq (r_load (r_seq ?_))))))))
  refine r_ldIn 3 2 1 (by decide) _ n (by simp [update_apply, hmem, t0]) _
    (fun k1 hk1 a1 b1 σ1 r1 m1 => ?_)
  refine r_seq (f_const fun σ2 r2 m2 => r_seq (f_sub fun σ3 r3 m3 => ?_))
  have h31 : σ3.regs 1 = (n : ℝ) := by simp [r3, r2, r1, update_apply, hmem, t0]
  have h32 : σ3.regs 2 = (T.root.val : ℝ) := by simp [r3, r2, r1, update_apply, hmem, t1]
  have h319 : σ3.regs 19 = ((L.length - 1 : ℕ) : ℝ) := by
    simp only [r3, r2, r1, update_apply, reduceIte, Nat.reduceEqDiff]
    rw [hmem, ti_len, Nat.cast_sub hlen.1]; simp
  have hM3 : ∀ z : ℤ, 0 ≤ z → σ3.mem z = treeInput T d L z := by
    intro z hz; simp [m3, m2, m1, hmem]
  refine r_for 10 1 11 12 xOuter (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) n (cOut (3 + 3 * n + L.length)) (IXo T d L) σ3 h31 ?_ ?_ _
    (fun k2 σ4 hk2 hI4 => ?_)
  · intro a b
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [update_apply, h31]
    · simp [update_apply, h32]
    · simp [update_apply, h319]
    · exact hM3
    · intro v hv; omega
  · intro m hm σ' hI h10 _
    exact xOuter_spec T d L hL m hm σ' hI h10
  obtain ⟨h41, h42, -, hin, hx⟩ := hI4
  refine hQ _ _ ?_ h41 h42 hin (fun v => hx v v.isLt)
  have hmul : n * (cOut (3 + 3 * n + L.length) + 5) ≤
      (3 + 3 * n + L.length) * (cOut (3 + 3 * n + L.length) + 5) :=
    Nat.mul_le_mul (by omega) le_rfl
  unfold cX
  generalize cOut (3 + 3 * n + L.length) = c at *
  clear * - hk1 hk2 hmul
  omega

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
/-! ## Phase E: evaluating `R`, `F`, `Rin` at a time `t` -/
/-- Registers in `S` are overwritten by `g`, the others kept from `R`. -/
def scr (S : List ℕ) (g R : ℕ → ℝ) : ℕ → ℝ := fun r => if r ∈ S then g r else R r

theorem scr_eq {S : List ℕ} {σ σ' : Cfg} {dst : ℕ} {val : ℝ}
    (hfr : ∀ r, r ≠ dst → r ∉ S → σ'.regs r = σ.regs r) (hv : σ'.regs dst = val) :
    σ'.regs = update (scr S σ'.regs σ.regs) dst val := by
  funext r
  by_cases hr : r = dst
  · subst hr; simp [hv]
  · rw [update_of_ne hr]
    unfold scr
    split_ifs with h
    · rfl
    · exact hfr r hr h

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
variable {n : ℕ} (T : Tree n)
theorem depth_iter (v : Fin n) : ∀ i, i ≤ T.depth v →
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

theorem iter_depth (v : Fin n) : T.parent^[T.depth v] v = T.root := by
  have := depth_iter T v (T.depth v) le_rfl
  by_contra hne
  have := T.depth_parent _ hne
  omega

theorem iter_ne_root (v : Fin n) (i : ℕ) (hi : i < T.depth v) : T.parent^[i] v ≠ T.root := by
  intro h
  have := depth_iter T v i hi.le
  rw [h, T.depth_root] at this
  omega

theorem depth_lt (v : Fin n) : T.depth v < n := by
  have hinj : Set.InjOn (fun i => T.parent^[i] v) (Finset.range (T.depth v + 1)) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have h1 := depth_iter T v i (by omega)
    have h2 := depth_iter T v j (by omega)
    simp only at hij
    rw [hij] at h1
    omega
  have := Finset.card_le_card_of_injOn (fun i => T.parent^[i] v) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) hinj
  simp at this
  omega

/-- Ancestor edges of `f` are exactly `parent^[i] f` for `i < depth f`. -/
theorem anc_iff (P : Fin n → Prop) (f : Fin n) :
    (∀ i < T.depth f, P (T.parent^[i] f)) ↔ (∀ a ∈ T.edges, T.IsAnc a f → P a) := by
  constructor
  · rintro h a ha ⟨i, rfl⟩
    by_cases hi : i < T.depth f
    · exact h i hi
    · exfalso
      have : T.parent^[i] f = T.root := by
        obtain ⟨j, rfl⟩ : ∃ j, i = T.depth f + j := ⟨i - T.depth f, by omega⟩
        rw [add_comm, Function.iterate_add_apply, iter_depth,
          Function.iterate_fixed T.parent_root]
      exact (mem_edges_iff T _).mp ha this
  · intro h i hi
    exact h _ ((mem_edges_iff T _).mpr (iter_ne_root T f i hi)) ⟨i, rfl⟩

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
variable {n : ℕ} (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n))
/-- The memory after phase X. -/
def MemOK (M : ℤ → ℝ) : Prop :=
  (∀ z : ℤ, 0 ≤ z → M z = treeInput T d L z) ∧ ∀ v : Fin n, M (-3 - (v.val : ℤ)) = T.x L v

/-- `dst := [d f < x f + t]` for the vertex `f` in register `r` and `t` in register `30`. -/
def isRed (dst r : ℕ) : Stmt :=
  .seq (ldIn 50 4 r) (.seq (ldx 51 r) (.seq (.add 52 51 30) (.seq (.sub 53 52 50)
    (.ifle 53 (.const dst 0) (.const dst 1)))))

def SRed : List ℕ := [50, 51, 52, 53, 100, 101]

theorem isRed_spec (dst r : ℕ) (hd : dst ∉ SRed) (hr : r ∉ SRed) (M : ℤ → ℝ)
    (hM : MemOK T d L M) (σ : Cfg) (hmem : σ.mem = M) (f : Fin n) (hf : σ.regs r = f.val)
    (t : ℝ) (ht : σ.regs 30 = t) (Q : ℕ → Cfg → Prop)
    (hQ : ∀ k, k ≤ 16 * n + 40 → ∀ g : ℕ → ℝ, ∀ σ' : Cfg,
      σ'.regs = update (scr SRed g σ.regs) dst (if d f < T.x L f + t then 1 else 0) →
      σ'.mem = σ.mem → Q k σ') :
    Runs (isRed dst r) σ Q := by
  simp only [SRed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd hr
  obtain ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩ := hd
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩ := hr
  have hfn := f.isLt
  have hdf : σ.mem ((4 + 3 * f.val : ℕ) : ℤ) = d f := by rw [hmem, hM.1 _ (by positivity), ti_d]
  have hxf : σ.mem (-3 - ((f.val : ℕ) : ℤ)) = T.x L f := by rw [hmem, hM.2]
  refine r_seq (r_ldIn 50 4 r hr5 σ f.val hf _ (fun k1 hk1 a1 b1 σ1 r1 m1 => ?_))
  refine r_seq (r_ldx 51 r hr4 σ1 f.val (by simp [r1, hf, hr0, hr4, hr5]) _
    (fun k2 hk2 a2 b2 σ2 r2 m2 => ?_))
  refine r_seq (f_add fun σ3 r3 m3 => r_seq (f_sub fun σ4 r4 m4 => f_ifle ?_ ?_))
  · intro hle
    refine f_const fun σ5 r5 m5 => ?_
    refine hQ _ (by omega) σ5.regs σ5 ?_ (by rw [m5, m4, m3, m2, m1])
    have hval : ¬ (d f < T.x L f + t) := by
      simp only [r4, r3, r2, r1, update_apply, reduceIte, Nat.reduceEqDiff, m1, hdf, hxf,
        ht] at hle
      push Not; linarith
    rw [if_neg hval]
    refine scr_eq (fun j hj hS => ?_) (by simp [r5])
    simp only [SRed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hS
    simp [r5, r4, r3, r2, r1, update_apply, hj, hS]
  · intro hle
    refine f_const fun σ5 r5 m5 => ?_
    refine hQ _ (by omega) σ5.regs σ5 ?_ (by rw [m5, m4, m3, m2, m1])
    have hval : d f < T.x L f + t := by
      simp only [r4, r3, r2, r1, update_apply, reduceIte, Nat.reduceEqDiff, m1, hdf, hxf,
        ht] at hle
      push Not at hle; linarith
    rw [if_pos hval]
    refine scr_eq (fun j hj hS => ?_) (by simp [r5])
    simp only [SRed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hS
    simp [r5, r4, r3, r2, r1, update_apply, hj, hS]

theorem mem_red (t : ℝ) (a : Fin n) (ha : a ≠ T.root) :
    a ∈ T.red d L t ↔ d a < T.x L a + t := by
  simp [Tree.red, mem_edges_iff, ha]

/-- One step of the walk to the root. -/
def pfBody : Stmt :=
  .seq (isRed 64 60) (.seq (.mul 45 45 64) (.seq (ldIn 65 2 60) (.seq (mov 60 65)
    (.seq (eqT 61 60 2) (.seq (.const 62 1) (.sub 63 62 61))))))

/-- `45 := [every edge on the root path of the vertex in register 34 is red]`. -/
def patchFlag : Stmt :=
  .seq (mov 60 34) (.seq (.const 45 1) (.seq (eqT 61 60 2) (.seq (.const 62 1)
    (.seq (.sub 63 62 61) (.whilegt 63 pfBody)))))

def SPF : List ℕ := [50, 51, 52, 53, 60, 61, 62, 63, 64, 65, 100, 101]

theorem patchFlag_spec (M : ℤ → ℝ) (hM : MemOK T d L M) (σ : Cfg) (hmem : σ.mem = M)
    (f : Fin n) (hf : σ.regs 34 = f.val) (t : ℝ) (ht : σ.regs 30 = t)
    (h2 : σ.regs 2 = T.root.val) (Q : ℕ → Cfg → Prop)
    (hQ : ∀ k, k ≤ n * (30 * n + 80) + 20 → ∀ g : ℕ → ℝ, ∀ σ' : Cfg,
      σ'.regs = update (scr SPF g σ.regs) 45
        (if ∀ i < T.depth f, T.parent^[i] f ∈ T.red d L t then 1 else 0) →
      σ'.mem = σ.mem → Q k σ') :
    Runs patchFlag σ Q := by
  let I : ℕ → Cfg → Prop := fun j σ' => σ'.mem = σ.mem ∧
    (∀ r, r ≠ 45 → r ∉ SPF → σ'.regs r = σ.regs r) ∧
    σ'.regs 60 = (T.parent^[j] f).val ∧
    σ'.regs 45 = (if ∀ i < j, T.parent^[i] f ∈ T.red d L t then 1 else 0) ∧
    σ'.regs 63 = (if T.parent^[j] f = T.root then 0 else 1)
  have hdn := depth_lt T f
  refine r_seq (r_mov (by decide) (r_seq (f_const fun σ1 r1 m1 => r_seq (r_eqT 61 60 2
    (by decide) (by decide) (by decide) _ _ (fun k2 hk2 z2 σ2 r2 m2 => r_seq (f_const
    fun σ3 r3 m3 => r_seq (f_sub fun σ4 r4 m4 => ?_)))))))
  refine r_while 63 pfBody (T.depth f) (28 * n + 56) I _ ?_ ?_ σ4 ?_ ?_
  · -- one step
    intro j hj σ' ⟨hm', hfr', h60, h45, h63⟩
    have hne := iter_ne_root T f j hj
    refine ⟨by rw [h63, if_neg hne]; norm_num, ?_⟩
    set a := T.parent^[j] f with ha_def
    have han := a.isLt
    have hda : σ'.regs 30 = t := by
      rw [hfr' 30 (by decide) (by decide), ht]
    have hd2 : σ'.regs 2 = T.root.val := by
      rw [hfr' 2 (by decide) (by decide), h2]
    have hpa : σ'.mem ((2 + 3 * a.val : ℕ) : ℤ) = (T.parent a).val := by
      rw [hm', hmem, hM.1 _ (by positivity), ti_parent]
    refine r_seq (isRed_spec T d L 64 60 (by decide) (by decide) M hM σ' (by rw [hm', hmem]) a
      h60 t hda _ (fun k1 hk1 g1 σ5 r5 m5 => ?_))
    refine r_seq (f_mul fun σ6 r6 m6 => r_seq (r_ldIn 65 2 60 (by decide) σ6 a.val
      (by simp [r6, r5, scr, SRed, h60]) _ (fun k3 hk3 a3 b3 σ7 r7 m7 => r_seq (r_mov
      (by decide) (r_seq (r_eqT 61 60 2 (by decide) (by decide) (by decide) _ _
      (fun k4 hk4 z4 σ8 r8 m8 => r_seq (f_const fun σ9 r9 m9 => f_sub fun σ10 r10 m10 =>
      ?_))))))))
    have e60 : σ10.regs 60 = ((T.parent a).val : ℝ) := by
      simp only [r10, r9, r8, r7, r6, r5, scr, SRed, update_apply, reduceIte, Nat.reduceEqDiff,
        List.mem_cons, List.not_mem_nil, or_false, or_self, false_or]
      rw [m6, m5, hpa]
    have e2 : σ10.regs 2 = (T.root.val : ℝ) := by
      simp only [r10, r9, r8, r7, r6, r5, scr, SRed, update_apply, reduceIte, Nat.reduceEqDiff,
        List.mem_cons, List.not_mem_nil, or_false, or_self, false_or, hd2]
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [m10, m9, m8, m7, m6, m5, hm']
    · intro r hr1 hr2
      simp only [SPF, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr2
      rw [← hfr' r hr1 (by simp [SPF, hr2])]
      simp [r10, r9, r8, r7, r6, r5, scr, SRed, update_apply, hr1, hr2]
    · rw [e60, Function.iterate_succ_apply']
    · simp only [r10, r9, r8, r7, r6, r5, scr, SRed, update_apply, reduceIte, Nat.reduceEqDiff,
        List.mem_cons, List.not_mem_nil, or_false, or_self, false_or, h45]
      simp only [← mem_red T d L t a hne]
      have key : (∀ i < j + 1, T.parent^[i] f ∈ T.red d L t) ↔
          (∀ i < j, T.parent^[i] f ∈ T.red d L t) ∧ a ∈ T.red d L t := by
        constructor
        · intro h; exact ⟨fun i hi => h i (by omega), h j (by omega)⟩
        · rintro ⟨h1, h2⟩ i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · exact h1 i hi
          · exact h2
      simp only [key]
      by_cases hall : ∀ i < j, T.parent^[i] f ∈ T.red d L t <;>
        by_cases hra : a ∈ T.red d L t <;> simp [hall, hra]
    · have : σ10.regs 63 = 1 - (if σ10.regs 60 = σ10.regs 2 then 1 else 0) := by
        simp [r10, r9, r8]
      rw [this, e60, e2, Function.iterate_succ_apply', ← ha_def]
      simp only [cast_val_eq]
      by_cases hp : T.parent a = T.root <;> simp [hp]
  · intro σ' ⟨_, _, _, _, h63⟩
    rw [h63, if_pos (iter_depth T f)]
  · refine ⟨by rw [m4, m3, m2, m1], ?_, ?_, ?_, ?_⟩
    · intro r hr1 hr2
      simp only [SPF, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr2
      simp [r4, r3, r2, r1, update_apply, hr1, hr2]
    · simp [r4, r3, r2, r1, hf]
    · simp [r4, r3, r2, r1]
    · simp [r4, r3, r2, r1, hf, h2, cast_val_eq]
      by_cases hp : f = T.root <;> simp [hp, Fin.val_inj]
  · rintro k σ' hk ⟨hm', hfr', -, h45, -⟩
    refine hQ _ ?_ σ'.regs σ' (scr_eq (fun r hr1 hr2 => hfr' r hr1 hr2) h45) hm'
    have : T.depth f * (28 * n + 56 + 2) ≤ n * (28 * n + 58) := Nat.mul_le_mul (by omega) le_rfl
    clear * - this hk hk2
    ring_nf at this hk ⊢
    nlinarith

/-! ### Sums over the edges with index `< m` -/
/-- Partial sum over the edges `f` with `f < m`. -/
noncomputable def psum (m : ℕ) (g : Fin n → ℝ) : ℝ :=
  ∑ f ∈ T.edges.filter (fun f => f.val < m), g f

theorem psum_zero (g : Fin n → ℝ) : psum T 0 g = 0 := by
  simp [psum]

theorem psum_succ (g : Fin n → ℝ) (m : ℕ) (hm : m < n) :
    psum T (m + 1) g = psum T m g + (if (⟨m, hm⟩ : Fin n) ∈ T.edges then g ⟨m, hm⟩ else 0) := by
  unfold psum
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_ite_eq' T.edges (⟨m, hm⟩ : Fin n) g,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  by_cases h1 : f.val < m
  · have : f ≠ ⟨m, hm⟩ := fun h => by rw [h] at h1; simp at h1
    simp [h1, show f.val < m + 1 by omega, Ne.symm this, this]
  · by_cases h2 : f.val = m
    · have : (⟨m, hm⟩ : Fin n) = f := Fin.ext h2.symm
      simp [h1, h2, this]
    · have : (⟨m, hm⟩ : Fin n) ≠ f := fun h => h2 (by rw [← h])
      simp [h1, show ¬ f.val < m + 1 by omega, this, Ne.symm this]

theorem psum_all (g : Fin n → ℝ) : psum T n g = ∑ f ∈ T.edges, g f := by
  unfold psum
  rw [Finset.filter_true_of_mem (fun f _ => f.isLt)]

theorem sum_mem_eq (S : Finset (Fin n)) (hS : S ⊆ T.edges) :
    ∑ f ∈ T.edges, (if f ∈ S then T.W f else 0) = ∑ f ∈ S, T.W f := by
  rw [← Finset.sum_filter]
  congr 1
  ext f
  simp only [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨hS h, h⟩

theorem mem_rootPatch (t : ℝ) (f : Fin n) (hf : f ≠ T.root) :
    f ∈ T.rootPatch d L t ↔ ∀ i < T.depth f, T.parent^[i] f ∈ T.red d L t := by
  unfold Tree.rootPatch
  rw [Finset.mem_filter, ← anc_iff T (fun a => a ∈ T.red d L t) f]
  constructor
  · exact fun h => h.2
  · intro h
    have := T.depth_parent f hf
    exact ⟨h 0 (by omega), h⟩

/-! ### The evaluation loop -/
def Fpart : Stmt :=
  .seq (ldIn 40 4 34) (.seq (.div 41 30 40) (.seq (.const 42 1) (.seq (.sub 43 41 42)
    (.seq (.ifle 43 (.mul 44 39 41) (mov 44 39)) (.add 32 32 44)))))

def eBody : Stmt :=
  .seq (eqT 37 34 2) (.seq (isRed 38 34) (.seq (ldIn 39 3 34) (.seq patchFlag
  (.seq (.const 46 1) (.seq (.sub 46 46 37)
  (.seq (.mul 47 46 38) (.seq (.mul 47 47 39) (.seq (.add 31 31 47)
  (.seq (.mul 48 46 45) (.seq (.mul 48 48 39) (.seq (.add 33 33 48)
  (.ifle 46 skip Fpart))))))))))))

/-- `31 := R t`, `32 := F t`, `33 := Rin t` for `t` in register `30`. -/
def evalE : Stmt :=
  .seq (.const 31 0) (.seq (.const 32 0) (.seq (.const 33 0) (forLoop 34 1 35 36 eBody)))

def SE : List ℕ := [31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
  50, 51, 52, 53, 60, 61, 62, 63, 64, 65, 100, 101]

noncomputable def gR (t : ℝ) (f : Fin n) : ℝ := if f ∈ T.red d L t then T.W f else 0

noncomputable def gF (t : ℝ) (f : Fin n) : ℝ := T.W f * min 1 (t / d f)

noncomputable def gI (t : ℝ) (f : Fin n) : ℝ := if f ∈ T.rootPatch d L t then T.W f else 0

/-- The invariant of the evaluation loop. -/
def IE (σ0 : Cfg) (t : ℝ) (m : ℕ) (σ : Cfg) : Prop :=
  σ.mem = σ0.mem ∧ (∀ r, r ∉ SE → σ.regs r = σ0.regs r) ∧
    σ.regs 31 = psum T m (gR T d L t) ∧ σ.regs 32 = psum T m (gF T d t) ∧
    σ.regs 33 = psum T m (gI T d L t)

def cEb (n : ℕ) : ℕ := n * (30 * n + 80) + 50 * n + 120

theorem eBody_spec (hD : T.Normalized d) (M : ℤ → ℝ) (hM : MemOK T d L M) (σ0 : Cfg)
    (hmem0 : σ0.mem = M) (t : ℝ) (ht : σ0.regs 30 = t) (h1 : σ0.regs 1 = n)
    (h2 : σ0.regs 2 = T.root.val) (m : ℕ) (hm : m < n) (σ : Cfg) (hI : IE T d L σ0 t m σ)
    (h34 : σ.regs 34 = m) :
    Runs eBody σ (fun k σ' => k ≤ cEb n ∧ σ'.regs 34 = m ∧ σ'.regs 1 = n ∧
      ∀ a b e, IE T d L σ0 t (m + 1)
        ⟨update (update (update σ'.regs 36 a) 34 b) 35 e, σ'.ptrs, σ'.mem⟩) := by
  obtain ⟨hmem, hfr, h31, h32, h33⟩ := hI
  set f : Fin n := ⟨m, hm⟩ with hf_def
  have hfv : σ.regs 34 = (f.val : ℝ) := h34
  have hσ1 : σ.regs 1 = n := by rw [hfr 1 (by decide), h1]
  have hσ2 : σ.regs 2 = T.root.val := by rw [hfr 2 (by decide), h2]
  have hσ30 : σ.regs 30 = t := by rw [hfr 30 (by decide), ht]
  have hWf : σ.mem ((3 + 3 * f.val : ℕ) : ℤ) = T.W f := by
    rw [hmem, hmem0, hM.1 _ (by positivity), ti_W]
  have hdf : σ.mem ((4 + 3 * f.val : ℕ) : ℤ) = d f := by
    rw [hmem, hmem0, hM.1 _ (by positivity), ti_d]
  refine r_seq (r_eqT 37 34 2 (by decide) (by decide) (by decide) σ _
    (fun k1 hk1 z1 σ1 r1 m1 => ?_))
  refine r_seq (isRed_spec T d L 38 34 (by decide) (by decide) M hM σ1 (by rw [m1, hmem, hmem0])
    f (by simp [r1, hfv]) t (by simp [r1, hσ30]) _ (fun k2 hk2 g2 σ2 r2 m2 => ?_))
  refine r_seq (r_ldIn 39 3 34 (by decide) σ2 f.val (by simp [r2, r1, scr, SRed, hfv]) _
    (fun k3 hk3 a3 b3 σ3 r3 m3 => ?_))
  refine r_seq (patchFlag_spec T d L M hM σ3 (by rw [m3, m2, m1, hmem, hmem0]) f
    (by simp [r3, r2, r1, scr, SRed, hfv]) t (by simp [r3, r2, r1, scr, SRed, hσ30])
    (by simp [r3, r2, r1, scr, SRed, hσ2]) _ (fun k4 hk4 g4 σ4 r4 m4 => ?_))
  refine r_seq (f_const fun σ5 r5 m5 => r_seq (f_sub fun σ6 r6 m6 => r_seq (f_mul
    fun σ7 r7 m7 => r_seq (f_mul fun σ8 r8 m8 => r_seq (f_add fun σ9 r9 m9 => r_seq (f_mul
    fun σ10 r10 m10 => r_seq (f_mul fun σ11 r11 m11 => r_seq (f_add
    fun σ12 r12 m12 => ?_))))))))
  -- values at σ12
  have v46 : σ12.regs 46 = 1 - (if f = T.root then 1 else 0) := by
    simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, scr, SPF, SRed, hfv, hσ2,
      cast_val_eq, Fin.val_inj]
  have v39 : σ12.regs 39 = T.W f := by
    simp only [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, scr, SPF, update_apply, reduceIte,
      Nat.reduceEqDiff, List.mem_cons, List.not_mem_nil, or_false, or_self, false_or]
    rw [m2, m1, hWf]
  have v31 : σ12.regs 31 = psum T m (gR T d L t) +
      (1 - (if f = T.root then 1 else 0)) * (if d f < T.x L f + t then 1 else 0) * T.W f := by
    rw [← v39]
    simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, scr, SPF, SRed, hfv, hσ2,
      cast_val_eq, Fin.val_inj, h31]
  have v33 : σ12.regs 33 = psum T m (gI T d L t) +
      (1 - (if f = T.root then 1 else 0)) *
        (if ∀ i < T.depth f, T.parent^[i] f ∈ T.red d L t then 1 else 0) * T.W f := by
    rw [← v39]
    simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, scr, SPF, SRed, hfv, hσ2,
      cast_val_eq, Fin.val_inj, h33]
  have v32 : σ12.regs 32 = psum T m (gF T d t) := by
    simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, scr, SPF, SRed, h32]
  have v34 : σ12.regs 34 = f.val := by
    simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, scr, SPF, SRed, hfv]
  have v30 : σ12.regs 30 = t := by
    simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, scr, SPF, SRed, hσ30]
  have vfr : ∀ r, r ∉ SE → σ12.regs r = σ0.regs r := by
    intro r hr
    rw [← hfr r hr]
    simp only [SE, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [r12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, scr, SPF, SRed, update_apply, hr]
  have vmem : σ12.mem = σ0.mem := by
    rw [m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1, hmem, hmem0]
  have hfn := hm
  have hstepR : psum T (m + 1) (gR T d L t) = psum T m (gR T d L t) +
      (1 - (if f = T.root then 1 else 0)) * (if d f < T.x L f + t then 1 else 0) * T.W f := by
    rw [psum_succ T _ m hm, ← hf_def]
    by_cases hr : f = T.root
    · simp [hr, mem_edges_iff]
    · simp [hr, mem_edges_iff, gR, mem_red T d L t f hr]
  have hstepI : psum T (m + 1) (gI T d L t) = psum T m (gI T d L t) +
      (1 - (if f = T.root then 1 else 0)) *
        (if ∀ i < T.depth f, T.parent^[i] f ∈ T.red d L t then 1 else 0) * T.W f := by
    rw [psum_succ T _ m hm, ← hf_def]
    by_cases hr : f = T.root
    · simp [hr, mem_edges_iff]
    · simp only [hr, mem_edges_iff, gI, mem_rootPatch T d L t f hr]
      by_cases ha : ∀ i < T.depth f, T.parent^[i] f ∈ T.red d L t <;> simp [ha, hr]
  refine f_ifle ?_ ?_
  · -- the root: skip
    intro hle
    have hr : f = T.root := by
      rw [v46] at hle; by_contra h; norm_num [h] at hle
    refine r_skip ⟨?_, ?_, ?_, fun a b e => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · have : f.val < n := hm
      unfold cEb
      clear * - hk1 hk2 hk3 hk4 this
      ring_nf at hk3 hk4 ⊢
      omega
    · rw [v34]
    · rw [vfr 1 (by decide), h1]
    · rw [vmem]
    · intro r hr'
      rw [← vfr r hr']
      simp only [SE, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp [update_apply, hr']
    · simp [update_apply, v31, hstepR]
    · simp [update_apply, v32, psum_succ T _ m hm, ← hf_def, hr, mem_edges_iff]
    · simp [update_apply, v33, hstepI]
  · intro hle
    have hr : f ≠ T.root := by
      rw [v46] at hle; intro h; simp [h] at hle
    have hdpos : 0 < d f := hD.1 f ((mem_edges_iff T f).mpr hr)
    have hfinal : ∀ σ' : Cfg, σ'.mem = σ12.mem →
        (∀ r, r ∉ [32, 40, 41, 42, 43, 44, 100, 101] → σ'.regs r = σ12.regs r) →
        σ'.regs 32 = σ12.regs 32 + T.W f * min 1 (t / d f) →
        σ'.regs 34 = m ∧ σ'.regs 1 = n ∧ ∀ a b e, IE T d L σ0 t (m + 1)
          ⟨update (update (update σ'.regs 36 a) 34 b) 35 e, σ'.ptrs, σ'.mem⟩ := by
      intro σ' hm' hfr' h32'
      refine ⟨by rw [hfr' 34 (by decide), v34], by rw [hfr' 1 (by decide), vfr 1 (by decide), h1],
        fun a b e => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
      · simp [hm', vmem]
      · intro r hr'
        rw [← vfr r hr']
        simp only [SE, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        simp [update_apply, hr', hfr' r (by simp [hr'])]
      · simp [update_apply, hfr' 31 (by decide), v31, hstepR]
      · simp [update_apply, h32', v32, psum_succ T _ m hm, ← hf_def, hr, mem_edges_iff, gF]
      · simp [update_apply, hfr' 33 (by decide), v33, hstepI]
    have hd40 : σ12.mem ((4 + 3 * f.val : ℕ) : ℤ) = d f := by rw [vmem, ← hmem]; exact hdf
    refine r_seq (r_ldIn 40 4 34 (by decide) σ12 f.val v34 _
      (fun k5 hk5 a5 b5 σ13 r13 m13 => ?_))
    have h40 : σ13.regs 40 = d f := by rw [r13, update_self]; exact hd40
    refine r_seq (f_div (by rw [h40]; exact hdpos) fun σ14 r14 m14 => r_seq (f_const
      fun σ15 r15 m15 => r_seq (f_sub fun σ16 r16 m16 => r_seq (f_ifle ?_ ?_))))
    · intro hle2
      have e41 : σ16.regs 41 = t / d f := by simp [r16, r15, r14, h40, r13, v30]
      have e43 : σ16.regs 43 = t / d f - 1 := by simp [r16, r15, r14, h40, r13, v30]
      have e39 : σ16.regs 39 = T.W f := by simp [r16, r15, r14, r13, v39]
      have e32 : σ16.regs 32 = σ12.regs 32 := by simp [r16, r15, r14, r13]
      refine f_mul fun σ17 r17 m17 => f_add fun σ18 r18 m18 => ?_
      have hmin : min 1 (t / d f) = t / d f := by
        rw [e43] at hle2
        rw [min_eq_right]; linarith
      obtain ⟨hA, hB, hC⟩ := hfinal σ18 (by rw [m18, m17, m16, m15, m14, m13]) (by
        intro r hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        simp [r18, r17, r16, r15, r14, r13, update_apply, hr']) (by
        rw [hmin, r18, update_self, r17]
        simp [e39, e41, e32])
      refine ⟨?_, hA, hB, hC⟩
      have : f.val < n := hm
      unfold cEb
      clear * - hk1 hk2 hk3 hk4 hk5 this
      ring_nf at hk3 hk4 hk5 ⊢
      omega
    · intro hle2
      have e41 : σ16.regs 41 = t / d f := by simp [r16, r15, r14, h40, r13, v30]
      have e43 : σ16.regs 43 = t / d f - 1 := by simp [r16, r15, r14, h40, r13, v30]
      have e39 : σ16.regs 39 = T.W f := by simp [r16, r15, r14, r13, v39]
      have e32 : σ16.regs 32 = σ12.regs 32 := by simp [r16, r15, r14, r13]
      refine r_mov (by decide) (f_add fun σ18 r18 m18 => ?_)
      have hmin : min 1 (t / d f) = 1 := by
        rw [e43] at hle2
        rw [min_eq_left]; linarith
      obtain ⟨hA, hB, hC⟩ := hfinal σ18 (by rw [m18, m16, m15, m14, m13]) (by
        intro r hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        simp [r18, r16, r15, r14, r13, update_apply, hr']) (by
        rw [hmin, r18, update_self]
        simp [e39, e32])
      refine ⟨?_, hA, hB, hC⟩
      have : f.val < n := hm
      unfold cEb
      clear * - hk1 hk2 hk3 hk4 hk5 this
      ring_nf at hk3 hk4 hk5 ⊢
      omega

def cE (n : ℕ) : ℕ := n * (cEb n + 5) + 6

theorem evalE_spec (hD : T.Normalized d) (M : ℤ → ℝ) (hM : MemOK T d L M) (σ : Cfg)
    (hmem : σ.mem = M) (t : ℝ) (ht : σ.regs 30 = t) (h1 : σ.regs 1 = n)
    (h2 : σ.regs 2 = T.root.val) (Q : ℕ → Cfg → Prop)
    (hQ : ∀ k, k ≤ cE n → ∀ σ' : Cfg, σ'.mem = σ.mem → (∀ r, r ∉ SE → σ'.regs r = σ.regs r) →
      σ'.regs 31 = T.R d L t → σ'.regs 32 = T.F d t → σ'.regs 33 = T.Rin d L t → Q k σ') :
    Runs evalE σ Q := by
  refine r_seq (f_const fun σ1 r1 m1 => r_seq (f_const fun σ2 r2 m2 => r_seq (f_const
    fun σ3 r3 m3 => ?_)))
  refine r_for 34 1 35 36 eBody (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) n (cEb n) (IE T d L σ t) σ3 (by simp [r3, r2, r1, h1]) ?_ ?_ _
    (fun k σ' hk hI => ?_)
  · intro a b
    refine ⟨by simp [m3, m2, m1], ?_, ?_, ?_, ?_⟩
    · intro r hr
      simp only [SE, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [r3, r2, r1, update_apply, hr]
    · simp [r3, r2, r1, psum_zero]
    · simp [r3, r2, r1, psum_zero]
    · simp [r3, r2, r1, psum_zero]
  · intro m hm σ' hI h34 _
    exact eBody_spec T d L hD M hM σ hmem t ht h1 h2 m hm σ' hI h34
  obtain ⟨hm', hfr', h31, h32, h33⟩ := hI
  refine hQ _ ?_ σ' hm' hfr' ?_ ?_ ?_
  · unfold cE
    generalize cEb n = c at *
    omega
  · rw [h31, psum_all]
    exact sum_mem_eq T _ (Finset.filter_subset _ _)
  · rw [h32, psum_all]; rfl
  · rw [h33, psum_all]
    exact sum_mem_eq T _ ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
/-! ## Phase C: the search for a good time `t` -/
/-- `70 += d v` for a non-root vertex `v` in register `71`. -/
def fbBody : Stmt :=
  .seq (eqT 74 71 2) (.seq (ldIn 75 4 71) (.seq (.const 76 1) (.seq (.sub 76 76 74)
    (.seq (.mul 77 76 75) (.add 70 70 77)))))

/-- Test the candidate `d v - x v` for the vertex `v` in register `71`. -/
def cBody : Stmt :=
  .seq (eqT 74 71 2) (.ifle 74 (.seq (ldIn 75 4 71) (.seq (ldx 76 71) (.seq (.sub 30 75 76)
    (.ifle 30 skip (.seq evalE (.seq (.sub 77 32 31) (.ifle 77 skip (mov 70 30))))))))
    skip)

/-- `70 := ∑ d + 1`, then overwritten by any candidate that works. -/
def phaseC : Stmt :=
  .seq (.const 70 0) (.seq (forLoop 71 1 72 73 fbBody) (.seq (.const 76 1) (.seq (.add 70 70 76)
    (forLoop 71 1 72 73 cBody))))

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
variable {n : ℕ} (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n))
/-- A good time. -/
def Good (t : ℝ) : Prop := 0 < t ∧ T.R d L t < T.F d t

/-- The invariant of the fallback loop. -/
def IFb (σ0 : Cfg) (m : ℕ) (σ : Cfg) : Prop :=
  σ.mem = σ0.mem ∧ σ.regs 1 = n ∧ σ.regs 2 = T.root.val ∧ σ.regs 70 = psum T m d

theorem fbBody_spec (M : ℤ → ℝ) (hM : MemOK T d L M) (σ0 : Cfg) (hmem0 : σ0.mem = M)
    (m : ℕ) (hm : m < n) (σ : Cfg) (hI : IFb T d σ0 m σ) (h71 : σ.regs 71 = m) :
    Runs fbBody σ (fun k σ' => k ≤ 12 * n + 40 ∧ σ'.regs 71 = m ∧ σ'.regs 1 = n ∧
      ∀ a b e, IFb T d σ0 (m + 1)
        ⟨update (update (update σ'.regs 73 a) 71 b) 72 e, σ'.ptrs, σ'.mem⟩) := by
  obtain ⟨hmem, h1, h2, h70⟩ := hI
  set f : Fin n := ⟨m, hm⟩ with hf_def
  have hfv : σ.regs 71 = (f.val : ℝ) := h71
  have hdf : σ.mem ((4 + 3 * f.val : ℕ) : ℤ) = d f := by
    rw [hmem, hmem0, hM.1 _ (by positivity), ti_d]
  refine r_seq (r_eqT 74 71 2 (by decide) (by decide) (by decide) σ _
    (fun k1 hk1 z1 σ1 r1 m1 => ?_))
  refine r_seq (r_ldIn 75 4 71 (by decide) σ1 f.val (by simp [r1, hfv]) _
    (fun k2 hk2 a2 b2 σ2 r2 m2 => ?_))
  refine r_seq (f_const fun σ3 r3 m3 => r_seq (f_sub fun σ4 r4 m4 => r_seq (f_mul
    fun σ5 r5 m5 => f_add fun σ6 r6 m6 => ⟨?_, ?_, ?_, fun a b e => ⟨?_, ?_, ?_, ?_⟩⟩)))
  · have : f.val < n := hm
    clear * - hk1 hk2 this
    ring_nf at hk2 ⊢
    omega
  · simp [r6, r5, r4, r3, r2, r1, h71]
  · simp [r6, r5, r4, r3, r2, r1, h1]
  · simp [m6, m5, m4, m3, m2, m1, hmem]
  · simp [update_apply, r6, r5, r4, r3, r2, r1, h1]
  · simp [update_apply, r6, r5, r4, r3, r2, r1, h2]
  · have e75 : σ6.regs 75 = d f := by
      simp only [r6, r5, r4, r3, update_apply, reduceIte, Nat.reduceEqDiff]
      rw [r2, update_self, m1, hdf]
    have e70 : σ6.regs 70 = psum T m d + (1 - if f = T.root then 1 else 0) * σ6.regs 75 := by
      simp [r6, r5, r4, r3, r2, r1, h70, hfv, h2, cast_val_eq, Fin.val_inj]
    simp only [update_apply, reduceIte, Nat.reduceEqDiff]
    rw [e70, e75, psum_succ T d m hm, ← hf_def]
    by_cases hr : f = T.root <;> simp [hr, mem_edges_iff]

/-- The invariant of the candidate loop (`fb` is the fallback time). -/
def IC (σ0 : Cfg) (fb : ℝ) (m : ℕ) (σ : Cfg) : Prop :=
  σ.mem = σ0.mem ∧ σ.regs 1 = n ∧ σ.regs 2 = T.root.val ∧
    (Good T d L (σ.regs 70) ∨ (σ.regs 70 = fb ∧ ∀ e : Fin n, e.val < m → e ∈ T.edges →
      0 < d e - T.x L e → ¬ T.R d L (d e - T.x L e) < T.F d (d e - T.x L e)))

def cCb (n : ℕ) : ℕ := cE n + 20 * n + 50

theorem cBody_spec (hD : T.Normalized d) (M : ℤ → ℝ) (hM : MemOK T d L M) (σ0 : Cfg)
    (hmem0 : σ0.mem = M) (fb : ℝ) (m : ℕ) (hm : m < n) (σ : Cfg) (hI : IC T d L σ0 fb m σ)
    (h71 : σ.regs 71 = m) :
    Runs cBody σ (fun k σ' => k ≤ cCb n ∧ σ'.regs 71 = m ∧ σ'.regs 1 = n ∧
      ∀ a b e, IC T d L σ0 fb (m + 1)
        ⟨update (update (update σ'.regs 73 a) 71 b) 72 e, σ'.ptrs, σ'.mem⟩) := by
  obtain ⟨hmem, h1, h2, h70⟩ := hI
  set f : Fin n := ⟨m, hm⟩ with hf_def
  have hfv : σ.regs 71 = (f.val : ℝ) := h71
  have hdf : σ.mem ((4 + 3 * f.val : ℕ) : ℤ) = d f := by
    rw [hmem, hmem0, hM.1 _ (by positivity), ti_d]
  have hxf : σ.mem (-3 - ((f.val : ℕ) : ℤ)) = T.x L f := by rw [hmem, hmem0, hM.2]
  have hfin : ∀ σ' : Cfg, σ'.mem = σ.mem → σ'.regs 1 = n → σ'.regs 2 = T.root.val →
      σ'.regs 71 = m → (Good T d L (σ'.regs 70) ∨ (σ'.regs 70 = fb ∧ ∀ e : Fin n,
        e.val < m + 1 → e ∈ T.edges → 0 < d e - T.x L e →
          ¬ T.R d L (d e - T.x L e) < T.F d (d e - T.x L e))) →
      σ'.regs 71 = m ∧ σ'.regs 1 = n ∧ ∀ a b e, IC T d L σ0 fb (m + 1)
        ⟨update (update (update σ'.regs 73 a) 71 b) 72 e, σ'.ptrs, σ'.mem⟩ := by
    intro σ' hm' h1' h2' h71' h70'
    refine ⟨h71', h1', fun a b e => ⟨by simp [hm', hmem], by simp [update_apply, h1'],
      by simp [update_apply, h2'], ?_⟩⟩
    simpa [update_apply] using h70'
  have hold : ∀ x : ℝ, (Good T d L x ∨ (x = fb ∧ ∀ e : Fin n, e.val < m → e ∈ T.edges →
      0 < d e - T.x L e → ¬ T.R d L (d e - T.x L e) < T.F d (d e - T.x L e))) →
      ¬ (f ∈ T.edges ∧ 0 < d f - T.x L f ∧ T.R d L (d f - T.x L f) < T.F d (d f - T.x L f)) →
      (Good T d L x ∨ (x = fb ∧ ∀ e : Fin n, e.val < m + 1 → e ∈ T.edges →
        0 < d e - T.x L e → ¬ T.R d L (d e - T.x L e) < T.F d (d e - T.x L e))) := by
    rintro x (hg | ⟨hx, hall⟩) hnot
    · exact Or.inl hg
    · refine Or.inr ⟨hx, fun e he h1 h2 h3 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp he with he | he
      · exact hall e he h1 h2 h3
      · have : e = f := Fin.ext he
        subst this
        exact hnot ⟨h1, h2, h3⟩
  have hfn : f.val < n := hm
  refine r_seq (r_eqT 74 71 2 (by decide) (by decide) (by decide) σ _
    (fun k1 hk1 z1 σ1 r1 m1 => f_ifle ?_ ?_))
  · intro hle
    have hr : f ≠ T.root := by
      intro h; norm_num [r1, hfv, h2, h, cast_val_eq, Fin.val_inj] at hle
    refine r_seq (r_ldIn 75 4 71 (by decide) σ1 f.val (by simp [r1, hfv]) _
      (fun k2 hk2 a2 b2 σ2 r2 m2 => ?_))
    refine r_seq (r_ldx 76 71 (by decide) σ2 f.val (by simp [r2, r1, hfv]) _
      (fun k3 hk3 a3 b3 σ3 r3 m3 => ?_))
    refine r_seq (f_sub fun σ4 r4 m4 => f_ifle ?_ ?_)
    · have e30 : σ4.regs 30 = d f - T.x L f := by
        simp only [r4, r3, r2, update_apply, reduceIte, Nat.reduceEqDiff]
        rw [m2, m1, hdf, hxf]
      intro hle2
      refine r_skip ?_
      obtain ⟨hA, hB, hC⟩ := hfin σ4 (by rw [m4, m3, m2, m1]) (by simp [r4, r3, r2, r1, h1])
        (by simp [r4, r3, r2, r1, h2]) (by simp [r4, r3, r2, r1, h71])
        (hold _ (by simpa [r4, r3, r2, r1] using h70) (fun h => by
          rw [e30] at hle2; linarith [h.2.1]))
      refine ⟨?_, hA, hB, hC⟩
      unfold cCb
      clear * - hk1 hk2 hk3 hfn
      ring_nf at hk2 hk3 ⊢
      omega
    · have e30 : σ4.regs 30 = d f - T.x L f := by
        simp only [r4, r3, r2, update_apply, reduceIte, Nat.reduceEqDiff]
        rw [m2, m1, hdf, hxf]
      intro hlt2
      refine r_seq (evalE_spec T d L hD M hM σ4 (by rw [m4, m3, m2, m1, hmem, hmem0]) _ e30
        (by simp [r4, r3, r2, r1, h1]) (by simp [r4, r3, r2, r1, h2]) _
        (fun k4 hk4 σ5 m5 hfr5 h31 h32 h33 => ?_))
      have g1 : σ5.regs 1 = n := by rw [hfr5 1 (by decide)]; simp [r4, r3, r2, r1, h1]
      have g2 : σ5.regs 2 = T.root.val := by rw [hfr5 2 (by decide)]; simp [r4, r3, r2, r1, h2]
      have g71 : σ5.regs 71 = m := by rw [hfr5 71 (by decide)]; simp [r4, r3, r2, r1, h71]
      have g70 : σ5.regs 70 = σ.regs 70 := by rw [hfr5 70 (by decide)]; simp [r4, r3, r2, r1]
      have g30 : σ5.regs 30 = d f - T.x L f := by rw [hfr5 30 (by decide), e30]
      refine r_seq (f_sub fun σ6 r6 m6 => f_ifle ?_ ?_)
      · intro hle3
        refine r_skip ?_
        obtain ⟨hA, hB, hC⟩ := hfin σ6 (by rw [m6, m5, m4, m3, m2, m1])
          (by simp [r6, g1]) (by simp [r6, g2]) (by simp [r6, g71])
          (hold _ (by simpa [r6, g70] using h70) (fun h => by
            simp [r6, h31, h32] at hle3; linarith [h.2.2]))
        refine ⟨?_, hA, hB, hC⟩
        unfold cCb
        clear * - hk1 hk2 hk3 hk4 hfn
        ring_nf at hk2 hk3 ⊢
        omega
      · intro hlt3
        refine r_mov (by decide) ?_
        have hgood : Good T d L (d f - T.x L f) := by
          refine ⟨by rw [← e30]; linarith, ?_⟩
          simp [r6, h31, h32, g30] at hlt3
          linarith
        obtain ⟨hA, hB, hC⟩ := hfin ⟨update σ6.regs 70 (σ6.regs 30), σ6.ptrs, σ6.mem⟩
          (by simp [m6, m5, m4, m3, m2, m1])
          (by simp [r6, g1]) (by simp [r6, g2]) (by simp [r6, g71])
          (Or.inl (by simpa [r6, g30] using hgood))
        refine ⟨?_, hA, hB, hC⟩
        unfold cCb
        clear * - hk1 hk2 hk3 hk4 hfn
        ring_nf at hk2 hk3 ⊢
        omega
  · intro hlt
    have hr : f = T.root := by
      by_contra h; simp [r1, hfv, h2, h, cast_val_eq, Fin.val_inj] at hlt
    refine r_skip ?_
    obtain ⟨hA, hB, hC⟩ := hfin σ1 (by rw [m1]) (by simp [r1, h1]) (by simp [r1, h2])
      (by simp [r1, h71])
      (hold _ (by simpa [r1] using h70) (fun h => (mem_edges_iff T f).mp h.1 hr))
    refine ⟨?_, hA, hB, hC⟩
    unfold cCb
    clear * - hk1
    omega

def cC (n : ℕ) : ℕ := n * (12 * n + 45) + n * (cCb n + 5) + 12

theorem phaseC_spec (hD : T.Normalized d) (hL : T.DFS L) (hU : T.Unequal d) (M : ℤ → ℝ)
    (hM : MemOK T d L M) (σ : Cfg) (hmem : σ.mem = M) (h1 : σ.regs 1 = n)
    (h2 : σ.regs 2 = T.root.val) (Q : ℕ → Cfg → Prop)
    (hQ : ∀ k, k ≤ cC n → ∀ σ' : Cfg, σ'.mem = σ.mem → σ'.regs 1 = n →
      σ'.regs 2 = T.root.val → Good T d L (σ'.regs 70) → Q k σ') :
    Runs phaseC σ Q := by
  refine r_seq (f_const fun σ1 r1 m1 => r_seq ?_)
  have hm1 : σ1.mem = M := by rw [m1, hmem]
  refine r_for 71 1 72 73 fbBody (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) n (12 * n + 40) (IFb T d σ1) σ1 (by simp [r1, h1]) ?_ ?_ _
    (fun k1 σ2 hk1 hI2 => ?_)
  · intro a b
    exact ⟨rfl, by simp [update_apply, r1, h1], by simp [update_apply, r1, h2],
      by simp [update_apply, r1, psum_zero]⟩
  · intro m hm σ' hI h71 _
    exact fbBody_spec T d L M hM σ1 hm1 m hm σ' hI h71
  obtain ⟨hm2, h21, h22, h270⟩ := hI2
  refine r_seq (f_const fun σ3 r3 m3 => r_seq (f_add fun σ4 r4 m4 => ?_))
  have h470 : σ4.regs 70 = psum T n d + 1 := by simp [r4, r3, h270]
  refine r_for 71 1 72 73 cBody (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) n (cCb n) (IC T d L σ1 (psum T n d + 1)) σ4 (by simp [r4, r3, h21]) ?_ ?_ _
    (fun k2 σ5 hk2 hI5 => ?_)
  · intro a b
    refine ⟨by simp [m4, m3, hm2], by simp [update_apply, r4, r3, h21],
      by simp [update_apply, r4, r3, h22], Or.inr ⟨by simp [update_apply, h470], ?_⟩⟩
    intro e he; omega
  · intro m hm σ' hI h71 _
    exact cBody_spec T d L hD M hM σ1 hm1 _ m hm σ' hI h71
  obtain ⟨hm5, h51, h52, h570⟩ := hI5
  refine hQ _ ?_ σ5 (by rw [hm5, m1]) h51 h52 ?_
  · unfold cC
    generalize cCb n = c at *
    rw [show 12 * n + 40 + 5 = 12 * n + 45 by ring] at hk1
    clear * - hk1 hk2
    omega
  · rcases h570 with hg | ⟨hfb, hall⟩
    · exact hg
    · rw [hfb, psum_all]
      rcases cand_exists T d L hD hL hU with ⟨e, he, hpos, hlt⟩ | hlt
      · exact absurd hlt (hall e e.isLt he hpos)
      · refine ⟨?_, hlt⟩
        have : 0 ≤ ∑ e ∈ T.edges, d e := Finset.sum_nonneg (fun e he => (hD.1 e he).le)
        linarith

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
/-! ## Phase S: `betaLo`, the two sums and `s` -/
/-- `80 := max 80 (d v)` when `F (d v) ≤ r` (`r` in register `87`), for a non-root `v`. -/
def bBody : Stmt :=
  .seq (eqT 84 81 2) (.ifle 84 (.seq (ldIn 85 4 81) (.seq (mov 30 85) (.seq evalE
    (.seq (.sub 86 32 87) (.ifle 86 (.seq (.sub 88 85 80) (.ifle 88 skip (mov 80 85))) skip)))))
    skip)

/-- `89 += W v` if `d v ≤ β`, else `90 += W v / d v` (`β` in register `80`). -/
def abBody : Stmt :=
  .seq (eqT 84 81 2) (.ifle 84 (.seq (ldIn 85 4 81) (.seq (ldIn 92 3 81) (.seq (.sub 88 85 80)
    (.ifle 88 (.add 89 89 92) (.seq (.div 93 92 85) (.add 90 90 93)))))) skip)

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
variable {n : ℕ} (T : Tree n) (d : Fin n → ℝ)
/-- `betaLo` restricted to the vertices `< m`. -/
noncomputable def bl (r : ℝ) (m : ℕ) : ℝ :=
  (insert 0 ((T.edges.filter (fun e => e.val < m ∧ T.F d (d e) ≤ r)).image d)).max'
    (Finset.insert_nonempty _ _)

theorem bl_zero (r : ℝ) : bl T d r 0 = 0 := by
  unfold bl
  simp

theorem bl_succ (r : ℝ) (m : ℕ) (hm : m < n) :
    bl T d r (m + 1) = if (⟨m, hm⟩ : Fin n) ∈ T.edges ∧ T.F d (d ⟨m, hm⟩) ≤ r then
      max (bl T d r m) (d ⟨m, hm⟩) else bl T d r m := by
  unfold bl
  split_ifs with h
  · have hs : T.edges.filter (fun e => e.val < m + 1 ∧ T.F d (d e) ≤ r) =
        insert ⟨m, hm⟩ (T.edges.filter (fun e => e.val < m ∧ T.F d (d e) ≤ r)) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨he, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | h1
        · exact Or.inr ⟨he, h1, h2⟩
        · exact Or.inl (Fin.ext h1)
      · rintro (rfl | ⟨he, h1, h2⟩)
        · exact ⟨h.1, by simp, h.2⟩
        · exact ⟨he, by omega, h2⟩
    simp only [hs, Finset.image_insert, Finset.insert_comm (0 : ℝ) (d ⟨m, hm⟩)]
    rw [Finset.max'_insert _ _ (Finset.insert_nonempty _ _), max_comm]
  · have hs : T.edges.filter (fun e => e.val < m + 1 ∧ T.F d (d e) ≤ r) =
        T.edges.filter (fun e => e.val < m ∧ T.F d (d e) ≤ r) := by
      ext e
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨he, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | h1
        · exact ⟨he, h1, h2⟩
        · exfalso
          have : e = ⟨m, hm⟩ := Fin.ext h1
          subst this
          exact h ⟨he, h2⟩
      · rintro ⟨he, h1, h2⟩
        exact ⟨he, by omega, h2⟩
    simp only [hs]

theorem bl_all (r : ℝ) : bl T d r n = betaLo T d r := by
  unfold bl betaLo
  have : T.edges.filter (fun e => e.val < n ∧ T.F d (d e) ≤ r) =
      T.edges.filter (fun e => T.F d (d e) ≤ r) := by
    ext e; simp [e.isLt]
  simp only [this]

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
variable {n : ℕ} (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n))
/-- The invariant of the `betaLo` loop. -/
def IB (σ0 : Cfg) (r t : ℝ) (m : ℕ) (σ : Cfg) : Prop :=
  σ.mem = σ0.mem ∧ σ.regs 1 = n ∧ σ.regs 2 = T.root.val ∧ σ.regs 87 = r ∧ σ.regs 70 = t ∧
    σ.regs 80 = bl T d r m

theorem bBody_spec (hD : T.Normalized d) (M : ℤ → ℝ) (hM : MemOK T d L M) (σ0 : Cfg)
    (hmem0 : σ0.mem = M) (r t : ℝ) (m : ℕ) (hm : m < n) (σ : Cfg) (hI : IB T d σ0 r t m σ)
    (h81 : σ.regs 81 = m) :
    Runs bBody σ (fun k σ' => k ≤ cCb n ∧ σ'.regs 81 = m ∧ σ'.regs 1 = n ∧
      ∀ a b e, IB T d σ0 r t (m + 1)
        ⟨update (update (update σ'.regs 83 a) 81 b) 82 e, σ'.ptrs, σ'.mem⟩) := by
  obtain ⟨hmem, h1, h2, h87, h70, h80⟩ := hI
  set f : Fin n := ⟨m, hm⟩ with hf_def
  have hfv : σ.regs 81 = (f.val : ℝ) := h81
  have hdf : σ.mem ((4 + 3 * f.val : ℕ) : ℤ) = d f := by
    rw [hmem, hmem0, hM.1 _ (by positivity), ti_d]
  have hfn : f.val < n := hm
  have hfin : ∀ σ' : Cfg, σ'.mem = σ.mem → σ'.regs 1 = n → σ'.regs 2 = T.root.val →
      σ'.regs 81 = m → σ'.regs 87 = r → σ'.regs 70 = t → σ'.regs 80 = bl T d r (m + 1) →
      σ'.regs 81 = m ∧ σ'.regs 1 = n ∧ ∀ a b e, IB T d σ0 r t (m + 1)
        ⟨update (update (update σ'.regs 83 a) 81 b) 82 e, σ'.ptrs, σ'.mem⟩ := by
    intro σ' hm' h1' h2' h81' h87' h70' h80'
    exact ⟨h81', h1', fun a b e => ⟨by simp [hm', hmem], by simp [update_apply, h1'],
      by simp [update_apply, h2'], by simp [update_apply, h87'], by simp [update_apply, h70'],
      by simp [update_apply, h80']⟩⟩
  refine r_seq (r_eqT 84 81 2 (by decide) (by decide) (by decide) σ _
    (fun k1 hk1 z1 σ1 r1 m1 => f_ifle ?_ ?_))
  · intro hle
    have hr : f ≠ T.root := by
      intro h; norm_num [r1, hfv, h2, h, cast_val_eq, Fin.val_inj] at hle
    refine r_seq (r_ldIn 85 4 81 (by decide) σ1 f.val (by simp [r1, hfv]) _
      (fun k2 hk2 a2 b2 σ2 r2 m2 => ?_))
    have e85 : σ2.regs 85 = d f := by rw [r2, update_self, m1, hdf]
    refine r_seq (r_mov (by decide) ?_)
    refine r_seq (evalE_spec T d L hD M hM _ (by simp [m2, m1, hmem, hmem0]) (d f)
      (by simp [e85]) (by simp [r2, r1, h1]) (by simp [r2, r1, h2]) _
      (fun k4 hk4 σ5 m5 hfr5 h31 h32 h33 => ?_))
    have g : ∀ j, j ∉ SE → j ≠ 30 → σ5.regs j = σ2.regs j := by
      intro j hj hj30
      rw [hfr5 j hj]; simp [hj30]
    have g1 : σ5.regs 1 = n := by rw [g 1 (by decide) (by decide)]; simp [r2, r1, h1]
    have g2 : σ5.regs 2 = T.root.val := by rw [g 2 (by decide) (by decide)]; simp [r2, r1, h2]
    have g81 : σ5.regs 81 = m := by rw [g 81 (by decide) (by decide)]; simp [r2, r1, h81]
    have g87 : σ5.regs 87 = r := by rw [g 87 (by decide) (by decide)]; simp [r2, r1, h87]
    have g70 : σ5.regs 70 = t := by rw [g 70 (by decide) (by decide)]; simp [r2, r1, h70]
    have g80 : σ5.regs 80 = bl T d r m := by rw [g 80 (by decide) (by decide)]; simp [r2, r1, h80]
    have g85 : σ5.regs 85 = d f := by rw [g 85 (by decide) (by decide), e85]
    have gm : σ5.mem = σ.mem := by rw [m5]; simp [m2, m1]
    refine r_seq (f_sub fun σ6 r6 m6 => f_ifle ?_ ?_)
    · intro hle2
      have hF : T.F d (d f) ≤ r := by
        simp [r6, h32, g87] at hle2; linarith
      have hbl : bl T d r (m + 1) = max (bl T d r m) (d f) := by
        rw [bl_succ T d r m hm, ← hf_def, if_pos ⟨(mem_edges_iff T f).mpr hr, hF⟩]
      refine r_seq (f_sub fun σ7 r7 m7 => f_ifle ?_ ?_)
      · intro hle3
        refine r_skip ?_
        have hmx : max (bl T d r m) (d f) = bl T d r m := by
          simp [r7, r6, g85, g80] at hle3
          exact max_eq_left (by linarith)
        obtain ⟨hA, hB, hC⟩ := hfin σ7 (by rw [m7, m6, gm]) (by simp [r7, r6, g1])
          (by simp [r7, r6, g2]) (by simp [r7, r6, g81]) (by simp [r7, r6, g87])
          (by simp [r7, r6, g70]) (by simp [r7, r6, g80, hbl, hmx])
        refine ⟨?_, hA, hB, hC⟩
        unfold cCb
        clear * - hk1 hk2 hk4 hfn
        ring_nf at hk2 ⊢
        omega
      · intro hlt3
        refine r_mov (by decide) ?_
        have hmx : max (bl T d r m) (d f) = d f := by
          simp [r7, r6, g85, g80] at hlt3
          exact max_eq_right (by linarith)
        obtain ⟨hA, hB, hC⟩ := hfin ⟨update σ7.regs 80 (σ7.regs 85), σ7.ptrs, σ7.mem⟩
          (by simp [m7, m6, gm]) (by simp [r7, r6, g1])
          (by simp [r7, r6, g2]) (by simp [r7, r6, g81]) (by simp [r7, r6, g87])
          (by simp [r7, r6, g70]) (by simp [r7, r6, g85, hbl, hmx])
        refine ⟨?_, hA, hB, hC⟩
        unfold cCb
        clear * - hk1 hk2 hk4 hfn
        ring_nf at hk2 ⊢
        omega
    · intro hlt2
      have hF : ¬ T.F d (d f) ≤ r := by
        simp [r6, h32, g87] at hlt2; linarith
      have hbl : bl T d r (m + 1) = bl T d r m := by
        rw [bl_succ T d r m hm, ← hf_def, if_neg (fun h => hF h.2)]
      refine r_skip ?_
      obtain ⟨hA, hB, hC⟩ := hfin σ6 (by rw [m6, gm]) (by simp [r6, g1])
        (by simp [r6, g2]) (by simp [r6, g81]) (by simp [r6, g87])
        (by simp [r6, g70]) (by simp [r6, g80, hbl])
      refine ⟨?_, hA, hB, hC⟩
      unfold cCb
      clear * - hk1 hk2 hk4 hfn
      ring_nf at hk2 ⊢
      omega
  · intro hlt
    have hr : f = T.root := by
      by_contra h; simp [r1, hfv, h2, h, cast_val_eq, Fin.val_inj] at hlt
    have hbl : bl T d r (m + 1) = bl T d r m := by
      rw [bl_succ T d r m hm, ← hf_def, if_neg (fun h => (mem_edges_iff T f).mp h.1 hr)]
    refine r_skip ?_
    obtain ⟨hA, hB, hC⟩ := hfin σ1 (by rw [m1]) (by simp [r1, h1]) (by simp [r1, h2])
      (by simp [r1, h81]) (by simp [r1, h87]) (by simp [r1, h70]) (by simp [r1, h80, hbl])
    refine ⟨?_, hA, hB, hC⟩
    unfold cCb
    clear * - hk1
    omega

noncomputable def gA (β : ℝ) (e : Fin n) : ℝ := if d e ≤ β then T.W e else 0

noncomputable def gB (β : ℝ) (e : Fin n) : ℝ := if β < d e then T.W e / d e else 0

/-- The invariant of the loop computing the two sums. -/
def IAB (σ0 : Cfg) (r t β : ℝ) (m : ℕ) (σ : Cfg) : Prop :=
  σ.mem = σ0.mem ∧ σ.regs 1 = n ∧ σ.regs 2 = T.root.val ∧ σ.regs 87 = r ∧ σ.regs 70 = t ∧
    σ.regs 80 = β ∧ σ.regs 89 = psum T m (gA T d β) ∧ σ.regs 90 = psum T m (gB T d β)

theorem abBody_spec (hD : T.Normalized d) (M : ℤ → ℝ) (hM : MemOK T d L M) (σ0 : Cfg)
    (hmem0 : σ0.mem = M) (r t β : ℝ) (m : ℕ) (hm : m < n) (σ : Cfg)
    (hI : IAB T d σ0 r t β m σ) (h81 : σ.regs 81 = m) :
    Runs abBody σ (fun k σ' => k ≤ 30 * n + 60 ∧ σ'.regs 81 = m ∧ σ'.regs 1 = n ∧
      ∀ a b e, IAB T d σ0 r t β (m + 1)
        ⟨update (update (update σ'.regs 83 a) 81 b) 82 e, σ'.ptrs, σ'.mem⟩) := by
  obtain ⟨hmem, h1, h2, h87, h70, h80, h89, h90⟩ := hI
  set f : Fin n := ⟨m, hm⟩ with hf_def
  have hfv : σ.regs 81 = (f.val : ℝ) := h81
  have hdf : σ.mem ((4 + 3 * f.val : ℕ) : ℤ) = d f := by
    rw [hmem, hmem0, hM.1 _ (by positivity), ti_d]
  have hWf : σ.mem ((3 + 3 * f.val : ℕ) : ℤ) = T.W f := by
    rw [hmem, hmem0, hM.1 _ (by positivity), ti_W]
  have hfn : f.val < n := hm
  have hfin : ∀ σ' : Cfg, σ'.mem = σ.mem → σ'.regs 1 = n → σ'.regs 2 = T.root.val →
      σ'.regs 81 = m → σ'.regs 87 = r → σ'.regs 70 = t → σ'.regs 80 = β →
      σ'.regs 89 = psum T (m + 1) (gA T d β) → σ'.regs 90 = psum T (m + 1) (gB T d β) →
      σ'.regs 81 = m ∧ σ'.regs 1 = n ∧ ∀ a b e, IAB T d σ0 r t β (m + 1)
        ⟨update (update (update σ'.regs 83 a) 81 b) 82 e, σ'.ptrs, σ'.mem⟩ := by
    intro σ' hm' h1' h2' h81' h87' h70' h80' h89' h90'
    exact ⟨h81', h1', fun a b e => ⟨by simp [hm', hmem], by simp [update_apply, h1'],
      by simp [update_apply, h2'], by simp [update_apply, h87'], by simp [update_apply, h70'],
      by simp [update_apply, h80'], by simp [update_apply, h89'], by simp [update_apply, h90']⟩⟩
  refine r_seq (r_eqT 84 81 2 (by decide) (by decide) (by decide) σ _
    (fun k1 hk1 z1 σ1 r1 m1 => f_ifle ?_ ?_))
  · intro hle
    have hr : f ≠ T.root := by
      intro h; norm_num [r1, hfv, h2, h, cast_val_eq, Fin.val_inj] at hle
    have hdpos : 0 < d f := hD.1 f ((mem_edges_iff T f).mpr hr)
    have hA1 : psum T (m + 1) (gA T d β) = psum T m (gA T d β) + gA T d β f := by
      rw [psum_succ T _ m hm, ← hf_def, if_pos ((mem_edges_iff T f).mpr hr)]
    have hB1 : psum T (m + 1) (gB T d β) = psum T m (gB T d β) + gB T d β f := by
      rw [psum_succ T _ m hm, ← hf_def, if_pos ((mem_edges_iff T f).mpr hr)]
    refine r_seq (r_ldIn 85 4 81 (by decide) σ1 f.val (by simp [r1, hfv]) _
      (fun k2 hk2 a2 b2 σ2 r2 m2 => ?_))
    have e85 : σ2.regs 85 = d f := by rw [r2, update_self, m1, hdf]
    refine r_seq (r_ldIn 92 3 81 (by decide) σ2 f.val (by simp [r2, r1, hfv]) _
      (fun k3 hk3 a3 b3 σ3 r3 m3 => ?_))
    have e92 : σ3.regs 92 = T.W f := by rw [r3, update_self, m2, m1, hWf]
    have e85' : σ3.regs 85 = d f := by simp [r3, e85]
    refine r_seq (f_sub fun σ4 r4 m4 => f_ifle ?_ ?_)
    · intro hle2
      have hle' : d f ≤ β := by simp [r4, r3, r2, r1, e85', h80] at hle2; linarith
      refine f_add fun σ5 r5 m5 => ?_
      obtain ⟨hA, hB, hC⟩ := hfin σ5 (by rw [m5, m4, m3, m2, m1])
        (by simp [r5, r4, r3, r2, r1, h1]) (by simp [r5, r4, r3, r2, r1, h2])
        (by simp [r5, r4, r3, r2, r1, h81]) (by simp [r5, r4, r3, r2, r1, h87])
        (by simp [r5, r4, r3, r2, r1, h70]) (by simp [r5, r4, r3, r2, r1, h80])
        (by rw [hA1]; simp [r5, r4, e92, gA, hle']; simp [r3, r2, r1, h89])
        (by rw [hB1]; simp [r5, r4, r3, r2, r1, h90, gB, not_lt.mpr hle'])
      refine ⟨?_, hA, hB, hC⟩
      clear * - hk1 hk2 hk3 hfn
      ring_nf at hk2 hk3 ⊢
      omega
    · intro hlt2
      have hlt' : β < d f := by simp [r4, r3, r2, r1, e85', h80] at hlt2; linarith
      refine r_seq (f_div (by simp [r4, e85', hdpos]) fun σ5 r5 m5 => f_add fun σ6 r6 m6 => ?_)
      obtain ⟨hA, hB, hC⟩ := hfin σ6 (by rw [m6, m5, m4, m3, m2, m1])
        (by simp [r6, r5, r4, r3, r2, r1, h1]) (by simp [r6, r5, r4, r3, r2, r1, h2])
        (by simp [r6, r5, r4, r3, r2, r1, h81]) (by simp [r6, r5, r4, r3, r2, r1, h87])
        (by simp [r6, r5, r4, r3, r2, r1, h70]) (by simp [r6, r5, r4, r3, r2, r1, h80])
        (by rw [hA1]; simp [r6, r5, r4, r3, r2, r1, h89, gA, not_le.mpr hlt'])
        (by rw [hB1]; simp [r6, r5, r4, e92, e85', gB, hlt']; simp [r3, r2, r1, h90])
      refine ⟨?_, hA, hB, hC⟩
      clear * - hk1 hk2 hk3 hfn
      ring_nf at hk2 hk3 ⊢
      omega
  · intro hlt
    have hr : f = T.root := by
      by_contra h; simp [r1, hfv, h2, h, cast_val_eq, Fin.val_inj] at hlt
    have hA1 : psum T (m + 1) (gA T d β) = psum T m (gA T d β) := by
      rw [psum_succ T _ m hm, ← hf_def, if_neg (fun h => (mem_edges_iff T f).mp h hr)]; simp
    have hB1 : psum T (m + 1) (gB T d β) = psum T m (gB T d β) := by
      rw [psum_succ T _ m hm, ← hf_def, if_neg (fun h => (mem_edges_iff T f).mp h hr)]; simp
    refine r_skip ?_
    obtain ⟨hA, hB, hC⟩ := hfin σ1 (by rw [m1]) (by simp [r1, h1]) (by simp [r1, h2])
      (by simp [r1, h81]) (by simp [r1, h87]) (by simp [r1, h70]) (by simp [r1, h80])
      (by simp [r1, h89, hA1]) (by simp [r1, h90, hB1])
    refine ⟨?_, hA, hB, hC⟩
    clear * - hk1
    omega

def sPart : Stmt :=
  .seq (.const 80 0) (.seq (forLoop 81 1 82 83 bBody) (.seq (.const 89 0) (.seq (.const 90 0)
    (.seq (forLoop 81 1 82 83 abBody) (.seq (.sub 94 87 89) (.div 91 94 90))))))

/-- `91 := s` from `Rin t` in register `33`. -/
def phaseS : Stmt := .seq (mov 87 33) (.ifle 87 (.const 91 0) sPart)

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
/-- Phase X (`x`), phase C (a good `t`), `Rin t`, phase S (`s`), output. -/
def prog : Stmt :=
  .seq phaseX (.seq phaseC (.seq (mov 30 70) (.seq evalE (.seq phaseS output))))

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
variable {n : ℕ} (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n))
def cS (n : ℕ) : ℕ := n * (cCb n + 5) + n * (30 * n + 65) + 20

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
theorem cost_bound (n len : ℕ) (hlen : len ≤ 2 * n) :
    cX (3 + 3 * n + len) + (cC n + (2 + (cE n + (cS n + 4)))) ≤ 10000 * (n + 1) ^ 4 := by
  set N := n + 1 with hN
  have hn : n ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hA : 3 + 3 * n + len ≤ 5 * N := by omega
  have b1 : cOut (3 + 3 * n + len) ≤ 857 * N ^ 2 := by
    calc cOut (3 + 3 * n + len) ≤ cOut (5 * N) := by unfold cOut; gcongr
      _ ≤ 857 * N ^ 2 := by unfold cOut; nlinarith
  have b2 : cX (3 + 3 * n + len) ≤ 4360 * N ^ 3 := by
    calc cX (3 + 3 * n + len) ≤ 5 * N * (857 * N ^ 2 + 5) + 4 * (5 * N) + 30 := by
          unfold cX; gcongr
      _ ≤ 4360 * N ^ 3 := by nlinarith
  have b3 : cEb n ≤ 280 * N ^ 2 := by
    calc cEb n ≤ cEb N := by unfold cEb; gcongr
      _ ≤ 280 * N ^ 2 := by unfold cEb; nlinarith
  have b4 : cE n ≤ 291 * N ^ 3 := by
    calc cE n ≤ N * (280 * N ^ 2 + 5) + 6 := by unfold cE; gcongr
      _ ≤ 291 * N ^ 3 := by nlinarith
  have b5 : cCb n ≤ 361 * N ^ 3 := by
    unfold cCb; nlinarith
  have b6 : cC n ≤ 435 * N ^ 4 := by
    calc cC n ≤ N * (12 * N + 45) + N * (361 * N ^ 3 + 5) + 12 := by unfold cC; gcongr
      _ ≤ 435 * N ^ 4 := by nlinarith
  have b7 : cS n ≤ 481 * N ^ 4 := by
    calc cS n ≤ N * (361 * N ^ 3 + 5) + N * (30 * N + 65) + 20 := by unfold cS; gcongr
      _ ≤ 481 * N ^ 4 := by nlinarith
  have h3 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right hN1 (by norm_num)
  have h1 : 1 ≤ N ^ 4 := Nat.one_le_pow _ _ hN1
  omega

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
variable {n : ℕ} (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n))
theorem F_le_total (hD : T.Normalized d) (t : ℝ) : T.F d t ≤ ∑ e ∈ T.edges, T.W e := by
  unfold Tree.F
  apply Finset.sum_le_sum
  intro e he
  have hW : 0 ≤ T.W e := (T.W_pos e ((mem_edges_iff T e).mp he)).le
  calc T.W e * min 1 (t / d e) ≤ T.W e * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hW
    _ = T.W e := mul_one _

theorem Rin_nonneg (t : ℝ) : 0 ≤ T.Rin d L t := by
  unfold Tree.Rin
  apply Finset.sum_nonneg
  intro e he
  have he1 : e ∈ T.edges :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
  exact (T.W_pos e ((mem_edges_iff T e).mp he1)).le

theorem Rin_le_R (t : ℝ) : T.Rin d L t ≤ T.R d L t := by
  unfold Tree.Rin Tree.R
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro e he _
  exact (T.W_pos e ((mem_edges_iff T e).mp (Finset.mem_filter.mp he).1)).le

theorem phaseS_spec (hD : T.Normalized d) (M : ℤ → ℝ) (hM : MemOK T d L M) (σ : Cfg)
    (hmem : σ.mem = M) (h1 : σ.regs 1 = n) (h2 : σ.regs 2 = T.root.val) (t : ℝ)
    (h70 : σ.regs 70 = t) (hG : Good T d L t) (h33 : σ.regs 33 = T.Rin d L t)
    (Q : ℕ → Cfg → Prop)
    (hQ : ∀ k, k ≤ cS n → ∀ σ' : Cfg, σ'.mem = σ.mem → σ'.regs 70 = t →
      σ'.regs 91 = (if T.Rin d L t = 0 then 0 else sOf T d (T.Rin d L t)) → Q k σ') :
    Runs phaseS σ Q := by
  refine r_seq (r_mov (by decide) (f_ifle ?_ ?_))
  · intro hle
    have h0 : T.Rin d L t = 0 := by
      simp [h33] at hle; exact le_antisymm hle (Rin_nonneg T d L t)
    refine f_const fun σ1 r1 m1 => hQ _ ?_ σ1 (by simp [m1]) (by simp [r1, h70]) (by simp [r1, h0])
    unfold cS; omega
  · intro hlt
    set r := T.Rin d L t with hr_def
    have hr0 : 0 < r := by simp [h33] at hlt; exact hlt
    have hrW : r < ∑ e ∈ T.edges, T.W e :=
      lt_of_le_of_lt (Rin_le_R T d L t) (lt_of_lt_of_le hG.2 (F_le_total T d hD t))
    have hsp := sOf_spec T d hD r hr0 hrW
    have hrne : r ≠ 0 := hr0.ne'
    refine r_seq (f_const fun σ1 r1 m1 => r_seq ?_)
    refine r_for 81 1 82 83 bBody (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) n (cCb n) (IB T d σ1 r t) σ1 (by simp [r1, h1]) ?_ ?_ _
      (fun k2 σ2 hk2 hI2 => ?_)
    · intro a b
      exact ⟨rfl, by simp [update_apply, r1, h1], by simp [update_apply, r1, h2],
        by simp [update_apply, r1, h33], by simp [update_apply, r1, h70],
        by simp [update_apply, r1, bl_zero]⟩
    · intro m hm σ' hI h81 _
      exact bBody_spec T d L hD M hM σ1 (by simp [m1, hmem]) r t m hm σ' hI h81
    obtain ⟨hm2, g1, g2, g87, g70, g80⟩ := hI2
    rw [bl_all] at g80
    refine r_seq (f_const fun σ3 r3 m3 => r_seq (f_const fun σ4 r4 m4 => r_seq ?_))
    refine r_for 81 1 82 83 abBody (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) n (30 * n + 60) (IAB T d σ1 r t (betaLo T d r)) σ4
      (by simp [r4, r3, g1]) ?_ ?_ _ (fun k5 σ5 hk5 hI5 => ?_)
    · intro a b
      exact ⟨by simp [m4, m3, hm2], by simp [update_apply, r4, r3, g1],
        by simp [update_apply, r4, r3, g2], by simp [update_apply, r4, r3, g87],
        by simp [update_apply, r4, r3, g70], by simp [update_apply, r4, r3, g80],
        by simp [update_apply, r4, r3, psum_zero], by simp [update_apply, r4, r3, psum_zero]⟩
    · intro m hm σ' hI h81 _
      exact abBody_spec T d L hD M hM σ1 (by simp [m1, hmem]) r t _ m hm σ' hI h81
    obtain ⟨hm5, -, -, h587, h570, -, h589, h590⟩ := hI5
    have hA : psum T n (gA T d (betaLo T d r)) =
        ∑ e ∈ T.edges.filter (fun e => d e ≤ betaLo T d r), T.W e := by
      rw [psum_all, Finset.sum_filter]; rfl
    have hB : psum T n (gB T d (betaLo T d r)) =
        ∑ e ∈ T.edges.filter (fun e => betaLo T d r < d e), T.W e / d e := by
      rw [psum_all, Finset.sum_filter]; rfl
    refine r_seq (f_sub fun σ6 r6 m6 => f_div (by simp [r6, h590, hB, hsp.1])
      fun σ7 r7 m7 => ?_)
    refine hQ _ ?_ σ7 (by rw [m7, m6, hm5, m1]) (by simp [r7, r6, h570])
      (by rw [if_neg hrne]; simp [r7, r6, h587, h589, h590, hA, hB, sOf])
    unfold cS
    generalize cCb n = c at *
    rw [show 30 * n + 60 + 5 = 30 * n + 65 by ring] at hk5
    clear * - hk2 hk5
    omega

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.RAM.PartG
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.RAM SmaleNinth Function
theorem algo : ∃ (prog : Stmt) (C p : ℕ), 0 < C ∧
    ∀ (n : ℕ) (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)),
      T.Normalized d → T.DFS L → T.Unequal d →
      ∃ (k : ℕ) (σ : Cfg), Exec prog (Cfg.init (treeInput T d L)) k σ ∧
        k ≤ C * (n + 1) ^ p ∧ T.Budget d L (σ.mem (-1)) (σ.mem (-2)) := by
  refine ⟨prog, 10000, 4, by norm_num, ?_⟩
  intro n T d L hD hL hU
  have hlen := dfs_len T L hL
  suffices h : Runs prog (Cfg.init (treeInput T d L)) (fun k σ => k ≤ 10000 * (n + 1) ^ 4 ∧
      T.Budget d L (σ.mem (-1)) (σ.mem (-2))) by
    obtain ⟨k, σ, hE, hk, hB⟩ := h
    exact ⟨k, σ, hE, hk, hB⟩
  refine r_seq (phaseX_spec T d L hL _ rfl _ (fun k1 σ1 hk1 h1 h2 hin hx => ?_))
  have hM : MemOK T d L σ1.mem := ⟨hin, hx⟩
  refine r_seq (phaseC_spec T d L hD hL hU σ1.mem hM σ1 rfl h1 h2 _
    (fun k2 hk2 σ2 hm2 g1 g2 hG => ?_))
  set t := σ2.regs 70 with ht
  refine r_seq (r_mov (by decide) (r_seq (evalE_spec T d L hD σ1.mem hM _ (by simp [hm2]) t
    (by simp [ht]) (by simp [g1]) (by simp [g2]) _ (fun k3 hk3 σ3 hm3 hfr3 h31 h32 h33 => ?_))))
  have f1 : σ3.regs 1 = n := by rw [hfr3 1 (by decide)]; simp [g1]
  have f2 : σ3.regs 2 = T.root.val := by rw [hfr3 2 (by decide)]; simp [g2]
  have f70 : σ3.regs 70 = t := by rw [hfr3 70 (by decide)]; simp [ht]
  refine r_seq (phaseS_spec T d L hD σ1.mem hM σ3 (by simp [hm3, hm2]) f1 f2 t f70 hG h33 _
    (fun k4 hk4 σ4 hm4 h470 h491 => ?_))
  refine r_seq (r_pset (r_seq (r_store (r_seq (r_pset (r_store ⟨?_, ?_⟩))))))
  · have := cost_bound n L.length hlen.2
    clear * - this hk1 hk2 hk3 hk4
    omega
  · simp only [update_apply]
    simp only [show ((-1 : ℤ) = -2) = False by decide, if_false, if_true, h491, h470]
    exact budget_of T d L hD hL t hG.1 hG.2

end OnlineTransportation1195.Dev.RAM.PartG
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Dev.RAM
open OnlineTransportation1195.Main SmaleNinth
/-! ## Part G: the algorithm -/
alias algo := OnlineTransportation1195.Dev.RAM.PartG.algo

theorem main : ∃ (P : SmaleNinth.RAMProgram) (C power : ℕ),
      RationalProgram P ∧ 0 < C ∧
      ∀ (n : ℕ) (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)),
        T.Normalized d → T.DFS L → T.Unequal d →
        ∃ fuel : ℕ, fuel ≤ C * (n + 1) ^ power ∧
          PositiveDivisions P (treeInput T d L) fuel ∧
          SmaleNinth.RAMHaltedWith P (SmaleNinth.RAMRun P (treeInput T d L) fuel) true ∧
          T.Budget d L
            ((SmaleNinth.RAMRun P (treeInput T d L) fuel).mem (-1))
            ((SmaleNinth.RAMRun P (treeInput T d L) fuel).mem (-2)) := by
  obtain ⟨prog, C, p, hC, h⟩ := algo
  refine ⟨program prog, C, p, program_rational prog, hC, ?_⟩
  intro n T d L hD hL hU
  obtain ⟨k, σ, hE, hk, hB⟩ := h n T d L hD hL hU
  obtain ⟨h1, h2, h3⟩ := program_correct prog _ k σ hE
  exact ⟨k, hk, h1, h2, by rw [h3]; exact hB⟩

end OnlineTransportation1195.Dev.RAM
end

section
open scoped BigOperators
open Classical
set_option autoImplicit false
namespace OnlineTransportation1195.Main
theorem chk_constructible_root_patch_budgets :
    ∃ (P : SmaleNinth.RAMProgram) (C power : ℕ),
      RationalProgram P ∧ 0 < C ∧
      ∀ (n : ℕ) (T : Tree n) (d : Fin n → ℝ) (L : List (Fin n)),
        T.Normalized d → T.DFS L → T.Unequal d →
        ∃ fuel : ℕ, fuel ≤ C * (n + 1) ^ power ∧
          PositiveDivisions P (treeInput T d L) fuel ∧
          SmaleNinth.RAMHaltedWith P (SmaleNinth.RAMRun P (treeInput T d L) fuel) true ∧
          T.Budget d L
            ((SmaleNinth.RAMRun P (treeInput T d L) fuel).mem (-1))
            ((SmaleNinth.RAMRun P (treeInput T d L) fuel).mem (-2)) :=
  OnlineTransportation1195.Dev.RAM.main

end OnlineTransportation1195.Main
end

theorem solution : type_of% @OnlineTransportation1195.Main.chk_constructible_root_patch_budgets := @OnlineTransportation1195.Main.chk_constructible_root_patch_budgets

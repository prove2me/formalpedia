-- Prove2me | solution 1 for SubspaceEvasion312.Explicit.local_graph
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:34:38.694615+00:00
-- url     : https://prove2.me/submissions/4396b8ae-7ed2-4bc9-89cd-d9befed1fb80

import Mathlib
import Definitions.Def_SubspaceEvasion312_Explicit_local_search

section
set_option autoImplicit false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.LG
open SubspaceEvasion312.Explicit

/-! ## A structured layer over the register machine

Nat registers 60 and 61 are reserved temporaries: the region store/load macros and the loop
increment use them.  Field memory regions are residue classes modulo 16. -/

variable {F : Type} [Field F]

structure rt_St (F : Type) where
  nr : ℕ → ℕ
  fr : ℕ → F
  out : List F

def rt_simple : Instruction F → Bool
  | .literal _ _ => true
  | .inputNat _ _ => true
  | .addNat _ _ _ => true
  | .subNat _ _ _ => true
  | .mulNat _ _ _ => true
  | .divNat _ _ _ => true
  | .modNat _ _ _ => true
  | .constant _ _ => true
  | .add _ _ _ => true
  | .sub _ _ _ => true
  | .mul _ _ _ => true
  | .output _ => true
  | _ => false

def rt_setN (s : rt_St F) (d v : ℕ) : rt_St F := {s with nr := Function.update s.nr d v}
def rt_setF (s : rt_St F) (d : ℕ) (v : F) : rt_St F := {s with fr := Function.update s.fr d v}

def rt_eff (ns : List ℕ) (s : rt_St F) : Instruction F → rt_St F
  | .literal d v => rt_setN s d v
  | .inputNat d i => rt_setN s d (ns.getD i 0)
  | .addNat d a b => rt_setN s d (s.nr a + s.nr b)
  | .subNat d a b => rt_setN s d (s.nr a - s.nr b)
  | .mulNat d a b => rt_setN s d (s.nr a * s.nr b)
  | .divNat d a b => rt_setN s d (s.nr a / s.nr b)
  | .modNat d a b => rt_setN s d (s.nr a % s.nr b)
  | .constant d v => rt_setF s d v
  | .add d a b => rt_setF s d (s.fr a + s.fr b)
  | .sub d a b => rt_setF s d (s.fr a - s.fr b)
  | .mul d a b => rt_setF s d (s.fr a * s.fr b)
  | .output a => {s with out := s.fr a :: s.out}
  | _ => s

def rt_Bd (B : ℕ) (s : rt_St F) : Prop := ∀ i, s.nr i ≤ B

inductive rt_Cmd (F : Type) where
  | basic (i : Instruction F)
  | stR (k off src : ℕ)
  | ldR (dst k off : ℕ)
  | seq (a b : rt_Cmd F)
  | ifN (x y : ℕ) (t e : rt_Cmd F)
  | ifF (x y : ℕ) (t e : rt_Cmd F)
  | loop (i n : ℕ) (body : rt_Cmd F)

def rt_stRes (s : rt_St F) (k off src : ℕ) : rt_St F :=
  ⟨Function.update (Function.update s.nr 60 (s.nr off * 16 + k)) 61 k,
   Function.update s.fr (s.nr off * 16 + k) (s.fr src), s.out⟩

def rt_ldRes (s : rt_St F) (dst k off : ℕ) : rt_St F :=
  ⟨Function.update (Function.update s.nr 60 (s.nr off * 16 + k)) 61 k,
   Function.update s.fr dst (s.fr (s.nr off * 16 + k)), s.out⟩

def rt_inc (s : rt_St F) (i : ℕ) : rt_St F :=
  ⟨Function.update (Function.update s.nr 61 1) i (Function.update s.nr 61 1 i + 1), s.fr, s.out⟩

inductive rt_Exec (ns : List ℕ) (B : ℕ) : rt_Cmd F → rt_St F → ℕ → rt_St F → Prop
  | basic {i : Instruction F} {s : rt_St F} : rt_simple i = true → rt_Bd B s →
      rt_Exec ns B (.basic i) s 1 (rt_eff ns s i)
  | stR {k off src : ℕ} {s : rt_St F} : off ≠ 61 → rt_Bd B s → s.nr off * 16 + k + 16 ≤ B →
      rt_Exec ns B (.stR k off src) s 5 (rt_stRes s k off src)
  | ldR {dst k off : ℕ} {s : rt_St F} : off ≠ 61 → rt_Bd B s → s.nr off * 16 + k + 16 ≤ B →
      rt_Exec ns B (.ldR dst k off) s 5 (rt_ldRes s dst k off)
  | seq {a b : rt_Cmd F} {s s1 s2 : rt_St F} {n1 n2 : ℕ} :
      rt_Exec ns B a s n1 s1 → rt_Exec ns B b s1 n2 s2 → rt_Exec ns B (.seq a b) s (n1 + n2) s2
  | ifNT {x y : ℕ} {t e : rt_Cmd F} {s s' : rt_St F} {n : ℕ} : rt_Bd B s → s.nr x = s.nr y →
      rt_Exec ns B t s n s' → rt_Bd B s' → rt_Exec ns B (.ifN x y t e) s (n + 2) s'
  | ifNF {x y : ℕ} {t e : rt_Cmd F} {s s' : rt_St F} {n : ℕ} : rt_Bd B s → s.nr x ≠ s.nr y →
      rt_Exec ns B e s n s' → rt_Exec ns B (.ifN x y t e) s (n + 1) s'
  | ifFT {x y : ℕ} {t e : rt_Cmd F} {s s' : rt_St F} {n : ℕ} : rt_Bd B s → s.fr x = s.fr y →
      rt_Exec ns B t s n s' → rt_Bd B s' → rt_Exec ns B (.ifF x y t e) s (n + 2) s'
  | ifFF {x y : ℕ} {t e : rt_Cmd F} {s s' : rt_St F} {n : ℕ} : rt_Bd B s → s.fr x ≠ s.fr y →
      rt_Exec ns B e s n s' → rt_Exec ns B (.ifF x y t e) s (n + 1) s'
  | loopD {i n : ℕ} {body : rt_Cmd F} {s : rt_St F} : rt_Bd B s → s.nr i = s.nr n →
      rt_Exec ns B (.loop i n body) s 1 s
  | loopS {i n : ℕ} {body : rt_Cmd F} {s s1 s2 : rt_St F} {n1 n2 : ℕ} : rt_Bd B s →
      s.nr i ≠ s.nr n → rt_Exec ns B body s n1 s1 → rt_Bd B s1 → rt_Bd B (rt_inc s1 i) →
      rt_Exec ns B (.loop i n body) (rt_inc s1 i) n2 s2 →
      rt_Exec ns B (.loop i n body) s (n1 + 4 + n2) s2

def rt_len : rt_Cmd F → ℕ
  | .basic _ => 1
  | .stR _ _ _ => 5
  | .ldR _ _ _ => 5
  | .seq a b => rt_len a + rt_len b
  | .ifN _ _ t e => rt_len t + rt_len e + 2
  | .ifF _ _ t e => rt_len t + rt_len e + 2
  | .loop _ _ b => rt_len b + 4

def rt_comp : rt_Cmd F → ℕ → List (Instruction F)
  | .basic i, _ => [i]
  | .stR k off src, _ =>
      [.literal 61 16, .mulNat 60 off 61, .literal 61 k, .addNat 60 60 61, .store 60 src]
  | .ldR dst k off, _ =>
      [.literal 61 16, .mulNat 60 off 61, .literal 61 k, .addNat 60 60 61, .load dst 60]
  | .seq a b, p => rt_comp a p ++ rt_comp b (p + rt_len a)
  | .ifN x y t e, p => [.branchNat x y (p + 1) (p + 2 + rt_len t)] ++ rt_comp t (p + 1) ++
      [.jump (p + 2 + rt_len t + rt_len e)] ++ rt_comp e (p + 2 + rt_len t)
  | .ifF x y t e, p => [.branch x y (p + 1) (p + 2 + rt_len t)] ++ rt_comp t (p + 1) ++
      [.jump (p + 2 + rt_len t + rt_len e)] ++ rt_comp e (p + 2 + rt_len t)
  | .loop i n b, p => [.branchNat i n (p + 4 + rt_len b) (p + 1)] ++ rt_comp b (p + 1) ++
      [.literal 61 1, .addNat i i 61, .jump p]

theorem rt_comp_length (c : rt_Cmd F) : ∀ p, (rt_comp c p).length = rt_len c := by
  induction c with
  | basic i => intro p; rfl
  | stR => intro p; rfl
  | ldR => intro p; rfl
  | seq a b iha ihb => intro p; simp [rt_comp, rt_len, iha, ihb]
  | ifN x y t e iht ihe => intro p; simp [rt_comp, rt_len, iht, ihe]; try omega
  | ifF x y t e iht ihe => intro p; simp [rt_comp, rt_len, iht, ihe]; try omega
  | loop i n b ih => intro p; simp [rt_comp, rt_len, ih]; try omega

/-! ### Machine-level simulation -/

def rt_mk (pc : ℕ) (s : rt_St F) : MachineState F := ⟨pc, s.nr, s.fr, s.out, []⟩

inductive rt_reach (P : Program F) (ns : List ℕ) (B : ℕ) :
    ℕ → MachineState F → MachineState F → Prop
  | zero (w : MachineState F) : rt_reach P ns B 0 w w
  | succ {n : ℕ} {w w1 w' : MachineState F} : (∀ i, w.natReg i ≤ B) →
      P[w.pc]? ≠ some .halt → step P ns [] w = some w1 → rt_reach P ns B n w1 w' →
      rt_reach P ns B (n + 1) w w'

theorem rt_reach_trans {P : Program F} {ns : List ℕ} {B a b : ℕ} {w1 w2 w3 : MachineState F}
    (h1 : rt_reach P ns B a w1 w2) (h2 : rt_reach P ns B b w2 w3) :
    rt_reach P ns B (a + b) w1 w3 := by
  induction h1 with
  | zero => simpa using h2
  | @succ n w w1 w' hb hh hs _ ih =>
    rw [show n + 1 + b = (n + b) + 1 by omega]
    exact rt_reach.succ hb hh hs (ih h2)

theorem rt_runFrom_of_reach {P : Program F} {ns : List ℕ} {B n : ℕ} {w w' : MachineState F}
    (h : rt_reach P ns B n w w') (t : ℕ) :
    runFrom P ns [] B (n + t) w = runFrom P ns [] B t w' := by
  induction h with
  | zero => simp
  | @succ n w w1 w' hb hh hs _ ih =>
    rw [show n + 1 + t = (n + t) + 1 by omega]
    simp only [runFrom, hb, implies_true, if_true]
    rw [hs]; simpa using ih

def rt_seg (P : Program F) (b : ℕ) (l : List (Instruction F)) : Prop :=
  ∀ k < l.length, P[b + k]? = l[k]?

theorem rt_seg_left {P : Program F} {b : ℕ} {l1 l2 : List (Instruction F)}
    (h : rt_seg P b (l1 ++ l2)) : rt_seg P b l1 := by
  intro k hk
  have := h k (by simp; omega)
  rw [this, List.getElem?_append_left hk]

theorem rt_seg_right {P : Program F} {b : ℕ} {l1 l2 : List (Instruction F)}
    (h : rt_seg P b (l1 ++ l2)) : rt_seg P (b + l1.length) l2 := by
  intro k hk
  have := h (l1.length + k) (by simp; omega)
  rw [show b + l1.length + k = b + (l1.length + k) by omega, this,
    List.getElem?_append_right (by omega)]
  simp

theorem rt_seg_at {P : Program F} {b : ℕ} {l : List (Instruction F)} (h : rt_seg P b l)
    (k : ℕ) (hk : k < l.length) : P[b + k]? = some l[k] := by
  rw [h k hk]; simp [hk]

theorem rt_bd_mk {B pc : ℕ} {s : rt_St F} (h : rt_Bd B s) : ∀ i, (rt_mk pc s).natReg i ≤ B := h

/-- One simple instruction. -/
theorem rt_step_simple {P : Program F} {ns : List ℕ} {pc : ℕ} {s : rt_St F} {i : Instruction F}
    (hP : P[pc]? = some i) (hs : rt_simple i = true) :
    step P ns [] (rt_mk pc s) = some (rt_mk (pc + 1) (rt_eff ns s i)) := by
  cases i <;> simp_all [step, rt_mk, rt_eff, rt_simple, rt_setN, rt_setF]

theorem rt_ne_halt_of {P : Program F} {pc : ℕ} {i : Instruction F} (hP : P[pc]? = some i)
    (hi : i ≠ .halt) : P[pc]? ≠ some .halt := by
  rw [hP]; intro h; exact hi (Option.some_inj.mp h)

theorem rt_simple_ne_halt {i : Instruction F} (h : rt_simple i = true) : i ≠ .halt := by
  rintro rfl; simp [rt_simple] at h

theorem rt_reach_one {P : Program F} {ns : List ℕ} {B pc : ℕ} {s : rt_St F} {i : Instruction F}
    {w' : MachineState F} {n : ℕ}
    (hP : P[pc]? = some i) (hs : rt_simple i = true) (hb : rt_Bd B s)
    (h : rt_reach P ns B n (rt_mk (pc + 1) (rt_eff ns s i)) w') :
    rt_reach P ns B (n + 1) (rt_mk pc s) w' :=
  rt_reach.succ (rt_bd_mk hb) (rt_ne_halt_of hP (rt_simple_ne_halt hs)) (rt_step_simple hP hs) h

theorem rt_Bd_setN {B d v : ℕ} {s : rt_St F} (h : rt_Bd B s) (hv : v ≤ B) :
    rt_Bd B (rt_setN s d v) := by
  intro i; simp only [rt_setN, Function.update_apply]; split_ifs <;> [exact hv; exact h i]

theorem rt_reach_jump {P : Program F} {ns : List ℕ} {B pc tgt : ℕ} {s : rt_St F}
    (hP : P[pc]? = some (.jump tgt)) (hb : rt_Bd B s) :
    rt_reach P ns B 1 (rt_mk pc s) (rt_mk tgt s) :=
  rt_reach.succ (rt_bd_mk hb) (rt_ne_halt_of hP (by simp)) (by simp [step, rt_mk, hP])
    (rt_reach.zero _)

theorem rt_reach_brN {P : Program F} {ns : List ℕ} {B pc x y yes no : ℕ} {s : rt_St F}
    (hP : P[pc]? = some (.branchNat x y yes no)) (hb : rt_Bd B s) :
    rt_reach P ns B 1 (rt_mk pc s) (rt_mk (if s.nr x = s.nr y then yes else no) s) :=
  rt_reach.succ (rt_bd_mk hb) (rt_ne_halt_of hP (by simp))
    (by by_cases h : s.nr x = s.nr y <;> simp [step, rt_mk, hP, h]) (rt_reach.zero _)

open Classical in
theorem rt_reach_brF {P : Program F} {ns : List ℕ} {B pc x y yes no : ℕ} {s : rt_St F}
    (hP : P[pc]? = some (.branch x y yes no)) (hb : rt_Bd B s) :
    rt_reach P ns B 1 (rt_mk pc s) (rt_mk (if s.fr x = s.fr y then yes else no) s) :=
  rt_reach.succ (rt_bd_mk hb) (rt_ne_halt_of hP (by simp))
    (by by_cases h : s.fr x = s.fr y <;> simp [step, rt_mk, hP, h]) (rt_reach.zero _)

theorem rt_sim {P : Program F} {ns : List ℕ} {B : ℕ} {c : rt_Cmd F} {s s' : rt_St F} {n : ℕ}
    (h : rt_Exec ns B c s n s') :
    ∀ base, rt_seg P base (rt_comp c base) →
      rt_reach P ns B n (rt_mk base s) (rt_mk (base + rt_len c) s') := by
  induction h with
  | @basic i s hs hb =>
    intro base hseg
    have hP := rt_seg_at hseg 0 (by simp [rt_comp])
    simp only [rt_comp, add_zero, List.getElem_cons_zero] at hP
    exact rt_reach_one hP hs hb (rt_reach.zero _)
  | @stR k off src s hoff hb hB =>
    intro base hseg
    have g := fun j (hj : j < 5) => rt_seg_at hseg j (by simp [rt_comp]; omega)
    simp only [rt_comp] at g
    have h0 := g 0 (by omega); have h1 := g 1 (by omega); have h2 := g 2 (by omega)
    have h3 := g 3 (by omega); have h4 := g 4 (by omega)
    simp only [add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4
    refine rt_reach.succ (rt_bd_mk hb) (rt_ne_halt_of h0 (by simp))
      (by simp [step, rt_mk, h0] <;> rfl) ?_
    refine rt_reach.succ ?_ (rt_ne_halt_of h1 (by simp)) (by simp [step, h1] <;> rfl) ?_
    · intro i; simp only [Function.update_apply]; split_ifs <;> first | omega | exact hb i | (exfalso; omega)
    refine rt_reach.succ ?_ (rt_ne_halt_of h2 (by simp)) (by simp [step, h2] <;> rfl) ?_
    · intro i; simp only [Function.update_apply]; split_ifs <;> first | omega | exact hb i | (exfalso; omega)
    refine rt_reach.succ ?_ (rt_ne_halt_of h3 (by simp)) (by simp [step, h3] <;> rfl) ?_
    · intro i; simp only [Function.update_apply]; split_ifs <;> first | omega | exact hb i | (exfalso; omega)
    refine rt_reach.succ ?_ (rt_ne_halt_of h4 (by simp)) (by simp [step, h4] <;> rfl) ?_
    · intro i; simp only [Function.update_apply]; split_ifs <;> first | omega | exact hb i | (exfalso; omega)
    convert rt_reach.zero (P := P) (ns := ns) (B := B) _ using 1
    simp only [rt_mk, rt_stRes, rt_len, Function.update_apply, hoff, if_false]
    congr 1
    all_goals first | omega | (funext x; by_cases h60 : x = 60 <;> by_cases h61 : x = 61 <;> simp_all)
  | @ldR dst k off s hoff hb hB =>
    intro base hseg
    have g := fun j (hj : j < 5) => rt_seg_at hseg j (by simp [rt_comp]; omega)
    simp only [rt_comp] at g
    have h0 := g 0 (by omega); have h1 := g 1 (by omega); have h2 := g 2 (by omega)
    have h3 := g 3 (by omega); have h4 := g 4 (by omega)
    simp only [add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4
    refine rt_reach.succ (rt_bd_mk hb) (rt_ne_halt_of h0 (by simp))
      (by simp [step, rt_mk, h0] <;> rfl) ?_
    refine rt_reach.succ ?_ (rt_ne_halt_of h1 (by simp)) (by simp [step, h1] <;> rfl) ?_
    · intro i; simp only [Function.update_apply]; split_ifs <;> first | omega | exact hb i | (exfalso; omega)
    refine rt_reach.succ ?_ (rt_ne_halt_of h2 (by simp)) (by simp [step, h2] <;> rfl) ?_
    · intro i; simp only [Function.update_apply]; split_ifs <;> first | omega | exact hb i | (exfalso; omega)
    refine rt_reach.succ ?_ (rt_ne_halt_of h3 (by simp)) (by simp [step, h3] <;> rfl) ?_
    · intro i; simp only [Function.update_apply]; split_ifs <;> first | omega | exact hb i | (exfalso; omega)
    refine rt_reach.succ ?_ (rt_ne_halt_of h4 (by simp)) (by simp [step, h4] <;> rfl) ?_
    · intro i; simp only [Function.update_apply]; split_ifs <;> first | omega | exact hb i | (exfalso; omega)
    convert rt_reach.zero (P := P) (ns := ns) (B := B) _ using 1
    simp only [rt_mk, rt_ldRes, rt_len, Function.update_apply, hoff, if_false]
    congr 1
    all_goals first | omega | (funext x; by_cases h60 : x = 60 <;> by_cases h61 : x = 61 <;> simp_all)
  | @seq a b s s1 s2 n1 n2 _ _ iha ihb =>
    intro base hseg
    simp only [rt_comp] at hseg
    have := rt_reach_trans (iha base (rt_seg_left hseg))
      (ihb _ (by have := rt_seg_right hseg; rwa [rt_comp_length] at this))
    simpa [rt_len, add_assoc] using this
  | @ifNT x y t e s s' n hb hxy _ hb' iht =>
    intro base hseg
    simp only [rt_comp] at hseg
    have hs1 := rt_seg_left (rt_seg_left (rt_seg_left hseg))
    have hs2 := rt_seg_right (rt_seg_left (rt_seg_left hseg))
    have hs3 := rt_seg_right (rt_seg_left hseg)
    simp only [List.length_singleton, List.length_append, rt_comp_length] at hs2 hs3
    have h0 := rt_seg_at hs1 0 (by simp)
    have hj := rt_seg_at hs3 0 (by simp)
    simp only [add_zero, List.getElem_cons_zero] at h0 hj
    rw [show base + (1 + rt_len t) = base + 1 + rt_len t by omega] at hj
    have r1 := rt_reach_brN (ns := ns) h0 hb
    rw [if_pos hxy] at r1
    have r2 := iht (base + 1) (by simpa [add_comm] using hs2)
    have r3 := rt_reach_jump (ns := ns) hj hb'
    have := rt_reach_trans (rt_reach_trans r1 r2) r3
    rw [show base + rt_len (rt_Cmd.ifN x y t e) = base + 2 + rt_len t + rt_len e by
      simp [rt_len]; omega]
    convert this using 1; omega
  | @ifNF x y t e s s' n hb hxy _ ihe =>
    intro base hseg
    simp only [rt_comp] at hseg
    have hs1 := rt_seg_left (rt_seg_left (rt_seg_left hseg))
    have hs4 := rt_seg_right hseg
    simp only [List.length_singleton, List.length_append, rt_comp_length] at hs4
    rw [show base + (1 + rt_len t + 1) = base + 2 + rt_len t by omega] at hs4
    have h0 := rt_seg_at hs1 0 (by simp)
    simp only [add_zero, List.getElem_cons_zero] at h0
    have r1 := rt_reach_brN (ns := ns) h0 hb
    rw [if_neg hxy] at r1
    have r2 := ihe _ hs4
    have := rt_reach_trans r1 r2
    rw [show base + rt_len (rt_Cmd.ifN x y t e) = base + 2 + rt_len t + rt_len e by
      simp [rt_len]; omega]
    convert this using 1; omega
  | @ifFT x y t e s s' n hb hxy _ hb' iht =>
    intro base hseg
    simp only [rt_comp] at hseg
    have hs1 := rt_seg_left (rt_seg_left (rt_seg_left hseg))
    have hs2 := rt_seg_right (rt_seg_left (rt_seg_left hseg))
    have hs3 := rt_seg_right (rt_seg_left hseg)
    simp only [List.length_singleton, List.length_append, rt_comp_length] at hs2 hs3
    have h0 := rt_seg_at hs1 0 (by simp)
    have hj := rt_seg_at hs3 0 (by simp)
    simp only [add_zero, List.getElem_cons_zero] at h0 hj
    rw [show base + (1 + rt_len t) = base + 1 + rt_len t by omega] at hj
    have r1 := rt_reach_brF (ns := ns) h0 hb
    rw [if_pos hxy] at r1
    have r2 := iht (base + 1) (by simpa [add_comm] using hs2)
    have r3 := rt_reach_jump (ns := ns) hj hb'
    have := rt_reach_trans (rt_reach_trans r1 r2) r3
    rw [show base + rt_len (rt_Cmd.ifF x y t e) = base + 2 + rt_len t + rt_len e by
      simp [rt_len]; omega]
    convert this using 1; omega
  | @ifFF x y t e s s' n hb hxy _ ihe =>
    intro base hseg
    simp only [rt_comp] at hseg
    have hs1 := rt_seg_left (rt_seg_left (rt_seg_left hseg))
    have hs4 := rt_seg_right hseg
    simp only [List.length_singleton, List.length_append, rt_comp_length] at hs4
    rw [show base + (1 + rt_len t + 1) = base + 2 + rt_len t by omega] at hs4
    have h0 := rt_seg_at hs1 0 (by simp)
    simp only [add_zero, List.getElem_cons_zero] at h0
    have r1 := rt_reach_brF (ns := ns) h0 hb
    rw [if_neg hxy] at r1
    have r2 := ihe _ hs4
    have := rt_reach_trans r1 r2
    rw [show base + rt_len (rt_Cmd.ifF x y t e) = base + 2 + rt_len t + rt_len e by
      simp [rt_len]; omega]
    convert this using 1; omega
  | @loopD i n body s hb hin =>
    intro base hseg
    simp only [rt_comp] at hseg
    have h0 := rt_seg_at (rt_seg_left (rt_seg_left hseg)) 0 (by simp)
    simp only [add_zero, List.getElem_cons_zero] at h0
    have r1 := rt_reach_brN (ns := ns) h0 hb
    rw [if_pos hin] at r1
    rw [show base + rt_len (rt_Cmd.loop i n body) = base + 4 + rt_len body by
      simp [rt_len]; omega]
    exact r1
  | @loopS i n body s s1 s2 n1 n2 hb hin _ hb1 hbi _ ihb ihl =>
    intro base hseg
    have hseg' := hseg
    simp only [rt_comp] at hseg
    have h0 := rt_seg_at (rt_seg_left (rt_seg_left hseg)) 0 (by simp)
    have hs2 := rt_seg_right (rt_seg_left hseg)
    have hs3 := rt_seg_right hseg
    simp only [List.length_singleton, List.length_append, rt_comp_length] at hs2 hs3
    simp only [add_zero, List.getElem_cons_zero] at h0
    have g0 := rt_seg_at hs3 0 (by simp)
    have g1 := rt_seg_at hs3 1 (by simp)
    have g2 := rt_seg_at hs3 2 (by simp)
    simp only [add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at g0 g1 g2
    rw [show base + (1 + rt_len body) = base + 1 + rt_len body by omega] at g0 g1 g2
    have r1 := rt_reach_brN (ns := ns) h0 hb
    rw [if_neg hin] at r1
    have hbody := ihb (base + 1) (by simpa [add_comm] using hs2)
    have hbm : ∀ j, (Function.update s1.nr 61 1) j ≤ B := by
      intro j; simp only [Function.update_apply]; split_ifs with hj
      · have := hbi 61; simp only [rt_inc, Function.update_apply] at this
        split_ifs at this <;> omega
      · exact hb1 j
    have hrest : rt_reach P ns B 3 (rt_mk (base + 1 + rt_len body) s1)
        (rt_mk base (rt_inc s1 i)) := by
      refine rt_reach.succ (rt_bd_mk hb1) (rt_ne_halt_of g0 (by simp))
        (by simp [step, rt_mk, g0] <;> rfl) ?_
      refine rt_reach.succ hbm (rt_ne_halt_of g1 (by simp))
        (by simp [step, g1] <;> rfl) ?_
      refine rt_reach.succ (rt_bd_mk hbi) (rt_ne_halt_of g2 (by simp))
        (by simp [step, g2] <;> rfl) ?_
      exact rt_reach.zero _
    have := rt_reach_trans (rt_reach_trans (rt_reach_trans r1 hbody) hrest) (ihl base hseg')
    convert this using 1
    omega

/-- Running a whole structured program followed by `halt`. -/
theorem rt_run {ns : List ℕ} {B : ℕ} {c : rt_Cmd F} {s : rt_St F} {n : ℕ}
    (h : rt_Exec ns B c (⟨fun _ => 0, fun _ => 0, []⟩ : rt_St F) n s) (hb : rt_Bd B s) :
    runFrom (rt_comp c 0 ++ [.halt]) ns [] B (n + 1) initialState =
      some (rt_mk (rt_len c) s) := by
  have hseg : rt_seg (rt_comp c 0 ++ [.halt]) 0 (rt_comp c 0) := by
    intro k hk; simp [List.getElem?_append_left hk]
  have hr := rt_sim h 0 hseg
  have e : (initialState : MachineState F) = rt_mk 0 ⟨fun _ => 0, fun _ => 0, []⟩ := rfl
  rw [e, rt_runFrom_of_reach hr 1]
  simp only [zero_add]
  have hh : (rt_comp c 0 ++ [Instruction.halt])[rt_len c]? = some .halt := by
    rw [List.getElem?_append_right (by rw [rt_comp_length])]; simp [rt_comp_length]
  simp [runFrom, rt_mk, hh, show ∀ i, s.nr i ≤ B from hb]

/-! ### Hoare-style specifications -/

def rt_Sp (ns : List ℕ) (B : ℕ) (c : rt_Cmd F) (P Q : rt_St F → Prop) (N : ℕ) : Prop :=
  ∀ s, P s → ∃ n s', n ≤ N ∧ rt_Exec ns B c s n s' ∧ Q s'

section Hoare
variable {ns : List ℕ} {B : ℕ}

theorem rt_sp_conseq {c : rt_Cmd F} {P Q P' Q' : rt_St F → Prop} {N N' : ℕ}
    (h : rt_Sp ns B c P Q N) (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s) (hN : N ≤ N') :
    rt_Sp ns B c P' Q' N' := by
  intro s hs
  obtain ⟨n, s', hn, he, hq⟩ := h s (hP s hs)
  exact ⟨n, s', by omega, he, hQ _ hq⟩

theorem rt_sp_basic {i : Instruction F} {P Q : rt_St F → Prop} (hi : rt_simple i = true)
    (h : ∀ s, P s → rt_Bd B s ∧ Q (rt_eff ns s i)) : rt_Sp ns B (.basic i) P Q 1 := by
  intro s hs
  exact ⟨1, _, le_rfl, rt_Exec.basic hi (h s hs).1, (h s hs).2⟩

theorem rt_sp_seq {a b : rt_Cmd F} {P R Q : rt_St F → Prop} {N1 N2 : ℕ}
    (ha : rt_Sp ns B a P R N1) (hb : rt_Sp ns B b R Q N2) :
    rt_Sp ns B (.seq a b) P Q (N1 + N2) := by
  intro s hs
  obtain ⟨n1, s1, hn1, he1, hr⟩ := ha s hs
  obtain ⟨n2, s2, hn2, he2, hq⟩ := hb s1 hr
  exact ⟨n1 + n2, s2, by omega, rt_Exec.seq he1 he2, hq⟩

theorem rt_sp_ifN {x y : ℕ} {t e : rt_Cmd F} {P Q : rt_St F → Prop} {N1 N2 : ℕ}
    (hb : ∀ s, P s → rt_Bd B s)
    (ht : rt_Sp ns B t (fun s => P s ∧ s.nr x = s.nr y) (fun s => Q s ∧ rt_Bd B s) N1)
    (he : rt_Sp ns B e (fun s => P s ∧ s.nr x ≠ s.nr y) Q N2) :
    rt_Sp ns B (.ifN x y t e) P Q (max N1 N2 + 2) := by
  intro s hs
  by_cases hxy : s.nr x = s.nr y
  · obtain ⟨n, s', hn, he', hq, hb'⟩ := ht s ⟨hs, hxy⟩
    exact ⟨n + 2, s', by omega, rt_Exec.ifNT (hb s hs) hxy he' hb', hq⟩
  · obtain ⟨n, s', hn, he', hq⟩ := he s ⟨hs, hxy⟩
    exact ⟨n + 1, s', by omega, rt_Exec.ifNF (hb s hs) hxy he', hq⟩

theorem rt_sp_ifF {x y : ℕ} {t e : rt_Cmd F} {P Q : rt_St F → Prop} {N1 N2 : ℕ}
    (hb : ∀ s, P s → rt_Bd B s)
    (ht : rt_Sp ns B t (fun s => P s ∧ s.fr x = s.fr y) (fun s => Q s ∧ rt_Bd B s) N1)
    (he : rt_Sp ns B e (fun s => P s ∧ s.fr x ≠ s.fr y) Q N2) :
    rt_Sp ns B (.ifF x y t e) P Q (max N1 N2 + 2) := by
  intro s hs
  by_cases hxy : s.fr x = s.fr y
  · obtain ⟨n, s', hn, he', hq, hb'⟩ := ht s ⟨hs, hxy⟩
    exact ⟨n + 2, s', by omega, rt_Exec.ifFT (hb s hs) hxy he' hb', hq⟩
  · obtain ⟨n, s', hn, he', hq⟩ := he s ⟨hs, hxy⟩
    exact ⟨n + 1, s', by omega, rt_Exec.ifFF (hb s hs) hxy he', hq⟩

/-- The counting loop rule. `I k` describes the state at the head with counter value `k`. -/
theorem rt_sp_loop {i n : ℕ} {body : rt_Cmd F} (I : ℕ → rt_St F → Prop) (a N cb : ℕ)
    (haN : a ≤ N)
    (hI : ∀ k s, a ≤ k → k ≤ N → I k s → s.nr i = k ∧ s.nr n = N ∧ rt_Bd B s)
    (hbody : ∀ k, a ≤ k → k < N → rt_Sp ns B body (I k)
      (fun s1 => rt_Bd B s1 ∧ rt_Bd B (rt_inc s1 i) ∧ I (k + 1) (rt_inc s1 i)) cb) :
    rt_Sp ns B (.loop i n body) (I a) (I N) ((N - a) * (cb + 4) + 1) := by
  suffices H : ∀ m k, k + m = N → a ≤ k → ∀ s, I k s →
      ∃ n' s', n' ≤ m * (cb + 4) + 1 ∧ rt_Exec ns B (.loop i n body) s n' s' ∧ I N s' by
    intro s hs
    obtain ⟨n', s', h1, h2, h3⟩ := H (N - a) a (by omega) le_rfl s hs
    exact ⟨n', s', h1, h2, h3⟩
  intro m
  induction m with
  | zero =>
    intro k hk hak s hs
    have hk' : k = N := by omega
    subst hk'
    obtain ⟨h1, h2, h3⟩ := hI k s hak le_rfl hs
    exact ⟨1, s, by omega, rt_Exec.loopD h3 (by rw [h1, h2]), hs⟩
  | succ m ih =>
    intro k hk hak s hs
    obtain ⟨h1, h2, h3⟩ := hI k s hak (by omega) hs
    obtain ⟨n1, s1, hn1, he1, hb1, hbi, hI1⟩ := hbody k hak (by omega) s hs
    obtain ⟨n2, s2, hn2, he2, hI2⟩ := ih (k + 1) (by omega) (by omega) _ hI1
    refine ⟨n1 + 4 + n2, s2, ?_, rt_Exec.loopS h3 (by rw [h1, h2]; omega) he1 hb1 hbi he2, hI2⟩
    rw [Nat.succ_mul]; omega

end Hoare

/-! ### Frames -/

def rt_wnI : Instruction F → List ℕ
  | .literal d _ => [d]
  | .inputNat d _ => [d]
  | .addNat d _ _ => [d]
  | .subNat d _ _ => [d]
  | .mulNat d _ _ => [d]
  | .divNat d _ _ => [d]
  | .modNat d _ _ => [d]
  | _ => []

def rt_wfI : Instruction F → List ℕ
  | .constant d _ => [d]
  | .add d _ _ => [d]
  | .sub d _ _ => [d]
  | .mul d _ _ => [d]
  | _ => []

def rt_woI : Instruction F → Bool
  | .output _ => true
  | _ => false

def rt_wn : rt_Cmd F → List ℕ
  | .basic i => rt_wnI i
  | .stR _ _ _ => [60, 61]
  | .ldR _ _ _ => [60, 61]
  | .seq a b => rt_wn a ++ rt_wn b
  | .ifN _ _ t e => rt_wn t ++ rt_wn e
  | .ifF _ _ t e => rt_wn t ++ rt_wn e
  | .loop i _ b => i :: 61 :: rt_wn b

def rt_wf : rt_Cmd F → List ℕ
  | .basic i => rt_wfI i
  | .stR _ _ _ => []
  | .ldR d _ _ => [d]
  | .seq a b => rt_wf a ++ rt_wf b
  | .ifN _ _ t e => rt_wf t ++ rt_wf e
  | .ifF _ _ t e => rt_wf t ++ rt_wf e
  | .loop _ _ b => rt_wf b

def rt_wr : rt_Cmd F → List ℕ
  | .basic _ => []
  | .stR k _ _ => [k % 16]
  | .ldR _ _ _ => []
  | .seq a b => rt_wr a ++ rt_wr b
  | .ifN _ _ t e => rt_wr t ++ rt_wr e
  | .ifF _ _ t e => rt_wr t ++ rt_wr e
  | .loop _ _ b => rt_wr b

def rt_wo : rt_Cmd F → Bool
  | .basic i => rt_woI i
  | .stR _ _ _ => false
  | .ldR _ _ _ => false
  | .seq a b => rt_wo a || rt_wo b
  | .ifN _ _ t e => rt_wo t || rt_wo e
  | .ifF _ _ t e => rt_wo t || rt_wo e
  | .loop _ _ b => rt_wo b

def rt_Agr (c : rt_Cmd F) (s s' : rt_St F) : Prop :=
  (∀ j, j ∉ rt_wn c → s'.nr j = s.nr j) ∧
  (∀ a, a ∉ rt_wf c → a % 16 ∉ rt_wr c → s'.fr a = s.fr a) ∧
  (rt_wo c = false → s'.out = s.out)

theorem rt_agr_of_exec {ns : List ℕ} {B : ℕ} {c : rt_Cmd F} {s s' : rt_St F} {n : ℕ}
    (h : rt_Exec ns B c s n s') : rt_Agr c s s' := by
  induction h with
  | @basic i s hs hb =>
    refine ⟨?_, ?_, ?_⟩
    · intro j hj; cases i <;> simp_all [rt_eff, rt_wn, rt_wnI, rt_setN, rt_setF, rt_simple,
        Function.update_apply]
    · intro a ha _; cases i <;> simp_all [rt_eff, rt_wf, rt_wfI, rt_setN, rt_setF, rt_simple,
        Function.update_apply]
    · intro ho; cases i <;> simp_all [rt_eff, rt_wo, rt_woI, rt_setN, rt_setF, rt_simple]
  | @stR k off src s _ _ _ =>
    refine ⟨?_, ?_, ?_⟩
    · intro j hj; simp only [rt_wn, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      simp [rt_stRes, Function.update_apply, hj.1, hj.2]
    · intro a _ ha; simp only [rt_wr, List.mem_singleton] at ha
      simp only [rt_stRes, Function.update_apply]
      rw [if_neg]; omega
    · intro _; rfl
  | @ldR dst k off s _ _ _ =>
    refine ⟨?_, ?_, ?_⟩
    · intro j hj; simp only [rt_wn, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      simp [rt_ldRes, Function.update_apply, hj.1, hj.2]
    · intro a ha _; simp only [rt_wf, List.mem_singleton] at ha
      simp [rt_ldRes, Function.update_apply, ha]
    · intro _; rfl
  | seq _ _ iha ihb =>
    obtain ⟨a1, a2, a3⟩ := iha; obtain ⟨b1, b2, b3⟩ := ihb
    refine ⟨fun j hj => ?_, fun a ha hr => ?_, fun ho => ?_⟩
    · simp only [rt_wn, List.mem_append, not_or] at hj; rw [b1 j hj.2, a1 j hj.1]
    · simp only [rt_wf, rt_wr, List.mem_append, not_or] at ha hr
      rw [b2 a ha.2 hr.2, a2 a ha.1 hr.1]
    · simp only [rt_wo, Bool.or_eq_false_iff] at ho; rw [b3 ho.2, a3 ho.1]
  | ifNT _ _ _ _ iht =>
    obtain ⟨a1, a2, a3⟩ := iht
    refine ⟨fun j hj => ?_, fun a ha hr => ?_, fun ho => ?_⟩
    · simp only [rt_wn, List.mem_append, not_or] at hj; exact a1 j hj.1
    · simp only [rt_wf, rt_wr, List.mem_append, not_or] at ha hr; exact a2 a ha.1 hr.1
    · simp only [rt_wo, Bool.or_eq_false_iff] at ho; exact a3 ho.1
  | ifNF _ _ _ ihe =>
    obtain ⟨a1, a2, a3⟩ := ihe
    refine ⟨fun j hj => ?_, fun a ha hr => ?_, fun ho => ?_⟩
    · simp only [rt_wn, List.mem_append, not_or] at hj; exact a1 j hj.2
    · simp only [rt_wf, rt_wr, List.mem_append, not_or] at ha hr; exact a2 a ha.2 hr.2
    · simp only [rt_wo, Bool.or_eq_false_iff] at ho; exact a3 ho.2
  | ifFT _ _ _ _ iht =>
    obtain ⟨a1, a2, a3⟩ := iht
    refine ⟨fun j hj => ?_, fun a ha hr => ?_, fun ho => ?_⟩
    · simp only [rt_wn, List.mem_append, not_or] at hj; exact a1 j hj.1
    · simp only [rt_wf, rt_wr, List.mem_append, not_or] at ha hr; exact a2 a ha.1 hr.1
    · simp only [rt_wo, Bool.or_eq_false_iff] at ho; exact a3 ho.1
  | ifFF _ _ _ ihe =>
    obtain ⟨a1, a2, a3⟩ := ihe
    refine ⟨fun j hj => ?_, fun a ha hr => ?_, fun ho => ?_⟩
    · simp only [rt_wn, List.mem_append, not_or] at hj; exact a1 j hj.2
    · simp only [rt_wf, rt_wr, List.mem_append, not_or] at ha hr; exact a2 a ha.2 hr.2
    · simp only [rt_wo, Bool.or_eq_false_iff] at ho; exact a3 ho.2
  | loopD _ _ => exact ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩
  | @loopS i n body s s1 s2 n1 n2 _ _ _ _ _ _ ihb ihl =>
    obtain ⟨a1, a2, a3⟩ := ihb; obtain ⟨b1, b2, b3⟩ := ihl
    refine ⟨fun j hj => ?_, fun a ha hr => ?_, fun ho => ?_⟩
    · have hj' := hj
      simp only [rt_wn, List.mem_cons, not_or] at hj'
      rw [b1 j hj]; simp only [rt_inc, Function.update_apply, hj'.1, hj'.2.1, if_false]
      exact a1 j hj'.2.2
    · rw [b2 a ha hr]; exact a2 a ha hr
    · rw [b3 ho]; exact a3 ho

theorem rt_sp_frame {ns : List ℕ} {B : ℕ} {c : rt_Cmd F} {P Q R : rt_St F → Prop} {N : ℕ}
    (h : rt_Sp ns B c P Q N) (hR : ∀ s s', rt_Agr c s s' → R s → R s') :
    rt_Sp ns B c (fun s => P s ∧ R s) (fun s => Q s ∧ R s) N := by
  intro s ⟨hp, hr⟩
  obtain ⟨n, s', hn, he, hq⟩ := h s hp
  exact ⟨n, s', hn, he, hq, hR s s' (rt_agr_of_exec he) hr⟩

/-! ### Symbolic execution of loop-free code -/

open Classical in
def rt_sym (ns : List ℕ) : rt_Cmd F → rt_St F → rt_St F
  | .basic i, s => rt_eff ns s i
  | .stR k off src, s => rt_stRes s k off src
  | .ldR dst k off, s => rt_ldRes s dst k off
  | .seq a b, s => rt_sym ns b (rt_sym ns a s)
  | .ifN x y t e, s => if s.nr x = s.nr y then rt_sym ns t s else rt_sym ns e s
  | .ifF x y t e, s => if s.fr x = s.fr y then rt_sym ns t s else rt_sym ns e s
  | .loop _ _ _, s => s

open Classical in
def rt_symC (ns : List ℕ) : rt_Cmd F → rt_St F → ℕ
  | .basic _, _ => 1
  | .stR _ _ _, _ => 5
  | .ldR _ _ _, _ => 5
  | .seq a b, s => rt_symC ns a s + rt_symC ns b (rt_sym ns a s)
  | .ifN x y t e, s => if s.nr x = s.nr y then rt_symC ns t s + 2 else rt_symC ns e s + 1
  | .ifF x y t e, s => if s.fr x = s.fr y then rt_symC ns t s + 2 else rt_symC ns e s + 1
  | .loop _ _ _, _ => 0

/-- The natural-number value an instruction writes (0 if none). -/
def rt_wv (ns : List ℕ) (s : rt_St F) : Instruction F → ℕ
  | .literal _ v => v
  | .inputNat _ i => ns.getD i 0
  | .addNat _ a b => s.nr a + s.nr b
  | .subNat _ a b => s.nr a - s.nr b
  | .mulNat _ a b => s.nr a * s.nr b
  | .divNat _ a b => s.nr a / s.nr b
  | .modNat _ a b => s.nr a % s.nr b
  | _ => 0

open Classical in
def rt_symV (ns : List ℕ) (B : ℕ) : rt_Cmd F → rt_St F → Prop
  | .basic i, s => rt_simple i = true ∧ rt_wv ns s i ≤ B
  | .stR k off _, s => off ≠ 61 ∧ s.nr off * 16 + k + 16 ≤ B
  | .ldR _ k off, s => off ≠ 61 ∧ s.nr off * 16 + k + 16 ≤ B
  | .seq a b, s => rt_symV ns B a s ∧ rt_symV ns B b (rt_sym ns a s)
  | .ifN x y t e, s => if s.nr x = s.nr y then rt_symV ns B t s else rt_symV ns B e s
  | .ifF x y t e, s => if s.fr x = s.fr y then rt_symV ns B t s else rt_symV ns B e s
  | .loop _ _ _, _ => False

theorem rt_sym_exec {ns : List ℕ} {B : ℕ} :
    ∀ (c : rt_Cmd F) (s : rt_St F), rt_Bd B s → rt_symV ns B c s →
      rt_Exec ns B c s (rt_symC ns c s) (rt_sym ns c s) ∧ rt_Bd B (rt_sym ns c s)
  | .basic i, s, hb, ⟨hs, hv⟩ => by
    refine ⟨rt_Exec.basic hs hb, ?_⟩
    cases i <;> simp only [rt_sym, rt_eff, rt_wv] at hv ⊢ <;>
      first | exact hb | exact rt_Bd_setN hb hv | (intro j; exact hb j)
  | .stR k off src, s, hb, ⟨ho, hv⟩ => by
    refine ⟨rt_Exec.stR ho hb hv, ?_⟩
    intro j; simp only [rt_sym, rt_stRes, Function.update_apply]
    split_ifs <;> first | omega | exact hb j
  | .ldR dst k off, s, hb, ⟨ho, hv⟩ => by
    refine ⟨rt_Exec.ldR ho hb hv, ?_⟩
    intro j; simp only [rt_sym, rt_ldRes, Function.update_apply]
    split_ifs <;> first | omega | exact hb j
  | .seq a b, s, hb, ⟨ha, hb'⟩ => by
    obtain ⟨e1, b1⟩ := rt_sym_exec a s hb ha
    obtain ⟨e2, b2⟩ := rt_sym_exec b _ b1 hb'
    exact ⟨rt_Exec.seq e1 e2, b2⟩
  | .ifN x y t e, s, hb, h => by
    simp only [rt_symV] at h
    by_cases hxy : s.nr x = s.nr y
    · rw [if_pos hxy] at h
      obtain ⟨e1, b1⟩ := rt_sym_exec t s hb h
      simp only [rt_sym, rt_symC, if_pos hxy]
      exact ⟨rt_Exec.ifNT hb hxy e1 b1, b1⟩
    · rw [if_neg hxy] at h
      obtain ⟨e1, b1⟩ := rt_sym_exec e s hb h
      simp only [rt_sym, rt_symC, if_neg hxy]
      exact ⟨rt_Exec.ifNF hb hxy e1, b1⟩
  | .ifF x y t e, s, hb, h => by
    simp only [rt_symV] at h
    by_cases hxy : s.fr x = s.fr y
    · rw [if_pos hxy] at h
      obtain ⟨e1, b1⟩ := rt_sym_exec t s hb h
      simp only [rt_sym, rt_symC, if_pos hxy]
      exact ⟨rt_Exec.ifFT hb hxy e1 b1, b1⟩
    · rw [if_neg hxy] at h
      obtain ⟨e1, b1⟩ := rt_sym_exec e s hb h
      simp only [rt_sym, rt_symC, if_neg hxy]
      exact ⟨rt_Exec.ifFF hb hxy e1, b1⟩
  | .loop _ _ _, _, _, h => h.elim

theorem rt_symC_le (ns : List ℕ) : ∀ (c : rt_Cmd F) (s : rt_St F), rt_symC ns c s ≤ rt_len c
  | .basic _, _ => le_rfl
  | .stR _ _ _, _ => le_rfl
  | .ldR _ _ _, _ => le_rfl
  | .seq a b, s => by
    have := rt_symC_le ns a s; have := rt_symC_le ns b (rt_sym ns a s)
    simp only [rt_symC, rt_len]; omega
  | .ifN x y t e, s => by
    have := rt_symC_le ns t s; have := rt_symC_le ns e s
    simp only [rt_symC, rt_len]; split_ifs <;> omega
  | .ifF x y t e, s => by
    have := rt_symC_le ns t s; have := rt_symC_le ns e s
    simp only [rt_symC, rt_len]; split_ifs <;> omega
  | .loop _ _ _, _ => Nat.zero_le _

theorem rt_sp_sym {ns : List ℕ} {B : ℕ} {c : rt_Cmd F} {P Q : rt_St F → Prop}
    (h : ∀ s, P s → rt_Bd B s ∧ rt_symV ns B c s ∧ (rt_Bd B (rt_sym ns c s) → Q (rt_sym ns c s))) :
    rt_Sp ns B c P Q (rt_len c) := by
  intro s hs
  obtain ⟨hb, hv, hq⟩ := h s hs
  obtain ⟨e, b⟩ := rt_sym_exec c s hb hv
  exact ⟨_, _, rt_symC_le ns c s, e, hq b⟩

theorem rt_sp_sym' {ns : List ℕ} {B : ℕ} {c : rt_Cmd F} {P Q : rt_St F → Prop}
    (h : ∀ s, P s → rt_Bd B s ∧ rt_symV ns B c s ∧
      (rt_Bd B (rt_sym ns c s) → rt_Agr c s (rt_sym ns c s) → Q (rt_sym ns c s))) :
    rt_Sp ns B c P Q (rt_len c) := by
  intro s hs
  obtain ⟨hb, hv, hq⟩ := h s hs
  obtain ⟨e, b⟩ := rt_sym_exec c s hb hv
  exact ⟨_, _, rt_symC_le ns c s, e, hq b (rt_agr_of_exec e)⟩

end SubspaceEvasion312.Explicit.Dev.LG
end
end

section
set_option autoImplicit false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.LG
open SubspaceEvasion312.Explicit
open Classical

/-! ## Index-level description of the greedy algorithm

Field elements are indexed by their position in `al`; vectors by base-`q` digits, most
significant first; `rt_dg q n p` is the digit of `n` at position `p` from the least
significant end. -/

def rt_dg (q n p : ℕ) : ℕ := n / q ^ p % q

section Defs
variable {F : Type} [Field F]

def rt_ix (al : List F) (v : F) : ℕ := al.idxOf v

/-- Coordinate `k'` (counted from the least significant end) of the point with basis index `β`
and coefficient index `c`. -/
def rt_pv (al : List F) (s b r β c k' : ℕ) : F :=
  ∑ i ∈ Finset.range r, al.getD (rt_dg al.length c i) 0 *
    al.getD (rt_dg al.length β (i * (s + b) + k')) 0

def rt_pidx (al : List F) (s b r β c : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (s + b), rt_ix al (rt_pv al s b r β c k) * al.length ^ k

def rt_xi (al : List F) (s b r β c : ℕ) : ℕ := rt_pidx al s b r β c / al.length ^ b
def rt_yi (al : List F) (s b r β c : ℕ) : ℕ := rt_pidx al s b r β c % al.length ^ b

/-- Coefficient digit `j` (base `q^r`, least significant first) of the coefficient tuple `t`. -/
def rt_ci (q r t j : ℕ) : ℕ := t / (q ^ r) ^ j % q ^ r

/-- `x`-index of point `j` of event number `ev = β * Q2 + t`. -/
def rt_ex (al : List F) (s b r d ev j : ℕ) : ℕ :=
  rt_xi al s b r (ev / (al.length ^ r) ^ d) (rt_ci al.length r (ev % (al.length ^ r) ^ d) j)

/-- Among the first `jl` points of event `ev`, two share their `x`-index. -/
def rt_dupP (al : List F) (s b r d ev jl : ℕ) : Prop :=
  ∃ j1 j2, j1 < j2 ∧ j2 < jl ∧ rt_ex al s b r d ev j1 = rt_ex al s b r d ev j2

def rt_vec (al : List F) (n i : ℕ) : Vec F n :=
  fun k => al.getD (rt_dg al.length i (n - 1 - k)) 0

def rt_vidx (al : List F) (n : ℕ) (v : Vec F n) : ℕ :=
  ∑ k : Fin n, rt_ix al (v k) * al.length ^ (n - 1 - k)

variable [Fintype F]

/-- The index of the value chosen at the `k`-th input vector. -/
def rt_sel (al : List F) (s b r d k : ℕ) : ℕ :=
  rt_vidx al b (localFunction al s b r d (rt_vec al s k))

/-- Status of the point `(β, c)` while input number `k` is processed. -/
def rt_bad (al : List F) (s b r d k β c : ℕ) : Prop :=
  rt_xi al s b r β c < k ∧ rt_yi al s b r β c ≠ rt_sel al s b r d (rt_xi al s b r β c)

def rt_okp (al : List F) (s b r d k w β c : ℕ) : Prop :=
  ¬ rt_bad al s b r d k β c ∧ (rt_xi al s b r β c = k → rt_yi al s b r β c = w)

def rt_nfree (al : List F) (s b r d k β t : ℕ) : ℕ :=
  ((Finset.range d).filter (fun j => k < rt_xi al s b r β (rt_ci al.length r t j))).card

def rt_term (al : List F) (s b r d k w β t : ℕ) : ℕ :=
  if rt_dupP al s b r d (β * (al.length ^ r) ^ d + t) d then 0
  else if ∀ j < d, rt_okp al s b r d k w β (rt_ci al.length r t j) then
    (al.length ^ b) ^ (d - rt_nfree al s b r d k β t)
  else 0

/-- The scaled conditional score of assigning value index `w` to input index `k`. -/
def rt_Sc (al : List F) (s b r d k w : ℕ) : ℕ :=
  ∑ β ∈ Finset.range ((al.length ^ (s + b)) ^ r),
    ∑ t ∈ Finset.range ((al.length ^ r) ^ d), rt_term al s b r d k w β t

def rt_z0 (al : List F) (b : ℕ) : ℕ := rt_vidx al b 0

def rt_chooseStep (al : List F) (s b r d k : ℕ) (bi w : ℕ) : ℕ :=
  if rt_Sc al s b r d k w < rt_Sc al s b r d k bi then w else bi

def rt_choose (al : List F) (s b r d k : ℕ) : ℕ :=
  (List.range (al.length ^ b)).foldl (rt_chooseStep al s b r d k) (rt_z0 al b)

/-- The output data, digit by digit. -/
def rt_outData (al : List F) (s b r d : ℕ) : ℕ → List F
  | 0 => []
  | k + 1 => rt_outData al s b r d k ++
      (List.range b).map (fun j => al.getD (rt_dg al.length (rt_sel al s b r d k) (b - 1 - j)) 0)

end Defs

/-! ## The mathematical correctness statements -/

section Math
variable {F : Type} [Field F] [Fintype F]

theorem rt_digsum_lt (q n : ℕ) (f : ℕ → ℕ) (hq : 1 ≤ q) (hf : ∀ k < n, f k < q) :
    ∑ k ∈ Finset.range n, f k * q ^ k < q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := ih (fun k hk => hf k (by omega))
    have h2 : f n * q ^ n ≤ (q - 1) * q ^ n := Nat.mul_le_mul_right _ (by have := hf n (by omega); omega)
    have h3 : (q - 1) * q ^ n + q ^ n = q ^ n * q := by
      rw [mul_comm (q ^ n) q]; zify [hq]; ring
    omega

theorem rt_ix_lt {al : List F} (hall : ∀ a : F, a ∈ al) (v : F) : rt_ix al v < al.length := by
  unfold rt_ix; exact List.idxOf_lt_length_iff.mpr (hall v)

theorem rt_getD_eq_iff {al : List F} (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al) (v : F) (e : ℕ)
    (he : e < al.length) : al.getD e 0 = v ↔ e = rt_ix al v := by
  rw [List.getD_eq_getElem _ _ he]
  constructor
  · rintro rfl; unfold rt_ix; exact (List.Nodup.idxOf_getElem hnd e he).symm
  · rintro rfl; unfold rt_ix; exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (hall v))

theorem rt_len_pos {al : List F} (hall : ∀ a : F, a ∈ al) : 0 < al.length :=
  List.length_pos_of_mem (hall 0)

/-- Digits of a digit sum. -/
theorem rt_digsum_digit (q n : ℕ) (f : ℕ → ℕ) (hq : 1 ≤ q) (hf : ∀ k < n, f k < q) (p : ℕ)
    (hp : p < n) : (∑ k ∈ Finset.range n, f k * q ^ k) / q ^ p % q = f p := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with h | h
    · -- the top term contributes a multiple of q^(p+1)
      have hlow := rt_digsum_lt q n f hq (fun k hk => hf k (by omega))
      have e : f n * q ^ n = (f n * q ^ (n - p - 1) * q) * q ^ p := by
        rw [mul_assoc, mul_assoc, ← pow_succ', ← pow_add]; congr 2; omega
      rw [e, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mod, Nat.mul_mod_left, add_zero,
        Nat.mod_mod, ih (fun k hk => hf k (by omega)) h]
    · subst h
      have hlow := rt_digsum_lt q p f hq (fun k hk => hf k (by omega))
      have key : ((∑ k ∈ Finset.range p, f k * q ^ k) + f p * q ^ p) / q ^ p % q = f p := by
        rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlow, zero_add,
          Nat.mod_eq_of_lt (hf p (by omega))]
      simpa [Nat.add_comm] using key

theorem rt_dg_div (q n a p : ℕ) : rt_dg q (n / q ^ a) p = rt_dg q n (a + p) := by
  unfold rt_dg; rw [Nat.div_div_eq_div_mul, ← pow_add]

theorem rt_dg_mod (q n a p : ℕ) (hq : 1 ≤ q) (hp : p < a) : rt_dg q (n % q ^ a) p = rt_dg q n p := by
  unfold rt_dg
  have e : q ^ a = q ^ p * (q ^ (a - p - 1) * q) := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mul_left_mod]

/-- A digit of a base-`q^m` digit. -/
theorem rt_dg_dg (q n m a p : ℕ) (hq : 1 ≤ q) (hp : p < m) :
    rt_dg q (n / (q ^ m) ^ a % q ^ m) p = rt_dg q n (a * m + p) := by
  rw [rt_dg_mod q _ m p hq hp, ← pow_mul, rt_dg_div, mul_comm m a]

def rt_vdig (al : List F) (n : ℕ) (v : Vec F n) (k : ℕ) : ℕ :=
  if h : k < n then rt_ix al (v ⟨n - 1 - k, by omega⟩) else 0

theorem rt_vidx_eq (al : List F) (n : ℕ) (v : Vec F n) :
    rt_vidx al n v = ∑ k ∈ Finset.range n, rt_vdig al n v k * al.length ^ k := by
  unfold rt_vidx
  let G : ℕ → ℕ := fun k => (if h : k < n then rt_ix al (v ⟨k, h⟩) else 0) * al.length ^ (n - 1 - k)
  calc ∑ k : Fin n, rt_ix al (v k) * al.length ^ (n - 1 - (k : ℕ))
      = ∑ k : Fin n, G k := by
        apply Finset.sum_congr rfl; intro k _; simp [G, k.isLt]
    _ = ∑ k ∈ Finset.range n, G k := Fin.sum_univ_eq_sum_range G n
    _ = ∑ k ∈ Finset.range n, G (n - 1 - k) := (Finset.sum_range_reflect G n).symm
    _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_range] at hk
        simp only [G, rt_vdig, dif_pos hk, dif_pos (show n - 1 - k < n by omega)]
        congr 2; omega

theorem rt_vidx_lt (al : List F) (hall : ∀ a : F, a ∈ al) (n : ℕ) (v : Vec F n) :
    rt_vidx al n v < al.length ^ n := by
  rw [rt_vidx_eq]
  apply rt_digsum_lt _ _ _ (rt_len_pos hall)
  intro k hk
  simp only [rt_vdig, dif_pos hk]; exact rt_ix_lt hall _

theorem rt_vec_vidx (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al) (n : ℕ)
    (v : Vec F n) : rt_vec al n (rt_vidx al n v) = v := by
  funext k
  unfold rt_vec
  rw [rt_vidx_eq, rt_dg, rt_digsum_digit _ _ _ (rt_len_pos hall)
    (fun k hk => by simp only [rt_vdig, dif_pos hk]; exact rt_ix_lt hall _) _ (by omega)]
  simp only [rt_vdig, dif_pos (show n - 1 - k < n by omega)]
  have : (⟨n - 1 - (n - 1 - k), by omega⟩ : Fin n) = k := by ext; simp; omega
  rw [this]
  exact (rt_getD_eq_iff hnd hall _ _ (rt_ix_lt hall _)).mpr rfl

theorem rt_vidx_vec (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al) (n i : ℕ)
    (hi : i < al.length ^ n) : rt_vidx al n (rt_vec al n i) = i := by
  rw [rt_vidx_eq]
  have hq := rt_len_pos hall
  have h1 : ∀ k < n, rt_vdig al n (rt_vec al n i) k = rt_dg al.length i k := by
    intro k hk
    simp only [rt_vdig, dif_pos hk, rt_vec]
    rw [show n - 1 - (n - 1 - k) = k by omega]
    exact ((rt_getD_eq_iff hnd hall _ _ (Nat.mod_lt _ hq)).mp rfl).symm
  rw [Finset.sum_congr rfl (fun k hk => by rw [h1 k (Finset.mem_range.mp hk)])]
  -- base-q expansion
  clear h1
  induction n generalizing i with
  | zero => simp at hi; simp [hi]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have hi' : i / al.length < al.length ^ n := by
      rw [Nat.div_lt_iff_lt_mul hq, ← pow_succ]; exact hi
    have e : ∀ k, rt_dg al.length i (k + 1) = rt_dg al.length (i / al.length) k := by
      intro k; unfold rt_dg; rw [Nat.div_div_eq_div_mul, ← pow_succ']
    simp only [e, pow_succ, ← mul_assoc, ← Finset.sum_mul]
    rw [ih _ hi', rt_dg, pow_zero, Nat.div_one, mul_one]
    exact Nat.div_add_mod' i al.length

theorem rt_vec_inj (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al) (n i j : ℕ)
    (hi : i < al.length ^ n) (hj : j < al.length ^ n) (h : rt_vec al n i = rt_vec al n j) :
    i = j := by
  rw [← rt_vidx_vec al hnd hall n i hi, h, rt_vidx_vec al hnd hall n j hj]

theorem rt_pidx_lt (al : List F) (hall : ∀ a : F, a ∈ al) (s b r β c : ℕ) :
    rt_pidx al s b r β c < al.length ^ (s + b) :=
  rt_digsum_lt _ _ _ (rt_len_pos hall) (fun k _ => rt_ix_lt hall _)

theorem rt_xi_lt (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al)
    (s b r β c : ℕ) : rt_xi al s b r β c < al.length ^ s := by
  unfold rt_xi
  rw [Nat.div_lt_iff_lt_mul (by have := rt_len_pos hall; positivity), ← pow_add]
  exact rt_pidx_lt al hall s b r β c

theorem rt_yi_lt (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al)
    (s b r β c : ℕ) : rt_yi al s b r β c < al.length ^ b :=
  Nat.mod_lt _ (by have := rt_len_pos hall; positivity)

theorem rt_z0_lt (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al) (b : ℕ) :
    rt_z0 al b < al.length ^ b := rt_vidx_lt al hall b 0

theorem rt_sel_lt (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al)
    (s b r d k : ℕ) : rt_sel al s b r d k < al.length ^ b := rt_vidx_lt al hall b _

theorem rt_divmod {Q k x : ℕ} (hx : x < Q) : (k * Q + x) / Q = k ∧ (k * Q + x) % Q = x := by
  have hQ : 0 < Q := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt hx, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

/-! ### Enumerations -/

theorem rt_list_sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem rt_range_flatMap {X : Type} (m L : ℕ) (g : ℕ → ℕ → X) :
    (List.range m).flatMap (fun a => (List.range L).map (g a)) =
      (List.range (m * L)).map (fun i => g (i / L) (i % L)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add, List.map_append]
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    have := rt_divmod (k := m) hj
    simp [Function.comp, this.1, this.2]

theorem rt_list_eq_map_range {X : Type} (xs : List X) (x0 : X) :
    xs = (List.range xs.length).map (fun i => xs.getD i x0) := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp [List.getElem?_eq_getElem h1]

theorem rt_flatMap_range {X Y : Type} (l : List X) (x0 : X) (g : X → List Y) :
    l.flatMap g = (List.range l.length).flatMap (fun a => g (l.getD a x0)) := by
  conv_lhs => rw [rt_list_eq_map_range l x0]
  rw [List.flatMap_map]

theorem rt_allTuples_eq {X : Type} (xs : List X) (x0 : X) (n : ℕ) :
    allTuples xs n = (List.range (xs.length ^ n)).map
      (fun i => fun k : Fin n => xs.getD (i / xs.length ^ (n - 1 - k) % xs.length) x0) := by
  induction n with
  | zero =>
    simp only [allTuples, pow_zero, List.range_one, List.map_cons, List.map_nil]
    congr 1; funext k; exact k.elim0
  | succ n ih =>
    simp only [allTuples]
    rw [rt_flatMap_range xs x0, ih]
    simp only [List.map_map]
    rw [show (fun a => List.map (Fin.cons (xs.getD a x0) ∘ fun i => fun k : Fin n =>
      xs.getD (i / xs.length ^ (n - 1 - ↑k) % xs.length) x0) (List.range (xs.length ^ n))) =
      (fun a => (List.range (xs.length ^ n)).map (fun j => (Fin.cons (xs.getD a x0)
        (fun k : Fin n => xs.getD (j / xs.length ^ (n - 1 - ↑k) % xs.length) x0) :
        Fin (n + 1) → X))) from rfl]
    rw [rt_range_flatMap, ← pow_succ']
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    have hq : 0 < xs.length := by
      rcases Nat.eq_zero_or_pos xs.length with h | h
      · rw [h] at hi; simp at hi
      · exact h
    funext k
    refine Fin.cases ?_ (fun k' => ?_) k
    · simp only [Fin.cons_zero, Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel]
      congr 1
      rw [Nat.mod_eq_of_lt]
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_succ']; exact hi
    · simp only [Fin.cons_succ, Fin.val_succ]
      congr 1
      have := rt_dg_mod xs.length i n (n - 1 - k') hq (by omega)
      unfold rt_dg at this
      rw [this, show n + 1 - 1 - (↑k' + 1) = n - 1 - ↑k' by omega]

theorem rt_allVectors_eq_tuples (al : List F) (n : ℕ) : allVectors al n = allTuples al n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [allVectors, allTuples, ih]

theorem rt_allVectors_eq (al : List F) (n : ℕ) :
    allVectors al n = (List.range (al.length ^ n)).map (rt_vec al n) := by
  rw [rt_allVectors_eq_tuples, rt_allTuples_eq al 0]
  rfl

theorem rt_pairs_eq (al : List F) (s b : ℕ) :
    ((allVectors al s).flatMap fun x => (allVectors al b).map fun y => (x, y)) =
      (List.range (al.length ^ (s + b))).map
        (fun p => (rt_vec al s (p / al.length ^ b), rt_vec al b (p % al.length ^ b))) := by
  rw [rt_allVectors_eq, rt_allVectors_eq, List.flatMap_map]
  simp only [List.map_map]
  rw [show (fun a => List.map ((fun y => (rt_vec al s a, y)) ∘ rt_vec al b)
      (List.range (al.length ^ b))) = (fun a => (List.range (al.length ^ b)).map
      (fun j => (rt_vec al s a, rt_vec al b j))) from rfl]
  rw [rt_range_flatMap, pow_add]

/-! ### Events and points -/

def rt_basisOf (al : List F) (s b r β : ℕ) : Fin r → Vec F s × Vec F b := fun i =>
  (rt_vec al s (β / (al.length ^ (s + b)) ^ (r - 1 - i) % al.length ^ (s + b) / al.length ^ b),
   rt_vec al b (β / (al.length ^ (s + b)) ^ (r - 1 - i) % al.length ^ (s + b) % al.length ^ b))

def rt_coeffOf (al : List F) (r d t : ℕ) : Fin d → Vec F r := fun j =>
  rt_vec al r (rt_ci al.length r t (d - 1 - j))

theorem rt_bases_eq (al : List F) (hall : ∀ a : F, a ∈ al) (s b r : ℕ) :
    allTuples ((allVectors al s).flatMap fun x => (allVectors al b).map fun y => (x, y)) r =
      (List.range ((al.length ^ (s + b)) ^ r)).map (rt_basisOf al s b r) := by
  have hq := rt_len_pos hall
  rw [rt_allTuples_eq _ (0, 0), rt_pairs_eq]
  simp only [List.length_map, List.length_range]
  apply List.map_congr_left
  intro β _
  funext k
  have hlt : β / (al.length ^ (s + b)) ^ (r - 1 - ↑k) % al.length ^ (s + b) < al.length ^ (s + b) :=
    Nat.mod_lt _ (by positivity)
  rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
  simp [rt_basisOf]

theorem rt_coeffs_eq (al : List F) (hall : ∀ a : F, a ∈ al) (r d : ℕ) :
    allTuples (allVectors al r) d =
      (List.range ((al.length ^ r) ^ d)).map (rt_coeffOf al r d) := by
  have hq := rt_len_pos hall
  rw [rt_allTuples_eq _ 0]
  conv_lhs => rw [rt_allVectors_eq al r]
  simp only [List.length_map, List.length_range]
  apply List.map_congr_left
  intro t _
  funext j
  have hlt : t / (al.length ^ r) ^ (d - 1 - ↑j) % al.length ^ r < al.length ^ r :=
    Nat.mod_lt _ (by positivity)
  rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
  simp [rt_coeffOf, rt_ci]

theorem rt_pidx_coord (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al) (s b r β c k' : ℕ)
    (hk : k' < s + b) :
    al.getD (rt_dg al.length (rt_pidx al s b r β c) k') 0 = rt_pv al s b r β c k' := by
  unfold rt_pidx
  rw [rt_dg, rt_digsum_digit _ _ _ (rt_len_pos hall) (fun k _ => rt_ix_lt hall _) _ hk]
  exact (rt_getD_eq_iff hnd hall _ _ (rt_ix_lt hall _)).mpr rfl

theorem rt_sum_coord (al : List F) (s b r β c k' : ℕ) :
    ∑ i : Fin r, al.getD (rt_dg al.length c (r - 1 - i)) 0 *
      al.getD (rt_dg al.length β ((r - 1 - i) * (s + b) + k')) 0 = rt_pv al s b r β c k' := by
  unfold rt_pv
  rw [Fin.sum_univ_eq_sum_range (fun i => al.getD (rt_dg al.length c (r - 1 - i)) 0 *
      al.getD (rt_dg al.length β ((r - 1 - i) * (s + b) + k')) 0) r,
    ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [show r - 1 - (r - 1 - i) = i by omega]

theorem rt_point_eq (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al) (s b r β c : ℕ) :
    ∑ i : Fin r, rt_vec al r c i • rt_basisOf al s b r β i =
      (rt_vec al s (rt_xi al s b r β c), rt_vec al b (rt_yi al s b r β c)) := by
  have hq := rt_len_pos hall
  ext k
  · simp only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    simp only [rt_basisOf, rt_vec]
    rw [rt_xi, rt_dg_div, rt_pidx_coord al hnd hall _ _ _ _ _ _ (by omega)]
    rw [← rt_sum_coord]
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    rw [rt_dg_div, rt_dg_dg _ _ _ _ _ hq (by omega)]
  · simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    simp only [rt_basisOf, rt_vec]
    rw [rt_yi, rt_dg_mod _ _ _ _ hq (by omega), rt_pidx_coord al hnd hall _ _ _ _ _ _ (by omega)]
    rw [← rt_sum_coord]
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    rw [rt_dg_mod _ _ _ _ hq (by omega), rt_dg_dg _ _ _ _ _ hq (by omega)]

theorem rt_eventPoints_eq (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al)
    (s b r d β t : ℕ) :
    eventPoints (rt_basisOf al s b r β) (rt_coeffOf al r d t) =
      List.ofFn (fun j : Fin d =>
        (rt_vec al s (rt_xi al s b r β (rt_ci al.length r t (d - 1 - j))),
         rt_vec al b (rt_yi al s b r β (rt_ci al.length r t (d - 1 - j))))) := by
  unfold eventPoints
  congr 1
  funext j
  exact rt_point_eq al hnd hall s b r β _

/-! ### The score of an event -/

theorem rt_card (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al) :
    Fintype.card F = al.length := by
  rw [← List.toFinset_card_of_nodup hnd, ← Finset.card_univ]
  congr 1; ext a; simp [hall a]

/-- The assignment after `k` inputs plus a tentative value `w` for input `k`. -/
def rt_Apre (al : List F) (s b r d k : ℕ) : List (Vec F s × Vec F b) :=
  (List.range k).map (fun i => (rt_vec al s i, rt_vec al b (rt_sel al s b r d i)))

theorem rt_ofFn_rev {X : Type} (d : ℕ) (Z : ℕ → X) :
    List.ofFn (fun j : Fin d => Z (d - 1 - j)) = ((List.range d).map Z).reverse := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_ofFn, List.getElem_reverse, List.getElem_map, List.getElem_range,
    List.length_map, List.length_range]

theorem rt_consistent_iff (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al)
    (s b r d k w x y : ℕ) (hk : k < al.length ^ s) (hw : w < al.length ^ b)
    (hx : x < al.length ^ s) (hy : y < al.length ^ b) :
    (∀ a ∈ rt_Apre al s b r d k ++ [(rt_vec al s k, rt_vec al b w)],
      rt_vec al s x = a.1 → rt_vec al b y = a.2) ↔
      ((x < k → y = rt_sel al s b r d x) ∧ (x = k → y = w)) := by
  have injs := rt_vec_inj al hnd hall s
  have injb := rt_vec_inj al hnd hall b
  constructor
  · intro h
    refine ⟨fun hxk => ?_, fun hxk => ?_⟩
    · have := h (rt_vec al s x, rt_vec al b (rt_sel al s b r d x))
        (List.mem_append_left _ (List.mem_map.mpr ⟨x, List.mem_range.mpr hxk, rfl⟩)) rfl
      exact injb _ _ hy (rt_sel_lt al hnd hall s b r d x) this
    · subst hxk
      have := h (rt_vec al s x, rt_vec al b w) (List.mem_append_right _ (List.mem_singleton_self _)) rfl
      exact injb _ _ hy hw this
  · rintro ⟨h1, h2⟩ a ha hxa
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      simp only [List.mem_range] at hi
      have hxi := injs _ _ hx (by omega) hxa
      subst hxi
      rw [h1 hi]
    · rw [List.mem_singleton] at ha; subst ha
      have hxi := injs _ _ hx hk hxa
      rw [h2 hxi]

theorem rt_assigned_iff (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al)
    (s b r d k w x : ℕ) (hk : k < al.length ^ s) (hx : x < al.length ^ s) :
    ((rt_Apre al s b r d k ++ [(rt_vec al s k, rt_vec al b w)]).any
      (fun a => decide (a.1 = rt_vec al s x))) = true ↔ x ≤ k := by
  have injs := rt_vec_inj al hnd hall s
  simp only [List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, hax⟩
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      simp only [List.mem_range] at hi
      have := injs _ _ (by omega) hx hax; omega
    · rw [List.mem_singleton] at ha; subst ha
      have := injs _ _ hk hx hax; omega
  · intro hxk
    rcases Nat.lt_or_eq_of_le hxk with h | h
    · exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨x, List.mem_range.mpr h, rfl⟩), rfl⟩
    · subst h; exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩

theorem rt_eventProb_eq (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al)
    (s b r d k w β t : ℕ) (hk : k < al.length ^ s) (hw : w < al.length ^ b)
    (ht : t < (al.length ^ r) ^ d) :
    eventProbability (rt_Apre al s b r d k ++ [(rt_vec al s k, rt_vec al b w)])
      (eventPoints (rt_basisOf al s b r β) (rt_coeffOf al r d t)) *
      (al.length : ℚ) ^ (b * d) = (rt_term al s b r d k w β t : ℚ) := by
  have hq := rt_len_pos hall
  set X : ℕ → ℕ := fun j => rt_xi al s b r β (rt_ci al.length r t j) with hX
  set Y : ℕ → ℕ := fun j => rt_yi al s b r β (rt_ci al.length r t j) with hY
  have hXl : ∀ j, X j < al.length ^ s := fun j => rt_xi_lt al hnd hall _ _ _ _ _
  have hYl : ∀ j, Y j < al.length ^ b := fun j => rt_yi_lt al hnd hall _ _ _ _ _
  rw [rt_eventPoints_eq al hnd hall,
    rt_ofFn_rev d (fun j => (rt_vec al s (X j), rt_vec al b (Y j)))]
  set A := rt_Apre al s b r d k ++ [(rt_vec al s k, rt_vec al b w)] with hA
  set L := (List.range d).map (fun j => (rt_vec al s (X j), rt_vec al b (Y j))) with hL
  -- nodup
  have hnodup : (L.reverse.map Prod.fst).Nodup ↔
      ¬ rt_dupP al s b r d (β * (al.length ^ r) ^ d + t) d := by
    rw [List.map_reverse, List.nodup_reverse, hL, List.map_map,
      List.nodup_map_iff_inj_on List.nodup_range]
    have hex : ∀ j, rt_ex al s b r d (β * (al.length ^ r) ^ d + t) j = X j := by
      intro j
      obtain ⟨e1, e2⟩ := rt_divmod (k := β) ht
      simp only [rt_ex, e1, e2, hX]
    unfold rt_dupP
    simp only [hex, Function.comp, List.mem_range]
    constructor
    · rintro h ⟨j1, j2, h1, h2, h3⟩
      have := h j1 (by omega) j2 h2 (congrArg (rt_vec al s) h3)
      omega
    · intro h x hx y hy hxy
      have hxy' := rt_vec_inj al hnd hall s _ _ (hXl x) (hXl y) hxy
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · exact h ⟨x, y, h', hy, hxy'⟩
      · exact h ⟨y, x, h', hx, hxy'.symm⟩
  -- consistency
  have hcons : (∀ z ∈ L.reverse, ∀ a ∈ A, z.1 = a.1 → z.2 = a.2) ↔
      ∀ j < d, rt_okp al s b r d k w β (rt_ci al.length r t j) := by
    simp only [List.mem_reverse, hL, List.mem_map, List.mem_range]
    constructor
    · intro h j hj
      have := (rt_consistent_iff al hnd hall s b r d k w (X j) (Y j) hk hw (hXl j) (hYl j)).mp
        (fun a ha hxa => h _ ⟨j, hj, rfl⟩ a ha hxa)
      refine ⟨fun hbad => hbad.2 (this.1 hbad.1), this.2⟩
    · rintro h z ⟨j, hj, rfl⟩
      have hok := h j hj
      refine (rt_consistent_iff al hnd hall s b r d k w (X j) (Y j) hk hw (hXl j) (hYl j)).mpr
        ⟨fun hxk => ?_, hok.2⟩
      by_contra hne
      exact hok.1 ⟨hxk, hne⟩
  -- unassigned count
  have hcount : (L.reverse.filter (fun z => !(A.any (fun a => decide (a.1 = z.1))))).length =
      rt_nfree al s b r d k β t := by
    rw [List.filter_reverse, List.length_reverse, hL, List.filter_map, List.length_map]
    unfold rt_nfree
    have : ∀ j ∈ List.range d, ((fun z : Vec F s × Vec F b => !(A.any (fun a => decide (a.1 = z.1))))
        ∘ (fun j => (rt_vec al s (X j), rt_vec al b (Y j)))) j = decide (k < X j) := by
      intro j _
      simp only [Function.comp]
      have := rt_assigned_iff al hnd hall s b r d k w (X j) hk (hXl j)
      rw [← hA] at this
      by_cases h : X j ≤ k
      · rw [this.mpr h]; simp; omega
      · have h' : (A.any fun a => decide (a.1 = rt_vec al s (X j))) = false := by
          by_contra hc; simp only [Bool.not_eq_false] at hc; exact h (this.mp hc)
        rw [h']; simp; omega
    rw [List.filter_congr this]
    simp [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, hX]
  -- assemble
  have hnf : rt_nfree al s b r d k β t ≤ d := by
    unfold rt_nfree; exact le_trans (Finset.card_filter_le _ _) (by simp)
  unfold eventProbability rt_term
  rw [rt_card al hnd hall]
  by_cases hd : rt_dupP al s b r d (β * (al.length ^ r) ^ d + t) d
  · rw [if_neg (fun h => (hnodup.mp h.1) hd), if_pos hd]; simp
  · rw [if_neg hd]
    by_cases hc : ∀ j < d, rt_okp al s b r d k w β (rt_ci al.length r t j)
    · rw [if_pos ⟨hnodup.mpr hd, hcons.mpr hc⟩, if_pos hc, hcount]
      have hq' : (al.length : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
      push_cast
      rw [← pow_mul, show b * d = b * rt_nfree al s b r d k β t +
        b * (d - rt_nfree al s b r d k β t) by rw [← Nat.mul_add]; congr 1; omega, pow_add]
      field_simp
    · rw [if_neg (fun h => hc (hcons.mp h.2)), if_neg hc]; simp

theorem rt_score_eq (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al)
    (s b r d k w : ℕ) (hk : k < al.length ^ s) (hw : w < al.length ^ b) :
    conditionalScore al r d (rt_Apre al s b r d k ++ [(rt_vec al s k, rt_vec al b w)]) *
      (al.length : ℚ) ^ (b * d) = (rt_Sc al s b r d k w : ℚ) := by
  unfold conditionalScore
  simp only
  rw [rt_bases_eq al hall, rt_coeffs_eq al hall, List.map_map, rt_list_sum_range, Finset.sum_mul]
  unfold rt_Sc
  push_cast
  apply Finset.sum_congr rfl
  intro β _
  simp only [Function.comp]
  rw [List.map_map, rt_list_sum_range, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Function.comp, Finset.mem_range] at ht ⊢
  exact rt_eventProb_eq al hnd hall s b r d k w β t hk hw ht

/-! ### The greedy table -/

def rt_g (al : List F) (s b r d : ℕ) (A : List (Vec F s × Vec F b)) (i : ℕ) :
    List (Vec F s × Vec F b) :=
  A ++ [(rt_vec al s i, chooseValue al r d A (rt_vec al s i))]

def rt_PF (al : List F) (s b r d k : ℕ) : List (Vec F s × Vec F b) :=
  (List.range k).foldl (rt_g al s b r d) []

theorem rt_localTable_eq (al : List F) (s b r d : ℕ) :
    localTable al s b r d = rt_PF al s b r d (al.length ^ s) := by
  unfold localTable rt_PF
  rw [rt_allVectors_eq, List.foldl_map]
  rfl

theorem rt_PF_succ (al : List F) (s b r d k : ℕ) :
    rt_PF al s b r d (k + 1) = rt_PF al s b r d k ++
      [(rt_vec al s k, chooseValue al r d (rt_PF al s b r d k) (rt_vec al s k))] := by
  unfold rt_PF
  rw [List.range_succ, List.foldl_append]
  rfl

theorem rt_PF_eq (al : List F) (s b r d : ℕ) : ∀ k, rt_PF al s b r d k =
    (List.range k).map (fun i => (rt_vec al s i, chooseValue al r d (rt_PF al s b r d i)
      (rt_vec al s i))) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [rt_PF_succ, List.range_succ, List.map_append, ← ih]; rfl

theorem rt_find_range (q : ℕ → Bool) (n k : ℕ) (hk : k < n) (hq : q k = true)
    (hlt : ∀ i < k, q i = false) : (List.range n).find? q = some k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.find?_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · rw [ih h]; rfl
    · subst h
      rw [List.find?_eq_none.mpr (fun i hi => by
        simp only [List.mem_range] at hi; rw [hlt i hi]; simp)]
      simp [hq]

theorem rt_localFunction_eq (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al)
    (s b r d k : ℕ) (hk : k < al.length ^ s) :
    localFunction al s b r d (rt_vec al s k) =
      chooseValue al r d (rt_PF al s b r d k) (rt_vec al s k) := by
  unfold localFunction
  rw [rt_localTable_eq, rt_PF_eq, List.find?_map]
  rw [rt_find_range _ (al.length ^ s) k hk (by simp) (fun i hi => by
    simp only [Function.comp, decide_eq_false_iff_not]
    intro h
    have := rt_vec_inj al hnd hall s _ _ (by omega) hk h
    omega)]
  rfl

theorem rt_PF_eq_Apre (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al)
    (s b r d k : ℕ) (hk : k ≤ al.length ^ s) : rt_PF al s b r d k = rt_Apre al s b r d k := by
  rw [rt_PF_eq]
  unfold rt_Apre
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  congr 1
  rw [← rt_localFunction_eq al hnd hall s b r d i (by omega)]
  unfold rt_sel
  rw [rt_vec_vidx al hnd hall]

theorem rt_chooseStep_lt (al : List F) (s b r d k : ℕ) (l : List ℕ)
    (hl : ∀ i ∈ l, i < al.length ^ b) (bi : ℕ) (hbi : bi < al.length ^ b) :
    l.foldl (rt_chooseStep al s b r d k) bi < al.length ^ b := by
  induction l generalizing bi with
  | nil => exact hbi
  | cons i l ih =>
    simp only [List.foldl_cons]
    apply ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    unfold rt_chooseStep; split_ifs
    · exact hl i (List.mem_cons_self)
    · exact hbi

theorem rt_chooseValue_eq (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al)
    (s b r d k : ℕ) (hk : k < al.length ^ s) :
    chooseValue al r d (rt_Apre al s b r d k) (rt_vec al s k) =
      rt_vec al b (rt_choose al s b r d k) := by
  have hq := rt_len_pos hall
  have hpos : (0 : ℚ) < (al.length : ℚ) ^ (b * d) := by positivity
  have hS : ∀ w, w < al.length ^ b →
      conditionalScore al r d (rt_Apre al s b r d k ++ [(rt_vec al s k, rt_vec al b w)]) =
        (rt_Sc al s b r d k w : ℚ) / (al.length : ℚ) ^ (b * d) := by
    intro w hw
    rw [← rt_score_eq al hnd hall s b r d k w hk hw]; field_simp
  unfold chooseValue rt_choose
  rw [rt_allVectors_eq, List.foldl_map]
  have key : ∀ (l : List ℕ), (∀ i ∈ l, i < al.length ^ b) → ∀ bi, bi < al.length ^ b →
      l.foldl (fun best i => if conditionalScore al r d (rt_Apre al s b r d k ++
        [(rt_vec al s k, rt_vec al b i)]) < conditionalScore al r d (rt_Apre al s b r d k ++
        [(rt_vec al s k, best)]) then rt_vec al b i else best) (rt_vec al b bi) =
      rt_vec al b (l.foldl (rt_chooseStep al s b r d k) bi) := by
    intro l
    induction l with
    | nil => intro _ bi _; rfl
    | cons i l ih =>
      intro hl bi hbi
      simp only [List.foldl_cons]
      have hi : i < al.length ^ b := hl i List.mem_cons_self
      have hl' : ∀ j ∈ l, j < al.length ^ b := fun j hj => hl j (List.mem_cons_of_mem _ hj)
      have hstep : (if conditionalScore al r d (rt_Apre al s b r d k ++
          [(rt_vec al s k, rt_vec al b i)]) < conditionalScore al r d (rt_Apre al s b r d k ++
          [(rt_vec al s k, rt_vec al b bi)]) then rt_vec al b i else rt_vec al b bi) =
          rt_vec al b (rt_chooseStep al s b r d k bi i) := by
        simp only [hS i hi, hS bi hbi, div_lt_div_iff_of_pos_right hpos]
        unfold rt_chooseStep
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd (by exact_mod_cast h1) h2
        · exact absurd (by exact_mod_cast h2) h1
        · rfl
      rw [hstep]
      apply ih hl'
      unfold rt_chooseStep; split_ifs
      · exact hi
      · exact hbi
  have h0 : (0 : Vec F b) = rt_vec al b (rt_z0 al b) := (rt_vec_vidx al hnd hall b 0).symm
  rw [h0]
  exact key _ (fun i hi => List.mem_range.mp hi) _ (rt_z0_lt al hnd hall b)

theorem rt_sel_eq_choose (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al)
    (s b r d : ℕ) (hs : 0 < s) (hb : 0 < b) (hr : 0 < r) (hd : 0 < d) (k : ℕ)
    (hk : k < al.length ^ s) :
    rt_sel al s b r d k = rt_choose al s b r d k := by
  have hq := rt_len_pos hall
  unfold rt_sel
  rw [rt_localFunction_eq al hnd hall s b r d k hk, rt_PF_eq_Apre al hnd hall s b r d k (by omega),
    rt_chooseValue_eq al hnd hall s b r d k hk]
  exact rt_vidx_vec al hnd hall b _ (rt_chooseStep_lt al s b r d k _
    (fun i hi => List.mem_range.mp hi) _ (rt_z0_lt al hnd hall b))

theorem rt_vectorData_vec (al : List F) (n w : ℕ) :
    vectorData (rt_vec al n w) =
      (List.range n).map (fun j => al.getD (rt_dg al.length w (n - 1 - j)) 0) := by
  apply List.ext_getElem (by simp [vectorData])
  intro i h1 h2
  simp [vectorData, rt_vec]

theorem rt_tableData_eq (al : List F) (hnd : al.Nodup) (hall : ∀ a : F, a ∈ al)
    (s b r d : ℕ) (hs : 0 < s) (hb : 0 < b) :
    localTableData al s b r d = rt_outData al s b r d (al.length ^ s) := by
  unfold localTableData
  rw [rt_allVectors_eq, List.map_map]
  have : ∀ n, n ≤ al.length ^ s → ((List.range n).map
      ((fun x => vectorData (localFunction al s b r d x)) ∘ rt_vec al s)).flatten =
      rt_outData al s b r d n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.map_append, List.flatten_append, ih (by omega)]
      simp only [rt_outData, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, Function.comp]
      congr 1
      have : localFunction al s b r d (rt_vec al s n) = rt_vec al b (rt_sel al s b r d n) := by
        unfold rt_sel; rw [rt_vec_vidx al hnd hall]
      rw [this, rt_vectorData_vec]
  exact this _ le_rfl

end Math

end SubspaceEvasion312.Explicit.Dev.LG
end
end

section
set_option autoImplicit false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.LG
open SubspaceEvasion312.Explicit
open Classical

/-! ## The program

Nat registers: 0 ZERO, 2 s, 3 b, 4 r, 5 d, 6 q, 7 q^b, 8 q^r, 9 q^(s+b), 10 Q1 = (q^(s+b))^r,
11 Q2 = (q^r)^d, 12 QA = Q1 * q^r, 13 q^s, 14 z0, 15 q^(b-1), 16 s+b;
20 K, 21 β, 22 t, 23 c, 24 j, 25 PJ, 26 XI, 27 YI, 28 AD, 29 W, 30 SC, 31 BS, 32 BEST, 33 OK,
34 U, 35 E, 36 PW, 37 TMP, 39 EV, 40 IDX, 41 PK, 42 KP, 43 IP, 44 PC, 45 PB, 46 DC, 47 DB,
48 DIG, 49 EE, 50 TA, 53 PD.  Field: 0 V, 16 F1, 32 F2, 48 ONE, 64 FT.
Memory regions (residues mod 16): 1 alphabet table, 2 marks, 3 DUP, 4 BAD, 5 FREE, 6 CUR,
7 CURW, 8 AMARK. -/

section Prog
variable {F : Type} [Field F]

def rt_L (d v : ℕ) : rt_Cmd F := .basic (.literal d v)
def rt_A (d a b : ℕ) : rt_Cmd F := .basic (.addNat d a b)
def rt_Sb (d a b : ℕ) : rt_Cmd F := .basic (.subNat d a b)
def rt_M (d a b : ℕ) : rt_Cmd F := .basic (.mulNat d a b)
def rt_D (d a b : ℕ) : rt_Cmd F := .basic (.divNat d a b)
def rt_Md (d a b : ℕ) : rt_Cmd F := .basic (.modNat d a b)
def rt_K (d : ℕ) (v : F) : rt_Cmd F := .basic (.constant d v)
def rt_FA (d a b : ℕ) : rt_Cmd F := .basic (.add d a b)
def rt_FM (d a b : ℕ) : rt_Cmd F := .basic (.mul d a b)
def rt_skip : rt_Cmd F := rt_L 61 0

def rt_seqs : List (rt_Cmd F) → rt_Cmd F
  | [] => rt_skip
  | [c] => c
  | c :: d :: cs => .seq c (rt_seqs (d :: cs))

/-- `dst := base ^ ex` (counter in register 35). -/
def rt_cPow (dst base ex : ℕ) : rt_Cmd F :=
  .seq (rt_seqs [rt_L dst 1, rt_L 35 0]) (.loop 35 ex (rt_M dst dst base))

def rt_cTab : List F → ℕ → rt_Cmd F
  | [], _ => rt_skip
  | a :: as, e => .seq (rt_seqs [rt_L 37 e, rt_K 64 a, .stR 1 37 64]) (rt_cTab as (e + 1))

def rt_cSetup (al : List F) (i0 : ℕ) : rt_Cmd F :=
  .seq (rt_seqs [.basic (.inputNat 2 0), .basic (.inputNat 3 1), .basic (.inputNat 4 2),
    .basic (.inputNat 5 3), rt_L 6 al.length])
  (.seq (rt_cPow 7 6 3) (.seq (rt_cPow 8 6 4) (.seq (rt_A 16 2 3) (.seq (rt_cPow 9 6 16)
  (.seq (rt_cPow 13 6 2) (.seq (rt_cPow 10 9 4) (.seq (rt_cPow 11 8 5)
  (.seq (rt_seqs [rt_M 12 10 8, rt_D 15 7 6, rt_L 14 0, rt_L 37 i0, rt_L 35 0])
  (.seq (.loop 35 3 (.seq (rt_M 14 14 6) (rt_A 14 14 37)))
  (.seq (rt_K 48 1) (rt_cTab al 0)))))))))))

/-- The inner loop of the point computation: `V += c_i * β_{i,k}`. -/
def rt_cPTin : rt_Cmd F :=
  rt_seqs [rt_D 46 23 44, rt_Md 46 46 6, rt_D 47 21 45, rt_Md 47 47 6,
    .ldR 16 1 46, .ldR 32 1 47, rt_FM 16 16 32, rt_FA 0 0 16, rt_M 44 44 6, rt_M 45 45 9]

/-- Scan for the index of `V` in the alphabet. -/
def rt_cScan : rt_Cmd F :=
  .seq (.ldR 16 1 49) (.ifF 16 0 (rt_A 48 49 0) rt_skip)

def rt_cPTout : rt_Cmd F :=
  .seq (rt_seqs [rt_K 0 0, rt_L 44 1, rt_A 45 41 0, rt_L 43 0]) (.seq (.loop 43 4 rt_cPTin)
    (.seq (rt_seqs [rt_L 48 0, rt_L 49 0]) (.seq (.loop 49 6 rt_cScan)
      (rt_seqs [rt_M 50 48 41, rt_A 40 40 50, rt_M 41 41 6]))))

/-- Point index: from `β` (21) and `c` (23) compute `XI` (26) and `YI` (27). -/
def rt_cPT : rt_Cmd F :=
  .seq (rt_seqs [rt_L 40 0, rt_L 41 1, rt_L 42 0])
    (.seq (.loop 42 16 rt_cPTout) (rt_seqs [rt_D 26 40 7, rt_Md 27 40 7]))

def rt_cPh0m : rt_Cmd F :=
  rt_seqs [rt_M 28 39 13, rt_A 28 28 26, .ldR 64 2 28, .ifF 64 48 (.stR 3 39 48) (.stR 2 28 48)]

def rt_cPh0j : rt_Cmd F :=
  .seq (rt_seqs [rt_D 23 22 25, rt_Md 23 23 8, rt_M 25 25 8]) (.seq rt_cPT rt_cPh0m)

def rt_cPh0t : rt_Cmd F :=
  .seq (rt_seqs [rt_M 39 21 11, rt_A 39 39 22, rt_L 25 1, rt_L 24 0]) (.loop 24 5 rt_cPh0j)

def rt_cPh0 : rt_Cmd F :=
  .seq (rt_L 21 0) (.loop 21 10 (.seq (rt_L 22 0) (.loop 22 11 rt_cPh0t)))

def rt_cPh1r : rt_Cmd F :=
  rt_seqs [rt_M 28 20 12, rt_M 37 21 8, rt_A 28 28 37, rt_A 28 28 23, rt_Sb 37 26 20,
    .ifN 37 0
      (.ifN 26 20 (rt_seqs [.stR 6 28 48, rt_M 37 28 7, rt_A 37 37 27, .stR 7 37 48])
        (rt_seqs [rt_M 37 26 7, rt_A 37 37 27, .ldR 64 8 37, .ifF 64 48 rt_skip (.stR 4 28 48)]))
      (.stR 5 28 48)]

def rt_cPh1c : rt_Cmd F := .seq rt_cPT rt_cPh1r

def rt_cPh1 : rt_Cmd F :=
  .seq (rt_L 21 0) (.loop 21 10 (.seq (rt_L 23 0) (.loop 23 8 rt_cPh1c)))

def rt_cScjA : rt_Cmd F :=
  rt_seqs [rt_D 23 22 25, rt_Md 23 23 8, rt_M 25 25 8,
    rt_M 28 20 12, rt_M 37 21 8, rt_A 28 28 37, rt_A 28 28 23]

def rt_cChkBad : rt_Cmd F := .seq (.ldR 64 4 28) (.ifF 64 48 (rt_L 33 0) rt_skip)

def rt_cChkFree : rt_Cmd F :=
  .seq (.ldR 64 5 28) (.ifF 64 48 (.seq (rt_L 37 1) (rt_A 34 34 37)) rt_skip)

def rt_cChkCur : rt_Cmd F :=
  .seq (.ldR 64 6 28)
    (.ifF 64 48 (rt_seqs [rt_M 37 28 7, rt_A 37 37 29, .ldR 64 7 37, .ifF 64 48 rt_skip (rt_L 33 0)])
      rt_skip)

def rt_cScj : rt_Cmd F := .seq rt_cScjA (.seq rt_cChkBad (.seq rt_cChkFree rt_cChkCur))

def rt_cScAdd : rt_Cmd F :=
  .seq (rt_seqs [rt_L 36 1, rt_A 35 34 0]) (.seq (.loop 35 5 (rt_M 36 36 7)) (rt_A 30 30 36))

def rt_cScEv : rt_Cmd F :=
  .seq (rt_seqs [rt_L 33 1, rt_L 34 0, rt_L 25 1, rt_L 24 0])
    (.seq (.loop 24 5 rt_cScj) (.seq (rt_L 37 1) (.ifN 33 37 rt_cScAdd rt_skip)))

def rt_cSct : rt_Cmd F :=
  .seq (rt_seqs [rt_M 39 21 11, rt_A 39 39 22, .ldR 64 3 39]) (.ifF 64 48 rt_skip rt_cScEv)

/-- `SC` (30) := the scaled score of value `W` (29) at input `K` (20). -/
def rt_cScore : rt_Cmd F :=
  .seq (rt_seqs [rt_L 30 0, rt_L 21 0]) (.loop 21 10 (.seq (rt_L 22 0) (.loop 22 11 rt_cSct)))

def rt_cChw : rt_Cmd F :=
  .seq rt_cScore (.seq (rt_Sb 37 31 30) (.ifN 37 0 rt_skip (.seq (rt_A 32 29 0) (rt_A 31 30 0))))

def rt_cChoose : rt_Cmd F :=
  .seq (rt_A 29 14 0) (.seq rt_cScore (.seq (rt_seqs [rt_A 31 30 0, rt_A 32 14 0, rt_L 29 0])
    (.loop 29 7 rt_cChw)))

def rt_cOutj : rt_Cmd F :=
  rt_seqs [rt_D 37 32 53, rt_Md 37 37 6, .ldR 64 1 37, .basic (.output 64), rt_D 53 53 6]

def rt_cOut : rt_Cmd F :=
  .seq (rt_seqs [rt_M 37 20 7, rt_A 37 37 32, .stR 8 37 48, rt_A 53 15 0, rt_L 24 0])
    (.loop 24 3 rt_cOutj)

def rt_cMain (al : List F) (i0 : ℕ) : rt_Cmd F :=
  rt_seqs [rt_cSetup al i0, rt_cPh0, rt_L 20 0,
    .loop 20 13 (rt_seqs [rt_cPh1, rt_cChoose, rt_cOut])]

end Prog

/-! ## Invariants -/

section Inv
variable {F : Type} [Field F] [Fintype F]

/-- A memory region holds the indicator of `S`. -/
def rt_Reg (st : rt_St F) (k : ℕ) (S : ℕ → Prop) : Prop :=
  ∀ o, st.fr (o * 16 + k) = if S o then 1 else 0

/-- The constant registers and the alphabet table. -/
structure rt_Cst (al : List F) (s b r d : ℕ) (st : rt_St F) : Prop where
  h0 : st.nr 0 = 0
  h2 : st.nr 2 = s
  h3 : st.nr 3 = b
  h4 : st.nr 4 = r
  h5 : st.nr 5 = d
  h6 : st.nr 6 = al.length
  h7 : st.nr 7 = al.length ^ b
  h8 : st.nr 8 = al.length ^ r
  h9 : st.nr 9 = al.length ^ (s + b)
  h10 : st.nr 10 = (al.length ^ (s + b)) ^ r
  h11 : st.nr 11 = (al.length ^ r) ^ d
  h12 : st.nr 12 = (al.length ^ (s + b)) ^ r * al.length ^ r
  h13 : st.nr 13 = al.length ^ s
  h14 : st.nr 14 = rt_z0 al b
  h15 : st.nr 15 = al.length ^ (b - 1)
  h16 : st.nr 16 = s + b
  f48 : st.fr 48 = 1
  tab : ∀ e < al.length, st.fr (e * 16 + 1) = al.getD e 0

/-- Commands that never touch the constants: nat writes at registers `≥ 17`, field writes to
residue-0 registers other than 48, no stores into region 1. -/
def rt_okC (c : rt_Cmd F) : Bool :=
  (rt_wn c).all (fun j => decide (17 ≤ j)) &&
  (rt_wf c).all (fun x => decide (x % 16 = 0 ∧ x ≠ 48)) &&
  (rt_wr c).all (fun k => decide (k ≠ 1 ∧ k ≠ 0))

/-- The global sizes. -/
def rt_G (q s b r d : ℕ) : ℕ :=
  (q ^ (s + b)) ^ r * (q ^ r) ^ d * q ^ s * q ^ r * q ^ b * (q ^ b) ^ d * q ^ (s + b) * q

structure rt_Hyp (al : List F) (s b r d B : ℕ) : Prop where
  nd : al.Nodup
  all : ∀ a : F, a ∈ al
  q2 : 2 ≤ al.length
  hs : 0 < s
  hb : 0 < b
  hr : 0 < r
  hd : 0 < d
  hB : 64 * rt_G al.length s b r d ≤ B

/-! Region contents during the run. -/

def rt_DUPS (al : List F) (s b r d : ℕ) (ev : ℕ) : Prop :=
  ev < (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d ∧ rt_dupP al s b r d ev d

/-- Keys `o = k * QA + β * q^r + c` processed so far (`o < D`) whose point is bad. -/
def rt_BADS (al : List F) (s b r d D : ℕ) (o : ℕ) : Prop :=
  o < D ∧ rt_bad al s b r d (o / ((al.length ^ (s + b)) ^ r * al.length ^ r))
    (o % ((al.length ^ (s + b)) ^ r * al.length ^ r) / al.length ^ r) (o % al.length ^ r)

def rt_FREES (al : List F) (s b r D : ℕ) (o : ℕ) : Prop :=
  o < D ∧ o / ((al.length ^ (s + b)) ^ r * al.length ^ r) <
    rt_xi al s b r (o % ((al.length ^ (s + b)) ^ r * al.length ^ r) / al.length ^ r)
      (o % al.length ^ r)

def rt_CURS (al : List F) (s b r D : ℕ) (o : ℕ) : Prop :=
  o < D ∧ rt_xi al s b r (o % ((al.length ^ (s + b)) ^ r * al.length ^ r) / al.length ^ r)
      (o % al.length ^ r) = o / ((al.length ^ (s + b)) ^ r * al.length ^ r)

def rt_CURWS (al : List F) (s b r D : ℕ) (m : ℕ) : Prop :=
  rt_CURS al s b r D (m / al.length ^ b) ∧
    m % al.length ^ b = rt_yi al s b r
      (m / al.length ^ b % ((al.length ^ (s + b)) ^ r * al.length ^ r) / al.length ^ r)
      (m / al.length ^ b % al.length ^ r)

def rt_AMS (al : List F) (s b r d k : ℕ) (m : ℕ) : Prop :=
  m / al.length ^ b < k ∧ m % al.length ^ b = rt_sel al s b r d (m / al.length ^ b)

/-- The phase-2 regions, keys below `D` processed. -/
def rt_Regs47 (al : List F) (s b r d D : ℕ) (st : rt_St F) : Prop :=
  rt_Reg st 4 (rt_BADS al s b r d D) ∧ rt_Reg st 5 (rt_FREES al s b r D) ∧
  rt_Reg st 6 (rt_CURS al s b r D) ∧ rt_Reg st 7 (rt_CURWS al s b r D)

end Inv


/-! ## Generic invariant lemmas -/

section Gen
variable {F : Type} [Field F] [Fintype F]

theorem rt_notin_of {l : List ℕ} {j : ℕ} (h : l.contains j = false) : j ∉ l := by
  intro hm; simp_all

theorem rt_okC_iff (c : rt_Cmd F) : rt_okC c = true ↔
    (∀ j ∈ rt_wn c, 17 ≤ j) ∧ (∀ x ∈ rt_wf c, x % 16 = 0 ∧ x ≠ 48) ∧
      (∀ k ∈ rt_wr c, k ≠ 1 ∧ k ≠ 0) := by
  simp [rt_okC, List.all_eq_true, and_assoc]

theorem rt_Cst_agr {al : List F} {s b r d : ℕ} {c : rt_Cmd F} (hc : rt_okC c = true)
    {st st' : rt_St F} (h : rt_Agr c st st') (hC : rt_Cst al s b r d st) :
    rt_Cst al s b r d st' := by
  obtain ⟨h1, h2, h3⟩ := (rt_okC_iff c).mp hc
  obtain ⟨a1, a2, _⟩ := h
  have hn : ∀ j, j ≤ 16 → st'.nr j = st.nr j := fun j hj =>
    a1 j (fun hm => by have := h1 j hm; omega)
  have hf : ∀ x, x % 16 ≠ 0 ∨ x = 48 → x % 16 = 1 ∨ x % 16 = 0 → st'.fr x = st.fr x := by
    intro x hx1 hx2
    apply a2
    · intro hm; have := (h2 x hm).1; have := (h2 x hm).2; omega
    · intro hm; have := (h3 _ hm).1; have := (h3 _ hm).2; omega
  exact ⟨by rw [hn 0 (by omega)]; exact hC.h0, by rw [hn 2 (by omega)]; exact hC.h2,
    by rw [hn 3 (by omega)]; exact hC.h3, by rw [hn 4 (by omega)]; exact hC.h4,
    by rw [hn 5 (by omega)]; exact hC.h5, by rw [hn 6 (by omega)]; exact hC.h6,
    by rw [hn 7 (by omega)]; exact hC.h7, by rw [hn 8 (by omega)]; exact hC.h8,
    by rw [hn 9 (by omega)]; exact hC.h9, by rw [hn 10 (by omega)]; exact hC.h10,
    by rw [hn 11 (by omega)]; exact hC.h11, by rw [hn 12 (by omega)]; exact hC.h12,
    by rw [hn 13 (by omega)]; exact hC.h13, by rw [hn 14 (by omega)]; exact hC.h14,
    by rw [hn 15 (by omega)]; exact hC.h15, by rw [hn 16 (by omega)]; exact hC.h16,
    by rw [hf 48 (by omega) (by omega)]; exact hC.f48,
    fun e he => by rw [hf (e * 16 + 1) (by omega) (by omega)]; exact hC.tab e he⟩

theorem rt_Reg_agr {c : rt_Cmd F} (hc : rt_okC c = true) {k : ℕ} (hk : k % 16 ∉ rt_wr c)
    (hk0 : k % 16 ≠ 0) {S : ℕ → Prop} {st st' : rt_St F} (h : rt_Agr c st st')
    (hR : rt_Reg st k S) : rt_Reg st' k S := by
  obtain ⟨_, h2, _⟩ := (rt_okC_iff c).mp hc
  intro o
  rw [h.2.1 _ (fun hm => by have := (h2 _ hm).1; omega)
    (by rw [show (o * 16 + k) % 16 = k % 16 by omega]; exact hk)]
  exact hR o

theorem rt_nr_agr {c : rt_Cmd F} {j : ℕ} (hj : j ∉ rt_wn c) {st st' : rt_St F}
    (h : rt_Agr c st st') : st'.nr j = st.nr j := h.1 j hj

theorem rt_out_agr {c : rt_Cmd F} (hc : rt_wo c = false) {st st' : rt_St F}
    (h : rt_Agr c st st') : st'.out = st.out := h.2.2 hc

theorem rt_inc_nr (st : rt_St F) (i j : ℕ) (hi : i ≠ 61) :
    (rt_inc st i).nr j = if j = i then st.nr i + 1 else if j = 61 then 1 else st.nr j := by
  simp only [rt_inc, Function.update_apply]
  split_ifs <;> simp_all

theorem rt_Cst_inc {al : List F} {s b r d : ℕ} {st : rt_St F} {i : ℕ} (hi : 17 ≤ i)
    (hi' : i ≠ 61)
    (hC : rt_Cst al s b r d st) : rt_Cst al s b r d (rt_inc st i) := by
  have hn : ∀ j, j ≤ 16 → (rt_inc st i).nr j = st.nr j := by
    intro j hj
    rw [rt_inc_nr st i j (by omega), if_neg (show j ≠ i by omega), if_neg (show j ≠ 61 by omega)]
  exact ⟨by rw [hn 0 (by omega)]; exact hC.h0, by rw [hn 2 (by omega)]; exact hC.h2,
    by rw [hn 3 (by omega)]; exact hC.h3, by rw [hn 4 (by omega)]; exact hC.h4,
    by rw [hn 5 (by omega)]; exact hC.h5, by rw [hn 6 (by omega)]; exact hC.h6,
    by rw [hn 7 (by omega)]; exact hC.h7, by rw [hn 8 (by omega)]; exact hC.h8,
    by rw [hn 9 (by omega)]; exact hC.h9, by rw [hn 10 (by omega)]; exact hC.h10,
    by rw [hn 11 (by omega)]; exact hC.h11, by rw [hn 12 (by omega)]; exact hC.h12,
    by rw [hn 13 (by omega)]; exact hC.h13, by rw [hn 14 (by omega)]; exact hC.h14,
    by rw [hn 15 (by omega)]; exact hC.h15, by rw [hn 16 (by omega)]; exact hC.h16,
    hC.f48, hC.tab⟩

theorem rt_Bd_inc {B : ℕ} {st : rt_St F} {i : ℕ} (hi : i ≠ 61) (hb : rt_Bd B st)
    (h1 : 1 ≤ B) (hv : st.nr i + 1 ≤ B) : rt_Bd B (rt_inc st i) := by
  intro j; rw [rt_inc_nr st i j hi]; split_ifs
  · exact hv
  · exact h1
  · exact hb j

theorem rt_Reg_congr {st : rt_St F} {k : ℕ} {S S' : ℕ → Prop} (h : rt_Reg st k S)
    (hS : ∀ o, S o ↔ S' o) : rt_Reg st k S' := by
  intro o; rw [h o]; simp only [hS o]

theorem rt_Reg_inc {st : rt_St F} {k i : ℕ} {S : ℕ → Prop} (h : rt_Reg st k S) :
    rt_Reg (rt_inc st i) k S := h

theorem rt_Reg_read {st : rt_St F} {k : ℕ} {S : ℕ → Prop} (h : rt_Reg st k S) (o : ℕ) :
    st.fr (o * 16 + k) = 1 ↔ S o := by
  rw [h o]; split_ifs with hs
  · simp [hs]
  · simp [hs]

theorem rt_Reg_upd {st st' : rt_St F} {k o : ℕ} {S S' : ℕ → Prop} (hk : k < 16)
    (h : rt_Reg st k S) (hfr : st'.fr = Function.update st.fr (o * 16 + k) 1)
    (hS : ∀ x, S' x ↔ S x ∨ x = o) : rt_Reg st' k S' := by
  intro x
  rw [hfr, Function.update_apply]
  by_cases hx : x = o
  · subst hx; rw [if_pos rfl, if_pos ((hS _).mpr (Or.inr rfl))]
  · rw [if_neg (by omega), h x]; simp only [hS x, hx, or_false]

theorem rt_Reg_same {st st' : rt_St F} {k : ℕ} {S : ℕ → Prop} (h : rt_Reg st k S)
    (hfr : st'.fr = st.fr) : rt_Reg st' k S := by
  intro x; rw [hfr]; exact h x

theorem rt_G_pos (q s b r d : ℕ) (hq : 1 ≤ q) : 0 < rt_G q s b r d := by
  unfold rt_G; have : 0 < q := hq; positivity

theorem rt_b_le_pow (q b : ℕ) (hq : 2 ≤ q) : b < q ^ b :=
  lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_left hq b)

/-- Bounds from the global size. -/
theorem rt_Gb1 (q s b r d : ℕ) (hq : 1 ≤ q) :
    q ^ s * ((q ^ (s + b)) ^ r * q ^ r) * q ^ b ≤ rt_G q s b r d :=
  Nat.le_of_dvd (rt_G_pos q s b r d hq) ⟨(q ^ r) ^ d * (q ^ b) ^ d * q ^ (s + b) * q,
    by unfold rt_G; ring⟩

theorem rt_Gb2 (q s b r d : ℕ) (hq : 1 ≤ q) :
    (q ^ (s + b)) ^ r * (q ^ r) ^ d * (q ^ b) ^ d ≤ rt_G q s b r d :=
  Nat.le_of_dvd (rt_G_pos q s b r d hq) ⟨q ^ s * q ^ r * q ^ b * q ^ (s + b) * q,
    by unfold rt_G; ring⟩

theorem rt_Gb3 (q s b r d : ℕ) (hq : 1 ≤ q) :
    (q ^ (s + b)) ^ r * (q ^ r) ^ d * q ^ s ≤ rt_G q s b r d :=
  Nat.le_of_dvd (rt_G_pos q s b r d hq) ⟨q ^ r * q ^ b * (q ^ b) ^ d * q ^ (s + b) * q,
    by unfold rt_G; ring⟩

theorem rt_Gb4 (q s b r d : ℕ) (hq : 1 ≤ q) :
    (q ^ (s + b)) ^ r * q ^ (s + b) * q ≤ rt_G q s b r d :=
  Nat.le_of_dvd (rt_G_pos q s b r d hq) ⟨(q ^ r) ^ d * q ^ s * q ^ r * q ^ b * (q ^ b) ^ d,
    by unfold rt_G; ring⟩

theorem rt_val01 {st : rt_St F} {k o : ℕ} {S : ℕ → Prop} {P : Prop} [Decidable P] (hR : rt_Reg st k S)
    (h : S o ↔ P) : st.fr (o * 16 + k) = if P then 1 else 0 := by
  rw [hR o]; simp only [h]

theorem rt_val01' {st : rt_St F} {k o : ℕ} {S : ℕ → Prop} {P : Prop} [Decidable P] (hR : rt_Reg st k S)
    (h : st.fr (o * 16 + k) = 1 ↔ P) : st.fr (o * 16 + k) = if P then 1 else 0 := by
  rw [hR o] at h ⊢
  by_cases hS : S o
  · rw [if_pos hS] at h; rw [if_pos hS, if_pos (h.mp rfl)]
  · rw [if_neg hS] at h
    have hP : ¬ P := fun hp => zero_ne_one (h.mpr hp)
    rw [if_neg hS, if_neg hP]

theorem rt_Reg_chg {st st' : rt_St F} {k : ℕ} {S S' P : ℕ → Prop} (hR : rt_Reg st k S)
    (hfr : ∀ o, st'.fr (o * 16 + k) = if P o then 1 else st.fr (o * 16 + k))
    (hS : ∀ o, S' o ↔ S o ∨ P o) : rt_Reg st' k S' := by
  intro o
  rw [hfr o, hR o]
  by_cases hP : P o
  · rw [if_pos hP, if_pos ((hS o).mpr (Or.inr hP))]
  · rw [if_neg hP]; simp only [hS o, hP, or_false]

theorem rt_ad_dm {Q1 QR k β c : ℕ} (hβ : β < Q1) (hc : c < QR) :
    (k * (Q1 * QR) + β * QR + c) / (Q1 * QR) = k ∧
    (k * (Q1 * QR) + β * QR + c) % (Q1 * QR) / QR = β ∧
    (k * (Q1 * QR) + β * QR + c) % QR = c ∧
    k * (Q1 * QR) + β * QR + c < (k + 1) * (Q1 * QR) := by
  have h1 : β * QR + c < Q1 * QR := by
    have : (β + 1) * QR ≤ Q1 * QR := Nat.mul_le_mul_right _ hβ
    rw [Nat.succ_mul] at this; omega
  have e1 := rt_divmod (k := k) h1
  have e2 := rt_divmod (k := β) hc
  have e3 := rt_divmod (k := k * Q1 + β) hc
  rw [add_assoc]
  refine ⟨e1.1, by rw [e1.2, e2.1], ?_, by rw [Nat.succ_mul]; omega⟩
  rw [show k * (Q1 * QR) + (β * QR + c) = (k * Q1 + β) * QR + c by ring, e3.2]

end Gen

/-! ## Component specifications -/

section Specs
variable {F : Type} [Field F] [Fintype F]

def rt_kPT (q s b r : ℕ) : ℕ := (s + b) * (22 * r + 13 * q + 30) + 10

set_option maxHeartbeats 1000000 in
theorem rt_PT_spec (al : List F) (s b r d B : ℕ) (H : rt_Hyp al s b r d B) (ns : List ℕ)
    (β c : ℕ) (hβ : β < (al.length ^ (s + b)) ^ r) (hc : c < al.length ^ r) :
    rt_Sp ns B rt_cPT
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 21 = β ∧ st.nr 23 = c)
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 26 = rt_xi al s b r β c ∧
        st.nr 27 = rt_yi al s b r β c)
      (rt_kPT al.length s b r) := by
  have hq := H.q2
  have hB := H.hB
  have hG4 := rt_Gb4 al.length s b r d (by omega)
  have hG1 := rt_Gb1 al.length s b r d (by omega)
  have hq0 : 0 < al.length := by omega
  -- generic size facts
  have hpow : ∀ e, e ≤ r * (s + b) + (s + b) → al.length ^ e ≤ B := by
    intro e he
    have : al.length ^ e ≤ (al.length ^ (s + b)) ^ r * al.length ^ (s + b) := by
      rw [← pow_mul, ← pow_add]
      exact Nat.pow_le_pow_right hq0 (by have := Nat.mul_comm r (s + b); omega)
    have : (al.length ^ (s + b)) ^ r * al.length ^ (s + b) ≤
      (al.length ^ (s + b)) ^ r * al.length ^ (s + b) * al.length := Nat.le_mul_of_pos_right _ hq0
    omega
  have hβB : β ≤ B := by
    have : (al.length ^ (s + b)) ^ r ≤ (al.length ^ (s + b)) ^ r * al.length ^ (s + b) * al.length :=
      by rw [mul_assoc]; exact Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hs := H.hs
  have hb := H.hb
  have hrsb : r ≤ r * (s + b) := Nat.le_mul_of_pos_right r (by omega)
  have hcB : c ≤ B := by
    have := hpow r (by omega); omega
  have hrB : r + 1 ≤ B := by
    have := hpow r (by omega)
    have := Nat.lt_pow_self (n := r) (show 1 < al.length by omega); omega
  have hqB : al.length * 17 + 17 ≤ B := by
    have h1 : 1 ≤ (al.length ^ (s + b)) ^ r := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h2 : al.length ≤ al.length ^ (s + b) := Nat.le_self_pow (by omega) _
    have h3 : al.length * 1 ≤ al.length ^ (s + b) * (al.length ^ (s + b)) ^ r :=
      Nat.mul_le_mul h2 h1
    have h4 : al.length ^ (s + b) * (al.length ^ (s + b)) ^ r * 2 ≤
        (al.length ^ (s + b)) ^ r * al.length ^ (s + b) * al.length := by
      rw [mul_comm (al.length ^ (s + b)) _]; exact Nat.mul_le_mul_left _ hq
    omega
  let V : ℕ → ℕ → F := fun k' i => ∑ i' ∈ Finset.range i,
    al.getD (rt_dg al.length c i') 0 * al.getD (rt_dg al.length β (i' * (s + b) + k')) 0
  let ACC : ℕ → ℕ := fun k' => ∑ k ∈ Finset.range k', rt_ix al (rt_pv al s b r β c k) * al.length ^ k
  have hACC : ∀ k' ≤ s + b, ACC k' < al.length ^ k' :=
    fun k' _ => rt_digsum_lt _ _ _ (by omega) (fun k _ => rt_ix_lt H.all _)
  let OI : ℕ → rt_St F → Prop := fun k' st => rt_Cst al s b r d st ∧ rt_Bd B st ∧
    st.nr 21 = β ∧ st.nr 23 = c ∧ st.nr 42 = k' ∧ st.nr 41 = al.length ^ k' ∧ st.nr 40 = ACC k'
  have e1 : rt_Sp ns B (rt_seqs [rt_L 40 0, rt_L 41 1, rt_L 42 0])
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 21 = β ∧ st.nr 23 = c) (OI 0) 3 := by
    apply rt_sp_sym'
    rintro st ⟨hC, hb, h21, h23⟩
    refine ⟨hb, by simp [rt_seqs, rt_symV, rt_L, rt_wv, rt_simple]; omega, fun hb' hA => ?_⟩
    have hn : ∀ x, x ∉ rt_wn (rt_seqs [rt_L (F := F) 40 0, rt_L 41 1, rt_L 42 0]) →
        (rt_sym ns (rt_seqs [rt_L 40 0, rt_L 41 1, rt_L 42 0]) st).nr x = st.nr x :=
      fun x hx => rt_nr_agr hx hA
    refine ⟨rt_Cst_agr rfl hA hC, hb', by rw [hn 21 (rt_notin_of rfl), h21],
      by rw [hn 23 (rt_notin_of rfl), h23], ?_, ?_, ?_⟩ <;>
      simp [rt_seqs, rt_sym, rt_L, rt_eff, rt_setN, ACC]
  have e2 : rt_Sp ns B (.loop 42 16 rt_cPTout) (OI 0) (OI (s + b))
      ((s + b - 0) * ((4 + ((r - 0) * (18 + 4) + 1) + (2 + ((al.length - 0) * (9 + 4) + 1) + 3)) + 4)
        + 1) := by
    refine rt_sp_loop OI 0 (s + b) _ (Nat.zero_le _) ?_ ?_
    · rintro k' st _ _ ⟨hC, hb, -, -, h42, -⟩
      exact ⟨h42, hC.h16, hb⟩
    · intro k' _ hk'
      have hk'B : k' + 1 ≤ B := by
        have := hpow (k' + 1) (by omega)
        have := Nat.lt_pow_self (n := k' + 1) (show 1 < al.length by omega)
        omega
      let II : ℕ → rt_St F → Prop := fun i st => OI k' st ∧ st.nr 43 = i ∧
        st.nr 44 = al.length ^ i ∧ st.nr 45 = al.length ^ (i * (s + b) + k') ∧ st.fr 0 = V k' i
      let SI : ℕ → rt_St F → Prop := fun e st => OI k' st ∧ st.fr 0 = V k' r ∧ st.nr 49 = e ∧
        st.nr 48 = (if rt_ix al (V k' r) < e then rt_ix al (V k' r) else 0)
      have hOIn : ∀ (c' : rt_Cmd F), rt_okC c' = true → (21 : ℕ) ∉ rt_wn c' →
          (23 : ℕ) ∉ rt_wn c' → (42 : ℕ) ∉ rt_wn c' → (41 : ℕ) ∉ rt_wn c' → (40 : ℕ) ∉ rt_wn c' →
          ∀ st st', rt_Agr c' st st' → rt_Bd B st' → OI k' st → OI k' st' := by
        intro c' hok n21 n23 n42 n41 n40 st st' hA hb' ⟨hC, _, h21, h23, h42, h41, h40⟩
        exact ⟨rt_Cst_agr hok hA hC, hb', by rw [rt_nr_agr n21 hA, h21], by rw [rt_nr_agr n23 hA, h23],
          by rw [rt_nr_agr n42 hA, h42], by rw [rt_nr_agr n41 hA, h41], by rw [rt_nr_agr n40 hA, h40]⟩
      have f1 : rt_Sp ns B (rt_seqs [rt_K 0 0, rt_L 44 1, rt_A 45 41 0, rt_L 43 0]) (OI k')
          (II 0) 4 := by
        apply rt_sp_sym'
        rintro st hO
        obtain ⟨hC, hb, h21, h23, h42, h41, h40⟩ := hO
        refine ⟨hb, by simp [rt_seqs, rt_symV, rt_sym, rt_K, rt_L, rt_A, rt_wv, rt_simple, rt_eff,
          rt_setN, rt_setF, h41, hC.h0]; exact ⟨by omega, by rw [← h41]; exact hb 41⟩,
          fun hb' hA => ⟨hOIn _ rfl (rt_notin_of rfl) (rt_notin_of rfl) (rt_notin_of rfl)
            (rt_notin_of rfl) (rt_notin_of rfl) st _ hA hb' ⟨hC, hb, h21, h23, h42, h41, h40⟩,
            ?_, ?_, ?_, ?_⟩⟩ <;>
          simp [rt_seqs, rt_sym, rt_K, rt_L, rt_A, rt_eff, rt_setN, rt_setF, h41, hC.h0, V]
      have f2 : rt_Sp ns B (.loop 43 4 rt_cPTin) (II 0) (II r) ((r - 0) * (18 + 4) + 1) := by
        refine rt_sp_loop II 0 r _ (Nat.zero_le _) ?_ ?_
        · rintro i st _ _ ⟨⟨hC, hb, -⟩, h43, -⟩
          exact ⟨h43, hC.h4, hb⟩
        · intro i _ hi
          apply rt_sp_sym'
          rintro st ⟨⟨hC, hb, h21, h23, h42, h41, h40⟩, h43, h44, h45, h0⟩
          have hdc : c / al.length ^ i % al.length < al.length := Nat.mod_lt _ hq0
          have hdb : β / al.length ^ (i * (s + b) + k') % al.length < al.length := Nat.mod_lt _ hq0
          have t1 := hC.tab _ hdc
          have t2 := hC.tab _ hdb
          have hne : ∀ x : ℕ, x * 16 + 1 ≠ 16 := by intro x; omega
          have hp1 := hpow (i + 1) (by omega)
          have hmi : (i + 1) * (s + b) ≤ r * (s + b) := Nat.mul_le_mul_right _ hi
          have hp2 := hpow ((i + 1) * (s + b) + k') (by omega)
          have e44 : al.length ^ i * al.length = al.length ^ (i + 1) := (pow_succ _ _).symm
          have e45 : al.length ^ (i * (s + b) + k') * al.length ^ (s + b) =
              al.length ^ ((i + 1) * (s + b) + k') := by rw [← pow_add]; ring_nf
          refine ⟨hb, ?_, fun hb' hA => ?_⟩
          · simp [rt_cPTin, rt_seqs, rt_symV, rt_sym, rt_D, rt_Md, rt_M, rt_FA, rt_FM, rt_wv,
              rt_simple, rt_eff, rt_setN, rt_setF, rt_ldRes, h23, h44, hC.h6, h21, h45, hC.h9]
            rw [e44, e45]
            exact ⟨le_trans (Nat.div_le_self _ _) hcB, by omega,
              le_trans (Nat.div_le_self _ _) hβB, by omega, by omega, by omega, hp1, hp2⟩
          · have key : (rt_sym ns rt_cPTin st).nr 44 = al.length ^ (i + 1) ∧
                (rt_sym ns rt_cPTin st).nr 45 = al.length ^ ((i + 1) * (s + b) + k') ∧
                (rt_sym ns rt_cPTin st).fr 0 = V k' (i + 1) := by
              simp [rt_cPTin, rt_seqs, rt_sym, rt_D, rt_Md, rt_M, rt_FA, rt_FM, rt_eff, rt_setN,
                rt_setF, rt_ldRes, h23, h44, hC.h6, h21, h45, hC.h9, e44, e45, hne, t1, t2, h0, V,
                Finset.sum_range_succ, rt_dg]
            obtain ⟨k44, k45, k0⟩ := key
            have hO' := hOIn _ rfl (rt_notin_of rfl) (rt_notin_of rfl) (rt_notin_of rfl)
              (rt_notin_of rfl) (rt_notin_of rfl) st _ hA hb' ⟨hC, hb, h21, h23, h42, h41, h40⟩
            have hbi : rt_Bd B (rt_inc (rt_sym ns rt_cPTin st) 43) := rt_Bd_inc (by decide) hb'
              (by omega) (by rw [rt_nr_agr (rt_notin_of rfl) hA, h43]; omega)
            have hI : ∀ x, x ≠ 43 → x ≠ 61 → (rt_inc (rt_sym ns (rt_cPTin (F := F)) st) 43).nr x =
                (rt_sym ns rt_cPTin st).nr x := by
              intro x h1 h2; rw [rt_inc_nr _ _ _ (by decide), if_neg h1, if_neg h2]
            obtain ⟨oC, -, o21, o23, o42, o41, o40⟩ := hO'
            refine ⟨hb', hbi, ⟨rt_Cst_inc (by decide) (by decide) oC, hbi,
              by rw [hI 21 (by decide) (by decide), o21], by rw [hI 23 (by decide) (by decide), o23],
              by rw [hI 42 (by decide) (by decide), o42], by rw [hI 41 (by decide) (by decide), o41],
              by rw [hI 40 (by decide) (by decide), o40]⟩,
              by rw [rt_inc_nr _ _ _ (by decide), if_pos rfl, rt_nr_agr (rt_notin_of rfl) hA, h43],
              by rw [hI 44 (by decide) (by decide), k44], by rw [hI 45 (by decide) (by decide), k45],
              k0⟩
      have f3 : rt_Sp ns B (rt_seqs [rt_L 48 0, rt_L 49 0]) (II r) (SI 0) 2 := by
        apply rt_sp_sym'
        rintro st ⟨hO, h43, h44, h45, h0⟩
        refine ⟨hO.2.1, by simp [rt_seqs, rt_symV, rt_L, rt_wv, rt_simple], fun hb' hA => ?_⟩
        refine ⟨hOIn _ rfl (rt_notin_of rfl) (rt_notin_of rfl) (rt_notin_of rfl) (rt_notin_of rfl)
          (rt_notin_of rfl) st _ hA hb' hO, by rw [← h0]; rfl, ?_, ?_⟩ <;>
          simp [rt_seqs, rt_sym, rt_L, rt_eff, rt_setN]
      have f4 : rt_Sp ns B (.loop 49 6 rt_cScan) (SI 0) (SI al.length) ((al.length - 0) * (9 + 4) + 1) := by
        refine rt_sp_loop SI 0 _ _ (Nat.zero_le _) ?_ ?_
        · rintro e st _ _ ⟨⟨hC, hb, -⟩, -, h49, -⟩
          exact ⟨h49, hC.h6, hb⟩
        · intro e _ he
          apply rt_sp_sym'
          rintro st ⟨hO, h0, h49, h48⟩
          obtain ⟨hC, hb, h21, h23, h42, h41, h40⟩ := hO
          have t1 := hC.tab e he
          have hne : ∀ x : ℕ, x * 16 + 1 ≠ 16 := by intro x; omega
          have hiff := rt_getD_eq_iff H.nd H.all (V k' r) e he
          refine ⟨hb, ?_, fun hb' hA => ?_⟩
          · simp [rt_cScan, rt_symV, rt_sym, rt_ldRes, rt_A, rt_skip, rt_L, rt_wv, rt_simple, h49,
              t1, hne, h0, hC.h0]
            exact ⟨by omega, fun _ => by omega⟩
          · have k48 : (rt_sym ns rt_cScan st).nr 48 =
                (if rt_ix al (V k' r) < e + 1 then rt_ix al (V k' r) else 0) := by
              have hcond : (rt_ldRes st 16 1 49).fr 16 = (rt_ldRes st 16 1 49).fr 0 ↔
                  e = rt_ix al (V k' r) := by
                simp only [rt_ldRes, h49, Function.update_apply, if_true,
                  show (0 : ℕ) ≠ 16 from by decide, if_false, t1, h0]
                exact hiff
              by_cases hx : e = rt_ix al (V k' r)
              · have hc := hcond.mpr hx
                simp only [rt_cScan, rt_sym, if_pos hc]
                have hc' : st.fr (e * 16 + 1) = st.fr 0 := by rw [t1, h0]; exact hiff.mpr hx
                simp [rt_sym, rt_A, rt_eff, rt_setN, rt_ldRes, h49, hC.h0, hc']
                split_ifs <;> omega
              · have hc : ¬ (rt_ldRes st 16 1 49).fr 16 = (rt_ldRes st 16 1 49).fr 0 :=
                  fun h => hx (hcond.mp h)
                simp only [rt_cScan, rt_sym, if_neg hc]
                have hc' : ¬ st.fr (e * 16 + 1) = st.fr 0 := by
                  rw [t1, h0]; exact fun h => hx (hiff.mp h)
                simp [rt_sym, rt_skip, rt_L, rt_eff, rt_setN, rt_ldRes, h48, hc', h49]
                split_ifs <;> omega
            have hO' := hOIn _ rfl (rt_notin_of rfl) (rt_notin_of rfl) (rt_notin_of rfl)
              (rt_notin_of rfl) (rt_notin_of rfl) st _ hA hb' ⟨hC, hb, h21, h23, h42, h41, h40⟩
            have hbi : rt_Bd B (rt_inc (rt_sym ns rt_cScan st) 49) := rt_Bd_inc (by decide) hb'
              (by omega) (by rw [rt_nr_agr (rt_notin_of rfl) hA, h49]; omega)
            have hI : ∀ x, x ≠ 49 → x ≠ 61 → (rt_inc (rt_sym ns (rt_cScan (F := F)) st) 49).nr x =
                (rt_sym ns rt_cScan st).nr x := by
              intro x h1 h2; rw [rt_inc_nr _ _ _ (by decide), if_neg h1, if_neg h2]
            obtain ⟨oC, -, o21, o23, o42, o41, o40⟩ := hO'
            have hf0 : (rt_sym ns (rt_cScan (F := F)) st).fr 0 = V k' r := by
              rw [hA.2.1 0 (rt_notin_of rfl) (rt_notin_of rfl), h0]
            refine ⟨hb', hbi, ⟨rt_Cst_inc (by decide) (by decide) oC, hbi,
              by rw [hI 21 (by decide) (by decide), o21], by rw [hI 23 (by decide) (by decide), o23],
              by rw [hI 42 (by decide) (by decide), o42], by rw [hI 41 (by decide) (by decide), o41],
              by rw [hI 40 (by decide) (by decide), o40]⟩, hf0,
              by rw [rt_inc_nr _ _ _ (by decide), if_pos rfl, rt_nr_agr (rt_notin_of rfl) hA, h49],
              by rw [hI 48 (by decide) (by decide), k48]⟩
      have f5 : rt_Sp ns B (rt_seqs [rt_M 50 48 41, rt_A 40 40 50, rt_M 41 41 6]) (SI al.length)
          (fun s1 => rt_Bd B s1 ∧ rt_Bd B (rt_inc s1 42) ∧ OI (k' + 1) (rt_inc s1 42)) 3 := by
        apply rt_sp_sym'
        rintro st ⟨⟨hC, hb, h21, h23, h42, h41, h40⟩, h0, h49, h48⟩
        have hix := rt_ix_lt H.all (V k' r)
        rw [if_pos hix] at h48
        have hA1 : ACC (k' + 1) = ACC k' + rt_ix al (V k' r) * al.length ^ k' := by
          simp only [ACC, Finset.sum_range_succ]; rfl
        have hA2 := hACC (k' + 1) (by omega)
        have hp := hpow (k' + 1) (by omega)
        have e41 : al.length ^ k' * al.length = al.length ^ (k' + 1) := (pow_succ _ _).symm
        refine ⟨hb, ?_, fun hb' hA => ?_⟩
        · simp [rt_seqs, rt_symV, rt_sym, rt_M, rt_A, rt_wv, rt_simple, rt_eff, rt_setN, h48, h41,
            h40, hC.h6]
          rw [e41]; refine ⟨by omega, by omega, by omega⟩
        · have hn : ∀ x, x ∉ rt_wn (rt_seqs [rt_M (F := F) 50 48 41, rt_A 40 40 50, rt_M 41 41 6]) →
              (rt_sym ns (rt_seqs [rt_M 50 48 41, rt_A 40 40 50, rt_M 41 41 6]) st).nr x = st.nr x :=
            fun x hx => rt_nr_agr hx hA
          have k40 : (rt_sym ns (rt_seqs [rt_M (F := F) 50 48 41, rt_A 40 40 50, rt_M 41 41 6]) st).nr 40
              = ACC (k' + 1) := by
            simp [rt_seqs, rt_sym, rt_M, rt_A, rt_eff, rt_setN, h48, h41, h40, hC.h6]; omega
          have k41 : (rt_sym ns (rt_seqs [rt_M (F := F) 50 48 41, rt_A 40 40 50, rt_M 41 41 6]) st).nr 41
              = al.length ^ (k' + 1) := by
            simp [rt_seqs, rt_sym, rt_M, rt_A, rt_eff, rt_setN, h48, h41, h40, hC.h6]; exact e41
          have hbi : rt_Bd B (rt_inc (rt_sym ns (rt_seqs [rt_M (F := F) 50 48 41, rt_A 40 40 50,
              rt_M 41 41 6]) st) 42) :=
            rt_Bd_inc (by decide) hb' (by omega) (by rw [hn 42 (rt_notin_of rfl), h42]; omega)
          have hI : ∀ x, x ≠ 42 → x ≠ 61 → (rt_inc (rt_sym ns (rt_seqs [rt_M (F := F) 50 48 41,
              rt_A 40 40 50, rt_M 41 41 6]) st) 42).nr x = (rt_sym ns (rt_seqs [rt_M (F := F) 50 48 41,
              rt_A 40 40 50, rt_M 41 41 6]) st).nr x := by
            intro x h1 h2; rw [rt_inc_nr _ _ _ (by decide), if_neg h1, if_neg h2]
          refine ⟨hb', hbi, rt_Cst_inc (by decide) (by decide) (rt_Cst_agr rfl hA hC), hbi,
            by rw [hI 21 (by decide) (by decide), hn 21 (rt_notin_of rfl), h21],
            by rw [hI 23 (by decide) (by decide), hn 23 (rt_notin_of rfl), h23],
            by rw [rt_inc_nr _ _ _ (by decide), if_pos rfl, hn 42 (rt_notin_of rfl), h42],
            by rw [hI 41 (by decide) (by decide), k41], by rw [hI 40 (by decide) (by decide), k40]⟩
      refine rt_sp_conseq (rt_sp_seq f1 (rt_sp_seq f2 (rt_sp_seq f3 (rt_sp_seq f4 f5))))
        (fun st h => h) (fun st h => h) ?_
      omega
  have e3 : rt_Sp ns B (rt_seqs [rt_D 26 40 7, rt_Md 27 40 7]) (OI (s + b))
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 26 = rt_xi al s b r β c ∧
        st.nr 27 = rt_yi al s b r β c) 2 := by
    apply rt_sp_sym'
    rintro st ⟨hC, hb, h21, h23, h42, h41, h40⟩
    have := hACC (s + b) le_rfl
    have := hpow (s + b) (by omega)
    have := Nat.div_le_self (ACC (s + b)) (al.length ^ b)
    have := Nat.mod_le (ACC (s + b)) (al.length ^ b)
    refine ⟨hb, by simp [rt_seqs, rt_symV, rt_sym, rt_D, rt_Md, rt_wv, rt_simple, rt_eff, rt_setN,
      h40, hC.h7]; constructor <;> omega, fun hb' hA => ?_⟩
    refine ⟨rt_Cst_agr rfl hA hC, hb', ?_, ?_⟩ <;>
      simp [rt_seqs, rt_sym, rt_D, rt_Md, rt_eff, rt_setN, h40, hC.h7, rt_xi, rt_yi, rt_pidx, ACC]
  refine rt_sp_conseq (rt_sp_seq e1 (rt_sp_seq e2 e3)) (fun st h => h) (fun st h => h) ?_
  simp only [rt_kPT, Nat.sub_zero]
  ring_nf; omega

/-! ### Phase 0 -/

/-- Marks set before stage `(ev, j)`: key `m = ev' * q^s + x`. -/
def rt_M0 (al : List F) (s b r d ev j m : ℕ) : Prop :=
  ∃ j' < d, (m / al.length ^ s) * d + j' < ev * d + j ∧
    rt_ex al s b r d (m / al.length ^ s) j' = m % al.length ^ s

def rt_D0 (al : List F) (s b r d ev j e : ℕ) : Prop :=
  (e < ev ∧ rt_dupP al s b r d e d) ∨ (e = ev ∧ rt_dupP al s b r d e j)

theorem rt_M0_read (al : List F) (s b r d ev j x : ℕ) (hj : j ≤ d) (hx : x < al.length ^ s) :
    rt_M0 al s b r d ev j (ev * al.length ^ s + x) ↔ ∃ j' < j, rt_ex al s b r d ev j' = x := by
  obtain ⟨e1, e2⟩ := rt_divmod (k := ev) hx
  unfold rt_M0
  rw [e1, e2]
  constructor
  · rintro ⟨j', _, h1, h2⟩; exact ⟨j', by omega, h2⟩
  · rintro ⟨j', h1, h2⟩; exact ⟨j', by omega, by omega, h2⟩

theorem rt_M0_succ (al : List F) (s b r d ev j : ℕ) (hj : j < d)
    (hx : rt_ex al s b r d ev j < al.length ^ s) (m : ℕ) :
    rt_M0 al s b r d ev (j + 1) m ↔
      rt_M0 al s b r d ev j m ∨ m = ev * al.length ^ s + rt_ex al s b r d ev j := by
  obtain ⟨e1, e2⟩ := rt_divmod (k := ev) hx
  unfold rt_M0
  constructor
  · rintro ⟨j', hj', h1, h2⟩
    by_cases hlt : m / al.length ^ s * d + j' < ev * d + j
    · exact Or.inl ⟨j', hj', hlt, h2⟩
    · right
      have heq : m / al.length ^ s * d + j' = ev * d + j := by omega
      have hm : m / al.length ^ s = ev ∧ j' = j := by
        have := rt_divmod (Q := d) (k := m / al.length ^ s) hj'
        have := rt_divmod (Q := d) (k := ev) hj
        rw [heq] at *
        constructor <;> omega
      obtain ⟨hm1, rfl⟩ := hm
      rw [hm1] at h2
      have := Nat.div_add_mod m (al.length ^ s)
      rw [hm1, ← h2] at this; rw [← this]; ring
  · rintro (⟨j', hj', h1, h2⟩ | rfl)
    · exact ⟨j', hj', by omega, h2⟩
    · rw [e1, e2]; exact ⟨j, hj, by omega, rfl⟩

theorem rt_dupP_succ (al : List F) (s b r d ev j : ℕ) :
    rt_dupP al s b r d ev (j + 1) ↔ rt_dupP al s b r d ev j ∨
      ∃ j' < j, rt_ex al s b r d ev j' = rt_ex al s b r d ev j := by
  unfold rt_dupP
  constructor
  · rintro ⟨j1, j2, h1, h2, h3⟩
    by_cases h : j2 < j
    · exact Or.inl ⟨j1, j2, h1, h, h3⟩
    · right; have : j2 = j := by omega
      subst this; exact ⟨j1, h1, h3⟩
  · rintro (⟨j1, j2, h1, h2, h3⟩ | ⟨j', h1, h2⟩)
    · exact ⟨j1, j2, h1, by omega, h3⟩
    · exact ⟨j', j, h1, by omega, h2⟩

theorem rt_D0_succ (al : List F) (s b r d ev j e : ℕ) :
    rt_D0 al s b r d ev (j + 1) e ↔ rt_D0 al s b r d ev j e ∨
      (e = ev ∧ ∃ j' < j, rt_ex al s b r d ev j' = rt_ex al s b r d ev j) := by
  unfold rt_D0
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · exact Or.inl (Or.inl h)
    · rcases (rt_dupP_succ al s b r d e j).mp h with h' | h'
      · exact Or.inl (Or.inr ⟨rfl, h'⟩)
      · exact Or.inr ⟨rfl, h'⟩
  · rintro ((h | ⟨rfl, h⟩) | ⟨rfl, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, (rt_dupP_succ al s b r d e j).mpr (Or.inl h)⟩
    · exact Or.inr ⟨rfl, (rt_dupP_succ al s b r d e j).mpr (Or.inr h)⟩

theorem rt_D0_next (al : List F) (s b r d ev e : ℕ) :
    rt_D0 al s b r d ev d e ↔ rt_D0 al s b r d (ev + 1) 0 e := by
  unfold rt_D0
  have h0 : ¬ rt_dupP al s b r d e 0 := by rintro ⟨j1, j2, h1, h2, -⟩; omega
  constructor
  · rintro (⟨h1, h2⟩ | ⟨rfl, h2⟩)
    · exact Or.inl ⟨by omega, h2⟩
    · exact Or.inl ⟨by omega, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨rfl, h2⟩)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨h, h2⟩
    · exact absurd h2 h0

theorem rt_M0_next (al : List F) (s b r d ev m : ℕ) :
    rt_M0 al s b r d ev d m ↔ rt_M0 al s b r d (ev + 1) 0 m := by
  unfold rt_M0; rw [show ev * d + d = (ev + 1) * d + 0 by ring]

def rt_kPh0 (q s b r d : ℕ) : ℕ :=
  (q ^ (s + b)) ^ r * ((q ^ r) ^ d * (d * (rt_kPT q s b r + 40) + 10) + 10) + 10

theorem rt_Ph0_spec (al : List F) (s b r d B : ℕ) (H : rt_Hyp al s b r d B) (ns : List ℕ) :
    rt_Sp ns B rt_cPh0
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ rt_Reg st 2 (fun _ => False) ∧
        rt_Reg st 3 (fun _ => False))
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ rt_Reg st 3 (rt_DUPS al s b r d))
      (rt_kPh0 al.length s b r d) := by
  have hq := H.q2
  have hB := H.hB
  have hG3 := rt_Gb3 al.length s b r d (by omega)
  have hG2 := rt_Gb2 al.length s b r d (by omega)
  have hG1 := rt_Gb1 al.length s b r d (by omega)
  have hQRp : 0 < al.length ^ r := by positivity
  have hQ12 : (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d ≤
      (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d * al.length ^ s :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have hQ2le : (al.length ^ r) ^ d ≤ (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have hdB : d + 1 ≤ B := by
    have : d < (al.length ^ b) ^ d := lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_left (le_trans hq (Nat.le_self_pow (by have := H.hb; omega) _)) _)
    have : (al.length ^ b) ^ d ≤ (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d *
      (al.length ^ b) ^ d := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  -- the per-point update
  have eM : ∀ β t j, β < (al.length ^ (s + b)) ^ r → t < (al.length ^ r) ^ d → j < d →
      rt_Sp ns B rt_cPh0m
        (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 21 = β ∧ st.nr 22 = t ∧
          st.nr 39 = β * (al.length ^ r) ^ d + t ∧ st.nr 24 = j ∧
          st.nr 25 = (al.length ^ r) ^ (j + 1) ∧
          st.nr 26 = rt_ex al s b r d (β * (al.length ^ r) ^ d + t) j ∧
          rt_Reg st 2 (rt_M0 al s b r d (β * (al.length ^ r) ^ d + t) j) ∧
          rt_Reg st 3 (rt_D0 al s b r d (β * (al.length ^ r) ^ d + t) j))
        (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 21 = β ∧ st.nr 22 = t ∧
          st.nr 39 = β * (al.length ^ r) ^ d + t ∧ st.nr 24 = j ∧
          st.nr 25 = (al.length ^ r) ^ (j + 1) ∧
          rt_Reg st 2 (rt_M0 al s b r d (β * (al.length ^ r) ^ d + t) (j + 1)) ∧
          rt_Reg st 3 (rt_D0 al s b r d (β * (al.length ^ r) ^ d + t) (j + 1)))
        (rt_len (rt_cPh0m (F := F))) := by
    intro β t j hβ ht hj
    have hEV : β * (al.length ^ r) ^ d + t < (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d := by
      have : (β + 1) * (al.length ^ r) ^ d ≤ (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d :=
        Nat.mul_le_mul_right _ hβ
      rw [Nat.succ_mul] at this; omega
    set ev := β * (al.length ^ r) ^ d + t with hev
    set x := rt_ex al s b r d ev j with hxdef
    have hx : x < al.length ^ s := rt_xi_lt al H.nd H.all s b r _ _
    have hAD : ev * al.length ^ s + x < (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d *
        al.length ^ s := by
      have := Nat.mul_le_mul_right (al.length ^ s) hEV
      rw [Nat.succ_mul] at this; omega
    apply rt_sp_sym'
    rintro st ⟨hC, hb, h21, h22, h39, h24, h25, h26, h2, h3⟩
    have hv2 : st.fr ((ev * al.length ^ s + x) * 16 + 2) =
        if (∃ j' < j, rt_ex al s b r d ev j' = x) then 1 else 0 :=
      rt_val01 h2 (rt_M0_read al s b r d ev j x (by omega) hx)
    refine ⟨hb, ?_, fun hb' hA => ?_⟩
    · simp [rt_cPh0m, rt_seqs, rt_symV, rt_sym, rt_M, rt_A, rt_wv, rt_simple, rt_eff, rt_setN,
        rt_ldRes, h39, h26, hC.h13, hv2, hC.f48]
      refine ⟨by omega, by omega, by omega, ?_⟩
      split_ifs <;> omega
    · have hC' := rt_Cst_agr rfl hA hC
      have hn : ∀ y, y ∉ rt_wn (rt_cPh0m (F := F)) → (rt_sym ns rt_cPh0m st).nr y = st.nr y :=
        fun y hy => rt_nr_agr hy hA
      refine ⟨hC', hb', by rw [hn 21 (rt_notin_of rfl), h21], by rw [hn 22 (rt_notin_of rfl), h22],
        by rw [hn 39 (rt_notin_of rfl), h39], by rw [hn 24 (rt_notin_of rfl), h24],
        by rw [hn 25 (rt_notin_of rfl), h25], ?_⟩
      have SM := rt_M0_succ al s b r d ev j hj hx
      have SD := rt_D0_succ al s b r d ev j
      by_cases hd : ∃ j' < j, rt_ex al s b r d ev j' = x
      · have hv2' : st.fr ((ev * al.length ^ s + x) * 16 + 2) = 1 := by rw [hv2, if_pos hd]
        have hin : rt_M0 al s b r d ev j (ev * al.length ^ s + x) :=
          (rt_M0_read al s b r d ev j x (by omega) hx).mpr hd
        have hfr : (rt_sym ns rt_cPh0m st).fr = Function.update (Function.update st.fr 64
            (st.fr ((ev * al.length ^ s + x) * 16 + 2))) (ev * 16 + 3) 1 := by
          simp [rt_cPh0m, rt_seqs, rt_sym, rt_M, rt_A, rt_eff, rt_setN, rt_ldRes, rt_stRes,
            h39, h26, hC.h13, hv2', hC.f48]
        refine ⟨rt_Reg_chg (P := fun _ => False) h2 (fun o => ?_) (fun o => ?_),
          rt_Reg_chg (P := fun e => e = ev) h3 (fun o => ?_) (fun o => ?_)⟩
        · clear * - hfr; rw [hfr]; simp only [Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega)
        · rw [SM o]; constructor
          · rintro (h | rfl); · exact Or.inl h
            · exact Or.inl hin
          · rintro (h | h); · exact Or.inl h
            · exact h.elim
        · clear * - hfr; rw [hfr]; simp only [Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega)
        · rw [SD o]; constructor
          · rintro (h | ⟨rfl, -⟩); · exact Or.inl h
            · exact Or.inr rfl
          · rintro (h | rfl); · exact Or.inl h
            · exact Or.inr ⟨rfl, hd⟩
      · have hv2' : st.fr ((ev * al.length ^ s + x) * 16 + 2) = 0 := by rw [hv2, if_neg hd]
        have hfr : (rt_sym ns rt_cPh0m st).fr = Function.update (Function.update st.fr 64
            (st.fr ((ev * al.length ^ s + x) * 16 + 2))) ((ev * al.length ^ s + x) * 16 + 2) 1 := by
          simp [rt_cPh0m, rt_seqs, rt_sym, rt_M, rt_A, rt_eff, rt_setN, rt_ldRes, rt_stRes,
            h39, h26, hC.h13, hv2', hC.f48]
        refine ⟨rt_Reg_chg (P := fun m => m = ev * al.length ^ s + x) h2 (fun o => ?_)
            (fun o => SM o),
          rt_Reg_chg (P := fun _ => False) h3 (fun o => ?_) (fun o => ?_)⟩
        · clear * - hfr; rw [hfr]; simp only [Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega)
        · clear * - hfr; rw [hfr]; simp only [Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega)
        · rw [SD o]; constructor
          · rintro (h | ⟨-, h⟩); · exact Or.inl h
            · exact absurd h hd
          · rintro (h | h); · exact Or.inl h
            · exact h.elim
  -- loops
  let JI : ℕ → ℕ → ℕ → rt_St F → Prop := fun β t j st => rt_Cst al s b r d st ∧ rt_Bd B st ∧
    st.nr 21 = β ∧ st.nr 22 = t ∧ st.nr 39 = β * (al.length ^ r) ^ d + t ∧ st.nr 24 = j ∧
    st.nr 25 = (al.length ^ r) ^ j ∧
    rt_Reg st 2 (rt_M0 al s b r d (β * (al.length ^ r) ^ d + t) j) ∧
    rt_Reg st 3 (rt_D0 al s b r d (β * (al.length ^ r) ^ d + t) j)
  let TI : ℕ → ℕ → rt_St F → Prop := fun β t st => rt_Cst al s b r d st ∧ rt_Bd B st ∧
    st.nr 21 = β ∧ st.nr 22 = t ∧
    rt_Reg st 2 (rt_M0 al s b r d (β * (al.length ^ r) ^ d + t) 0) ∧
    rt_Reg st 3 (rt_D0 al s b r d (β * (al.length ^ r) ^ d + t) 0)
  let BI : ℕ → rt_St F → Prop := fun β st => rt_Cst al s b r d st ∧ rt_Bd B st ∧
    st.nr 21 = β ∧ rt_Reg st 2 (rt_M0 al s b r d (β * (al.length ^ r) ^ d) 0) ∧
    rt_Reg st 3 (rt_D0 al s b r d (β * (al.length ^ r) ^ d) 0)
  have hj : ∀ β t j, β < (al.length ^ (s + b)) ^ r → t < (al.length ^ r) ^ d → j < d →
      rt_Sp ns B rt_cPh0j (JI β t j)
        (fun s1 => rt_Bd B s1 ∧ rt_Bd B (rt_inc s1 24) ∧ JI β t (j + 1) (rt_inc s1 24))
        (3 + (rt_kPT al.length s b r + rt_len (rt_cPh0m (F := F)))) := by
    intro β t j hβ ht hj
    have hc : rt_ci al.length r t j < al.length ^ r := Nat.mod_lt _ hQRp
    have hQ2j : (al.length ^ r) ^ (j + 1) ≤ (al.length ^ r) ^ d := Nat.pow_le_pow_right hQRp hj
    have g0 : rt_Sp ns B (rt_seqs [rt_D 23 22 25, rt_Md 23 23 8, rt_M 25 25 8]) (JI β t j)
        (fun st => (rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 21 = β ∧
          st.nr 23 = rt_ci al.length r t j) ∧ (st.nr 21 = β ∧ st.nr 22 = t ∧
          st.nr 39 = β * (al.length ^ r) ^ d + t ∧
          st.nr 24 = j ∧ st.nr 25 = (al.length ^ r) ^ (j + 1) ∧
          rt_Reg st 2 (rt_M0 al s b r d (β * (al.length ^ r) ^ d + t) j) ∧
          rt_Reg st 3 (rt_D0 al s b r d (β * (al.length ^ r) ^ d + t) j))) 3 := by
      apply rt_sp_sym'
      rintro st ⟨hC, hb, h21, h22, h39, h24, h25, h2, h3⟩
      have htd : t / (al.length ^ r) ^ j ≤ t := Nat.div_le_self _ _
      have hQRle : al.length ^ r ≤ (al.length ^ r) ^ d := Nat.le_self_pow (by omega) _
      have hmod : t / (al.length ^ r) ^ j % al.length ^ r < al.length ^ r := Nat.mod_lt _ hQRp
      refine ⟨hb, ?_, fun hb' hA => ?_⟩
      · simp [rt_seqs, rt_symV, rt_sym, rt_D, rt_Md, rt_M, rt_wv, rt_simple, rt_eff, rt_setN, h22,
          h25, hC.h8]
        rw [← pow_succ]
        exact ⟨by omega, by omega, by omega⟩
      · have hn : ∀ y, y ∉ rt_wn (rt_seqs [rt_D (F := F) 23 22 25, rt_Md 23 23 8, rt_M 25 25 8]) →
            (rt_sym ns (rt_seqs [rt_D 23 22 25, rt_Md 23 23 8, rt_M 25 25 8]) st).nr y = st.nr y :=
          fun y hy => rt_nr_agr hy hA
        have kfr : (rt_sym ns (rt_seqs [rt_D (F := F) 23 22 25, rt_Md 23 23 8, rt_M 25 25 8]) st).fr
            = st.fr := rfl
        exact ⟨⟨rt_Cst_agr rfl hA hC, hb', by rw [hn 21 (rt_notin_of rfl), h21],
          by simp [rt_seqs, rt_sym, rt_D, rt_Md, rt_M, rt_eff, rt_setN, h22, h25, hC.h8, rt_ci]⟩,
          by rw [hn 21 (rt_notin_of rfl), h21], by rw [hn 22 (rt_notin_of rfl), h22], by rw [hn 39 (rt_notin_of rfl), h39],
          by rw [hn 24 (rt_notin_of rfl), h24],
          by simp [rt_seqs, rt_sym, rt_D, rt_Md, rt_M, rt_eff, rt_setN, h22, h25, hC.h8, pow_succ],
          rt_Reg_same h2 kfr, rt_Reg_same h3 kfr⟩
    have g1 := rt_sp_frame (rt_PT_spec al s b r d B H ns β (rt_ci al.length r t j) hβ hc)
      (R := fun st => st.nr 21 = β ∧ st.nr 22 = t ∧ st.nr 39 = β * (al.length ^ r) ^ d + t ∧
          st.nr 24 = j ∧ st.nr 25 = (al.length ^ r) ^ (j + 1) ∧
          rt_Reg st 2 (rt_M0 al s b r d (β * (al.length ^ r) ^ d + t) j) ∧
          rt_Reg st 3 (rt_D0 al s b r d (β * (al.length ^ r) ^ d + t) j))
      (by
        rintro st st' hA ⟨h21, h22, h39, h24, h25, h2, h3⟩
        exact ⟨by rw [rt_nr_agr (rt_notin_of rfl) hA, h21], by rw [rt_nr_agr (rt_notin_of rfl) hA, h22], by rw [rt_nr_agr (rt_notin_of rfl) hA, h39],
          by rw [rt_nr_agr (rt_notin_of rfl) hA, h24], by rw [rt_nr_agr (rt_notin_of rfl) hA, h25],
          rt_Reg_agr rfl (rt_notin_of rfl) (by decide) hA h2,
          rt_Reg_agr rfl (rt_notin_of rfl) (by decide) hA h3⟩)
    have hexj : rt_ex al s b r d (β * (al.length ^ r) ^ d + t) j = rt_xi al s b r β (rt_ci al.length r t j) := by
      obtain ⟨e1, e2⟩ := rt_divmod (k := β) ht
      unfold rt_ex; rw [e1, e2]
    have g2 := eM β t j hβ ht hj
    refine rt_sp_seq g0 (rt_sp_seq (rt_sp_conseq g1 ?_ (fun st h => h) le_rfl)
      (rt_sp_conseq g2 ?_ ?_ le_rfl))
    · rintro st ⟨⟨hC, hb, h21, h23⟩, hR⟩; exact ⟨⟨hC, hb, h21, h23⟩, hR⟩
    · rintro st ⟨⟨hC, hb, h26, -⟩, h21, h22, h39, h24, h25, h2, h3⟩
      exact ⟨hC, hb, h21, h22, h39, h24, h25, by rw [h26, hexj], h2, h3⟩
    · rintro st ⟨hC, hb, h21, h22, h39, h24, h25, h2, h3⟩
      have hbi : rt_Bd B (rt_inc st 24) := rt_Bd_inc (by decide) hb (by omega) (by rw [h24]; omega)
      have hI : ∀ x, x ≠ 24 → x ≠ 61 → (rt_inc st 24).nr x = st.nr x := by
        intro x h1 h2; rw [rt_inc_nr _ _ _ (by decide), if_neg h1, if_neg h2]
      exact ⟨hb, hbi, rt_Cst_inc (by decide) (by decide) hC, hbi,
        by rw [hI 21 (by decide) (by decide), h21], by rw [hI 22 (by decide) (by decide), h22],
        by rw [hI 39 (by decide) (by decide), h39], by rw [rt_inc_nr _ _ _ (by decide), if_pos rfl, h24],
        by rw [hI 25 (by decide) (by decide), h25], rt_Reg_inc h2, rt_Reg_inc h3⟩
  have ht : ∀ β t, β < (al.length ^ (s + b)) ^ r → t < (al.length ^ r) ^ d →
      rt_Sp ns B rt_cPh0t (TI β t)
        (fun s1 => rt_Bd B s1 ∧ rt_Bd B (rt_inc s1 22) ∧ TI β (t + 1) (rt_inc s1 22))
        (4 + ((d - 0) * (3 + (rt_kPT al.length s b r + rt_len (rt_cPh0m (F := F))) + 4) + 1)) := by
    intro β t hβ ht'
    have hEV : β * (al.length ^ r) ^ d + t < (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d := by
      have : (β + 1) * (al.length ^ r) ^ d ≤ (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d :=
        Nat.mul_le_mul_right _ hβ
      rw [Nat.succ_mul] at this; omega
    have g0 : rt_Sp ns B (rt_seqs [rt_M 39 21 11, rt_A 39 39 22, rt_L 25 1, rt_L 24 0]) (TI β t)
        (JI β t 0) 4 := by
      apply rt_sp_sym'
      rintro st ⟨hC, hb, h21, h22, h2, h3⟩
      refine ⟨hb, ?_, fun hb' hA => ?_⟩
      · simp [rt_seqs, rt_symV, rt_sym, rt_M, rt_A, rt_L, rt_wv, rt_simple, rt_eff, rt_setN, h21, h22,
          hC.h11]
        exact ⟨by omega, by omega, by omega⟩
      · have hn : ∀ y, y ∉ rt_wn (rt_seqs [rt_M (F := F) 39 21 11, rt_A 39 39 22, rt_L 25 1, rt_L 24 0])
            → (rt_sym ns (rt_seqs [rt_M 39 21 11, rt_A 39 39 22, rt_L 25 1, rt_L 24 0]) st).nr y =
              st.nr y := fun y hy => rt_nr_agr hy hA
        have kfr : (rt_sym ns (rt_seqs [rt_M (F := F) 39 21 11, rt_A 39 39 22, rt_L 25 1, rt_L 24 0])
            st).fr = st.fr := rfl
        exact ⟨rt_Cst_agr rfl hA hC, hb', by rw [hn 21 (rt_notin_of rfl), h21],
          by rw [hn 22 (rt_notin_of rfl), h22],
          by simp [rt_seqs, rt_sym, rt_M, rt_A, rt_L, rt_eff, rt_setN, h21, h22, hC.h11],
          by simp [rt_seqs, rt_sym, rt_M, rt_A, rt_L, rt_eff, rt_setN],
          by simp [rt_seqs, rt_sym, rt_M, rt_A, rt_L, rt_eff, rt_setN],
          rt_Reg_same h2 kfr, rt_Reg_same h3 kfr⟩
    have g1 : rt_Sp ns B (.loop 24 5 rt_cPh0j) (JI β t 0) (JI β t d)
        ((d - 0) * (3 + (rt_kPT al.length s b r + rt_len (rt_cPh0m (F := F))) + 4) + 1) := by
      refine rt_sp_loop (JI β t) 0 d _ (Nat.zero_le _) ?_ ?_
      · rintro j st _ _ ⟨hC, hb, -, -, -, h24, -⟩
        exact ⟨h24, hC.h5, hb⟩
      · intro j _ hj'
        exact hj β t j hβ ht' hj'
    refine rt_sp_conseq (rt_sp_seq g0 g1) (fun st h => h) ?_ le_rfl
    rintro st ⟨hC, hb, h21, h22, h39, h24, h25, h2, h3⟩
    have hbi : rt_Bd B (rt_inc st 22) := rt_Bd_inc (by decide) hb (by omega) (by rw [h22]; omega)
    have hI : ∀ x, x ≠ 22 → x ≠ 61 → (rt_inc st 22).nr x = st.nr x := by
      intro x h1 h2; rw [rt_inc_nr _ _ _ (by decide), if_neg h1, if_neg h2]
    refine ⟨hb, hbi, rt_Cst_inc (by decide) (by decide) hC, hbi,
      by rw [hI 21 (by decide) (by decide), h21], by rw [rt_inc_nr _ _ _ (by decide), if_pos rfl, h22],
      rt_Reg_congr (rt_Reg_inc h2) (fun m => ?_), rt_Reg_congr (rt_Reg_inc h3) (fun e => ?_)⟩
    · rw [rt_M0_next, Nat.add_assoc]
    · rw [rt_D0_next, Nat.add_assoc]
  have hβ : ∀ β, 0 ≤ β → β < (al.length ^ (s + b)) ^ r →
      rt_Sp ns B (.seq (rt_L 22 0) (.loop 22 11 rt_cPh0t)) (BI β)
        (fun s1 => rt_Bd B s1 ∧ rt_Bd B (rt_inc s1 21) ∧ BI (β + 1) (rt_inc s1 21))
        (1 + (((al.length ^ r) ^ d - 0) * ((4 + ((d - 0) * (3 + (rt_kPT al.length s b r +
          rt_len (rt_cPh0m (F := F))) + 4) + 1)) + 4) + 1)) := by
    intro β _ hβ'
    have g0 : rt_Sp ns B (rt_L 22 0) (BI β) (TI β 0) 1 := by
      apply rt_sp_sym'
      rintro st ⟨hC, hb, h21, h2, h3⟩
      refine ⟨hb, by simp [rt_symV, rt_L, rt_wv, rt_simple], fun hb' hA => ?_⟩
      have kfr : (rt_sym ns (rt_L (F := F) 22 0) st).fr = st.fr := rfl
      refine ⟨rt_Cst_agr rfl hA hC, hb', by rw [rt_nr_agr (rt_notin_of rfl) hA, h21],
        by simp [rt_sym, rt_L, rt_eff, rt_setN], ?_, ?_⟩
      · rw [Nat.add_zero]; exact rt_Reg_same h2 kfr
      · rw [Nat.add_zero]; exact rt_Reg_same h3 kfr
    have g1 : rt_Sp ns B (.loop 22 11 rt_cPh0t) (TI β 0) (TI β ((al.length ^ r) ^ d))
        (((al.length ^ r) ^ d - 0) * ((4 + ((d - 0) * (3 + (rt_kPT al.length s b r +
          rt_len (rt_cPh0m (F := F))) + 4) + 1)) + 4) + 1) := by
      refine rt_sp_loop (TI β) 0 _ _ (Nat.zero_le _) ?_ ?_
      · rintro t st _ _ ⟨hC, hb, -, h22, -⟩
        exact ⟨h22, hC.h11, hb⟩
      · intro t _ ht'
        exact ht β t hβ' ht'
    refine rt_sp_conseq (rt_sp_seq g0 g1) (fun st h => h) ?_ le_rfl
    rintro st ⟨hC, hb, h21, h22, h2, h3⟩
    have hβB : β + 1 ≤ B := by
      have : (al.length ^ (s + b)) ^ r ≤ (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d :=
        Nat.le_mul_of_pos_right _ (by positivity)
      omega
    have hbi : rt_Bd B (rt_inc st 21) := rt_Bd_inc (by decide) hb (by omega) (by rw [h21]; omega)
    refine ⟨hb, hbi, rt_Cst_inc (by decide) (by decide) hC, hbi,
      by rw [rt_inc_nr _ _ _ (by decide), if_pos rfl, h21], ?_, ?_⟩
    · rw [Nat.succ_mul]; exact rt_Reg_inc h2
    · rw [Nat.succ_mul]; exact rt_Reg_inc h3
  have e1 : rt_Sp ns B (rt_L 21 0)
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ rt_Reg st 2 (fun _ => False) ∧
        rt_Reg st 3 (fun _ => False)) (BI 0) 1 := by
    apply rt_sp_sym'
    rintro st ⟨hC, hb, h2, h3⟩
    refine ⟨hb, by simp [rt_symV, rt_L, rt_wv, rt_simple], fun hb' hA => ?_⟩
    have kfr : (rt_sym ns (rt_L (F := F) 21 0) st).fr = st.fr := rfl
    refine ⟨rt_Cst_agr rfl hA hC, hb', by simp [rt_sym, rt_L, rt_eff, rt_setN],
      rt_Reg_congr (rt_Reg_same h2 kfr) (fun m => ?_), rt_Reg_congr (rt_Reg_same h3 kfr) (fun e => ?_)⟩
    · simp [rt_M0]
    · simp [rt_D0]
      intro _ h; rcases h with ⟨j1, j2, h1, h2, -⟩; omega
  have e2 := rt_sp_loop (ns := ns) (B := B) (i := 21) (n := 10) BI 0 _ _ (Nat.zero_le _)
    (by rintro β st _ _ ⟨hC, hb, h21, -⟩; exact ⟨h21, hC.h10, hb⟩) hβ
  refine rt_sp_conseq (rt_sp_seq e1 e2) (fun st h => h) ?_ ?_
  · rintro st ⟨hC, hb, -, -, h3⟩
    refine ⟨hC, hb, rt_Reg_congr h3 (fun e => ?_)⟩
    simp only [rt_D0, rt_DUPS]
    constructor
    · rintro (h | ⟨-, j1, j2, h1, h2, -⟩)
      · exact h
      · omega
    · exact fun h => Or.inl h
  · simp only [rt_kPh0, Nat.sub_zero]
    have hl : rt_len (rt_cPh0m (F := F)) = 19 := by
      simp [rt_cPh0m, rt_seqs, rt_len, rt_M, rt_A]
    rw [hl]
    have h1 : d * (3 + (rt_kPT al.length s b r + 19) + 4) ≤ d * (rt_kPT al.length s b r + 40) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : (al.length ^ r) ^ d * (4 + (d * (3 + (rt_kPT al.length s b r + 19) + 4) + 1) + 4) ≤
        (al.length ^ r) ^ d * (d * (rt_kPT al.length s b r + 40) + 10) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : (al.length ^ (s + b)) ^ r * (1 + ((al.length ^ r) ^ d *
        (4 + (d * (3 + (rt_kPT al.length s b r + 19) + 4) + 1) + 4) + 1) + 4) ≤
        (al.length ^ (s + b)) ^ r * ((al.length ^ r) ^ d * (d * (rt_kPT al.length s b r + 40) + 10)
          + 10) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

theorem rt_succ_iff {o D : ℕ} {P : ℕ → Prop} :
    (o < D + 1 ∧ P o) ↔ (o < D ∧ P o) ∨ (o = D ∧ P D) := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
    · exact Or.inl ⟨h, h2⟩
    · subst h; exact Or.inr ⟨rfl, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨rfl, h2⟩)
    · exact ⟨by omega, h2⟩
    · exact ⟨by omega, h2⟩

section SetSucc
variable (al : List F) (s b r d k β c : ℕ) (hβ : β < (al.length ^ (s + b)) ^ r)
  (hc : c < al.length ^ r)
include hβ hc

theorem rt_BADS_succ (o : ℕ) :
    rt_BADS al s b r d (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c + 1) o
    ↔ rt_BADS al s b r d (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c) o
      ∨ (o = k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c ∧
        rt_bad al s b r d k β c) := by
  obtain ⟨d1, d2, d3, -⟩ := rt_ad_dm (k := k) hβ hc
  have := rt_succ_iff (o := o)
    (D := k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c)
    (P := fun o => rt_bad al s b r d (o / ((al.length ^ (s + b)) ^ r * al.length ^ r))
      (o % ((al.length ^ (s + b)) ^ r * al.length ^ r) / al.length ^ r) (o % al.length ^ r))
  simp only [d1, d2, d3] at this
  exact this

theorem rt_FREES_succ (o : ℕ) :
    rt_FREES al s b r (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c + 1) o
    ↔ rt_FREES al s b r (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c) o
      ∨ (o = k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c ∧
        k < rt_xi al s b r β c) := by
  obtain ⟨d1, d2, d3, -⟩ := rt_ad_dm (k := k) hβ hc
  have := rt_succ_iff (o := o)
    (D := k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c)
    (P := fun o => o / ((al.length ^ (s + b)) ^ r * al.length ^ r) <
      rt_xi al s b r (o % ((al.length ^ (s + b)) ^ r * al.length ^ r) / al.length ^ r)
        (o % al.length ^ r))
  simp only [d1, d2, d3] at this
  exact this

theorem rt_CURS_succ (o : ℕ) :
    rt_CURS al s b r (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c + 1) o
    ↔ rt_CURS al s b r (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c) o
      ∨ (o = k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c ∧
        rt_xi al s b r β c = k) := by
  obtain ⟨d1, d2, d3, -⟩ := rt_ad_dm (k := k) hβ hc
  have := rt_succ_iff (o := o)
    (D := k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c)
    (P := fun o => rt_xi al s b r (o % ((al.length ^ (s + b)) ^ r * al.length ^ r) / al.length ^ r)
      (o % al.length ^ r) = o / ((al.length ^ (s + b)) ^ r * al.length ^ r))
  simp only [d1, d2, d3] at this
  exact this

theorem rt_CURWS_succ (hy : rt_yi al s b r β c < al.length ^ b) (m : ℕ) :
    rt_CURWS al s b r (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c + 1) m
    ↔ rt_CURWS al s b r (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c) m
      ∨ (m = (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c) *
          al.length ^ b + rt_yi al s b r β c ∧ rt_xi al s b r β c = k) := by
  obtain ⟨d1, d2, d3, -⟩ := rt_ad_dm (k := k) hβ hc
  unfold rt_CURWS
  rw [rt_CURS_succ al s b r k β c hβ hc]
  constructor
  · rintro ⟨h1 | ⟨h1, h2⟩, h3⟩
    · exact Or.inl ⟨h1, h3⟩
    · right
      rw [h1, d2, d3] at h3
      refine ⟨?_, h2⟩
      have := Nat.div_add_mod m (al.length ^ b)
      rw [h1, h3] at this; rw [← this]; ring
  · rintro (⟨h1, h3⟩ | ⟨rfl, h2⟩)
    · exact ⟨Or.inl h1, h3⟩
    · obtain ⟨e1, e2⟩ := rt_divmod (k := k * ((al.length ^ (s + b)) ^ r * al.length ^ r) +
        β * al.length ^ r + c) hy
      rw [e1, e2, d2, d3]
      exact ⟨Or.inr ⟨rfl, h2⟩, rfl⟩

end SetSucc

/-- The point-status update of phase 1 at key `D = k * QA + β * q^r + c`. -/
theorem rt_Ph1r_spec (al : List F) (s b r d B : ℕ) (H : rt_Hyp al s b r d B) (ns : List ℕ)
    (k β c : ℕ) (hk : k < al.length ^ s) (hβ : β < (al.length ^ (s + b)) ^ r)
    (hc : c < al.length ^ r) :
    rt_Sp ns B rt_cPh1r
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 20 = k ∧ st.nr 21 = β ∧
        st.nr 23 = c ∧ st.nr 26 = rt_xi al s b r β c ∧ st.nr 27 = rt_yi al s b r β c ∧
        rt_Reg st 8 (rt_AMS al s b r d k) ∧
        rt_Regs47 al s b r d (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) +
          β * al.length ^ r + c) st)
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 20 = k ∧ st.nr 21 = β ∧
        st.nr 23 = c ∧ rt_Reg st 8 (rt_AMS al s b r d k) ∧
        rt_Regs47 al s b r d (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) +
          β * al.length ^ r + c + 1) st)
      (rt_len (rt_cPh1r (F := F))) := by
  have hq := H.q2
  have hB := H.hB
  have hG1 := rt_Gb1 al.length s b r d (by omega)
  have hx := rt_xi_lt al H.nd H.all s b r β c
  have hy := rt_yi_lt al H.nd H.all s b r β c
  obtain ⟨d1, d2, d3, d4⟩ := rt_ad_dm (k := k) hβ hc
  have hAD : k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c <
      al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) := by
    have : (k + 1) * ((al.length ^ (s + b)) ^ r * al.length ^ r) ≤
      al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) := Nat.mul_le_mul_right _ hk
    omega
  have hADy : (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c) *
      al.length ^ b + rt_yi al s b r β c <
      al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) * al.length ^ b := by
    have h2 := Nat.mul_le_mul_right (al.length ^ b) hAD
    rw [Nat.succ_mul] at h2; omega
  have hxy : rt_xi al s b r β c * al.length ^ b + rt_yi al s b r β c <
      al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) * al.length ^ b := by
    have h2 := Nat.mul_le_mul_right (al.length ^ b) hx
    rw [Nat.succ_mul] at h2
    have : al.length ^ s * al.length ^ b ≤
        al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) * al.length ^ b := by
      apply Nat.mul_le_mul_right; apply Nat.le_mul_of_pos_right; positivity
    omega
  have hQAs : al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) ≤
      al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) * al.length ^ b :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have hxs : al.length ^ s ≤ al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) :=
    Nat.le_mul_of_pos_right _ (by positivity)
  apply rt_sp_sym'
  rintro st ⟨hC, hb, h20, h21, h23, h26, h27, h8, h4, h5, h6, h7⟩
  have hv8 : st.fr ((rt_xi al s b r β c * al.length ^ b + rt_yi al s b r β c) * 16 + 8) =
      if rt_xi al s b r β c < k ∧ rt_yi al s b r β c = rt_sel al s b r d (rt_xi al s b r β c)
      then 1 else 0 := by
    refine rt_val01 h8 ?_
    obtain ⟨e1, e2⟩ := rt_divmod (k := rt_xi al s b r β c) hy
    simp only [rt_AMS, e1, e2]
  have hne : ∀ o : ℕ, ∀ j : ℕ, 0 < j → j < 16 → o * 16 + j ≠ 64 := by intro o j _ _; omega
  refine ⟨hb, ?_, fun hb' hA => ?_⟩
  · rcases lt_trichotomy (rt_xi al s b r β c) k with hlt | heq | hgt
    · have hs0 : rt_xi al s b r β c - k = 0 := by omega
      have hnk : rt_xi al s b r β c ≠ k := by omega
      simp [rt_cPh1r, rt_seqs, rt_symV, rt_sym, rt_M, rt_A, rt_Sb, rt_wv, rt_simple, rt_eff,
        rt_setN, rt_ldRes, rt_skip, rt_L, h20, h21, h23, h26, h27, hC.h0, hC.h7, hC.h8, hC.h12,
        hC.f48, hs0, hnk, hv8, hne]
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        fun _ => by omega⟩
    · have hs0 : rt_xi al s b r β c - k = 0 := by omega
      simp [rt_cPh1r, rt_seqs, rt_symV, rt_sym, rt_M, rt_A, rt_Sb, rt_wv, rt_simple, rt_eff,
        rt_setN, rt_stRes, rt_skip, rt_L, h20, h21, h23, h26, h27, hC.h0, hC.h7, hC.h8, hC.h12,
        hC.f48, hs0, heq]
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · have hs0 : rt_xi al s b r β c - k ≠ 0 := by omega
      simp [rt_cPh1r, rt_seqs, rt_symV, rt_sym, rt_M, rt_A, rt_Sb, rt_wv, rt_simple, rt_eff,
        rt_setN, rt_stRes, rt_skip, rt_L, h20, h21, h23, h26, h27, hC.h0, hC.h7, hC.h8, hC.h12,
        hC.f48, hs0]
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · have hC' := rt_Cst_agr rfl hA hC
    have k20 := rt_nr_agr (j := 20) (rt_notin_of rfl) hA
    have k21 := rt_nr_agr (j := 21) (rt_notin_of rfl) hA
    have k23 := rt_nr_agr (j := 23) (rt_notin_of rfl) hA
    have k8 := rt_Reg_agr rfl (rt_notin_of rfl) (by decide) hA h8
    refine ⟨hC', hb', by rw [k20, h20], by rw [k21, h21], by rw [k23, h23], k8, ?_⟩
    have S4 := rt_BADS_succ al s b r d k β c hβ hc
    have S5 := rt_FREES_succ al s b r k β c hβ hc
    have S6 := rt_CURS_succ al s b r k β c hβ hc
    have S7 := rt_CURWS_succ al s b r k β c hβ hc hy
    have rd : ∀ (f : ℕ → F) (a : ℕ) (v : F) (o j : ℕ),
        Function.update f a v (o * 16 + j) = if o * 16 + j = a then v else f (o * 16 + j) :=
      fun f a v o j => Function.update_apply _ _ _ _
    rcases lt_trichotomy (rt_xi al s b r β c) k with hlt | heq | hgt
    · have hs0 : rt_xi al s b r β c - k = 0 := by omega
      have hnk : rt_xi al s b r β c ≠ k := by omega
      have hnk' : ¬ k < rt_xi al s b r β c := by omega
      by_cases hys : rt_yi al s b r β c = rt_sel al s b r d (rt_xi al s b r β c)
      · have hnb : ¬ rt_bad al s b r d k β c := fun h => h.2 hys
        have hfr : (rt_sym ns rt_cPh1r st).fr = Function.update st.fr 64
            (st.fr ((rt_xi al s b r β c * al.length ^ b + rt_yi al s b r β c) * 16 + 8)) := by
          have hv8' : st.fr ((rt_xi al s b r β c * al.length ^ b + rt_yi al s b r β c) * 16 + 8)
              = 1 := by rw [hv8, if_pos ⟨hlt, hys⟩]
          simp [rt_cPh1r, rt_seqs, rt_sym, rt_M, rt_A, rt_Sb, rt_eff, rt_setN, rt_ldRes, rt_skip,
            rt_L, h20, h21, h23, h26, h27, hC.h0, hC.h7, hC.h8, hC.h12, hC.f48, hs0, hnk, hv8']
        refine ⟨rt_Reg_chg (P := fun _ => False) h4 (fun o => ?_) (fun o => by simp [S4 o, hnb]),
          rt_Reg_chg (P := fun _ => False) h5 (fun o => ?_) (fun o => by simp [S5 o, hnk']),
          rt_Reg_chg (P := fun _ => False) h6 (fun o => ?_) (fun o => by simp [S6 o, hnk]),
          rt_Reg_chg (P := fun _ => False) h7 (fun o => ?_) (fun o => by simp [S7 o, hnk])⟩ <;>
          (clear * - hfr rd; rw [hfr, rd] <;> simp <;> omega)
      · have hbd : rt_bad al s b r d k β c := ⟨hlt, hys⟩
        have hfr : (rt_sym ns rt_cPh1r st).fr = Function.update (Function.update st.fr 64
            (st.fr ((rt_xi al s b r β c * al.length ^ b + rt_yi al s b r β c) * 16 + 8)))
            ((k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c) * 16 + 4)
            1 := by
          have hv8' : st.fr ((rt_xi al s b r β c * al.length ^ b + rt_yi al s b r β c) * 16 + 8)
              = 0 := by rw [hv8, if_neg (fun h => hys h.2)]
          simp [rt_cPh1r, rt_seqs, rt_sym, rt_M, rt_A, rt_Sb, rt_eff, rt_setN, rt_ldRes, rt_skip,
            rt_L, rt_stRes, h20, h21, h23, h26, h27, hC.h0, hC.h7, hC.h8, hC.h12, hC.f48, hs0, hnk,
            hv8']
        refine ⟨rt_Reg_chg (P := fun o => o = k * ((al.length ^ (s + b)) ^ r * al.length ^ r) +
            β * al.length ^ r + c) h4 (fun o => ?_) (fun o => by simp [S4 o, hbd]),
          rt_Reg_chg (P := fun _ => False) h5 (fun o => ?_) (fun o => by simp [S5 o, hnk']),
          rt_Reg_chg (P := fun _ => False) h6 (fun o => ?_) (fun o => by simp [S6 o, hnk]),
          rt_Reg_chg (P := fun _ => False) h7 (fun o => ?_) (fun o => by simp [S7 o, hnk])⟩ <;>
          (clear * - hfr; rw [hfr]; simp only [Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega))
    · have hs0 : rt_xi al s b r β c - k = 0 := by omega
      have hnk' : ¬ k < rt_xi al s b r β c := by omega
      have hnb : ¬ rt_bad al s b r d k β c := fun h => by have := h.1; omega
      have hfr : (rt_sym ns rt_cPh1r st).fr = Function.update (Function.update st.fr
          ((k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c) * 16 + 6) 1)
          (((k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c) *
            al.length ^ b + rt_yi al s b r β c) * 16 + 7) 1 := by
        simp [rt_cPh1r, rt_seqs, rt_sym, rt_M, rt_A, rt_Sb, rt_eff, rt_setN, rt_ldRes, rt_skip,
          rt_L, rt_stRes, h20, h21, h23, h26, h27, hC.h0, hC.h7, hC.h8, hC.h12, hC.f48, hs0, heq,
          show ∀ o : ℕ, o * 16 + 6 ≠ 48 from fun o => by omega,
          show ∀ o : ℕ, (48 : ℕ) ≠ o * 16 + 6 from fun o => by omega]
      refine ⟨rt_Reg_chg (P := fun _ => False) h4 (fun o => ?_) (fun o => by simp [S4 o, hnb]),
        rt_Reg_chg (P := fun _ => False) h5 (fun o => ?_) (fun o => by simp [S5 o, hnk']),
        rt_Reg_chg (P := fun o => o = k * ((al.length ^ (s + b)) ^ r * al.length ^ r) +
            β * al.length ^ r + c) h6 (fun o => ?_) (fun o => by simp [S6 o, heq]),
        rt_Reg_chg (P := fun o => o = (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) +
            β * al.length ^ r + c) * al.length ^ b + rt_yi al s b r β c) h7 (fun o => ?_)
            (fun o => by simp [S7 o, heq])⟩ <;>
        (clear * - hfr; rw [hfr]; simp only [Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega))
    · have hs0 : rt_xi al s b r β c - k ≠ 0 := by omega
      have hnk : rt_xi al s b r β c ≠ k := by omega
      have hnb : ¬ rt_bad al s b r d k β c := fun h => by have := h.1; omega
      have hfr : (rt_sym ns rt_cPh1r st).fr = Function.update st.fr
          ((k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c) * 16 + 5) 1 := by
        simp [rt_cPh1r, rt_seqs, rt_sym, rt_M, rt_A, rt_Sb, rt_eff, rt_setN, rt_ldRes, rt_skip,
          rt_L, rt_stRes, h20, h21, h23, h26, h27, hC.h0, hC.h7, hC.h8, hC.h12, hC.f48, hs0]
      refine ⟨rt_Reg_chg (P := fun _ => False) h4 (fun o => ?_) (fun o => by simp [S4 o, hnb]),
        rt_Reg_chg (P := fun o => o = k * ((al.length ^ (s + b)) ^ r * al.length ^ r) +
            β * al.length ^ r + c) h5 (fun o => ?_) (fun o => by simp [S5 o, hgt]),
        rt_Reg_chg (P := fun _ => False) h6 (fun o => ?_) (fun o => by simp [S6 o, hnk]),
        rt_Reg_chg (P := fun _ => False) h7 (fun o => ?_) (fun o => by simp [S7 o, hnk])⟩ <;>
        (clear * - hfr; rw [hfr]; simp only [Function.update_apply]; split_ifs <;> first | rfl | (exfalso; omega))

def rt_kPh1 (q s b r : ℕ) : ℕ :=
  (q ^ (s + b)) ^ r * (q ^ r * (rt_kPT q s b r + 50) + 10) + 10

theorem rt_Ph1_spec (al : List F) (s b r d B : ℕ) (H : rt_Hyp al s b r d B) (ns : List ℕ)
    (k : ℕ) (hk : k < al.length ^ s) :
    rt_Sp ns B rt_cPh1
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 20 = k ∧
        rt_Reg st 8 (rt_AMS al s b r d k) ∧
        rt_Regs47 al s b r d (k * ((al.length ^ (s + b)) ^ r * al.length ^ r)) st)
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 20 = k ∧
        rt_Regs47 al s b r d ((k + 1) * ((al.length ^ (s + b)) ^ r * al.length ^ r)) st)
      (rt_kPh1 al.length s b r) := by
  have hq := H.q2
  have hB := H.hB
  have hG1 := rt_Gb1 al.length s b r d (by omega)
  have hQ1B : (al.length ^ (s + b)) ^ r ≤ B := by
    have : (al.length ^ (s + b)) ^ r ≤ al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) *
        al.length ^ b := by
      calc (al.length ^ (s + b)) ^ r = 1 * ((al.length ^ (s + b)) ^ r * 1) * 1 := by ring
        _ ≤ _ := by
          gcongr
          · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
          · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
          · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hQRB : al.length ^ r ≤ B := by
    have : al.length ^ r ≤ al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) *
        al.length ^ b := by
      calc al.length ^ r = 1 * (1 * al.length ^ r) * 1 := by ring
        _ ≤ _ := by
          gcongr
          · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
          · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
          · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  let BI : ℕ → rt_St F → Prop := fun β st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 20 = k ∧
    st.nr 21 = β ∧ rt_Reg st 8 (rt_AMS al s b r d k) ∧
    rt_Regs47 al s b r d (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r) st
  let CI : ℕ → ℕ → rt_St F → Prop := fun β c st => rt_Cst al s b r d st ∧ rt_Bd B st ∧
    st.nr 20 = k ∧ st.nr 21 = β ∧ st.nr 23 = c ∧ rt_Reg st 8 (rt_AMS al s b r d k) ∧
    rt_Regs47 al s b r d (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c)
      st
  have e1 : rt_Sp ns B (rt_L 21 0)
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 20 = k ∧
        rt_Reg st 8 (rt_AMS al s b r d k) ∧
        rt_Regs47 al s b r d (k * ((al.length ^ (s + b)) ^ r * al.length ^ r)) st) (BI 0) 1 := by
    apply rt_sp_sym'
    rintro st ⟨hC, hb, h20, h8, h47⟩
    refine ⟨hb, by simp [rt_symV, rt_L, rt_wv, rt_simple], fun hb' hA => ?_⟩
    have kfr : (rt_sym ns (rt_L (F := F) 21 0) st).fr = st.fr := rfl
    obtain ⟨h4, h5, h6, h7⟩ := h47
    refine ⟨rt_Cst_agr rfl hA hC, hb', by rw [rt_nr_agr (rt_notin_of rfl) hA, h20],
      by simp [rt_sym, rt_L, rt_eff, rt_setN], rt_Reg_same h8 kfr, ?_⟩
    simp only [zero_mul, add_zero]
    exact ⟨rt_Reg_same h4 kfr, rt_Reg_same h5 kfr, rt_Reg_same h6 kfr, rt_Reg_same h7 kfr⟩
  have hbody : ∀ β, 0 ≤ β → β < (al.length ^ (s + b)) ^ r →
      rt_Sp ns B (.seq (rt_L 23 0) (.loop 23 8 rt_cPh1c)) (BI β)
        (fun s1 => rt_Bd B s1 ∧ rt_Bd B (rt_inc s1 21) ∧ BI (β + 1) (rt_inc s1 21))
        (1 + ((al.length ^ r - 0) * (rt_kPT al.length s b r + rt_len (rt_cPh1r (F := F)) + 4) + 1)) := by
    intro β _ hβ
    have f1 : rt_Sp ns B (rt_L 23 0) (BI β) (CI β 0) 1 := by
      apply rt_sp_sym'
      rintro st ⟨hC, hb, h20, h21, h8, h47⟩
      refine ⟨hb, by simp [rt_symV, rt_L, rt_wv, rt_simple], fun hb' hA => ?_⟩
      have kfr : (rt_sym ns (rt_L (F := F) 23 0) st).fr = st.fr := rfl
      obtain ⟨h4, h5, h6, h7⟩ := h47
      exact ⟨rt_Cst_agr rfl hA hC, hb', by rw [rt_nr_agr (rt_notin_of rfl) hA, h20],
        by rw [rt_nr_agr (rt_notin_of rfl) hA, h21], by simp [rt_sym, rt_L, rt_eff, rt_setN],
        rt_Reg_same h8 kfr, rt_Reg_same h4 kfr, rt_Reg_same h5 kfr, rt_Reg_same h6 kfr,
        rt_Reg_same h7 kfr⟩
    have f2 : rt_Sp ns B (.loop 23 8 rt_cPh1c) (CI β 0) (CI β (al.length ^ r))
        ((al.length ^ r - 0) * (rt_kPT al.length s b r + rt_len (rt_cPh1r (F := F)) + 4) + 1) := by
      refine rt_sp_loop (CI β) 0 _ _ (Nat.zero_le _) ?_ ?_
      · rintro c st _ _ ⟨hC, hb, -, -, h23, -⟩
        exact ⟨h23, hC.h8, hb⟩
      · intro c _ hc
        let R : rt_St F → Prop := fun st => st.nr 20 = k ∧ st.nr 21 = β ∧ st.nr 23 = c ∧
          rt_Reg st 8 (rt_AMS al s b r d k) ∧
          rt_Regs47 al s b r d (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) +
            β * al.length ^ r + c) st
        have g1 := rt_sp_frame (rt_PT_spec al s b r d B H ns β c hβ hc) (R := R) (by
          rintro st st' hA ⟨h20, h21, h23, h8, h4, h5, h6, h7⟩
          exact ⟨by rw [rt_nr_agr (rt_notin_of rfl) hA, h20], by rw [rt_nr_agr (rt_notin_of rfl) hA, h21],
            by rw [rt_nr_agr (rt_notin_of rfl) hA, h23],
            rt_Reg_agr rfl (rt_notin_of rfl) (by decide) hA h8,
            rt_Reg_agr rfl (rt_notin_of rfl) (by decide) hA h4,
            rt_Reg_agr rfl (rt_notin_of rfl) (by decide) hA h5,
            rt_Reg_agr rfl (rt_notin_of rfl) (by decide) hA h6,
            rt_Reg_agr rfl (rt_notin_of rfl) (by decide) hA h7⟩)
        have g2 := rt_Ph1r_spec al s b r d B H ns k β c hk hβ hc
        refine rt_sp_seq (rt_sp_conseq g1 ?_ (fun st h => h) le_rfl)
          (rt_sp_conseq g2 ?_ ?_ le_rfl)
        · rintro st ⟨hC, hb, h20, h21, h23, h8, h47⟩
          exact ⟨⟨hC, hb, h21, h23⟩, h20, h21, h23, h8, h47⟩
        · rintro st ⟨⟨hC, hb, h26, h27⟩, h20, h21, h23, h8, h47⟩
          exact ⟨hC, hb, h20, h21, h23, h26, h27, h8, h47⟩
        · rintro st ⟨hC, hb, h20, h21, h23, h8, h47⟩
          have hbi : rt_Bd B (rt_inc st 23) :=
            rt_Bd_inc (by decide) hb (by omega) (by rw [h23]; omega)
          have hI : ∀ x, x ≠ 23 → x ≠ 61 → (rt_inc st 23).nr x = st.nr x := by
            intro x h1 h2; rw [rt_inc_nr _ _ _ (by decide), if_neg h1, if_neg h2]
          refine ⟨hb, hbi, rt_Cst_inc (by decide) (by decide) hC, hbi,
            by rw [hI 20 (by decide) (by decide), h20], by rw [hI 21 (by decide) (by decide), h21],
            by rw [rt_inc_nr _ _ _ (by decide), if_pos rfl, h23], rt_Reg_inc h8, ?_⟩
          rw [← Nat.add_assoc]; exact h47
    refine rt_sp_conseq (rt_sp_seq f1 f2) (fun st h => h) ?_ le_rfl
    rintro st ⟨hC, hb, h20, h21, h23, h8, h47⟩
    have hbi : rt_Bd B (rt_inc st 21) := rt_Bd_inc (by decide) hb (by omega) (by rw [h21]; omega)
    have hI : ∀ x, x ≠ 21 → x ≠ 61 → (rt_inc st 21).nr x = st.nr x := by
      intro x h1 h2; rw [rt_inc_nr _ _ _ (by decide), if_neg h1, if_neg h2]
    refine ⟨hb, hbi, rt_Cst_inc (by decide) (by decide) hC, hbi,
      by rw [hI 20 (by decide) (by decide), h20], by rw [rt_inc_nr _ _ _ (by decide), if_pos rfl, h21],
      rt_Reg_inc h8, ?_⟩
    rw [show k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + (β + 1) * al.length ^ r =
      k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + al.length ^ r by ring]
    exact h47
  have e2 := rt_sp_loop (ns := ns) (B := B) (i := 21) (n := 10) BI 0 _ _ (Nat.zero_le _)
    (by rintro β st _ _ ⟨hC, hb, -, h21, -⟩; exact ⟨h21, hC.h10, hb⟩) hbody
  refine rt_sp_conseq (rt_sp_seq e1 e2) (fun st h => h) ?_ ?_
  · rintro st ⟨hC, hb, h20, -, -, h47⟩
    refine ⟨hC, hb, h20, ?_⟩
    rw [show (k + 1) * ((al.length ^ (s + b)) ^ r * al.length ^ r) =
      k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + (al.length ^ (s + b)) ^ r * al.length ^ r
      by ring]
    exact h47
  · simp only [rt_kPh1, Nat.sub_zero]
    have hl : rt_len (rt_cPh1r (F := F)) = 41 := by
      simp [rt_cPh1r, rt_seqs, rt_len, rt_M, rt_A, rt_Sb, rt_skip, rt_L]
    rw [hl]
    have h1 : al.length ^ r * (rt_kPT al.length s b r + 41 + 4) ≤
        al.length ^ r * (rt_kPT al.length s b r + 50) := Nat.mul_le_mul_left _ (by omega)
    have h2 : (al.length ^ (s + b)) ^ r * (1 + (al.length ^ r * (rt_kPT al.length s b r + 41 + 4) + 1)
        + 4) ≤ (al.length ^ (s + b)) ^ r * (al.length ^ r * (rt_kPT al.length s b r + 50) + 10) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

end Specs

end SubspaceEvasion312.Explicit.Dev.LG
end
end

section
set_option autoImplicit false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.LG
open SubspaceEvasion312.Explicit
open Classical

section Specs
variable {F : Type} [Field F] [Fintype F]

/-! ### Score: the inner pieces -/

def rt_SCf (al : List F) (s b r d k w : ℕ) (st : rt_St F) : Prop :=
  st.nr 20 = k ∧ st.nr 29 = w ∧ rt_Reg st 3 (rt_DUPS al s b r d) ∧
  rt_Regs47 al s b r d ((k + 1) * ((al.length ^ (s + b)) ^ r * al.length ^ r)) st

theorem rt_SCf_agr {al : List F} {s b r d k w : ℕ} {c : rt_Cmd F} (hok : rt_okC c = true)
    (h20 : (20 : ℕ) ∉ rt_wn c) (h29 : (29 : ℕ) ∉ rt_wn c) (hwr : rt_wr c = [])
    {st st' : rt_St F} (hA : rt_Agr c st st') (h : rt_SCf al s b r d k w st) :
    rt_SCf al s b r d k w st' := by
  obtain ⟨a20, a29, a3, a4, a5, a6, a7⟩ := h
  have hn : ∀ k' : ℕ, k' % 16 ∉ rt_wr c := by rw [hwr]; simp
  exact ⟨by rw [rt_nr_agr h20 hA, a20], by rw [rt_nr_agr h29 hA, a29],
    rt_Reg_agr hok (hn 3) (by decide) hA a3, rt_Reg_agr hok (hn 4) (by decide) hA a4,
    rt_Reg_agr hok (hn 5) (by decide) hA a5, rt_Reg_agr hok (hn 6) (by decide) hA a6,
    rt_Reg_agr hok (hn 7) (by decide) hA a7⟩

theorem rt_SCf_inc {al : List F} {s b r d k w : ℕ} {st : rt_St F} {i : ℕ} (h20 : i ≠ 20)
    (h29 : i ≠ 29) (hi : i ≠ 61) (h : rt_SCf al s b r d k w st) :
    rt_SCf al s b r d k w (rt_inc st i) := by
  obtain ⟨a20, a29, a3, a47⟩ := h
  refine ⟨?_, ?_, a3, a47⟩
  · rw [rt_inc_nr _ _ _ hi, if_neg (Ne.symm h20), if_neg (by decide), a20]
  · rw [rt_inc_nr _ _ _ hi, if_neg (Ne.symm h29), if_neg (by decide), a29]

theorem rt_rd_curw {al : List F} {s b r d k w β c w' : ℕ} {st : rt_St F}
    (h : rt_SCf al s b r d k w st) (hβ : β < (al.length ^ (s + b)) ^ r)
    (hc : c < al.length ^ r) (hw' : w' < al.length ^ b) :
    st.fr (((k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r + c) *
      al.length ^ b + w') * 16 + 7) = 1 ↔ (rt_xi al s b r β c = k ∧ w' = rt_yi al s b r β c) := by
  rw [rt_Reg_read h.2.2.2.2.2.2]
  obtain ⟨d1, d2, d3, d4⟩ := rt_ad_dm (k := k) hβ hc
  obtain ⟨e1, e2⟩ := rt_divmod (k := k * ((al.length ^ (s + b)) ^ r * al.length ^ r) +
    β * al.length ^ r + c) hw'
  simp only [rt_CURWS, rt_CURS, e1, e2, d1, d2, d3, d4, true_and]

def rt_okc (al : List F) (s b r d k w β t j : ℕ) : Prop :=
  ∀ j' < j, rt_okp al s b r d k w β (rt_ci al.length r t j')

def rt_nf (al : List F) (s b r k β t j : ℕ) : ℕ :=
  ((Finset.range j).filter (fun j' => k < rt_xi al s b r β (rt_ci al.length r t j'))).card

def rt_JI (al : List F) (s b r d B k w β t acc j : ℕ) (st : rt_St F) : Prop :=
  rt_Cst al s b r d st ∧ rt_Bd B st ∧ rt_SCf al s b r d k w st ∧ st.nr 21 = β ∧
  st.nr 22 = t ∧ st.nr 30 = acc ∧ st.nr 24 = j ∧ st.nr 25 = (al.length ^ r) ^ j ∧
  st.nr 33 = (if rt_okc al s b r d k w β t j then 1 else 0) ∧ st.nr 34 = rt_nf al s b r k β t j

def rt_JC (al : List F) (s b r d B k w β t acc j : ℕ) (st : rt_St F) : Prop :=
  rt_Cst al s b r d st ∧ rt_Bd B st ∧ rt_SCf al s b r d k w st ∧ st.nr 21 = β ∧
  st.nr 22 = t ∧ st.nr 30 = acc ∧ st.nr 24 = j ∧ st.nr 25 = (al.length ^ r) ^ (j + 1) ∧
  st.nr 23 = rt_ci al.length r t j ∧
  st.nr 28 = k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r +
    rt_ci al.length r t j

theorem rt_okc_succ {al : List F} {s b r d k w β t j : ℕ} :
    rt_okc al s b r d k w β t (j + 1) ↔
      rt_okc al s b r d k w β t j ∧ rt_okp al s b r d k w β (rt_ci al.length r t j) := by
  unfold rt_okc
  constructor
  · intro h; exact ⟨fun j' hj' => h j' (by omega), h j (by omega)⟩
  · rintro ⟨h1, h2⟩ j' hj'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | h
    · exact h1 j' h
    · subst h; exact h2

theorem rt_nf_succ {al : List F} {s b r k β t j : ℕ} :
    rt_nf al s b r k β t (j + 1) = rt_nf al s b r k β t j +
      (if k < rt_xi al s b r β (rt_ci al.length r t j) then 1 else 0) := by
  unfold rt_nf
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem rt_Scj_spec (al : List F) (s b r d B : ℕ) (H : rt_Hyp al s b r d B) (ns : List ℕ)
    (k w β t acc j : ℕ) (hk : k < al.length ^ s) (hw : w < al.length ^ b)
    (hβ : β < (al.length ^ (s + b)) ^ r) (ht : t < (al.length ^ r) ^ d) (hj : j < d) :
    rt_Sp ns B rt_cScj (rt_JI al s b r d B k w β t acc j)
      (fun s1 => rt_Bd B s1 ∧ rt_Bd B (rt_inc s1 24) ∧
        rt_JI al s b r d B k w β t acc (j + 1) (rt_inc s1 24)) (rt_len (rt_cScj (F := F))) := by
  have hq := H.q2
  have hB := H.hB
  have hG1 := rt_Gb1 al.length s b r d (by omega)
  have hG2 := rt_Gb2 al.length s b r d (by omega)
  have hQR : 0 < al.length ^ r := by positivity
  have hc : rt_ci al.length r t j < al.length ^ r := Nat.mod_lt _ hQR
  have hci : t / (al.length ^ r) ^ j % al.length ^ r = rt_ci al.length r t j := rfl
  obtain ⟨d1, d2, d3, d4⟩ := rt_ad_dm (k := k) hβ hc
  have hAD : k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r +
      rt_ci al.length r t j < al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) := by
    have : (k + 1) * ((al.length ^ (s + b)) ^ r * al.length ^ r) ≤
      al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) := Nat.mul_le_mul_right _ hk
    omega
  have hADw : (k * ((al.length ^ (s + b)) ^ r * al.length ^ r) + β * al.length ^ r +
      rt_ci al.length r t j) * al.length ^ b + w <
      al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) * al.length ^ b := by
    have h2 := Nat.mul_le_mul_right (al.length ^ b) hAD
    rw [Nat.succ_mul] at h2
    omega
  have hQ2 : (al.length ^ r) ^ (j + 1) ≤ (al.length ^ r) ^ d := Nat.pow_le_pow_right hQR hj
  have hQ2' : (al.length ^ r) ^ d ≤ (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d *
      (al.length ^ b) ^ d := by
    have : 1 ≤ (al.length ^ (s + b)) ^ r := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have : 1 ≤ (al.length ^ b) ^ d := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc (al.length ^ r) ^ d = 1 * (al.length ^ r) ^ d * 1 := by ring
      _ ≤ _ := by gcongr
  have hdq : d < (al.length ^ b) ^ d := by
    calc d < 2 ^ d := Nat.lt_two_pow_self
      _ ≤ (al.length ^ b) ^ d := Nat.pow_le_pow_left (le_trans hq (Nat.le_self_pow (by
          have := H.hb; omega) _)) _
  have hdB : d + 1 ≤ B := by
    have : (al.length ^ b) ^ d ≤ (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d *
      (al.length ^ b) ^ d := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hQAs : al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) ≤
      al.length ^ s * ((al.length ^ (s + b)) ^ r * al.length ^ r) * al.length ^ b :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have htd : t / (al.length ^ r) ^ j ≤ t := Nat.div_le_self _ _
  -- step A
  have eA : rt_Sp ns B rt_cScjA (rt_JI al s b r d B k w β t acc j)
      (fun st => rt_JC al s b r d B k w β t acc j st ∧
        st.nr 33 = (if rt_okc al s b r d k w β t j then 1 else 0) ∧
        st.nr 34 = rt_nf al s b r k β t j) (rt_len (rt_cScjA (F := F))) := by
    apply rt_sp_sym'
    rintro st ⟨hC, hb, hS, h21, h22, h30, h24, h25, h33, h34⟩
    have h20 := hS.1
    refine ⟨hb, ?_, fun hb' hA => ?_⟩
    · simp [rt_cScjA, rt_seqs, rt_symV, rt_sym, rt_D, rt_Md, rt_M, rt_A, rt_eff, rt_setN, rt_wv,
        rt_simple, h22, h25, hC.h8, h20, hC.h12, h21]
      rw [hci, ← pow_succ]
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · have key : (rt_sym ns rt_cScjA st).nr 23 = rt_ci al.length r t j ∧
          (rt_sym ns rt_cScjA st).nr 25 = (al.length ^ r) ^ (j + 1) ∧
          (rt_sym ns rt_cScjA st).nr 28 = k * ((al.length ^ (s + b)) ^ r * al.length ^ r) +
            β * al.length ^ r + rt_ci al.length r t j := by
        simp [rt_cScjA, rt_seqs, rt_sym, rt_D, rt_Md, rt_M, rt_A, rt_eff, rt_setN,
          h22, h25, hC.h8, h20, hC.h12, h21, rt_ci, pow_succ]
      obtain ⟨k23, k25, k28⟩ := key
      have hn : ∀ x, x ∉ rt_wn (rt_cScjA (F := F)) → (rt_sym ns rt_cScjA st).nr x = st.nr x :=
        fun x hx => rt_nr_agr hx hA
      refine ⟨⟨rt_Cst_agr rfl hA hC, hb', rt_SCf_agr rfl (rt_notin_of rfl) (rt_notin_of rfl) rfl
        hA hS, by rw [hn 21 (rt_notin_of rfl), h21], by rw [hn 22 (rt_notin_of rfl), h22],
        by rw [hn 30 (rt_notin_of rfl), h30], by rw [hn 24 (rt_notin_of rfl), h24], k25, k23, k28⟩,
        by rw [hn 33 (rt_notin_of rfl), h33], by rw [hn 34 (rt_notin_of rfl), h34]⟩
  -- step Bad
  have eBad : rt_Sp ns B rt_cChkBad
      (fun st => rt_JC al s b r d B k w β t acc j st ∧
        st.nr 33 = (if rt_okc al s b r d k w β t j then 1 else 0) ∧
        st.nr 34 = rt_nf al s b r k β t j)
      (fun st => rt_JC al s b r d B k w β t acc j st ∧
        st.nr 33 = (if rt_okc al s b r d k w β t j ∧
          ¬ rt_bad al s b r d k β (rt_ci al.length r t j) then 1 else 0) ∧
        st.nr 34 = rt_nf al s b r k β t j) (rt_len (rt_cChkBad (F := F))) := by
    apply rt_sp_sym'
    rintro st ⟨⟨hC, hb, hS, h21, h22, h30, h24, h25, h23, h28⟩, h33, h34⟩
    have hv : st.fr (st.nr 28 * 16 + 4) =
        if rt_bad al s b r d k β (rt_ci al.length r t j) then 1 else 0 := by
      refine rt_val01 hS.2.2.2.1 ?_
      rw [h28]; simp only [rt_BADS, d1, d2, d3, d4, true_and]
    refine ⟨hb, ?_, fun hb' hA => ?_⟩
    · simp [rt_cChkBad, rt_symV, rt_sym, rt_ldRes, rt_L, rt_skip, rt_wv, rt_simple, hv, hC.f48]
      rw [h28]; omega
    · have hn : ∀ x, x ∉ rt_wn (rt_cChkBad (F := F)) → (rt_sym ns rt_cChkBad st).nr x = st.nr x :=
        fun x hx => rt_nr_agr hx hA
      have k33 : (rt_sym ns rt_cChkBad st).nr 33 = (if rt_okc al s b r d k w β t j ∧
          ¬ rt_bad al s b r d k β (rt_ci al.length r t j) then 1 else 0) := by
        simp only [rt_cChkBad, rt_sym, rt_ldRes, rt_L, rt_skip, rt_eff, rt_setN]
        by_cases hbd : rt_bad al s b r d k β (rt_ci al.length r t j)
        · simp [hv, hbd, hC.f48]
        · simp [hv, hbd, hC.f48, h33]
      refine ⟨⟨rt_Cst_agr rfl hA hC, hb', rt_SCf_agr rfl (rt_notin_of rfl) (rt_notin_of rfl) rfl
        hA hS, by rw [hn 21 (rt_notin_of rfl), h21], by rw [hn 22 (rt_notin_of rfl), h22],
        by rw [hn 30 (rt_notin_of rfl), h30], by rw [hn 24 (rt_notin_of rfl), h24],
        by rw [hn 25 (rt_notin_of rfl), h25], by rw [hn 23 (rt_notin_of rfl), h23],
        by rw [hn 28 (rt_notin_of rfl), h28]⟩, k33, by rw [hn 34 (rt_notin_of rfl), h34]⟩
  -- step Free
  have eFree : rt_Sp ns B rt_cChkFree
      (fun st => rt_JC al s b r d B k w β t acc j st ∧
        st.nr 33 = (if rt_okc al s b r d k w β t j ∧
          ¬ rt_bad al s b r d k β (rt_ci al.length r t j) then 1 else 0) ∧
        st.nr 34 = rt_nf al s b r k β t j)
      (fun st => rt_JC al s b r d B k w β t acc j st ∧
        st.nr 33 = (if rt_okc al s b r d k w β t j ∧
          ¬ rt_bad al s b r d k β (rt_ci al.length r t j) then 1 else 0) ∧
        st.nr 34 = rt_nf al s b r k β t (j + 1)) (rt_len (rt_cChkFree (F := F))) := by
    apply rt_sp_sym'
    rintro st ⟨⟨hC, hb, hS, h21, h22, h30, h24, h25, h23, h28⟩, h33, h34⟩
    have hv : st.fr (st.nr 28 * 16 + 5) =
        if k < rt_xi al s b r β (rt_ci al.length r t j) then 1 else 0 := by
      refine rt_val01 hS.2.2.2.2.1 ?_
      rw [h28]; simp only [rt_FREES, d1, d2, d3, d4, true_and]
    have hnf : rt_nf al s b r k β t j ≤ j := by
      unfold rt_nf
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    refine ⟨hb, ?_, fun hb' hA => ?_⟩
    · simp [rt_cChkFree, rt_symV, rt_sym, rt_ldRes, rt_L, rt_A, rt_skip, rt_wv, rt_simple, hv,
        hC.f48, rt_eff, rt_setN]
      exact ⟨by rw [h28]; omega, fun _ => ⟨by omega, by rw [h34]; omega⟩⟩
    · have hn : ∀ x, x ∉ rt_wn (rt_cChkFree (F := F)) → (rt_sym ns rt_cChkFree st).nr x = st.nr x :=
        fun x hx => rt_nr_agr hx hA
      have k34 : (rt_sym ns rt_cChkFree st).nr 34 = rt_nf al s b r k β t (j + 1) := by
        rw [rt_nf_succ]
        simp only [rt_cChkFree, rt_sym, rt_ldRes, rt_L, rt_A, rt_skip, rt_eff, rt_setN]
        by_cases hf : k < rt_xi al s b r β (rt_ci al.length r t j)
        · simp [hv, hf, hC.f48, h34]
        · simp [hv, hf, hC.f48, h34]
      refine ⟨⟨rt_Cst_agr rfl hA hC, hb', rt_SCf_agr rfl (rt_notin_of rfl) (rt_notin_of rfl) rfl
        hA hS, by rw [hn 21 (rt_notin_of rfl), h21], by rw [hn 22 (rt_notin_of rfl), h22],
        by rw [hn 30 (rt_notin_of rfl), h30], by rw [hn 24 (rt_notin_of rfl), h24],
        by rw [hn 25 (rt_notin_of rfl), h25], by rw [hn 23 (rt_notin_of rfl), h23],
        by rw [hn 28 (rt_notin_of rfl), h28]⟩, by rw [hn 33 (rt_notin_of rfl), h33], k34⟩
  -- step Cur
  have eCur : rt_Sp ns B rt_cChkCur
      (fun st => rt_JC al s b r d B k w β t acc j st ∧
        st.nr 33 = (if rt_okc al s b r d k w β t j ∧
          ¬ rt_bad al s b r d k β (rt_ci al.length r t j) then 1 else 0) ∧
        st.nr 34 = rt_nf al s b r k β t (j + 1))
      (fun st => rt_JC al s b r d B k w β t acc j st ∧
        st.nr 33 = (if rt_okc al s b r d k w β t (j + 1) then 1 else 0) ∧
        st.nr 34 = rt_nf al s b r k β t (j + 1)) (rt_len (rt_cChkCur (F := F))) := by
    apply rt_sp_sym'
    rintro st ⟨⟨hC, hb, hS, h21, h22, h30, h24, h25, h23, h28⟩, h33, h34⟩
    have hv : st.fr (st.nr 28 * 16 + 6) =
        if rt_xi al s b r β (rt_ci al.length r t j) = k then 1 else 0 := by
      refine rt_val01 hS.2.2.2.2.2.1 ?_
      rw [h28]; simp only [rt_CURS, d1, d2, d3, d4, true_and]
    have hv7 : st.fr ((st.nr 28 * st.nr 7 + st.nr 29) * 16 + 7) =
        if (rt_xi al s b r β (rt_ci al.length r t j) = k ∧
          w = rt_yi al s b r β (rt_ci al.length r t j)) then 1 else 0 := by
      refine rt_val01' hS.2.2.2.2.2.2 ?_
      rw [h28, hC.h7, hS.2.1]
      exact rt_rd_curw hS hβ hc hw
    have hne7 : ∀ x : ℕ, x * 16 + 7 ≠ 64 := by intro x; omega
    refine ⟨hb, ?_, fun hb' hA => ?_⟩
    · simp [rt_cChkCur, rt_seqs, rt_symV, rt_sym, rt_ldRes, rt_L, rt_A, rt_M, rt_skip, rt_wv,
        rt_simple, hv, hC.f48, rt_eff, rt_setN, hne7]
      exact ⟨by rw [h28]; omega, fun _ => by
        rw [h28, hC.h7, hS.2.1]; exact ⟨by omega, by omega, by omega⟩⟩
    · have hn : ∀ x, x ∉ rt_wn (rt_cChkCur (F := F)) → (rt_sym ns rt_cChkCur st).nr x = st.nr x :=
        fun x hx => rt_nr_agr hx hA
      have k33 : (rt_sym ns rt_cChkCur st).nr 33 =
          (if rt_okc al s b r d k w β t (j + 1) then 1 else 0) := by
        rw [rt_okc_succ]
        simp only [rt_cChkCur, rt_seqs, rt_sym, rt_ldRes, rt_L, rt_A, rt_M, rt_skip, rt_eff,
          rt_setN]
        by_cases hcur : rt_xi al s b r β (rt_ci al.length r t j) = k
        · by_cases hy : w = rt_yi al s b r β (rt_ci al.length r t j)
          · simp [hv, hv7, hcur, hy, hC.f48, h33, hne7, rt_okp]
          · simp [hv, hv7, hcur, hy, hC.f48, h33, hne7, rt_okp, Ne.symm hy]
        · simp [hv, hcur, hC.f48, h33, rt_okp]
      refine ⟨⟨rt_Cst_agr rfl hA hC, hb', rt_SCf_agr rfl (rt_notin_of rfl) (rt_notin_of rfl) rfl
        hA hS, by rw [hn 21 (rt_notin_of rfl), h21], by rw [hn 22 (rt_notin_of rfl), h22],
        by rw [hn 30 (rt_notin_of rfl), h30], by rw [hn 24 (rt_notin_of rfl), h24],
        by rw [hn 25 (rt_notin_of rfl), h25], by rw [hn 23 (rt_notin_of rfl), h23],
        by rw [hn 28 (rt_notin_of rfl), h28]⟩, k33, by rw [hn 34 (rt_notin_of rfl), h34]⟩
  have hall := rt_sp_seq eA (rt_sp_seq eBad (rt_sp_seq eFree eCur))
  refine rt_sp_conseq hall (fun st h => h) ?_ (by simp [rt_cScj, rt_len])
  rintro st ⟨⟨hC, hb, hS, h21, h22, h30, h24, h25, h23, h28⟩, h33, h34⟩
  have hbi : rt_Bd B (rt_inc st 24) := rt_Bd_inc (by decide) hb (by omega) (by rw [h24]; omega)
  have hI : ∀ x, x ≠ 24 → x ≠ 61 → (rt_inc st 24).nr x = st.nr x := by
    intro x h1 h2; rw [rt_inc_nr _ _ _ (by decide), if_neg h1, if_neg h2]
  refine ⟨hb, hbi, rt_Cst_inc (by decide) (by decide) hC, hbi,
    rt_SCf_inc (by decide) (by decide) (by decide) hS, by rw [hI 21 (by decide) (by decide), h21],
    by rw [hI 22 (by decide) (by decide), h22], by rw [hI 30 (by decide) (by decide), h30],
    by rw [rt_inc_nr _ _ _ (by decide), if_pos rfl, h24], by rw [hI 25 (by decide) (by decide), h25],
    by rw [hI 33 (by decide) (by decide), h33], by rw [hI 34 (by decide) (by decide), h34]⟩

/-- Common frame of the score loops. -/
def rt_TB (al : List F) (s b r d B k w β t acc : ℕ) (st : rt_St F) : Prop :=
  rt_Cst al s b r d st ∧ rt_Bd B st ∧ rt_SCf al s b r d k w st ∧ st.nr 21 = β ∧
  st.nr 22 = t ∧ st.nr 30 = acc

theorem rt_ScAdd_spec (al : List F) (s b r d B : ℕ) (H : rt_Hyp al s b r d B) (ns : List ℕ)
    (k w β t acc u : ℕ) (hu : u ≤ d) (hacc : acc + (al.length ^ b) ^ d ≤ B) :
    rt_Sp ns B rt_cScAdd
      (fun st => rt_TB al s b r d B k w β t acc st ∧ st.nr 34 = u)
      (fun st => rt_TB al s b r d B k w β t (acc + (al.length ^ b) ^ (d - u)) st)
      (5 * d + 5) := by
  have hq := H.q2
  have hQB : 0 < al.length ^ b := by positivity
  have hpow : ∀ e, e ≤ d → (al.length ^ b) ^ e ≤ (al.length ^ b) ^ d :=
    fun e he => Nat.pow_le_pow_right hQB he
  have hdB : d + 1 ≤ B := by
    have : d < (al.length ^ b) ^ d := lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_left (le_trans hq (Nat.le_self_pow (by have := H.hb; omega) _)) _)
    omega
  let I : ℕ → rt_St F → Prop := fun e st => rt_TB al s b r d B k w β t acc st ∧
    st.nr 35 = e ∧ st.nr 36 = (al.length ^ b) ^ (e - u)
  have e1 : rt_Sp ns B (rt_seqs [rt_L 36 1, rt_A 35 34 0])
      (fun st => rt_TB al s b r d B k w β t acc st ∧ st.nr 34 = u) (I u) 2 := by
    apply rt_sp_sym'
    rintro st ⟨⟨hC, hb, hS, h21, h22, h30⟩, h34⟩
    refine ⟨hb, by simp [rt_seqs, rt_symV, rt_sym, rt_L, rt_A, rt_eff, rt_setN, rt_wv, rt_simple,
      h34, hC.h0]; omega, fun hb' hA => ?_⟩
    have hn : ∀ x, x ∉ rt_wn (rt_seqs [rt_L (F := F) 36 1, rt_A 35 34 0]) →
        (rt_sym ns (rt_seqs [rt_L 36 1, rt_A 35 34 0]) st).nr x = st.nr x :=
      fun x hx => rt_nr_agr hx hA
    refine ⟨⟨rt_Cst_agr rfl hA hC, hb', rt_SCf_agr rfl (rt_notin_of rfl) (rt_notin_of rfl) rfl
      hA hS, by rw [hn 21 (rt_notin_of rfl), h21], by rw [hn 22 (rt_notin_of rfl), h22],
      by rw [hn 30 (rt_notin_of rfl), h30]⟩, ?_, ?_⟩
    · simp [rt_seqs, rt_sym, rt_L, rt_A, rt_eff, rt_setN, h34, hC.h0]
    · simp [rt_seqs, rt_sym, rt_L, rt_A, rt_eff, rt_setN]
  have e2 : rt_Sp ns B (.loop 35 5 (rt_M 36 36 7)) (I u) (I d) ((d - u) * (1 + 4) + 1) := by
    refine rt_sp_loop I u d 1 hu ?_ ?_
    · rintro e st _ _ ⟨⟨hC, hb, -⟩, h35, -⟩
      exact ⟨h35, hC.h5, hb⟩
    · intro e hue hed
      apply rt_sp_sym'
      rintro st ⟨⟨hC, hb, hS, h21, h22, h30⟩, h35, h36⟩
      have hp : (al.length ^ b) ^ (e - u) * al.length ^ b = (al.length ^ b) ^ (e + 1 - u) := by
        rw [show e + 1 - u = (e - u) + 1 by omega, pow_succ]
      have hpb : (al.length ^ b) ^ (e + 1 - u) ≤ B := le_trans (hpow _ (by omega)) (by omega)
      refine ⟨hb, by simp [rt_symV, rt_M, rt_wv, rt_simple, h36, hC.h7]; rw [hp]; exact hpb,
        fun hb' hA => ?_⟩
      have hn : ∀ x, x ∉ rt_wn (rt_M (F := F) 36 36 7) →
          (rt_sym ns (rt_M 36 36 7) st).nr x = st.nr x := fun x hx => rt_nr_agr hx hA
      have k36 : (rt_sym ns (rt_M (F := F) 36 36 7) st).nr 36 = (al.length ^ b) ^ (e + 1 - u) := by
        simp [rt_sym, rt_M, rt_eff, rt_setN, h36, hC.h7]; rw [hp]
      have hbi : rt_Bd B (rt_inc (rt_sym ns (rt_M 36 36 7) st) 35) :=
        rt_Bd_inc (by decide) hb' (by omega) (by rw [hn 35 (rt_notin_of rfl), h35]; omega)
      have hI : ∀ x, x ≠ 35 → x ≠ 61 → (rt_inc (rt_sym ns (rt_M (F := F) 36 36 7) st) 35).nr x =
          (rt_sym ns (rt_M 36 36 7) st).nr x := by
        intro x h1 h2; rw [rt_inc_nr _ _ _ (by decide), if_neg h1, if_neg h2]
      refine ⟨hb', hbi, ⟨rt_Cst_inc (by decide) (by decide) (rt_Cst_agr rfl hA hC), hbi,
        rt_SCf_inc (by decide) (by decide) (by decide)
          (rt_SCf_agr rfl (rt_notin_of rfl) (rt_notin_of rfl) rfl hA hS),
        by rw [hI 21 (by decide) (by decide), hn 21 (rt_notin_of rfl), h21],
        by rw [hI 22 (by decide) (by decide), hn 22 (rt_notin_of rfl), h22],
        by rw [hI 30 (by decide) (by decide), hn 30 (rt_notin_of rfl), h30]⟩,
        by rw [rt_inc_nr _ _ _ (by decide), if_pos rfl, hn 35 (rt_notin_of rfl), h35],
        by rw [hI 36 (by decide) (by decide), k36]⟩
  have e3 : rt_Sp ns B (rt_A 30 30 36) (I d)
      (fun st => rt_TB al s b r d B k w β t (acc + (al.length ^ b) ^ (d - u)) st) 1 := by
    apply rt_sp_sym'
    rintro st ⟨⟨hC, hb, hS, h21, h22, h30⟩, h35, h36⟩
    have hp := hpow (d - u) (by omega)
    refine ⟨hb, (by simp [rt_symV, rt_A, rt_wv, rt_simple, h30, h36]; omega), fun hb' hA => ?_⟩
    have hn : ∀ x, x ∉ rt_wn (rt_A (F := F) 30 30 36) →
        (rt_sym ns (rt_A 30 30 36) st).nr x = st.nr x := fun x hx => rt_nr_agr hx hA
    exact ⟨rt_Cst_agr rfl hA hC, hb', rt_SCf_agr rfl (rt_notin_of rfl) (rt_notin_of rfl) rfl hA hS,
      by rw [hn 21 (rt_notin_of rfl), h21], by rw [hn 22 (rt_notin_of rfl), h22],
      by simp [rt_sym, rt_A, rt_eff, rt_setN, h30, h36]⟩
  refine rt_sp_conseq (rt_sp_seq e1 (rt_sp_seq e2 e3)) (fun st h => h) (fun st h => h) ?_
  have : (d - u) * (1 + 4) ≤ 5 * d := by
    have := Nat.mul_le_mul_right 5 (Nat.sub_le d u); omega
  omega

theorem rt_ScEv_spec (al : List F) (s b r d B : ℕ) (H : rt_Hyp al s b r d B) (ns : List ℕ)
    (k w β t acc : ℕ) (hk : k < al.length ^ s) (hw : w < al.length ^ b)
    (hβ : β < (al.length ^ (s + b)) ^ r) (ht : t < (al.length ^ r) ^ d)
    (hacc : acc + (al.length ^ b) ^ d ≤ B) :
    rt_Sp ns B rt_cScEv (rt_TB al s b r d B k w β t acc)
      (fun st => rt_TB al s b r d B k w β t (acc +
        if rt_okc al s b r d k w β t d then
          (al.length ^ b) ^ (d - rt_nf al s b r k β t d) else 0) st)
      (54 * d + 20) := by
  have hq := H.q2
  have hB1 : 1 ≤ B := by
    have : 1 ≤ (al.length ^ b) ^ d := Nat.one_le_pow _ _ (by positivity)
    omega
  have e1 : rt_Sp ns B (rt_seqs [rt_L 33 1, rt_L 34 0, rt_L 25 1, rt_L 24 0])
      (rt_TB al s b r d B k w β t acc) (rt_JI al s b r d B k w β t acc 0) 4 := by
    apply rt_sp_sym'
    rintro st ⟨hC, hb, hS, h21, h22, h30⟩
    refine ⟨hb, (by simp [rt_seqs, rt_symV, rt_sym, rt_L, rt_eff, rt_setN, rt_wv, rt_simple]; omega),
      fun hb' hA => ?_⟩
    have hn : ∀ x, x ∉ rt_wn (rt_seqs [rt_L (F := F) 33 1, rt_L 34 0, rt_L 25 1, rt_L 24 0]) →
        (rt_sym ns (rt_seqs [rt_L 33 1, rt_L 34 0, rt_L 25 1, rt_L 24 0]) st).nr x = st.nr x :=
      fun x hx => rt_nr_agr hx hA
    refine ⟨rt_Cst_agr rfl hA hC, hb', rt_SCf_agr rfl (rt_notin_of rfl) (rt_notin_of rfl) rfl
      hA hS, by rw [hn 21 (rt_notin_of rfl), h21], by rw [hn 22 (rt_notin_of rfl), h22],
      by rw [hn 30 (rt_notin_of rfl), h30], ?_, ?_, ?_, ?_⟩ <;>
      simp [rt_seqs, rt_sym, rt_L, rt_eff, rt_setN, rt_okc, rt_nf]
  have e2 : rt_Sp ns B (.loop 24 5 rt_cScj) (rt_JI al s b r d B k w β t acc 0)
      (rt_JI al s b r d B k w β t acc d) ((d - 0) * (rt_len (rt_cScj (F := F)) + 4) + 1) := by
    refine rt_sp_loop _ 0 d _ (Nat.zero_le _) ?_ ?_
    · rintro j st _ _ ⟨hC, hb, -, -, -, -, h24, -⟩
      exact ⟨h24, hC.h5, hb⟩
    · intro j _ hj
      exact rt_Scj_spec al s b r d B H ns k w β t acc j hk hw hβ ht hj
  have e3 : rt_Sp ns B (.seq (rt_L 37 1) (.ifN 33 37 rt_cScAdd rt_skip))
      (rt_JI al s b r d B k w β t acc d)
      (fun st => rt_TB al s b r d B k w β t (acc +
        if rt_okc al s b r d k w β t d then
          (al.length ^ b) ^ (d - rt_nf al s b r k β t d) else 0) st) (5 * d + 8) := by
    have hnf : rt_nf al s b r k β t d ≤ d := by
      unfold rt_nf; exact le_trans (Finset.card_filter_le _ _) (by simp)
    refine rt_sp_conseq (rt_sp_seq (N1 := 1)
      (R := fun st => rt_JI al s b r d B k w β t acc d st ∧ st.nr 37 = 1) ?_
      (rt_sp_ifN (N1 := 5 * d + 5) (N2 := 1) ?_ ?_ ?_)) (fun st h => h) (fun st h => h) (by omega)
    · apply rt_sp_sym'
      rintro st ⟨hC, hb, hS, h21, h22, h30, h24, h25, h33, h34⟩
      refine ⟨hb, by simp [rt_symV, rt_L, rt_wv, rt_simple]; omega, fun hb' hA => ?_⟩
      have hn : ∀ x, x ∉ rt_wn (rt_L (F := F) 37 1) → (rt_sym ns (rt_L 37 1) st).nr x = st.nr x :=
        fun x hx => rt_nr_agr hx hA
      exact ⟨⟨rt_Cst_agr rfl hA hC, hb', rt_SCf_agr rfl (rt_notin_of rfl) (rt_notin_of rfl) rfl
        hA hS, by rw [hn 21 (rt_notin_of rfl), h21], by rw [hn 22 (rt_notin_of rfl), h22],
        by rw [hn 30 (rt_notin_of rfl), h30], by rw [hn 24 (rt_notin_of rfl), h24],
        by rw [hn 25 (rt_notin_of rfl), h25], by rw [hn 33 (rt_notin_of rfl), h33],
        by rw [hn 34 (rt_notin_of rfl), h34]⟩, by simp [rt_sym, rt_L, rt_eff, rt_setN]⟩
    · exact fun st h => h.1.2.1
    · by_cases hok : rt_okc al s b r d k w β t d
      · have := rt_ScAdd_spec al s b r d B H ns k w β t acc (rt_nf al s b r k β t d) hnf hacc
        refine rt_sp_conseq this ?_ ?_ le_rfl
        · rintro st ⟨⟨⟨hC, hb, hS, h21, h22, h30, h24, h25, h33, h34⟩, h37⟩, he⟩
          exact ⟨⟨hC, hb, hS, h21, h22, h30⟩, h34⟩
        · intro st h
          exact ⟨by rw [if_pos hok]; exact h, h.2.1⟩
      · intro st ⟨⟨⟨_, _, _, _, _, _, _, _, h33, _⟩, h37⟩, he⟩
        rw [if_neg hok] at h33; omega
    · apply rt_sp_sym'
      rintro st ⟨⟨⟨hC, hb, hS, h21, h22, h30, h24, h25, h33, h34⟩, h37⟩, he⟩
      have hok : ¬ rt_okc al s b r d k w β t d := by
        intro hok; rw [if_pos hok] at h33; exact he (by rw [h33, h37])
      refine ⟨hb, by simp [rt_symV, rt_skip, rt_L, rt_wv, rt_simple], fun hb' hA => ?_⟩
      have hn : ∀ x, x ∉ rt_wn (rt_skip (F := F)) → (rt_sym ns rt_skip st).nr x = st.nr x :=
        fun x hx => rt_nr_agr hx hA
      rw [if_neg hok, Nat.add_zero]
      exact ⟨rt_Cst_agr rfl hA hC, hb', rt_SCf_agr rfl (rt_notin_of rfl) (rt_notin_of rfl) rfl
        hA hS, by rw [hn 21 (rt_notin_of rfl), h21], by rw [hn 22 (rt_notin_of rfl), h22],
        by rw [hn 30 (rt_notin_of rfl), h30]⟩
  have := rt_sp_seq e1 (rt_sp_seq e2 e3)
  refine rt_sp_conseq this (fun st h => h) (fun st h => h) ?_
  simp only [Nat.sub_zero, rt_len, rt_cScj, rt_cScjA, rt_cChkBad, rt_cChkFree, rt_cChkCur,
    rt_seqs, rt_skip, rt_D, rt_Md, rt_M, rt_A, rt_L]
  omega

theorem rt_term_le (al : List F) (s b r d k w β t : ℕ) (hq : 1 ≤ al.length) :
    rt_term al s b r d k w β t ≤ (al.length ^ b) ^ d := by
  unfold rt_term
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.pow_le_pow_right (by positivity) (Nat.sub_le _ _)
  · exact Nat.zero_le _

theorem rt_Sct_spec (al : List F) (s b r d B : ℕ) (H : rt_Hyp al s b r d B) (ns : List ℕ)
    (k w β t acc : ℕ) (hk : k < al.length ^ s) (hw : w < al.length ^ b)
    (hβ : β < (al.length ^ (s + b)) ^ r) (ht : t < (al.length ^ r) ^ d)
    (hacc : acc + (al.length ^ b) ^ d ≤ B) :
    rt_Sp ns B rt_cSct (rt_TB al s b r d B k w β t acc)
      (rt_TB al s b r d B k w β t (acc + rt_term al s b r d k w β t)) (54 * d + 30) := by
  have hq := H.q2
  have hG2 := rt_Gb2 al.length s b r d (by omega)
  have hB := H.hB
  have hEV : β * (al.length ^ r) ^ d + t < (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d := by
    have : (β + 1) * (al.length ^ r) ^ d ≤ (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d :=
      Nat.mul_le_mul_right _ hβ
    rw [Nat.succ_mul] at this; omega
  have hEVG : (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d ≤
      (al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d * (al.length ^ b) ^ d :=
    Nat.le_mul_of_pos_right _ (by positivity)
  let P1 : rt_St F → Prop := fun st => rt_TB al s b r d B k w β t acc st ∧
    (st.fr 64 = 1 ↔ rt_dupP al s b r d (β * (al.length ^ r) ^ d + t) d)
  have e1 : rt_Sp ns B (rt_seqs [rt_M 39 21 11, rt_A 39 39 22, .ldR 64 3 39])
      (rt_TB al s b r d B k w β t acc) P1 7 := by
    apply rt_sp_sym'
    rintro st ⟨hC, hb, hS, h21, h22, h30⟩
    refine ⟨hb, ?_, fun hb' hA => ?_⟩
    · simp [rt_seqs, rt_symV, rt_sym, rt_M, rt_A, rt_eff, rt_setN, rt_wv, rt_simple, h21, h22,
        hC.h11]
      refine ⟨by omega, by omega, by omega⟩
    · have hn : ∀ x, x ∉ rt_wn (rt_seqs [rt_M (F := F) 39 21 11, rt_A 39 39 22, .ldR 64 3 39]) →
          (rt_sym ns (rt_seqs [rt_M 39 21 11, rt_A 39 39 22, .ldR 64 3 39]) st).nr x = st.nr x :=
        fun x hx => rt_nr_agr hx hA
      refine ⟨⟨rt_Cst_agr rfl hA hC, hb', rt_SCf_agr rfl (rt_notin_of rfl) (rt_notin_of rfl) rfl
        hA hS, by rw [hn 21 (rt_notin_of rfl), h21], by rw [hn 22 (rt_notin_of rfl), h22],
        by rw [hn 30 (rt_notin_of rfl), h30]⟩, ?_⟩
      have k64 : (rt_sym ns (rt_seqs [rt_M (F := F) 39 21 11, rt_A 39 39 22, .ldR 64 3 39]) st).fr 64
          = st.fr ((β * (al.length ^ r) ^ d + t) * 16 + 3) := by
        simp [rt_seqs, rt_sym, rt_M, rt_A, rt_eff, rt_setN, rt_ldRes, h21, h22, hC.h11]
      rw [k64, rt_Reg_read hS.2.2.1]
      simp only [rt_DUPS, hEV, true_and]
  have e2 : rt_Sp ns B (.ifF 64 48 rt_skip rt_cScEv) P1
      (rt_TB al s b r d B k w β t (acc + rt_term al s b r d k w β t)) (max 1 (54 * d + 20) + 2) := by
    by_cases hd : rt_dupP al s b r d (β * (al.length ^ r) ^ d + t) d
    · have hT : rt_term al s b r d k w β t = 0 := by unfold rt_term; rw [if_pos hd]
      refine rt_sp_ifF ?_ ?_ ?_
      · exact fun st h => h.1.2.1
      · apply rt_sp_sym'
        rintro st ⟨⟨⟨hC, hb, hS, h21, h22, h30⟩, hdup⟩, he⟩
        refine ⟨hb, by simp [rt_symV, rt_skip, rt_L, rt_wv, rt_simple], fun hb' hA => ?_⟩
        have hn : ∀ x, x ∉ rt_wn (rt_skip (F := F)) → (rt_sym ns rt_skip st).nr x = st.nr x :=
          fun x hx => rt_nr_agr hx hA
        rw [hT, Nat.add_zero]
        exact ⟨⟨rt_Cst_agr rfl hA hC, hb', rt_SCf_agr rfl (rt_notin_of rfl) (rt_notin_of rfl) rfl
          hA hS, by rw [hn 21 (rt_notin_of rfl), h21], by rw [hn 22 (rt_notin_of rfl), h22],
          by rw [hn 30 (rt_notin_of rfl), h30]⟩, hb'⟩
      · rintro st ⟨⟨⟨hC, -⟩, hdup⟩, he⟩
        exact absurd (by rw [hC.f48]; exact hdup.mpr hd) he
    · have hT : rt_term al s b r d k w β t = if rt_okc al s b r d k w β t d then
          (al.length ^ b) ^ (d - rt_nf al s b r k β t d) else 0 := by
        unfold rt_term; rw [if_neg hd]
        by_cases h : rt_okc al s b r d k w β t d
        · rw [if_pos h, if_pos (show ∀ j < d, rt_okp al s b r d k w β (rt_ci al.length r t j)
            from h)]; rfl
        · rw [if_neg h, if_neg (show ¬ ∀ j < d, rt_okp al s b r d k w β (rt_ci al.length r t j)
            from h)]
      refine rt_sp_ifF ?_ ?_ ?_
      · exact fun st h => h.1.2.1
      · rintro st ⟨⟨⟨hC, -⟩, hdup⟩, he⟩
        exact absurd (hdup.mp (by rw [he, hC.f48])) hd
      · have := rt_ScEv_spec al s b r d B H ns k w β t acc hk hw hβ ht hacc
        refine rt_sp_conseq this ?_ ?_ le_rfl
        · rintro st ⟨⟨hT, -⟩, -⟩; exact hT
        · intro st h; rw [hT]; exact h
  refine rt_sp_conseq (rt_sp_seq e1 e2) (fun st h => h) (fun st h => h) ?_
  omega

def rt_kSc (q s b r d : ℕ) : ℕ :=
  (q ^ (s + b)) ^ r * ((q ^ r) ^ d * (54 * d + 40) + 10) + 10

def rt_Spart (al : List F) (s b r d k w β : ℕ) : ℕ :=
  ∑ β' ∈ Finset.range β, ∑ t ∈ Finset.range ((al.length ^ r) ^ d), rt_term al s b r d k w β' t

theorem rt_Score_spec (al : List F) (s b r d B : ℕ) (H : rt_Hyp al s b r d B) (ns : List ℕ)
    (k w : ℕ) (hk : k < al.length ^ s) (hw : w < al.length ^ b) :
    rt_Sp ns B rt_cScore
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 20 = k ∧ st.nr 29 = w ∧
        rt_Reg st 3 (rt_DUPS al s b r d) ∧
        rt_Regs47 al s b r d ((k + 1) * ((al.length ^ (s + b)) ^ r * al.length ^ r)) st)
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 30 = rt_Sc al s b r d k w)
      (rt_kSc al.length s b r d) := by
  have hq := H.q2
  have hG2 := rt_Gb2 al.length s b r d (by omega)
  have hB := H.hB
  have hGpos := rt_G_pos al.length s b r d (by omega)
  set Q1 := (al.length ^ (s + b)) ^ r with hQ1
  set Q2 := (al.length ^ r) ^ d with hQ2
  set M := (al.length ^ b) ^ d with hM
  have hQ1B : Q1 ≤ B := by
    have : Q1 ≤ Q1 * Q2 * M := by
      have : 1 ≤ Q2 * M := Nat.one_le_iff_ne_zero.mpr (by positivity)
      calc Q1 = Q1 * 1 := by ring
        _ ≤ Q1 * (Q2 * M) := Nat.mul_le_mul_left _ this
        _ = Q1 * Q2 * M := by ring
    omega
  have hQ2B : Q2 ≤ B := by
    have : Q2 ≤ Q1 * Q2 * M := by
      have : 1 ≤ Q1 * M := Nat.one_le_iff_ne_zero.mpr (by positivity)
      calc Q2 = 1 * Q2 := by ring
        _ ≤ (Q1 * M) * Q2 := Nat.mul_le_mul_right _ this
        _ = Q1 * Q2 * M := by ring
    omega
  have hsum : ∀ β t, β < Q1 → t < Q2 →
      rt_Spart al s b r d k w β + (∑ t' ∈ Finset.range t, rt_term al s b r d k w β t') + M ≤ B := by
    intro β t hβ ht
    have h1 : rt_Spart al s b r d k w β ≤ β * (Q2 * M) := by
      unfold rt_Spart
      calc _ ≤ ∑ β' ∈ Finset.range β, Q2 * M := Finset.sum_le_sum (fun β' _ => by
            calc _ ≤ ∑ t ∈ Finset.range Q2, M :=
                  Finset.sum_le_sum (fun t _ => rt_term_le al s b r d k w β' t (by omega))
              _ = Q2 * M := by simp)
        _ = β * (Q2 * M) := by simp
    have h2 : ∑ t' ∈ Finset.range t, rt_term al s b r d k w β t' ≤ t * M := by
      calc _ ≤ ∑ t' ∈ Finset.range t, M :=
            Finset.sum_le_sum (fun t _ => rt_term_le al s b r d k w β t (by omega))
        _ = t * M := by simp
    have h3 : (β * Q2 + t + 1) * M ≤ Q1 * Q2 * M := by
      apply Nat.mul_le_mul_right
      have : (β + 1) * Q2 ≤ Q1 * Q2 := Nat.mul_le_mul_right _ hβ
      rw [Nat.succ_mul] at this; omega
    have h4 : (β * Q2 + t + 1) * M = β * (Q2 * M) + t * M + M := by ring
    omega
  let BI : ℕ → rt_St F → Prop := fun β st => rt_Cst al s b r d st ∧ rt_Bd B st ∧
    rt_SCf al s b r d k w st ∧ st.nr 21 = β ∧ st.nr 30 = rt_Spart al s b r d k w β
  let TI : ℕ → ℕ → rt_St F → Prop := fun β t st => rt_TB al s b r d B k w β t
    (rt_Spart al s b r d k w β + ∑ t' ∈ Finset.range t, rt_term al s b r d k w β t') st
  have e1 : rt_Sp ns B (rt_seqs [rt_L 30 0, rt_L 21 0])
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 20 = k ∧ st.nr 29 = w ∧
        rt_Reg st 3 (rt_DUPS al s b r d) ∧
        rt_Regs47 al s b r d ((k + 1) * ((al.length ^ (s + b)) ^ r * al.length ^ r)) st)
      (BI 0) 2 := by
    apply rt_sp_sym'
    rintro st ⟨hC, hb, h20, h29, h3, h47⟩
    refine ⟨hb, by simp [rt_seqs, rt_symV, rt_sym, rt_L, rt_wv, rt_simple], fun hb' hA => ?_⟩
    refine ⟨rt_Cst_agr rfl hA hC, hb', rt_SCf_agr rfl (rt_notin_of rfl) (rt_notin_of rfl) rfl hA
      ⟨h20, h29, h3, h47⟩, ?_, ?_⟩ <;> simp [rt_seqs, rt_sym, rt_L, rt_eff, rt_setN, rt_Spart]
  have hbody : ∀ β, 0 ≤ β → β < Q1 →
      rt_Sp ns B (.seq (rt_L 22 0) (.loop 22 11 rt_cSct)) (BI β)
        (fun s1 => rt_Bd B s1 ∧ rt_Bd B (rt_inc s1 21) ∧ BI (β + 1) (rt_inc s1 21))
        (1 + ((Q2 - 0) * (54 * d + 30 + 4) + 1)) := by
    intro β _ hβ
    have f1 : rt_Sp ns B (rt_L 22 0) (BI β) (TI β 0) 1 := by
      apply rt_sp_sym'
      rintro st ⟨hC, hb, hS, h21, h30⟩
      refine ⟨hb, by simp [rt_symV, rt_L, rt_wv, rt_simple], fun hb' hA => ?_⟩
      have hn : ∀ x, x ∉ rt_wn (rt_L (F := F) 22 0) → (rt_sym ns (rt_L 22 0) st).nr x = st.nr x :=
        fun x hx => rt_nr_agr hx hA
      exact ⟨rt_Cst_agr rfl hA hC, hb', rt_SCf_agr rfl (rt_notin_of rfl) (rt_notin_of rfl) rfl hA hS,
        by rw [hn 21 (rt_notin_of rfl), h21], by simp [rt_sym, rt_L, rt_eff, rt_setN],
        by rw [hn 30 (rt_notin_of rfl), h30]; simp⟩
    have f2 : rt_Sp ns B (.loop 22 11 rt_cSct) (TI β 0) (TI β Q2) ((Q2 - 0) * (54 * d + 30 + 4) + 1) := by
      refine rt_sp_loop (TI β) 0 Q2 _ (Nat.zero_le _) ?_ ?_
      · rintro t st _ _ ⟨hC, hb, -, -, h22, -⟩
        exact ⟨h22, hC.h11, hb⟩
      · intro t _ ht
        have := rt_Sct_spec al s b r d B H ns k w β t _ hk hw hβ ht (hsum β t hβ ht)
        refine rt_sp_conseq this (fun st h => h) ?_ le_rfl
        rintro st ⟨hC, hb, hS, h21, h22, h30⟩
        have hbi : rt_Bd B (rt_inc st 22) := rt_Bd_inc (by decide) hb (by omega) (by rw [h22]; omega)
        have hI : ∀ x, x ≠ 22 → x ≠ 61 → (rt_inc st 22).nr x = st.nr x := by
          intro x h1 h2; rw [rt_inc_nr _ _ _ (by decide), if_neg h1, if_neg h2]
        refine ⟨hb, hbi, rt_Cst_inc (by decide) (by decide) hC, hbi,
          rt_SCf_inc (by decide) (by decide) (by decide) hS,
          by rw [hI 21 (by decide) (by decide), h21],
          by rw [rt_inc_nr _ _ _ (by decide), if_pos rfl, h22],
          by rw [hI 30 (by decide) (by decide), h30, Finset.sum_range_succ, add_assoc]⟩
    refine rt_sp_conseq (rt_sp_seq f1 f2) (fun st h => h) ?_ le_rfl
    rintro st ⟨hC, hb, hS, h21, h22, h30⟩
    have hbi : rt_Bd B (rt_inc st 21) := rt_Bd_inc (by decide) hb (by omega) (by rw [h21]; omega)
    have hI : ∀ x, x ≠ 21 → x ≠ 61 → (rt_inc st 21).nr x = st.nr x := by
      intro x h1 h2; rw [rt_inc_nr _ _ _ (by decide), if_neg h1, if_neg h2]
    refine ⟨hb, hbi, rt_Cst_inc (by decide) (by decide) hC, hbi,
      rt_SCf_inc (by decide) (by decide) (by decide) hS,
      by rw [rt_inc_nr _ _ _ (by decide), if_pos rfl, h21],
      by rw [hI 30 (by decide) (by decide), h30]; unfold rt_Spart; rw [Finset.sum_range_succ]⟩
  have e2 := rt_sp_loop (ns := ns) (B := B) (i := 21) (n := 10) BI 0 Q1 _ (Nat.zero_le _)
    (by rintro β st _ _ ⟨hC, hb, -, h21, -⟩; exact ⟨h21, hC.h10, hb⟩) hbody
  refine rt_sp_conseq (rt_sp_seq e1 e2) (fun st h => h) ?_ ?_
  · rintro st ⟨hC, hb, -, -, h30⟩
    exact ⟨hC, hb, by rw [h30]; rfl⟩
  · simp only [rt_kSc, Nat.sub_zero]
    rw [← hQ1, ← hQ2]
    have h1 : Q2 * (54 * d + 30 + 4) ≤ Q2 * (54 * d + 40) := Nat.mul_le_mul_left _ (by omega)
    have h2 : Q1 * (1 + (Q2 * (54 * d + 30 + 4) + 1) + 4) ≤ Q1 * (Q2 * (54 * d + 40) + 10) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

def rt_kCh (q s b r d : ℕ) : ℕ := (q ^ b + 1) * (rt_kSc q s b r d + 10) + 10

theorem rt_Choose_spec (al : List F) (s b r d B : ℕ) (H : rt_Hyp al s b r d B) (ns : List ℕ)
    (k : ℕ) (hk : k < al.length ^ s) :
    rt_Sp ns B rt_cChoose
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 20 = k ∧
        rt_Reg st 3 (rt_DUPS al s b r d) ∧
        rt_Regs47 al s b r d ((k + 1) * ((al.length ^ (s + b)) ^ r * al.length ^ r)) st)
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 32 = rt_choose al s b r d k)
      (rt_kCh al.length s b r d) := by
  have hq := H.q2
  have hGpos := rt_G_pos al.length s b r d (by omega)
  have hB := H.hB
  have hz0 := rt_z0_lt al H.nd H.all b
  have hQ : al.length ^ b ≤ rt_G al.length s b r d :=
    Nat.le_of_dvd hGpos ⟨(al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d * al.length ^ s *
      al.length ^ r * (al.length ^ b) ^ d * al.length ^ (s + b) * al.length, by unfold rt_G; ring⟩
  set QA := (al.length ^ (s + b)) ^ r * al.length ^ r with hQA
  -- the shared frame
  let R : ℕ → rt_St F → Prop := fun w st => st.nr 20 = k ∧ st.nr 29 = w ∧
    rt_Reg st 3 (rt_DUPS al s b r d) ∧ rt_Regs47 al s b r d ((k + 1) * QA) st
  have hRst : ∀ w st st', rt_Agr (rt_cScore (F := F)) st st' → R w st → R w st' := by
    rintro w st st' hA ⟨h20, h29, h3, h4, h5, h6, h7⟩
    exact ⟨by rw [rt_nr_agr (rt_notin_of rfl) hA, h20], by rw [rt_nr_agr (rt_notin_of rfl) hA, h29],
      rt_Reg_agr rfl (rt_notin_of rfl) (by decide) hA h3,
      rt_Reg_agr rfl (rt_notin_of rfl) (by decide) hA h4,
      rt_Reg_agr rfl (rt_notin_of rfl) (by decide) hA h5,
      rt_Reg_agr rfl (rt_notin_of rfl) (by decide) hA h6,
      rt_Reg_agr rfl (rt_notin_of rfl) (by decide) hA h7⟩
  have hSc : ∀ w, w < al.length ^ b → ∀ (X : rt_St F → Prop),
      (∀ st st', rt_Agr (rt_cScore (F := F)) st st' → X st → X st') →
      rt_Sp ns B rt_cScore (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ R w st ∧ X st)
        (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 30 = rt_Sc al s b r d k w ∧
          R w st ∧ X st) (rt_kSc al.length s b r d) := by
    intro w hw X hX
    have := rt_sp_frame (rt_Score_spec al s b r d B H ns k w hk hw)
      (R := fun st => R w st ∧ X st)
      (fun st st' hA ⟨h1, h2⟩ => ⟨hRst w st st' hA h1, hX st st' hA h2⟩)
    refine rt_sp_conseq this ?_ ?_ le_rfl
    · rintro st ⟨hC, hb, hR, hXs⟩
      obtain ⟨h20, h29, h3, h47⟩ := hR
      exact ⟨⟨hC, hb, h20, h29, h3, h47⟩, ⟨h20, h29, h3, h47⟩, hXs⟩
    · rintro st ⟨⟨hC, hb, h30⟩, hR, hXs⟩
      exact ⟨hC, hb, h30, hR, hXs⟩
  -- the loop invariant
  let I : ℕ → rt_St F → Prop := fun w st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ R w st ∧
    st.nr 32 = (List.range w).foldl (rt_chooseStep al s b r d k) (rt_z0 al b) ∧
    st.nr 31 = rt_Sc al s b r d k (st.nr 32)
  -- first instruction
  have e0 : rt_Sp ns B (rt_A 29 14 0)
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 20 = k ∧
        rt_Reg st 3 (rt_DUPS al s b r d) ∧ rt_Regs47 al s b r d ((k + 1) * QA) st)
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ R (rt_z0 al b) st ∧ True) 1 := by
    apply rt_sp_sym'
    rintro st ⟨hC, hb, h20, h3, h47⟩
    refine ⟨hb, by simp [rt_symV, rt_A, rt_wv, rt_simple, hC.h14, hC.h0]; omega,
      fun hb' hA => ⟨rt_Cst_agr rfl hA hC, hb', ⟨?_, ?_, h3, h47⟩, trivial⟩⟩
    · simp [rt_sym, rt_A, rt_eff, rt_setN, h20]
    · simp [rt_sym, rt_A, rt_eff, rt_setN, hC.h14, hC.h0]
  have e1 := hSc (rt_z0 al b) hz0 (fun _ => True) (fun _ _ _ _ => trivial)
  have e2 : rt_Sp ns B (rt_seqs [rt_A 31 30 0, rt_A 32 14 0, rt_L 29 0])
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧
        st.nr 30 = rt_Sc al s b r d k (rt_z0 al b) ∧ R (rt_z0 al b) st ∧ True) (I 0) 3 := by
    apply rt_sp_sym'
    rintro st ⟨hC, hb, h30, ⟨h20, h29, h3, h47⟩, -⟩
    refine ⟨hb, ?_, fun hb' hA => ?_⟩
    · simp [rt_seqs, rt_symV, rt_sym, rt_A, rt_L, rt_eff, rt_setN, rt_wv, rt_simple, hC.h14,
        hC.h0]
      exact ⟨hb 30, by omega⟩
    · have key : (rt_sym ns (rt_seqs [rt_A 31 30 0, rt_A 32 14 0, rt_L (F := F) 29 0]) st).nr 20 = k ∧
          (rt_sym ns (rt_seqs [rt_A 31 30 0, rt_A 32 14 0, rt_L (F := F) 29 0]) st).nr 29 = 0 ∧
          (rt_sym ns (rt_seqs [rt_A 31 30 0, rt_A 32 14 0, rt_L (F := F) 29 0]) st).nr 32 =
            rt_z0 al b ∧
          (rt_sym ns (rt_seqs [rt_A 31 30 0, rt_A 32 14 0, rt_L (F := F) 29 0]) st).nr 31 =
            rt_Sc al s b r d k (rt_z0 al b) ∧
          (rt_sym ns (rt_seqs [rt_A 31 30 0, rt_A 32 14 0, rt_L (F := F) 29 0]) st).fr = st.fr := by
        simp [rt_seqs, rt_sym, rt_A, rt_L, rt_eff, rt_setN, hC.h14, hC.h0, h20, h30]
      obtain ⟨k20, k29, k32, k31, kfr⟩ := key
      refine ⟨rt_Cst_agr rfl hA hC, hb', ⟨k20, k29, rt_Reg_same h3 kfr, ?_⟩, by simp [k32], ?_⟩
      · obtain ⟨h4, h5, h6, h7⟩ := h47
        exact ⟨rt_Reg_same h4 kfr, rt_Reg_same h5 kfr, rt_Reg_same h6 kfr, rt_Reg_same h7 kfr⟩
      · rw [k31, k32]
  have e3 : rt_Sp ns B (.loop 29 7 rt_cChw) (I 0) (I (al.length ^ b))
      ((al.length ^ b - 0) * (rt_kSc al.length s b r d + 5 + 4) + 1) := by
    refine rt_sp_loop I 0 _ _ (Nat.zero_le _) ?_ ?_
    · rintro w st _ _ ⟨hC, hb, ⟨_, h29, _⟩, -⟩
      exact ⟨h29, hC.h7, hb⟩
    · intro w _ hw
      let X : rt_St F → Prop := fun st =>
        st.nr 32 = (List.range w).foldl (rt_chooseStep al s b r d k) (rt_z0 al b) ∧
        st.nr 31 = rt_Sc al s b r d k (st.nr 32)
      have hX : ∀ st st', rt_Agr (rt_cScore (F := F)) st st' → X st → X st' := by
        rintro st st' hA ⟨h1, h2⟩
        rw [show X st' = (st'.nr 32 = _ ∧ st'.nr 31 = _) from rfl,
          rt_nr_agr (rt_notin_of rfl) hA, rt_nr_agr (rt_notin_of rfl) hA]
        exact ⟨h1, h2⟩
      have f1 := hSc w hw X hX
      have f2 : rt_Sp ns B (.seq (rt_Sb 37 31 30) (.ifN 37 0 rt_skip (.seq (rt_A 32 29 0) (rt_A 31 30 0))))
          (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 30 = rt_Sc al s b r d k w ∧
            R w st ∧ X st)
          (fun s1 => rt_Bd B s1 ∧ rt_Bd B (rt_inc s1 29) ∧ I (w + 1) (rt_inc s1 29)) 5 := by
        refine rt_sp_seq (N1 := 1) (N2 := 4)
          (R := fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 30 = rt_Sc al s b r d k w ∧
            R w st ∧ X st ∧ st.nr 37 = st.nr 31 - st.nr 30) ?_ ?_
        · apply rt_sp_sym'
          rintro st ⟨hC, hb, h30, ⟨h20, h29, h3, h47⟩, h32, h31⟩
          refine ⟨hb, by have := hb 31; simp [rt_symV, rt_Sb, rt_wv, rt_simple]; omega,
            fun hb' hA => ?_⟩
          have kfr : (rt_sym ns (rt_Sb (F := F) 37 31 30) st).fr = st.fr := rfl
          obtain ⟨h4, h5, h6, h7⟩ := h47
          refine ⟨rt_Cst_agr rfl hA hC, hb', ?_, ⟨?_, ?_, rt_Reg_same h3 kfr, rt_Reg_same h4 kfr,
            rt_Reg_same h5 kfr, rt_Reg_same h6 kfr, rt_Reg_same h7 kfr⟩, ⟨?_, ?_⟩, ?_⟩ <;>
            simp [rt_sym, rt_Sb, rt_eff, rt_setN, h30, h20, h29, h32, h31]
        · refine rt_sp_conseq (rt_sp_ifN (N1 := 1) (N2 := 2) ?_ ?_ ?_) (fun st h => h)
            (fun st h => h) (by omega)
          · exact fun st h => h.2.1
          · -- not an improvement
            apply rt_sp_sym'
            rintro st ⟨⟨hC, hb, h30, ⟨h20, h29, h3, h47⟩, ⟨h32, h31⟩, h37⟩, h0⟩
            refine ⟨hb, by simp [rt_symV, rt_skip, rt_L, rt_wv, rt_simple], fun hb' hA => ?_⟩
            have hC' := rt_Cst_agr rfl hA hC
            have kfr : (rt_sym ns (rt_skip (F := F)) st).fr = st.fr := rfl
            have hn : ∀ j, j ≠ 61 → (rt_sym ns (rt_skip (F := F)) st).nr j = st.nr j := by
              intro j hj; simp [rt_sym, rt_skip, rt_L, rt_eff, rt_setN, hj]
            have hbi : rt_Bd B (rt_inc (rt_sym ns rt_skip st) 29) :=
              rt_Bd_inc (by decide) hb' (by omega) (by rw [hn 29 (by decide), h29]; omega)
            have hlt : ¬ rt_Sc al s b r d k w < st.nr 31 := by
              rw [hC.h0] at h0; omega
            obtain ⟨h4, h5, h6, h7⟩ := h47
            refine ⟨⟨hb', hbi, rt_Cst_inc (by decide) (by decide) hC', hbi, ⟨?_, ?_,
              rt_Reg_same h3 kfr, rt_Reg_same h4 kfr, rt_Reg_same h5 kfr, rt_Reg_same h6 kfr,
              rt_Reg_same h7 kfr⟩, ?_, ?_⟩, hb'⟩
            · rw [rt_inc_nr _ 29 20 (by decide), if_neg (by decide), if_neg (by decide),
                hn 20 (by decide), h20]
            · rw [rt_inc_nr _ 29 29 (by decide), if_pos rfl, hn 29 (by decide), h29]
            · rw [rt_inc_nr _ 29 32 (by decide), if_neg (by decide), if_neg (by decide),
                hn 32 (by decide), h32, List.range_succ, List.foldl_append]
              simp only [List.foldl_cons, List.foldl_nil, rt_chooseStep]
              rw [if_neg (by rw [← h32, ← h31]; exact hlt)]
            · rw [rt_inc_nr _ 29 31 (by decide), if_neg (by decide), if_neg (by decide),
                hn 31 (by decide), rt_inc_nr _ 29 32 (by decide), if_neg (by decide),
                if_neg (by decide), hn 32 (by decide), h31]
          · -- an improvement
            apply rt_sp_sym'
            rintro st ⟨⟨hC, hb, h30, ⟨h20, h29, h3, h47⟩, ⟨h32, h31⟩, h37⟩, h0⟩
            refine ⟨hb, ?_, fun hb' hA => ?_⟩
            · simp [rt_symV, rt_sym, rt_A, rt_wv, rt_simple, rt_eff, rt_setN, hC.h0]
              exact ⟨hb 29, hb 30⟩
            have hC' := rt_Cst_agr rfl hA hC
            have kfr : (rt_sym ns (.seq (rt_A (F := F) 32 29 0) (rt_A 31 30 0)) st).fr = st.fr := rfl
            have hn : ∀ j, j ≠ 31 → j ≠ 32 →
                (rt_sym ns (.seq (rt_A (F := F) 32 29 0) (rt_A 31 30 0)) st).nr j = st.nr j := by
              intro j h1 h2; simp [rt_sym, rt_A, rt_eff, rt_setN, h1, h2]
            have k31 : (rt_sym ns (.seq (rt_A (F := F) 32 29 0) (rt_A 31 30 0)) st).nr 31 =
                rt_Sc al s b r d k w := by simp [rt_sym, rt_A, rt_eff, rt_setN, hC.h0, h30]
            have k32 : (rt_sym ns (.seq (rt_A (F := F) 32 29 0) (rt_A 31 30 0)) st).nr 32 = w := by
              simp [rt_sym, rt_A, rt_eff, rt_setN, hC.h0, h29]
            have hbi : rt_Bd B (rt_inc (rt_sym ns (.seq (rt_A (F := F) 32 29 0) (rt_A 31 30 0)) st) 29) :=
              rt_Bd_inc (by decide) hb' (by omega) (by rw [hn 29 (by decide) (by decide), h29]; omega)
            have hlt : rt_Sc al s b r d k w < st.nr 31 := by
              rw [hC.h0] at h0; omega
            obtain ⟨h4, h5, h6, h7⟩ := h47
            refine ⟨hb', hbi, rt_Cst_inc (by decide) (by decide) hC', hbi, ⟨?_, ?_,
              rt_Reg_same h3 kfr, rt_Reg_same h4 kfr, rt_Reg_same h5 kfr, rt_Reg_same h6 kfr,
              rt_Reg_same h7 kfr⟩, ?_, ?_⟩
            · rw [rt_inc_nr _ 29 20 (by decide), if_neg (by decide), if_neg (by decide),
                hn 20 (by decide) (by decide), h20]
            · rw [rt_inc_nr _ 29 29 (by decide), if_pos rfl, hn 29 (by decide) (by decide), h29]
            · rw [rt_inc_nr _ 29 32 (by decide), if_neg (by decide), if_neg (by decide), k32,
                List.range_succ, List.foldl_append]
              simp only [List.foldl_cons, List.foldl_nil, rt_chooseStep]
              rw [if_pos (by rw [← h32, ← h31]; exact hlt)]
            · rw [rt_inc_nr _ 29 31 (by decide), if_neg (by decide), if_neg (by decide), k31,
                rt_inc_nr _ 29 32 (by decide), if_neg (by decide), if_neg (by decide), k32]
      have := rt_sp_seq f1 f2
      refine rt_sp_conseq this ?_ (fun st h => h) le_rfl
      rintro st ⟨hC, hb, hR, h32, h31⟩
      exact ⟨hC, hb, hR, h32, h31⟩
  have := rt_sp_seq e0 (rt_sp_seq e1 (rt_sp_seq e2 e3))
  refine rt_sp_conseq this (fun st h => h) ?_ ?_
  · rintro st ⟨hC, hb, -, h32, -⟩
    exact ⟨hC, hb, h32⟩
  · simp only [rt_kCh, Nat.sub_zero]; ring_nf; omega

def rt_kOut (b : ℕ) : ℕ := 15 * b + 20

theorem rt_Out_spec (al : List F) (s b r d B : ℕ) (H : rt_Hyp al s b r d B) (ns : List ℕ)
    (k : ℕ) (hk : k < al.length ^ s) :
    rt_Sp ns B rt_cOut
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 20 = k ∧
        st.nr 32 = rt_sel al s b r d k ∧ rt_Reg st 8 (rt_AMS al s b r d k) ∧
        st.out = (rt_outData al s b r d k).reverse)
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 20 = k ∧
        rt_Reg st 8 (rt_AMS al s b r d (k + 1)) ∧
        st.out = (rt_outData al s b r d (k + 1)).reverse)
      (rt_kOut b) := by
  have hq := H.q2
  have hGpos := rt_G_pos al.length s b r d (by omega)
  have hB := H.hB
  have hselb := rt_sel_lt al H.nd H.all s b r d k
  have hQ : al.length ^ s * al.length ^ b ≤ rt_G al.length s b r d :=
    Nat.le_of_dvd hGpos ⟨(al.length ^ (s + b)) ^ r * (al.length ^ r) ^ d * al.length ^ r *
      (al.length ^ b) ^ d * al.length ^ (s + b) * al.length, by unfold rt_G; ring⟩
  have hbq := rt_b_le_pow al.length b hq
  have hqb : al.length ^ b ≤ al.length ^ s * al.length ^ b :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have hkq : k * al.length ^ b + rt_sel al s b r d k < al.length ^ s * al.length ^ b := by
    have : (k + 1) * al.length ^ b ≤ al.length ^ s * al.length ^ b :=
      Nat.mul_le_mul_right _ hk
    rw [Nat.succ_mul] at this; omega
  set f : ℕ → F := fun j => al.getD (rt_dg al.length (rt_sel al s b r d k) (b - 1 - j)) 0
    with hf
  have hout : rt_outData al s b r d (k + 1) =
      rt_outData al s b r d k ++ (List.range b).map f := rfl
  let I : ℕ → rt_St F → Prop := fun j st => rt_Cst al s b r d st ∧ rt_Bd B st ∧
    st.nr 24 = j ∧ st.nr 20 = k ∧ st.nr 32 = rt_sel al s b r d k ∧
    st.nr 53 = al.length ^ (b - 1) / al.length ^ j ∧ rt_Reg st 8 (rt_AMS al s b r d (k + 1)) ∧
    st.out = (rt_outData al s b r d k ++ (List.range j).map f).reverse
  have hqB : al.length ^ b ≤ B := by omega
  have hq1 : al.length ≤ al.length ^ b := Nat.le_self_pow (by have := H.hb; omega) _
  have hqb1 : al.length ^ (b - 1) ≤ al.length ^ b := Nat.pow_le_pow_right (by omega) (by omega)
  have e1 : rt_Sp ns B (rt_seqs [rt_M 37 20 7, rt_A 37 37 32, .stR 8 37 48, rt_A 53 15 0,
      rt_L 24 0])
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 20 = k ∧
        st.nr 32 = rt_sel al s b r d k ∧ rt_Reg st 8 (rt_AMS al s b r d k) ∧
        st.out = (rt_outData al s b r d k).reverse) (I 0) 9 := by
    apply rt_sp_sym'
    rintro st ⟨hC, hb, h20, h32, h8, ho⟩
    refine ⟨hb, ?_, fun hb' hA => ?_⟩
    · simp [rt_seqs, rt_symV, rt_sym, rt_M, rt_A, rt_L, rt_eff, rt_setN, rt_wv, rt_stRes,
        rt_simple, hC.h7, h20, h32, hC.h15, hC.h0]
      refine ⟨by omega, by omega, by omega, by omega⟩
    · have key : (rt_sym ns (rt_seqs [rt_M 37 20 7, rt_A 37 37 32, .stR 8 37 48, rt_A 53 15 0,
          rt_L 24 0]) st).nr 24 = 0 ∧
          (rt_sym ns (rt_seqs [rt_M 37 20 7, rt_A 37 37 32, .stR 8 37 48, rt_A 53 15 0,
          rt_L 24 0]) st).nr 20 = k ∧
          (rt_sym ns (rt_seqs [rt_M 37 20 7, rt_A 37 37 32, .stR 8 37 48, rt_A 53 15 0,
          rt_L 24 0]) st).nr 32 = rt_sel al s b r d k ∧
          (rt_sym ns (rt_seqs [rt_M 37 20 7, rt_A 37 37 32, .stR 8 37 48, rt_A 53 15 0,
          rt_L 24 0]) st).nr 53 = al.length ^ (b - 1) ∧
          (rt_sym ns (rt_seqs [rt_M 37 20 7, rt_A 37 37 32, .stR 8 37 48, rt_A 53 15 0,
          rt_L 24 0]) st).fr = Function.update st.fr
            ((k * al.length ^ b + rt_sel al s b r d k) * 16 + 8) 1 ∧
          (rt_sym ns (rt_seqs [rt_M 37 20 7, rt_A 37 37 32, .stR 8 37 48, rt_A 53 15 0,
          rt_L 24 0]) st).out = st.out := by
        simp [rt_seqs, rt_sym, rt_M, rt_A, rt_L, rt_eff, rt_setN, rt_stRes,
          hC.h7, h20, h32, hC.h15, hC.h0, hC.f48]
      obtain ⟨k24, k20, k32, k53, kfr, kout⟩ := key
      refine ⟨rt_Cst_agr rfl hA hC, hb', k24, k20, k32, by rw [k53]; simp, ?_, ?_⟩
      · refine rt_Reg_upd (by omega) h8 kfr ?_
        intro m
        simp only [rt_AMS]
        have hd := rt_divmod (k := k) hselb
        constructor
        · rintro ⟨h1, h2⟩
          by_cases hmk : m / al.length ^ b < k
          · exact Or.inl ⟨hmk, h2⟩
          · right
            have hm : m / al.length ^ b = k := by omega
            have := Nat.div_add_mod m (al.length ^ b)
            rw [hm] at h2 this
            rw [← this, h2]; ring
        · rintro (⟨h1, h2⟩ | rfl)
          · exact ⟨by omega, h2⟩
          · rw [hd.1, hd.2]; exact ⟨by omega, rfl⟩
      · rw [kout, ho]; simp
  have e2 : rt_Sp ns B (.loop 24 3 rt_cOutj) (I 0) (I b) ((b - 0) * (9 + 4) + 1) := by
    refine rt_sp_loop I 0 b 9 (Nat.zero_le _) ?_ ?_
    · rintro j st _ _ ⟨hC, hb, h24, -⟩
      exact ⟨h24, hC.h3, hb⟩
    · intro j _ hj
      apply rt_sp_sym'
      rintro st ⟨hC, hb, h24, h20, h32, h53, h8, ho⟩
      have hpd : al.length ^ (b - 1) / al.length ^ j = al.length ^ (b - 1 - j) :=
        Nat.pow_div (by omega) (by omega)
      rw [hpd] at h53
      have hdig : rt_sel al s b r d k / al.length ^ (b - 1 - j) % al.length < al.length :=
        Nat.mod_lt _ (by omega)
      have hpdle : al.length ^ (b - 1 - j) ≤ al.length ^ b :=
        Nat.pow_le_pow_right (by omega) (by omega)
      refine ⟨hb, ?_, fun hb' hA => ?_⟩
      · simp [rt_cOutj, rt_seqs, rt_symV, rt_sym, rt_D, rt_Md, rt_eff, rt_setN, rt_wv,
          rt_ldRes, rt_simple, h32, h53, hC.h6]
        refine ⟨le_trans (Nat.div_le_self _ _) (by omega), by omega, by omega,
          le_trans (Nat.div_le_self _ _) (by omega)⟩
      · have key : (rt_sym ns rt_cOutj st).nr 24 = j ∧ (rt_sym ns rt_cOutj st).nr 20 = k ∧
            (rt_sym ns rt_cOutj st).nr 32 = rt_sel al s b r d k ∧
            (rt_sym ns rt_cOutj st).nr 53 = al.length ^ (b - 1 - j) / al.length ∧
            (rt_sym ns rt_cOutj st).out =
              st.fr ((rt_sel al s b r d k / al.length ^ (b - 1 - j) % al.length) * 16 + 1)
                :: st.out := by
          simp [rt_cOutj, rt_seqs, rt_sym, rt_D, rt_Md, rt_eff, rt_setN, rt_ldRes,
            h32, h53, hC.h6, h24, h20]
        obtain ⟨k24, k20, k32, k53, kout⟩ := key
        have hfr : (rt_sym ns rt_cOutj st).fr 48 = 1 ∧ True := ⟨(rt_Cst_agr rfl hA hC).f48, trivial⟩
        have hC' := rt_Cst_agr rfl hA hC
        have hbi : rt_Bd B (rt_inc (rt_sym ns rt_cOutj st) 24) :=
          rt_Bd_inc (by decide) hb' (by omega) (by rw [k24]; omega)
        refine ⟨hb', hbi, rt_Cst_inc (by decide) (by decide) hC', hbi, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [rt_inc_nr _ 24 24 (by decide), if_pos rfl, k24]
        · rw [rt_inc_nr _ 24 20 (by decide), if_neg (by decide), if_neg (by decide), k20]
        · rw [rt_inc_nr _ 24 32 (by decide), if_neg (by decide), if_neg (by decide), k32]
        · rw [rt_inc_nr _ 24 53 (by decide), if_neg (by decide), if_neg (by decide), k53,
            pow_succ, ← Nat.div_div_eq_div_mul, hpd]
        · exact rt_Reg_inc (rt_Reg_agr rfl (rt_notin_of rfl) (by decide) hA h8)
        · show (rt_sym ns rt_cOutj st).out = _
          rw [kout, ho, hC.tab _ hdig, List.range_succ, List.map_append, ← List.append_assoc,
            List.reverse_append]
          simp [hf, rt_dg]
  refine rt_sp_conseq (rt_sp_seq e1 e2) (fun st h => h) ?_ ?_
  · rintro st ⟨hC, hb, -, h20, -, -, h8, ho⟩
    exact ⟨hC, hb, h20, h8, by rw [ho, hout]⟩
  · simp only [rt_kOut, Nat.sub_zero]; omega

def rt_kSet (q s b r d : ℕ) : ℕ := 20 * (s + b + r + d) + 7 * q + 60

def rt_Vals (l : List (ℕ × ℕ)) (st : rt_St F) : Prop := ∀ p ∈ l, st.nr p.1 = p.2

theorem rt_Vals_agr {c : rt_Cmd F} {l : List (ℕ × ℕ)}
    (h : (l.map Prod.fst).all (fun j => !(rt_wn c).contains j) = true) {st st' : rt_St F}
    (hA : rt_Agr c st st') (hV : rt_Vals l st) : rt_Vals l st' := by
  intro p hp
  have : p.1 ∉ rt_wn c := by
    rw [List.all_eq_true] at h
    have := h p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
    simpa using this
  rw [rt_nr_agr this hA]; exact hV p hp

def rt_R0 (st : rt_St F) : Prop := st.out = [] ∧ ∀ a, 2 ≤ a % 16 → st.fr a = 0

def rt_okS (c : rt_Cmd F) : Bool :=
  (rt_wf c).all (fun x => decide (x % 16 = 0)) && (rt_wr c).all (fun k => decide (k < 2)) &&
    !(rt_wo c)

theorem rt_R0_agr {c : rt_Cmd F} (h : rt_okS c = true) {st st' : rt_St F}
    (hA : rt_Agr c st st') (hR : rt_R0 st) : rt_R0 st' := by
  simp only [rt_okS, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨by rw [hA.2.2 h3, hR.1], fun a ha => ?_⟩
  rw [hA.2.1 a (fun hm => by have := h1 a hm; omega) (fun hm => by have := h2 _ hm; omega)]
  exact hR.2 a ha

theorem rt_Pow_core {ns : List ℕ} {B : ℕ} (dst bs ex x e : ℕ) (h1 : dst ≠ 35) (h2 : dst ≠ 61)
    (h3 : bs ≠ 35) (h4 : bs ≠ 61) (h5 : bs ≠ dst) (h6 : ex ≠ 35) (h7 : ex ≠ 61) (h8 : ex ≠ dst)
    (hB : ∀ i ≤ e, x ^ i ≤ B) (heB : e + 1 ≤ B) :
    rt_Sp ns B (rt_cPow (F := F) dst bs ex)
      (fun st => rt_Bd B st ∧ st.nr bs = x ∧ st.nr ex = e)
      (fun st => rt_Bd B st ∧ st.nr dst = x ^ e) (e * 5 + 3) := by
  let I : ℕ → rt_St F → Prop := fun i st => rt_Bd B st ∧ st.nr 35 = i ∧ st.nr dst = x ^ i ∧
    st.nr bs = x ∧ st.nr ex = e
  have e1 : rt_Sp ns B (rt_seqs [rt_L (F := F) dst 1, rt_L 35 0])
      (fun st => rt_Bd B st ∧ st.nr bs = x ∧ st.nr ex = e) (I 0) 2 := by
    apply rt_sp_sym
    rintro st ⟨hb, hx, he⟩
    have := hB 0 (Nat.zero_le _)
    refine ⟨hb, by simp [rt_seqs, rt_symV, rt_L, rt_wv, rt_simple]; omega, fun hb' => ?_⟩
    refine ⟨hb', ?_, ?_, ?_, ?_⟩ <;>
      simp [rt_seqs, rt_sym, rt_L, rt_eff, rt_setN, Function.update_apply, h1, h2, h3, h4, h5, h6,
        h7, h8, Ne.symm h1, Ne.symm h3, Ne.symm h5, Ne.symm h6, Ne.symm h8, hx, he]
  have e2 : rt_Sp ns B (.loop 35 ex (rt_M (F := F) dst dst bs)) (I 0) (I e) ((e - 0) * (1 + 4) + 1) := by
    refine rt_sp_loop I 0 e 1 (Nat.zero_le _) ?_ ?_
    · rintro i st _ _ ⟨hb, h35, -, -, hex⟩
      exact ⟨h35, hex, hb⟩
    · intro i _ hi
      apply rt_sp_sym
      rintro st ⟨hb, h35, hd, hx, he⟩
      have hp := hB (i + 1) (by omega)
      have e' : x ^ i * x = x ^ (i + 1) := (pow_succ _ _).symm
      refine ⟨hb, by simp [rt_symV, rt_M, rt_wv, rt_simple, hd, hx]; rw [e']; exact hp,
        fun hb' => ?_⟩
      have hn : ∀ j, j ≠ dst → (rt_sym ns (rt_M (F := F) dst dst bs) st).nr j = st.nr j := by
        intro j hj; simp [rt_sym, rt_M, rt_eff, rt_setN, Function.update_apply, hj]
      have kd : (rt_sym ns (rt_M (F := F) dst dst bs) st).nr dst = x ^ (i + 1) := by
        simp [rt_sym, rt_M, rt_eff, rt_setN, hd, hx, e']
      have hbi : rt_Bd B (rt_inc (rt_sym ns (rt_M (F := F) dst dst bs) st) 35) :=
        rt_Bd_inc (by decide) hb' (by have := hB 0 (Nat.zero_le _); simp at this; omega)
          (by rw [hn 35 (Ne.symm h1), h35]; omega)
      have hI : ∀ j, j ≠ 35 → j ≠ 61 → (rt_inc (rt_sym ns (rt_M (F := F) dst dst bs) st) 35).nr j =
          (rt_sym ns (rt_M dst dst bs) st).nr j := by
        intro j j1 j2; rw [rt_inc_nr _ _ _ (by decide), if_neg j1, if_neg j2]
      refine ⟨hb', hbi, hbi, by rw [rt_inc_nr _ _ _ (by decide), if_pos rfl, hn 35 (Ne.symm h1), h35],
        by rw [hI dst h1 h2, kd], by rw [hI bs h3 h4, hn bs h5, hx], by rw [hI ex h6 h7, hn ex h8, he]⟩
  refine rt_sp_conseq (rt_sp_seq e1 e2) (fun st h => h) ?_ ?_
  · rintro st ⟨hb, -, hd, -⟩; exact ⟨hb, hd⟩
  · simp only [Nat.sub_zero]; omega

theorem rt_Pow_spec {ns : List ℕ} {B : ℕ} (dst bs ex x e : ℕ) (h1 : dst ≠ 35) (h2 : dst ≠ 61)
    (h3 : bs ≠ 35) (h4 : bs ≠ 61) (h5 : bs ≠ dst) (h6 : ex ≠ 35) (h7 : ex ≠ 61) (h8 : ex ≠ dst)
    (hB : ∀ i ≤ e, x ^ i ≤ B) (heB : e + 1 ≤ B) (R : rt_St F → Prop)
    (hR : ∀ st st', rt_Agr (rt_cPow (F := F) dst bs ex) st st' → R st → R st') :
    rt_Sp ns B (rt_cPow (F := F) dst bs ex)
      (fun st => R st ∧ rt_Bd B st ∧ st.nr bs = x ∧ st.nr ex = e)
      (fun st => R st ∧ rt_Bd B st ∧ st.nr dst = x ^ e) (e * 5 + 3) := by
  have := rt_sp_frame (rt_Pow_core (F := F) (ns := ns) (B := B) dst bs ex x e h1 h2 h3 h4 h5 h6 h7
    h8 hB heB) (R := R) hR
  refine rt_sp_conseq this ?_ ?_ le_rfl
  · rintro st ⟨hR', hb, hx, he⟩; exact ⟨⟨hb, hx, he⟩, hR'⟩
  · rintro st ⟨⟨hb, hd⟩, hR'⟩; exact ⟨hR', hb, hd⟩

theorem rt_Tab_spec {ns : List ℕ} {B : ℕ} (al : List F) (hB : 17 * al.length + 17 ≤ B) :
    ∀ (l : List F) (e : ℕ), l = al.drop e → e + l.length = al.length →
      rt_Sp ns B (rt_cTab l e)
        (fun st => rt_Bd B st ∧ rt_R0 st ∧ st.fr 48 = 1 ∧
          ∀ e' < e, st.fr (e' * 16 + 1) = al.getD e' 0)
        (fun st => rt_Bd B st ∧ rt_R0 st ∧ st.fr 48 = 1 ∧
          ∀ e' < al.length, st.fr (e' * 16 + 1) = al.getD e' 0)
        (7 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro e _ hlen
    apply rt_sp_sym'
    rintro st ⟨hb, hR, h48, ht⟩
    refine ⟨hb, by simp [rt_cTab, rt_skip, rt_symV, rt_L, rt_wv, rt_simple], fun hb' hA => ?_⟩
    have kfr : (rt_sym ns (rt_cTab (F := F) [] e) st).fr = st.fr := rfl
    refine ⟨hb', ⟨by rw [rt_out_agr rfl hA, hR.1], fun a ha => by rw [kfr]; exact hR.2 a ha⟩,
      by rw [kfr, h48], fun e' he' => by rw [kfr]; exact ht e' (by simp at hlen; omega)⟩
  | cons a l ih =>
    intro e hl hlen
    have hlen' : e + 1 + l.length = al.length := by simp at hlen; omega
    have hl' : l = al.drop (e + 1) := by
      rw [← List.drop_drop, ← hl]; simp
    have he : e < al.length := by simp at hlen; omega
    have ha : al.getD e 0 = a := by
      have : al.drop e = a :: l := hl.symm
      rw [List.getD_eq_getElem _ _ he]
      have h2 := congrArg (fun l => l[0]?) this
      simp [List.getElem?_drop] at h2
      rw [List.getElem?_eq_getElem he] at h2
      exact Option.some_inj.mp h2
    have g1 : rt_Sp ns B (rt_seqs [rt_L 37 e, rt_K 64 a, .stR 1 37 64])
        (fun st => rt_Bd B st ∧ rt_R0 st ∧ st.fr 48 = 1 ∧
          ∀ e' < e, st.fr (e' * 16 + 1) = al.getD e' 0)
        (fun st => rt_Bd B st ∧ rt_R0 st ∧ st.fr 48 = 1 ∧
          ∀ e' < e + 1, st.fr (e' * 16 + 1) = al.getD e' 0) 7 := by
      apply rt_sp_sym'
      rintro st ⟨hb, hR, h48, ht⟩
      have hsv : rt_symV ns B (rt_seqs [rt_L (F := F) 37 e, rt_K 64 a, .stR 1 37 64]) st := by
        simp [rt_seqs, rt_symV, rt_sym, rt_L, rt_K, rt_wv, rt_simple, rt_eff, rt_setN, rt_setF]
        omega
      refine ⟨hb, hsv, fun hb' hA => ?_⟩
      have kfr : ∀ x, (rt_sym ns (rt_seqs [rt_L (F := F) 37 e, rt_K 64 a, .stR 1 37 64]) st).fr x =
          if x = e * 16 + 1 then a else if x = 64 then a else st.fr x := by
        intro x
        simp [rt_seqs, rt_sym, rt_L, rt_K, rt_eff, rt_setN, rt_setF, rt_stRes, Function.update_apply]
      refine ⟨hb', ⟨by rw [rt_out_agr rfl hA, hR.1], fun x hx => ?_⟩, ?_, fun e' he' => ?_⟩
      · rw [kfr, if_neg (by omega), if_neg (by omega)]; exact hR.2 x hx
      · rw [kfr, if_neg (by omega), if_neg (by omega), h48]
      · rw [kfr]
        by_cases h : e' = e
        · subst h; rw [if_pos rfl, ha]
        · rw [if_neg (by omega), if_neg (by omega)]; exact ht e' (by omega)
    have g2 := ih (e + 1) hl' hlen'
    refine rt_sp_conseq (rt_sp_seq g1 g2) (fun st h => h) (fun st h => h) ?_
    simp; omega

theorem rt_z0_eq (al : List F) (b : ℕ) :
    rt_z0 al b = ∑ k ∈ Finset.range b, rt_ix al 0 * al.length ^ k := by
  unfold rt_z0 rt_vidx
  simp only [Pi.zero_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => rt_ix al 0 * al.length ^ (b - 1 - k)) b]
  exact Finset.sum_range_reflect (fun k => rt_ix al 0 * al.length ^ k) b

theorem rt_cTab_wn (l : List F) : ∀ e, ∀ j ∈ rt_wn (rt_cTab l e), j = 37 ∨ j = 60 ∨ j = 61 := by
  induction l with
  | nil => intro e j hj; simp [rt_cTab, rt_skip, rt_L, rt_wn, rt_wnI] at hj; omega
  | cons a l ih =>
    intro e j hj
    simp only [rt_cTab, rt_wn, List.mem_append] at hj
    rcases hj with hj | hj
    · simp [rt_seqs, rt_L, rt_K, rt_wn, rt_wnI] at hj; omega
    · exact ih (e + 1) j hj

theorem rt_Setup_spec (al : List F) (s b r d B : ℕ) (H : rt_Hyp al s b r d B) :
    rt_Sp [s, b, r, d] B (rt_cSetup al (rt_ix al 0))
      (fun st => st = ⟨fun _ => 0, fun _ => 0, []⟩)
      (fun st => rt_Cst al s b r d st ∧ rt_Bd B st ∧
        (∀ k, 2 ≤ k → k ≤ 8 → rt_Reg st k (fun _ => False)) ∧ st.out = [])
      (rt_kSet al.length s b r d) := by
  have hq := H.q2
  have hBG := H.hB
  set q := al.length with hqdef
  have hGeq : rt_G q s b r d = q ^ ((s + b) * r + r * d + s + r + b + b * d + (s + b) + 1) := by
    unfold rt_G; ring
  have hpw : ∀ n, n ≤ (s + b) * r + r * d + s + r + b + b * d + (s + b) + 1 → q ^ n ≤ B := by
    intro n hn
    have := Nat.pow_le_pow_right (show 0 < q by omega) hn
    omega
  have hlt : ∀ n, n ≤ (s + b) * r + r * d + s + r + b + b * d + (s + b) + 1 → n + 1 ≤ B := by
    intro n hn; have := hpw n hn; have := Nat.lt_pow_self (n := n) (show 1 < q by omega); omega
  have hbd : d ≤ b * d := Nat.le_mul_of_pos_left d H.hb
  set i0 := rt_ix al 0 with hi0
  have hi0q : i0 < q := rt_ix_lt H.all 0
  have hqB : 17 * q + 17 ≤ B := by
    have h1 : q ^ 2 ≤ rt_G q s b r d := by
      rw [hGeq]; exact Nat.pow_le_pow_right (by omega) (by have := H.hs; omega)
    have : q * 17 + 17 ≤ q ^ 2 * 64 := by
      have : 2 * q ≤ q ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right q hq
      omega
    omega
  have hVc : ∀ (l : List (ℕ × ℕ)) j v (st : rt_St F), st.nr j = v → rt_Vals l st →
      rt_Vals ((j, v) :: l) st := by
    intro l j v st h hV p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h
    · exact hV p hp
  -- stage 1: inputs
  let l1 : List (ℕ × ℕ) := [(0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)]
  have g1 : rt_Sp [s, b, r, d] B (rt_seqs [.basic (.inputNat 2 0), .basic (.inputNat 3 1),
      .basic (.inputNat 4 2), .basic (.inputNat 5 3), rt_L (F := F) 6 al.length])
      (fun st => st = ⟨fun _ => 0, fun _ => 0, []⟩)
      (fun st => rt_Vals l1 st ∧ rt_R0 st ∧ rt_Bd B st) 5 := by
    apply rt_sp_sym
    rintro st rfl
    refine ⟨fun _ => Nat.zero_le _, ?_, fun hb' => ⟨?_, ?_, hb'⟩⟩
    · simp [rt_seqs, rt_symV, rt_sym, rt_L, rt_wv, rt_simple, rt_eff, rt_setN]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> [exact le_trans (by omega) (hlt s (by omega));
        exact le_trans (by omega) (hlt b (by omega)); exact le_trans (by omega) (hlt r (by omega));
        exact le_trans (by omega) (hlt d (by omega)); omega]
    · intro p hp
      simp only [l1, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [rt_seqs, rt_sym, rt_L, rt_eff, rt_setN, hqdef]
    · exact ⟨by simp [rt_seqs, rt_sym, rt_L, rt_eff, rt_setN],
        fun a _ => by simp [rt_seqs, rt_sym, rt_L, rt_eff, rt_setN]⟩
  have g2 : rt_Sp [s, b, r, d] B (rt_cPow (F := F) 7 6 3)
      (fun st => rt_Vals [(0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st)
      (fun st => rt_Vals [(7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st) (b * 5 + 3) := by
    have gP := rt_Pow_spec (F := F) (ns := [s, b, r, d]) (B := B) 7 6 3 (q) (b)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (fun i hi => hpw i (by omega)) (hlt b (by omega))
      (R := fun st => rt_Vals [(0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st)
      (fun st st' hA ⟨hV, hR⟩ => ⟨rt_Vals_agr rfl hA hV, rt_R0_agr rfl hA hR⟩)
    refine rt_sp_conseq gP ?_ ?_ le_rfl
    · rintro st ⟨hV, hR, hb⟩
      exact ⟨⟨hV, hR⟩, hb, hV (6, q) (by simp), hV (3, b) (by simp)⟩
    · rintro st ⟨⟨hV, hR⟩, hb, hd⟩
      exact ⟨hVc _ _ _ _ hd hV, hR, hb⟩

  have g3 : rt_Sp [s, b, r, d] B (rt_cPow (F := F) 8 6 4)
      (fun st => rt_Vals [(7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st)
      (fun st => rt_Vals [(8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st) (r * 5 + 3) := by
    have gP := rt_Pow_spec (F := F) (ns := [s, b, r, d]) (B := B) 8 6 4 (q) (r)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (fun i hi => hpw i (by omega)) (hlt r (by omega))
      (R := fun st => rt_Vals [(7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st)
      (fun st st' hA ⟨hV, hR⟩ => ⟨rt_Vals_agr rfl hA hV, rt_R0_agr rfl hA hR⟩)
    refine rt_sp_conseq gP ?_ ?_ le_rfl
    · rintro st ⟨hV, hR, hb⟩
      exact ⟨⟨hV, hR⟩, hb, hV (6, q) (by simp), hV (4, r) (by simp)⟩
    · rintro st ⟨⟨hV, hR⟩, hb, hd⟩
      exact ⟨hVc _ _ _ _ hd hV, hR, hb⟩

  have g4 : rt_Sp [s, b, r, d] B (rt_A (F := F) 16 2 3)
      (fun st => rt_Vals [(8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st)
      (fun st => rt_Vals [(16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st) 1 := by
    apply rt_sp_sym'
    rintro st ⟨hV, hR, hb⟩
    have h2 := hV (2, s) (by simp)
    have h3 := hV (3, b) (by simp)
    have hsb := hlt (s + b) (by omega)
    refine ⟨hb, by simp [rt_symV, rt_A, rt_wv, rt_simple, h2, h3]; omega,
      fun hb' hA => ⟨hVc _ _ _ _ ?_ (rt_Vals_agr rfl hA hV), rt_R0_agr rfl hA hR, hb'⟩⟩
    simp [rt_sym, rt_A, rt_eff, rt_setN, h2, h3]

  have g5 : rt_Sp [s, b, r, d] B (rt_cPow (F := F) 9 6 16)
      (fun st => rt_Vals [(16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st)
      (fun st => rt_Vals [(9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st) ((s + b) * 5 + 3) := by
    have gP := rt_Pow_spec (F := F) (ns := [s, b, r, d]) (B := B) 9 6 16 (q) ((s + b))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (fun i hi => hpw i (by omega)) (hlt (s + b) (by omega))
      (R := fun st => rt_Vals [(16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st)
      (fun st st' hA ⟨hV, hR⟩ => ⟨rt_Vals_agr rfl hA hV, rt_R0_agr rfl hA hR⟩)
    refine rt_sp_conseq gP ?_ ?_ le_rfl
    · rintro st ⟨hV, hR, hb⟩
      exact ⟨⟨hV, hR⟩, hb, hV (6, q) (by simp), hV (16, (s + b)) (by simp)⟩
    · rintro st ⟨⟨hV, hR⟩, hb, hd⟩
      exact ⟨hVc _ _ _ _ hd hV, hR, hb⟩

  have g6 : rt_Sp [s, b, r, d] B (rt_cPow (F := F) 13 6 2)
      (fun st => rt_Vals [(9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st)
      (fun st => rt_Vals [(13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st) (s * 5 + 3) := by
    have gP := rt_Pow_spec (F := F) (ns := [s, b, r, d]) (B := B) 13 6 2 (q) (s)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (fun i hi => hpw i (by omega)) (hlt s (by omega))
      (R := fun st => rt_Vals [(9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st)
      (fun st st' hA ⟨hV, hR⟩ => ⟨rt_Vals_agr rfl hA hV, rt_R0_agr rfl hA hR⟩)
    refine rt_sp_conseq gP ?_ ?_ le_rfl
    · rintro st ⟨hV, hR, hb⟩
      exact ⟨⟨hV, hR⟩, hb, hV (6, q) (by simp), hV (2, s) (by simp)⟩
    · rintro st ⟨⟨hV, hR⟩, hb, hd⟩
      exact ⟨hVc _ _ _ _ hd hV, hR, hb⟩

  have g7 : rt_Sp [s, b, r, d] B (rt_cPow (F := F) 10 9 4)
      (fun st => rt_Vals [(13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st)
      (fun st => rt_Vals [(10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st) (r * 5 + 3) := by
    have gP := rt_Pow_spec (F := F) (ns := [s, b, r, d]) (B := B) 10 9 4 (q ^ (s + b)) (r)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (fun i hi => by
        rw [← pow_mul]
        exact hpw _ (by have := Nat.mul_le_mul_left (s + b) hi; omega)) (hlt r (by omega))
      (R := fun st => rt_Vals [(13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st)
      (fun st st' hA ⟨hV, hR⟩ => ⟨rt_Vals_agr rfl hA hV, rt_R0_agr rfl hA hR⟩)
    refine rt_sp_conseq gP ?_ ?_ le_rfl
    · rintro st ⟨hV, hR, hb⟩
      exact ⟨⟨hV, hR⟩, hb, hV (9, q ^ (s + b)) (by simp), hV (4, r) (by simp)⟩
    · rintro st ⟨⟨hV, hR⟩, hb, hd⟩
      exact ⟨hVc _ _ _ _ hd hV, hR, hb⟩

  have g8 : rt_Sp [s, b, r, d] B (rt_cPow (F := F) 11 8 5)
      (fun st => rt_Vals [(10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st)
      (fun st => rt_Vals [(11, (q ^ r) ^ d), (10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st) (d * 5 + 3) := by
    have gP := rt_Pow_spec (F := F) (ns := [s, b, r, d]) (B := B) 11 8 5 (q ^ r) (d)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (fun i hi => by
        rw [← pow_mul]
        exact hpw _ (by have := Nat.mul_le_mul_left r hi; omega)) (hlt d (by omega))
      (R := fun st => rt_Vals [(10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st)
      (fun st st' hA ⟨hV, hR⟩ => ⟨rt_Vals_agr rfl hA hV, rt_R0_agr rfl hA hR⟩)
    refine rt_sp_conseq gP ?_ ?_ le_rfl
    · rintro st ⟨hV, hR, hb⟩
      exact ⟨⟨hV, hR⟩, hb, hV (8, q ^ r) (by simp), hV (5, d) (by simp)⟩
    · rintro st ⟨⟨hV, hR⟩, hb, hd⟩
      exact ⟨hVc _ _ _ _ hd hV, hR, hb⟩

  have g9 : rt_Sp [s, b, r, d] B
      (rt_seqs [rt_M (F := F) 12 10 8, rt_D 15 7 6, rt_L 14 0, rt_L 37 i0, rt_L 35 0])
      (fun st => rt_Vals [(11, (q ^ r) ^ d), (10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st ∧ rt_Bd B st)
      (fun st => (rt_Vals [(12, (q ^ (s + b)) ^ r * q ^ r), (15, q ^ b / q), (11, (q ^ r) ^ d), (10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st) ∧ rt_Bd B st ∧ st.nr 35 = 0 ∧ st.nr 37 = i0 ∧
        st.nr 14 = ∑ k ∈ Finset.range 0, i0 * q ^ k) 5 := by
    apply rt_sp_sym'
    rintro st ⟨hV, hR, hb⟩
    have h10 := hV (10, (q ^ (s + b)) ^ r) (by simp)
    have h8 := hV (8, q ^ r) (by simp)
    have h7 := hV (7, q ^ b) (by simp)
    have h6 := hV (6, q) (by simp)
    have hQ : (q ^ (s + b)) ^ r * q ^ r ≤ B := by
      rw [← pow_mul, ← pow_add]; exact hpw _ (by omega)
    have hQb : q ^ b ≤ B := hpw _ (by omega)
    refine ⟨hb, ?_, fun hb' hA => ?_⟩
    · simp [rt_seqs, rt_symV, rt_sym, rt_M, rt_D, rt_L, rt_wv, rt_simple, rt_eff, rt_setN, h10, h8,
        h7, h6]
      exact ⟨hQ, le_trans (Nat.div_le_self _ _) hQb, by omega⟩
    · refine ⟨⟨hVc _ _ _ _ ?_ (hVc _ _ _ _ ?_ (rt_Vals_agr rfl hA hV)), rt_R0_agr rfl hA hR⟩, hb',
        ?_, ?_, ?_⟩ <;>
        simp [rt_seqs, rt_sym, rt_M, rt_D, rt_L, rt_eff, rt_setN, h10, h8, h7, h6]

  have g10 : rt_Sp [s, b, r, d] B (.loop 35 3 (.seq (rt_M (F := F) 14 14 6) (rt_A 14 14 37)))
      (fun st => (rt_Vals [(12, (q ^ (s + b)) ^ r * q ^ r), (15, q ^ b / q), (11, (q ^ r) ^ d), (10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st) ∧ rt_Bd B st ∧ st.nr 35 = 0 ∧ st.nr 37 = i0 ∧
        st.nr 14 = ∑ k ∈ Finset.range 0, i0 * q ^ k)
      (fun st => (rt_Vals [(12, (q ^ (s + b)) ^ r * q ^ r), (15, q ^ b / q), (11, (q ^ r) ^ d), (10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st) ∧ rt_Bd B st ∧ st.nr 35 = b ∧ st.nr 37 = i0 ∧
        st.nr 14 = ∑ k ∈ Finset.range b, i0 * q ^ k) ((b - 0) * (2 + 4) + 1) := by
    refine rt_sp_loop (fun i st => (rt_Vals [(12, (q ^ (s + b)) ^ r * q ^ r), (15, q ^ b / q), (11, (q ^ r) ^ d), (10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st) ∧ rt_Bd B st ∧ st.nr 35 = i ∧
      st.nr 37 = i0 ∧ st.nr 14 = ∑ k ∈ Finset.range i, i0 * q ^ k) 0 b 2 (Nat.zero_le _) ?_ ?_
    · rintro i st _ _ ⟨⟨hV, -⟩, hb, h35, -⟩
      exact ⟨h35, hV (3, b) (by simp), hb⟩
    · intro i _ hi
      apply rt_sp_sym'
      rintro st ⟨⟨hV, hR⟩, hb, h35, h37, h14⟩
      have h6 := hV (6, q) (by simp)
      have hS : ∑ k ∈ Finset.range i, i0 * q ^ k < q ^ i :=
        rt_digsum_lt q i (fun _ => i0) (by omega) (fun _ _ => hi0q)
      have hS' : (∑ k ∈ Finset.range i, i0 * q ^ k) * q + i0 = ∑ k ∈ Finset.range (i + 1), i0 * q ^ k := by
        rw [Finset.sum_range_succ', Finset.sum_mul]; simp [pow_succ, mul_assoc]
      have hS2 := rt_digsum_lt q (i + 1) (fun _ => i0) (by omega) (fun _ _ => hi0q)
      have hp := hpw (i + 1) (by omega)
      refine ⟨hb, ?_, fun hb' hA => ?_⟩
      · simp [rt_symV, rt_sym, rt_M, rt_A, rt_wv, rt_simple, rt_eff, rt_setN, h14, h6, h37]
        omega
      · have k14 : (rt_sym [s, b, r, d] (.seq (rt_M (F := F) 14 14 6) (rt_A 14 14 37)) st).nr 14 =
            ∑ k ∈ Finset.range (i + 1), i0 * q ^ k := by
          simp [rt_sym, rt_M, rt_A, rt_eff, rt_setN, h14, h6, h37]; rw [← hS']
        have hn : ∀ j, j ≠ 14 →
            (rt_sym [s, b, r, d] (.seq (rt_M (F := F) 14 14 6) (rt_A 14 14 37)) st).nr j = st.nr j :=
          by intro j hj; simp [rt_sym, rt_M, rt_A, rt_eff, rt_setN, hj]
        have hbi := rt_Bd_inc (i := 35) (by decide) hb' (by omega)
          (by rw [hn 35 (by decide), h35]; exact hlt (i + 0) (by omega))
        refine ⟨hb', hbi, ⟨?_, ?_⟩, hbi, ?_, ?_, ?_⟩
        · intro p hp
          rw [rt_inc_nr _ _ _ (by decide)]
          have := (rt_Vals_agr (c := .seq (rt_M (F := F) 14 14 6) (rt_A 14 14 37)) rfl hA hV) p hp
          have hp1 : p.1 ≠ 35 ∧ p.1 ≠ 61 := by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
            rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl <;> simp
          rw [if_neg hp1.1, if_neg hp1.2]; exact this
        · have := rt_R0_agr (c := .seq (rt_M (F := F) 14 14 6) (rt_A 14 14 37)) rfl hA hR
          exact this
        · rw [rt_inc_nr _ _ _ (by decide), if_pos rfl, hn 35 (by decide), h35]
        · rw [rt_inc_nr _ _ _ (by decide), if_neg (by decide), if_neg (by decide), hn 37 (by decide),
            h37]
        · rw [rt_inc_nr _ _ _ (by decide), if_neg (by decide), if_neg (by decide), k14]
  have hR0V : ∀ st st' : rt_St F, rt_Agr (rt_cTab al 0) st st' →
      (rt_Vals [(12, (q ^ (s + b)) ^ r * q ^ r), (15, q ^ b / q), (11, (q ^ r) ^ d), (10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ st.nr 14 = ∑ k ∈ Finset.range b, i0 * q ^ k) →
      (rt_Vals [(12, (q ^ (s + b)) ^ r * q ^ r), (15, q ^ b / q), (11, (q ^ r) ^ d), (10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st' ∧ st'.nr 14 = ∑ k ∈ Finset.range b, i0 * q ^ k) := by
    rintro st st' hA ⟨hV, h14⟩
    have hn : ∀ j, j ≠ 37 → j ≠ 60 → j ≠ 61 → st'.nr j = st.nr j := by
      intro j h1 h2 h3
      exact hA.1 j (fun hm => by rcases rt_cTab_wn al 0 j hm with h | h | h <;> omega)
    refine ⟨fun p hp => ?_, by rw [hn 14 (by decide) (by decide) (by decide), h14]⟩
    have hp1 : p.1 ≠ 37 ∧ p.1 ≠ 60 ∧ p.1 ≠ 61 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp
    rw [hn _ hp1.1 hp1.2.1 hp1.2.2]; exact hV p hp
  have g11 : rt_Sp [s, b, r, d] B (rt_K (F := F) 48 1)
      (fun st => (rt_Vals [(12, (q ^ (s + b)) ^ r * q ^ r), (15, q ^ b / q), (11, (q ^ r) ^ d), (10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ rt_R0 st) ∧ rt_Bd B st ∧ st.nr 35 = b ∧ st.nr 37 = i0 ∧
        st.nr 14 = ∑ k ∈ Finset.range b, i0 * q ^ k)
      (fun st => (rt_Bd B st ∧ rt_R0 st ∧ st.fr 48 = 1 ∧
          ∀ e' < 0, st.fr (e' * 16 + 1) = al.getD e' 0) ∧
        (rt_Vals [(12, (q ^ (s + b)) ^ r * q ^ r), (15, q ^ b / q), (11, (q ^ r) ^ d), (10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ st.nr 14 = ∑ k ∈ Finset.range b, i0 * q ^ k)) 1 := by
    apply rt_sp_sym'
    rintro st ⟨⟨hV, hR⟩, hb, -, -, h14⟩
    refine ⟨hb, by simp [rt_symV, rt_K, rt_wv, rt_simple], fun hb' hA => ?_⟩
    refine ⟨⟨hb', ?_, by simp [rt_sym, rt_K, rt_eff, rt_setF], fun e' he' => by omega⟩,
      rt_Vals_agr rfl hA hV, by rw [rt_nr_agr (rt_notin_of rfl) hA, h14]⟩
    refine ⟨by rw [rt_out_agr rfl hA, hR.1], fun a ha => ?_⟩
    simp only [rt_sym, rt_K, rt_eff, rt_setF, Function.update_apply]
    rw [if_neg (by omega)]; exact hR.2 a ha
  have g12 := rt_sp_frame (rt_Tab_spec (ns := [s, b, r, d]) (B := B) al hqB al 0 (by simp)
    (by simp)) (R := fun st => rt_Vals [(12, (q ^ (s + b)) ^ r * q ^ r), (15, q ^ b / q), (11, (q ^ r) ^ d), (10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] st ∧ st.nr 14 = ∑ k ∈ Finset.range b, i0 * q ^ k) hR0V
  have hall := rt_sp_seq g1 (rt_sp_seq g2 (rt_sp_seq g3 (rt_sp_seq g4 (rt_sp_seq g5 (rt_sp_seq g6
    (rt_sp_seq g7 (rt_sp_seq g8 (rt_sp_seq g9 (rt_sp_seq g10 (rt_sp_seq g11 g12))))))))))
  unfold rt_cSetup
  refine rt_sp_conseq hall (fun st h => h) ?_ ?_
  · rintro st ⟨⟨hb, hR, h48, htab⟩, hV, h14⟩
    have v : ∀ j v, (j, v) ∈ [(12, (q ^ (s + b)) ^ r * q ^ r), (15, q ^ b / q), (11, (q ^ r) ^ d), (10, (q ^ (s + b)) ^ r), (13, q ^ s), (9, q ^ (s + b)), (16, s + b), (8, q ^ r), (7, q ^ b), (0, 0), (2, s), (3, b), (4, r), (5, d), (6, q)] → st.nr j = v := fun j v h => hV (j, v) h
    refine ⟨⟨v 0 0 (by simp only [List.mem_cons, true_or, or_true, hqdef]), v 2 s (by simp only [List.mem_cons, true_or, or_true, hqdef]), v 3 b (by simp only [List.mem_cons, true_or, or_true, hqdef]), v 4 r (by simp only [List.mem_cons, true_or, or_true, hqdef]), v 5 d (by simp only [List.mem_cons, true_or, or_true, hqdef]),
      v 6 q (by simp only [List.mem_cons, true_or, or_true, hqdef]), v 7 _ (by simp only [List.mem_cons, true_or, or_true, hqdef]), v 8 _ (by simp only [List.mem_cons, true_or, or_true, hqdef]), v 9 _ (by simp only [List.mem_cons, true_or, or_true, hqdef]), v 10 _ (by simp only [List.mem_cons, true_or, or_true, hqdef]),
      v 11 _ (by simp only [List.mem_cons, true_or, or_true, hqdef]), v 12 _ (by simp only [List.mem_cons, true_or, or_true, hqdef]), v 13 _ (by simp only [List.mem_cons, true_or, or_true, hqdef]), ?_, ?_, v 16 _ (by simp only [List.mem_cons, true_or, or_true, hqdef]), h48, htab⟩,
      hb, fun k hk2 hk8 o => ?_, hR.1⟩
    · rw [h14, rt_z0_eq]
    · rw [v 15 (q ^ b / q) (by simp)]
      have := Nat.pow_div (show 1 ≤ b from H.hb) (show 0 < q by omega)
      rw [pow_one] at this; exact this
    · rw [hR.2 _ (by omega)]; simp
  · simp only [rt_kSet, Nat.sub_zero, List.length_cons, hqdef]
    clear * -
    omega

def rt_kMain (q s b r d : ℕ) : ℕ :=
  rt_kSet q s b r d + rt_kPh0 q s b r d +
    q ^ s * (rt_kPh1 q s b r + rt_kCh q s b r d + rt_kOut b + 4) + 3

def rt_MI (al : List F) (s b r d B k : ℕ) (st : rt_St F) : Prop :=
  rt_Cst al s b r d st ∧ rt_Bd B st ∧ st.nr 20 = k ∧ rt_Reg st 3 (rt_DUPS al s b r d) ∧
  rt_Regs47 al s b r d (k * ((al.length ^ (s + b)) ^ r * al.length ^ r)) st ∧
  rt_Reg st 8 (rt_AMS al s b r d k) ∧ st.out = (rt_outData al s b r d k).reverse

theorem rt_G_ge_qs (q s b r d : ℕ) (hq : 1 ≤ q) : q ^ s ≤ rt_G q s b r d := by
  unfold rt_G
  have h1 : 1 ≤ (q ^ (s + b)) ^ r * (q ^ r) ^ d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : 1 ≤ q ^ r * q ^ b * (q ^ b) ^ d * q ^ (s + b) * q :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc q ^ s ≤ ((q ^ (s + b)) ^ r * (q ^ r) ^ d) * q ^ s := Nat.le_mul_of_pos_left _ h1
    _ ≤ ((q ^ (s + b)) ^ r * (q ^ r) ^ d * q ^ s) * (q ^ r * q ^ b * (q ^ b) ^ d * q ^ (s + b) * q) :=
        Nat.le_mul_of_pos_right _ h2
    _ = _ := by ring

theorem rt_Main_spec (al : List F) (s b r d B : ℕ) (H : rt_Hyp al s b r d B) :
    rt_Sp [s, b, r, d] B (rt_cMain al (rt_ix al 0))
      (fun st => st = ⟨fun _ => 0, fun _ => 0, []⟩)
      (fun st => rt_Bd B st ∧ st.out.reverse = rt_outData al s b r d (al.length ^ s))
      (rt_kMain al.length s b r d) := by
  have hqB : al.length ^ s + 1 ≤ B := by
    have := rt_G_ge_qs al.length s b r d (by have := H.q2; omega)
    have : 1 ≤ al.length ^ s := Nat.one_le_pow _ _ (by have := H.q2; omega)
    have := H.hB; omega
  have ok0 : rt_okC (rt_cPh0 (F := F)) = true := by rfl
  have ok1 : rt_okC (rt_cPh1 (F := F)) = true := by rfl
  have okC : rt_okC (rt_cChoose (F := F)) = true := by rfl
  have okO : rt_okC (rt_cOut (F := F)) = true := by rfl
  have w0 : rt_wr (rt_cPh0 (F := F)) = [3, 2] := by rfl
  have w1 : rt_wr (rt_cPh1 (F := F)) = [6, 7, 4, 5] := by rfl
  have wC : rt_wr (rt_cChoose (F := F)) = [] := by rfl
  have wO : rt_wr (rt_cOut (F := F)) = [8] := by rfl
  have o0 : rt_wo (rt_cPh0 (F := F)) = false := by rfl
  have o1 : rt_wo (rt_cPh1 (F := F)) = false := by rfl
  have oC : rt_wo (rt_cChoose (F := F)) = false := by rfl
  -- setup and phase 0
  have hS := rt_sp_conseq (rt_Setup_spec al s b r d B H) (fun _ h => h)
    (Q' := fun st => (rt_Cst al s b r d st ∧ rt_Bd B st ∧ rt_Reg st 2 (fun _ => False) ∧
        rt_Reg st 3 (fun _ => False)) ∧ rt_Reg st 4 (fun _ => False) ∧
        rt_Reg st 5 (fun _ => False) ∧ rt_Reg st 6 (fun _ => False) ∧
        rt_Reg st 7 (fun _ => False) ∧ rt_Reg st 8 (fun _ => False) ∧ st.out = [])
    (fun st ⟨hC, hb, hR, ho⟩ => ⟨⟨hC, hb, hR 2 (by omega) (by omega), hR 3 (by omega) (by omega)⟩,
      hR 4 (by omega) (by omega), hR 5 (by omega) (by omega), hR 6 (by omega) (by omega),
      hR 7 (by omega) (by omega), hR 8 (by omega) (by omega), ho⟩) le_rfl
  have hP0 := rt_sp_frame (rt_Ph0_spec al s b r d B H [s, b, r, d])
    (R := fun st => rt_Reg st 4 (fun _ => False) ∧ rt_Reg st 5 (fun _ => False) ∧
      rt_Reg st 6 (fun _ => False) ∧ rt_Reg st 7 (fun _ => False) ∧
      rt_Reg st 8 (fun _ => False) ∧ st.out = [])
    (by
      intro st st' hA ⟨h4, h5, h6, h7, h8, ho⟩
      exact ⟨rt_Reg_agr ok0 (by rw [w0]; decide) (by decide) hA h4,
        rt_Reg_agr ok0 (by rw [w0]; decide) (by decide) hA h5,
        rt_Reg_agr ok0 (by rw [w0]; decide) (by decide) hA h6,
        rt_Reg_agr ok0 (by rw [w0]; decide) (by decide) hA h7,
        rt_Reg_agr ok0 (by rw [w0]; decide) (by decide) hA h8,
        by rw [rt_out_agr o0 hA, ho]⟩)
  have hL : rt_Sp [s, b, r, d] B (rt_L (F := F) 20 0)
      (fun st => (rt_Cst al s b r d st ∧ rt_Bd B st ∧ rt_Reg st 3 (rt_DUPS al s b r d)) ∧
        rt_Reg st 4 (fun _ => False) ∧ rt_Reg st 5 (fun _ => False) ∧
        rt_Reg st 6 (fun _ => False) ∧ rt_Reg st 7 (fun _ => False) ∧
        rt_Reg st 8 (fun _ => False) ∧ st.out = [])
      (rt_MI al s b r d B 0) 1 := by
    apply rt_sp_basic rfl
    rintro st ⟨⟨hC, hb, h3⟩, h4, h5, h6, h7, h8, ho⟩
    refine ⟨hb, ?_⟩
    have hC' : rt_Cst al s b r d (rt_eff [s, b, r, d] st (.literal 20 0)) :=
      rt_Cst_agr (c := rt_L 20 0) rfl (rt_agr_of_exec (rt_Exec.basic (ns := [s, b, r, d])
        (B := B) rfl hb)) hC
    refine ⟨hC', ?_, by simp [rt_eff, rt_setN], h3, ⟨?_, ?_, ?_, ?_⟩, ?_, ho⟩
    · exact rt_Bd_setN hb (Nat.zero_le _)
    · exact rt_Reg_congr h4 (fun o => by simp [rt_BADS])
    · exact rt_Reg_congr h5 (fun o => by simp [rt_FREES])
    · exact rt_Reg_congr h6 (fun o => by simp [rt_CURS])
    · exact rt_Reg_congr h7 (fun o => by simp [rt_CURWS, rt_CURS])
    · exact rt_Reg_congr h8 (fun o => by simp [rt_AMS])
  -- the main loop
  have hbody : ∀ k, 0 ≤ k → k < al.length ^ s →
      rt_Sp [s, b, r, d] B (rt_seqs [rt_cPh1, rt_cChoose, rt_cOut]) (rt_MI al s b r d B k)
        (fun s1 => rt_Bd B s1 ∧ rt_Bd B (rt_inc s1 20) ∧ rt_MI al s b r d B (k + 1) (rt_inc s1 20))
        (rt_kPh1 al.length s b r + (rt_kCh al.length s b r d + rt_kOut b)) := by
    intro k _ hk
    have e1 := rt_sp_frame (rt_Ph1_spec al s b r d B H [s, b, r, d] k hk)
      (R := fun st => rt_Reg st 3 (rt_DUPS al s b r d) ∧ rt_Reg st 8 (rt_AMS al s b r d k) ∧
        st.out = (rt_outData al s b r d k).reverse)
      (by
        intro st st' hA ⟨h3, h8, ho⟩
        exact ⟨rt_Reg_agr ok1 (by rw [w1]; decide) (by decide) hA h3,
          rt_Reg_agr ok1 (by rw [w1]; decide) (by decide) hA h8, by rw [rt_out_agr o1 hA, ho]⟩)
    have e2 := rt_sp_frame (rt_Choose_spec al s b r d B H [s, b, r, d] k hk)
      (R := fun st => st.nr 20 = k ∧ rt_Reg st 8 (rt_AMS al s b r d k) ∧
        st.out = (rt_outData al s b r d k).reverse ∧ rt_Reg st 3 (rt_DUPS al s b r d) ∧
        rt_Regs47 al s b r d ((k + 1) * ((al.length ^ (s + b)) ^ r * al.length ^ r)) st)
      (by
        intro st st' hA ⟨h20, h8, ho, h3, h4, h5, h6, h7⟩
        exact ⟨by rw [rt_nr_agr (rt_notin_of rfl) hA, h20],
          rt_Reg_agr okC (by rw [wC]; decide) (by decide) hA h8, by rw [rt_out_agr oC hA, ho],
          rt_Reg_agr okC (by rw [wC]; decide) (by decide) hA h3,
          rt_Reg_agr okC (by rw [wC]; decide) (by decide) hA h4,
          rt_Reg_agr okC (by rw [wC]; decide) (by decide) hA h5,
          rt_Reg_agr okC (by rw [wC]; decide) (by decide) hA h6,
          rt_Reg_agr okC (by rw [wC]; decide) (by decide) hA h7⟩)
    have e3 := rt_sp_frame (rt_Out_spec al s b r d B H [s, b, r, d] k hk)
      (R := fun st => rt_Reg st 3 (rt_DUPS al s b r d) ∧
        rt_Regs47 al s b r d ((k + 1) * ((al.length ^ (s + b)) ^ r * al.length ^ r)) st)
      (by
        intro st st' hA ⟨h3, h4, h5, h6, h7⟩
        exact ⟨rt_Reg_agr okO (by rw [wO]; decide) (by decide) hA h3,
          rt_Reg_agr okO (by rw [wO]; decide) (by decide) hA h4,
          rt_Reg_agr okO (by rw [wO]; decide) (by decide) hA h5,
          rt_Reg_agr okO (by rw [wO]; decide) (by decide) hA h6,
          rt_Reg_agr okO (by rw [wO]; decide) (by decide) hA h7⟩)
    have hsel := rt_sel_eq_choose al H.nd H.all s b r d H.hs H.hb H.hr H.hd k hk
    have e1' := rt_sp_conseq e1 (P' := rt_MI al s b r d B k) ?_ (fun st h => h) le_rfl
    rotate_left
    · rintro st ⟨hC, hb, h20, h3, h47, h8, ho⟩
      exact ⟨⟨hC, hb, h20, h8, h47⟩, h3, h8, ho⟩
    have e2' := rt_sp_conseq e2 (fun st h => h) (fun st h => h) le_rfl
    have e3' := rt_sp_conseq e3 (fun st h => h)
      (Q' := fun s1 => rt_Bd B s1 ∧ rt_Bd B (rt_inc s1 20) ∧ rt_MI al s b r d B (k + 1) (rt_inc s1 20))
      ?_ le_rfl
    rotate_left
    · rintro st ⟨⟨hC, hb, h20, h8, ho⟩, h3, h47⟩
      have hbi : rt_Bd B (rt_inc st 20) := rt_Bd_inc (by decide) hb (by omega) (by omega)
      refine ⟨hb, hbi, rt_Cst_inc (by decide) (by decide) hC, hbi, ?_, h3, h47, h8, ho⟩
      rw [rt_inc_nr st 20 20 (by decide), if_pos rfl, h20]
    show rt_Sp _ _ (.seq rt_cPh1 (.seq rt_cChoose rt_cOut)) _ _ _
    refine rt_sp_seq e1' (rt_sp_seq (rt_sp_conseq e2' ?_ (fun st h => h) le_rfl)
      (rt_sp_conseq e3' ?_ (fun st h => h) le_rfl))
    · rintro st ⟨⟨hC, hb, h20, h47⟩, h3, h8, ho⟩
      exact ⟨⟨hC, hb, h20, h3, h47⟩, h20, h8, ho, h3, h47⟩
    · rintro st ⟨⟨hC, hb, h32⟩, h20, h8, ho, h3, h47⟩
      exact ⟨⟨hC, hb, h20, by rw [h32, hsel], h8, ho⟩, h3, h47⟩
  have hloop := rt_sp_loop (ns := [s, b, r, d]) (B := B) (i := 20) (n := 13)
    (body := rt_seqs [rt_cPh1, rt_cChoose, rt_cOut]) (rt_MI al s b r d B) 0 (al.length ^ s)
    _ (Nat.zero_le _)
    (by
      rintro k st _ _ ⟨hC, hb, h20, -⟩
      exact ⟨h20, hC.h13, hb⟩) hbody
  have hall := rt_sp_seq hS (rt_sp_seq hP0 (rt_sp_seq hL hloop))
  unfold rt_cMain
  simp only [rt_seqs]
  refine rt_sp_conseq hall (fun st h => h) ?_ ?_
  · rintro st ⟨hC, hb, h20, h3, h47, h8, ho⟩
    exact ⟨hb, by rw [ho, List.reverse_reverse]⟩
  · unfold rt_kMain; simp only [Nat.sub_zero]
    rw [← Nat.add_assoc (rt_kPh1 al.length s b r)]; omega
end Specs

end SubspaceEvasion312.Explicit.Dev.LG
end
end

section
set_option autoImplicit false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.LG
open SubspaceEvasion312.Explicit

section Final
variable {F : Type} [Field F]

def rt_szI : Instruction F → ℕ
  | .literal _ v => 2 + v
  | _ => 1

def rt_szB : rt_Cmd F → ℕ
  | .basic i => rt_szI i
  | .stR k _ _ => 18 + 1 + (2 + k) + 1 + 1
  | .ldR _ k _ => 18 + 1 + (2 + k) + 1 + 1
  | .seq a b => rt_szB a + rt_szB b
  | .ifN _ _ t e => rt_szB t + rt_szB e + 2
  | .ifF _ _ t e => rt_szB t + rt_szB e + 2
  | .loop _ _ b => rt_szB b + 6

theorem rt_size_le_szB (c : rt_Cmd F) : ∀ p, programSize (rt_comp c p) ≤ rt_szB c := by
  have hlit : ∀ d v : ℕ, instructionSize (Instruction.literal (F := F) d v) ≤ 2 + v := by
    intro d v; simp [instructionSize, Nat.log2_le_self]
  induction c with
  | basic i =>
    intro p
    cases i <;> simp only [rt_comp, rt_szB, rt_szI, programSize, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero] <;> first | exact hlit _ _ | simp [instructionSize]
  | stR k off src =>
    intro p
    simp only [rt_comp, rt_szB, programSize, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have h1 := hlit 61 16; have h2 := hlit 61 k
    simp only [instructionSize] at h1 h2 ⊢
    omega
  | ldR dst k off =>
    intro p
    simp only [rt_comp, rt_szB, programSize, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have h1 := hlit 61 16; have h2 := hlit 61 k
    simp only [instructionSize] at h1 h2 ⊢
    omega
  | seq a b iha ihb =>
    intro p
    simp only [rt_comp, rt_szB, programSize, List.map_append, List.sum_append] at *
    have := iha p; have := ihb (p + rt_len a); omega
  | ifN x y t e iht ihe =>
    intro p
    simp only [rt_comp, rt_szB, programSize, List.map_append, List.sum_append] at *
    have := iht (p + 1); have := ihe (p + 2 + rt_len t)
    simp [instructionSize]; omega
  | ifF x y t e iht ihe =>
    intro p
    simp only [rt_comp, rt_szB, programSize, List.map_append, List.sum_append] at *
    have := iht (p + 1); have := ihe (p + 2 + rt_len t)
    simp [instructionSize]; omega
  | loop i n b ih =>
    intro p
    simp only [rt_comp, rt_szB, programSize, List.map_append, List.sum_append] at *
    have := ih (p + 1); have h1 := hlit 61 1
    simp only [instructionSize] at h1
    simp [instructionSize]; omega

theorem rt_szB_tab (l : List F) : ∀ e, rt_szB (rt_cTab l e) ≤ l.length * (27 + e + l.length) + 2 := by
  induction l with
  | nil => intro e; simp [rt_cTab, rt_szB, rt_skip, rt_L, rt_szI]
  | cons a l ih =>
    intro e
    have := ih (e + 1)
    simp only [rt_cTab, rt_szB, rt_seqs, rt_L, rt_K, rt_szI, List.length_cons]
    nlinarith

theorem rt_szB_main (al : List F) (i0 : ℕ) :
    rt_szB (rt_cMain al i0) = 1198 + al.length + i0 + rt_szB (rt_cTab al 0) := by
  simp [rt_szB, rt_szI, rt_cMain, rt_cSetup, rt_cPow, rt_seqs, rt_L, rt_A, rt_M, rt_D, rt_Md, rt_K,
    rt_Sb, rt_FA, rt_FM, rt_skip, rt_cPh0, rt_cPh0t, rt_cPh0j, rt_cPh0m, rt_cPT, rt_cPTin,
    rt_cPTout, rt_cScan, rt_cPh1, rt_cPh1c, rt_cPh1r, rt_cChoose, rt_cChw, rt_cScore, rt_cSct,
    rt_cScEv, rt_cScAdd, rt_cScj, rt_cScjA, rt_cChkBad, rt_cChkFree, rt_cChkCur, rt_cOut, rt_cOutj]
  omega

theorem rt_progSize_le (al : List F) (i0 : ℕ) :
    programSize (rt_comp (rt_cMain al i0) 0) ≤ 5000 + 20 * al.length ^ 2 + i0 := by
  have h1 := rt_size_le_szB (rt_cMain al i0) 0
  have h2 := rt_szB_main al i0
  have h3 := rt_szB_tab al 0
  nlinarith

/-- The word bound dominates every value the program computes. -/
theorem rt_G_le (q s b r d : ℕ) (hq : 2 ≤ q) (hs : 0 < s) (hb : 0 < b) (hr : 0 < r)
    (hd : 0 < d) (hsbd : (s + b + d) * r < b * d) :
    64 * rt_G q s b r d ≤ localWordBound q s b r d := by
  have hG : rt_G q s b r d = q ^ ((s + b) * r + r * d + s + r + b + b * d + (s + b) + 1) := by
    unfold rt_G; ring
  have h64 : 64 ≤ q ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 6)
  have hexp : (s + b) * r + r * d + s + r + b + b * d + (s + b) + 1 + 6 ≤
      (s + b + r + d + 1) ^ 3 := by
    have h1 : (s + b) * r + r * d + s + r + b + b * d + (s + b) + 1 + 6 ≤ (s + b + r + d + 1) ^ 2 := by
      nlinarith
    have h2 : (s + b + r + d + 1) ^ 2 ≤ (s + b + r + d + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  unfold localWordBound
  rw [hG]
  calc 64 * q ^ ((s + b) * r + r * d + s + r + b + b * d + (s + b) + 1)
      ≤ q ^ 6 * q ^ ((s + b) * r + r * d + s + r + b + b * d + (s + b) + 1) :=
        Nat.mul_le_mul_right _ h64
    _ = q ^ ((s + b) * r + r * d + s + r + b + b * d + (s + b) + 1 + 6) := by ring
    _ ≤ q ^ ((s + b + r + d + 1) ^ 3) := Nat.pow_le_pow_right (by omega) hexp

theorem rt_sq_le_two_pow (n : ℕ) : n ^ 2 ≤ 2 * 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> simp
    · have h1 : 2 * n + 1 ≤ n ^ 2 := by nlinarith
      have e : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      rw [e, show 2 ^ (n + 1) = 2 ^ n * 2 from pow_succ 2 n]; omega

theorem rt_kPT_le1 (q s b r P : ℕ) (hsb1 : 1 ≤ s + b) (hrb : r ≤ s + b) (hP1 : s + b ≤ P)
    (hP2 : (s + b) ^ 2 ≤ 2 * P) (hP3 : (s + b) * q ≤ 2 * P) :
    rt_kPT q s b r + 70 ≤ 300 * P := by
  have e1 : rt_kPT q s b r = (s + b) * r * 22 + (s + b) * q * 13 + (s + b) * 30 + 10 := by
    unfold rt_kPT; ring
  have e2 : (s + b) * r ≤ (s + b) ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left _ hrb
  omega

theorem rt_kPT_le2 (q s b r : ℕ) (hsb : 1 ≤ s + b) :
    rt_kPT q s b r + 70 ≤ 110 * ((s + b) * (r + 1) * (q + 1)) := by
  have e1 : rt_kPT q s b r = (s + b) * r * 22 + (s + b) * q * 13 + (s + b) * 30 + 10 := by
    unfold rt_kPT; ring
  have e2 : (s + b) * (r + 1) * (q + 1) = (s + b) * r * q + (s + b) * r + (s + b) * q + (s + b) := by
    ring
  omega

theorem rt_aux1 (A X Q : ℕ) (hA : 1 ≤ A) (hQ : 1 ≤ Q) :
    A * (Q * (X + 50) + 10) + 10 ≤ A * Q * (X + 70) := by
  have h1 : A ≤ A * Q := Nat.le_mul_of_pos_right _ hQ
  have e1 : A * (Q * (X + 50) + 10) + 10 = A * Q * X + 50 * (A * Q) + 10 * A + 10 := by ring
  have e2 : A * Q * (X + 70) = A * Q * X + 70 * (A * Q) := by ring
  rw [e1, e2]; omega

theorem rt_aux2 (A Q d X : ℕ) (hA : 1 ≤ A) (hQ : 1 ≤ Q) (hd : 1 ≤ d) :
    A * (Q * (d * (X + 40) + 10) + 10) + 10 ≤ A * Q * d * (X + 70) := by
  have h1 : A ≤ A * Q := Nat.le_mul_of_pos_right _ hQ
  have h2 : A * Q ≤ A * Q * d := Nat.le_mul_of_pos_right _ hd
  have e1 : A * (Q * (d * (X + 40) + 10) + 10) + 10 = A * Q * d * X + 40 * (A * Q * d) +
    10 * (A * Q) + 10 * A + 10 := by ring
  have e2 : A * Q * d * (X + 70) = A * Q * d * X + 70 * (A * Q * d) := by ring
  rw [e1, e2]; omega

theorem rt_aux3 (A Q d QB : ℕ) (hA : 1 ≤ A) (hQ : 1 ≤ Q) (hd : 1 ≤ d) (hB : 1 ≤ QB) :
    (QB + 1) * (A * (Q * (54 * d + 40) + 10) + 10 + 10) + 10 ≤ 258 * d * (QB * A * Q) := by
  have h1 : A ≤ A * Q := Nat.le_mul_of_pos_right _ hQ
  have h2 : A * Q ≤ A * Q * d := Nat.le_mul_of_pos_right _ hd
  have h3 : A * (Q * (54 * d + 40) + 10) + 10 + 10 ≤ 124 * (A * Q * d) := by
    have e : A * (Q * (54 * d + 40) + 10) + 10 + 10 = 54 * (A * Q * d) + 40 * (A * Q) + 10 * A + 20 :=
      by ring
    rw [e]; omega
  have h4 : QB + 1 ≤ 2 * QB := by omega
  have h6 : 1 ≤ QB * (A * Q * d) := Nat.mul_pos hB (Nat.mul_pos (Nat.mul_pos hA hQ) hd)
  calc (QB + 1) * (A * (Q * (54 * d + 40) + 10) + 10 + 10) + 10
      ≤ 2 * QB * (124 * (A * Q * d)) + 10 * (QB * (A * Q * d)) :=
        Nat.add_le_add (Nat.mul_le_mul h4 h3) (by omega)
    _ = 258 * d * (QB * A * Q) := by ring

/-- The total cost fits the claimed bound. -/
theorem rt_cost_le (q s b r d : ℕ) (hq : 2 ≤ q) (hs : 0 < s) (hb : 0 < b) (hr : 0 < r)
    (hd : 0 < d) (hsbd : (s + b + d) * r < b * d) :
    5000 + 20 * q ^ 2 + q + 1 + (rt_kMain q s b r d + 1) ≤
      100000 * q ^ ((s + b) * (r + 1) + r * d) * d := by
  -- consequences of the constraint
  have hrb : r < b := by
    by_contra h; push_neg at h
    have : b * d ≤ (s + b + d) * r :=
      calc b * d ≤ (s + b + d) * b := by rw [mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
        _ ≤ (s + b + d) * r := Nat.mul_le_mul_left _ h
    omega
  have hsr : s + b + d ≤ (s + b + d) * r := Nat.le_mul_of_pos_right _ hr
  have hsb : s < b * d := by omega
  have hd2 : 2 ≤ d := by
    by_contra h
    have : d = 1 := by omega
    subst this; omega
  have hq0 : 0 < q := by omega
  -- the powers
  obtain ⟨QS, hQS⟩ : ∃ x, x = q ^ s := ⟨_, rfl⟩
  obtain ⟨QB, hQB⟩ : ∃ x, x = q ^ b := ⟨_, rfl⟩
  obtain ⟨QR, hQR⟩ : ∃ x, x = q ^ r := ⟨_, rfl⟩
  obtain ⟨Q1, hQ1⟩ : ∃ x, x = (q ^ (s + b)) ^ r := ⟨_, rfl⟩
  obtain ⟨Q2, hQ2⟩ : ∃ x, x = (q ^ r) ^ d := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ x, x = q ^ ((s + b) * (r + 1) + r * d) := ⟨_, rfl⟩
  have hM : M = QS * QB * Q1 * Q2 := by rw [hMdef, hQS, hQB, hQ1, hQ2]; ring
  have hQS1 : 1 ≤ QS := by rw [hQS]; exact Nat.one_le_pow _ _ hq0
  have hQB1 : 1 ≤ QB := by rw [hQB]; exact Nat.one_le_pow _ _ hq0
  have hQR1 : 1 ≤ QR := by rw [hQR]; exact Nat.one_le_pow _ _ hq0
  have hQ11 : 1 ≤ Q1 := by rw [hQ1]; exact Nat.one_le_pow _ _ (by positivity)
  have hQ21 : 1 ≤ Q2 := by rw [hQ2]; exact Nat.one_le_pow _ _ (by positivity)
  have hM1 : 1 ≤ M := by rw [hM]; exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hQS1 hQB1) hQ11) hQ21
  -- basic growth facts
  have hbq : b * q ≤ QB := by
    have h1 : b ≤ 2 ^ (b - 1) := by
      have := Nat.lt_two_pow_self (n := b - 1); omega
    have h2 : 2 ^ (b - 1) ≤ q ^ (b - 1) := Nat.pow_le_pow_left hq _
    have h3 : q ^ (b - 1) * q = QB := by rw [hQB, ← pow_succ]; congr 1; omega
    rw [← h3]; exact Nat.mul_le_mul_right q (h1.trans h2)
  have hr1 : r + 1 ≤ QR ^ (d - 1) := by
    have h1 : r + 1 ≤ 2 ^ r := Nat.lt_two_pow_self
    have h2 : 2 ^ r ≤ QR := by rw [hQR]; exact Nat.pow_le_pow_left hq _
    have h3 : QR ≤ QR ^ (d - 1) := Nat.le_self_pow (by omega) _
    omega
  have hQ2' : QR * QR ^ (d - 1) = Q2 := by rw [hQ2, hQR, ← pow_succ']; congr 1; omega
  have hn : ∀ n, 1 ≤ n → n ≤ q ^ n ∧ n ^ 2 ≤ 2 * q ^ n ∧ n * q ≤ 2 * q ^ n := by
    intro n hn1
    have h2 : 2 ^ n ≤ q ^ n := Nat.pow_le_pow_left hq _
    have h3 := rt_sq_le_two_pow n
    have h4 : n < 2 ^ n := Nat.lt_two_pow_self
    have h5 : 2 ^ (n - 1) * 2 = 2 ^ n := by rw [← pow_succ]; congr 1; omega
    have h6 : q ^ (n - 1) * q = q ^ n := by rw [← pow_succ]; congr 1; omega
    have h7 : 2 ^ (n - 1) ≤ q ^ (n - 1) := Nat.pow_le_pow_left hq _
    have h8 : n ≤ 2 ^ (n - 1) := by
      have := Nat.lt_two_pow_self (n := n - 1); omega
    refine ⟨by omega, by omega, ?_⟩
    have h9 : n * q ≤ q ^ (n - 1) * q := Nat.mul_le_mul_right q (h8.trans h7)
    omega
  -- the point-index cost
  have hPT1 : rt_kPT q s b r + 70 ≤ 300 * (QS * QB) := by
    obtain ⟨h1, h2, h3⟩ := hn (s + b) (by omega)
    have e : q ^ (s + b) = QS * QB := by rw [hQS, hQB, pow_add]
    rw [e] at h1 h2 h3
    exact rt_kPT_le1 q s b r _ (by omega) (by omega) h1 h2 h3
  have hPT2 : rt_kPT q s b r + 70 ≤ 110 * ((s + b) * (r + 1) * (q + 1)) :=
    rt_kPT_le2 q s b r (by omega)
  have hPT3 : (s + b) * (r + 1) * (q + 1) ≤ 4 * d * QB * QR ^ (d - 1) := by
    have h1 : s + b ≤ 2 * b * d := by
      have : b ≤ b * d := Nat.le_mul_of_pos_right _ hd
      rw [mul_assoc]; omega
    have h2 : q + 1 ≤ 2 * q := by omega
    calc (s + b) * (r + 1) * (q + 1) ≤ (2 * b * d) * (r + 1) * (2 * q) := by gcongr
      _ = 4 * d * (b * q) * (r + 1) := by ring
      _ ≤ 4 * d * QB * QR ^ (d - 1) := by gcongr
  -- phase 1
  have hP1 : QS * rt_kPh1 q s b r ≤ 440 * d * M := by
    unfold rt_kPh1
    rw [← hQ1, ← hQR]
    have h1 : Q1 * (QR * (rt_kPT q s b r + 50) + 10) + 10 ≤ Q1 * QR * (rt_kPT q s b r + 70) :=
      rt_aux1 _ _ _ hQ11 hQR1
    have h2 : Q1 * QR * (rt_kPT q s b r + 70) ≤ Q1 * QR * (110 * (4 * d * QB * QR ^ (d - 1))) := by
      apply Nat.mul_le_mul_left; omega
    have h3 : Q1 * QR * (110 * (4 * d * QB * QR ^ (d - 1))) = 440 * d * (QB * Q1 * Q2) := by
      rw [← hQ2']; ring
    calc QS * (Q1 * (QR * (rt_kPT q s b r + 50) + 10) + 10)
        ≤ QS * (440 * d * (QB * Q1 * Q2)) := Nat.mul_le_mul_left _ (le_trans h1 (le_trans h2 (le_of_eq h3)))
      _ = 440 * d * M := by rw [hM]; ring
  -- phase 0
  have hP0 : rt_kPh0 q s b r d ≤ 300 * d * M := by
    unfold rt_kPh0
    rw [← hQ1, ← hQ2]
    have h1 : Q1 * (Q2 * (d * (rt_kPT q s b r + 40) + 10) + 10) + 10 ≤
        Q1 * Q2 * d * (rt_kPT q s b r + 70) := rt_aux2 _ _ _ _ hQ11 hQ21 (by omega)
    calc Q1 * (Q2 * (d * (rt_kPT q s b r + 40) + 10) + 10) + 10
        ≤ Q1 * Q2 * d * (rt_kPT q s b r + 70) := h1
      _ ≤ Q1 * Q2 * d * (300 * (QS * QB)) := Nat.mul_le_mul_left _ hPT1
      _ = 300 * d * M := by rw [hM]; ring
  -- choose
  have hCh : QS * rt_kCh q s b r d ≤ 300 * d * M := by
    unfold rt_kCh rt_kSc
    rw [← hQ1, ← hQ2, ← hQB]
    have h2 : (QB + 1) * (Q1 * (Q2 * (54 * d + 40) + 10) + 10 + 10) + 10 ≤
        258 * d * (QB * Q1 * Q2) := rt_aux3 _ _ _ _ hQ11 hQ21 (by omega) hQB1
    calc QS * ((QB + 1) * (Q1 * (Q2 * (54 * d + 40) + 10) + 10 + 10) + 10)
        ≤ QS * (258 * d * (QB * Q1 * Q2)) := Nat.mul_le_mul_left _ h2
      _ = 258 * d * M := by rw [hM]; ring
      _ ≤ 300 * d * M := by gcongr; omega
  -- output
  have hOut : QS * (rt_kOut b + 4) ≤ 39 * d * M := by
    unfold rt_kOut
    have hbB : b ≤ QB := le_trans (Nat.le_mul_of_pos_right _ hq0) hbq
    have h1 : QS * (15 * b + 20 + 4) ≤ QS * (39 * QB) := Nat.mul_le_mul_left _ (by omega)
    have h2 : QS * QB ≤ M := by
      rw [hM, mul_assoc]; exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hQ11 hQ21)
    have h3 : M ≤ d * M := Nat.le_mul_of_pos_left _ (by omega)
    have e1 : QS * (39 * QB) = 39 * (QS * QB) := by ring
    have e2 : 39 * d * M = 39 * (d * M) := by ring
    omega
  -- setup and constants
  have hE : s + b + r + 2 ≤ (s + b) * (r + 1) + r * d := by
    have h1 : 3 * r ≤ (s + b) * r := Nat.mul_le_mul_right r (show 3 ≤ s + b by omega)
    have e : (s + b) * (r + 1) + r * d = (s + b) * r + (s + b) + r * d := by ring
    omega
  have hME : (s + b) * (r + 1) + r * d < M := by
    rw [hMdef]
    exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hq _)
  have hq2M : q ^ 2 ≤ M := by rw [hMdef]; exact Nat.pow_le_pow_right hq0 (by omega)
  have hqM : q ≤ M := le_trans (Nat.le_self_pow (by norm_num) q) hq2M
  have hSet : rt_kSet q s b r d ≤ 107 * d * M := by
    unfold rt_kSet
    have h3 : M ≤ d * M := Nat.le_mul_of_pos_left _ (by omega)
    have h4 : d ≤ d * M := Nat.le_mul_of_pos_right _ hM1
    have e2 : 107 * d * M = 107 * (d * M) := by ring
    omega
  -- total
  unfold rt_kMain
  rw [← hQS, ← hMdef]
  have : QS * (rt_kPh1 q s b r + rt_kCh q s b r d + rt_kOut b + 4) =
      QS * rt_kPh1 q s b r + QS * rt_kCh q s b r d + QS * (rt_kOut b + 4) := by ring
  rw [this]
  have hdM : M ≤ d * M := Nat.le_mul_of_pos_left _ (by omega)
  have : 100000 * M * d = 100000 * (d * M) := by ring
  rw [this]
  have : 440 * d * M = 440 * (d * M) := by ring
  have : 300 * d * M = 300 * (d * M) := by ring
  have : 39 * d * M = 39 * (d * M) := by ring
  have : 107 * d * M = 107 * (d * M) := by ring
  omega

end Final

theorem runtime_half : ∃ K : ℕ, 0 < K ∧
    ∀ (F : Type) [Field F] [Fintype F] (alphabet : List F),
      alphabet.Nodup → (∀ a : F, a ∈ alphabet) →
    ∃ P : Program F, ∀ s b r d : ℕ,
      0 < s → 0 < b → 0 < r → 0 < d → (s+b+d)*r < b*d →
      RunsWithin P [s,b,r,d] []
        (K * (Fintype.card F)^((s+b)*(r+1)+r*d) * d)
        (localWordBound (Fintype.card F) s b r d)
        (localTableData alphabet s b r d) := by
  refine ⟨100000, by norm_num, ?_⟩
  intro F _ _ al hnd hall
  classical
  refine ⟨(rt_comp (rt_cMain al (rt_ix al 0)) 0 ++ [Instruction.halt] : List (Instruction F)), ?_⟩
  intro s b r d hs hb hr hd hsbd
  have hcard : Fintype.card F = al.length := by
    rw [← List.toFinset_card_of_nodup hnd, ← Finset.card_univ]
    congr 1
    ext a; simp [hall a]
  have hq : 2 ≤ al.length := by
    rw [← hcard]; exact Fintype.one_lt_card
  rw [hcard]
  have H : rt_Hyp al s b r d (localWordBound al.length s b r d) :=
    ⟨hnd, hall, hq, hs, hb, hr, hd, rt_G_le _ _ _ _ _ hq hs hb hr hd hsbd⟩
  obtain ⟨n, st, hn, hex, hbd, hout⟩ := rt_Main_spec al s b r d _ H _ rfl
  have hrun := rt_run hex hbd
  refine ⟨n + 1, rt_mk (rt_len (rt_cMain al (rt_ix al 0))) st, ?_, hrun, ?_, rfl⟩
  · have h1 := rt_progSize_le al (rt_ix al 0)
    have h2 : rt_ix al 0 < al.length := by
      unfold rt_ix; exact List.idxOf_lt_length_iff.mpr (hall 0)
    have h3 := rt_cost_le al.length s b r d hq hs hb hr hd hsbd
    have h4 : programSize (rt_comp (rt_cMain al (rt_ix al 0)) 0 ++ [Instruction.halt]) =
        programSize (rt_comp (rt_cMain al (rt_ix al 0)) 0) + 1 := by
      simp [programSize, instructionSize]
    rw [h4]; omega
  · simp only [rt_mk]
    rw [hout, rt_tableData_eq al hnd hall s b r d hs hb]

end SubspaceEvasion312.Explicit.Dev.LG
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.LG
open SubspaceEvasion312.Explicit
open scoped BigOperators

/-! ### Enumeration lists -/

theorem ev_allVectors_eq {F : Type} (alphabet : List F) (n : ℕ) :
    allVectors alphabet n = allTuples alphabet n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allVectors, allTuples, ih]

theorem ev_nodup_flatMap_map {α β γ : Type} (l1 : List α) (l2 : List β) (g : α → β → γ)
    (hg : ∀ a a' c c', g a c = g a' c' → a = a' ∧ c = c') (h1 : l1.Nodup) (h2 : l2.Nodup) :
    (l1.flatMap fun a => l2.map (g a)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun a _ => h2.map (fun c c' h => (hg a a c c' h).2), ?_⟩
  refine h1.imp ?_
  intro a a' hne x hx hx'
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨c', _, h⟩ := List.mem_map.mp hx'
  exact hne (hg _ _ _ _ h).1.symm

theorem ev_nodup_allTuples {X : Type} (xs : List X) (h : xs.Nodup) (n : ℕ) :
    (allTuples xs n).Nodup := by
  induction n with
  | zero => exact List.nodup_singleton _
  | succ n ih =>
    exact ev_nodup_flatMap_map _ _ _
      (fun a a' c c' hh => ⟨by simpa using congrFun hh 0,
        funext fun i => by simpa using congrFun hh i.succ⟩) h ih

theorem ev_mem_allTuples {X : Type} (xs : List X) (hall : ∀ a, a ∈ xs) (n : ℕ)
    (t : Fin n → X) : t ∈ allTuples xs n := by
  induction n with
  | zero =>
    have : t = Fin.elim0 := funext (fun i => Fin.elim0 i)
    simp [allTuples, this]
  | succ n ih =>
    simp only [allTuples, List.mem_flatMap, List.mem_map]
    exact ⟨t 0, hall _, Fin.tail t, ih _, Fin.cons_self_tail t⟩

theorem ev_list_sum_eq {α : Type} [Fintype α] (l : List α) (hn : l.Nodup)
    (hall : ∀ a, a ∈ l) (f : α → ℚ) : (l.map f).sum = ∑ a, f a := by
  classical
  rw [← List.sum_toFinset f hn]
  congr
  ext a
  simp [hall]

/-! ### The score as a finite sum over events -/

section
variable {F : Type} [Field F] [Fintype F] {s b : ℕ}

theorem ev_score_eq (alphabet : List F) (hnd : alphabet.Nodup) (hall : ∀ a : F, a ∈ alphabet)
    (r d : ℕ) (A : List (Vec F s × Vec F b)) :
    conditionalScore alphabet r d A =
      ∑ basis : Fin r → Vec F s × Vec F b, ∑ coeff : Fin d → Vec F r,
        eventProbability A (eventPoints basis coeff) := by
  have hv : ∀ n, (allVectors alphabet n).Nodup := fun n => by
    rw [ev_allVectors_eq]; exact ev_nodup_allTuples _ hnd n
  have hva : ∀ n (v : Vec F n), v ∈ allVectors alphabet n := fun n v => by
    rw [ev_allVectors_eq]; exact ev_mem_allTuples _ hall n v
  set pairs := (allVectors alphabet s).flatMap fun x =>
    (allVectors alphabet b).map fun y => (x, y) with hpairs
  have hpn : pairs.Nodup := ev_nodup_flatMap_map _ _ _
    (fun a a' c c' h => Prod.mk.inj h) (hv s) (hv b)
  have hpa : ∀ z, z ∈ pairs := fun z => by
    rw [hpairs, List.mem_flatMap]
    exact ⟨z.1, hva _ _, List.mem_map.mpr ⟨z.2, hva _ _, rfl⟩⟩
  unfold conditionalScore
  simp only []
  rw [← hpairs]
  rw [ev_list_sum_eq _ (ev_nodup_allTuples _ hpn r) (ev_mem_allTuples _ hpa r)]
  refine Finset.sum_congr rfl (fun basis _ => ?_)
  rw [ev_list_sum_eq _ (ev_nodup_allTuples _ (hv r) d) (ev_mem_allTuples _ (hva r) d)]

/-- Number of points whose first coordinate is unassigned. -/
def ev_un (A pts : List (Vec F s × Vec F b)) : ℕ := by
  classical exact pts.countP (fun z => decide (z.1 ∉ A.map Prod.fst))

def ev_cons (A pts : List (Vec F s × Vec F b)) : Prop :=
  ∀ z ∈ pts, ∀ w ∈ A, z.1 = w.1 → z.2 = w.2

theorem ev_prob_pos (A pts : List (Vec F s × Vec F b))
    (h : (pts.map Prod.fst).Nodup ∧ ev_cons A pts) :
    eventProbability A pts = 1 / (Fintype.card F : ℚ) ^ (b * ev_un A pts) := by
  unfold ev_cons at h
  unfold eventProbability
  rw [if_pos h]
  unfold ev_un
  rw [List.countP_eq_length_filter]
  congr 4
  apply List.filter_congr
  intro z _
  classical
  have key : (A.any fun w => decide (w.1 = z.1)) = true ↔ z.1 ∈ A.map Prod.fst := by
    simp only [List.any_eq_true, decide_eq_true_eq, List.mem_map]
  by_cases hm : z.1 ∈ A.map Prod.fst
  · rw [key.mpr hm]; simp [hm]
  · rw [Bool.eq_false_iff.mpr (fun h => hm (key.mp h))]; simp [hm]

theorem ev_prob_zero (A pts : List (Vec F s × Vec F b))
    (h : ¬ ((pts.map Prod.fst).Nodup ∧ ev_cons A pts)) :
    eventProbability A pts = 0 := by
  unfold ev_cons at h
  unfold eventProbability
  rw [if_neg h]

theorem ev_prob_nonneg (A pts : List (Vec F s × Vec F b)) : 0 ≤ eventProbability A pts := by
  by_cases h : (pts.map Prod.fst).Nodup ∧ ev_cons A pts
  · rw [ev_prob_pos A pts h]; positivity
  · rw [ev_prob_zero A pts h]

theorem ev_cons_append (A pts : List (Vec F s × Vec F b)) (x : Vec F s) (w : Vec F b) :
    ev_cons (A ++ [(x, w)]) pts ↔ ev_cons A pts ∧ ∀ z ∈ pts, z.1 = x → z.2 = w := by
  unfold ev_cons
  constructor
  · intro h
    exact ⟨fun z hz v hv => h z hz v (List.mem_append_left _ hv),
      fun z hz hzx => h z hz (x, w) (by simp) hzx⟩
  · rintro ⟨h1, h2⟩ z hz v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact h1 z hz v hv
    · rw [List.mem_singleton] at hv; subst hv; exact h2 z hz

theorem ev_un_append_of_not_mem (A pts : List (Vec F s × Vec F b)) (x : Vec F s)
    (w : Vec F b) (hx : x ∉ pts.map Prod.fst) :
    ev_un (A ++ [(x, w)]) pts = ev_un A pts := by
  classical
  unfold ev_un
  apply List.countP_congr
  intro z hz
  have hzx : z.1 ≠ x := fun h => hx (List.mem_map.mpr ⟨z, hz, h⟩)
  simp [hzx]

theorem ev_un_append_of_mem (A pts : List (Vec F s × Vec F b)) (z0 : Vec F s × Vec F b)
    (hz0 : z0 ∈ pts) (hN : (pts.map Prod.fst).Nodup) (hx : z0.1 ∉ A.map Prod.fst)
    (w : Vec F b) :
    ev_un A pts = ev_un (A ++ [(z0.1, w)]) pts + 1 := by
  classical
  unfold ev_un
  have hperm := List.perm_cons_erase hz0
  rw [hperm.countP_eq, hperm.countP_eq, List.countP_cons, List.countP_cons]
  have hrest : ∀ z ∈ pts.erase z0, z.1 ≠ z0.1 := by
    intro z hz hzx
    have hzp : z ∈ pts := List.mem_of_mem_erase hz
    have : z = z0 := List.inj_on_of_nodup_map hN hzp hz0 hzx
    subst this
    exact (hN.of_map _).not_mem_erase hz
  have hc : (pts.erase z0).countP (fun z => decide (z.1 ∉ A.map Prod.fst)) =
      (pts.erase z0).countP (fun z => decide (z.1 ∉ (A ++ [(z0.1, w)]).map Prod.fst)) := by
    apply List.countP_congr
    intro z hz
    simp [hrest z hz]
  rw [hc]
  simp [hx]

theorem ev_avg_event (A : List (Vec F s × Vec F b)) (x : Vec F s)
    (hx : x ∉ A.map Prod.fst) (pts : List (Vec F s × Vec F b)) :
    ∑ w : Vec F b, eventProbability (A ++ [(x, w)]) pts
      = (Fintype.card F : ℚ) ^ b * eventProbability A pts := by
  classical
  by_cases hN : (pts.map Prod.fst).Nodup
  · by_cases hxp : x ∈ pts.map Prod.fst
    · obtain ⟨z0, hz0, rfl⟩ := List.mem_map.mp hxp
      by_cases hC : ev_cons A pts
      · have huniq : ∀ z ∈ pts, z.1 = z0.1 → z.2 = z0.2 := fun z hz hzx => by
          rw [List.inj_on_of_nodup_map hN hz hz0 hzx]
        rw [Finset.sum_eq_single z0.2]
        · rw [ev_prob_pos _ _ ⟨hN, (ev_cons_append A pts z0.1 z0.2).mpr ⟨hC, huniq⟩⟩,
            ev_prob_pos _ _ ⟨hN, hC⟩, ev_un_append_of_mem A pts z0 hz0 hN hx z0.2]
          have hq : (Fintype.card F : ℚ) ≠ 0 := by
            have := Fintype.card_pos (α := F); positivity
          rw [mul_add, mul_one, pow_add]
          field_simp
        · intro w _ hw
          apply ev_prob_zero
          rintro ⟨_, hC'⟩
          exact hw (((ev_cons_append A pts z0.1 w).mp hC').2 z0 hz0 rfl).symm
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [ev_prob_zero A pts (fun h => hC h.2), mul_zero]
        apply Finset.sum_eq_zero
        intro w _
        apply ev_prob_zero
        rintro ⟨_, hC'⟩
        exact hC ((ev_cons_append A pts z0.1 w).mp hC').1
    · have hsame : ∀ w : Vec F b, eventProbability (A ++ [(x, w)]) pts = eventProbability A pts := by
        intro w
        have hiff : ev_cons (A ++ [(x, w)]) pts ↔ ev_cons A pts := by
          rw [ev_cons_append]
          constructor
          · exact fun h => h.1
          · intro h
            exact ⟨h, fun z hz hzx => absurd (List.mem_map.mpr ⟨z, hz, hzx⟩) hxp⟩
        by_cases hC : ev_cons A pts
        · rw [ev_prob_pos _ _ ⟨hN, hiff.mpr hC⟩, ev_prob_pos _ _ ⟨hN, hC⟩,
            ev_un_append_of_not_mem A pts x w hxp]
        · rw [ev_prob_zero _ _ (fun h => hC (hiff.mp h.2)), ev_prob_zero _ _ (fun h => hC h.2)]
      simp only [hsame, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
        Fintype.card_fin]
      push_cast
      ring
  · rw [ev_prob_zero A pts (fun h => hN h.1), mul_zero]
    exact Finset.sum_eq_zero (fun w _ => ev_prob_zero _ _ (fun h => hN h.1))

theorem ev_avg_score (alphabet : List F) (hnd : alphabet.Nodup) (hall : ∀ a : F, a ∈ alphabet)
    (r d : ℕ) (A : List (Vec F s × Vec F b)) (x : Vec F s) (hx : x ∉ A.map Prod.fst) :
    ∑ w : Vec F b, conditionalScore alphabet r d (A ++ [(x, w)])
      = (Fintype.card F : ℚ) ^ b * conditionalScore alphabet r d A := by
  simp only [ev_score_eq alphabet hnd hall]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun basis _ => ?_)
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun coeff _ => ev_avg_event A x hx _)

theorem ev_foldl_min {β : Type} (S : β → ℚ) (L : List β) (init : β) :
    S (L.foldl (fun best w => if S w < S best then w else best) init) ≤ S init ∧
      ∀ w ∈ L, S (L.foldl (fun best w => if S w < S best then w else best) init) ≤ S w := by
  induction L generalizing init with
  | nil => simp
  | cons w L ih =>
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2⟩ := ih (if S w < S init then w else init)
    have h3 : S (if S w < S init then w else init) ≤ S init ∧
        S (if S w < S init then w else init) ≤ S w := by
      split_ifs with h
      · exact ⟨h.le, le_rfl⟩
      · exact ⟨le_rfl, not_lt.mp h⟩
    refine ⟨h1.trans h3.1, ?_⟩
    rintro w' (rfl | hw')
    · exact h1.trans h3.2
    · exact h2 w' hw'

theorem ev_choose_le (alphabet : List F) (hnd : alphabet.Nodup) (hall : ∀ a : F, a ∈ alphabet)
    (r d : ℕ) (A : List (Vec F s × Vec F b)) (x : Vec F s) (hx : x ∉ A.map Prod.fst) :
    conditionalScore alphabet r d (A ++ [(x, chooseValue alphabet r d A x)])
      ≤ conditionalScore alphabet r d A := by
  set S : Vec F b → ℚ := fun w => conditionalScore alphabet r d (A ++ [(x, w)]) with hS
  have hmin : ∀ w, S (chooseValue alphabet r d A x) ≤ S w := by
    intro w
    have hw : w ∈ allVectors alphabet b := by
      rw [ev_allVectors_eq]; exact ev_mem_allTuples _ hall b w
    exact (ev_foldl_min S (allVectors alphabet b) 0).2 w hw
  have havg := ev_avg_score alphabet hnd hall r d A x hx
  have hsum : ∑ _w : Vec F b, S (chooseValue alphabet r d A x) ≤ ∑ w : Vec F b, S w :=
    Finset.sum_le_sum (fun w _ => hmin w)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin] at hsum
  have hq : (0 : ℚ) < (Fintype.card F : ℚ) ^ b := by
    have := Fintype.card_pos (α := F); positivity
  push_cast at hsum
  have : (Fintype.card F : ℚ) ^ b * S (chooseValue alphabet r d A x)
      ≤ (Fintype.card F : ℚ) ^ b * conditionalScore alphabet r d A := by
    rw [← havg]; exact hsum
  exact le_of_mul_le_mul_left this hq

theorem ev_foldl_fst (alphabet : List F) (r d : ℕ) (L : List (Vec F s))
    (A : List (Vec F s × Vec F b)) :
    (L.foldl (fun assigned x => assigned ++ [(x, chooseValue alphabet r d assigned x)]) A).map
      Prod.fst = A.map Prod.fst ++ L := by
  induction L generalizing A with
  | nil => simp
  | cons x L ih => simp [ih]

theorem ev_foldl_score (alphabet : List F) (hnd : alphabet.Nodup) (hall : ∀ a : F, a ∈ alphabet)
    (r d : ℕ) (L : List (Vec F s)) (hL : L.Nodup) (A : List (Vec F s × Vec F b))
    (hA : ∀ y ∈ L, y ∉ A.map Prod.fst) :
    conditionalScore alphabet r d
      (L.foldl (fun assigned x => assigned ++ [(x, chooseValue alphabet r d assigned x)]) A)
      ≤ conditionalScore alphabet r d A := by
  induction L generalizing A with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons]
    have hx : x ∉ A.map Prod.fst := hA x List.mem_cons_self
    refine (ih (List.nodup_cons.mp hL).2 _ ?_).trans
      (ev_choose_le alphabet hnd hall r d A x hx)
    intro y hy hyA
    rw [List.map_append, List.mem_append] at hyA
    rcases hyA with h | h
    · exact hA y (List.mem_cons_of_mem _ hy) h
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
      subst h
      exact (List.nodup_cons.mp hL).1 hy

theorem ev_score_nil_lt (alphabet : List F) (hnd : alphabet.Nodup) (hall : ∀ a : F, a ∈ alphabet)
    (r d : ℕ) (hsbd : (s+b+d)*r < b*d) :
    conditionalScore alphabet r d ([] : List (Vec F s × Vec F b)) < 1 := by
  rw [ev_score_eq alphabet hnd hall]
  set q : ℚ := (Fintype.card F : ℚ) with hqdef
  have hq1 : (1 : ℚ) < q := by
    have := Fintype.one_lt_card (α := F); rw [hqdef]; exact_mod_cast this
  have hq0 : (0 : ℚ) < q := by linarith
  have hle : ∀ (basis : Fin r → Vec F s × Vec F b) (coeff : Fin d → Vec F r),
      eventProbability ([] : List (Vec F s × Vec F b)) (eventPoints basis coeff)
        ≤ 1 / q ^ (b * d) := by
    intro basis coeff
    by_cases h : ((eventPoints basis coeff).map Prod.fst).Nodup ∧
        ev_cons ([] : List (Vec F s × Vec F b)) (eventPoints basis coeff)
    · rw [ev_prob_pos _ _ h]
      have : ev_un ([] : List (Vec F s × Vec F b)) (eventPoints basis coeff) = d := by
        unfold ev_un eventPoints
        simp
      rw [this]
    · rw [ev_prob_zero _ _ h]; positivity
  calc (∑ basis : Fin r → Vec F s × Vec F b, ∑ coeff : Fin d → Vec F r,
        eventProbability ([] : List (Vec F s × Vec F b)) (eventPoints basis coeff))
      ≤ ∑ _basis : Fin r → Vec F s × Vec F b, ∑ _coeff : Fin d → Vec F r, 1 / q ^ (b * d) :=
        Finset.sum_le_sum (fun basis _ => Finset.sum_le_sum (fun coeff _ => hle basis coeff))
    _ = q ^ ((s + b + d) * r) / q ^ (b * d) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
          Fintype.card_prod, Fintype.card_fin]
        push_cast
        rw [← hqdef]
        rw [show (s + b + d) * r = s * r + b * r + r * d by ring]
        simp only [pow_add, mul_pow, ← pow_mul]
        ring
    _ < 1 := by
        rw [div_lt_one (by positivity)]
        exact pow_lt_pow_right₀ hq1 hsbd

theorem ev_table_lt (alphabet : List F) (hnd : alphabet.Nodup) (hall : ∀ a : F, a ∈ alphabet)
    (s b r d : ℕ) (hsbd : (s+b+d)*r < b*d) :
    conditionalScore alphabet r d (localTable alphabet s b r d) < 1 := by
  unfold localTable
  refine lt_of_le_of_lt ?_ (ev_score_nil_lt (s := s) (b := b) alphabet hnd hall r d hsbd)
  refine ev_foldl_score alphabet hnd hall r d _ ?_ [] (fun y _ h => by simp at h)
  rw [ev_allVectors_eq]; exact ev_nodup_allTuples _ hnd s

theorem ev_table_fst (alphabet : List F) (s b r d : ℕ) :
    (localTable alphabet s b r d).map Prod.fst = allVectors alphabet s := by
  unfold localTable
  rw [ev_foldl_fst]
  simp

theorem ev_find_getD {α β : Type} (l : List (α × β)) (hl : (l.map Prod.fst).Nodup)
    (w : α × β) (hw : w ∈ l) (p : α × β → Bool) (hp : ∀ z, p z = true ↔ z.1 = w.1)
    (y0 : β) : ((l.find? p).map Prod.snd).getD y0 = w.2 := by
  cases h : l.find? p with
  | none =>
    exact absurd ((hp w).mpr rfl) (List.find?_eq_none.mp h w hw)
  | some w' =>
    have hw' := List.mem_of_find?_eq_some h
    have hpw := List.find?_some h
    have : w' = w := List.inj_on_of_nodup_map hl hw' hw ((hp w').mp hpw)
    simp [this]

theorem ev_localFunction (alphabet : List F) (hnd : alphabet.Nodup) (s b r d : ℕ)
    (w : Vec F s × Vec F b) (hw : w ∈ localTable alphabet s b r d) :
    localFunction alphabet s b r d w.1 = w.2 := by
  have hl : ((localTable alphabet s b r d).map Prod.fst).Nodup := by
    rw [ev_table_fst, ev_allVectors_eq]; exact ev_nodup_allTuples _ hnd s
  unfold localFunction
  exact ev_find_getD _ hl w hw _ (fun z => by simp) 0

end

/-- The algebraic half of Theorem 9: the conditional-expectation function has an evasive graph. -/
theorem evasive_half (F : Type) [Field F] [Fintype F] (alphabet : List F)
    (hnd : alphabet.Nodup) (hall : ∀ a : F, a ∈ alphabet) (s b r d : ℕ)
    (hs : 0 < s) (hb : 0 < b) (hr : 0 < r) (hd : 0 < d) (hsbd : (s+b+d)*r < b*d) :
    Evasive (F := F) (graph (localFunction alphabet s b r d)) r (d-1) := by
  classical
  intro U hU
  set T := localTable alphabet s b r d with hT
  set G : Set (Vec F s × Vec F b) := graph (localFunction alphabet s b r d) ∩ (U : Set _)
    with hG
  have hfin : G.Finite := Set.toFinite G
  refine ⟨hfin, ?_⟩
  by_contra hcon
  have hd' : d ≤ G.ncard := by omega
  rw [Set.ncard_eq_toFinset_card G hfin] at hd'
  obtain ⟨e⟩ : Nonempty (Fin d ↪ hfin.toFinset) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hd')
  set pts : Fin d → Vec F s × Vec F b := fun j => (e j : Vec F s × Vec F b) with hpts
  have hptsG : ∀ j, pts j ∈ G := fun j => hfin.mem_toFinset.mp (e j).2
  have hinj : Function.Injective pts := fun i j h => e.injective (Subtype.ext h)
  have hgr : ∀ j, (pts j).2 = localFunction alphabet s b r d (pts j).1 := fun j => (hptsG j).1
  -- a spanning family of `U` with `r` members
  have hkr : Module.finrank F U ≤ r := hU
  let B := Module.finBasis F U
  let basis : Fin r → Vec F s × Vec F b := fun i =>
    if h : (i : ℕ) < Module.finrank F U then (B ⟨i, h⟩ : Vec F s × Vec F b) else 0
  let cf : U → Vec F r := fun u i =>
    if h : (i : ℕ) < Module.finrank F U then B.repr u ⟨i, h⟩ else 0
  have hspan : ∀ u : U, ∑ i : Fin r, cf u i • basis i = (u : Vec F s × Vec F b) := by
    intro u
    have h1 : ∑ i : Fin r, cf u i • basis i =
        ∑ j : Fin (Module.finrank F U), B.repr u j • (B j : Vec F s × Vec F b) := by
      symm
      apply Fintype.sum_of_injective (Fin.castLE hkr) (Fin.castLE_injective hkr)
      · intro i hi
        have : ¬ (i : ℕ) < Module.finrank F U := fun h => hi ⟨⟨i, h⟩, rfl⟩
        simp [cf, basis, this]
      · intro j
        simp [cf, basis, j.isLt]
    rw [h1]
    have h2 : ((∑ j, B.repr u j • B j : U) : Vec F s × Vec F b) = u := by rw [B.sum_repr]
    rw [← h2, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  let coeff : Fin d → Vec F r := fun j => cf ⟨pts j, (hptsG j).2⟩
  have hev : eventPoints basis coeff = List.ofFn pts := by
    unfold eventPoints
    congr 1
    funext j
    exact hspan _
  have hone : eventProbability T (eventPoints basis coeff) = 1 := by
    rw [hev]
    have hN : ((List.ofFn pts).map Prod.fst).Nodup := by
      rw [List.map_ofFn, List.nodup_ofFn]
      intro i j h
      apply hinj
      have h1 : (pts i).1 = (pts j).1 := h
      exact Prod.ext h1 (by rw [hgr i, hgr j, h1])
    have hC : ev_cons T (List.ofFn pts) := by
      intro z hz w hw hzw
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
      rw [hgr j, hzw]
      exact ev_localFunction alphabet hnd s b r d w hw
    rw [ev_prob_pos _ _ ⟨hN, hC⟩]
    have hu : ev_un T (List.ofFn pts) = 0 := by
      unfold ev_un
      rw [List.countP_eq_zero]
      intro z _
      have : z.1 ∈ T.map Prod.fst := by
        rw [hT, ev_table_fst, ev_allVectors_eq]; exact ev_mem_allTuples _ hall s _
      simp [this]
    rw [hu]
    simp
  have hge : 1 ≤ conditionalScore alphabet r d T := by
    rw [ev_score_eq alphabet hnd hall]
    have h1 : eventProbability T (eventPoints basis coeff) ≤
        ∑ coeff' : Fin d → Vec F r, eventProbability T (eventPoints basis coeff') :=
      Finset.single_le_sum (f := fun c => eventProbability T (eventPoints basis c))
        (fun c _ => ev_prob_nonneg _ _) (Finset.mem_univ coeff)
    have h2 : (∑ coeff' : Fin d → Vec F r, eventProbability T (eventPoints basis coeff')) ≤
        ∑ basis' : Fin r → Vec F s × Vec F b, ∑ coeff' : Fin d → Vec F r,
          eventProbability T (eventPoints basis' coeff') :=
      Finset.single_le_sum
        (f := fun bs => ∑ coeff' : Fin d → Vec F r, eventProbability T (eventPoints bs coeff'))
        (fun _ _ => Finset.sum_nonneg (fun _ _ => ev_prob_nonneg _ _)) (Finset.mem_univ basis)
    linarith
  have hlt := ev_table_lt alphabet hnd hall s b r d hsbd
  rw [← hT] at hlt
  linarith

end SubspaceEvasion312.Explicit.Dev.LG
end
end

section
set_option autoImplicit false

namespace SubspaceEvasion312.Explicit
theorem chk_local_graph :
    ∃ K : ℕ, 0 < K ∧
    ∀ (F : Type) [Field F] [Fintype F] (alphabet : List F),
      alphabet.Nodup → (∀ a : F, a ∈ alphabet) →
    ∃ P : Program F, ∀ s b r d : ℕ,
      0 < s → 0 < b → 0 < r → 0 < d → (s+b+d)*r < b*d →
      Evasive (F := F) (graph (localFunction alphabet s b r d)) r (d-1) ∧
      RunsWithin P [s,b,r,d] []
        (K * (Fintype.card F)^((s+b)*(r+1)+r*d) * d)
        (localWordBound (Fintype.card F) s b r d)
        (localTableData alphabet s b r d) := by
  obtain ⟨K, hK, h⟩ := Dev.LG.runtime_half
  refine ⟨K, hK, fun F _ _ alphabet hnd hall => ?_⟩
  obtain ⟨P, hP⟩ := h F alphabet hnd hall
  exact ⟨P, fun s b r d hs hb hr hd hsbd =>
    ⟨Dev.LG.evasive_half F alphabet hnd hall s b r d hs hb hr hd hsbd, hP s b r d hs hb hr hd hsbd⟩⟩
end SubspaceEvasion312.Explicit
end

theorem solution : type_of% @SubspaceEvasion312.Explicit.chk_local_graph := @SubspaceEvasion312.Explicit.chk_local_graph

-- Prove2me | solution 1 for SubspaceEvasion312.Explicit.explicit_subspace_evasive_sets
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:33:34.69641+00:00
-- url     : https://prove2.me/submissions/f596b2db-d9ab-42df-9768-826ba5476943
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SubspaceEvasion312_Explicit_construction
import Theorems.Thm_SubspaceEvasion312_Explicit_local_graph
import Theorems.Thm_SubspaceEvasion312_Explicit_local_to_global
import Theorems.Thm_SubspaceEvasion312_Explicit_quadratic_code_family
import Theorems.Thm_SubspaceEvasion312_Explicit_logarithmic_code_family

section
set_option autoImplicit false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal
open SubspaceEvasion312.Explicit

/-- Regroup `t` consecutive blocks of length `s` into one block of length `t*s`
(the flattened word is unchanged). -/
def regroup {F : Type} {s t m : ℕ} (x : Blocks F s (t * m)) : Blocks F (t * s) m :=
  fun i j =>
    have hs : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; simpa using j.2)
    have h1 : t * i.1 + j.1 / s < t * m := by
      have : j.1 / s < t := (Nat.div_lt_iff_lt_mul hs).2 (by simpa [Nat.mul_comm] using j.2)
      have : t * i.1 + t ≤ t * m := by
        have := i.2; nlinarith
      omega
    x ⟨t * i.1 + j.1 / s, h1⟩ ⟨j.1 % s, Nat.mod_lt _ hs⟩

def regroupL (F : Type) [Field F] (s t m : ℕ) : Blocks F s (t * m) →ₗ[F] Blocks F (t * s) m where
  toFun := regroup
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Zero padding of a message. -/
def padL (F : Type) [Field F] (k k' : ℕ) : Vec F k →ₗ[F] Vec F k' where
  toFun x i := if h : i.1 < k then x ⟨i.1, h⟩ else 0
  map_add' x y := by funext i; by_cases h : i.1 < k <;> simp [h]
  map_smul' c x := by funext i; by_cases h : i.1 < k <;> simp [h]

/-- `m(N) = ⌊ (num/den) N / b ⌋`. -/
def mN (num den b N : ℕ) : ℕ := num * N / (den * b)

def kN (num den b N : ℕ) : ℕ := N - b * mN num den b N

/-- The encoder used at length `N`: pad the message, encode with the family at `t*m(N)`,
regroup. -/
def encN {F : Type} [Field F] {s : ℕ} (kf : ℕ → ℕ) (E : ∀ m, Vec F (kf m) →ₗ[F] Blocks F s m)
    (t b num den N : ℕ) :
    Vec F (kN num den b N) →ₗ[F] Blocks F (t * s) (mN num den b N) :=
  regroupL F s t (mN num den b N) ∘ₗ E (t * mN num den b N) ∘ₗ
    padL F (kN num den b N) (kf (t * mN num den b N))

/-- The assembly at length `N`. -/
def asm {F : Type} [Field F] {s : ℕ} (kf : ℕ → ℕ) (E : ∀ m, Vec F (kf m) →ₗ[F] Blocks F s m)
    (t b num den : ℕ) (f : Vec F (t * s) → Vec F b) (N : ℕ) : Assembly F N where
  s := t * s
  b := b
  m := mN num den b N
  k := kN num den b N
  code := LinearMap.range (encN kf E t b num den N)
  encoder := encN kf E t b num den N
  localMap := f

end SubspaceEvasion312.Explicit.Dev.Goal
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal
open SubspaceEvasion312.Explicit

/-! ## A structured layer over the register machine (adapted from `LGRuntime1`)

Nat register 61 is the reserved loop temporary. Field input is allowed, and a `raw` command
embeds arbitrary position-dependent code with a semantic specification. -/

variable {F : Type} [Field F]

structure um_St (F : Type) where
  nr : ℕ → ℕ
  fr : ℕ → F
  out : List F

def um_simple : Instruction F → Bool
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
  | .inv _ _ => true
  | .load _ _ => true
  | .input _ _ => true
  | .output _ => true
  | _ => false

def um_setN (s : um_St F) (d v : ℕ) : um_St F := {s with nr := Function.update s.nr d v}
def um_setF (s : um_St F) (d : ℕ) (v : F) : um_St F := {s with fr := Function.update s.fr d v}

def um_eff (ns : List ℕ) (xs : List F) (s : um_St F) : Instruction F → um_St F
  | .literal d v => um_setN s d v
  | .inputNat d i => um_setN s d (ns.getD i 0)
  | .addNat d a b => um_setN s d (s.nr a + s.nr b)
  | .subNat d a b => um_setN s d (s.nr a - s.nr b)
  | .mulNat d a b => um_setN s d (s.nr a * s.nr b)
  | .divNat d a b => um_setN s d (s.nr a / s.nr b)
  | .modNat d a b => um_setN s d (s.nr a % s.nr b)
  | .constant d v => um_setF s d v
  | .add d a b => um_setF s d (s.fr a + s.fr b)
  | .sub d a b => um_setF s d (s.fr a - s.fr b)
  | .mul d a b => um_setF s d (s.fr a * s.fr b)
  | .inv d a => um_setF s d (s.fr a)⁻¹
  | .load d a => um_setF s d (s.fr (s.nr a))
  | .input d a => um_setF s d (xs.getD (s.nr a) 0)
  | .output a => {s with out := s.fr a :: s.out}
  | .store a src => um_setF s (s.nr a) (s.fr src)
  | _ => s

def um_Bd (B : ℕ) (s : um_St F) : Prop := ∀ i, s.nr i ≤ B

inductive um_Cmd (F : Type) where
  | basic (i : Instruction F)
  | seq (a b : um_Cmd F)
  | ifN (x y : ℕ) (t e : um_Cmd F)
  | ifF (x y : ℕ) (t e : um_Cmd F)
  | loop (i n : ℕ) (body : um_Cmd F)
  | raw (len : ℕ) (g : ℕ → List (Instruction F)) (hg : ∀ p, (g p).length = len)

def um_inc (s : um_St F) (i : ℕ) : um_St F :=
  ⟨Function.update (Function.update s.nr 61 1) i (Function.update s.nr 61 1 i + 1), s.fr, s.out⟩

def um_mk (pc : ℕ) (s : um_St F) : MachineState F := ⟨pc, s.nr, s.fr, s.out, []⟩

inductive um_reach (P : Program F) (ns : List ℕ) (xs : List F) (B : ℕ) :
    ℕ → MachineState F → MachineState F → Prop
  | zero (w : MachineState F) : um_reach P ns xs B 0 w w
  | succ {n : ℕ} {w w1 w' : MachineState F} : (∀ i, w.natReg i ≤ B) →
      P[w.pc]? ≠ some .halt → step P ns xs w = some w1 → um_reach P ns xs B n w1 w' →
      um_reach P ns xs B (n + 1) w w'

def um_seg (P : Program F) (b : ℕ) (l : List (Instruction F)) : Prop :=
  ∀ k < l.length, P[b + k]? = l[k]?

inductive um_Exec (ns : List ℕ) (xs : List F) (B : ℕ) : um_Cmd F → um_St F → ℕ → um_St F → Prop
  | basic {i : Instruction F} {s : um_St F} : um_simple i = true → um_Bd B s →
      um_Exec ns xs B (.basic i) s 1 (um_eff ns xs s i)
  | seq {a b : um_Cmd F} {s s1 s2 : um_St F} {n1 n2 : ℕ} :
      um_Exec ns xs B a s n1 s1 → um_Exec ns xs B b s1 n2 s2 →
      um_Exec ns xs B (.seq a b) s (n1 + n2) s2
  | ifNT {x y : ℕ} {t e : um_Cmd F} {s s' : um_St F} {n : ℕ} : um_Bd B s → s.nr x = s.nr y →
      um_Exec ns xs B t s n s' → um_Bd B s' → um_Exec ns xs B (.ifN x y t e) s (n + 2) s'
  | ifNF {x y : ℕ} {t e : um_Cmd F} {s s' : um_St F} {n : ℕ} : um_Bd B s → s.nr x ≠ s.nr y →
      um_Exec ns xs B e s n s' → um_Exec ns xs B (.ifN x y t e) s (n + 1) s'
  | ifFT {x y : ℕ} {t e : um_Cmd F} {s s' : um_St F} {n : ℕ} : um_Bd B s → s.fr x = s.fr y →
      um_Exec ns xs B t s n s' → um_Bd B s' → um_Exec ns xs B (.ifF x y t e) s (n + 2) s'
  | ifFF {x y : ℕ} {t e : um_Cmd F} {s s' : um_St F} {n : ℕ} : um_Bd B s → s.fr x ≠ s.fr y →
      um_Exec ns xs B e s n s' → um_Exec ns xs B (.ifF x y t e) s (n + 1) s'
  | loopD {i n : ℕ} {body : um_Cmd F} {s : um_St F} : um_Bd B s → s.nr i = s.nr n →
      um_Exec ns xs B (.loop i n body) s 1 s
  | loopS {i n : ℕ} {body : um_Cmd F} {s s1 s2 : um_St F} {n1 n2 : ℕ} : um_Bd B s →
      s.nr i ≠ s.nr n → um_Exec ns xs B body s n1 s1 → um_Bd B s1 → um_Bd B (um_inc s1 i) →
      um_Exec ns xs B (.loop i n body) (um_inc s1 i) n2 s2 →
      um_Exec ns xs B (.loop i n body) s (n1 + 4 + n2) s2
  | raw {len : ℕ} {g : ℕ → List (Instruction F)} {hg : ∀ p, (g p).length = len}
      {s s' : um_St F} {n : ℕ} :
      (∀ (P : Program F) base, um_seg P base (g base) →
        um_reach P ns xs B n (um_mk base s) (um_mk (base + len) s')) →
      um_Exec ns xs B (.raw len g hg) s n s'

def um_len : um_Cmd F → ℕ
  | .basic _ => 1
  | .seq a b => um_len a + um_len b
  | .ifN _ _ t e => um_len t + um_len e + 2
  | .ifF _ _ t e => um_len t + um_len e + 2
  | .loop _ _ b => um_len b + 4
  | .raw len _ _ => len

def um_comp : um_Cmd F → ℕ → List (Instruction F)
  | .basic i, _ => [i]
  | .seq a b, p => um_comp a p ++ um_comp b (p + um_len a)
  | .ifN x y t e, p => [.branchNat x y (p + 1) (p + 2 + um_len t)] ++ um_comp t (p + 1) ++
      [.jump (p + 2 + um_len t + um_len e)] ++ um_comp e (p + 2 + um_len t)
  | .ifF x y t e, p => [.branch x y (p + 1) (p + 2 + um_len t)] ++ um_comp t (p + 1) ++
      [.jump (p + 2 + um_len t + um_len e)] ++ um_comp e (p + 2 + um_len t)
  | .loop i n b, p => [.branchNat i n (p + 4 + um_len b) (p + 1)] ++ um_comp b (p + 1) ++
      [.literal 61 1, .addNat i i 61, .jump p]
  | .raw _ g _, p => g p

theorem um_comp_length (c : um_Cmd F) : ∀ p, (um_comp c p).length = um_len c := by
  induction c with
  | basic i => intro p; rfl
  | seq a b iha ihb => intro p; simp [um_comp, um_len, iha, ihb]
  | ifN x y t e iht ihe => intro p; simp [um_comp, um_len, iht, ihe]; try omega
  | ifF x y t e iht ihe => intro p; simp [um_comp, um_len, iht, ihe]; try omega
  | loop i n b ih => intro p; simp [um_comp, um_len, ih]; try omega
  | raw len g hg => intro p; exact hg p

/-! ### Machine-level simulation -/

theorem um_reach_trans {P : Program F} {ns : List ℕ} {xs : List F} {B a b : ℕ}
    {w1 w2 w3 : MachineState F}
    (h1 : um_reach P ns xs B a w1 w2) (h2 : um_reach P ns xs B b w2 w3) :
    um_reach P ns xs B (a + b) w1 w3 := by
  induction h1 with
  | zero => simpa using h2
  | @succ n w w1 w' hb hh hs _ ih =>
    rw [show n + 1 + b = (n + b) + 1 by omega]
    exact um_reach.succ hb hh hs (ih h2)

theorem um_runFrom_of_reach {P : Program F} {ns : List ℕ} {xs : List F} {B n : ℕ}
    {w w' : MachineState F}
    (h : um_reach P ns xs B n w w') (t : ℕ) :
    runFrom P ns xs B (n + t) w = runFrom P ns xs B t w' := by
  induction h with
  | zero => simp
  | @succ n w w1 w' hb hh hs _ ih =>
    rw [show n + 1 + t = (n + t) + 1 by omega]
    simp only [runFrom, hb, implies_true, if_true]
    rw [hs]; simpa using ih

theorem um_seg_left {P : Program F} {b : ℕ} {l1 l2 : List (Instruction F)}
    (h : um_seg P b (l1 ++ l2)) : um_seg P b l1 := by
  intro k hk
  have := h k (by simp; omega)
  rw [this, List.getElem?_append_left hk]

theorem um_seg_right {P : Program F} {b : ℕ} {l1 l2 : List (Instruction F)}
    (h : um_seg P b (l1 ++ l2)) : um_seg P (b + l1.length) l2 := by
  intro k hk
  have := h (l1.length + k) (by simp; omega)
  rw [show b + l1.length + k = b + (l1.length + k) by omega, this,
    List.getElem?_append_right (by omega)]
  simp

theorem um_seg_at {P : Program F} {b : ℕ} {l : List (Instruction F)} (h : um_seg P b l)
    (k : ℕ) (hk : k < l.length) : P[b + k]? = some l[k] := by
  rw [h k hk]; simp [hk]

theorem um_bd_mk {B pc : ℕ} {s : um_St F} (h : um_Bd B s) : ∀ i, (um_mk pc s).natReg i ≤ B := h

theorem um_step_simple {P : Program F} {ns : List ℕ} {xs : List F} {pc : ℕ} {s : um_St F}
    {i : Instruction F} (hP : P[pc]? = some i) (hs : um_simple i = true) :
    step P ns xs (um_mk pc s) = some (um_mk (pc + 1) (um_eff ns xs s i)) := by
  cases i <;> simp_all [step, um_mk, um_eff, um_simple, um_setN, um_setF]

theorem um_step_store {P : Program F} {ns : List ℕ} {xs : List F} {pc : ℕ} {s : um_St F}
    {a src : ℕ} (hP : P[pc]? = some (.store a src)) :
    step P ns xs (um_mk pc s) = some (um_mk (pc + 1) (um_eff ns xs s (.store a src))) := by
  simp_all [step, um_mk, um_eff, um_setF]

theorem um_ne_halt_of {P : Program F} {pc : ℕ} {i : Instruction F} (hP : P[pc]? = some i)
    (hi : i ≠ .halt) : P[pc]? ≠ some .halt := by
  rw [hP]; intro h; exact hi (Option.some_inj.mp h)

theorem um_simple_ne_halt {i : Instruction F} (h : um_simple i = true) : i ≠ .halt := by
  rintro rfl; simp [um_simple] at h

theorem um_reach_one {P : Program F} {ns : List ℕ} {xs : List F} {B pc : ℕ} {s : um_St F}
    {i : Instruction F} {w' : MachineState F} {n : ℕ}
    (hP : P[pc]? = some i) (hs : um_simple i = true) (hb : um_Bd B s)
    (h : um_reach P ns xs B n (um_mk (pc + 1) (um_eff ns xs s i)) w') :
    um_reach P ns xs B (n + 1) (um_mk pc s) w' :=
  um_reach.succ (um_bd_mk hb) (um_ne_halt_of hP (um_simple_ne_halt hs)) (um_step_simple hP hs) h

theorem um_Bd_setN {B d v : ℕ} {s : um_St F} (h : um_Bd B s) (hv : v ≤ B) :
    um_Bd B (um_setN s d v) := by
  intro i; simp only [um_setN, Function.update_apply]; split_ifs <;> [exact hv; exact h i]

theorem um_reach_jump {P : Program F} {ns : List ℕ} {xs : List F} {B pc tgt : ℕ} {s : um_St F}
    (hP : P[pc]? = some (.jump tgt)) (hb : um_Bd B s) :
    um_reach P ns xs B 1 (um_mk pc s) (um_mk tgt s) :=
  um_reach.succ (um_bd_mk hb) (um_ne_halt_of hP (by simp)) (by simp [step, um_mk, hP])
    (um_reach.zero _)

theorem um_reach_brN {P : Program F} {ns : List ℕ} {xs : List F} {B pc x y yes no : ℕ}
    {s : um_St F}
    (hP : P[pc]? = some (.branchNat x y yes no)) (hb : um_Bd B s) :
    um_reach P ns xs B 1 (um_mk pc s) (um_mk (if s.nr x = s.nr y then yes else no) s) :=
  um_reach.succ (um_bd_mk hb) (um_ne_halt_of hP (by simp))
    (by by_cases h : s.nr x = s.nr y <;> simp [step, um_mk, hP, h]) (um_reach.zero _)

open Classical in
theorem um_reach_brF {P : Program F} {ns : List ℕ} {xs : List F} {B pc x y yes no : ℕ}
    {s : um_St F}
    (hP : P[pc]? = some (.branch x y yes no)) (hb : um_Bd B s) :
    um_reach P ns xs B 1 (um_mk pc s) (um_mk (if s.fr x = s.fr y then yes else no) s) :=
  um_reach.succ (um_bd_mk hb) (um_ne_halt_of hP (by simp))
    (by by_cases h : s.fr x = s.fr y <;> simp [step, um_mk, hP, h]) (um_reach.zero _)

theorem um_sim {P : Program F} {ns : List ℕ} {xs : List F} {B : ℕ} {c : um_Cmd F}
    {s s' : um_St F} {n : ℕ}
    (h : um_Exec ns xs B c s n s') :
    ∀ base, um_seg P base (um_comp c base) →
      um_reach P ns xs B n (um_mk base s) (um_mk (base + um_len c) s') := by
  induction h with
  | @basic i s hs hb =>
    intro base hseg
    have hP := um_seg_at hseg 0 (by simp [um_comp])
    simp only [um_comp, add_zero, List.getElem_cons_zero] at hP
    exact um_reach_one hP hs hb (um_reach.zero _)
  | @seq a b s s1 s2 n1 n2 _ _ iha ihb =>
    intro base hseg
    simp only [um_comp] at hseg
    have := um_reach_trans (iha base (um_seg_left hseg))
      (ihb _ (by have := um_seg_right hseg; rwa [um_comp_length] at this))
    simpa [um_len, add_assoc] using this
  | @ifNT x y t e s s' n hb hxy _ hb' iht =>
    intro base hseg
    simp only [um_comp] at hseg
    have hs1 := um_seg_left (um_seg_left (um_seg_left hseg))
    have hs2 := um_seg_right (um_seg_left (um_seg_left hseg))
    have hs3 := um_seg_right (um_seg_left hseg)
    simp only [List.length_singleton, List.length_append, um_comp_length] at hs2 hs3
    have h0 := um_seg_at hs1 0 (by simp)
    have hj := um_seg_at hs3 0 (by simp)
    simp only [add_zero, List.getElem_cons_zero] at h0 hj
    rw [show base + (1 + um_len t) = base + 1 + um_len t by omega] at hj
    have r1 := um_reach_brN (ns := ns) (xs := xs) h0 hb
    rw [if_pos hxy] at r1
    have r2 := iht (base + 1) (by simpa [add_comm] using hs2)
    have r3 := um_reach_jump (ns := ns) (xs := xs) hj hb'
    have := um_reach_trans (um_reach_trans r1 r2) r3
    rw [show base + um_len (um_Cmd.ifN x y t e) = base + 2 + um_len t + um_len e by
      simp [um_len]; omega]
    convert this using 1; omega
  | @ifNF x y t e s s' n hb hxy _ ihe =>
    intro base hseg
    simp only [um_comp] at hseg
    have hs1 := um_seg_left (um_seg_left (um_seg_left hseg))
    have hs4 := um_seg_right hseg
    simp only [List.length_singleton, List.length_append, um_comp_length] at hs4
    rw [show base + (1 + um_len t + 1) = base + 2 + um_len t by omega] at hs4
    have h0 := um_seg_at hs1 0 (by simp)
    simp only [add_zero, List.getElem_cons_zero] at h0
    have r1 := um_reach_brN (ns := ns) (xs := xs) h0 hb
    rw [if_neg hxy] at r1
    have r2 := ihe _ hs4
    have := um_reach_trans r1 r2
    rw [show base + um_len (um_Cmd.ifN x y t e) = base + 2 + um_len t + um_len e by
      simp [um_len]; omega]
    convert this using 1; omega
  | @ifFT x y t e s s' n hb hxy _ hb' iht =>
    intro base hseg
    simp only [um_comp] at hseg
    have hs1 := um_seg_left (um_seg_left (um_seg_left hseg))
    have hs2 := um_seg_right (um_seg_left (um_seg_left hseg))
    have hs3 := um_seg_right (um_seg_left hseg)
    simp only [List.length_singleton, List.length_append, um_comp_length] at hs2 hs3
    have h0 := um_seg_at hs1 0 (by simp)
    have hj := um_seg_at hs3 0 (by simp)
    simp only [add_zero, List.getElem_cons_zero] at h0 hj
    rw [show base + (1 + um_len t) = base + 1 + um_len t by omega] at hj
    have r1 := um_reach_brF (ns := ns) (xs := xs) h0 hb
    rw [if_pos hxy] at r1
    have r2 := iht (base + 1) (by simpa [add_comm] using hs2)
    have r3 := um_reach_jump (ns := ns) (xs := xs) hj hb'
    have := um_reach_trans (um_reach_trans r1 r2) r3
    rw [show base + um_len (um_Cmd.ifF x y t e) = base + 2 + um_len t + um_len e by
      simp [um_len]; omega]
    convert this using 1; omega
  | @ifFF x y t e s s' n hb hxy _ ihe =>
    intro base hseg
    simp only [um_comp] at hseg
    have hs1 := um_seg_left (um_seg_left (um_seg_left hseg))
    have hs4 := um_seg_right hseg
    simp only [List.length_singleton, List.length_append, um_comp_length] at hs4
    rw [show base + (1 + um_len t + 1) = base + 2 + um_len t by omega] at hs4
    have h0 := um_seg_at hs1 0 (by simp)
    simp only [add_zero, List.getElem_cons_zero] at h0
    have r1 := um_reach_brF (ns := ns) (xs := xs) h0 hb
    rw [if_neg hxy] at r1
    have r2 := ihe _ hs4
    have := um_reach_trans r1 r2
    rw [show base + um_len (um_Cmd.ifF x y t e) = base + 2 + um_len t + um_len e by
      simp [um_len]; omega]
    convert this using 1; omega
  | @loopD i n body s hb hin =>
    intro base hseg
    simp only [um_comp] at hseg
    have h0 := um_seg_at (um_seg_left (um_seg_left hseg)) 0 (by simp)
    simp only [add_zero, List.getElem_cons_zero] at h0
    have r1 := um_reach_brN (ns := ns) (xs := xs) h0 hb
    rw [if_pos hin] at r1
    rw [show base + um_len (um_Cmd.loop i n body) = base + 4 + um_len body by
      simp [um_len]; omega]
    exact r1
  | @loopS i n body s s1 s2 n1 n2 hb hin _ hb1 hbi _ ihb ihl =>
    intro base hseg
    have hseg' := hseg
    simp only [um_comp] at hseg
    have h0 := um_seg_at (um_seg_left (um_seg_left hseg)) 0 (by simp)
    have hs2 := um_seg_right (um_seg_left hseg)
    have hs3 := um_seg_right hseg
    simp only [List.length_singleton, List.length_append, um_comp_length] at hs2 hs3
    simp only [add_zero, List.getElem_cons_zero] at h0
    have g0 := um_seg_at hs3 0 (by simp)
    have g1 := um_seg_at hs3 1 (by simp)
    have g2 := um_seg_at hs3 2 (by simp)
    simp only [add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at g0 g1 g2
    rw [show base + (1 + um_len body) = base + 1 + um_len body by omega] at g0 g1 g2
    have r1 := um_reach_brN (ns := ns) (xs := xs) h0 hb
    rw [if_neg hin] at r1
    have hbody := ihb (base + 1) (by simpa [add_comm] using hs2)
    have hbm : ∀ j, (Function.update s1.nr 61 1) j ≤ B := by
      intro j; simp only [Function.update_apply]; split_ifs with hj
      · have := hbi 61; simp only [um_inc, Function.update_apply] at this
        split_ifs at this <;> omega
      · exact hb1 j
    have hrest : um_reach P ns xs B 3 (um_mk (base + 1 + um_len body) s1)
        (um_mk base (um_inc s1 i)) := by
      refine um_reach.succ (um_bd_mk hb1) (um_ne_halt_of g0 (by simp))
        (by simp [step, um_mk, g0] <;> rfl) ?_
      refine um_reach.succ hbm (um_ne_halt_of g1 (by simp))
        (by simp [step, g1] <;> rfl) ?_
      refine um_reach.succ (um_bd_mk hbi) (um_ne_halt_of g2 (by simp))
        (by simp [step, g2] <;> rfl) ?_
      exact um_reach.zero _
    have := um_reach_trans (um_reach_trans (um_reach_trans r1 hbody) hrest) (ihl base hseg')
    convert this using 1
    omega
  | @raw len g hg s s' n h =>
    intro base hseg
    exact h P base hseg

/-- Running a whole structured program followed by `halt`. -/
theorem um_run {ns : List ℕ} {xs : List F} {B : ℕ} {c : um_Cmd F} {s : um_St F} {n : ℕ}
    (h : um_Exec ns xs B c (⟨fun _ => 0, fun _ => 0, []⟩ : um_St F) n s) (hb : um_Bd B s) :
    runFrom (um_comp c 0 ++ [.halt]) ns xs B (n + 1) initialState =
      some (um_mk (um_len c) s) := by
  have hseg : um_seg (um_comp c 0 ++ [.halt]) 0 (um_comp c 0) := by
    intro k hk; simp [List.getElem?_append_left hk]
  have hr := um_sim h 0 hseg
  have e : (initialState : MachineState F) = um_mk 0 ⟨fun _ => 0, fun _ => 0, []⟩ := rfl
  rw [e, um_runFrom_of_reach hr 1]
  simp only [zero_add]
  have hh : (um_comp c 0 ++ [Instruction.halt])[um_len c]? = some .halt := by
    rw [List.getElem?_append_right (by rw [um_comp_length])]; simp [um_comp_length]
  simp [runFrom, um_mk, hh, show ∀ i, s.nr i ≤ B from hb]

/-! ### Hoare-style specifications -/

def um_Sp (ns : List ℕ) (xs : List F) (B : ℕ) (c : um_Cmd F) (P Q : um_St F → Prop)
    (N : ℕ) : Prop :=
  ∀ s, P s → ∃ n s', n ≤ N ∧ um_Exec ns xs B c s n s' ∧ Q s'

section Hoare
variable {ns : List ℕ} {xs : List F} {B : ℕ}

theorem um_sp_conseq {c : um_Cmd F} {P Q P' Q' : um_St F → Prop} {N N' : ℕ}
    (h : um_Sp ns xs B c P Q N) (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s) (hN : N ≤ N') :
    um_Sp ns xs B c P' Q' N' := by
  intro s hs
  obtain ⟨n, s', hn, he, hq⟩ := h s (hP s hs)
  exact ⟨n, s', by omega, he, hQ _ hq⟩

theorem um_sp_basic {i : Instruction F} {P Q : um_St F → Prop} (hi : um_simple i = true)
    (h : ∀ s, P s → um_Bd B s ∧ Q (um_eff ns xs s i)) : um_Sp ns xs B (.basic i) P Q 1 := by
  intro s hs
  exact ⟨1, _, le_rfl, um_Exec.basic hi (h s hs).1, (h s hs).2⟩

theorem um_sp_seq {a b : um_Cmd F} {P R Q : um_St F → Prop} {N1 N2 : ℕ}
    (ha : um_Sp ns xs B a P R N1) (hb : um_Sp ns xs B b R Q N2) :
    um_Sp ns xs B (.seq a b) P Q (N1 + N2) := by
  intro s hs
  obtain ⟨n1, s1, hn1, he1, hr⟩ := ha s hs
  obtain ⟨n2, s2, hn2, he2, hq⟩ := hb s1 hr
  exact ⟨n1 + n2, s2, by omega, um_Exec.seq he1 he2, hq⟩

theorem um_sp_ifN {x y : ℕ} {t e : um_Cmd F} {P Q : um_St F → Prop} {N1 N2 : ℕ}
    (hb : ∀ s, P s → um_Bd B s)
    (ht : um_Sp ns xs B t (fun s => P s ∧ s.nr x = s.nr y) (fun s => Q s ∧ um_Bd B s) N1)
    (he : um_Sp ns xs B e (fun s => P s ∧ s.nr x ≠ s.nr y) Q N2) :
    um_Sp ns xs B (.ifN x y t e) P Q (max N1 N2 + 2) := by
  intro s hs
  by_cases hxy : s.nr x = s.nr y
  · obtain ⟨n, s', hn, he', hq, hb'⟩ := ht s ⟨hs, hxy⟩
    exact ⟨n + 2, s', by omega, um_Exec.ifNT (hb s hs) hxy he' hb', hq⟩
  · obtain ⟨n, s', hn, he', hq⟩ := he s ⟨hs, hxy⟩
    exact ⟨n + 1, s', by omega, um_Exec.ifNF (hb s hs) hxy he', hq⟩

theorem um_sp_ifF {x y : ℕ} {t e : um_Cmd F} {P Q : um_St F → Prop} {N1 N2 : ℕ}
    (hb : ∀ s, P s → um_Bd B s)
    (ht : um_Sp ns xs B t (fun s => P s ∧ s.fr x = s.fr y) (fun s => Q s ∧ um_Bd B s) N1)
    (he : um_Sp ns xs B e (fun s => P s ∧ s.fr x ≠ s.fr y) Q N2) :
    um_Sp ns xs B (.ifF x y t e) P Q (max N1 N2 + 2) := by
  intro s hs
  by_cases hxy : s.fr x = s.fr y
  · obtain ⟨n, s', hn, he', hq, hb'⟩ := ht s ⟨hs, hxy⟩
    exact ⟨n + 2, s', by omega, um_Exec.ifFT (hb s hs) hxy he' hb', hq⟩
  · obtain ⟨n, s', hn, he', hq⟩ := he s ⟨hs, hxy⟩
    exact ⟨n + 1, s', by omega, um_Exec.ifFF (hb s hs) hxy he', hq⟩

/-- The counting loop rule. `I k` describes the state at the head with counter value `k`. -/
theorem um_sp_loop {i n : ℕ} {body : um_Cmd F} (I : ℕ → um_St F → Prop) (a N cb : ℕ)
    (haN : a ≤ N)
    (hI : ∀ k s, a ≤ k → k ≤ N → I k s → s.nr i = k ∧ s.nr n = N ∧ um_Bd B s)
    (hbody : ∀ k, a ≤ k → k < N → um_Sp ns xs B body (I k)
      (fun s1 => um_Bd B s1 ∧ um_Bd B (um_inc s1 i) ∧ I (k + 1) (um_inc s1 i)) cb) :
    um_Sp ns xs B (.loop i n body) (I a) (I N) ((N - a) * (cb + 4) + 1) := by
  suffices H : ∀ m k, k + m = N → a ≤ k → ∀ s, I k s →
      ∃ n' s', n' ≤ m * (cb + 4) + 1 ∧ um_Exec ns xs B (.loop i n body) s n' s' ∧ I N s' by
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
    exact ⟨1, s, by omega, um_Exec.loopD h3 (by rw [h1, h2]), hs⟩
  | succ m ih =>
    intro k hk hak s hs
    obtain ⟨h1, h2, h3⟩ := hI k s hak (by omega) hs
    obtain ⟨n1, s1, hn1, he1, hb1, hbi, hI1⟩ := hbody k hak (by omega) s hs
    obtain ⟨n2, s2, hn2, he2, hI2⟩ := ih (k + 1) (by omega) (by omega) _ hI1
    refine ⟨n1 + 4 + n2, s2, ?_, um_Exec.loopS h3 (by rw [h1, h2]; omega) he1 hb1 hbi he2, hI2⟩
    rw [Nat.succ_mul]; omega

end Hoare

/-! ### Program size -/

def um_szI : Instruction F → ℕ
  | .literal _ v => 2 + v
  | _ => 1

/-- A size bound; every `raw` block is charged `R`. -/
def um_szB (R : ℕ) : um_Cmd F → ℕ
  | .basic i => um_szI i
  | .seq a b => um_szB R a + um_szB R b
  | .ifN _ _ t e => um_szB R t + um_szB R e + 2
  | .ifF _ _ t e => um_szB R t + um_szB R e + 2
  | .loop _ _ b => um_szB R b + 6
  | .raw _ _ _ => R

def um_rawOK (R : ℕ) : um_Cmd F → Prop
  | .basic _ => True
  | .seq a b => um_rawOK R a ∧ um_rawOK R b
  | .ifN _ _ t e => um_rawOK R t ∧ um_rawOK R e
  | .ifF _ _ t e => um_rawOK R t ∧ um_rawOK R e
  | .loop _ _ b => um_rawOK R b
  | .raw _ g _ => ∀ p, programSize (g p) ≤ R

theorem um_size_le_szB (R : ℕ) (c : um_Cmd F) (hc : um_rawOK R c) :
    ∀ p, programSize (um_comp c p) ≤ um_szB R c := by
  have hlit : ∀ d v : ℕ, instructionSize (Instruction.literal (F := F) d v) ≤ 2 + v := by
    intro d v; simp [instructionSize, Nat.log2_le_self]
  induction c with
  | basic i =>
    intro p
    cases i <;> simp only [um_comp, um_szB, um_szI, programSize, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero] <;> first | exact hlit _ _ | simp [instructionSize]
  | seq a b iha ihb =>
    intro p
    simp only [um_rawOK] at hc
    simp only [um_comp, um_szB, programSize, List.map_append, List.sum_append] at *
    have := iha hc.1 p; have := ihb hc.2 (p + um_len a); omega
  | ifN x y t e iht ihe =>
    intro p
    simp only [um_rawOK] at hc
    simp only [um_comp, um_szB, programSize, List.map_append, List.sum_append] at *
    have := iht hc.1 (p + 1); have := ihe hc.2 (p + 2 + um_len t)
    simp [instructionSize]; omega
  | ifF x y t e iht ihe =>
    intro p
    simp only [um_rawOK] at hc
    simp only [um_comp, um_szB, programSize, List.map_append, List.sum_append] at *
    have := iht hc.1 (p + 1); have := ihe hc.2 (p + 2 + um_len t)
    simp [instructionSize]; omega
  | loop i n b ih =>
    intro p
    simp only [um_rawOK] at hc
    simp only [um_comp, um_szB, programSize, List.map_append, List.sum_append] at *
    have := ih hc (p + 1); have h1 := hlit 61 1
    simp only [instructionSize] at h1
    simp [instructionSize]; omega
  | raw len g hg => intro p; exact hc p

end SubspaceEvasion312.Explicit.Dev.Goal
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal
open SubspaceEvasion312.Explicit

/-! ## Translating a program into a relocated block

Register conventions inside the translated block:
* nat registers `100 + j` hold the guest's nat register `j`;
* field registers `2 a + 1` hold the guest's field register `a`;
* nat 2 = `k` (input length), 3 = `M` (guest nat input), 4 = 1, 5 = 2, 6 = 0;
* nat 7 is a scratch register; nat 8 is the output pointer `2 (8 + #outputs)`;
* the guest's output `i` goes to field register `2 (8 + i)`. -/

variable {F : Type} [Field F]

def um_p1 (q : ℕ) (X : Instruction F) : List (Instruction F) :=
  [X, .jump (q + 2), .jump (q + 3), .jump (q + 4), .jump (q + 7), .halt, .halt]
def um_p2 (q : ℕ) (X Y : Instruction F) : List (Instruction F) :=
  [X, Y, .jump (q + 3), .jump (q + 4), .jump (q + 7), .halt, .halt]
def um_p3 (q : ℕ) (X Y Z : Instruction F) : List (Instruction F) :=
  [X, Y, Z, .jump (q + 4), .jump (q + 7), .halt, .halt]
def um_pc (q : ℕ) (X : Instruction F) : List (Instruction F) :=
  [.jump (q + 1), .jump (q + 2), .jump (q + 3), .jump (q + 4), X, .halt, .halt]

def um_tr (base exit p : ℕ) : Instruction F → List (Instruction F)
  | .halt => [.literal 7 0, .jump exit, .halt, .halt, .halt, .halt, .halt]
  | .literal d v => um_p1 (base + 7 * p) (.literal (100 + d) v)
  | .inputNat d i => um_p1 (base + 7 * p)
      (if i = 0 then .addNat (100 + d) 3 6 else .literal (100 + d) 0)
  | .addNat d a b => um_p1 (base + 7 * p) (.addNat (100 + d) (100 + a) (100 + b))
  | .subNat d a b => um_p1 (base + 7 * p) (.subNat (100 + d) (100 + a) (100 + b))
  | .mulNat d a b => um_p1 (base + 7 * p) (.mulNat (100 + d) (100 + a) (100 + b))
  | .divNat d a b => um_p1 (base + 7 * p) (.divNat (100 + d) (100 + a) (100 + b))
  | .modNat d a b => um_p1 (base + 7 * p) (.modNat (100 + d) (100 + a) (100 + b))
  | .branchNat a b y n => um_pc (base + 7 * p)
      (.branchNat (100 + a) (100 + b) (base + 7 * y) (base + 7 * n))
  | .constant d v => um_p1 (base + 7 * p) (.constant (2 * d + 1) v)
  | .add d a b => um_p1 (base + 7 * p) (.add (2 * d + 1) (2 * a + 1) (2 * b + 1))
  | .sub d a b => um_p1 (base + 7 * p) (.sub (2 * d + 1) (2 * a + 1) (2 * b + 1))
  | .mul d a b => um_p1 (base + 7 * p) (.mul (2 * d + 1) (2 * a + 1) (2 * b + 1))
  | .inv d a => um_p1 (base + 7 * p) (.inv (2 * d + 1) (2 * a + 1))
  | .load d a => um_p3 (base + 7 * p) (.mulNat 7 (100 + a) 5) (.addNat 7 7 4)
      (.load (2 * d + 1) 7)
  | .store a s => um_p3 (base + 7 * p) (.mulNat 7 (100 + a) 5) (.addNat 7 7 4)
      (.store 7 (2 * s + 1))
  | .input d a =>
      [.subNat 7 2 (100 + a), .branchNat 7 6 (base + 7 * p + 4) (base + 7 * p + 2),
       .input (2 * d + 1) (100 + a), .jump (base + 7 * p + 6), .constant (2 * d + 1) 0,
       .jump (base + 7 * p + 6), .jump (base + 7 * p + 7)]
  | .branch a b y n => um_pc (base + 7 * p)
      (.branch (2 * a + 1) (2 * b + 1) (base + 7 * y) (base + 7 * n))
  | .jump t => um_pc (base + 7 * p) (.jump (base + 7 * t))
  | .output s => um_p2 (base + 7 * p) (.store 8 (2 * s + 1)) (.addNat 8 8 5)
  | .outputNat _ => um_pc (base + 7 * p) (.jump (base + 7 * p + 7))

theorem um_tr_length (base exit p : ℕ) (ins : Instruction F) :
    (um_tr base exit p ins).length = 7 := by
  cases ins <;> simp [um_tr, um_p1, um_p2, um_p3, um_pc]

def um_trL (base exit : ℕ) : ℕ → List (Instruction F) → List (Instruction F)
  | _, [] => []
  | p, ins :: rest => um_tr base exit p ins ++ um_trL base exit (p + 1) rest

theorem um_trL_length (base exit : ℕ) : ∀ (P : List (Instruction F)) (p : ℕ),
    (um_trL base exit p P).length = 7 * P.length := by
  intro P
  induction P with
  | nil => intro p; rfl
  | cons ins rest ih => intro p; simp [um_trL, um_tr_length, ih]; ring

theorem um_trL_seg {Q : Program F} {base exit : ℕ} : ∀ (P : List (Instruction F)) (p i : ℕ)
    (ins : Instruction F), um_seg Q (base + 7 * p) (um_trL base exit p P) → P[i]? = some ins →
    um_seg Q (base + 7 * (p + i)) (um_tr base exit (p + i) ins) := by
  intro P
  induction P with
  | nil => intro p i ins _ h; simp at h
  | cons a rest ih =>
    intro p i ins hseg hi
    simp only [um_trL] at hseg
    cases i with
    | zero =>
      simp at hi; subst hi; simpa using um_seg_left hseg
    | succ i =>
      have h2 := um_seg_right hseg
      rw [um_tr_length, show base + 7 * p + 7 = base + 7 * (p + 1) by ring] at h2
      have := ih (p + 1) i ins h2 (by simpa using hi)
      rwa [show p + 1 + i = p + (i + 1) by omega] at this

theorem um_trL_size (base exit : ℕ) : ∀ (P : List (Instruction F)) (p : ℕ),
    programSize (um_trL base exit p P) ≤ 8 * programSize P := by
  intro P
  induction P with
  | nil => intro p; simp [um_trL, programSize]
  | cons ins rest ih =>
    intro p
    have h1 := ih (p + 1)
    have h2 : programSize (um_tr base exit p ins) ≤ 8 * instructionSize ins := by
      cases ins <;> simp only [um_tr, um_p1, um_p2, um_p3, um_pc, programSize, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, instructionSize] <;> (try split_ifs) <;>
        (try simp only [instructionSize, Nat.log2_zero]) <;> omega
    simp only [um_trL, programSize, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons] at h1 h2 ⊢
    omega

/-! ### Guest semantics -/

/-- The effect of one non-halting guest instruction. -/
def um_geff (ns : List ℕ) (xs : List F) (z : MachineState F) : Instruction F → MachineState F
  | .halt => z
  | .literal d v => {z with pc := z.pc + 1, natReg := Function.update z.natReg d v}
  | .inputNat d i => {z with pc := z.pc + 1, natReg := Function.update z.natReg d (ns.getD i 0)}
  | .addNat d a b =>
      {z with pc := z.pc + 1, natReg := Function.update z.natReg d (z.natReg a + z.natReg b)}
  | .subNat d a b =>
      {z with pc := z.pc + 1, natReg := Function.update z.natReg d (z.natReg a - z.natReg b)}
  | .mulNat d a b =>
      {z with pc := z.pc + 1, natReg := Function.update z.natReg d (z.natReg a * z.natReg b)}
  | .divNat d a b =>
      {z with pc := z.pc + 1, natReg := Function.update z.natReg d (z.natReg a / z.natReg b)}
  | .modNat d a b =>
      {z with pc := z.pc + 1, natReg := Function.update z.natReg d (z.natReg a % z.natReg b)}
  | .branchNat a b y n => {z with pc := if z.natReg a = z.natReg b then y else n}
  | .constant d v => {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg d v}
  | .add d a b =>
      {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg d (z.fieldReg a + z.fieldReg b)}
  | .sub d a b =>
      {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg d (z.fieldReg a - z.fieldReg b)}
  | .mul d a b =>
      {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg d (z.fieldReg a * z.fieldReg b)}
  | .inv d a => {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg d (z.fieldReg a)⁻¹}
  | .load d a =>
      {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg d (z.fieldReg (z.natReg a))}
  | .store a s =>
      {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg (z.natReg a) (z.fieldReg s)}
  | .input d a =>
      {z with pc := z.pc + 1, fieldReg := Function.update z.fieldReg d (xs.getD (z.natReg a) 0)}
  | .branch a b y n => by
      classical
      exact {z with pc := if z.fieldReg a = z.fieldReg b then y else n}
  | .jump p => {z with pc := p}
  | .output s => {z with pc := z.pc + 1, out := z.fieldReg s :: z.out}
  | .outputNat s => {z with pc := z.pc + 1, natOut := z.natReg s :: z.natOut}

theorem um_gstep {P : Program F} {ns : List ℕ} {xs : List F} {z : MachineState F}
    {ins : Instruction F} (h : P[z.pc]? = some ins) (hh : ins ≠ .halt) :
    step P ns xs z = some (um_geff ns xs z ins) := by
  cases ins <;> simp_all [step, um_geff]

theorem um_grun_succ {P : Program F} {ns : List ℕ} {xs : List F} {B t : ℕ}
    {z zf : MachineState F}
    (h : runFrom P ns xs B (t + 1) z = some zf) :
    (∀ i, z.natReg i ≤ B) ∧
    ((P[z.pc]? = some .halt ∧ zf = z) ∨
     ∃ ins, P[z.pc]? = some ins ∧ ins ≠ .halt ∧
       runFrom P ns xs B t (um_geff ns xs z ins) = some zf) := by
  simp only [runFrom] at h
  split_ifs at h with hb
  refine ⟨hb, ?_⟩
  split at h
  · rename_i heq; left; exact ⟨heq, (Option.some_inj.mp h).symm⟩
  · rename_i hne
    cases hq : P[z.pc]? with
    | none => simp [step, hq] at h
    | some ins =>
      have hh : ins ≠ .halt := by rintro rfl; exact hne hq
      right; exact ⟨ins, rfl, hh, by rw [um_gstep hq hh] at h; simpa using h⟩

theorem um_grun_bounded {P : Program F} {ns : List ℕ} {xs : List F} {B t : ℕ}
    {z zf : MachineState F}
    (h : runFrom P ns xs B t z = some zf) : ∀ i, z.natReg i ≤ B := by
  cases t with
  | zero => simp [runFrom] at h
  | succ t => exact (um_grun_succ h).1

theorem um_geff_out (ns : List ℕ) (xs : List F) (z : MachineState F) (ins : Instruction F) :
    z.out.length ≤ (um_geff ns xs z ins).out.length := by
  cases ins <;> simp [um_geff]

theorem um_grun_out {P : Program F} {ns : List ℕ} {xs : List F} {B : ℕ} :
    ∀ t (z zf : MachineState F), runFrom P ns xs B t z = some zf →
      z.out.length ≤ zf.out.length ∧ (∀ i, zf.natReg i ≤ B) := by
  intro t
  induction t with
  | zero => intro z zf h; simp [runFrom] at h
  | succ t ih =>
    intro z zf h
    obtain ⟨hb, ⟨_, rfl⟩ | ⟨ins, _, _, h2⟩⟩ := um_grun_succ h
    · exact ⟨le_rfl, hb⟩
    · have h3 := ih _ _ h2
      have := um_geff_out ns xs z ins
      exact ⟨by omega, h3.2⟩

/-! ### The simulation relation -/

def um_imgN (w0 : um_St F) (z : MachineState F) (j : ℕ) : ℕ :=
  if 100 ≤ j then z.natReg (j - 100) else if j = 8 then 2 * (8 + z.out.length)
  else if j = 7 then 0 else w0.nr j

def um_imgF (w0 : um_St F) (z : MachineState F) (a : ℕ) : F :=
  if a % 2 = 1 then z.fieldReg (a / 2)
  else if 8 ≤ a / 2 ∧ a / 2 < 8 + z.out.length then z.out.reverse.getD (a / 2 - 8) 0
  else w0.fr a

def um_img (w0 : um_St F) (z : MachineState F) : um_St F :=
  ⟨um_imgN w0 z, um_imgF w0 z, w0.out⟩

structure um_Rel (w0 : um_St F) (z : MachineState F) (s : um_St F) : Prop where
  nr : ∀ j, j ≠ 7 → s.nr j = um_imgN w0 z j
  fr : ∀ a, s.fr a = um_imgF w0 z a
  out : s.out = w0.out

/-- The context registers of the host. -/
structure um_W0 (w0 : um_St F) (k M : ℕ) : Prop where
  k : w0.nr 2 = k
  M : w0.nr 3 = M
  one : w0.nr 4 = 1
  two : w0.nr 5 = 2
  zero : w0.nr 6 = 0

theorem um_rel_nat {w0 : um_St F} {z : MachineState F} {s : um_St F} (h : um_Rel w0 z s)
    (j : ℕ) : s.nr (100 + j) = z.natReg j := by
  rw [h.nr _ (by omega)]; simp [um_imgN]

theorem um_rel_fld {w0 : um_St F} {z : MachineState F} {s : um_St F} (h : um_Rel w0 z s)
    (a : ℕ) : s.fr (2 * a + 1) = z.fieldReg a := by
  rw [h.fr]; simp only [um_imgF]; rw [if_pos (by omega)]; congr 1; omega

theorem um_rel_ctx {w0 : um_St F} {z : MachineState F} {s : um_St F} (h : um_Rel w0 z s)
    (j : ℕ) (hj : j < 7) : s.nr j = w0.nr j := by
  rw [h.nr _ (by omega)]; simp only [um_imgN]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem um_rel_op {w0 : um_St F} {z : MachineState F} {s : um_St F} (h : um_Rel w0 z s) :
    s.nr 8 = 2 * (8 + z.out.length) := by
  rw [h.nr _ (by omega)]; simp [um_imgN]

theorem um_rel_bd {w0 : um_St F} {z : MachineState F} {s : um_St F} {B : ℕ}
    (h : um_Rel w0 z s) (hz : ∀ i, z.natReg i ≤ B) (ho : 2 * (8 + z.out.length) ≤ B)
    (hw : ∀ j, w0.nr j ≤ B) (h7 : s.nr 7 ≤ B) : um_Bd B s := by
  intro j
  by_cases hj : j = 7
  · subst hj; exact h7
  rw [h.nr j hj]; simp only [um_imgN]
  split_ifs <;> first | exact hz _ | exact ho | omega | exact hw j

theorem um_img_bd {w0 : um_St F} {z : MachineState F} {B : ℕ}
    (hz : ∀ i, z.natReg i ≤ B) (ho : 2 * (8 + z.out.length) ≤ B)
    (hw : ∀ j, w0.nr j ≤ B) : um_Bd B (um_img w0 z) := by
  intro j; simp only [um_img, um_imgN]
  split_ifs <;> first | exact hz _ | exact ho | omega | exact hw j

/-- The scratch register is free. -/
theorem um_rel_t {w0 : um_St F} {z : MachineState F} {s : um_St F} (h : um_Rel w0 z s)
    (v : ℕ) : um_Rel w0 z (um_setN s 7 v) := by
  refine ⟨fun j hj => ?_, h.fr, h.out⟩
  simp only [um_setN, Function.update_apply, if_neg hj]; exact h.nr j hj

/-- Only the guest's program counter changed. -/
theorem um_rel_pc {w0 : um_St F} {z z' : MachineState F} {s : um_St F} (h : um_Rel w0 z s)
    (hn : z'.natReg = z.natReg) (hf : z'.fieldReg = z.fieldReg) (ho : z'.out = z.out) :
    um_Rel w0 z' s := by
  refine ⟨fun j hj => ?_, fun a => ?_, h.out⟩
  · rw [h.nr j hj]; simp [um_imgN, hn, ho]
  · rw [h.fr a]; simp [um_imgF, hf, ho]

theorem um_rel_setN {w0 : um_St F} {z z' : MachineState F} {s : um_St F} (h : um_Rel w0 z s)
    (d v : ℕ) (hn : z'.natReg = Function.update z.natReg d v) (hf : z'.fieldReg = z.fieldReg)
    (ho : z'.out = z.out) :
    um_Rel w0 z' (um_setN s (100 + d) v) := by
  refine ⟨fun j hj => ?_, fun a => ?_, h.out⟩
  · simp only [um_setN, Function.update_apply]
    split_ifs with hjd
    · subst hjd; simp [um_imgN, hn]
    · rw [h.nr j hj]; simp only [um_imgN, hn, ho, Function.update_apply]
      split_ifs <;> first | rfl | omega
  · rw [show (um_setN s (100 + d) v).fr = s.fr from rfl, h.fr a]; simp [um_imgF, hf, ho]

theorem um_rel_setF {w0 : um_St F} {z z' : MachineState F} {s : um_St F} (h : um_Rel w0 z s)
    (d : ℕ) (v : F) (hn : z'.natReg = z.natReg) (hf : z'.fieldReg = Function.update z.fieldReg d v)
    (ho : z'.out = z.out) :
    um_Rel w0 z' (um_setF s (2 * d + 1) v) := by
  refine ⟨fun j hj => ?_, fun a => ?_, h.out⟩
  · rw [show (um_setF s (2 * d + 1) v).nr = s.nr from rfl, h.nr j hj]; simp [um_imgN, hn, ho]
  · simp only [um_setF, Function.update_apply]
    split_ifs with had
    · subst had; simp only [um_imgF, hf]
      rw [if_pos (by omega), show (2 * d + 1) / 2 = d by omega]; simp
    · rw [h.fr a]; simp only [um_imgF, hf, ho, Function.update_apply]
      split_ifs <;> first | rfl | omega

theorem um_rel_out {w0 : um_St F} {z z' : MachineState F} {s : um_St F} (h : um_Rel w0 z s)
    (v : F) (hn : z'.natReg = z.natReg) (hf : z'.fieldReg = z.fieldReg)
    (ho : z'.out = v :: z.out) :
    um_Rel w0 z' ⟨Function.update s.nr 8 (2 * (8 + z.out.length) + 2),
      Function.update s.fr (2 * (8 + z.out.length)) v, s.out⟩ := by
  refine ⟨fun j hj => ?_, fun a => ?_, h.out⟩
  · simp only [Function.update_apply]
    split_ifs with hj8
    · subst hj8; simp [um_imgN, ho]; ring
    · rw [h.nr j hj]; simp only [um_imgN, hn, ho, List.length_cons]
      split_ifs <;> first | rfl | omega
  · simp only [Function.update_apply]
    split_ifs with ha
    · subst ha; simp only [um_imgF, ho, List.length_cons, List.reverse_cons]
      rw [if_neg (by omega), if_pos (by omega)]
      rw [show 2 * (8 + z.out.length) / 2 - 8 = z.out.reverse.length by simp]
      simp
    · rw [h.fr a]; simp only [um_imgF, hf, ho, List.length_cons, List.reverse_cons]
      by_cases h1 : a % 2 = 1
      · simp [h1]
      · simp only [h1, if_false]
        have hev : a = 2 * (a / 2) := by omega
        by_cases h2 : 8 ≤ a / 2 ∧ a / 2 < 8 + z.out.length
        · rw [if_pos h2, if_pos (by omega), List.getD_append _ _ _ _ (by simp; omega)]
        · rw [if_neg h2, if_neg (by omega)]

end SubspaceEvasion312.Explicit.Dev.Goal
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal
open SubspaceEvasion312.Explicit

variable {F : Type} [Field F]

section Shapes
variable {Q : Program F} {ns : List ℕ} {xs : List F} {B : ℕ}

def um_lin (X : Instruction F) : Prop := um_simple X = true ∨ ∃ a b, X = .store a b

theorem um_rl {pc n : ℕ} {s : um_St F} {X : Instruction F} {w : MachineState F}
    (hP : Q[pc]? = some X) (hX : um_lin X) (hb : um_Bd B s)
    (h : um_reach Q ns xs B n (um_mk (pc + 1) (um_eff ns xs s X)) w) :
    um_reach Q ns xs B (n + 1) (um_mk pc s) w := by
  rcases hX with hX | ⟨a, b, rfl⟩
  · exact um_reach_one hP hX hb h
  · exact um_reach.succ (um_bd_mk hb) (um_ne_halt_of hP (by simp)) (um_step_store hP) h

theorem um_rj {pc t n : ℕ} {s : um_St F} {w : MachineState F}
    (hP : Q[pc]? = some (.jump t)) (hb : um_Bd B s)
    (h : um_reach Q ns xs B n (um_mk t s) w) :
    um_reach Q ns xs B (n + 1) (um_mk pc s) w := by
  have := um_reach_trans (um_reach_jump hP hb) h; rwa [Nat.add_comm] at this

theorem um_sh1 {q : ℕ} {s : um_St F} {X : Instruction F}
    (hseg : um_seg Q q (um_p1 q X)) (hX : um_lin X) (hb : um_Bd B s)
    (hb1 : um_Bd B (um_eff ns xs s X)) :
    um_reach Q ns xs B 5 (um_mk q s) (um_mk (q + 7) (um_eff ns xs s X)) := by
  have g := fun j (hj : j < 7) => um_seg_at hseg j (by simp [um_p1]; omega)
  have h0 := g 0 (by omega); have h1 := g 1 (by omega); have h2 := g 2 (by omega)
  have h3 := g 3 (by omega); have h4 := g 4 (by omega)
  simp only [um_p1, add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4
  exact um_rl h0 hX hb (um_rj h1 hb1 (um_rj h2 hb1 (um_rj h3 hb1 (um_rj h4 hb1 (um_reach.zero _)))))

theorem um_sh2 {q : ℕ} {s : um_St F} {X Y : Instruction F}
    (hseg : um_seg Q q (um_p2 q X Y)) (hX : um_lin X) (hY : um_lin Y) (hb : um_Bd B s)
    (hb1 : um_Bd B (um_eff ns xs s X)) (hb2 : um_Bd B (um_eff ns xs (um_eff ns xs s X) Y)) :
    um_reach Q ns xs B 5 (um_mk q s) (um_mk (q + 7) (um_eff ns xs (um_eff ns xs s X) Y)) := by
  have g := fun j (hj : j < 7) => um_seg_at hseg j (by simp [um_p2]; omega)
  have h0 := g 0 (by omega); have h1 := g 1 (by omega); have h2 := g 2 (by omega)
  have h3 := g 3 (by omega); have h4 := g 4 (by omega)
  simp only [um_p2, add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4
  exact um_rl h0 hX hb (um_rl h1 hY hb1 (um_rj h2 hb2 (um_rj h3 hb2 (um_rj h4 hb2 (um_reach.zero _)))))

theorem um_sh3 {q : ℕ} {s : um_St F} {X Y Z : Instruction F}
    (hseg : um_seg Q q (um_p3 q X Y Z)) (hX : um_lin X) (hY : um_lin Y) (hZ : um_lin Z)
    (hb : um_Bd B s) (hb1 : um_Bd B (um_eff ns xs s X))
    (hb2 : um_Bd B (um_eff ns xs (um_eff ns xs s X) Y))
    (hb3 : um_Bd B (um_eff ns xs (um_eff ns xs (um_eff ns xs s X) Y) Z)) :
    um_reach Q ns xs B 5 (um_mk q s)
      (um_mk (q + 7) (um_eff ns xs (um_eff ns xs (um_eff ns xs s X) Y) Z)) := by
  have g := fun j (hj : j < 7) => um_seg_at hseg j (by simp [um_p3]; omega)
  have h0 := g 0 (by omega); have h1 := g 1 (by omega); have h2 := g 2 (by omega)
  have h3 := g 3 (by omega); have h4 := g 4 (by omega)
  simp only [um_p3, add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4
  exact um_rl h0 hX hb (um_rl h1 hY hb1 (um_rl h2 hZ hb2 (um_rj h3 hb3 (um_rj h4 hb3
    (um_reach.zero _)))))

theorem um_shc {q n : ℕ} {s : um_St F} {X : Instruction F} {w : MachineState F}
    (hseg : um_seg Q q (um_pc q X)) (hb : um_Bd B s)
    (h : um_reach Q ns xs B n (um_mk (q + 4) s) w) :
    um_reach Q ns xs B (n + 4) (um_mk q s) w := by
  have g := fun j (hj : j < 7) => um_seg_at hseg j (by simp [um_pc]; omega)
  have h0 := g 0 (by omega); have h1 := g 1 (by omega); have h2 := g 2 (by omega)
  have h3 := g 3 (by omega)
  simp only [um_pc, add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3
  exact um_rj h0 hb (um_rj h1 hb (um_rj h2 hb (um_rj h3 hb h)))

theorem um_rb {pc x y yes no n : ℕ} {s : um_St F} {w : MachineState F}
    (hP : Q[pc]? = some (.branchNat x y yes no)) (hb : um_Bd B s)
    (h : um_reach Q ns xs B n (um_mk (if s.nr x = s.nr y then yes else no) s) w) :
    um_reach Q ns xs B (n + 1) (um_mk pc s) w := by
  have := um_reach_trans (um_reach_brN hP hb) h; rwa [Nat.add_comm] at this

theorem um_shc_at {q : ℕ} {X : Instruction F} (hseg : um_seg Q q (um_pc q X)) :
    Q[q + 4]? = some X := by
  have := um_seg_at hseg 4 (by simp [um_pc]); simpa [um_pc] using this

end Shapes

theorem um_setN_ne {s : um_St F} {d v j : ℕ} (h : j ≠ d) : (um_setN s d v).nr j = s.nr j :=
  Function.update_of_ne h _ _

section Block
variable {ns : List ℕ} {xs : List F} {B : ℕ}

theorem um_case1 {z z' : MachineState F} {s s' : um_St F} {X ins : Instruction F}
    (hX : um_lin X) (hs' : um_eff ns xs s X = s') (hpc : z'.pc = z.pc + 1)
    (htr : ∀ base exit, um_tr base exit z.pc ins = um_p1 (base + 7 * z.pc) X)
    (hb : um_Bd B s) (hb' : um_Bd B s') :
    ∀ (Q : Program F) base exit, um_seg Q (base + 7 * z.pc) (um_tr base exit z.pc ins) →
      um_reach Q ns xs B 5 (um_mk (base + 7 * z.pc) s) (um_mk (base + 7 * z'.pc) s') := by
  intro Q base exit hseg
  rw [htr] at hseg; subst hs'
  rw [hpc, show base + 7 * (z.pc + 1) = base + 7 * z.pc + 7 by ring]
  exact um_sh1 hseg hX hb hb'

theorem um_casec {z z' : MachineState F} {s : um_St F} {X : ℕ → Instruction F}
    {ins : Instruction F}
    (htr : ∀ base exit, um_tr base exit z.pc ins = um_pc (base + 7 * z.pc) (X base))
    (hb : um_Bd B s)
    (hX : ∀ (Q : Program F) base, Q[base + 7 * z.pc + 4]? = some (X base) →
      um_reach Q ns xs B 1 (um_mk (base + 7 * z.pc + 4) s) (um_mk (base + 7 * z'.pc) s)) :
    ∀ (Q : Program F) base exit, um_seg Q (base + 7 * z.pc) (um_tr base exit z.pc ins) →
      um_reach Q ns xs B 5 (um_mk (base + 7 * z.pc) s) (um_mk (base + 7 * z'.pc) s) := by
  intro Q base exit hseg
  rw [htr] at hseg
  exact um_shc hseg hb (hX Q base (um_shc_at hseg))

theorem um_blk {M k Benc : ℕ} {xsE : List F} {w0 : um_St F}
    (hw : um_W0 w0 k M) (hwB : ∀ j, w0.nr j ≤ B)
    (hx : ∀ v, xsE.getD v 0 = if v < k then xs.getD v 0 else 0)
    (hB1 : Benc ≤ B) (hB2 : 2 * Benc + 1 ≤ B) (hk : k ≤ B)
    {z : MachineState F} {ins : Instruction F} (hh : ins ≠ .halt)
    (hz : ∀ i, z.natReg i ≤ Benc) (hz' : ∀ i, (um_geff [M] xsE z ins).natReg i ≤ Benc)
    (hO : 2 * (8 + (um_geff [M] xsE z ins).out.length) ≤ B)
    {s : um_St F} (hr : um_Rel w0 z s) (h7 : s.nr 7 ≤ B) :
    ∃ s', um_Rel w0 (um_geff [M] xsE z ins) s' ∧ s'.nr 7 ≤ B ∧
      ∀ (Q : Program F) base exit, um_seg Q (base + 7 * z.pc) (um_tr base exit z.pc ins) →
        um_reach Q ns xs B 5 (um_mk (base + 7 * z.pc) s)
          (um_mk (base + 7 * (um_geff [M] xsE z ins).pc) s') := by
  have hO' : 2 * (8 + z.out.length) ≤ B := by
    have := um_geff_out [M] xsE z ins; omega
  have hzB : ∀ i, z.natReg i ≤ B := fun i => (hz i).trans hB1
  have hb : um_Bd B s := um_rel_bd hr hzB hO' hwB h7
  have hbd : ∀ s', um_Rel w0 (um_geff [M] xsE z ins) s' → s'.nr 7 ≤ B → um_Bd B s' :=
    fun s' hr' h7' => um_rel_bd hr' (fun i => (hz' i).trans hB1) hO hwB h7'
  -- generic nat-write case
  have natCase : ∀ (d v : ℕ) (X : Instruction F), um_simple X = true →
      um_eff ns xs s X = um_setN s (100 + d) v →
      (um_geff [M] xsE z ins).natReg = Function.update z.natReg d v →
      (um_geff [M] xsE z ins).fieldReg = z.fieldReg →
      (um_geff [M] xsE z ins).out = z.out →
      (um_geff [M] xsE z ins).pc = z.pc + 1 →
      (∀ base exit, um_tr base exit z.pc ins = um_p1 (base + 7 * z.pc) X) →
      ∃ s', um_Rel w0 (um_geff [M] xsE z ins) s' ∧ s'.nr 7 ≤ B ∧
        ∀ (Q : Program F) base exit, um_seg Q (base + 7 * z.pc) (um_tr base exit z.pc ins) →
          um_reach Q ns xs B 5 (um_mk (base + 7 * z.pc) s)
            (um_mk (base + 7 * (um_geff [M] xsE z ins).pc) s') := by
    intro d v X hX hs' hn hf ho hpc htr
    have hr' := um_rel_setN hr d v hn hf ho
    have h7' : (um_setN s (100 + d) v).nr 7 ≤ B := by rw [um_setN_ne (by omega)]; exact h7
    exact ⟨_, hr', h7', um_case1 (Or.inl hX) hs' hpc htr hb (hbd _ hr' h7')⟩
  have fldCase : ∀ (d : ℕ) (v : F) (X : Instruction F), um_simple X = true →
      um_eff ns xs s X = um_setF s (2 * d + 1) v →
      (um_geff [M] xsE z ins).natReg = z.natReg →
      (um_geff [M] xsE z ins).fieldReg = Function.update z.fieldReg d v →
      (um_geff [M] xsE z ins).out = z.out →
      (um_geff [M] xsE z ins).pc = z.pc + 1 →
      (∀ base exit, um_tr base exit z.pc ins = um_p1 (base + 7 * z.pc) X) →
      ∃ s', um_Rel w0 (um_geff [M] xsE z ins) s' ∧ s'.nr 7 ≤ B ∧
        ∀ (Q : Program F) base exit, um_seg Q (base + 7 * z.pc) (um_tr base exit z.pc ins) →
          um_reach Q ns xs B 5 (um_mk (base + 7 * z.pc) s)
            (um_mk (base + 7 * (um_geff [M] xsE z ins).pc) s') := by
    intro d v X hX hs' hn hf ho hpc htr
    have hr' := um_rel_setF hr d v hn hf ho
    have h7' : (um_setF s (2 * d + 1) v).nr 7 ≤ B := h7
    exact ⟨_, hr', h7', um_case1 (Or.inl hX) hs' hpc htr hb (hbd _ hr' h7')⟩
  have ctlCase : ∀ (X : ℕ → Instruction F),
      um_Rel w0 (um_geff [M] xsE z ins) s →
      (∀ base exit, um_tr base exit z.pc ins = um_pc (base + 7 * z.pc) (X base)) →
      (∀ (Q : Program F) base, Q[base + 7 * z.pc + 4]? = some (X base) →
        um_reach Q ns xs B 1 (um_mk (base + 7 * z.pc + 4) s)
          (um_mk (base + 7 * (um_geff [M] xsE z ins).pc) s)) →
      ∃ s', um_Rel w0 (um_geff [M] xsE z ins) s' ∧ s'.nr 7 ≤ B ∧
        ∀ (Q : Program F) base exit, um_seg Q (base + 7 * z.pc) (um_tr base exit z.pc ins) →
          um_reach Q ns xs B 5 (um_mk (base + 7 * z.pc) s)
            (um_mk (base + 7 * (um_geff [M] xsE z ins).pc) s') := by
    intro X hr' htr hX
    exact ⟨s, hr', h7, um_casec htr hb hX⟩
  cases ins with
  | halt => exact absurd rfl hh
  | literal d v =>
    exact natCase d v _ rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
  | inputNat d i =>
    by_cases hi : i = 0
    · subst hi
      refine natCase d M (.addNat (100 + d) 3 6) rfl ?_ (by simp [um_geff]) rfl rfl rfl (fun _ _ => by simp [um_tr])
      simp only [um_eff, um_rel_ctx hr 3 (by omega), um_rel_ctx hr 6 (by omega), hw.M, hw.zero,
        add_zero]
    · refine natCase d 0 (.literal (100 + d) 0) rfl rfl (by simp [um_geff, hi]) rfl rfl rfl
        (fun _ _ => by simp [um_tr, hi])
  | addNat d a b =>
    exact natCase d _ _ rfl (by simp only [um_eff, um_rel_nat hr]) rfl rfl rfl rfl (fun _ _ => rfl)
  | subNat d a b =>
    exact natCase d _ _ rfl (by simp only [um_eff, um_rel_nat hr]) rfl rfl rfl rfl (fun _ _ => rfl)
  | mulNat d a b =>
    exact natCase d _ _ rfl (by simp only [um_eff, um_rel_nat hr]) rfl rfl rfl rfl (fun _ _ => rfl)
  | divNat d a b =>
    exact natCase d _ _ rfl (by simp only [um_eff, um_rel_nat hr]) rfl rfl rfl rfl (fun _ _ => rfl)
  | modNat d a b =>
    exact natCase d _ _ rfl (by simp only [um_eff, um_rel_nat hr]) rfl rfl rfl rfl (fun _ _ => rfl)
  | constant d v =>
    exact fldCase d v _ rfl rfl rfl rfl rfl rfl (fun _ _ => rfl)
  | add d a b =>
    exact fldCase d _ _ rfl (by simp only [um_eff, um_rel_fld hr]) rfl rfl rfl rfl (fun _ _ => rfl)
  | sub d a b =>
    exact fldCase d _ _ rfl (by simp only [um_eff, um_rel_fld hr]) rfl rfl rfl rfl (fun _ _ => rfl)
  | mul d a b =>
    exact fldCase d _ _ rfl (by simp only [um_eff, um_rel_fld hr]) rfl rfl rfl rfl (fun _ _ => rfl)
  | inv d a =>
    exact fldCase d _ _ rfl (by simp only [um_eff, um_rel_fld hr]) rfl rfl rfl rfl (fun _ _ => rfl)
  | branchNat a b y n =>
    refine ctlCase (fun base => .branchNat (100 + a) (100 + b) (base + 7 * y) (base + 7 * n)) (um_rel_pc hr rfl rfl rfl) (fun _ _ => rfl) ?_
    intro Q base hQ
    have := um_reach_brN (ns := ns) (xs := xs) (B := B) (s := s) hQ hb
    convert this using 2
    simp only [um_geff, um_rel_nat hr]; split_ifs <;> rfl
  | branch a b y n =>
    refine ctlCase (fun base => .branch (2 * a + 1) (2 * b + 1) (base + 7 * y) (base + 7 * n)) (um_rel_pc hr rfl rfl rfl) (fun _ _ => rfl) ?_
    intro Q base hQ
    have := um_reach_brF (ns := ns) (xs := xs) (B := B) (s := s) hQ hb
    convert this using 2
    simp only [um_geff, um_rel_fld hr]
    by_cases hab : z.fieldReg a = z.fieldReg b <;> simp [hab, um_rel_fld hr]
  | jump t =>
    refine ctlCase (fun base => .jump (base + 7 * t)) (um_rel_pc hr rfl rfl rfl) (fun _ _ => rfl) ?_
    intro Q base hQ
    exact um_reach_jump hQ hb
  | outputNat a =>
    refine ctlCase (fun base => .jump (base + 7 * z.pc + 7)) (um_rel_pc hr rfl rfl rfl) (fun _ _ => rfl) ?_
    intro Q base hQ
    have := um_reach_jump (ns := ns) (xs := xs) (B := B) (s := s) hQ hb
    convert this using 2
    simp only [um_geff]; ring
  | load d a =>
    have h2v : 2 * z.natReg a + 1 ≤ B := by have := hz a; omega
    have hr1 := um_rel_t hr (z.natReg a * 2)
    have hr2 := um_rel_t hr1 (z.natReg a * 2 + 1)
    have hr3 := um_rel_setF hr2 d (z.fieldReg (z.natReg a)) (z' := um_geff [M] xsE z (.load d a))
      rfl rfl rfl
    have h7' : (um_setF (um_setN (um_setN s 7 (z.natReg a * 2)) 7 (z.natReg a * 2 + 1))
        (2 * d + 1) (z.fieldReg (z.natReg a))).nr 7 ≤ B := by
      simp only [um_setF, um_setN, Function.update_self]; omega
    refine ⟨_, hr3, h7', ?_⟩
    intro Q base exit hseg
    simp only [um_tr] at hseg
    have e1 : um_eff ns xs s (.mulNat 7 (100 + a) 5) = um_setN s 7 (z.natReg a * 2) := by
      simp only [um_eff, um_rel_nat hr, um_rel_ctx hr 5 (by omega), hw.two]
    have e2 : um_eff ns xs (um_setN s 7 (z.natReg a * 2)) (.addNat 7 7 4) =
        um_setN (um_setN s 7 (z.natReg a * 2)) 7 (z.natReg a * 2 + 1) := by
      simp only [um_eff]; congr 1
      simp only [um_setN, Function.update_self]
      rw [Function.update_of_ne (by omega), um_rel_ctx hr 4 (by omega), hw.one]
    have e3 : um_eff ns xs (um_setN (um_setN s 7 (z.natReg a * 2)) 7 (z.natReg a * 2 + 1))
        (.load (2 * d + 1) 7) = um_setF (um_setN (um_setN s 7 (z.natReg a * 2)) 7
          (z.natReg a * 2 + 1)) (2 * d + 1) (z.fieldReg (z.natReg a)) := by
      simp only [um_eff]; congr 1
      simp only [um_setN, Function.update_self]
      rw [show z.natReg a * 2 + 1 = 2 * z.natReg a + 1 by ring, um_rel_fld hr]
    have := um_sh3 (ns := ns) (xs := xs) (B := B) hseg (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hb
      (by rw [e1]; exact um_rel_bd hr1 hzB hO' hwB (by simp [um_setN]; omega))
      (by rw [e1, e2]; exact um_rel_bd hr2 hzB hO' hwB (by simp [um_setN]; omega))
      (by rw [e1, e2, e3]; exact hbd _ hr3 h7')
    rw [e1, e2, e3] at this
    convert this using 2
    simp only [um_geff]; ring
  | store a src =>
    have h2v : 2 * z.natReg a + 1 ≤ B := by have := hz a; omega
    have hr1 := um_rel_t hr (z.natReg a * 2)
    have hr2 := um_rel_t hr1 (z.natReg a * 2 + 1)
    have hr3 := um_rel_setF hr2 (z.natReg a) (z.fieldReg src)
      (z' := um_geff [M] xsE z (.store a src)) rfl rfl rfl
    have h7' : (um_setF (um_setN (um_setN s 7 (z.natReg a * 2)) 7 (z.natReg a * 2 + 1))
        (2 * z.natReg a + 1) (z.fieldReg src)).nr 7 ≤ B := by
      simp only [um_setF, um_setN, Function.update_self]; omega
    refine ⟨_, hr3, h7', ?_⟩
    intro Q base exit hseg
    simp only [um_tr] at hseg
    have e1 : um_eff ns xs s (.mulNat 7 (100 + a) 5) = um_setN s 7 (z.natReg a * 2) := by
      simp only [um_eff, um_rel_nat hr, um_rel_ctx hr 5 (by omega), hw.two]
    have e2 : um_eff ns xs (um_setN s 7 (z.natReg a * 2)) (.addNat 7 7 4) =
        um_setN (um_setN s 7 (z.natReg a * 2)) 7 (z.natReg a * 2 + 1) := by
      simp only [um_eff]; congr 1
      simp only [um_setN, Function.update_self]
      rw [Function.update_of_ne (by omega), um_rel_ctx hr 4 (by omega), hw.one]
    have e3 : um_eff ns xs (um_setN (um_setN s 7 (z.natReg a * 2)) 7 (z.natReg a * 2 + 1))
        (.store 7 (2 * src + 1)) = um_setF (um_setN (um_setN s 7 (z.natReg a * 2)) 7
          (z.natReg a * 2 + 1)) (2 * z.natReg a + 1) (z.fieldReg src) := by
      simp only [um_eff]
      simp only [um_setN, Function.update_self]
      rw [show z.natReg a * 2 + 1 = 2 * z.natReg a + 1 by ring]
      congr 1
      exact um_rel_fld hr src
    have := um_sh3 (ns := ns) (xs := xs) (B := B) hseg (Or.inl rfl) (Or.inl rfl)
      (Or.inr ⟨_, _, rfl⟩) hb
      (by rw [e1]; exact um_rel_bd hr1 hzB hO' hwB (by simp [um_setN]; omega))
      (by rw [e1, e2]; exact um_rel_bd hr2 hzB hO' hwB (by simp [um_setN]; omega))
      (by rw [e1, e2, e3]; exact hbd _ hr3 h7')
    rw [e1, e2, e3] at this
    convert this using 2
    simp only [um_geff]; ring
  | output a0 =>
    have hr2 := um_rel_out hr (z.fieldReg a0) (z' := um_geff [M] xsE z (.output a0)) rfl rfl rfl
    refine ⟨_, hr2, by simp only [Function.update_apply]; exact h7, ?_⟩
    intro Q base exit hseg
    simp only [um_tr] at hseg
    have e1 : um_eff ns xs s (.store 8 (2 * a0 + 1)) =
        um_setF s (2 * (8 + z.out.length)) (z.fieldReg a0) := by
      simp only [um_eff, um_rel_op hr, um_rel_fld hr]
    have e2 : um_eff ns xs (um_setF s (2 * (8 + z.out.length)) (z.fieldReg a0)) (.addNat 8 8 5) =
        ⟨Function.update s.nr 8 (2 * (8 + z.out.length) + 2),
          Function.update s.fr (2 * (8 + z.out.length)) (z.fieldReg a0), s.out⟩ := by
      simp only [um_eff, um_setN, um_setF]
      rw [um_rel_op hr, um_rel_ctx hr 5 (by omega), hw.two]
    have := um_sh2 (ns := ns) (xs := xs) (B := B) hseg (Or.inr ⟨_, _, rfl⟩) (Or.inl rfl) hb
      (by rw [e1]; exact hb)
      (by rw [e1, e2]; exact hbd _ hr2 (by simp only [Function.update_apply]; exact h7))
    rw [e1, e2] at this
    convert this using 2
    simp only [um_geff]; ring
  | input d a =>
    have hval : xsE.getD (z.natReg a) 0 =
        if z.natReg a < k then xs.getD (z.natReg a) 0 else 0 := hx _
    have hr1 := um_rel_t hr (k - z.natReg a)
    have hr3 := um_rel_setF hr1 d (xsE.getD (z.natReg a) 0)
      (z' := um_geff [M] xsE z (.input d a)) rfl rfl rfl
    have h7' : (um_setF (um_setN s 7 (k - z.natReg a)) (2 * d + 1)
        (xsE.getD (z.natReg a) 0)).nr 7 ≤ B := by
      simp only [um_setF, um_setN, Function.update_self]; omega
    refine ⟨_, hr3, h7', ?_⟩
    intro Q base exit hseg
    simp only [um_tr] at hseg
    have g := fun j (hj : j < 7) => um_seg_at hseg j (by simp; omega)
    have h0 := g 0 (by omega); have h1 := g 1 (by omega); have h2 := g 2 (by omega)
    have h3 := g 3 (by omega); have h4 := g 4 (by omega); have h5 := g 5 (by omega)
    have h6 := g 6 (by omega)
    simp only [add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4 h5 h6
    have e1 : um_eff ns xs s (.subNat 7 2 (100 + a)) = um_setN s 7 (k - z.natReg a) := by
      simp only [um_eff, um_rel_nat hr, um_rel_ctx hr 2 (by omega), hw.k]
    have hb1 : um_Bd B (um_setN s 7 (k - z.natReg a)) :=
      um_rel_bd hr1 hzB hO' hwB (by simp [um_setN]; omega)
    have hb3 := hbd _ hr3 h7'
    have hpc : base + 7 * (um_geff [M] xsE z (.input d a)).pc = base + 7 * z.pc + 7 := by
      simp only [um_geff]; ring
    rw [hpc]
    refine um_rl h0 (Or.inl rfl) hb ?_
    rw [e1]
    refine um_rb h1 hb1 ?_
    have h6r : (um_setN s 7 (k - z.natReg a)).nr 6 = 0 := by
      rw [um_setN_ne (by omega), um_rel_ctx hr 6 (by omega), hw.zero]
    rw [h6r, show (um_setN s 7 (k - z.natReg a)).nr 7 = k - z.natReg a by
      simp [um_setN]]
    by_cases hlt : z.natReg a < k
    · rw [if_neg (by omega)]
      rw [hval, if_pos hlt]
      refine um_rl h2 (Or.inl rfl) hb1 ?_
      have e3 : um_eff ns xs (um_setN s 7 (k - z.natReg a)) (.input (2 * d + 1) (100 + a)) =
          um_setF (um_setN s 7 (k - z.natReg a)) (2 * d + 1) (xs.getD (z.natReg a) 0) := by
        simp only [um_eff]; congr 2
        rw [um_setN_ne (by omega), um_rel_nat hr]
      rw [e3]
      have hb3' : um_Bd B (um_setF (um_setN s 7 (k - z.natReg a)) (2 * d + 1)
          (xs.getD (z.natReg a) 0)) := hb1
      exact um_rj h3 hb3' (um_rj h6 hb3' (um_reach.zero _))
    · rw [if_pos (by omega)]
      rw [hval, if_neg hlt]
      refine um_rl h4 (Or.inl rfl) hb1 ?_
      have hb3' : um_Bd B (um_eff ns xs (um_setN s 7 (k - z.natReg a)) (.constant (2 * d + 1) 0)) :=
        hb1
      exact um_rj h5 hb3' (um_rj h6 hb3' (um_reach.zero _))

end Block

end SubspaceEvasion312.Explicit.Dev.Goal
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal
open SubspaceEvasion312.Explicit

variable {F : Type} [Field F]

section Sim
variable {ns : List ℕ} {xs : List F} {B : ℕ}

theorem um_encsim {enc : Program F} {M k Benc : ℕ} {xsE : List F} {w0 : um_St F}
    (hw : um_W0 w0 k M) (hwB : ∀ j, w0.nr j ≤ B)
    (hx : ∀ v, xsE.getD v 0 = if v < k then xs.getD v 0 else 0)
    (hB1 : Benc ≤ B) (hB2 : 2 * Benc + 1 ≤ B) (hk : k ≤ B) :
    ∀ t (z zf : MachineState F), runFrom enc [M] xsE Benc t z = some zf →
      2 * (8 + zf.out.length) ≤ B →
      ∃ n, n ≤ 5 * t ∧ ∀ s, um_Rel w0 z s → s.nr 7 ≤ B →
        ∀ (Q : Program F) base, um_seg Q base (um_trL base (base + 7 * enc.length) 0 enc) →
          um_reach Q ns xs B n (um_mk (base + 7 * z.pc) s)
            (um_mk (base + 7 * enc.length) (um_img w0 zf)) := by
  intro t
  induction t with
  | zero => intro z zf h; simp [runFrom] at h
  | succ t ih =>
    intro z zf h hOf
    obtain ⟨hz, ⟨hq, rfl⟩ | ⟨ins, hq, hh, h2⟩⟩ := um_grun_succ h
    · refine ⟨2, by omega, ?_⟩
      intro s hr h7 Q base hseg
      have hseg' := um_trL_seg enc 0 zf.pc .halt (by simpa using hseg) hq
      simp only [zero_add, um_tr] at hseg'
      have g0 := um_seg_at hseg' 0 (by simp)
      have g1 := um_seg_at hseg' 1 (by simp)
      simp only [add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at g0 g1
      have hb := um_rel_bd hr (fun i => (hz i).trans hB1) hOf hwB h7
      have hb1 : um_Bd B (um_setN s 7 0) :=
        um_rel_bd (um_rel_t hr 0) (fun i => (hz i).trans hB1) hOf hwB (by simp [um_setN])
      have e : um_setN s 7 0 = um_img w0 zf := by
        cases s with
        | mk nr fr out =>
          simp only [um_setN, um_img]
          congr 1
          · funext j
            by_cases hj : j = 7
            · subst hj; simp [um_imgN]
            · rw [Function.update_of_ne hj]; exact hr.nr j hj
          · funext a; exact hr.fr a
          · exact hr.out
      have := um_rl (ns := ns) (xs := xs) g0 (Or.inl rfl) hb (um_rj g1 hb1 (um_reach.zero _))
      rw [show um_eff ns xs s (.literal 7 0) = um_img w0 zf from e] at this
      exact this
    · have hz' := um_grun_bounded h2
      obtain ⟨hout, hzf⟩ := um_grun_out t _ _ h2
      obtain ⟨n', hn', hrest⟩ := ih _ _ h2 hOf
      refine ⟨5 + n', by omega, ?_⟩
      intro s hr h7 Q base hseg
      obtain ⟨s', hr', h7', hreach⟩ := um_blk (ns := ns) (xs := xs) (B := B) hw hwB hx hB1 hB2 hk
        hh hz hz' (by omega) hr h7
      have hseg' := um_trL_seg enc 0 z.pc ins (by simpa using hseg) hq
      simp only [zero_add] at hseg'
      exact um_reach_trans (hreach Q base _ hseg') (hrest s' hr' h7' Q base hseg)

end Sim

/-- The embedded encoder. -/
def um_encC (enc : Program F) : um_Cmd F :=
  .raw (7 * enc.length) (fun base => um_trL base (base + 7 * enc.length) 0 enc)
    (fun base => um_trL_length base _ enc 0)

/-- Initial conditions for the embedded run. -/
structure um_Init (w0 : um_St F) : Prop where
  nat0 : ∀ j, w0.nr (100 + j) = 0
  fld0 : ∀ a, w0.fr (2 * a + 1) = 0
  op : w0.nr 8 = 16

theorem um_rel_init {w0 : um_St F} (hi : um_Init w0) : um_Rel w0 initialState w0 := by
  refine ⟨fun j hj => ?_, fun a => ?_, rfl⟩
  · simp only [um_imgN, initialState, List.length_nil]
    by_cases h1 : 100 ≤ j
    · rw [if_pos h1]; have := hi.nat0 (j - 100); rwa [show 100 + (j - 100) = j by omega] at this
    · rw [if_neg h1]
      by_cases h2 : j = 8
      · subst h2; simp [hi.op]
      · rw [if_neg h2, if_neg hj]
  · unfold um_imgF
    split_ifs with h1 h2
    · have := hi.fld0 (a / 2); rwa [show 2 * (a / 2) + 1 = a by omega] at this
    · exfalso; simp [initialState] at h2; omega
    · rfl

theorem um_exec_enc {ns : List ℕ} {xs : List F} {B : ℕ}
    {enc : Program F} {M k Benc te : ℕ} {xsE : List F} {w0 : um_St F} {zf : MachineState F}
    (hw : um_W0 w0 k M) (hwB : ∀ j, w0.nr j ≤ B) (hi : um_Init w0)
    (hx : ∀ v, xsE.getD v 0 = if v < k then xs.getD v 0 else 0)
    (hB1 : Benc ≤ B) (hB2 : 2 * Benc + 1 ≤ B) (hk : k ≤ B)
    (hrun : runFrom enc [M] xsE Benc te initialState = some zf)
    (hOf : 2 * (8 + zf.out.length) ≤ B) :
    ∃ n, n ≤ 5 * te ∧ um_Exec ns xs B (um_encC enc) w0 n (um_img w0 zf) ∧
      um_Bd B (um_img w0 zf) := by
  obtain ⟨n, hn, h⟩ := um_encsim (ns := ns) (xs := xs) (B := B) hw hwB hx hB1 hB2 hk te _ _ hrun hOf
  refine ⟨n, hn, um_Exec.raw ?_, ?_⟩
  · intro Q base hseg
    have := h w0 (um_rel_init hi) (hwB 7) Q base hseg
    simpa [initialState] using this
  · exact um_img_bd (fun i => ((um_grun_out te _ _ hrun).2 i).trans hB1) hOf hwB

end SubspaceEvasion312.Explicit.Dev.Goal
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal
open SubspaceEvasion312.Explicit

variable {F : Type} [Field F]

/-! ### Symbolic execution of loop-free code -/

open Classical in
def um_sym (ns : List ℕ) (xs : List F) : um_Cmd F → um_St F → um_St F
  | .basic i, s => um_eff ns xs s i
  | .seq a b, s => um_sym ns xs b (um_sym ns xs a s)
  | .ifN x y t e, s => if s.nr x = s.nr y then um_sym ns xs t s else um_sym ns xs e s
  | .ifF x y t e, s => if s.fr x = s.fr y then um_sym ns xs t s else um_sym ns xs e s
  | .loop _ _ _, s => s
  | .raw _ _ _, s => s

open Classical in
def um_symC (ns : List ℕ) (xs : List F) : um_Cmd F → um_St F → ℕ
  | .basic _, _ => 1
  | .seq a b, s => um_symC ns xs a s + um_symC ns xs b (um_sym ns xs a s)
  | .ifN x y t e, s => if s.nr x = s.nr y then um_symC ns xs t s + 2 else um_symC ns xs e s + 1
  | .ifF x y t e, s => if s.fr x = s.fr y then um_symC ns xs t s + 2 else um_symC ns xs e s + 1
  | .loop _ _ _, _ => 0
  | .raw _ _ _, _ => 0

def um_wv (ns : List ℕ) (s : um_St F) : Instruction F → ℕ
  | .literal _ v => v
  | .inputNat _ i => ns.getD i 0
  | .addNat _ a b => s.nr a + s.nr b
  | .subNat _ a b => s.nr a - s.nr b
  | .mulNat _ a b => s.nr a * s.nr b
  | .divNat _ a b => s.nr a / s.nr b
  | .modNat _ a b => s.nr a % s.nr b
  | _ => 0

open Classical in
def um_symV (ns : List ℕ) (xs : List F) (B : ℕ) : um_Cmd F → um_St F → Prop
  | .basic i, s => um_simple i = true ∧ um_wv ns s i ≤ B
  | .seq a b, s => um_symV ns xs B a s ∧ um_symV ns xs B b (um_sym ns xs a s)
  | .ifN x y t e, s => if s.nr x = s.nr y then um_symV ns xs B t s else um_symV ns xs B e s
  | .ifF x y t e, s => if s.fr x = s.fr y then um_symV ns xs B t s else um_symV ns xs B e s
  | .loop _ _ _, _ => False
  | .raw _ _ _, _ => False

theorem um_sym_exec {ns : List ℕ} {xs : List F} {B : ℕ} :
    ∀ (c : um_Cmd F) (s : um_St F), um_Bd B s → um_symV ns xs B c s →
      um_Exec ns xs B c s (um_symC ns xs c s) (um_sym ns xs c s) ∧ um_Bd B (um_sym ns xs c s)
  | .basic i, s, hb, ⟨hs, hv⟩ => by
    refine ⟨um_Exec.basic hs hb, ?_⟩
    cases i <;> simp only [um_sym, um_eff, um_wv, um_simple] at hv hs ⊢ <;>
      first | exact hb | exact um_Bd_setN hb hv | (intro j; exact hb j) | simp at hs
  | .seq a b, s, hb, ⟨ha, hb'⟩ => by
    obtain ⟨e1, b1⟩ := um_sym_exec a s hb ha
    obtain ⟨e2, b2⟩ := um_sym_exec b _ b1 hb'
    exact ⟨um_Exec.seq e1 e2, b2⟩
  | .ifN x y t e, s, hb, h => by
    simp only [um_symV] at h
    by_cases hxy : s.nr x = s.nr y
    · rw [if_pos hxy] at h
      obtain ⟨e1, b1⟩ := um_sym_exec t s hb h
      simp only [um_sym, um_symC, if_pos hxy]
      exact ⟨um_Exec.ifNT hb hxy e1 b1, b1⟩
    · rw [if_neg hxy] at h
      obtain ⟨e1, b1⟩ := um_sym_exec e s hb h
      simp only [um_sym, um_symC, if_neg hxy]
      exact ⟨um_Exec.ifNF hb hxy e1, b1⟩
  | .ifF x y t e, s, hb, h => by
    simp only [um_symV] at h
    by_cases hxy : s.fr x = s.fr y
    · rw [if_pos hxy] at h
      obtain ⟨e1, b1⟩ := um_sym_exec t s hb h
      simp only [um_sym, um_symC, if_pos hxy]
      exact ⟨um_Exec.ifFT hb hxy e1 b1, b1⟩
    · rw [if_neg hxy] at h
      obtain ⟨e1, b1⟩ := um_sym_exec e s hb h
      simp only [um_sym, um_symC, if_neg hxy]
      exact ⟨um_Exec.ifFF hb hxy e1, b1⟩
  | .loop _ _ _, _, _, h => h.elim
  | .raw _ _ _, _, _, h => h.elim

theorem um_symC_le (ns : List ℕ) (xs : List F) :
    ∀ (c : um_Cmd F) (s : um_St F), um_symC ns xs c s ≤ um_len c
  | .basic _, _ => le_rfl
  | .seq a b, s => by
    have := um_symC_le ns xs a s; have := um_symC_le ns xs b (um_sym ns xs a s)
    simp only [um_symC, um_len]; omega
  | .ifN x y t e, s => by
    have := um_symC_le ns xs t s; have := um_symC_le ns xs e s
    simp only [um_symC, um_len]; split_ifs <;> omega
  | .ifF x y t e, s => by
    have := um_symC_le ns xs t s; have := um_symC_le ns xs e s
    simp only [um_symC, um_len]; split_ifs <;> omega
  | .loop _ _ _, _ => Nat.zero_le _
  | .raw _ _ _, _ => Nat.zero_le _

theorem um_sp_sym {ns : List ℕ} {xs : List F} {B : ℕ} {c : um_Cmd F} {P Q : um_St F → Prop}
    (h : ∀ s, P s → um_Bd B s ∧ um_symV ns xs B c s ∧ Q (um_sym ns xs c s)) :
    um_Sp ns xs B c P Q (um_len c) := by
  intro s hs
  obtain ⟨hb, hv, hq⟩ := h s hs
  obtain ⟨e, _⟩ := um_sym_exec c s hb hv
  exact ⟨_, _, um_symC_le ns xs c s, e, hq⟩

theorem um_sp_sym' {ns : List ℕ} {xs : List F} {B : ℕ} {c : um_Cmd F} {P Q : um_St F → Prop}
    (h : ∀ s, P s → um_Bd B s ∧ um_symV ns xs B c s ∧
      (um_Bd B (um_sym ns xs c s) → Q (um_sym ns xs c s))) :
    um_Sp ns xs B c P Q (um_len c) := by
  intro s hs
  obtain ⟨hb, hv, hq⟩ := h s hs
  obtain ⟨e, b⟩ := um_sym_exec c s hb hv
  exact ⟨_, _, um_symC_le ns xs c s, e, hq b⟩

/-! ### The decision tree over a block -/

def um_noop : um_Cmd F := .basic (.literal 9 0)

/-- Compare field register 2 against each alphabet letter (scratch field register 4). -/
def um_chain : List F → (F → um_Cmd F) → um_Cmd F
  | [], _ => um_noop
  | a :: rest, K => .seq (.basic (.constant 4 a)) (.ifF 2 4 (K a) (um_chain rest K))

/-- Read symbol `pre.length` of the block at field address `nr 13 + 2 j` into field 2. -/
def um_ld (j : ℕ) : um_Cmd F :=
  .seq (.basic (.literal 14 (2 * j))) (.seq (.basic (.addNat 14 13 14)) (.basic (.load 2 14)))

def um_tree (al : List F) (leaf : List F → um_Cmd F) : ℕ → List F → um_Cmd F
  | 0, pre => leaf pre
  | n + 1, pre => .seq (um_ld pre.length) (um_chain al (fun a => um_tree al leaf n (pre ++ [a])))

section TreeSpec
variable {ns : List ℕ} {xs : List F} {B : ℕ}

/-- A predicate preserved by the tree's scratch writes. -/
structure um_TStab (B : ℕ) (P : um_St F → Prop) : Prop where
  bd : ∀ s, P s → um_Bd B s
  n9 : ∀ s v, P s → v ≤ B → P (um_setN s 9 v)
  n14 : ∀ s v, P s → v ≤ B → P (um_setN s 14 v)
  f2 : ∀ s v, P s → P (um_setF s 2 v)
  f4 : ∀ s v, P s → P (um_setF s 4 v)

theorem um_sp_chain {P Q : um_St F → Prop} (hP : um_TStab B P) (hQ : ∀ s, Q s → um_Bd B s)
    (v : F) (K : F → um_Cmd F) (TK : ℕ)
    (hK : um_Sp ns xs B (K v) (fun s => P s ∧ s.fr 2 = v) Q TK) :
    ∀ l : List F, v ∈ l →
      um_Sp ns xs B (um_chain l K) (fun s => P s ∧ s.fr 2 = v) Q (3 * l.length + TK) := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a rest ih =>
    intro hv
    have hc : um_Sp ns xs B (.basic (.constant 4 a)) (fun s => P s ∧ s.fr 2 = v)
        (fun s => P s ∧ s.fr 2 = v ∧ s.fr 4 = a) 1 := by
      apply um_sp_basic rfl
      intro s ⟨hs, h2⟩
      refine ⟨hP.bd s hs, hP.f4 s a hs, ?_, ?_⟩ <;> simp [um_eff, um_setF, h2]
    have hif : um_Sp ns xs B (.ifF 2 4 (K a) (um_chain rest K))
        (fun s => P s ∧ s.fr 2 = v ∧ s.fr 4 = a) Q (3 * rest.length + TK + 2) := by
      have := um_sp_ifF (ns := ns) (xs := xs) (B := B) (x := 2) (y := 4) (t := K a)
        (e := um_chain rest K) (P := fun s => P s ∧ s.fr 2 = v ∧ s.fr 4 = a) (Q := Q)
        (N1 := TK) (N2 := 3 * rest.length + TK)
        (fun s hs => hP.bd s hs.1) ?_ ?_
      · exact um_sp_conseq this (fun _ h => h) (fun _ h => h) (by omega)
      · intro s ⟨⟨hs, h2, h4⟩, heq⟩
        have hva : v = a := by rw [← h2, ← h4, heq]
        subst hva
        obtain ⟨n, s', hn, he, hq⟩ := hK s ⟨hs, h2⟩
        exact ⟨n, s', hn, he, hq, hQ s' hq⟩
      · intro s ⟨⟨hs, h2, h4⟩, hne⟩
        have hva : v ≠ a := by intro h; apply hne; rw [h2, h4, h]
        have hvr : v ∈ rest := by
          rcases List.mem_cons.mp hv with h | h
          · exact absurd h hva
          · exact h
        exact ih hvr s ⟨hs, h2⟩
    have := um_sp_seq hc hif
    exact um_sp_conseq this (fun _ h => h) (fun _ h => h) (by simp; omega)

theorem um_sp_ld {P : um_St F → Prop} (hP : um_TStab B P) (j base : ℕ) (v : F)
    (hj : 2 * j ≤ B) (hjb : base + 2 * j ≤ B)
    (hd : ∀ s, P s → s.nr 13 = base ∧ s.fr (base + 2 * j) = v) :
    um_Sp ns xs B (um_ld j) P (fun s => P s ∧ s.fr 2 = v) 3 := by
  apply um_sp_sym
  intro s hs
  obtain ⟨h13, hv⟩ := hd s hs
  refine ⟨hP.bd s hs, ?_, ?_⟩
  · simp only [um_ld, um_symV, um_sym, um_simple, um_wv, um_eff, um_setN, true_and,
      Function.update_self]
    refine ⟨hj, ?_⟩
    rw [Function.update_of_ne (by omega), h13]; exact ⟨hjb, Nat.zero_le _⟩
  · simp only [um_ld, um_sym, um_eff]
    have h1 := hP.n14 s _ hs hj
    have h2 := hP.n14 _ (base + 2 * j) h1 hjb
    have h2' : um_setN (um_setN s 14 (2 * j)) 14 ((um_setN s 14 (2 * j)).nr 13 +
        (um_setN s 14 (2 * j)).nr 14) = um_setN (um_setN s 14 (2 * j)) 14 (base + 2 * j) := by
      simp only [um_setN, Function.update_self]
      rw [Function.update_of_ne (by omega), h13]
    rw [h2']
    refine ⟨hP.f2 _ _ h2, ?_⟩
    have hf := (hd _ h2).2
    simpa [um_setN, um_setF] using hf

theorem um_sp_tree (al : List F) (hal : ∀ a : F, a ∈ al) (leaf : List F → um_Cmd F)
    {P Q : um_St F → Prop} (hP : um_TStab B P) (hQ : ∀ s, Q s → um_Bd B s)
    (ts base : ℕ) (u : ℕ → F)
    (hd : ∀ s, P s → s.nr 13 = base ∧ ∀ j < ts, s.fr (base + 2 * j) = u j)
    (hB : base + 2 * ts ≤ B) (TL : ℕ)
    (hleaf : um_Sp ns xs B (leaf ((List.range ts).map u)) P Q TL) :
    ∀ n pre, pre.length + n = ts → pre = (List.range pre.length).map u →
      um_Sp ns xs B (um_tree al leaf n pre) P Q (n * (3 * al.length + 4) + TL) := by
  intro n
  induction n with
  | zero =>
    intro pre hl hpre
    simp only [um_tree, zero_mul, zero_add]
    rw [hpre, show pre.length = ts by omega]; exact hleaf
  | succ n ih =>
    intro pre hl hpre
    have hj : pre.length < ts := by omega
    have hld := um_sp_ld (ns := ns) (xs := xs) hP pre.length base (u pre.length) (by omega)
      (by omega) (fun s hs => ⟨(hd s hs).1, (hd s hs).2 _ hj⟩)
    have hK : um_Sp ns xs B (um_tree al leaf n (pre ++ [u pre.length]))
        (fun s => P s ∧ s.fr 2 = u pre.length) Q (n * (3 * al.length + 4) + TL) := by
      have := ih (pre ++ [u pre.length]) (by simp; omega)
        (by simp only [List.length_append, List.length_singleton, List.range_succ,
          List.map_append, List.map_cons, List.map_nil]; rw [← hpre])
      exact um_sp_conseq this (fun _ h => h.1) (fun _ h => h) le_rfl
    have hch := um_sp_chain hP hQ (u pre.length) (fun a => um_tree al leaf n (pre ++ [a])) _ hK
      al (hal _)
    have := um_sp_seq hld hch
    exact um_sp_conseq this (fun _ h => h) (fun _ h => h) (by ring_nf; omega)

/-! ### Leaves -/

def um_outL : List F → um_Cmd F
  | [] => um_noop
  | v :: vs => .seq (.seq (.basic (.constant 0 v)) (.basic (.output 0))) (um_outL vs)

/-- A predicate on everything except field register 0, nat register 9 and the output. -/
structure um_OStab (B : ℕ) (R : um_St F → Prop) : Prop where
  bd : ∀ s, R s → um_Bd B s
  n9 : ∀ s, R s → R (um_setN s 9 0)
  f0 : ∀ s v, R s → R (um_setF s 0 v)
  out : ∀ s o, R s → R {s with out := o}

theorem um_sp_outL {R : um_St F → Prop} (hR : um_OStab B R) :
    ∀ (vs : List F) (o : List F), um_Sp ns xs B (um_outL vs) (fun s => R s ∧ s.out = o)
      (fun s => R s ∧ s.out = vs.reverse ++ o) (2 * vs.length + 1) := by
  intro vs
  induction vs with
  | nil =>
    intro o
    apply um_sp_basic rfl
    intro s ⟨hs, ho⟩
    exact ⟨hR.bd s hs, hR.n9 s hs, by simpa [um_eff, um_setN] using ho⟩
  | cons v vs ih =>
    intro o
    have h1 : um_Sp ns xs B (.seq (.basic (.constant 0 v)) (.basic (.output 0)))
        (fun s => R s ∧ s.out = o) (fun s => R s ∧ s.out = v :: o) 2 := by
      apply um_sp_sym
      intro s ⟨hs, ho⟩
      refine ⟨hR.bd s hs, by simp [um_symV, um_simple, um_wv], ?_⟩
      simp only [um_sym, um_eff]
      refine ⟨hR.out _ _ (hR.f0 s v hs), ?_⟩
      simp [um_setF, ho]
    have := um_sp_seq h1 (ih (v :: o))
    exact um_sp_conseq this (fun _ h => h) (fun _ h => by simpa using h) (by simp; omega)

def um_cmpA (c : ℕ) (v : F) : um_Cmd F :=
  .seq (.basic (.constant 0 v)) (.seq (.basic (.literal 14 c)) (.seq (.basic (.addNat 14 15 14))
    (.basic (.input 6 14))))

def um_cmp1 (c : ℕ) (v : F) : um_Cmd F :=
  .seq (um_cmpA c v) (.ifF 0 6 um_noop (.basic (.literal 16 0)))

def um_cmpL : ℕ → List F → um_Cmd F
  | _, [] => um_noop
  | c, v :: vs => .seq (um_cmp1 c v) (um_cmpL (c + 1) vs)

/-- A predicate on everything except nat 9, 14, 16 and field 0, 6. -/
structure um_CStab (B : ℕ) (R : um_St F → Prop) : Prop where
  bd : ∀ s, R s → um_Bd B s
  n9 : ∀ s, R s → R (um_setN s 9 0)
  n14 : ∀ s v, R s → v ≤ B → R (um_setN s 14 v)
  n16 : ∀ s, R s → R (um_setN s 16 0)
  f0 : ∀ s v, R s → R (um_setF s 0 v)
  f6 : ∀ s v, R s → R (um_setF s 6 v)

theorem um_sp_cmpL {R : um_St F → Prop} (hR : um_CStab B R) (yb : ℕ)
    (h15 : ∀ s, R s → s.nr 15 = yb) :
    ∀ (vs : List F) (c : ℕ) (Φ : Prop), yb + c + vs.length ≤ B →
      um_Sp ns xs B (um_cmpL c vs) (fun s => R s ∧ s.nr 16 ≤ 1 ∧ (s.nr 16 = 1 ↔ Φ))
        (fun s => R s ∧ s.nr 16 ≤ 1 ∧ (s.nr 16 = 1 ↔
          Φ ∧ ∀ i < vs.length, xs.getD (yb + c + i) 0 = vs.getD i 0))
        (8 * vs.length + 1) := by
  intro vs
  induction vs with
  | nil =>
    intro c Φ _
    apply um_sp_basic rfl
    intro s ⟨hs, h16, hΦ⟩
    refine ⟨hR.bd s hs, hR.n9 s hs, ?_⟩
    simp only [um_eff, um_setN, Function.update_apply]
    simp [h16, hΦ]
  | cons v vs ih =>
    intro c Φ hB
    have hc : c ≤ B := by simp at hB; omega
    have hyc : yb + c ≤ B := by simp at hB; omega
    have hA : um_Sp ns xs B (um_cmpA c v) (fun s => R s ∧ s.nr 16 ≤ 1 ∧ (s.nr 16 = 1 ↔ Φ))
        (fun s => (R s ∧ s.nr 16 ≤ 1 ∧ (s.nr 16 = 1 ↔ Φ)) ∧ s.fr 0 = v ∧
          s.fr 6 = xs.getD (yb + c) 0) 4 := by
      apply um_sp_sym
      intro s ⟨hs, h16, hΦ⟩
      have hs1 := hR.f0 s v hs
      have hs2 := hR.n14 _ c hs1 hc
      have hs3 := hR.n14 _ (yb + c) hs2 hyc
      have hs4 := hR.f6 _ (xs.getD (yb + c) 0) hs3
      have h15' := h15 _ hs1
      simp only [um_setF] at h15'
      refine ⟨hR.bd s hs, ⟨⟨rfl, Nat.zero_le _⟩, ⟨rfl, hc⟩, ⟨rfl, ?_⟩, ⟨rfl, Nat.zero_le _⟩⟩, ?_⟩
      · simp only [um_wv, um_sym, um_eff, um_setN, um_setF, Function.update_self]
        rw [Function.update_of_ne (by omega), h15']; exact hyc
      · have e : um_sym ns xs (um_cmpA c v) s =
            um_setF (um_setN (um_setN (um_setF s 0 v) 14 c) 14 (yb + c)) 6
              (xs.getD (yb + c) 0) := by
          simp only [um_cmpA, um_sym, um_eff]
          simp only [um_setF, um_setN, Function.update_self]
          rw [Function.update_of_ne (by omega), h15']
        rw [e]
        refine ⟨⟨hs4, ?_, ?_⟩, ?_, ?_⟩
        · simp only [um_setF, um_setN]; rw [Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]; exact h16
        · simp only [um_setF, um_setN]; rw [Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]; exact hΦ
        · simp [um_setF, um_setN]
        · simp [um_setF, um_setN]
    have hI : um_Sp ns xs B (.ifF 0 6 um_noop (.basic (.literal 16 0)))
        (fun s => (R s ∧ s.nr 16 ≤ 1 ∧ (s.nr 16 = 1 ↔ Φ)) ∧ s.fr 0 = v ∧
          s.fr 6 = xs.getD (yb + c) 0)
        (fun s => R s ∧ s.nr 16 ≤ 1 ∧ (s.nr 16 = 1 ↔ (Φ ∧ xs.getD (yb + c) 0 = v)))
        (max 1 1 + 2) := by
      refine um_sp_ifF (fun (s : um_St F) (hs : (R s ∧ s.nr 16 ≤ 1 ∧ (s.nr 16 = 1 ↔ Φ)) ∧ s.fr 0 = v ∧
          s.fr 6 = xs.getD (yb + c) 0) => hR.bd s hs.1.1) ?_ ?_
      · apply um_sp_basic rfl
        intro s ⟨⟨⟨hs, h16, hΦ⟩, h0, h6⟩, heq⟩
        refine ⟨hR.bd s hs, ⟨hR.n9 s hs, ?_, ?_⟩, hR.bd _ (hR.n9 s hs)⟩
        · simp only [um_eff, um_setN]; rw [Function.update_of_ne (by omega)]; exact h16
        · simp only [um_eff, um_setN]; rw [Function.update_of_ne (by omega), hΦ]
          rw [← h0, ← h6, heq]; simp
      · apply um_sp_basic rfl
        intro s ⟨⟨⟨hs, h16, hΦ⟩, h0, h6⟩, hne⟩
        refine ⟨hR.bd s hs, hR.n16 s hs, ?_, ?_⟩
        · simp [um_eff, um_setN]
        · simp only [um_eff, um_setN, Function.update_self]
          constructor
          · intro h; omega
          · intro h; exact absurd (by rw [h0, h6, h.2]) hne
    have h1 := um_sp_seq hA hI
    have h2 := ih (c + 1) (Φ ∧ xs.getD (yb + c) 0 = v) (by simp at hB; omega)
    have := um_sp_seq h1 h2
    refine um_sp_conseq this (fun _ h => h) ?_ (by simp; omega)
    intro s ⟨hs, h16, hiff⟩
    refine ⟨hs, h16, ?_⟩
    rw [hiff]
    constructor
    · rintro ⟨⟨hΦ, h0⟩, hrest⟩
      refine ⟨hΦ, fun i hi => ?_⟩
      cases i with
      | zero => simpa using h0
      | succ i =>
        have := hrest i (by simp at hi; omega)
        simpa [show yb + (c + 1) + i = yb + c + (i + 1) by omega] using this
    · rintro ⟨hΦ, hall⟩
      refine ⟨⟨hΦ, by simpa using hall 0 (by simp)⟩, fun i hi => ?_⟩
      have := hall (i + 1) (by simp; omega)
      simpa [show yb + (c + 1) + i = yb + c + (i + 1) by omega] using this

end TreeSpec

end SubspaceEvasion312.Explicit.Dev.Goal
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal
open SubspaceEvasion312.Explicit

variable {F : Type} [Field F]

/-! ## The concrete programs

Nat registers: 0 = N, 1 = m, 2 = k, 3 = M, 4 = 1, 5 = 2, 6 = 0, 7/8 translation,
9, 10, 14 scratch, 11 = x loop, 12 = block loop, 13 = block address, 15 = y offset,
16 = flag, 61 = loop temporary, 100+ = encoder. Field: 0, 2, 4, 6 scratch, data at 2 (8 + i). -/

def um_seqL : List (Instruction F) → um_Cmd F
  | [] => um_noop
  | [i] => .basic i
  | i :: rest => .seq (.basic i) (um_seqL rest)

def um_setupL (num den b t : ℕ) : List (Instruction F) :=
  [.inputNat 0 0, .literal 4 1, .literal 5 2, .literal 6 0, .literal 9 num, .mulNat 9 9 0,
   .literal 10 (den * b), .divNat 1 9 10, .literal 10 b, .mulNat 9 10 1, .subNat 2 0 9,
   .literal 10 t, .mulNat 3 10 1, .literal 8 16]

def um_g {ts b : ℕ} (f : Vec F ts → Vec F b) (pre : List F) : List F :=
  vectorData (f (fun i => pre.getD i 0))

def um_xloop : um_Cmd F :=
  .seq (.basic (.literal 11 0)) (.loop 11 2 (.seq (.basic (.input 0 11)) (.basic (.output 0))))

def um_pre13 (ts : ℕ) : List (Instruction F) :=
  [.literal 9 ts, .mulNat 13 12 9, .literal 9 8, .addNat 13 13 9, .addNat 13 13 13]

def um_pre15 (b : ℕ) : List (Instruction F) :=
  [.literal 9 b, .mulNat 15 12 9, .addNat 15 15 2]

def um_bodyI (al : List F) {ts b : ℕ} (f : Vec F ts → Vec F b) : um_Cmd F :=
  .seq (um_seqL (um_pre13 ts)) (um_tree al (fun pre => um_outL (um_g f pre)) ts [])

def um_bodyM (al : List F) {ts b : ℕ} (f : Vec F ts → Vec F b) : um_Cmd F :=
  .seq (um_seqL (um_pre13 ts)) (.seq (um_seqL (um_pre15 b))
    (um_tree al (fun pre => um_cmpL 0 (um_g f pre)) ts []))

def um_final : um_Cmd F :=
  .ifN 16 4 (.seq (.basic (.constant 0 1)) (.basic (.output 0)))
    (.seq (.basic (.constant 0 0)) (.basic (.output 0)))

def um_indexC (al : List F) (enc : Program F) (num den t : ℕ) {ts b : ℕ}
    (f : Vec F ts → Vec F b) : um_Cmd F :=
  .seq (um_seqL (um_setupL num den b t)) (.seq (um_encC enc) (.seq um_xloop
    (.seq (.basic (.literal 12 0)) (.loop 12 1 (um_bodyI al f)))))

def um_memberC (al : List F) (enc : Program F) (num den t : ℕ) {ts b : ℕ}
    (f : Vec F ts → Vec F b) : um_Cmd F :=
  .seq (um_seqL (um_setupL num den b t)) (.seq (um_encC enc) (.seq (.basic (.literal 16 1))
    (.seq (.basic (.literal 12 0)) (.seq (.loop 12 1 (um_bodyM al f)) um_final))))

/-! ### Setup -/

def um_s0 : um_St F := ⟨fun _ => 0, fun _ => 0, []⟩

theorem um_setup_spec {xs : List F} {B : ℕ} (N num den b t : ℕ)
    (hB : N + num + num * N + den * b + b + b * (num * N / (den * b)) + t +
      t * (num * N / (den * b)) + 16 ≤ B) :
    um_Sp [N] xs B (um_seqL (um_setupL num den b t)) (fun s => s = um_s0)
      (fun s => um_W0 s (N - b * (num * N / (den * b))) (t * (num * N / (den * b))) ∧
        um_Init s ∧ s.nr 0 = N ∧ s.nr 1 = num * N / (den * b) ∧ s.out = [] ∧
        (∀ a, s.fr a = 0) ∧ um_Bd B s) 14 := by
  apply um_sp_sym'
  rintro s rfl
  refine ⟨fun _ => Nat.zero_le _, ?_, ?_⟩
  · simp only [um_setupL, um_seqL, um_symV, um_sym, um_simple, um_wv, um_eff, um_setN, um_s0,
      Function.update_apply, true_and]
    simp
    have := Nat.div_le_self (num * N) (den * b)
    omega
  · intro hbd
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, hbd⟩ <;>
      simp [um_setupL, um_seqL, um_sym, um_eff, um_setN, um_s0, Function.update_apply]
    all_goals (intro j; split_ifs <;> omega)

/-! ### The post-encoder context -/

structure um_PC (B N m k : ℕ) (D : List F) (L : ℕ) (s : um_St F) : Prop where
  bd : um_Bd B s
  n0 : s.nr 0 = N
  n1 : s.nr 1 = m
  n2 : s.nr 2 = k
  n4 : s.nr 4 = 1
  dat : ∀ i < L, s.fr (2 * (8 + i)) = D.getD i 0

section PC
variable {B N m k L : ℕ} {D : List F}

theorem um_PC_setN {s : um_St F} (h : um_PC B N m k D L s) (j v : ℕ) (hj0 : j ≠ 0) (hj1 : j ≠ 1)
    (hj2 : j ≠ 2) (hj4 : j ≠ 4) (hv : v ≤ B) : um_PC B N m k D L (um_setN s j v) :=
  ⟨um_Bd_setN h.bd hv, by rw [um_setN_ne (by omega)]; exact h.n0,
    by rw [um_setN_ne (by omega)]; exact h.n1, by rw [um_setN_ne (by omega)]; exact h.n2,
    by rw [um_setN_ne (by omega)]; exact h.n4, h.dat⟩

theorem um_PC_setF {s : um_St F} (h : um_PC B N m k D L s) (a : ℕ) (v : F) (ha : a < 16) :
    um_PC B N m k D L (um_setF s a v) :=
  ⟨h.bd, h.n0, h.n1, h.n2, h.n4, fun i hi => by
    simp only [um_setF]; rw [Function.update_of_ne (by omega)]; exact h.dat i hi⟩

theorem um_PC_out {s : um_St F} (h : um_PC B N m k D L s) (o : List F) :
    um_PC B N m k D L {s with out := o} :=
  ⟨h.bd, h.n0, h.n1, h.n2, h.n4, h.dat⟩

theorem um_PC_inc {s : um_St F} (h : um_PC B N m k D L s) (j : ℕ) (hj0 : j ≠ 0) (hj1 : j ≠ 1)
    (hj2 : j ≠ 2) (hj4 : j ≠ 4) (hj61 : j ≠ 61) (hB : s.nr j + 1 ≤ B) (hB1 : 1 ≤ B) :
    um_PC B N m k D L (um_inc s j) := by
  have e : um_inc s j = um_setN (um_setN s 61 1) j (s.nr j + 1) := by
    simp only [um_inc, um_setN]
    rw [Function.update_of_ne (by omega)]
  rw [e]
  exact um_PC_setN (um_PC_setN h 61 1 (by omega) (by omega) (by omega) (by omega) hB1) j _
    hj0 hj1 hj2 hj4 hB

theorem um_inc_nr {s : um_St F} (j i : ℕ) (hi : i ≠ j) (hi61 : i ≠ 61) :
    (um_inc s j).nr i = s.nr i := by
  simp only [um_inc]; rw [Function.update_of_ne hi, Function.update_of_ne hi61]

theorem um_inc_self {s : um_St F} (j : ℕ) (hj : j ≠ 61) : (um_inc s j).nr j = s.nr j + 1 := by
  simp only [um_inc, Function.update_self]; rw [Function.update_of_ne hj]

end PC

/-! ### The x loop -/

theorem um_sp_xloop {B N m k L : ℕ} {D : List F} (xs : List F) (hk : xs.length = k)
    (hB : k + 1 ≤ B) :
    um_Sp [N] xs B um_xloop (fun s => um_PC B N m k D L s ∧ s.out = [])
      (fun s => um_PC B N m k D L s ∧ s.out = xs.reverse) (1 + (k * (2 + 4) + 1)) := by
  have h1 : um_Sp [N] xs B (.basic (.literal 11 0)) (fun s => um_PC B N m k D L s ∧ s.out = [])
      (fun s => um_PC B N m k D L s ∧ s.nr 11 = 0 ∧ s.out = (xs.take 0).reverse) 1 := by
    apply um_sp_basic rfl
    intro s ⟨hs, ho⟩
    exact ⟨hs.bd, um_PC_setN hs 11 0 (by omega) (by omega) (by omega) (by omega) (Nat.zero_le _),
      by simp [um_eff, um_setN], by simpa [um_eff, um_setN] using ho⟩
  have h2 := um_sp_loop (ns := [N]) (xs := xs) (B := B) (i := 11) (n := 2)
    (body := .seq (.basic (.input 0 11)) (.basic (.output 0)))
    (fun j s => um_PC B N m k D L s ∧ s.nr 11 = j ∧ s.out = (xs.take j).reverse) 0 k 2
    (Nat.zero_le _) (fun j s _ _ hs => ⟨hs.2.1, hs.1.n2, hs.1.bd⟩) ?_
  · have := um_sp_seq h1 h2
    refine um_sp_conseq this (fun _ h => h) ?_ (by omega)
    intro s ⟨hs, _, ho⟩
    exact ⟨hs, by rw [ho, ← hk, List.take_length]⟩
  · intro j _ hj
    apply um_sp_sym
    intro s ⟨hs, h11, ho⟩
    refine ⟨hs.bd, ⟨⟨rfl, Nat.zero_le _⟩, ⟨rfl, Nat.zero_le _⟩⟩, ?_⟩
    simp only [um_sym, um_eff]
    set s1 : um_St F := {um_setF s 0 (xs.getD (s.nr 11) 0) with
      out := (um_setF s 0 (xs.getD (s.nr 11) 0)).fr 0 :: (um_setF s 0 (xs.getD (s.nr 11) 0)).out}
      with hs1
    have hP1 : um_PC B N m k D L s1 := um_PC_out (um_PC_setF hs 0 _ (by omega)) _
    have hj11 : s1.nr 11 = j := h11
    have hP2 := um_PC_inc hP1 11 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    refine ⟨hP1.bd, hP2.bd, hP2, ?_, ?_⟩
    · rw [um_inc_self 11 (by omega), hj11]
    · simp only [um_inc, hs1, um_setF, Function.update_self, ho, h11]
      rw [List.take_add_one, List.reverse_append]
      congr 1
      rw [List.getElem?_eq_getElem (by omega)]
      simp [List.getElem?_eq_getElem (show j < xs.length by omega)]

/-! ### The index block loop -/

theorem um_g_length {ts b : ℕ} (f : Vec F ts → Vec F b) (pre : List F) :
    (um_g f pre).length = b := by simp [um_g, vectorData]

def um_bk {ts b : ℕ} (f : Vec F ts → Vec F b) (D : List F) (i : ℕ) : List F :=
  um_g f ((List.range ts).map (fun j => D.getD (i * ts + j) 0))

theorem um_sp_pre13 {xs : List F} {B N m k L : ℕ} {D : List F} (ts i : ℕ) (O : List F)
    (E : um_St F → Prop) (hE : ∀ s j v, E s → (j = 9 ∨ j = 13) → E (um_setN s j v))
    (hB : 2 * (8 + i * ts) + ts ≤ B) :
    um_Sp [N] xs B (um_seqL (um_pre13 ts))
      (fun s => (um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.out = O) ∧ E s)
      (fun s => (um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.nr 13 = 2 * (8 + i * ts) ∧ s.out = O) ∧ E s)
      (um_len (um_seqL (F := F) (um_pre13 ts))) := by
  apply um_sp_sym
  intro s ⟨⟨hs, h12, ho⟩, hEs⟩
  refine ⟨hs.bd, ?_, ?_⟩
  · simp only [um_pre13, um_seqL, um_symV, um_sym, um_simple, um_wv, um_eff, um_setN,
      Function.update_apply, true_and]
    simp [h12]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · have e : um_sym [N] xs (um_seqL (um_pre13 ts)) s =
        um_setN (um_setN (um_setN (um_setN (um_setN s 9 ts) 13 (i * ts)) 9 8) 13 (i * ts + 8))
          13 (2 * (8 + i * ts)) := by
      simp only [um_pre13, um_seqL, um_sym, um_eff]
      simp only [um_setN, Function.update_apply, h12]
      simp
      congr 1; ring
    rw [e]
    have hit : i * ts ≤ B := by omega
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · refine um_PC_setN (um_PC_setN (um_PC_setN (um_PC_setN (um_PC_setN hs 9 ts ?_ ?_ ?_ ?_ ?_)
        13 _ ?_ ?_ ?_ ?_ hit) 9 8 ?_ ?_ ?_ ?_ ?_) 13 _ ?_ ?_ ?_ ?_ ?_) 13 _ ?_ ?_ ?_ ?_ ?_ <;>
        omega
    · simp only [um_setN, Function.update_apply]; simp [h12]
    · simp [um_setN]
    · simpa [um_setN] using ho
    · exact hE _ _ _ (hE _ _ _ (hE _ _ _ (hE _ _ _ (hE _ _ _ hEs (Or.inl rfl)) (Or.inr rfl))
        (Or.inl rfl)) (Or.inr rfl)) (Or.inr rfl)

theorem um_sp_bodyI (al : List F) (hal : ∀ a : F, a ∈ al) {ts b : ℕ} (f : Vec F ts → Vec F b)
    {xs : List F} {B N m k L : ℕ} {D : List F} (i : ℕ) (O : List F)
    (hL : (i + 1) * ts ≤ L) (hB : 2 * (8 + i * ts) + 2 * ts ≤ B) :
    um_Sp [N] xs B (um_bodyI al f)
      (fun s => um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.out = O)
      (fun s => um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.out = (um_bk f D i).reverse ++ O)
      (um_len (um_seqL (F := F) (um_pre13 ts)) + (ts * (3 * al.length + 4) + (2 * b + 1))) := by
  have h1' := um_sp_pre13 (xs := xs) (B := B) (N := N) (m := m) (k := k) (D := D) (L := L) ts i O
    (fun _ => True) (fun _ _ _ _ _ => trivial) (by omega)
  have h1 : um_Sp [N] xs B (um_seqL (um_pre13 ts))
      (fun s => um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.out = O)
      (fun s => um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.nr 13 = 2 * (8 + i * ts) ∧ s.out = O)
      (um_len (um_seqL (F := F) (um_pre13 ts))) :=
    um_sp_conseq h1' (fun _ h => ⟨h, trivial⟩) (fun _ h => h.1) le_rfl
  set base := 2 * (8 + i * ts) with hbase
  let P : um_St F → Prop := fun s =>
    um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.nr 13 = base ∧ s.out = O
  have hP : um_TStab B P := by
    refine ⟨fun s hs => hs.1.bd, ?_, ?_, ?_, ?_⟩
    · intro s v hs hv
      exact ⟨um_PC_setN hs.1 9 v (by omega) (by omega) (by omega) (by omega) hv,
        by rw [um_setN_ne (by omega)]; exact hs.2.1, by rw [um_setN_ne (by omega)]; exact hs.2.2.1,
        hs.2.2.2⟩
    · intro s v hs hv
      exact ⟨um_PC_setN hs.1 14 v (by omega) (by omega) (by omega) (by omega) hv,
        by rw [um_setN_ne (by omega)]; exact hs.2.1, by rw [um_setN_ne (by omega)]; exact hs.2.2.1,
        hs.2.2.2⟩
    · intro s v hs
      exact ⟨um_PC_setF hs.1 2 v (by omega), hs.2.1, hs.2.2.1, hs.2.2.2⟩
    · intro s v hs
      exact ⟨um_PC_setF hs.1 4 v (by omega), hs.2.1, hs.2.2.1, hs.2.2.2⟩
  let Q : um_St F → Prop := fun s =>
    um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.nr 13 = base ∧ s.out = (um_bk f D i).reverse ++ O
  let R : um_St F → Prop := fun s => um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.nr 13 = base
  have hR : um_OStab B R := by
    refine ⟨fun s hs => hs.1.bd, ?_, ?_, ?_⟩
    · intro s hs
      exact ⟨um_PC_setN hs.1 9 0 (by omega) (by omega) (by omega) (by omega) (Nat.zero_le _),
        by rw [um_setN_ne (by omega)]; exact hs.2.1, by rw [um_setN_ne (by omega)]; exact hs.2.2⟩
    · intro s v hs
      exact ⟨um_PC_setF hs.1 0 v (by omega), hs.2.1, hs.2.2⟩
    · intro s o hs
      exact ⟨um_PC_out hs.1 o, hs.2.1, hs.2.2⟩
  have hleaf : um_Sp [N] xs B (um_outL (um_g f ((List.range ts).map
      (fun j => D.getD (i * ts + j) 0)))) P Q (2 * b + 1) := by
    have := um_sp_outL (ns := [N]) (xs := xs) hR (um_g f ((List.range ts).map
      (fun j => D.getD (i * ts + j) 0))) O
    rw [um_g_length] at this
    refine um_sp_conseq this ?_ ?_ le_rfl
    · intro s hs; exact ⟨⟨hs.1, hs.2.1, hs.2.2.1⟩, hs.2.2.2⟩
    · intro s hs; exact ⟨hs.1.1, hs.1.2.1, hs.1.2.2, hs.2⟩
  have htree := um_sp_tree (ns := [N]) (xs := xs) al hal (fun pre => um_outL (um_g f pre)) hP
    (fun s hs => hs.1.bd) ts base (fun j => D.getD (i * ts + j) 0)
    (fun s hs => ⟨hs.2.2.1, fun j hj => by
      have := hs.1.dat (i * ts + j) (by nlinarith)
      rw [show base + 2 * j = 2 * (8 + (i * ts + j)) by omega]; exact this⟩)
    (by omega) _ hleaf ts [] (by simp) (by simp)
  have := um_sp_seq h1 htree
  refine um_sp_conseq this (fun _ h => h) ?_ le_rfl
  intro s hs; exact ⟨hs.1, hs.2.1, hs.2.2.2⟩

theorem um_sp_bloopI (al : List F) (hal : ∀ a : F, a ∈ al) {ts b : ℕ} (f : Vec F ts → Vec F b)
    {xs : List F} {B N m k L : ℕ} {D : List F} (X0 : List F)
    (hL : m * ts ≤ L) (hB : 2 * (8 + m * ts) + 2 * ts ≤ B) (hm : m + 1 ≤ B) :
    um_Sp [N] xs B (.seq (.basic (.literal 12 0)) (.loop 12 1 (um_bodyI al f)))
      (fun s => um_PC B N m k D L s ∧ s.out = X0.reverse)
      (fun s => um_PC B N m k D L s ∧ s.out = (X0 ++ (List.range m).flatMap (um_bk f D)).reverse)
      (1 + (m * (um_len (um_seqL (F := F) (um_pre13 ts)) + (ts * (3 * al.length + 4) +
        (2 * b + 1)) + 4) + 1)) := by
  let I : ℕ → um_St F → Prop := fun i s => um_PC B N m k D L s ∧ s.nr 12 = i ∧
    s.out = (X0 ++ (List.range i).flatMap (um_bk f D)).reverse
  have h1 : um_Sp [N] xs B (.basic (.literal 12 0))
      (fun s => um_PC B N m k D L s ∧ s.out = X0.reverse) (I 0) 1 := by
    apply um_sp_basic rfl
    intro s ⟨hs, ho⟩
    exact ⟨hs.bd, um_PC_setN hs 12 0 (by omega) (by omega) (by omega) (by omega) (Nat.zero_le _),
      by simp [um_eff, um_setN], by simpa [um_eff, um_setN] using ho⟩
  have h2 := um_sp_loop (ns := [N]) (xs := xs) (B := B) (i := 12) (n := 1) (body := um_bodyI al f)
    I 0 m (um_len (um_seqL (F := F) (um_pre13 ts)) + (ts * (3 * al.length + 4) + (2 * b + 1)))
    (Nat.zero_le _) (fun j s _ _ hs => ⟨hs.2.1, hs.1.n1, hs.1.bd⟩) ?_
  · have := um_sp_seq h1 h2
    exact um_sp_conseq this (fun _ h => h) (fun s hs => ⟨hs.1, hs.2.2⟩) (by simp)
  · intro i _ hi
    have hb := um_sp_bodyI (xs := xs) (B := B) (N := N) (m := m) (k := k) (L := L) (D := D) al hal f
      i (X0 ++ (List.range i).flatMap (um_bk f D)).reverse (by nlinarith) (by nlinarith)
    refine um_sp_conseq hb (fun _ h => h) ?_ le_rfl
    intro s ⟨hs, h12, ho⟩
    have hP2 := um_PC_inc hs 12 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    refine ⟨hs.bd, hP2.bd, hP2, by rw [um_inc_self 12 (by omega), h12], ?_⟩
    simp only [um_inc, ho, List.range_succ, List.flatMap_append, List.flatMap_singleton,
      List.reverse_append, List.append_assoc]

/-! ### The member block loop -/

theorem um_sp_pre15 {xs : List F} {B N m k L : ℕ} {D : List F} (b i base : ℕ) (O : List F)
    (Φ : Prop) (hB : i * b + k + b ≤ B) :
    um_Sp [N] xs B (um_seqL (um_pre15 b))
      (fun s => (um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.nr 13 = base ∧ s.out = O) ∧
        s.nr 16 ≤ 1 ∧ (s.nr 16 = 1 ↔ Φ))
      (fun s => ((um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.nr 13 = base ∧ s.out = O) ∧
        s.nr 15 = i * b + k) ∧ s.nr 16 ≤ 1 ∧ (s.nr 16 = 1 ↔ Φ))
      (um_len (um_seqL (F := F) (um_pre15 b))) := by
  apply um_sp_sym
  intro s ⟨⟨hs, h12, h13, ho⟩, h16, hΦ⟩
  refine ⟨hs.bd, ?_, ?_⟩
  · simp only [um_pre15, um_seqL, um_symV, um_sym, um_simple, um_wv, um_eff, um_setN,
      Function.update_apply, true_and]
    simp [h12, hs.n2]
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  · have e : um_sym [N] xs (um_seqL (um_pre15 b)) s =
        um_setN (um_setN (um_setN s 9 b) 15 (i * b)) 15 (i * b + k) := by
      simp only [um_pre15, um_seqL, um_sym, um_eff]
      simp only [um_setN, Function.update_apply, h12, hs.n2]
      simp
    rw [e]
    have hib : i * b ≤ B := by nlinarith
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · refine um_PC_setN (um_PC_setN (um_PC_setN hs 9 b ?_ ?_ ?_ ?_ ?_) 15 _ ?_ ?_ ?_ ?_ hib)
        15 _ ?_ ?_ ?_ ?_ ?_ <;> nlinarith
    · simp only [um_setN, Function.update_apply]; simp [h12]
    · simp only [um_setN, Function.update_apply]; simp [h13]
    · simpa [um_setN] using ho
    · simp [um_setN]
    · simp only [um_setN, Function.update_apply]; simpa using h16
    · simp only [um_setN, Function.update_apply]; simpa using hΦ

theorem um_sp_bodyM (al : List F) (hal : ∀ a : F, a ∈ al) {ts b : ℕ} (f : Vec F ts → Vec F b)
    {xs : List F} {B N m k L : ℕ} {D : List F} (i : ℕ) (Φ : Prop)
    (hL : (i + 1) * ts ≤ L) (hB : 2 * (8 + i * ts) + 2 * ts ≤ B) (hB2 : i * b + k + b ≤ B) :
    um_Sp [N] xs B (um_bodyM al f)
      (fun s => (um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.out = []) ∧
        s.nr 16 ≤ 1 ∧ (s.nr 16 = 1 ↔ Φ))
      (fun s => (um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.out = []) ∧ s.nr 16 ≤ 1 ∧
        (s.nr 16 = 1 ↔ Φ ∧ ∀ c < b, xs.getD (i * b + k + c) 0 = (um_bk f D i).getD c 0))
      (um_len (um_seqL (F := F) (um_pre13 ts)) + (um_len (um_seqL (F := F) (um_pre15 b)) +
        (ts * (3 * al.length + 4) + (8 * b + 1)))) := by
  set base := 2 * (8 + i * ts) with hbase
  have h1 := um_sp_pre13 (xs := xs) (B := B) (N := N) (m := m) (k := k) (D := D) (L := L)
    ts i [] (fun s => s.nr 16 ≤ 1 ∧ (s.nr 16 = 1 ↔ Φ))
    (fun s j v hs hj => by
      rcases hj with rfl | rfl <;> exact ⟨by rw [um_setN_ne (by omega)]; exact hs.1,
        by rw [um_setN_ne (by omega)]; exact hs.2⟩) (by omega)
  have h2 := um_sp_pre15 (xs := xs) (B := B) (N := N) (m := m) (k := k) (D := D) (L := L)
    b i base [] Φ hB2
  let R : um_St F → Prop := fun s =>
    (um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.nr 13 = base ∧ s.out = []) ∧ s.nr 15 = i * b + k
  let P : um_St F → Prop := fun s => R s ∧ s.nr 16 ≤ 1 ∧ (s.nr 16 = 1 ↔ Φ)
  let Q : um_St F → Prop := fun s => R s ∧ s.nr 16 ≤ 1 ∧
    (s.nr 16 = 1 ↔ Φ ∧ ∀ c < b,
      xs.getD (i * b + k + 0 + c) 0 = (um_bk f D i).getD c 0)
  have hR : um_CStab B R := by
    refine ⟨fun s hs => hs.1.1.bd, ?_, ?_, ?_, ?_, ?_⟩
    · intro s hs
      exact ⟨⟨um_PC_setN hs.1.1 9 0 (by omega) (by omega) (by omega) (by omega) (Nat.zero_le _),
        by rw [um_setN_ne (by omega)]; exact hs.1.2.1,
        by rw [um_setN_ne (by omega)]; exact hs.1.2.2.1, hs.1.2.2.2⟩,
        by rw [um_setN_ne (by omega)]; exact hs.2⟩
    · intro s v hs hv
      exact ⟨⟨um_PC_setN hs.1.1 14 v (by omega) (by omega) (by omega) (by omega) hv,
        by rw [um_setN_ne (by omega)]; exact hs.1.2.1,
        by rw [um_setN_ne (by omega)]; exact hs.1.2.2.1, hs.1.2.2.2⟩,
        by rw [um_setN_ne (by omega)]; exact hs.2⟩
    · intro s hs
      exact ⟨⟨um_PC_setN hs.1.1 16 0 (by omega) (by omega) (by omega) (by omega) (Nat.zero_le _),
        by rw [um_setN_ne (by omega)]; exact hs.1.2.1,
        by rw [um_setN_ne (by omega)]; exact hs.1.2.2.1, hs.1.2.2.2⟩,
        by rw [um_setN_ne (by omega)]; exact hs.2⟩
    · intro s v hs
      exact ⟨⟨um_PC_setF hs.1.1 0 v (by omega), hs.1.2.1, hs.1.2.2.1, hs.1.2.2.2⟩, hs.2⟩
    · intro s v hs
      exact ⟨⟨um_PC_setF hs.1.1 6 v (by omega), hs.1.2.1, hs.1.2.2.1, hs.1.2.2.2⟩, hs.2⟩
  have hP : um_TStab B P := by
    refine ⟨fun s hs => hs.1.1.1.bd, ?_, ?_, ?_, ?_⟩
    · intro s v hs hv
      exact ⟨⟨⟨um_PC_setN hs.1.1.1 9 v (by omega) (by omega) (by omega) (by omega) hv,
        by rw [um_setN_ne (by omega)]; exact hs.1.1.2.1,
        by rw [um_setN_ne (by omega)]; exact hs.1.1.2.2.1, hs.1.1.2.2.2⟩,
        by rw [um_setN_ne (by omega)]; exact hs.1.2⟩,
        by rw [um_setN_ne (by omega)]; exact hs.2.1, by rw [um_setN_ne (by omega)]; exact hs.2.2⟩
    · intro s v hs hv
      exact ⟨⟨⟨um_PC_setN hs.1.1.1 14 v (by omega) (by omega) (by omega) (by omega) hv,
        by rw [um_setN_ne (by omega)]; exact hs.1.1.2.1,
        by rw [um_setN_ne (by omega)]; exact hs.1.1.2.2.1, hs.1.1.2.2.2⟩,
        by rw [um_setN_ne (by omega)]; exact hs.1.2⟩,
        by rw [um_setN_ne (by omega)]; exact hs.2.1, by rw [um_setN_ne (by omega)]; exact hs.2.2⟩
    · intro s v hs
      exact ⟨⟨⟨um_PC_setF hs.1.1.1 2 v (by omega), hs.1.1.2.1, hs.1.1.2.2.1, hs.1.1.2.2.2⟩,
        hs.1.2⟩, hs.2⟩
    · intro s v hs
      exact ⟨⟨⟨um_PC_setF hs.1.1.1 4 v (by omega), hs.1.1.2.1, hs.1.1.2.2.1, hs.1.1.2.2.2⟩,
        hs.1.2⟩, hs.2⟩
  have hleaf : um_Sp [N] xs B (um_cmpL 0 (um_g f ((List.range ts).map
      (fun j => D.getD (i * ts + j) 0)))) P Q (8 * b + 1) := by
    have := um_sp_cmpL (ns := [N]) (xs := xs) hR (i * b + k) (fun s hs => hs.2)
      (um_g f ((List.range ts).map (fun j => D.getD (i * ts + j) 0))) 0 Φ
      (by rw [um_g_length]; omega)
    rw [um_g_length] at this
    exact this
  have htree := um_sp_tree (ns := [N]) (xs := xs) al hal (fun pre => um_cmpL 0 (um_g f pre)) hP
    (fun s hs => hs.1.1.1.bd) ts base (fun j => D.getD (i * ts + j) 0)
    (fun s hs => ⟨hs.1.1.2.2.1, fun j hj => by
      have := hs.1.1.1.dat (i * ts + j) (by nlinarith)
      rw [show base + 2 * j = 2 * (8 + (i * ts + j)) by omega]; exact this⟩)
    (by omega) _ hleaf ts [] (by simp) (by simp)
  have := um_sp_seq h1 (um_sp_seq h2 htree)
  refine um_sp_conseq this (fun _ h => h) ?_ le_rfl
  intro s ⟨⟨⟨hs, h12, _, ho⟩, _⟩, h16, hiff⟩
  refine ⟨⟨hs, h12, ho⟩, h16, ?_⟩
  rw [hiff]
  simp

theorem um_sp_bloopM (al : List F) (hal : ∀ a : F, a ∈ al) {ts b : ℕ} (f : Vec F ts → Vec F b)
    {xs : List F} {B N m k L : ℕ} {D : List F}
    (hL : m * ts ≤ L) (hB : 2 * (8 + m * ts) + 2 * ts ≤ B) (hm : m + 1 ≤ B)
    (hB2 : m * b + k ≤ B) :
    um_Sp [N] xs B (.seq (.basic (.literal 16 1)) (.seq (.basic (.literal 12 0))
        (.seq (.loop 12 1 (um_bodyM al f)) um_final)))
      (fun s => um_PC B N m k D L s ∧ s.out = [])
      (fun s => um_PC B N m k D L s ∧
        ((∀ i < m, ∀ c < b, xs.getD (i * b + k + c) 0 = (um_bk f D i).getD c 0) → s.out = [1]) ∧
        (¬ (∀ i < m, ∀ c < b, xs.getD (i * b + k + c) 0 = (um_bk f D i).getD c 0) →
          s.out = [0]))
      (1 + (1 + ((m * (um_len (um_seqL (F := F) (um_pre13 ts)) +
        (um_len (um_seqL (F := F) (um_pre15 b)) + (ts * (3 * al.length + 4) + (8 * b + 1))) + 4)
          + 1) + (max 2 2 + 2)))) := by
  let Φ : ℕ → Prop := fun i => ∀ i' < i, ∀ c < b,
    xs.getD (i' * b + k + c) 0 = (um_bk f D i').getD c 0
  let I : ℕ → um_St F → Prop := fun i s =>
    (um_PC B N m k D L s ∧ s.nr 12 = i ∧ s.out = []) ∧ s.nr 16 ≤ 1 ∧ (s.nr 16 = 1 ↔ Φ i)
  have h0 : um_Sp [N] xs B (.basic (.literal 16 1))
      (fun s => um_PC B N m k D L s ∧ s.out = [])
      (fun s => um_PC B N m k D L s ∧ s.out = [] ∧ s.nr 16 = 1) 1 := by
    apply um_sp_basic rfl
    intro s ⟨hs, ho⟩
    exact ⟨hs.bd, um_PC_setN hs 16 1 (by omega) (by omega) (by omega) (by omega) (by omega),
      by simpa [um_eff, um_setN] using ho, by simp [um_eff, um_setN]⟩
  have h1 : um_Sp [N] xs B (.basic (.literal 12 0))
      (fun s => um_PC B N m k D L s ∧ s.out = [] ∧ s.nr 16 = 1) (I 0) 1 := by
    apply um_sp_basic rfl
    intro s ⟨hs, ho, h16⟩
    refine ⟨hs.bd, ⟨um_PC_setN hs 12 0 (by omega) (by omega) (by omega) (by omega) (Nat.zero_le _),
      by simp [um_eff, um_setN], by simpa [um_eff, um_setN] using ho⟩, ?_, ?_⟩
    · simp only [um_eff]; rw [um_setN_ne (by omega), h16]
    · simp only [um_eff]; rw [um_setN_ne (by omega), h16]
      simp [Φ]
  have h2 := um_sp_loop (ns := [N]) (xs := xs) (B := B) (i := 12) (n := 1) (body := um_bodyM al f)
    I 0 m (um_len (um_seqL (F := F) (um_pre13 ts)) +
        (um_len (um_seqL (F := F) (um_pre15 b)) + (ts * (3 * al.length + 4) + (8 * b + 1))))
    (Nat.zero_le _) (fun j s _ _ hs => ⟨hs.1.2.1, hs.1.1.n1, hs.1.1.bd⟩) ?_
  · have h3 : um_Sp [N] xs B um_final (I m)
        (fun s => um_PC B N m k D L s ∧ (Φ m → s.out = [1]) ∧ (¬ Φ m → s.out = [0]))
        (max 2 2 + 2) := by
      refine um_sp_ifN (fun s hs => hs.1.1.bd) ?_ ?_
      · apply um_sp_sym
        intro s ⟨⟨⟨hs, _, ho⟩, h16, hiff⟩, heq⟩
        refine ⟨hs.bd, ⟨⟨rfl, Nat.zero_le _⟩, ⟨rfl, Nat.zero_le _⟩⟩, ?_⟩
        simp only [um_sym, um_eff]
        have hP := um_PC_out (um_PC_setF hs 0 (1 : F) (by omega))
          ((um_setF s 0 (1 : F)).fr 0 :: (um_setF s 0 (1 : F)).out)
        have h16' : s.nr 16 = 1 := by rw [heq, hs.n4]
        refine ⟨⟨hP, fun _ => ?_, fun hn => absurd (hiff.mp h16') hn⟩, hP.bd⟩
        simp [um_setF, ho]
      · apply um_sp_sym
        intro s ⟨⟨⟨hs, _, ho⟩, h16, hiff⟩, hne⟩
        refine ⟨hs.bd, ⟨⟨rfl, Nat.zero_le _⟩, ⟨rfl, Nat.zero_le _⟩⟩, ?_⟩
        simp only [um_sym, um_eff]
        have hP := um_PC_out (um_PC_setF hs 0 (0 : F) (by omega))
          ((um_setF s 0 (0 : F)).fr 0 :: (um_setF s 0 (0 : F)).out)
        refine ⟨hP, fun hΦ => ?_, fun _ => ?_⟩
        · exfalso; apply hne; rw [hs.n4]; exact hiff.mpr hΦ
        · simp [um_setF, ho]
    have := um_sp_seq h0 (um_sp_seq h1 (um_sp_seq h2 h3))
    exact um_sp_conseq this (fun _ h => h) (fun _ h => h) (by simp)
  · intro i _ hi
    have hb := um_sp_bodyM (xs := xs) (B := B) (N := N) (m := m) (k := k) (L := L) (D := D) al hal f
      i (Φ i) (by nlinarith) (by nlinarith) (by nlinarith)
    refine um_sp_conseq hb (fun _ h => h) ?_ le_rfl
    intro s ⟨⟨hs, h12, ho⟩, h16, hiff⟩
    have hP2 := um_PC_inc hs 12 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    refine ⟨hs.bd, hP2.bd, ⟨hP2, by rw [um_inc_self 12 (by omega), h12], by simpa [um_inc] using ho⟩,
      by rw [um_inc_nr 12 16 (by omega) (by omega)]; exact h16, ?_⟩
    rw [um_inc_nr 12 16 (by omega) (by omega), hiff]
    constructor
    · rintro ⟨hΦ, hc⟩ i' hi' c hcb
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | h
      · exact hΦ i' h c hcb
      · subst h; exact hc c hcb
    · intro h
      exact ⟨fun i' hi' c hc => h i' (by omega) c hc, fun c hc => h i (by omega) c hc⟩

end SubspaceEvasion312.Explicit.Dev.Goal
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal
open SubspaceEvasion312.Explicit

variable {F : Type} [Field F]

/-! ## Data layout lemmas (adapted from `LTGMachine`) -/

theorem um_flatten_get {α : Type} (L : ℕ) :
    ∀ (l : List (List α)), (∀ x ∈ l, x.length = L) → ∀ p r, r < L →
      l.flatten[L * p + r]? = (l[p]?).bind (·[r]?) := by
  intro l
  induction l with
  | nil => intro _ p r _; simp
  | cons x l ih =>
    intro hl p r hr
    have hx : x.length = L := hl x (by simp)
    rcases p with _ | p
    · simp [List.getElem?_append_left (show r < x.length by omega)]
    · rw [List.flatten_cons, List.getElem?_append_right (by rw [hx]; nlinarith)]
      have : L * (p + 1) + r - x.length = L * p + r := by rw [hx]; ring_nf; omega
      rw [this, ih (fun y hy => hl y (by simp [hy])) p r hr]
      simp

theorem um_flatten_length {α : Type} (L : ℕ) :
    ∀ (l : List (List α)), (∀ x ∈ l, x.length = L) → l.flatten.length = L * l.length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
    intro hl
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [hl x (by simp), ih (fun y hy => hl y (by simp [hy]))]
    ring

theorem um_blockData_length {s m : ℕ} (y : Blocks F s m) : (blockData y).length = m * s := by
  unfold blockData
  rw [um_flatten_length s]
  · simp; ring
  · intro x hx
    simp only [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [vectorData]

theorem um_blockData_getD {s m : ℕ} (y : Blocks F s m) (i : Fin m) (a : Fin s) :
    (blockData y).getD (i * s + a) 0 = y i a := by
  unfold blockData
  rw [List.getD_eq_getElem?_getD, show (i : ℕ) * s + a = s * i + a by ring,
    um_flatten_get s _ _ i a a.2]
  · simp [vectorData]
  · intro x hx
    simp only [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [vectorData]

theorem um_vectorData_getD {n : ℕ} (v : Vec F n) (a : ℕ) :
    (vectorData v).getD a 0 = if h : a < n then v ⟨a, h⟩ else 0 := by
  unfold vectorData
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · simp [h]

theorem um_ofFn_flatten {X : Type} : ∀ (m : ℕ) (G : Fin m → List X) (G' : ℕ → List X),
    (∀ i : Fin m, G i = G' i) → (List.ofFn G).flatten = (List.range m).flatMap G' := by
  intro m
  induction m with
  | zero => intro G G' _; simp
  | succ m ih =>
    intro G G' h
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append, List.range_succ,
      List.flatMap_append, ih _ G' (fun i => h i.castSucc)]
    simp [h (Fin.last m)]

theorem um_ofFn_getD {X : Type} (l : List X) (x0 : X) {n : ℕ} (hn : l.length = n) :
    List.ofFn (fun i : Fin n => l.getD i x0) = l := by
  subst hn
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem _ _ h2]

/-! ## The block outputs are the local map of the regrouped code word -/

theorem um_bk_eq {s t b m : ℕ} (hs : 0 < s) (f : Vec F (t * s) → Vec F b)
    (y : Blocks F s (t * m)) (i : ℕ) (hi : i < m) :
    um_bk f (blockData y) i = vectorData (f (regroup y ⟨i, hi⟩)) := by
  unfold um_bk um_g
  congr 2
  funext j
  have hj := j.2
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_map, List.getElem_range]
  have hjs : j.1 / s < t := (Nat.div_lt_iff_lt_mul hs).2 (by simpa [Nat.mul_comm] using hj)
  have ha : t * i + j.1 / s < t * m := by nlinarith
  have := um_blockData_getD y ⟨t * i + j.1 / s, ha⟩ ⟨j.1 % s, Nat.mod_lt _ hs⟩
  simp only at this
  rw [show i * (t * s) + j.1 = (t * i + j.1 / s) * s + j.1 % s by
    have := Nat.div_add_mod j.1 s; nlinarith [this]]
  rw [this]
  rfl

theorem um_compose_eq {s : ℕ} (hs : 0 < s) (kf : ℕ → ℕ) (E : ∀ m, Vec F (kf m) →ₗ[F] Blocks F s m)
    (t b num den N : ℕ) (f : Vec F (t * s) → Vec F b) (x : Vec F (kN num den b N)) :
    blockData (compose (encN kf E t b num den N) f x) =
      (List.range (mN num den b N)).flatMap (um_bk f (blockData (E (t * mN num den b N)
        (padL F (kN num den b N) (kf (t * mN num den b N)) x)))) := by
  conv_lhs => unfold blockData compose
  apply um_ofFn_flatten
  intro i
  rw [um_bk_eq hs f _ i i.2]
  rfl

theorem um_point_data {s : ℕ} (hs : 0 < s) (kf : ℕ → ℕ)
    (E : ∀ m, Vec F (kf m) →ₗ[F] Blocks F s m)
    (t b num den N : ℕ) (f : Vec F (t * s) → Vec F b) (hbm : b * mN num den b N ≤ N)
    (x : Vec F (kN num den b N)) :
    vectorData ((asm kf E t b num den f N).point x) = vectorData x ++
      (List.range (mN num den b N)).flatMap (um_bk f (blockData (E (t * mN num den b N)
        (padL F (kN num den b N) (kf (t * mN num den b N)) x)))) := by
  rw [← um_compose_eq hs]
  show List.ofFn (fun i : Fin N => (vectorData x ++
    blockData (compose (encN kf E t b num den N) f x)).getD i 0) = _
  apply um_ofFn_getD
  rw [List.length_append, um_blockData_length]
  have hx : (vectorData x).length = N - b * mN num den b N := List.length_ofFn
  have : mN num den b N * b = b * mN num den b N := Nat.mul_comm _ _
  omega

theorem um_flatMap_getD {X : Type} (G : ℕ → List X) (L : ℕ) (hG : ∀ i, (G i).length = L)
    (m i c : ℕ) (hi : i < m) (hc : c < L) (x0 : X) :
    ((List.range m).flatMap G).getD (i * L + c) x0 = (G i).getD c x0 := by
  rw [List.flatMap_def, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    show i * L + c = L * i + c by ring, um_flatten_get L _ _ i c hc]
  · simp [hi]
  · intro x hx; simp only [List.mem_map] at hx; obtain ⟨a, _, rfl⟩ := hx; exact hG a

theorem um_flatMap_length {X : Type} (G : ℕ → List X) (L : ℕ) (hG : ∀ i, (G i).length = L)
    (m : ℕ) : ((List.range m).flatMap G).length = m * L := by
  rw [List.flatMap_def, um_flatten_length L]
  · simp; ring
  · intro x hx; simp only [List.mem_map] at hx; obtain ⟨a, _, rfl⟩ := hx; exact hG a

theorem um_mem_iff {s : ℕ} (hs : 0 < s) (kf : ℕ → ℕ)
    (E : ∀ m, Vec F (kf m) →ₗ[F] Blocks F s m)
    (t b num den N : ℕ) (f : Vec F (t * s) → Vec F b) (hbm : b * mN num den b N ≤ N)
    (y : Vec F N) :
    y ∈ (asm kf E t b num den f N).set ↔
      ∀ i < mN num den b N, ∀ c < b,
        (vectorData y).getD (i * b + kN num den b N + c) 0 =
          (um_bk f (blockData (E (t * mN num den b N)
            (padL F (kN num den b N) (kf (t * mN num den b N))
              (fun i => y ⟨i, by have := i.2; simp only [kN] at this; omega⟩)))) i).getD c 0 := by
  have hkN : kN num den b N + b * mN num den b N = N := by simp only [kN]; omega
  have hlen : ∀ (x : Vec F (kN num den b N)) i, (um_bk f (blockData (E (t * mN num den b N)
      (padL F (kN num den b N) (kf (t * mN num den b N)) x))) i).length = b :=
    fun x i => um_g_length f _
  have key : ∀ x : Vec F (kN num den b N),
      vectorData ((asm kf E t b num den f N).point x) = vectorData x ++
      (List.range (mN num den b N)).flatMap (um_bk f (blockData (E (t * mN num den b N)
        (padL F (kN num den b N) (kf (t * mN num den b N)) x)))) :=
    fun x => um_point_data hs kf E t b num den N f hbm x
  have hvl : ∀ x : Vec F (kN num den b N), (vectorData x).length = kN num den b N :=
    fun x => List.length_ofFn
  have hyl : (vectorData y).length = N := List.length_ofFn
  constructor
  · intro hy
    obtain ⟨x', hx'⟩ : ∃ x' : Vec F (kN num den b N), (asm kf E t b num den f N).point x' = y := hy
    have hxx : x' = (fun i : Fin (kN num den b N) =>
        y ⟨i, by have := i.2; simp only [kN] at this; omega⟩) := by
      funext i
      have h1 : (vectorData ((asm kf E t b num den f N).point x')).getD i.1 0 =
          (vectorData x' ++ (List.range (mN num den b N)).flatMap (um_bk f (blockData
            (E (t * mN num den b N) (padL F (kN num den b N) (kf (t * mN num den b N)) x'))))).getD
              i.1 0 := by rw [key x']
      have hi := i.2
      rw [List.getD_append _ _ _ _ (by rw [hvl]; exact hi), um_vectorData_getD x',
        dif_pos hi, um_vectorData_getD, dif_pos (by omega), hx'] at h1
      exact h1.symm
    subst hxx
    intro i hi c hc
    have e := key (fun i : Fin (kN num den b N) =>
        y ⟨i, by have := i.2; simp only [kN] at this; omega⟩)
    rw [hx'] at e
    rw [e, List.getD_append_right _ _ _ _ (by rw [hvl]; omega), hvl,
      show i * b + kN num den b N + c - kN num den b N = i * b + c by omega]
    exact um_flatMap_getD _ b (hlen _) _ i c hi hc 0
  · intro h
    refine ⟨fun i : Fin (kN num den b N) => y ⟨i, by have := i.2; simp only [kN] at this; omega⟩,
      ?_⟩
    apply List.ofFn_injective
    show vectorData _ = vectorData y
    rw [key]
    apply List.ext_getElem
    · rw [List.length_append, um_flatMap_length _ b (hlen _), hvl, hyl]
      have : mN num den b N * b = b * mN num den b N := Nat.mul_comm _ _
      omega
    intro p h1 h2
    have hpN : p < N := by rwa [hyl] at h2
    rw [← List.getD_eq_getElem _ (0 : F) h1, ← List.getD_eq_getElem _ (0 : F) h2]
    by_cases hpk : p < kN num den b N
    · rw [List.getD_append _ _ _ _ (by rw [hvl]; exact hpk), um_vectorData_getD,
        um_vectorData_getD, dif_pos hpk, dif_pos hpN]
    · rw [List.getD_append_right _ _ _ _ (by rw [hvl]; omega), hvl]
      have hb : 0 < b := by
        rcases Nat.eq_zero_or_pos b with hb | hb
        · exfalso
          have := h1
          rw [List.length_append, um_flatMap_length _ b (hlen _), hvl] at this
          subst hb; simp at this; omega
        · exact hb
      have hdiv := Nat.div_add_mod (p - kN num den b N) b
      have hi : (p - kN num den b N) / b < mN num den b N := by
        rw [Nat.div_lt_iff_lt_mul hb]
        have : mN num den b N * b = b * mN num den b N := Nat.mul_comm _ _
        omega
      have hc := Nat.mod_lt (p - kN num den b N) hb
      have := h ((p - kN num den b N) / b) hi ((p - kN num den b N) % b) hc
      have e1 : (p - kN num den b N) / b * b + kN num den b N + (p - kN num den b N) % b = p := by
        have : (p - kN num den b N) / b * b = b * ((p - kN num den b N) / b) := Nat.mul_comm _ _
        omega
      rw [e1] at this
      have e2 : p - kN num den b N = (p - kN num den b N) / b * b + (p - kN num den b N) % b := by
        have : (p - kN num den b N) / b * b = b * ((p - kN num den b N) / b) := Nat.mul_comm _ _
        omega
      rw [e2, um_flatMap_getD _ b (hlen _) _ _ _ hi hc 0]
      exact this.symm

end SubspaceEvasion312.Explicit.Dev.Goal
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal
open SubspaceEvasion312.Explicit

variable {F : Type} [Field F]

theorem um_programSize_halt (P : Program F) : programSize (P ++ [.halt]) = programSize P + 1 := by
  simp [programSize, instructionSize]

theorem um_rawOK_trL (enc : Program F) : ∀ p,
    programSize (um_trL p (p + 7 * enc.length) 0 enc) ≤ 8 * programSize enc :=
  fun p => um_trL_size p _ enc 0

theorem um_rawOK_seqL (R : ℕ) : ∀ l : List (Instruction F), um_rawOK R (um_seqL l)
  | [] => trivial
  | [_] => trivial
  | _ :: _ :: rest => ⟨trivial, um_rawOK_seqL R (_ :: rest)⟩

theorem um_rawOK_chain (R : ℕ) (K : F → um_Cmd F) (hK : ∀ a, um_rawOK R (K a)) :
    ∀ l : List F, um_rawOK R (um_chain l K)
  | [] => trivial
  | a :: rest => ⟨trivial, hK a, um_rawOK_chain R K hK rest⟩

theorem um_rawOK_tree (R : ℕ) (al : List F) (leaf : List F → um_Cmd F)
    (hl : ∀ pre, um_rawOK R (leaf pre)) : ∀ n pre, um_rawOK R (um_tree al leaf n pre)
  | 0, pre => hl pre
  | n + 1, pre => ⟨⟨trivial, trivial, trivial⟩,
      um_rawOK_chain R _ (fun a => um_rawOK_tree R al leaf hl n (pre ++ [a])) al⟩

theorem um_rawOK_outL (R : ℕ) : ∀ l : List F, um_rawOK R (um_outL l)
  | [] => trivial
  | _ :: rest => ⟨⟨trivial, trivial⟩, um_rawOK_outL R rest⟩

theorem um_rawOK_cmpL (R : ℕ) : ∀ (c : ℕ) (l : List F), um_rawOK R (um_cmpL c l)
  | _, [] => trivial
  | c, _ :: rest => ⟨⟨⟨trivial, trivial, trivial, trivial⟩, trivial, trivial⟩,
      um_rawOK_cmpL R (c + 1) rest⟩

theorem um_rawOK_index (al : List F) (enc : Program F) (num den t : ℕ) {ts b : ℕ}
    (f : Vec F ts → Vec F b) :
    um_rawOK (8 * programSize enc) (um_indexC al enc num den t f) :=
  ⟨um_rawOK_seqL _ _, um_rawOK_trL enc, ⟨trivial, ⟨trivial, trivial⟩⟩, trivial,
    um_rawOK_seqL _ _, um_rawOK_tree _ al _ (fun pre => um_rawOK_outL _ _) _ _⟩

theorem um_rawOK_member (al : List F) (enc : Program F) (num den t : ℕ) {ts b : ℕ}
    (f : Vec F ts → Vec F b) :
    um_rawOK (8 * programSize enc) (um_memberC al enc num den t f) :=
  ⟨um_rawOK_seqL _ _, um_rawOK_trL enc, trivial, trivial,
    ⟨um_rawOK_seqL _ _, um_rawOK_seqL _ _, um_rawOK_tree _ al _ (fun pre => um_rawOK_cmpL _ _ _) _ _⟩,
    ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

/-- The padded message read by the embedded encoder. -/
theorem um_pad_getD {k k' : ℕ} (hk : k ≤ k') (x : Vec F k) (xs : List F)
    (hxs : ∀ v, v < k → xs.getD v 0 = (vectorData x).getD v 0) (v : ℕ) :
    (vectorData (padL F k k' x)).getD v 0 = if v < k then xs.getD v 0 else 0 := by
  rw [um_vectorData_getD]
  split_ifs with h1 h2 h2
  · rw [hxs v h2, um_vectorData_getD, dif_pos h2]; simp [padL, h2]
  · simp [padL, h2]
  · omega
  · rfl

theorem um_img_PC {B N m k L M : ℕ} {D : List F} {S1 : um_St F} {zf : MachineState F}
    (hw : um_W0 S1 k M) (h0 : S1.nr 0 = N) (h1 : S1.nr 1 = m) (hbd : um_Bd B (um_img S1 zf))
    (hD : zf.out.reverse = D) (hL : zf.out.length = L) :
    um_PC B N m k D L (um_img S1 zf) := by
  refine ⟨hbd, ?_, ?_, ?_, ?_, ?_⟩
  · simp [um_img, um_imgN, h0]
  · simp [um_img, um_imgN, h1]
  · simp [um_img, um_imgN, hw.k]
  · simp [um_img, um_imgN, hw.one]
  · intro i hi
    simp only [um_img, um_imgF]
    rw [if_neg (by omega), if_pos (by omega), ← hD]
    congr 1; omega

def um_cbI (al : List F) (ts b : ℕ) : ℕ :=
  um_len (um_seqL (F := F) (um_pre13 ts)) + (ts * (3 * al.length + 4) + (2 * b + 1))

def um_cbM (al : List F) (ts b : ℕ) : ℕ :=
  um_len (um_seqL (F := F) (um_pre13 ts)) +
    (um_len (um_seqL (F := F) (um_pre15 b)) + (ts * (3 * al.length + 4) + (8 * b + 1)))

/-- Everything the two programs share up to the end of the embedded encoder run. -/
theorem um_front {s : ℕ} (hs : 0 < s)
    (kf : ℕ → ℕ) (E : ∀ m, Vec F (kf m) →ₗ[F] Blocks F s m)
    (enc : Program F) (Kf h m₀ : ℕ)
    (henc : ∀ m ≥ m₀, ∀ x, RunsWithin enc [m] (vectorData x) (Kf * (m+1)^h) (Kf * (m+1)^h)
      (blockData (E m x)))
    (t b num den : ℕ) (N : ℕ)
    (hm0 : m₀ ≤ t * mN num den b N) (hkf : kN num den b N ≤ kf (t * mN num den b N))
    (B : ℕ)
    (hB0 : N + num + num * N + den * b + b + b * mN num den b N + t + t * mN num den b N + 16 ≤ B)
    (hB1 : 2 * (Kf * (t * mN num den b N + 1) ^ h) + 1 ≤ B)
    (hB3 : 2 * (8 + t * mN num den b N * s) ≤ B) (hB5 : N + 1 ≤ B)
    (xs : List F) (x0 : Vec F (kN num den b N))
    (hxs : ∀ v, v < kN num den b N → xs.getD v 0 = (vectorData x0).getD v 0) :
    ∃ n1 n2 S1 S, n1 + n2 ≤ 14 + 5 * (Kf * (t * mN num den b N + 1) ^ h) ∧
      um_Exec [N] xs B (um_seqL (um_setupL num den b t)) um_s0 n1 S1 ∧
      um_Exec [N] xs B (um_encC enc) S1 n2 S ∧
      um_PC B N (mN num den b N) (kN num den b N)
        (blockData (E (t * mN num den b N) (padL F (kN num den b N) (kf (t * mN num den b N)) x0)))
        (t * mN num den b N * s) S ∧ S.out = [] := by
  obtain ⟨n1, S1, hn1, e1, hw, hi, h0, h1, ho1, -, hbd1⟩ :=
    um_setup_spec (xs := xs) (B := B) N num den b t hB0 um_s0 rfl
  obtain ⟨te, zf, hsz, hrun, hout, -⟩ := henc (t * mN num den b N) hm0
    (padL F (kN num den b N) (kf (t * mN num den b N)) x0)
  have hzlen : zf.out.length = t * mN num den b N * s := by
    have := congrArg List.length hout
    rw [List.length_reverse, um_blockData_length] at this; exact this
  obtain ⟨n2, hn2, e2, hb2⟩ := um_exec_enc (ns := [N]) (xs := xs) (B := B) hw hbd1 hi
    (um_pad_getD hkf x0 xs hxs) (by omega) hB1 (le_trans (Nat.sub_le _ _) (by omega)) hrun
    (by rw [hzlen]; exact hB3)
  refine ⟨n1, n2, _, _, ?_, e1, e2, um_img_PC hw h0 h1 hb2 hout hzlen, ?_⟩
  · have : te ≤ Kf * (t * mN num den b N + 1) ^ h := by omega
    omega
  · simp [um_img, ho1]

theorem um_index_ok (al : List F) (hal : ∀ a : F, a ∈ al) {s : ℕ} (hs : 0 < s)
    (kf : ℕ → ℕ) (E : ∀ m, Vec F (kf m) →ₗ[F] Blocks F s m)
    (enc : Program F) (Kf h m₀ : ℕ)
    (henc : ∀ m ≥ m₀, ∀ x, RunsWithin enc [m] (vectorData x) (Kf * (m+1)^h) (Kf * (m+1)^h)
      (blockData (E m x)))
    (t b num den : ℕ) (f : Vec F (t * s) → Vec F b) (N : ℕ)
    (hm0 : m₀ ≤ t * mN num den b N) (hbm : b * mN num den b N ≤ N)
    (hkf : kN num den b N ≤ kf (t * mN num den b N)) (B T : ℕ)
    (hB0 : N + num + num * N + den * b + b + b * mN num den b N + t + t * mN num den b N + 16 ≤ B)
    (hB1 : 2 * (Kf * (t * mN num den b N + 1) ^ h) + 1 ≤ B)
    (hB3 : 2 * (8 + t * mN num den b N * s) ≤ B)
    (hB4 : 2 * (8 + mN num den b N * (t * s)) + 2 * (t * s) ≤ B) (hB5 : N + 1 ≤ B)
    (hT : um_szB (8 * programSize enc) (um_indexC al enc num den t f) + 1 +
      (14 + 5 * (Kf * (t * mN num den b N + 1) ^ h) + (1 + (N * (2 + 4) + 1)) +
        (1 + (N * (um_cbI al (t * s) b + 4) + 1)) + 1) ≤ T)
    (x : Vec F (kN num den b N)) :
    RunsWithin (um_comp (um_indexC al enc num den t f) 0 ++ [.halt]) [N] (vectorData x) T B
      (vectorData ((asm kf E t b num den f N).point x)) := by
  have hkN : kN num den b N ≤ N := by simp only [kN]; omega
  have hmN : mN num den b N ≤ N := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; simp [mN]
    · nlinarith
  obtain ⟨n1, n2, S1, S2, hn12, e1, e2, hP2, ho2⟩ := um_front hs kf E enc Kf h m₀ henc t b num den N hm0 hkf
    B hB0 hB1 hB3 hB5 (vectorData x) x (fun _ _ => rfl)
  obtain ⟨n3, S3, hn3, e3, hP3, ho3⟩ := um_sp_xloop (N := N) (vectorData x)
    (by simp [vectorData]) (by omega) S2 ⟨hP2, ho2⟩
  obtain ⟨n4, S4, hn4, e4, hP4, ho4⟩ := um_sp_bloopI al hal f (xs := vectorData x) (vectorData x)
    (le_of_eq (by ring))
    hB4 (by omega) S3 ⟨hP3, ho3⟩
  have e : um_Exec [N] (vectorData x) B (um_indexC al enc num den t f) um_s0
      (n1 + (n2 + (n3 + n4))) S4 :=
    um_Exec.seq e1 (um_Exec.seq e2 (um_Exec.seq e3 e4))
  have hrun := um_run e hP4.bd
  refine ⟨(n1 + (n2 + (n3 + n4))) + 1, _, ?_, hrun, ?_, rfl⟩
  · rw [um_programSize_halt]
    have hsz := um_size_le_szB _ _ (um_rawOK_index al enc num den t f) 0
    have h3 : n3 ≤ 1 + (N * (2 + 4) + 1) := by
      have := Nat.mul_le_mul_right (2 + 4) hkN; omega
    have h4 : n4 ≤ 1 + (N * (um_cbI al (t * s) b + 4) + 1) := by
      have := Nat.mul_le_mul_right (um_cbI al (t * s) b + 4) hmN
      unfold um_cbI; unfold um_cbI at this; omega
    omega
  · simp only [um_mk]
    rw [ho4, List.reverse_reverse, um_point_data hs kf E t b num den N f hbm x]

theorem um_member_ok (al : List F) (hal : ∀ a : F, a ∈ al) {s : ℕ} (hs : 0 < s)
    (kf : ℕ → ℕ) (E : ∀ m, Vec F (kf m) →ₗ[F] Blocks F s m)
    (enc : Program F) (Kf h m₀ : ℕ)
    (henc : ∀ m ≥ m₀, ∀ x, RunsWithin enc [m] (vectorData x) (Kf * (m+1)^h) (Kf * (m+1)^h)
      (blockData (E m x)))
    (t b num den : ℕ) (f : Vec F (t * s) → Vec F b) (N : ℕ)
    (hm0 : m₀ ≤ t * mN num den b N) (hbm : b * mN num den b N ≤ N)
    (hkf : kN num den b N ≤ kf (t * mN num den b N)) (B T : ℕ)
    (hB0 : N + num + num * N + den * b + b + b * mN num den b N + t + t * mN num den b N + 16 ≤ B)
    (hB1 : 2 * (Kf * (t * mN num den b N + 1) ^ h) + 1 ≤ B)
    (hB3 : 2 * (8 + t * mN num den b N * s) ≤ B)
    (hB4 : 2 * (8 + mN num den b N * (t * s)) + 2 * (t * s) ≤ B) (hB5 : N + 1 ≤ B)
    (hT : um_szB (8 * programSize enc) (um_memberC al enc num den t f) + 1 +
      (14 + 5 * (Kf * (t * mN num den b N + 1) ^ h) +
        (1 + (1 + ((N * (um_cbM al (t * s) b + 4) + 1) + (max 2 2 + 2)))) + 1) ≤ T)
    (y : Vec F N) :
    RunsWithin (um_comp (um_memberC al enc num den t f) 0 ++ [.halt]) [N] (vectorData y) T B
      [by classical exact if y ∈ (asm kf E t b num den f N).set then 1 else 0] := by
  classical
  have hkN : kN num den b N ≤ N := by simp only [kN]; omega
  have hmN : mN num den b N ≤ N := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; simp [mN]
    · nlinarith
  let x0 : Vec F (kN num den b N) := fun i => y ⟨i, by have := i.2; simp only [kN] at this; omega⟩
  have hxs : ∀ v, v < kN num den b N → (vectorData y).getD v 0 = (vectorData x0).getD v 0 := by
    intro v hv
    rw [um_vectorData_getD, um_vectorData_getD, dif_pos hv, dif_pos (by omega)]
  obtain ⟨n1, n2, S1, S2, hn12, e1, e2, hP2, ho2⟩ := um_front hs kf E enc Kf h m₀ henc t b num den
    N hm0 hkf B hB0 hB1 hB3 hB5 (vectorData y) x0 hxs
  obtain ⟨n5, S5, hn5, e5, hP5, h1, h0⟩ := um_sp_bloopM al hal f (xs := vectorData y)
    (le_of_eq (by ring)) hB4 (by omega) (by nlinarith) S2 ⟨hP2, ho2⟩
  have e : um_Exec [N] (vectorData y) B (um_memberC al enc num den t f) um_s0
      (n1 + (n2 + n5)) S5 :=
    um_Exec.seq e1 (um_Exec.seq e2 e5)
  have hrun := um_run e hP5.bd
  refine ⟨(n1 + (n2 + n5)) + 1, _, ?_, hrun, ?_, rfl⟩
  · rw [um_programSize_halt]
    have hsz := um_size_le_szB _ _ (um_rawOK_member al enc num den t f) 0
    have h5 : n5 ≤ 1 + (1 + ((N * (um_cbM al (t * s) b + 4) + 1) + (max 2 2 + 2))) := by
      have := Nat.mul_le_mul_right (um_cbM al (t * s) b + 4) hmN
      unfold um_cbM; unfold um_cbM at this; omega
    omega
  · simp only [um_mk]
    have hiff := um_mem_iff hs kf E t b num den N f hbm y
    by_cases hΦ : y ∈ (asm kf E t b num den f N).set
    · rw [if_pos hΦ, h1 (hiff.mp hΦ)]; rfl
    · rw [if_neg hΦ, h0 (fun h => hΦ (hiff.mpr h))]; rfl

end SubspaceEvasion312.Explicit.Dev.Goal
end
end

section
set_option autoImplicit false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal

/-- The arithmetic behind the time and register bounds. -/
theorem um_bounds (N m t s b num den Kf h SzI SzM cI cM : ℕ) (ht : 0 < t) (hmN : m ≤ N)
    (hbm : b * m ≤ N) :
    let C := SzI + SzM + 7 * cI + 7 * cM + 20 * (Kf * t ^ h) +
      20 * (num + den * b + b + t + t * s) + 100
    N + num + num * N + den * b + b + b * m + t + t * m + 16 ≤ C * (N + 1) ^ (h + 2) ∧
    2 * (Kf * (t * m + 1) ^ h) + 1 ≤ C * (N + 1) ^ (h + 2) ∧
    2 * (8 + t * m * s) ≤ C * (N + 1) ^ (h + 2) ∧
    2 * (8 + m * (t * s)) + 2 * (t * s) ≤ C * (N + 1) ^ (h + 2) ∧
    N + 1 ≤ C * (N + 1) ^ (h + 2) ∧
    SzI + 1 + (14 + 5 * (Kf * (t * m + 1) ^ h) + (1 + (N * (2 + 4) + 1)) +
      (1 + (N * (cI + 4) + 1)) + 1) ≤ C * (N + 1) ^ (h + 2) ∧
    SzM + 1 + (14 + 5 * (Kf * (t * m + 1) ^ h) +
      (1 + (1 + ((N * (cM + 4) + 1) + (max 2 2 + 2)))) + 1) ≤ C * (N + 1) ^ (h + 2) := by
  intro C
  set V := N + 1 with hV
  set X := V ^ (h + 2) with hX
  have hV1 : 1 ≤ V := by omega
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hVX : V ≤ X := by
    calc V = V ^ 1 := (pow_one V).symm
      _ ≤ X := Nat.pow_le_pow_right hV1 (by omega)
  have hVhX : V ^ h ≤ X := Nat.pow_le_pow_right hV1 (by omega)
  have hpow : Kf * (t * m + 1) ^ h ≤ (Kf * t ^ h) * X := by
    have h1 : t * m + 1 ≤ t * V := by rw [hV]; nlinarith
    calc Kf * (t * m + 1) ^ h ≤ Kf * (t * V) ^ h :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 h)
      _ = (Kf * t ^ h) * V ^ h := by rw [mul_pow]; ring
      _ ≤ (Kf * t ^ h) * X := Nat.mul_le_mul_left _ hVhX
  have hNX : N ≤ X := by omega
  have hCX : C * X = SzI * X + SzM * X + 7 * (cI * X) + 7 * (cM * X) + 20 * ((Kf * t ^ h) * X) +
      20 * (num * X + den * b * X + b * X + t * X + t * s * X) + 100 * X := by
    simp only [C]; ring
  have a1 : num * N ≤ num * X := Nat.mul_le_mul_left _ hNX
  have a2 : num ≤ num * X := Nat.le_mul_of_pos_right _ hX1
  have a3 : den * b ≤ den * b * X := Nat.le_mul_of_pos_right _ hX1
  have a4 : b ≤ b * X := Nat.le_mul_of_pos_right _ hX1
  have a5 : t ≤ t * X := Nat.le_mul_of_pos_right _ hX1
  have a6 : t * m ≤ t * X := Nat.mul_le_mul_left _ (by omega)
  have a7 : t * m * s ≤ t * s * X := by
    have : m * (t * s) ≤ X * (t * s) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have a8 : t * s ≤ t * s * X := Nat.le_mul_of_pos_right _ hX1
  have a9 : SzI ≤ SzI * X := Nat.le_mul_of_pos_right _ hX1
  have a10 : SzM ≤ SzM * X := Nat.le_mul_of_pos_right _ hX1
  have a11 : N * (cI + 4) ≤ cI * X + 4 * X := by
    have := Nat.mul_le_mul_right (cI + 4) hNX; nlinarith
  have a12 : N * (cM + 4) ≤ cM * X + 4 * X := by
    have := Nat.mul_le_mul_right (cM + 4) hNX; nlinarith
  have a13 : m * (t * s) = t * m * s := by ring
  rw [hCX]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  simp only [Nat.max_self]; omega

end SubspaceEvasion312.Explicit.Dev.Goal
end
end

section
set_option autoImplicit false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal
open SubspaceEvasion312.Explicit

/-- Uniform-in-`N` index and membership programs for the assembly `asm`, from an encoder
program of the code family (run at `t*m(N)`) and any local map on a finite field. -/
theorem uniform_machine (F : Type) [Field F] [Fintype F] {s : ℕ} (hs : 0 < s)
    (kf : ℕ → ℕ) (E : ∀ m, Vec F (kf m) →ₗ[F] Blocks F s m)
    (enc : Program F) (Kf h m₀ : ℕ)
    (henc : ∀ m ≥ m₀, ∀ x, RunsWithin enc [m] (vectorData x) (Kf * (m+1)^h) (Kf * (m+1)^h)
      (blockData (E m x)))
    (t b num den : ℕ) (ht : 0 < t) (hb : 0 < b) (hden : 0 < den)
    (f : Vec F (t * s) → Vec F b) (N₀ : ℕ)
    (hN : ∀ N ≥ N₀, m₀ ≤ t * mN num den b N ∧ 0 < mN num den b N ∧
      b * mN num den b N ≤ N ∧ kN num den b N ≤ kf (t * mN num den b N)) :
    ∃ (index member : Program F) (C : ℕ), 0 < C ∧
      GlobalAlgorithms (asm kf E t b num den f) index member C (h + 2) N₀ := by
  classical
  let al : List F := (Finset.univ : Finset F).toList
  have hal : ∀ a : F, a ∈ al := fun a => by simp [al]
  refine ⟨um_comp (um_indexC al enc num den t f) 0 ++ [.halt],
    um_comp (um_memberC al enc num den t f) 0 ++ [.halt],
    um_szB (8 * programSize enc) (um_indexC al enc num den t f) +
      um_szB (8 * programSize enc) (um_memberC al enc num den t f) +
      7 * um_cbI al (t * s) b + 7 * um_cbM al (t * s) b + 20 * (Kf * t ^ h) +
      20 * (num + den * b + b + t + t * s) + 100, by omega, ?_⟩
  intro N hN0
  obtain ⟨hm0, _, hbm, hkf⟩ := hN N hN0
  have hmN : mN num den b N ≤ N := by nlinarith
  obtain ⟨hB0, hB1, hB3, hB4, hB5, hTI, hTM⟩ := um_bounds N (mN num den b N) t s b num den Kf h
    (um_szB (8 * programSize enc) (um_indexC al enc num den t f))
    (um_szB (8 * programSize enc) (um_memberC al enc num den t f))
    (um_cbI al (t * s) b) (um_cbM al (t * s) b) ht hmN hbm
  exact ⟨fun x => um_index_ok al hal hs kf E enc Kf h m₀ henc t b num den f N hm0 hbm hkf _ _
      hB0 hB1 hB3 hB4 hB5 hTI x,
    fun y => um_member_ok al hal hs kf E enc Kf h m₀ henc t b num den f N hm0 hbm hkf _ _
      hB0 hB1 hB3 hB4 hB5 hTM y⟩

end SubspaceEvasion312.Explicit.Dev.Goal
end
end

section
set_option autoImplicit false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal
open SubspaceEvasion312.Explicit
open scoped ENNReal

/-! ## Part 1: ceiling estimates and parameter choice (real arithmetic) -/

theorem g_ceil (r : ℕ) (ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hε1 : ε < 1)
    (hx : 2 ≤ (r : ℝ) / ε) :
    (intersectionBound r ε : ℝ) ≤ 1028 * asymptoticShape r ε ∧
    (intersectionBound (r+1) ε : ℝ) ≤ 4112 * asymptoticShape r ε := by
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxpos : 0 < (r:ℝ) / ε := by positivity
  have hL1 : 1 ≤ log₂ ((r:ℝ) / ε) := by
    unfold log₂; rw [le_div_iff₀ hl2, one_mul]
    exact Real.log_le_log (by norm_num) hx
  have hrx : (r:ℝ)^2/ε = r * ((r:ℝ)/ε) := by ring
  have hrx2 : 2 ≤ (r:ℝ)^2/ε := by rw [hrx]; nlinarith
  have hrL2 : 2 ≤ (r:ℝ) * log₂ ((r:ℝ)/ε) / ε := by
    have : (r:ℝ) * log₂ ((r:ℝ)/ε) / ε = ((r:ℝ)/ε) * log₂ ((r:ℝ)/ε) := by ring
    rw [this]; nlinarith
  -- (r+1)/ε ≤ 2 r/ε gives log₂ ((r+1)/ε) ≤ 1 + log₂ (r/ε)
  have hM : log₂ (((r:ℝ)+1)/ε) ≤ 1 + log₂ ((r:ℝ)/ε) := by
    unfold log₂
    have : Real.log (((r:ℝ)+1)/ε) ≤ Real.log 2 + Real.log ((r:ℝ)/ε) := by
      rw [← Real.log_mul (by norm_num) hxpos.ne']
      apply Real.log_le_log (by positivity)
      rw [show (2:ℝ) * ((r:ℝ)/ε) = (2*r)/ε by ring]
      exact div_le_div_of_nonneg_right (by linarith) hε.le
    rw [div_le_iff₀ hl2]
    rw [add_mul, one_mul, div_mul_cancel₀ _ hl2.ne']
    linarith
  have hM0 : 0 ≤ log₂ (((r:ℝ)+1)/ε) := by
    unfold log₂
    apply div_nonneg _ hl2.le
    apply Real.log_nonneg
    rw [le_div_iff₀ hε]; linarith
  have h1 : 2 * (quadraticList r ε : ℝ) ≤ 1028 * ((r:ℝ)^2/ε) := by
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 16 * (r:ℝ)^2/ε by positivity)
    unfold quadraticList
    have e : 16 * (r:ℝ)^2/ε = 16 * ((r:ℝ)^2/ε) := by ring
    rw [e] at this ⊢
    linarith
  have h2 : 2 * (logarithmicList r ε : ℝ) ≤ 1028 * ((r:ℝ) * log₂ ((r:ℝ)/ε) / ε) := by
    have := Nat.ceil_lt_add_one
      (show (0:ℝ) ≤ 256 * (r:ℝ) * (1 + log₂ ((r:ℝ)/ε)) / ε by
        apply div_nonneg _ hε.le; apply mul_nonneg (by positivity); linarith)
    unfold logarithmicList
    have e : 256 * (r:ℝ) * (1 + log₂ ((r:ℝ)/ε)) / ε =
        256 * ((r:ℝ)/ε) + 256 * ((r:ℝ) * log₂ ((r:ℝ)/ε) / ε) := by ring
    have e2 : (r:ℝ) / ε ≤ (r:ℝ) * log₂ ((r:ℝ)/ε) / ε := by
      have : (r:ℝ) * log₂ ((r:ℝ)/ε) / ε = ((r:ℝ)/ε) * log₂ ((r:ℝ)/ε) := by ring
      rw [this]; nlinarith
    rw [e] at this ⊢
    linarith
  have h3 : 2 * (quadraticList (r+1) ε : ℝ) ≤ 4112 * ((r:ℝ)^2/ε) := by
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 16 * ((r+1:ℕ):ℝ)^2/ε by positivity)
    unfold quadraticList
    have e : 16 * ((r+1:ℕ):ℝ)^2/ε ≤ 64 * ((r:ℝ)^2/ε) := by
      push_cast
      rw [show 64 * ((r:ℝ)^2/ε) = (64 * (r:ℝ)^2)/ε by ring]
      apply div_le_div_of_nonneg_right _ hε.le
      nlinarith
    linarith
  have h4 : 2 * (logarithmicList (r+1) ε : ℝ) ≤ 4112 * ((r:ℝ) * log₂ ((r:ℝ)/ε) / ε) := by
    have := Nat.ceil_lt_add_one
      (show (0:ℝ) ≤ 256 * ((r+1:ℕ):ℝ) * (1 + log₂ (((r+1:ℕ):ℝ)/ε)) / ε by
        push_cast
        apply div_nonneg _ hε.le; apply mul_nonneg (by positivity); linarith)
    unfold logarithmicList
    have e : 256 * ((r+1:ℕ):ℝ) * (1 + log₂ (((r+1:ℕ):ℝ)/ε)) / ε ≤
        1536 * ((r:ℝ) * log₂ ((r:ℝ)/ε) / ε) := by
      push_cast
      rw [show 1536 * ((r:ℝ) * log₂ ((r:ℝ)/ε) / ε) = (1536 * ((r:ℝ) * log₂ ((r:ℝ)/ε)))/ε by
        ring]
      apply div_le_div_of_nonneg_right _ hε.le
      have hA : ((r:ℝ)+1) * (1 + log₂ (((r:ℝ)+1)/ε)) ≤ (2*r) * (2 + log₂ ((r:ℝ)/ε)) := by
        apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      nlinarith
    linarith
  unfold intersectionBound asymptoticShape
  push_cast
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1028),
    mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4112)]
  exact ⟨min_le_min h1 h2, min_le_min h3 h4⟩

/-- Choice of the regrouping factor `t` and the local output length `b`. -/
theorem g_params (s₀ r d : ℕ) (hs₀ : 0 < s₀) (R η : ℝ) (hR : 0 < R) (hη0 : 0 < η)
    (hη1 : η < 1) (h : (r:ℝ) < η * R * ((d:ℝ) - r)) :
    ∃ t b : ℕ, 0 < t ∧ 0 < b ∧ (t * s₀ + b + d) * r < b * d ∧
      (b:ℝ) * (1 - η) < η * R * ((t * s₀ : ℕ) : ℝ) := by
  have hηR : 0 < η * R := mul_pos hη0 hR
  have hg : 0 < (d:ℝ) - r := by
    by_contra hc; replace hc := not_lt.mp hc
    have : η * R * ((d:ℝ) - r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hηR.le hc
    have : (0:ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  set a : ℝ := (r:ℝ) / ((d:ℝ) - r) with ha_def
  have ha : a < η * R := by rw [ha_def, div_lt_iff₀ hg]; linarith
  have ha0 : 0 ≤ a := by positivity
  have hag : a * ((d:ℝ) - r) = r := by rw [ha_def]; field_simp
  have hs₀' : (0:ℝ) < s₀ := by exact_mod_cast hs₀
  set t : ℕ := ⌈(a * d + 1) / ((η * R - a) * s₀)⌉₊ + 1 with ht_def
  have ht1 : (a * d + 1) / ((η * R - a) * s₀) ≤ (t:ℝ) := by
    rw [ht_def]; push_cast
    have := Nat.le_ceil ((a * d + 1) / ((η * R - a) * s₀)); linarith
  have hpos : 0 < (η * R - a) * s₀ := mul_pos (by linarith) hs₀'
  have hkey : a * d + 1 ≤ (η * R - a) * ((t * s₀ : ℕ) : ℝ) := by
    rw [div_le_iff₀ hpos] at ht1; push_cast; linarith
  set S : ℕ := t * s₀ with hS_def
  set b : ℕ := ⌊a * ((S:ℝ) + d)⌋₊ + 1 with hb_def
  have hb_gt : a * ((S:ℝ) + d) < b := by
    rw [hb_def]; push_cast; exact Nat.lt_floor_add_one _
  have hb_le : (b:ℝ) ≤ a * ((S:ℝ) + d) + 1 := by
    rw [hb_def]; push_cast
    have := Nat.floor_le (show 0 ≤ a * ((S:ℝ) + d) by positivity); linarith
  refine ⟨t, b, by omega, by omega, ?_, ?_⟩
  · have hreal : ((S:ℝ) + b + d) * r < b * d := by
      have : a * ((S:ℝ) + d) * ((d:ℝ) - r) < b * ((d:ℝ) - r) := mul_lt_mul_of_pos_right hb_gt hg
      rw [mul_assoc, mul_comm ((S:ℝ) + d), ← mul_assoc, hag] at this
      nlinarith
    exact_mod_cast hreal
  · have hbpos : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    have : (b:ℝ) ≤ η * R * (S:ℝ) := by nlinarith
    nlinarith

/-- For `N` large, `m = ⌊ηN/b⌋` exceeds `m₀`, `bm ≤ N`, and `(b + RS) m ≥ N`. -/
theorem g_rate (b S m₀ : ℕ) (hb : 0 < b) (R η : ℝ) (hR : 0 < R) (hη0 : 0 < η)
    (hη1 : η < 1) (hbr : (b:ℝ) * (1 - η) < η * R * S) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, m₀ < ⌊η * N / b⌋₊ ∧ b * ⌊η * N / b⌋₊ ≤ N ∧
      (N:ℝ) ≤ (b + R * S) * ⌊η * N / b⌋₊ := by
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have hS0 : (0:ℝ) ≤ S := Nat.cast_nonneg S
  set δ : ℝ := (η * R * S - (1 - η) * b) / b with hδ
  have hδpos : 0 < δ := by rw [hδ]; apply div_pos _ hb'; linarith
  set B : ℝ := b + R * S with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  refine ⟨⌈B / δ⌉₊ + ⌈B * (m₀ + 1)⌉₊ + 1, by omega, ?_⟩
  intro N hN
  have hN' : (⌈B / δ⌉₊ : ℝ) + ⌈B * (m₀ + 1)⌉₊ + 1 ≤ N := by exact_mod_cast hN
  have hN1 : B / δ ≤ N := by
    have := Nat.le_ceil (B / δ)
    have : (0:ℝ) ≤ ⌈B * (m₀ + 1)⌉₊ := Nat.cast_nonneg _
    linarith
  have hN2 : B * (m₀ + 1) < N := by
    have := Nat.le_ceil (B * (m₀ + 1))
    have : (0:ℝ) ≤ ⌈B / δ⌉₊ := Nat.cast_nonneg _
    linarith
  have hNδ : B ≤ N * δ := by rwa [div_le_iff₀ hδpos] at hN1
  set m := ⌊η * N / b⌋₊ with hm
  have hm1 : η * N / b < m + 1 := Nat.lt_floor_add_one _
  have hm2 : (m:ℝ) ≤ η * N / b := Nat.floor_le (by positivity)
  have e : B * (η * N / b) = N + N * δ := by
    rw [hB, hδ]; field_simp; ring
  have hBm : (N:ℝ) ≤ B * m := by
    have : B * (η * N / b - 1) < B * m := mul_lt_mul_of_pos_left (by linarith) hBpos
    rw [mul_sub, e] at this
    linarith
  refine ⟨?_, ?_, hBm⟩
  · have : B * (m₀ + 1) < B * m := by linarith
    have := lt_of_mul_lt_mul_left this hBpos.le
    have : (m₀:ℝ) < m := by linarith
    exact_mod_cast this
  · have : (b:ℝ) * m ≤ N := by
      calc (b:ℝ) * m ≤ b * (η * N / b) := mul_le_mul_of_nonneg_left hm2 hb'.le
        _ = η * N := by field_simp
        _ ≤ N := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
    exact_mod_cast this

/-- `mN` is the real floor `⌊ηN/b⌋`. -/
theorem g_mN (num den b N : ℕ) (q : ℚ) (hq : (q:ℝ) = (num:ℝ) / den) (hden : 0 < den)
    (hb : 0 < b) : mN num den b N = ⌊(q:ℝ) * N / b⌋₊ := by
  unfold mN
  rw [← Nat.floor_div_eq_div (K := ℝ)]
  congr 1
  rw [hq]; push_cast
  have : (0:ℝ) < den := by exact_mod_cast hden
  have : (0:ℝ) < b := by exact_mod_cast hb
  field_simp

end SubspaceEvasion312.Explicit.Dev.Goal
end
end

section
set_option autoImplicit false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal
open SubspaceEvasion312.Explicit
open scoped ENNReal

/-! ## Part 2: linear algebra of the assembly -/

section lists
variable {F : Type} [Field F]

theorem g_flatten_get {α : Type} (L : ℕ) :
    ∀ (l : List (List α)), (∀ x ∈ l, x.length = L) → ∀ p r, r < L →
      l.flatten[L * p + r]? = (l[p]?).bind (·[r]?) := by
  intro l
  induction l with
  | nil => intro _ p r _; simp
  | cons x l ih =>
    intro hl p r hr
    have hx : x.length = L := hl x (by simp)
    rcases p with _ | p
    · simp [List.getElem?_append_left (show r < x.length by omega)]
    · rw [List.flatten_cons, List.getElem?_append_right (by rw [hx]; nlinarith)]
      have : L * (p + 1) + r - x.length = L * p + r := by rw [hx]; ring_nf; omega
      rw [this, ih (fun y hy => hl y (by simp [hy])) p r hr]
      simp

theorem g_flatten_length {α : Type} (L : ℕ) :
    ∀ (l : List (List α)), (∀ x ∈ l, x.length = L) → l.flatten.length = L * l.length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
    intro hl
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [hl x (by simp), ih (fun y hy => hl y (by simp [hy]))]
    ring

theorem g_blockData_length {s m : ℕ} (y : Blocks F s m) : (blockData y).length = m * s := by
  unfold blockData
  rw [g_flatten_length s]
  · simp; ring
  · intro x hx
    simp only [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [vectorData]

theorem g_blockData_getD' {s m : ℕ} (y : Blocks F s m) (i : Fin m) (a : Fin s) :
    (blockData y).getD (i * s + a) 0 = y i a := by
  unfold blockData
  rw [List.getD_eq_getElem?_getD, show (i : ℕ) * s + a = s * i + a by ring,
    g_flatten_get s _ _ i a a.2]
  · simp [vectorData]
  · intro x hx
    simp only [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [vectorData]

theorem g_div_lt {j m b : ℕ} (h : j < m * b) : j / b < m := by
  have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
  exact (Nat.div_lt_iff_lt_mul hb).2 h

theorem g_mod_lt {j m b : ℕ} (h : j < m * b) : j % b < b := by
  have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
  exact Nat.mod_lt _ hb

theorem g_blockData_getD {b m : ℕ} (y : Blocks F b m) (j : ℕ) (h : j < m * b) :
    (blockData y).getD j 0 = y ⟨j / b, g_div_lt h⟩ ⟨j % b, g_mod_lt h⟩ := by
  have := g_blockData_getD' y ⟨j / b, g_div_lt h⟩ ⟨j % b, g_mod_lt h⟩
  simp only at this
  rwa [Nat.div_add_mod'] at this

/-- The coordinate map `(x, y) ↦ x ++ flatten y`, as a linear map. -/
def g_Φ (F : Type) [Field F] (k b m N : ℕ) : (Vec F k × Blocks F b m) →ₗ[F] Vec F N where
  toFun p i := if h : i.1 < k then p.1 ⟨i.1, h⟩ else
    if h2 : i.1 - k < m * b then p.2 ⟨(i.1 - k) / b, g_div_lt h2⟩ ⟨(i.1 - k) % b, g_mod_lt h2⟩
    else 0
  map_add' p p' := by
    funext i; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c p := by
    funext i; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

theorem g_Φ_apply {k b m N : ℕ} (x : Vec F k) (y : Blocks F b m) (i : Fin N) :
    (vectorData x ++ blockData y).getD i 0 = g_Φ F k b m N (x, y) i := by
  have hvl : (vectorData x).length = k := by simp [vectorData]
  simp only [g_Φ, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases h : i.1 < k
  · rw [List.getD_append _ _ _ _ (by rw [hvl]; exact h), dif_pos h]
    unfold vectorData
    rw [List.getD_eq_getElem?_getD]
    simp [h]
  · rw [List.getD_append_right _ _ _ _ (by rw [hvl]; omega), dif_neg h, hvl]
    by_cases h2 : i.1 - k < m * b
    · rw [dif_pos h2, g_blockData_getD y _ h2]
    · rw [dif_neg h2, List.getD_eq_default _ _ (by rw [g_blockData_length]; omega)]

theorem g_Φ_block {k b m N : ℕ} (p : Vec F k × Blocks F b m) (u : Fin m) (v : Fin b)
    (h : k + (u.1 * b + v.1) < N) : g_Φ F k b m N p ⟨k + (u.1 * b + v.1), h⟩ = p.2 u v := by
  have hlt : u.1 * b + v.1 < m * b := by
    have := u.2; have := v.2
    have : (u.1 + 1) * b ≤ m * b := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have hb : 0 < b := by have := v.2; omega
  have hdm : (u.1 * b + v.1) / b = u.1 ∧ (u.1 * b + v.1) % b = v.1 :=
    ⟨by rw [add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt v.2, zero_add],
     by rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.2]⟩
  simp only [g_Φ, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_neg (by omega), dif_pos (by rw [Nat.add_sub_cancel_left]; exact hlt)]
  have key : ∀ (a a' : Fin m) (c c' : Fin b), a.1 = a'.1 → c.1 = c'.1 → p.2 a c = p.2 a' c' :=
    fun a a' c c' h1 h2 => by rw [Fin.ext h1, Fin.ext h2]
  apply key
  · simp only [Nat.add_sub_cancel_left]; exact hdm.1
  · simp only [Nat.add_sub_cancel_left]; exact hdm.2

theorem g_Φ_inj {k b m N : ℕ} (hN : k + m * b ≤ N) : Function.Injective (g_Φ F k b m N) := by
  intro p p' hpp
  have hc : ∀ i : Fin N, g_Φ F k b m N p i = g_Φ F k b m N p' i := fun i => congrFun hpp i
  apply Prod.ext
  · funext j
    have hj : j.1 < N := by have := j.2; omega
    have := hc ⟨j.1, hj⟩
    simpa [g_Φ, j.2] using this
  · funext u v
    have hlt : k + (u.1 * b + v.1) < N := by
      have := u.2; have := v.2
      have : (u.1 + 1) * b ≤ m * b := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    have := hc ⟨_, hlt⟩
    rwa [g_Φ_block, g_Φ_block] at this

end lists

/-! ### Evasiveness transport and the affine consequence -/

section evasive
variable {F : Type} [Field F]

theorem g_evasive_image {V W : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (Φ : V →ₗ[F] W) (hΦ : Function.Injective Φ) (G : Set V) (r c : ℕ)
    (h : Evasive (F := F) G r c) : Evasive (F := F) (Φ '' G) r c := by
  intro U hU
  have hU' : Module.finrank F (U.comap Φ) ≤ r := by
    have e := (Submodule.equivMapOfInjective Φ hΦ (U.comap Φ)).finrank_eq
    have := Submodule.finrank_mono (Submodule.map_comap_le Φ U)
    omega
  obtain ⟨h1, h2⟩ := h _ hU'
  have : Φ '' G ∩ (U : Set W) = Φ '' (G ∩ (U.comap Φ : Set V)) := by
    show _ = Φ '' (G ∩ Φ ⁻¹' (U : Set W))
    rw [Set.image_inter_preimage]
  rw [this]
  exact ⟨h1.image _, by rwa [Set.ncard_image_of_injective _ hΦ]⟩

theorem g_evasive_mono {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (G : Set V) (r c c' : ℕ) (h : Evasive (F := F) G r c) (hc : c ≤ c') :
    Evasive (F := F) G r c' := fun U hU => ⟨(h U hU).1, (h U hU).2.trans hc⟩

theorem g_affine {n : ℕ} (A : Set (Vec F n)) (r c : ℕ) (hr : 1 ≤ r)
    (h : Evasive (F := F) A r c) : AffineEvasive A (r - 1) c := by
  intro U hU a
  have hfr : Module.finrank F ↥(U ⊔ Submodule.span F {a}) ≤ r := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank U (Submodule.span F {a})
    have h2 : Module.finrank F (Submodule.span F ({a} : Set (Vec F n))) ≤ 1 := by
      simpa using finrank_span_le_card ({a} : Set (Vec F n))
    omega
  obtain ⟨hf, hc⟩ := h _ hfr
  have hsub : A ∩ {x | x - a ∈ U} ⊆ A ∩ ((U ⊔ Submodule.span F {a} : Submodule F _) : Set _) := by
    rintro x ⟨hx, hxU⟩
    refine ⟨hx, ?_⟩
    have : x = (x - a) + a := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hxU)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self a))
  exact ⟨hf.subset hsub, (Set.ncard_le_ncard hsub hf).trans hc⟩

end evasive

/-! ### Regrouping and list recovery -/

section regroup
variable {F : Type} [Field F]

theorem g_ug1 {J t m : ℕ} (h : J < t * m) : J / t < m := by
  have ht : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
  exact (Nat.div_lt_iff_lt_mul ht).2 (by rwa [mul_comm])

theorem g_ug2 {J t m s u : ℕ} (h : J < t * m) (hu : u < s) : (J % t) * s + u < t * s := by
  have ht : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
  have := Nat.mod_lt J ht
  have : (J % t + 1) * s ≤ t * s := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- Inverse of `regroup`. -/
def g_ungroup {s t m : ℕ} (c : Blocks F (t * s) m) : Blocks F s (t * m) :=
  fun J u => c ⟨J.1 / t, g_ug1 J.2⟩ ⟨(J.1 % t) * s + u.1, g_ug2 J.2 u.2⟩

theorem g_ungroup_regroup {s t m : ℕ} (x : Blocks F s (t * m)) :
    g_ungroup (regroup x) = x := by
  funext J u
  have hs : 0 < s := by have := u.2; omega
  have hdm : ((J.1 % t) * s + u.1) / s = J.1 % t ∧ ((J.1 % t) * s + u.1) % s = u.1 :=
    ⟨by rw [add_comm, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt u.2, zero_add],
     by rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt u.2]⟩
  simp only [g_ungroup, regroup]
  congr 1
  · apply Fin.ext; simp only; rw [hdm.1]; exact Nat.div_add_mod J.1 t
  · apply Fin.ext; simp only; exact hdm.2

theorem g_regroup_ungroup {s t m : ℕ} (c : Blocks F (t * s) m) :
    regroup (g_ungroup c) = c := by
  funext i j
  have hs : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; simpa using j.2)
  have ht : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; simpa using j.2)
  have hjt : j.1 / s < t := (Nat.div_lt_iff_lt_mul hs).2 j.2
  have h1 : (t * i.1 + j.1 / s) / t = i.1 := by
    rw [Nat.mul_add_div ht, Nat.div_eq_of_lt hjt, add_zero]
  have h2 : (t * i.1 + j.1 / s) % t = j.1 / s := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hjt]
  simp only [g_ungroup, regroup]
  congr 1
  · apply Fin.ext; simp only; exact h1
  · apply Fin.ext; simp only; rw [h2]; exact Nat.div_add_mod' j.1 s

theorem g_regroup_inj {s t m : ℕ} : Function.Injective (regroup (F := F) (s := s) (t := t) (m := m)) :=
  fun x y h => by rw [← g_ungroup_regroup x, h, g_ungroup_regroup]

theorem g_hamming_zero {s m : ℕ} {c y : Blocks F s m} (h : (hamming c y : ℝ) ≤ 0 * m) :
    c = y := by
  have h0 : hamming c y = 0 := by
    have : (hamming c y : ℝ) ≤ 0 := by simpa using h
    exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
  classical
  unfold hamming at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  funext i
  simpa using h0 (Finset.mem_univ i)

theorem g_hamming_self {s m : ℕ} (c : Blocks F s m) : hamming c c = 0 := by
  unfold hamming; simp

theorem g_LR_mono {s m : ℕ} (C : Code F s m) (r : ℕ) (ρ : ℝ) (ℓ : ℕ) (L L' : ℝ≥0∞)
    (h : ListRecoverable C r ρ ℓ L) (hL : L ≤ L') : ListRecoverable C r ρ ℓ L' :=
  fun U hU S hS T hT => (h U hU S hS T hT).trans hL

/-- Zero-error list recovery passes to a regrouped subcode. -/
theorem g_LR_regroup {s t m r ℓ : ℕ} (L : ℝ≥0∞) (C : Code F s (t * m))
    (hC : ListRecoverable C r 0 ℓ L) (C' : Code F (t * s) m)
    (hC' : ∀ c ∈ C', g_ungroup c ∈ C) : ListRecoverable C' r 0 ℓ L := by
  classical
  intro U hU S hS T hT
  let G := regroupL F s t m
  have hGinj : Function.Injective G := g_regroup_inj
  have hU0 : Module.finrank F (U.comap G) ≤ r := by
    have e := (Submodule.equivMapOfInjective G hGinj (U.comap G)).finrank_eq
    have := Submodule.finrank_mono (Submodule.map_comap_le G U)
    omega
  let sub : Fin (t * m) → Vec F (t * s) → Vec F s :=
    fun J v u => v ⟨(J.1 % t) * s + u.1, g_ug2 J.2 u.2⟩
  let S0 : Fin (t * m) → Finset (Vec F s) := fun J => (S ⟨J.1 / t, g_ug1 J.2⟩).image (sub J)
  have hS0 : ∀ J, (S0 J).card ≤ ℓ := fun J => Finset.card_image_le.trans (hS _)
  let T0 := T.image g_ungroup
  have hinj : Function.Injective (g_ungroup (F := F) (s := s) (t := t) (m := m)) :=
    fun x y h => by rw [← g_regroup_ungroup x, h, g_regroup_ungroup]
  have hT0 : (↑T0 : Set _) ⊆ recovered C (U.comap G) S0 0 := by
    intro c0 hc0
    simp only [T0, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hc0
    obtain ⟨c, hcT, rfl⟩ := hc0
    obtain ⟨hcC, hcU, y, hyS, hy⟩ := hT hcT
    have hcy := g_hamming_zero hy
    subst hcy
    refine ⟨hC' c hcC, ?_, g_ungroup c, ?_, by simp [g_hamming_self]⟩
    · show G (g_ungroup c) ∈ U
      show regroup (g_ungroup c) ∈ U
      rw [g_regroup_ungroup]; exact hcU
    · intro J
      exact Finset.mem_image.2 ⟨c ⟨J.1 / t, g_ug1 J.2⟩, hyS _, rfl⟩
  have := hC _ hU0 S0 hS0 T0 hT0
  rwa [Finset.card_image_of_injective _ hinj] at this

end regroup

/-! ### Machine monotonicity -/

section machine
variable {F : Type} [Field F]

theorem g_runFrom_mono (P : Program F) (ns : List ℕ) (xs : List F) {B B' : ℕ} (hB : B ≤ B') :
    ∀ (t : ℕ) (z w : MachineState F), runFrom P ns xs B t z = some w →
      runFrom P ns xs B' t z = some w := by
  intro t
  induction t with
  | zero => intro z w h; simp [runFrom] at h
  | succ t ih =>
    intro z w h
    simp only [runFrom] at h ⊢
    split_ifs at h with hb
    rw [if_pos (fun i => (hb i).trans hB)]
    split at h
    · simp [h]
    · rename_i hne
      cases hs : step P ns xs z with
      | none => rw [hs] at h; simp at h
      | some z' => rw [hs] at h; simp only [Option.bind_some] at h ⊢; exact ih z' w h

theorem g_runsWithin_mono {P : Program F} {ns : List ℕ} {xs : List F} {T B T' B' : ℕ}
    {ys : List F} {outN : List ℕ} (h : RunsWithin P ns xs T B ys outN) (hT : T ≤ T')
    (hB : B ≤ B') : RunsWithin P ns xs T' B' ys outN := by
  obtain ⟨t, z, h1, h2, h3, h4⟩ := h
  exact ⟨t, z, h1.trans hT, g_runFrom_mono P ns xs hB t _ _ h2, h3, h4⟩

theorem g_GA_mono {D : ∀ N, Assembly F N} {index member : Program F} {C deg deg' N₀ : ℕ}
    (h : GlobalAlgorithms D index member C deg N₀) (hd : deg ≤ deg') :
    GlobalAlgorithms D index member C deg' N₀ := by
  unfold GlobalAlgorithms at h ⊢
  intro N hN
  have hle : C * (N + 1) ^ deg ≤ C * (N + 1) ^ deg' :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hd)
  obtain ⟨h1, h2⟩ := h N hN
  exact ⟨fun x => g_runsWithin_mono (h1 x) hle hle, fun y => g_runsWithin_mono (h2 y) hle hle⟩

end machine

end SubspaceEvasion312.Explicit.Dev.Goal
end
end

section
set_option autoImplicit false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal
open SubspaceEvasion312.Explicit
open scoped ENNReal

/-! ## Part 3: the construction for one code family -/

theorem g_inj_of_encoder {F : Type} [Field F] {s m k : ℕ}
    (C : Code F s m) (E : Vec F k →ₗ[F] Blocks F s m) (hE : IsEncoder C E) :
    Function.Injective E := by
  obtain ⟨hk, hr⟩ := hE
  have h1 := LinearMap.finrank_range_add_finrank_ker E
  rw [hr, ← hk, Module.finrank_fin_fun] at h1
  have h2 : Module.finrank F (LinearMap.ker E) = 0 := by omega
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.mp h2

theorem g_encN_inj {F : Type} [Field F] {s₀ : ℕ} (kf : ℕ → ℕ)
    (E : ∀ m, Vec F (kf m) →ₗ[F] Blocks F s₀ m) (t b num den N : ℕ)
    (hE : Function.Injective (E (t * mN num den b N)))
    (hk : kN num den b N ≤ kf (t * mN num den b N)) :
    Function.Injective (encN kf E t b num den N) := by
  intro x y hxy
  have h1 : E (t * mN num den b N) (padL F _ _ x) = E (t * mN num den b N) (padL F _ _ y) :=
    g_regroup_inj hxy
  have h2 := hE h1
  funext i
  have := congrFun h2 ⟨i.1, by omega⟩
  simpa [padL, i.2] using this

theorem g_core (F : Type) [Field F] [Fintype F] (r : ℕ) (ε : ℝ) (degree : ℕ) (affine : Bool)
    (hr : 0 < r) (hε : 0 < ε) (hε1 : ε < 1) (ℓ : ℕ) (hIB : 2 * ℓ ≤ intersectionBound r ε)
    (s₀ K m₀ h : ℕ) (hs₀ : 0 < s₀) (C : ∀ m, Code F s₀ m) (kf : ℕ → ℕ)
    (E : ∀ m, Vec F (kf m) →ₗ[F] Blocks F s₀ m) (enc : Program F) (R : ℝ) (hR : 0 < R)
    (henc : ∀ m ≥ m₀, ∀ x, RunsWithin enc [m] (vectorData x) (K * (m+1)^h) (K * (m+1)^h)
      (blockData (E m x)))
    (hfam : ∀ m ≥ m₀, IsEncoder (C m) (E m) ∧ R ≤ codeRate (C m) ∧
      ListRecoverable (C m) r 0 ℓ (2 * ℓ))
    (hrate : (r:ℝ) < 3 * ε / 4 * R * (((ℓ + 1 : ℕ) : ℝ) - r))
    (hdeg : h + 2 ≤ degree) :
    FixedFieldConstruction (F := F) r ε degree affine := by
  classical
  -- the rational η
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show 3 * ε / 4 < ε by linarith)
  have hq0 : (0:ℝ) < q := by linarith
  have hq0' : (0:ℚ) < q := by exact_mod_cast hq0
  have hden : 0 < q.den := q.den_pos
  have hqnd : (q:ℝ) = ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) := by
    have h1 : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq0'.le)
    have hnum : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
      rw [← Int.cast_natCast, h1]
    have e : (q:ℝ) = (((q.num : ℚ) / q.den : ℚ) : ℝ) := by rw [Rat.num_div_den q]
    rw [e, hnum]; push_cast; rfl
  set num := q.num.toNat with hnum_def
  set den := q.den with hden_def
  -- t and b
  have hdr : 0 < ((ℓ + 1 : ℕ) : ℝ) - r := by
    by_contra hc
    replace hc := not_lt.mp hc
    have : 3 * ε / 4 * R * (((ℓ + 1 : ℕ) : ℝ) - r) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have hrate' : (r:ℝ) < q * R * (((ℓ + 1 : ℕ) : ℝ) - r) :=
    hrate.trans (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hq1 hR) hdr)
  obtain ⟨t, b, ht, hb, hloc, hbr⟩ :=
    g_params s₀ r (ℓ + 1) hs₀ R q hR hq0 (by linarith) hrate'
  obtain ⟨N₀, hN₀, hNbig⟩ := g_rate b (t * s₀) m₀ hb R q hR hq0 (by linarith) hbr
  set alphabet : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm with halph
  set f := localFunction (List.ofFn alphabet) (t * s₀) b r (ℓ + 1) with hf
  have hmN : ∀ N, mN num den b N = ⌊(q:ℝ) * N / b⌋₊ := fun N => g_mN num den b N q hqnd hden hb
  have hfacts : ∀ N ≥ N₀, m₀ ≤ t * mN num den b N ∧ 0 < mN num den b N ∧
      b * mN num den b N ≤ N ∧ kN num den b N ≤ kf (t * mN num den b N) := by
    intro N hN
    obtain ⟨h1, h2, h3⟩ := hNbig N hN
    rw [← hmN] at h1 h2 h3
    have hm0 : m₀ ≤ t * mN num den b N :=
      le_trans h1.le (Nat.le_mul_of_pos_left _ ht)
    refine ⟨hm0, by omega, h2, ?_⟩
    obtain ⟨hIE, hRate, -⟩ := hfam _ hm0
    have hkf : R * ((t * s₀ : ℕ) : ℝ) * (mN num den b N : ℝ) ≤ kf (t * mN num den b N) := by
      unfold codeRate at hRate
      rw [← hIE.1] at hRate
      have hpos : (0:ℝ) < ((s₀ * (t * mN num den b N) : ℕ) : ℝ) := by
        have : 0 < s₀ * (t * mN num den b N) := Nat.mul_pos hs₀ (Nat.mul_pos ht (by omega))
        exact_mod_cast this
      rw [le_div_iff₀ hpos] at hRate
      push_cast at hRate ⊢
      calc R * ((t:ℝ) * s₀) * (mN num den b N : ℝ) = R * (s₀ * (t * (mN num den b N : ℝ))) := by
            ring
        _ ≤ _ := hRate
    unfold kN
    have : ((N - b * mN num den b N : ℕ) : ℝ) ≤ kf (t * mN num den b N) := by
      rw [Nat.cast_sub h2]; push_cast at h3 hkf ⊢; nlinarith
    exact_mod_cast this
  obtain ⟨index, member, Cst, hC, hGA⟩ :=
    uniform_machine F hs₀ kf E enc K h m₀ henc t b num den ht hb hden f N₀ hfacts
  refine ⟨q, t * s₀, b, ℓ + 1, N₀, Cst, alphabet, asm kf E t b num den f, index, member,
    hq1, hq2, Nat.mul_pos ht hs₀, hb, by omega, hN₀, hC, g_GA_mono hGA hdeg, ?_⟩
  intro N hN A
  obtain ⟨hm0, hmpos, hbm, hk⟩ := hfacts N hN
  -- encoder
  have hE_inj : Function.Injective (E (t * mN num den b N)) :=
    g_inj_of_encoder _ _ (hfam _ hm0).1
  have henc_inj := g_encN_inj kf E t b num den N hE_inj hk
  have hIsEnc : IsEncoder (LinearMap.range (encN kf E t b num den N))
      (encN kf E t b num den N) :=
    ⟨by rw [LinearMap.finrank_range_of_inj henc_inj, Module.finrank_fin_fun], rfl⟩
  have hLR : ListRecoverable (LinearMap.range (encN kf E t b num den N)) r 0 ℓ (2 * ℓ) := by
    refine g_LR_regroup _ (C (t * mN num den b N)) (hfam _ hm0).2.2 _ ?_
    rintro c ⟨x, rfl⟩
    have h1 : g_ungroup (encN kf E t b num den N x) =
        E (t * mN num den b N) (padL F _ _ x) := g_ungroup_regroup _
    rw [h1, ← (hfam _ hm0).1.2]
    exact LinearMap.mem_range_self _ _
  -- the local graph
  obtain ⟨KL, -, hLG⟩ := local_graph
  obtain ⟨P, hP⟩ := hLG F (List.ofFn alphabet) (List.nodup_ofFn.mpr alphabet.injective)
    (fun a => List.mem_ofFn.mpr ⟨alphabet.symm a, by simp⟩)
  have hEvf : Evasive (F := F) (graph f) r ℓ := by
    have := (hP (t * s₀) b r (ℓ + 1) (Nat.mul_pos ht hs₀) hb hr (by omega) hloc).1
    simpa using this
  obtain ⟨KT, -, hLTG⟩ := local_to_global
  have hEvg : Evasive (F := F) (graph (compose (encN kf E t b num den N) f)) r (2 * ℓ) :=
    (hLTG F (t * s₀) b (mN num den b N) (kN num den b N) r ℓ (2 * ℓ) _
      (encN kf E t b num den N) f hIsEnc hEvf (by push_cast; exact hLR)).2.1
  -- the coordinate map
  have hNk : kN num den b N + mN num den b N * b ≤ N := by
    unfold kN; rw [Nat.mul_comm (mN num den b N) b]; omega
  have hΦinj := g_Φ_inj (F := F) hNk
  have hpoint : ∀ x, A.point x = g_Φ F (kN num den b N) b (mN num den b N) N
      (x, compose (encN kf E t b num den N) f x) := fun x => funext fun i => g_Φ_apply _ _ i
  have hset : A.set = g_Φ F (kN num den b N) b (mN num den b N) N ''
      graph (compose (encN kf E t b num den N) f) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x, compose (encN kf E t b num den N) f x), rfl, (hpoint x).symm⟩
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      have hy : y = compose (encN kf E t b num den N) f x := hxy
      subst hy
      exact ⟨x, hpoint x⟩
  have hpinj : Function.Injective A.point := fun x y hxy => by
    rw [hpoint, hpoint] at hxy
    exact congrArg Prod.fst (hΦinj hxy)
  have hEvA : Evasive (F := F) A.set r (intersectionBound r ε) := by
    rw [hset]
    exact g_evasive_mono _ _ _ _ (g_evasive_image _ hΦinj _ _ _ hEvg) hIB
  -- indexing
  let e1 : Fin (Fintype.card F ^ kN num den b N) ≃ Vec F (kN num den b N) :=
    finFunctionFinEquiv.symm.trans (Equiv.arrowCongr (Equiv.refl _) alphabet)
  have he1 : ∀ i, e1 i = indexVector alphabet i := by
    intro i; funext j
    simp only [e1, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.refl_symm,
      Equiv.coe_refl, Function.comp_apply, id, indexVector]
    congr 1
  let idx : Fin (Fintype.card F ^ A.k) ≃ A.set := e1.trans (Equiv.ofInjective A.point hpinj)
  have hncard : A.set.ncard = Fintype.card F ^ A.k := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_congr idx, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hbmq : ((b * mN num den b N : ℕ) : ℝ) ≤ q * N := by
    rw [hmN]; push_cast
    have hb' : (0:ℝ) < b := by exact_mod_cast hb
    calc (b:ℝ) * ⌊(q:ℝ) * N / b⌋₊ ≤ b * ((q:ℝ) * N / b) :=
          mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) hb'.le
      _ = q * N := by field_simp
  refine ⟨⟨Nat.mul_pos ht hs₀, hb, hmpos, ?_, rfl, hIsEnc⟩, rfl, rfl, hmN N, rfl, hloc,
    by simpa using hIB,
    by have h' : ListRecoverable A.code r 0 ℓ (2 * ℓ) := hLR; simpa using h', ⟨idx, fun i => ?_⟩, Set.finite_range _, hncard, ?_,
    hEvA, fun _ => by simpa using g_affine _ _ _ hr hEvA⟩
  · show N = kN num den b N + b * mN num den b N
    unfold kN; omega
  · show A.point (e1 i) = _
    exact congrArg A.point (he1 i)
  · rw [hncard]
    push_cast
    rw [← Real.rpow_natCast]
    have hq1' : (1:ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
    apply Real.rpow_le_rpow_of_exponent_le hq1'
    show (1 - ε) * N ≤ ((kN num den b N : ℕ) : ℝ)
    unfold kN
    rw [Nat.cast_sub hbm]
    nlinarith [Nat.cast_nonneg (α := ℝ) N]

end SubspaceEvasion312.Explicit.Dev.Goal
end
end

section
set_option autoImplicit false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.Goal
open SubspaceEvasion312.Explicit
open scoped ENNReal

/-! ## Part 4: choosing the code family -/

theorem g_fixed (F : Type) [Field F] [Fintype F] (r : ℕ) (ε : ℝ) (degree : ℕ) (affine : Bool)
    (hr : 0 < r) (hε : 0 < ε) (hε1 : ε < 1) (hq hl : ℕ)
    (hQ : ∀ (r : ℕ), 0 < r →
      ∃ (s K m₀ : ℕ) (C : ∀ m, Code F s m) (k : ℕ → ℕ)
        (E : ∀ m, Vec F (k m) →ₗ[F] Blocks F s m) (enc : Program F),
        0 < s ∧
        (∀ m ≥ m₀, ∀ x, RunsWithin enc [m] (vectorData x) (K * (m+1)^hq) (K * (m+1)^hq)
          (blockData (E m x))) ∧
        ∀ m ≥ m₀, IsEncoder (C m) (E m) ∧ 1 / (2*(r : ℝ)) ≤ codeRate (C m) ∧
          ∀ ℓ : ℕ, ListRecoverable (C m) r 0 ℓ ℓ)
    (hL : ∀ (r ℓ : ℕ), 0 < ℓ →
      ∃ (s K m₀ : ℕ) (C : ∀ m, Code F s m) (k : ℕ → ℕ)
        (E : ∀ m, Vec F (k m) →ₗ[F] Blocks F s m) (enc : Program F),
        0 < s ∧
        (∀ m ≥ m₀, ∀ x, RunsWithin enc [m] (vectorData x) (K * (m+1)^hl) (K * (m+1)^hl)
          (blockData (E m x))) ∧
        ∀ m ≥ m₀, IsEncoder (C m) (E m) ∧ 1 / (2 + 2 * log₂ (ℓ : ℝ)) ≤ codeRate (C m) ∧
          ListRecoverable (C m) r 0 ℓ (2*ℓ))
    (hdq : hq + 2 ≤ degree) (hdl : hl + 2 ≤ degree) :
    FixedFieldConstruction (F := F) r ε degree affine := by
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hQlo : 16 * (r:ℝ)^2/ε ≤ quadraticList r ε := Nat.le_ceil _
  have hQhi : (quadraticList r ε : ℝ) < 16 * (r:ℝ)^2/ε + 1 := Nat.ceil_lt_add_one (by positivity)
  by_cases hcase : quadraticList r ε ≤ logarithmicList r ε
  · obtain ⟨s, K, m₀, C, k, E, enc, hs, henc, hfam⟩ := hQ r hr
    refine g_core F r ε degree affine hr hε hε1 (quadraticList r ε)
      (le_min le_rfl (by omega)) s K m₀ hq hs C k E enc (1 / (2 * r)) (by positivity) henc
      (fun m hm => ⟨(hfam m hm).1, (hfam m hm).2.1,
        g_LR_mono _ _ _ _ _ _ ((hfam m hm).2.2 _)
          (le_mul_of_one_le_left (zero_le) (by norm_num))⟩) ?_ hdq
    have hεQ : 16 * (r:ℝ)^2 ≤ (quadraticList r ε : ℝ) * ε := by
      rwa [div_le_iff₀ hε] at hQlo
    push_cast
    rw [show 3 * ε / 4 * (1 / (2 * (r:ℝ))) * ((quadraticList r ε : ℝ) + 1 - r) =
      3 * ε * ((quadraticList r ε : ℝ) + 1 - r) / (8 * r) by field_simp; ring]
    rw [lt_div_iff₀ (by positivity)]
    have : ε * r < r := by nlinarith
    nlinarith
  · replace hcase := not_le.mp hcase
    set ℓ := logarithmicList r ε with hℓdef
    set L := log₂ ((r:ℝ) / ε) with hLdef
    have hx1 : (1:ℝ) ≤ (r:ℝ) / ε := by rw [le_div_iff₀ hε]; linarith
    have hL0 : 0 ≤ L := div_nonneg (Real.log_nonneg hx1) hl2.le
    have hℓlo : 256 * (r:ℝ) * (1 + L) / ε ≤ ℓ := Nat.le_ceil _
    have hℓpos : 0 < ℓ := by
      have : (0:ℝ) < ℓ := lt_of_lt_of_le (by positivity) hℓlo
      exact_mod_cast this
    have hℓ1 : (1:ℝ) ≤ ℓ := by exact_mod_cast hℓpos
    obtain ⟨s, K, m₀, C, k, E, enc, hs, henc, hfam⟩ := hL r ℓ hℓpos
    set P := log₂ (ℓ : ℝ) with hPdef
    have hP0 : 0 ≤ P := div_nonneg (Real.log_nonneg hℓ1) hl2.le
    refine g_core F r ε degree affine hr hε hε1 ℓ (le_min (by omega) le_rfl)
      s K m₀ hl hs C k E enc (1 / (2 + 2 * P)) (by positivity) henc hfam ?_ hdl
    -- ℓ < 16 r²/ε ≤ 16 (r/ε)², hence P ≤ 4 + 2 L
    have hℓhi : (ℓ : ℝ) ≤ 16 * ((r:ℝ) / ε)^2 := by
      have h1 : ((ℓ + 1 : ℕ) : ℝ) ≤ quadraticList r ε := by exact_mod_cast hcase
      push_cast at h1
      have h2 : 16 * (r:ℝ)^2/ε ≤ 16 * ((r:ℝ)/ε)^2 := by
        rw [div_pow, show 16 * ((r:ℝ)^2/ε^2) = 16 * (r:ℝ)^2/ε^2 by ring]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith
      linarith
    have hP : P ≤ 4 + 2 * L := by
      have hlog : Real.log ℓ ≤ 4 * Real.log 2 + 2 * Real.log ((r:ℝ)/ε) := by
        calc Real.log ℓ ≤ Real.log (16 * ((r:ℝ)/ε)^2) := Real.log_le_log (by positivity) hℓhi
          _ = 4 * Real.log 2 + 2 * Real.log ((r:ℝ)/ε) := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
              show (16:ℝ) = 2^4 by norm_num, Real.log_pow]
            push_cast; ring
      rw [hPdef, hLdef]
      unfold log₂
      rw [div_le_iff₀ hl2]
      rw [add_mul, mul_assoc, div_mul_cancel₀ _ hl2.ne']
      linarith
    have hεℓ : 256 * (r:ℝ) * (1 + L) ≤ ε * ℓ := by
      rw [div_le_iff₀ hε] at hℓlo; linarith
    push_cast
    rw [show 3 * ε / 4 * (1 / (2 + 2 * P)) * ((ℓ : ℝ) + 1 - r) =
      3 * ε * ((ℓ : ℝ) + 1 - r) / (4 * (2 + 2 * P)) by field_simp]
    rw [lt_div_iff₀ (by positivity)]
    have : (r:ℝ) * P ≤ r * (4 + 2 * L) := mul_le_mul_of_nonneg_left hP (by positivity)
    have : ε * r < r := by nlinarith
    nlinarith

end SubspaceEvasion312.Explicit.Dev.Goal

namespace SubspaceEvasion312.Explicit
open Dev.Goal in
/-- Theorem 24, printed p.12 (PDF p.13), with both ceiling estimates from
its proof and the introductory affine consequence at rank r+1. -/
theorem chk_explicit_subspace_evasive_sets :
    ∃ degree : ℕ,
      (∀ (r : ℕ) (ε : ℝ), 0 < r → 0 < ε → ε < 1 → 2 ≤ (r : ℝ)/ε →
        (intersectionBound r ε : ℝ) ≤ 1028 * asymptoticShape r ε ∧
        (intersectionBound (r+1) ε : ℝ) ≤ 4112 * asymptoticShape r ε) ∧
      ∀ (F : Type) [Field F] [Fintype F] (r : ℕ) (ε : ℝ),
        0 < r → 0 < ε → ε < 1 →
        FixedFieldConstruction (F := F) r ε degree false ∧
        FixedFieldConstruction (F := F) (r+1) ε degree true := by
  obtain ⟨Aq, aq, hq, -, hQ⟩ := quadratic_code_family
  obtain ⟨Al, al, hl, -, hL⟩ := logarithmic_code_family
  refine ⟨max hq hl + 2, fun r ε hr hε hε1 hx => g_ceil r ε hr hε hε1 hx, ?_⟩
  intro F _ _ r ε hr hε hε1
  have hQ' : ∀ (r : ℕ), 0 < r →
      ∃ (s K m₀ : ℕ) (C : ∀ m, Code F s m) (k : ℕ → ℕ)
        (E : ∀ m, Vec F (k m) →ₗ[F] Blocks F s m) (enc : Program F),
        0 < s ∧
        (∀ m ≥ m₀, ∀ x, RunsWithin enc [m] (vectorData x) (K * (m+1)^hq) (K * (m+1)^hq)
          (blockData (E m x))) ∧
        ∀ m ≥ m₀, IsEncoder (C m) (E m) ∧ 1 / (2*(r : ℝ)) ≤ codeRate (C m) ∧
          ∀ ℓ : ℕ, ListRecoverable (C m) r 0 ℓ ℓ := by
    intro r hr
    obtain ⟨s, K, m₀, C, k, E, τ, gen, enc, hs, -, -, -, hCA, hfam⟩ := hQ F r hr
    exact ⟨s, K, m₀, C, k, E, enc, hs, fun m hm x => (hCA m hm).2 x,
      fun m hm => ⟨(hfam m hm).1, (hfam m hm).2.1, (hfam m hm).2.2.2.2⟩⟩
  have hL' : ∀ (r ℓ : ℕ), 0 < ℓ →
      ∃ (s K m₀ : ℕ) (C : ∀ m, Code F s m) (k : ℕ → ℕ)
        (E : ∀ m, Vec F (k m) →ₗ[F] Blocks F s m) (enc : Program F),
        0 < s ∧
        (∀ m ≥ m₀, ∀ x, RunsWithin enc [m] (vectorData x) (K * (m+1)^hl) (K * (m+1)^hl)
          (blockData (E m x))) ∧
        ∀ m ≥ m₀, IsEncoder (C m) (E m) ∧ 1 / (2 + 2 * log₂ (ℓ : ℝ)) ≤ codeRate (C m) ∧
          ListRecoverable (C m) r 0 ℓ (2*ℓ) := by
    intro r ℓ hℓ
    obtain ⟨s, K, m₀, C, k, E, τ, gen, enc, hs, -, -, -, hCA, hfam⟩ := hL F r ℓ hℓ
    exact ⟨s, K, m₀, C, k, E, enc, hs, fun m hm x => (hCA m hm).2 x,
      fun m hm => ⟨(hfam m hm).1, (hfam m hm).2.1, (hfam m hm).2.2.2.2⟩⟩
  exact ⟨g_fixed F r ε _ false hr hε hε1 hq hl hQ' hL' (by omega) (by omega),
    g_fixed F (r+1) ε _ true (by omega) hε hε1 hq hl hQ' hL' (by omega) (by omega)⟩

end SubspaceEvasion312.Explicit
end
end

theorem solution : type_of% @SubspaceEvasion312.Explicit.chk_explicit_subspace_evasive_sets := @SubspaceEvasion312.Explicit.chk_explicit_subspace_evasive_sets

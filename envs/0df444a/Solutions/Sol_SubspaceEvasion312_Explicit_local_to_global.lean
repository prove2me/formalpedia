-- Prove2me | solution 1 for SubspaceEvasion312.Explicit.local_to_global
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T18:08:18.025255+00:00
-- url     : https://prove2.me/submissions/80e60734-328f-43ec-bcc7-b854e4dc78fe

import Mathlib
import Definitions.Def_SubspaceEvasion312_Explicit_effective

section
set_option autoImplicit false
noncomputable section

namespace SubspaceEvasion312.Explicit.Dev.LTG
open SubspaceEvasion312.Explicit

/-! ### Part LTGMachine1 -/
variable {F : Type} [Field F]

/-- The effect of one instruction (with empty nat input). -/
def m_eff (xs : List F) (z : MachineState F) : Instruction F → MachineState F
  | .halt => z
  | .literal d v => {z with pc := z.pc + 1, natReg := Function.update z.natReg d v}
  | .inputNat d _ => {z with pc := z.pc + 1, natReg := Function.update z.natReg d 0}
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

theorem m_step_eq {P : Program F} {xs : List F} {z : MachineState F} {ins : Instruction F}
    (h : P[z.pc]? = some ins) (hh : ins ≠ .halt) : step P [] xs z = some (m_eff xs z ins) := by
  cases ins <;> simp_all [step, m_eff]

/-- `m_reach Q xs B n w w'`: `n` non-halting steps, each from a bounded state. -/
inductive m_reach (Q : Program F) (xs : List F) (B : ℕ) :
    ℕ → MachineState F → MachineState F → Prop
  | zero (w : MachineState F) : m_reach Q xs B 0 w w
  | succ {n : ℕ} {w w' : MachineState F} (ins : Instruction F) :
      (∀ i, w.natReg i ≤ B) → Q[w.pc]? = some ins → ins ≠ .halt →
      m_reach Q xs B n (m_eff xs w ins) w' → m_reach Q xs B (n + 1) w w'

theorem m_reach_trans {Q : Program F} {xs : List F} {B a b : ℕ} {w1 w2 w3 : MachineState F}
    (h1 : m_reach Q xs B a w1 w2) (h2 : m_reach Q xs B b w2 w3) :
    m_reach Q xs B (b + a) w1 w3 := by
  induction h1 with
  | zero => simpa using h2
  | succ ins hb hq hh _ ih => exact m_reach.succ ins hb hq hh (ih h2)

theorem m_runFrom_of_reach {Q : Program F} {xs : List F} {B n : ℕ} {w w' : MachineState F}
    (h : m_reach Q xs B n w w') (t : ℕ) :
    runFrom Q [] xs B (n + t) w = runFrom Q [] xs B t w' := by
  induction h with
  | zero => simp
  | @succ n w w' ins hb hq hh _ ih =>
    rw [show n + 1 + t = (n + t) + 1 by omega]
    simp only [runFrom, hb, implies_true, if_true, hq]
    split
    · rename_i heq; cases heq; exact absurd rfl hh
    · rw [m_step_eq hq hh]; simpa using ih

theorem m_runFrom_halt {Q : Program F} {xs : List F} {B : ℕ} {w : MachineState F}
    (hb : ∀ i, w.natReg i ≤ B) (hq : Q[w.pc]? = some .halt) :
    runFrom Q [] xs B 1 w = some w := by
  simp [runFrom, hb, hq]

/-- Decomposing a successful sub-run. -/
theorem m_runFrom_succ {P : Program F} {xs : List F} {B t : ℕ} {z zf : MachineState F}
    (h : runFrom P [] xs B (t + 1) z = some zf) :
    (∀ i, z.natReg i ≤ B) ∧
    ((P[z.pc]? = some .halt ∧ zf = z) ∨
     ∃ ins, P[z.pc]? = some ins ∧ ins ≠ .halt ∧ runFrom P [] xs B t (m_eff xs z ins) = some zf) := by
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
      right; exact ⟨ins, rfl, hh, by rw [m_step_eq hq hh] at h; simpa using h⟩

theorem m_runFrom_bounded {P : Program F} {xs : List F} {B t : ℕ} {z zf : MachineState F}
    (h : runFrom P [] xs B t z = some zf) : ∀ i, z.natReg i ≤ B := by
  cases t with
  | zero => simp [runFrom] at h
  | succ t => exact (m_runFrom_succ h).1

/-- Output length grows by at most one per step, and never shrinks. -/
theorem m_eff_out (xs : List F) (z : MachineState F) (ins : Instruction F) :
    z.out.length ≤ (m_eff xs z ins).out.length ∧ (m_eff xs z ins).out.length ≤ z.out.length + 1 := by
  cases ins <;> simp [m_eff]

theorem m_runFrom_out {P : Program F} {xs : List F} {B : ℕ} :
    ∀ t (z zf : MachineState F), runFrom P [] xs B t z = some zf →
      z.out.length ≤ zf.out.length ∧ zf.out.length ≤ z.out.length + t := by
  intro t
  induction t with
  | zero => intro z zf h; simp [runFrom] at h
  | succ t ih =>
    intro z zf h
    obtain ⟨_, ⟨_, rfl⟩ | ⟨ins, _, _, h2⟩⟩ := m_runFrom_succ h
    · omega
    · have := ih _ _ h2
      have := m_eff_out xs z ins
      omega

theorem m_runFrom_halted {P : Program F} {xs : List F} {B : ℕ} :
    ∀ t (z zf : MachineState F), runFrom P [] xs B t z = some zf →
      P[zf.pc]? = some .halt ∧ ∀ i, zf.natReg i ≤ B := by
  intro t
  induction t with
  | zero => intro z zf h; simp [runFrom] at h
  | succ t ih =>
    intro z zf h
    obtain ⟨hb, ⟨hq, rfl⟩ | ⟨ins, _, _, h2⟩⟩ := m_runFrom_succ h
    · exact ⟨hq, hb⟩
    · exact ih _ _ h2

theorem m_programSize_pos {P : Program F} {xs : List F} {B t : ℕ} {z zf : MachineState F}
    (h : runFrom P [] xs B t z = some zf) : 1 ≤ programSize P := by
  have := (m_runFrom_halted t z zf h).1
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp this
  have : P ≠ [] := by rintro rfl; simp at hlt
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil this
  simp only [programSize, List.map_cons, List.sum_cons]
  have : 1 ≤ instructionSize a := by cases a <;> simp [instructionSize] <;> omega
  omega

theorem m_programSize_append (P Q : Program F) :
    programSize (P ++ Q) = programSize P + programSize Q := by
  simp [programSize]

theorem m_programSize_cons (a : Instruction F) (P : Program F) :
    programSize (a :: P) = instructionSize a + programSize P := by
  simp [programSize]

/-! ### Part LTGMachine2 -/
/-! Composite registers: 0 ZERO, 1 ONE, 2 RM (= M), 3 RES (residue), 4 S (= s), 5 IS (= i*s),
6 DA (data address), 7 IK (compare index), 8 KREG (= k), 9 FLAG, 10 T1, 11 T2, 12 CI.
Sub-program nat register `j` with residue `c` lives at `13 + j*M + c`; field register `j` at
`j*M + c`. Field residue 0 is the data region, field register 1 is scratch. -/

inductive m_Mode
  | pc
  | fd
  | fc

def m_nr (M c j : ℕ) : ℕ := 13 + j * M + c
def m_fr (M c j : ℕ) : ℕ := j * M + c


def m_tr (M c base exit : ℕ) (md : m_Mode) (p : ℕ) : Instruction F → List (Instruction F)
  | .halt => [.jump exit]
  | .literal d v => [.literal (m_nr M c d) v, .jump (base + 8 * p + 8)]
  | .inputNat d _ => [.subNat (m_nr M c d) (m_nr M c d) (m_nr M c d), .jump (base + 8 * p + 8)]
  | .addNat d a b => [.addNat (m_nr M c d) (m_nr M c a) (m_nr M c b), .jump (base + 8 * p + 8)]
  | .subNat d a b => [.subNat (m_nr M c d) (m_nr M c a) (m_nr M c b), .jump (base + 8 * p + 8)]
  | .mulNat d a b => [.mulNat (m_nr M c d) (m_nr M c a) (m_nr M c b), .jump (base + 8 * p + 8)]
  | .divNat d a b => [.divNat (m_nr M c d) (m_nr M c a) (m_nr M c b), .jump (base + 8 * p + 8)]
  | .modNat d a b => [.modNat (m_nr M c d) (m_nr M c a) (m_nr M c b), .jump (base + 8 * p + 8)]
  | .branchNat a b y n => [.branchNat (m_nr M c a) (m_nr M c b) (base + 8 * y) (base + 8 * n)]
  | .constant d v => [.constant (m_fr M c d) v, .jump (base + 8 * p + 8)]
  | .add d a b => [.add (m_fr M c d) (m_fr M c a) (m_fr M c b), .jump (base + 8 * p + 8)]
  | .sub d a b => [.sub (m_fr M c d) (m_fr M c a) (m_fr M c b), .jump (base + 8 * p + 8)]
  | .mul d a b => [.mul (m_fr M c d) (m_fr M c a) (m_fr M c b), .jump (base + 8 * p + 8)]
  | .inv d a => [.inv (m_fr M c d) (m_fr M c a), .jump (base + 8 * p + 8)]
  | .load d a => [.mulNat 11 (m_nr M c a) 2, .addNat 11 11 3, .load (m_fr M c d) 11,
      .jump (base + 8 * p + 8)]
  | .store a s => [.mulNat 11 (m_nr M c a) 2, .addNat 11 11 3, .store 11 (m_fr M c s),
      .jump (base + 8 * p + 8)]
  | .input d a => match md with
    | .pc => [.subNat 10 8 (m_nr M c a), .branchNat 10 0 (base + 8 * p + 4) (base + 8 * p + 2),
        .input (m_fr M c d) (m_nr M c a), .jump (base + 8 * p + 8),
        .constant (m_fr M c d) 0, .jump (base + 8 * p + 8)]
    | _ => [.subNat 10 4 (m_nr M c a), .branchNat 10 0 (base + 8 * p + 6) (base + 8 * p + 2),
        .addNat 11 5 (m_nr M c a), .mulNat 11 11 2, .load (m_fr M c d) 11,
        .jump (base + 8 * p + 8), .constant (m_fr M c d) 0, .jump (base + 8 * p + 8)]
  | .branch a b y n => [.branch (m_fr M c a) (m_fr M c b) (base + 8 * y) (base + 8 * n)]
  | .jump q => [.jump (base + 8 * q)]
  | .output s => match md with
    | .pc => [.store 6 (m_fr M c s), .addNat 6 6 2, .jump (base + 8 * p + 8)]
    | .fd => [.output (m_fr M c s), .jump (base + 8 * p + 8)]
    | .fc => [.input 1 7, .branch 1 (m_fr M c s) (base + 8 * p + 3) (base + 8 * p + 2),
        .addNat 9 1 0, .addNat 7 7 1, .jump (base + 8 * p + 8)]
  | .outputNat _ => [.jump (base + 8 * p + 8)]

def m_pad (l : List (Instruction F)) : List (Instruction F) :=
  l ++ List.replicate (8 - l.length) .halt

def m_blk (M c base exit : ℕ) (md : m_Mode) (p : ℕ) (ins : Instruction F) :
    List (Instruction F) :=
  m_pad (m_tr M c base exit md p ins)

theorem m_tr_length (M c base exit : ℕ) (md : m_Mode) (p : ℕ) (ins : Instruction F) :
    (m_tr M c base exit md p ins).length ≤ 8 := by
  cases ins <;> try cases md
  all_goals simp [m_tr]

theorem m_blk_length (M c base exit : ℕ) (md : m_Mode) (p : ℕ) (ins : Instruction F) :
    (m_blk M c base exit md p ins).length = 8 := by
  have := m_tr_length M c base exit md p ins
  simp only [m_blk, m_pad, List.length_append, List.length_replicate]
  omega

theorem m_blk_size (M c base exit : ℕ) (md : m_Mode) (p : ℕ) (ins : Instruction F) :
    programSize (m_blk M c base exit md p ins) ≤ 8 * instructionSize ins := by
  cases ins <;> try cases md
  all_goals (simp [m_blk, m_pad, m_tr, programSize, instructionSize]; try omega)

def m_nwr : m_Mode → ℕ → Prop
  | .pc, j => j = 6
  | .fd, _ => False
  | .fc, j => j = 7 ∨ j = 9

def m_fwr (M : ℕ) : m_Mode → ℕ → Prop
  | .pc, a => ∃ idx, a = idx * M
  | .fd, _ => False
  | .fc, a => a = 1

def m_outR (M : ℕ) (xs : List F) (w0 z w : MachineState F) : m_Mode → Prop
  | .pc => w.out = w0.out ∧ w.natReg 6 = z.out.length * M ∧
      ∀ idx < z.out.length, w.fieldReg (idx * M) = z.out.reverse.getD idx 0
  | .fd => w.out = z.out ++ w0.out
  | .fc => w.out = w0.out ∧ w.natReg 7 = w0.natReg 7 + z.out.length ∧
      (w.natReg 9 = 0 ↔ (w0.natReg 9 = 0 ∧
        ∀ t < z.out.length, z.out.reverse.getD t 0 = xs.getD (w0.natReg 7 + t) 0))

/-- The simulation relation between a sub-program state `z` and the composite state `w`. -/
structure m_Rn (M c B : ℕ) (md : m_Mode) (xs : List F) (w0 z w : MachineState F) : Prop where
  nat : ∀ j, w.natReg (m_nr M c j) = z.natReg j
  fld : ∀ j, w.fieldReg (m_fr M c j) = z.fieldReg j
  bnd : ∀ j, w.natReg j ≤ B
  nfr : ∀ j, j ≠ 10 → j ≠ 11 → ¬ m_nwr md j → (∀ a, j ≠ m_nr M c a) → w.natReg j = w0.natReg j
  ffr : ∀ a, (∀ j, a ≠ m_fr M c j) → ¬ m_fwr M md a → w.fieldReg a = w0.fieldReg a
  nout : w.natOut = w0.natOut
  out : m_outR M xs w0 z w md

def m_dataOK (M B : ℕ) (xsub : List F) (w0 : MachineState F) : Prop :=
  w0.natReg 4 ≤ B ∧ (w0.natReg 5 + w0.natReg 4) * M ≤ B ∧
  (∀ a < w0.natReg 4, w0.fieldReg ((w0.natReg 5 + a) * M) = xsub.getD a 0) ∧
  (∀ a, w0.natReg 4 ≤ a → xsub.getD a 0 = 0)

def m_inOK (M B Om : ℕ) (xs xsub : List F) (w0 : MachineState F) : m_Mode → Prop
  | .pc => w0.natReg 8 ≤ B ∧ (∀ a < w0.natReg 8, xs.getD a 0 = xsub.getD a 0) ∧
      (∀ a, w0.natReg 8 ≤ a → xsub.getD a 0 = 0) ∧ Om * M ≤ B
  | .fd => m_dataOK M B xsub w0
  | .fc => m_dataOK M B xsub w0 ∧ w0.natReg 7 + Om ≤ B

/-- Hypotheses on the start state of a sub-run. -/
structure m_Ctx (M c B Bs Om : ℕ) (md : m_Mode) (xs xsub : List F) (w0 : MachineState F) :
    Prop where
  hM : c < M
  hc : 2 ≤ c
  hB : Bs ≤ B
  hBa : (Bs + 1) * M ≤ B
  hB1 : 1 ≤ B
  r0 : w0.natReg 0 = 0
  r1 : w0.natReg 1 = 1
  rm : w0.natReg 2 = M
  rres : w0.natReg 3 = c
  inp : m_inOK M B Om xs xsub w0 md

theorem m_res {M c c' j j' : ℕ} (hc : c < M) (hc' : c' < M) (h : j * M + c = j' * M + c') :
    c = c' ∧ j = j' := by
  have h1 := congrArg (· % M) h
  simp only [    show ∀ x, (x * M + c) % M = c from fun x => by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc],
    show ∀ x, (x * M + c') % M = c' from fun x => by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc']] at h1
  subst h1
  refine ⟨rfl, ?_⟩
  have : j * M = j' * M := by omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) this

theorem m_nr_inj {M c j d : ℕ} (hc : c < M) : m_nr M c j = m_nr M c d ↔ j = d := by
  constructor
  · intro h; unfold m_nr at h; exact (m_res hc hc (by omega : j * M + c = d * M + c)).2
  · rintro rfl; rfl

theorem m_fr_inj {M c j d : ℕ} (hc : c < M) : m_fr M c j = m_fr M c d ↔ j = d := by
  constructor
  · intro h; exact (m_res hc hc h).2
  · rintro rfl; rfl

theorem m_nr_ge (M c j : ℕ) : 13 ≤ m_nr M c j := by unfold m_nr; omega

theorem m_fr_ne_data {M c j idx : ℕ} (hc : c < M) (hc2 : 2 ≤ c) : m_fr M c j ≠ idx * M := by
  intro h
  have := (m_res hc (by omega : 0 < M) (by simpa [m_fr] using h)).1
  omega

theorem m_fr_ne_one {M c j : ℕ} (hc : c < M) (hc2 : 2 ≤ c) : m_fr M c j ≠ 1 := by
  intro h
  unfold m_fr at h
  rcases j with _ | j
  · omega
  · have : M ≤ (j + 1) * M := Nat.le_mul_of_pos_left M (by omega)
    omega

/-! ### Part LTGMachine3 -/
theorem m_outR_congr {M : ℕ} {xs : List F} {w0 z w w' : MachineState F} {md : m_Mode}
    (h : m_outR M xs w0 z w md) (ho : w'.out = w.out) (h6 : w'.natReg 6 = w.natReg 6)
    (h7 : w'.natReg 7 = w.natReg 7) (h9 : w'.natReg 9 = w.natReg 9)
    (hf : ∀ idx, w'.fieldReg (idx * M) = w.fieldReg (idx * M)) : m_outR M xs w0 z w' md := by
  cases md <;> simp only [m_outR] at h ⊢
  · exact ⟨ho.trans h.1, h6.trans h.2.1, fun idx hi => (hf idx).trans (h.2.2 idx hi)⟩
  · exact ho.trans h
  · exact ⟨ho.trans h.1, h7.trans h.2.1, by rw [h9]; exact h.2.2⟩

theorem m_Rn_tmp {M c B : ℕ} {md : m_Mode} {xs : List F} {w0 z w w' : MachineState F}
    (hR : m_Rn M c B md xs w0 z w) {j v : ℕ} (hj : j = 10 ∨ j = 11) (hv : v ≤ B)
    (hn : w'.natReg = Function.update w.natReg j v) (hf : w'.fieldReg = w.fieldReg)
    (ho : w'.out = w.out) (hno : w'.natOut = w.natOut) : m_Rn M c B md xs w0 z w' := by
  have hne : ∀ a, m_nr M c a ≠ j := fun a h => by have := m_nr_ge M c a; omega
  refine ⟨fun a => ?_, fun a => ?_, fun i => ?_, fun i h1 h2 h3 h4 => ?_, fun a h1 h2 => ?_,
    hno.trans hR.nout, m_outR_congr hR.out ho ?_ ?_ ?_ (fun idx => by rw [hf])⟩
  · rw [hn, Function.update_of_ne (hne a)]; exact hR.nat a
  · rw [hf]; exact hR.fld a
  · rw [hn, Function.update_apply]; split_ifs
    · exact hv
    · exact hR.bnd i
  · rw [hn, Function.update_of_ne (by omega)]; exact hR.nfr i h1 h2 h3 h4
  · rw [hf]; exact hR.ffr a h1 h2
  all_goals rw [hn, Function.update_of_ne (by omega)]

theorem m_Rn_natw {M c B : ℕ} {md : m_Mode} {xs : List F} {w0 z w z' w' : MachineState F}
    (hR : m_Rn M c B md xs w0 z w) (hM : c < M) {d v : ℕ} (hv : v ≤ B)
    (hzn : z'.natReg = Function.update z.natReg d v) (hzf : z'.fieldReg = z.fieldReg)
    (hzo : z'.out = z.out)
    (hn : w'.natReg = Function.update w.natReg (m_nr M c d) v) (hf : w'.fieldReg = w.fieldReg)
    (ho : w'.out = w.out) (hno : w'.natOut = w.natOut) : m_Rn M c B md xs w0 z' w' := by
  have hge := m_nr_ge M c d
  refine ⟨fun a => ?_, fun a => ?_, fun i => ?_, fun i h1 h2 h3 h4 => ?_, fun a h1 h2 => ?_,
    hno.trans hR.nout, ?_⟩
  · rw [hn, hzn]
    by_cases had : a = d
    · subst had; simp
    · rw [Function.update_of_ne had, Function.update_of_ne (mt (m_nr_inj hM).mp had)]
      exact hR.nat a
  · rw [hf, hzf]; exact hR.fld a
  · rw [hn, Function.update_apply]; split_ifs
    · exact hv
    · exact hR.bnd i
  · rw [hn, Function.update_of_ne (h4 d)]; exact hR.nfr i h1 h2 h3 h4
  · rw [hf]; exact hR.ffr a h1 h2
  · have h := m_outR_congr (w' := w') hR.out ho (by rw [hn, Function.update_of_ne (by omega)])
      (by rw [hn, Function.update_of_ne (by omega)]) (by rw [hn, Function.update_of_ne (by omega)])
      (fun idx => by rw [hf])
    cases md <;> simp only [m_outR, hzo] at h ⊢ <;> exact h

theorem m_Rn_fldw {M c B : ℕ} {md : m_Mode} {xs : List F} {w0 z w z' w' : MachineState F}
    (hR : m_Rn M c B md xs w0 z w) (hM : c < M) (hc2 : 2 ≤ c) {d : ℕ} {v : F}
    (hzn : z'.natReg = z.natReg) (hzf : z'.fieldReg = Function.update z.fieldReg d v)
    (hzo : z'.out = z.out)
    (hn : w'.natReg = w.natReg) (hf : w'.fieldReg = Function.update w.fieldReg (m_fr M c d) v)
    (ho : w'.out = w.out) (hno : w'.natOut = w.natOut) : m_Rn M c B md xs w0 z' w' := by
  refine ⟨fun a => ?_, fun a => ?_, fun i => ?_, fun i h1 h2 h3 h4 => ?_, fun a h1 h2 => ?_,
    hno.trans hR.nout, ?_⟩
  · rw [hn, hzn]; exact hR.nat a
  · rw [hf, hzf]
    by_cases had : a = d
    · subst had; simp
    · rw [Function.update_of_ne had, Function.update_of_ne (mt (m_fr_inj hM).mp had)]
      exact hR.fld a
  · rw [hn]; exact hR.bnd i
  · rw [hn]; exact hR.nfr i h1 h2 h3 h4
  · rw [hf, Function.update_of_ne (h1 d)]; exact hR.ffr a h1 h2
  · have h := m_outR_congr (w' := w') hR.out ho (by rw [hn]) (by rw [hn]) (by rw [hn])
      (fun idx => by rw [hf, Function.update_of_ne (m_fr_ne_data hM hc2).symm])
    cases md <;> simp only [m_outR, hzo] at h ⊢ <;> exact h

theorem m_Rn_same {M c B : ℕ} {md : m_Mode} {xs : List F} {w0 z w z' w' : MachineState F}
    (hR : m_Rn M c B md xs w0 z w)
    (hzn : z'.natReg = z.natReg) (hzf : z'.fieldReg = z.fieldReg) (hzo : z'.out = z.out)
    (hn : w'.natReg = w.natReg) (hf : w'.fieldReg = w.fieldReg)
    (ho : w'.out = w.out) (hno : w'.natOut = w.natOut) : m_Rn M c B md xs w0 z' w' := by
  refine ⟨fun a => ?_, fun a => ?_, fun i => ?_, fun i h1 h2 h3 h4 => ?_, fun a h1 h2 => ?_,
    hno.trans hR.nout, ?_⟩
  · rw [hn, hzn]; exact hR.nat a
  · rw [hf, hzf]; exact hR.fld a
  · rw [hn]; exact hR.bnd i
  · rw [hn]; exact hR.nfr i h1 h2 h3 h4
  · rw [hf]; exact hR.ffr a h1 h2
  · have h := m_outR_congr (w' := w') hR.out ho (by rw [hn]) (by rw [hn]) (by rw [hn])
      (fun idx => by rw [hf])
    cases md <;> simp only [m_outR, hzo] at h ⊢ <;> exact h

/-- Composite registers below 13, other than temporaries and the mode's own, are frozen. -/
theorem m_Rn_reg {M c B : ℕ} {md : m_Mode} {xs : List F} {w0 z w : MachineState F}
    (hR : m_Rn M c B md xs w0 z w) {j : ℕ} (hj : j < 13) (h10 : j ≠ 10) (h11 : j ≠ 11)
    (hw : ¬ m_nwr md j) : w.natReg j = w0.natReg j :=
  hR.nfr j h10 h11 hw (fun a h => by have := m_nr_ge M c a; omega)

theorem m_code {Q : Program F} {bp : ℕ} {l : List (Instruction F)}
    (hc : ∀ r < 8, Q[bp + r]? = (m_pad l)[r]?) (hl : l.length ≤ 8) (r : ℕ) (hr : r < l.length) :
    Q[bp + r]? = l[r]? := by
  rw [hc r (by omega)]; simp [m_pad, List.getElem?_append_left hr]

/-! ### Part LTGMachine4 -/
@[simp] theorem m_nr_eq_lit {M c a k : ℕ} (hk : k < 13) : (m_nr M c a = k) = False := by
  have := m_nr_ge M c a; simp only [eq_iff_iff, iff_false]; omega

theorem m_nfwr {M : ℕ} {md : m_Mode} (hM3 : 3 ≤ M) (hmd : md ≠ .pc) (idx : ℕ) :
    ¬ m_fwr M md (idx * M) := by
  cases md
  · exact absurd rfl hmd
  · simp [m_fwr]
  · simp only [m_fwr]
    intro h
    rcases idx with _ | idx
    · simp at h
    · have : M ≤ (idx + 1) * M := Nat.le_mul_of_pos_left M (by omega)
      omega

theorem m_forall_rev (v : F) (l : List F) (g : ℕ → F) :
    (∀ t < (v :: l).length, (v :: l).reverse.getD t 0 = g t) ↔
      (∀ t < l.length, l.reverse.getD t 0 = g t) ∧ v = g l.length := by
  have h1 : ∀ t < l.length, (v :: l).reverse.getD t 0 = l.reverse.getD t 0 := by
    intro t ht
    rw [List.reverse_cons, List.getD_append _ _ _ _ (by simpa using ht)]
  have h2 : (v :: l).reverse.getD l.length 0 = v := by
    rw [List.reverse_cons, List.getD_append_right _ _ _ _ (by simp)]; simp
  constructor
  · intro h
    refine ⟨fun t ht => (h1 t ht).symm.trans (h t (by simp; omega)), ?_⟩
    rw [← h2]; exact h _ (by simp)
  · rintro ⟨h, hv⟩ t ht
    simp only [List.length_cons] at ht
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
    · rw [h1 t ht]; exact h t ht
    · rw [h2]; exact hv

theorem m_eff_branch_pos {xs : List F} {z : MachineState F} {a b y n : ℕ}
    (h : z.fieldReg a = z.fieldReg b) : m_eff xs z (.branch a b y n) = {z with pc := y} := by
  simp [m_eff, h]

theorem m_eff_branch_neg {xs : List F} {z : MachineState F} {a b y n : ℕ}
    (h : ¬ z.fieldReg a = z.fieldReg b) : m_eff xs z (.branch a b y n) = {z with pc := n} := by
  simp [m_eff, h]

theorem m_bnd_upd {f : ℕ → ℕ} {B j v : ℕ} (hb : ∀ i, f i ≤ B) (hv : v ≤ B) :
    ∀ i, Function.update f j v i ≤ B := by
  intro i; rw [Function.update_apply]; split_ifs
  · exact hv
  · exact hb i

theorem m_two {Q : Program F} {xs : List F} {B bp bp1 q : ℕ} {w : MachineState F}
    {X : Instruction F}
    (hb : ∀ i, w.natReg i ≤ B) (hpc : w.pc = bp) (c0 : Q[bp]? = some X) (hX : X ≠ .halt)
    (hb1 : ∀ i, (m_eff xs w X).natReg i ≤ B) (hpc1 : (m_eff xs w X).pc = bp1)
    (c1 : Q[bp1]? = some (.jump q)) :
    m_reach Q xs B 2 w {m_eff xs w X with pc := q} :=
  m_reach.succ X hb (hpc ▸ c0) hX
    (m_reach.succ (.jump q) hb1 (hpc1 ▸ c1) (by simp) (m_reach.zero _))

theorem m_one {Q : Program F} {xs : List F} {B bp : ℕ} {w : MachineState F} {X : Instruction F}
    (hb : ∀ i, w.natReg i ≤ B) (hpc : w.pc = bp) (c0 : Q[bp]? = some X) (hX : X ≠ .halt) :
    m_reach Q xs B 1 w (m_eff xs w X) :=
  m_reach.succ X hb (hpc ▸ c0) hX (m_reach.zero _)

/-- One translated sub-step. -/
theorem m_blk_sim {M c B Bs Om : ℕ} {md : m_Mode} {xs xsub : List F} {w0 : MachineState F}
    (hX : m_Ctx M c B Bs Om md xs xsub w0) {Q : Program F} {base exit : ℕ}
    {z w : MachineState F} {ins : Instruction F} (hins : ins ≠ .halt)
    (hc : ∀ r < 8, Q[base + 8 * z.pc + r]? = (m_blk M c base exit md z.pc ins)[r]?)
    (hpc : w.pc = base + 8 * z.pc)
    (hz : ∀ i, z.natReg i ≤ Bs) (hz1 : ∀ i, (m_eff xsub z ins).natReg i ≤ Bs)
    (hO : (m_eff xsub z ins).out.length ≤ Om)
    (hR : m_Rn M c B md xs w0 z w) :
    ∃ n w', n ≤ 8 ∧ m_reach Q xs B n w w' ∧ w'.pc = base + 8 * (m_eff xsub z ins).pc ∧
      m_Rn M c B md xs w0 (m_eff xsub z ins) w' := by
  have hM := hX.hM
  have hc2 := hX.hc
  have hl := m_tr_length (F := F) M c base exit md z.pc ins
  have hc' := m_code hc hl
  have hBs : ∀ i, z.natReg i ≤ B := fun i => (hz i).trans hX.hB
  have hreg : ∀ j, j < 13 → j ≠ 10 → j ≠ 11 → ¬ m_nwr md j → w.natReg j = w0.natReg j :=
    fun j h1 h2 h3 h4 => m_Rn_reg hR h1 h2 h3 h4
  have r0 : w.natReg 0 = 0 :=
    (hreg 0 (by norm_num) (by norm_num) (by norm_num) (by cases md <;> simp [m_nwr])).trans hX.r0
  have r1 : w.natReg 1 = 1 :=
    (hreg 1 (by norm_num) (by norm_num) (by norm_num) (by cases md <;> simp [m_nwr])).trans hX.r1
  have rm : w.natReg 2 = M :=
    (hreg 2 (by norm_num) (by norm_num) (by norm_num) (by cases md <;> simp [m_nwr])).trans hX.rm
  have rres : w.natReg 3 = c :=
    (hreg 3 (by norm_num) (by norm_num) (by norm_num) (by cases md <;> simp [m_nwr])).trans hX.rres
  have hM3 : 3 ≤ M := by omega
  cases ins with
  | halt => exact absurd rfl hins
  | literal d v =>
    have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
    simp [m_tr] at c0 c1
    have hv : v ≤ B := by have := hz1 d; simp only [m_eff, Function.update_self] at this; exact this.trans hX.hB
    refine ⟨2, _, by norm_num, m_two hR.bnd hpc c0 (by simp) (m_bnd_upd hR.bnd hv)
      (by simp [m_eff, hpc]) c1, by simp [m_eff] <;> omega, ?_⟩
    exact m_Rn_natw hR hM hv rfl rfl rfl rfl rfl rfl rfl
  | addNat d a b =>
    have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
    simp [m_tr] at c0 c1
    have hv : z.natReg a + z.natReg b ≤ B := by
      have := hz1 d; simp only [m_eff, Function.update_self] at this; exact this.trans hX.hB
    refine ⟨2, _, by norm_num, m_two hR.bnd hpc c0 (by simp) ?_
      (by simp [m_eff, hpc]) c1, by simp [m_eff] <;> omega, ?_⟩
    · simp only [m_eff, hR.nat]; exact m_bnd_upd hR.bnd hv
    · exact m_Rn_natw hR hM hv rfl rfl rfl (by simp [m_eff, hR.nat]) rfl rfl rfl
  | subNat d a b =>
    have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
    simp [m_tr] at c0 c1
    have hv : z.natReg a - z.natReg b ≤ B := by
      have := hz1 d; simp only [m_eff, Function.update_self] at this; exact this.trans hX.hB
    refine ⟨2, _, by norm_num, m_two hR.bnd hpc c0 (by simp) ?_
      (by simp [m_eff, hpc]) c1, by simp [m_eff] <;> omega, ?_⟩
    · simp only [m_eff, hR.nat]; exact m_bnd_upd hR.bnd hv
    · exact m_Rn_natw hR hM hv rfl rfl rfl (by simp [m_eff, hR.nat]) rfl rfl rfl
  | mulNat d a b =>
    have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
    simp [m_tr] at c0 c1
    have hv : z.natReg a * z.natReg b ≤ B := by
      have := hz1 d; simp only [m_eff, Function.update_self] at this; exact this.trans hX.hB
    refine ⟨2, _, by norm_num, m_two hR.bnd hpc c0 (by simp) ?_
      (by simp [m_eff, hpc]) c1, by simp [m_eff] <;> omega, ?_⟩
    · simp only [m_eff, hR.nat]; exact m_bnd_upd hR.bnd hv
    · exact m_Rn_natw hR hM hv rfl rfl rfl (by simp [m_eff, hR.nat]) rfl rfl rfl
  | divNat d a b =>
    have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
    simp [m_tr] at c0 c1
    have hv : z.natReg a / z.natReg b ≤ B := by
      have := hz1 d; simp only [m_eff, Function.update_self] at this; exact this.trans hX.hB
    refine ⟨2, _, by norm_num, m_two hR.bnd hpc c0 (by simp) ?_
      (by simp [m_eff, hpc]) c1, by simp [m_eff] <;> omega, ?_⟩
    · simp only [m_eff, hR.nat]; exact m_bnd_upd hR.bnd hv
    · exact m_Rn_natw hR hM hv rfl rfl rfl (by simp [m_eff, hR.nat]) rfl rfl rfl
  | modNat d a b =>
    have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
    simp [m_tr] at c0 c1
    have hv : z.natReg a % z.natReg b ≤ B := by
      have := hz1 d; simp only [m_eff, Function.update_self] at this; exact this.trans hX.hB
    refine ⟨2, _, by norm_num, m_two hR.bnd hpc c0 (by simp) ?_
      (by simp [m_eff, hpc]) c1, by simp [m_eff] <;> omega, ?_⟩
    · simp only [m_eff, hR.nat]; exact m_bnd_upd hR.bnd hv
    · exact m_Rn_natw hR hM hv rfl rfl rfl (by simp [m_eff, hR.nat]) rfl rfl rfl
  | inputNat d i =>
    have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
    simp [m_tr] at c0 c1
    refine ⟨2, _, by norm_num, m_two hR.bnd hpc c0 (by simp) ?_
      (by simp [m_eff, hpc]) c1, by simp [m_eff] <;> omega, ?_⟩
    · simp only [m_eff, Nat.sub_self]; exact m_bnd_upd hR.bnd (Nat.zero_le _)
    · exact m_Rn_natw hR hM (Nat.zero_le B) rfl rfl rfl (by simp [m_eff]) rfl rfl rfl
  | branchNat a b y n =>
    have c0 := hc' 0 (by simp [m_tr])
    simp [m_tr] at c0
    refine ⟨1, _, by norm_num, m_one hR.bnd hpc c0 (by simp), ?_, ?_⟩
    · simp only [m_eff, hR.nat]; split_ifs <;> rfl
    · exact m_Rn_same hR rfl rfl rfl rfl rfl rfl rfl
  | branch a b y n =>
    have c0 := hc' 0 (by simp [m_tr])
    simp [m_tr] at c0
    refine ⟨1, _, by norm_num, m_one hR.bnd hpc c0 (by simp), ?_, ?_⟩
    · have h' : (w.fieldReg (m_fr M c a) = w.fieldReg (m_fr M c b)) ↔
          (z.fieldReg a = z.fieldReg b) := by rw [hR.fld, hR.fld]
      simp only [m_eff]; split_ifs <;> first | rfl | (exfalso; tauto)
    · exact m_Rn_same hR rfl rfl rfl rfl rfl rfl rfl
  | jump q =>
    have c0 := hc' 0 (by simp [m_tr])
    simp [m_tr] at c0
    exact ⟨1, _, by norm_num, m_one hR.bnd hpc c0 (by simp), rfl,
      m_Rn_same hR rfl rfl rfl rfl rfl rfl rfl⟩
  | outputNat q =>
    have c0 := hc' 0 (by simp [m_tr])
    simp [m_tr] at c0
    exact ⟨1, _, by norm_num, m_one hR.bnd hpc c0 (by simp), by simp [m_eff]; omega,
      m_Rn_same hR rfl rfl rfl rfl rfl rfl rfl⟩
  | constant d v =>
    have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
    simp [m_tr] at c0 c1
    refine ⟨2, _, by norm_num, m_two hR.bnd hpc c0 (by simp) (by simpa [m_eff] using hR.bnd)
      (by simp [m_eff, hpc]) c1, by simp [m_eff] <;> omega, ?_⟩
    exact m_Rn_fldw hR hM hc2 rfl rfl rfl rfl rfl rfl rfl
  | add d a b =>
    have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
    simp [m_tr] at c0 c1
    refine ⟨2, _, by norm_num, m_two hR.bnd hpc c0 (by simp) (by simpa [m_eff] using hR.bnd)
      (by simp [m_eff, hpc]) c1, by simp [m_eff] <;> omega, ?_⟩
    exact m_Rn_fldw hR hM hc2 rfl rfl rfl rfl (by simp [m_eff, hR.fld]) rfl rfl
  | sub d a b =>
    have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
    simp [m_tr] at c0 c1
    refine ⟨2, _, by norm_num, m_two hR.bnd hpc c0 (by simp) (by simpa [m_eff] using hR.bnd)
      (by simp [m_eff, hpc]) c1, by simp [m_eff] <;> omega, ?_⟩
    exact m_Rn_fldw hR hM hc2 rfl rfl rfl rfl (by simp [m_eff, hR.fld]) rfl rfl
  | mul d a b =>
    have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
    simp [m_tr] at c0 c1
    refine ⟨2, _, by norm_num, m_two hR.bnd hpc c0 (by simp) (by simpa [m_eff] using hR.bnd)
      (by simp [m_eff, hpc]) c1, by simp [m_eff] <;> omega, ?_⟩
    exact m_Rn_fldw hR hM hc2 rfl rfl rfl rfl (by simp [m_eff, hR.fld]) rfl rfl
  | inv d a =>
    have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
    simp [m_tr] at c0 c1
    refine ⟨2, _, by norm_num, m_two hR.bnd hpc c0 (by simp) (by simpa [m_eff] using hR.bnd)
      (by simp [m_eff, hpc]) c1, by simp [m_eff] <;> omega, ?_⟩
    exact m_Rn_fldw hR hM hc2 rfl rfl rfl rfl (by simp [m_eff, hR.fld]) rfl rfl
  | load d a =>
    have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
    have c2 := hc' 2 (by simp [m_tr]); have c3 := hc' 3 (by simp [m_tr])
    simp [m_tr] at c0 c1 c2 c3
    have hA : z.natReg a * M + c ≤ B := by
      have h1 := hX.hBa; have h2 := Nat.mul_le_mul_right M (hz a)
      have : (Bs + 1) * M = Bs * M + M := by ring
      omega
    have hA' : z.natReg a * M ≤ B := le_trans (Nat.le_add_right _ _) hA
    have hfa : w.fieldReg (z.natReg a * M + c) = z.fieldReg (z.natReg a) := hR.fld _
    have hRt := m_Rn_tmp hR
      (w' := {w with natReg := Function.update w.natReg 11 (z.natReg a * M + c)})
      (Or.inr rfl) hA rfl rfl rfl rfl
    refine ⟨4, _, by norm_num, m_reach.succ _ hR.bnd (hpc ▸ c0) (by simp)
      (m_reach.succ (.addNat 11 11 3) ?_ ?_ (by simp) (m_two ?_ ?_ c2 (by simp) ?_ ?_ c3)), ?_, ?_⟩
    · simp only [m_eff, hR.nat, rm]; exact m_bnd_upd hR.bnd hA'
    · simp only [m_eff, hpc]; exact c1
    · simp [m_eff, hR.nat, rm, rres]; exact m_bnd_upd hR.bnd hA
    · simp [m_eff, hpc] <;> omega
    · simp [m_eff, hR.nat, rm, rres]; exact m_bnd_upd hR.bnd hA
    · simp [m_eff, hpc] <;> omega
    · simp [m_eff]; omega
    · exact m_Rn_fldw hRt hM hc2 rfl rfl rfl (by simp [m_eff, hR.nat, rm, rres])
        (by simp [m_eff, hR.nat, rm, rres, hfa]) rfl rfl
  | store a s =>
    have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
    have c2 := hc' 2 (by simp [m_tr]); have c3 := hc' 3 (by simp [m_tr])
    simp [m_tr] at c0 c1 c2 c3
    have hA : z.natReg a * M + c ≤ B := by
      have h1 := hX.hBa; have h2 := Nat.mul_le_mul_right M (hz a)
      have : (Bs + 1) * M = Bs * M + M := by ring
      omega
    have hA' : z.natReg a * M ≤ B := le_trans (Nat.le_add_right _ _) hA
    have hRt := m_Rn_tmp hR
      (w' := {w with natReg := Function.update w.natReg 11 (z.natReg a * M + c)})
      (Or.inr rfl) hA rfl rfl rfl rfl
    refine ⟨4, _, by norm_num, m_reach.succ _ hR.bnd (hpc ▸ c0) (by simp)
      (m_reach.succ (.addNat 11 11 3) ?_ ?_ (by simp) (m_two ?_ ?_ c2 (by simp) ?_ ?_ c3)), ?_, ?_⟩
    · simp only [m_eff, hR.nat, rm]; exact m_bnd_upd hR.bnd hA'
    · simp only [m_eff, hpc]; exact c1
    · simp [m_eff, hR.nat, rm, rres]; exact m_bnd_upd hR.bnd hA
    · simp [m_eff, hpc] <;> omega
    · simp [m_eff, hR.nat, rm, rres]; exact m_bnd_upd hR.bnd hA
    · simp [m_eff, hpc] <;> omega
    · simp [m_eff]; omega
    · refine m_Rn_fldw hRt hM hc2 (d := z.natReg a) rfl rfl rfl
        (by simp [m_eff, hR.nat, rm, rres]) ?_ rfl rfl
      simp [m_eff, hR.nat, rm, rres, hR.fld]; rfl
  | input d a =>
    cases md
    case pc =>
      have hinp := hX.inp
      simp only [m_inOK] at hinp
      obtain ⟨hK, hxs, hx0, -⟩ := hinp
      have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
      have c2 := hc' 2 (by simp [m_tr]); have c3 := hc' 3 (by simp [m_tr])
      have c4 := hc' 4 (by simp [m_tr]); have c5 := hc' 5 (by simp [m_tr])
      simp [m_tr] at c0 c1 c2 c3 c4 c5
      have rK : w.natReg 8 = w0.natReg 8 :=
        hreg 8 (by norm_num) (by norm_num) (by norm_num) (by simp [m_nwr])
      have hT : w0.natReg 8 - z.natReg a ≤ B := le_trans (Nat.sub_le _ _) hK
      have hRt := m_Rn_tmp hR
        (w' := {w with natReg := Function.update w.natReg 10 (w0.natReg 8 - z.natReg a)})
        (Or.inl rfl) hT rfl rfl rfl rfl
      have hb1 : ∀ i, (m_eff xs w (.subNat 10 8 (m_nr M c a))).natReg i ≤ B := by
        simp only [m_eff, hR.nat, rK]; exact m_bnd_upd hR.bnd hT
      by_cases hlt : z.natReg a < w0.natReg 8
      · refine ⟨4, _, by norm_num, m_reach.succ _ hR.bnd (hpc ▸ c0) (by simp)
          (m_reach.succ (.branchNat 10 0 (base + 8 * z.pc + 4) (base + 8 * z.pc + 2)) hb1
            (by simpa [m_eff, hpc] using c1) (by simp)
            (m_two ?_ ?_ c2 (by simp) ?_ ?_ c3)), ?_, ?_⟩
        · simpa [m_eff] using hb1
        · simp [m_eff, hpc, hR.nat, rK, r0] <;> omega
        · simpa [m_eff] using hb1
        · simp [m_eff, hpc, hR.nat, rK, r0] <;> omega
        · simp [m_eff]; omega
        · exact m_Rn_fldw hRt hM hc2 rfl rfl rfl (by simp [m_eff, hR.nat, rK])
            (by have := hxs _ hlt; simp at this; simp [m_eff, hR.nat, this]) rfl rfl
      · refine ⟨4, _, by norm_num, m_reach.succ _ hR.bnd (hpc ▸ c0) (by simp)
          (m_reach.succ (.branchNat 10 0 (base + 8 * z.pc + 4) (base + 8 * z.pc + 2)) hb1
            (by simpa [m_eff, hpc] using c1) (by simp)
            (m_two ?_ ?_ c4 (by simp) ?_ ?_ c5)), ?_, ?_⟩
        · simpa [m_eff] using hb1
        · simp [m_eff, hpc, hR.nat, rK, r0] <;> omega
        · simpa [m_eff] using hb1
        · simp [m_eff, hpc, hR.nat, rK, r0] <;> omega
        · simp [m_eff]; omega
        · exact m_Rn_fldw hRt hM hc2 rfl rfl rfl (by simp [m_eff, hR.nat, rK])
            (by have := hx0 _ (not_lt.mp hlt); simp at this; simp [m_eff, hR.nat, this]) rfl rfl
    all_goals
      have hdata : m_dataOK M B xsub w0 := by first | exact hX.inp | exact hX.inp.1
      obtain ⟨hS, hIS, hdat, hd0⟩ := hdata
      have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
      have c2 := hc' 2 (by simp [m_tr]); have c3 := hc' 3 (by simp [m_tr])
      have c4 := hc' 4 (by simp [m_tr]); have c5 := hc' 5 (by simp [m_tr])
      have c6 := hc' 6 (by simp [m_tr]); have c7 := hc' 7 (by simp [m_tr])
      simp [m_tr] at c0 c1 c2 c3 c4 c5 c6 c7
      have rS : w.natReg 4 = w0.natReg 4 :=
        hreg 4 (by norm_num) (by norm_num) (by norm_num) (by simp [m_nwr])
      have r5 : w.natReg 5 = w0.natReg 5 :=
        hreg 5 (by norm_num) (by norm_num) (by norm_num) (by simp [m_nwr])
      have hT : w0.natReg 4 - z.natReg a ≤ B := le_trans (Nat.sub_le _ _) hS
      have hRt := m_Rn_tmp hR
        (w' := {w with natReg := Function.update w.natReg 10 (w0.natReg 4 - z.natReg a)})
        (Or.inl rfl) hT rfl rfl rfl rfl
      have hb1 : ∀ i, (m_eff xs w (.subNat 10 4 (m_nr M c a))).natReg i ≤ B := by
        simp only [m_eff, hR.nat, rS]; exact m_bnd_upd hR.bnd hT
      by_cases hlt : z.natReg a < w0.natReg 4
      · have hA : (w0.natReg 5 + z.natReg a) * M ≤ B :=
          le_trans (Nat.mul_le_mul_right _ (by omega)) hIS
        have hA' : w0.natReg 5 + z.natReg a ≤ B :=
          le_trans (Nat.le_mul_of_pos_right _ (by omega)) hA
        have hRt2 := m_Rn_tmp hRt
          (w' := {w with natReg := Function.update (Function.update w.natReg 10
            (w0.natReg 4 - z.natReg a)) 11 ((w0.natReg 5 + z.natReg a) * M)})
          (Or.inr rfl) hA rfl rfl rfl rfl
        have hfa : w.fieldReg ((w0.natReg 5 + z.natReg a) * M) = xsub.getD (z.natReg a) 0 := by
          rw [hR.ffr _ (fun j => (m_fr_ne_data hM hc2).symm) (m_nfwr hM3 (by simp) _)]
          exact hdat _ hlt
        simp at hfa
        refine ⟨6, _, by norm_num, m_reach.succ _ hR.bnd (hpc ▸ c0) (by simp)
          (m_reach.succ (.branchNat 10 0 (base + 8 * z.pc + 6) (base + 8 * z.pc + 2)) hb1
            (by simpa [m_eff, hpc] using c1) (by simp)
          (m_reach.succ (.addNat 11 5 (m_nr M c a)) ?_ ?_ (by simp)
          (m_reach.succ (.mulNat 11 11 2) ?_ ?_ (by simp)
          (m_two ?_ ?_ c4 (by simp) ?_ ?_ c5)))), ?_, ?_⟩
        · simpa [m_eff] using hb1
        · simp [m_eff, hpc, hR.nat, rS, r0]; rw [if_neg (by omega)]; exact c2
        · simp [m_eff, hR.nat, rS, r5]; exact m_bnd_upd (m_bnd_upd hR.bnd hT) hA'
        · simp [m_eff, hpc, hR.nat, rS, r0]; rw [if_neg (by omega)]; exact c3
        · simp [m_eff, hR.nat, rS, r5, rm]
          exact m_bnd_upd (m_bnd_upd hR.bnd hT) hA
        · simp [m_eff, hpc, hR.nat, rS, r0]; omega
        · simp [m_eff, hR.nat, rS, r5, rm]
          exact m_bnd_upd (m_bnd_upd hR.bnd hT) hA
        · simp [m_eff, hpc, hR.nat, rS, r0]; omega
        · simp [m_eff]; omega
        · exact m_Rn_fldw hRt2 hM hc2 rfl rfl rfl (by simp [m_eff, hR.nat, rS, r5, rm])
            (by simp [m_eff, hR.nat, rS, r5, rm, hfa]) rfl rfl
      · refine ⟨4, _, by norm_num, m_reach.succ _ hR.bnd (hpc ▸ c0) (by simp)
          (m_reach.succ (.branchNat 10 0 (base + 8 * z.pc + 6) (base + 8 * z.pc + 2)) hb1
            (by simpa [m_eff, hpc] using c1) (by simp)
            (m_two ?_ ?_ c6 (by simp) ?_ ?_ c7)), ?_, ?_⟩
        · simpa [m_eff] using hb1
        · simp [m_eff, hpc, hR.nat, rS, r0] <;> omega
        · simpa [m_eff] using hb1
        · simp [m_eff, hpc, hR.nat, rS, r0] <;> omega
        · simp [m_eff]; omega
        · exact m_Rn_fldw hRt hM hc2 rfl rfl rfl (by simp [m_eff, hR.nat, rS])
            (by have := hd0 _ (not_lt.mp hlt); simp at this; simp [m_eff, hR.nat, this]) rfl rfl
  | output s =>
    have hO' : z.out.length + 1 ≤ Om := by simpa [m_eff] using hO
    cases md
    case pc =>
      have hinp := hX.inp
      simp only [m_inOK] at hinp
      obtain ⟨-, -, -, hOm⟩ := hinp
      have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
      have c2 := hc' 2 (by simp [m_tr])
      simp [m_tr] at c0 c1 c2
      have hout := hR.out
      simp only [m_outR] at hout
      obtain ⟨ho1, ho2, ho3⟩ := hout
      have hDA : z.out.length * M + M ≤ B := by
        have := le_trans (Nat.mul_le_mul_right M hO') hOm
        have e : (z.out.length + 1) * M = z.out.length * M + M := by ring
        omega
      refine ⟨3, _, by norm_num, m_reach.succ _ hR.bnd (hpc ▸ c0) (by simp)
        (m_two ?_ ?_ c1 (by simp) ?_ ?_ c2), ?_, ?_⟩
      · simpa [m_eff] using hR.bnd
      · simp [m_eff, hpc]
      · simp [m_eff, ho2, rm]; exact m_bnd_upd hR.bnd hDA
      · simp [m_eff, hpc] <;> omega
      · simp [m_eff] <;> omega
      · have hne : ∀ j, m_fr M c j ≠ z.out.length * M := fun j => m_fr_ne_data hM hc2
        refine ⟨fun j => ?_, fun j => ?_, ?_, fun i h1 h2 h3 h4 => ?_, fun a h1 h2 => ?_,
          hR.nout, ?_⟩
        · simp [m_eff]; exact hR.nat j
        · simp only [m_eff, ho2]; rw [Function.update_of_ne (hne j)]; exact hR.fld j
        · simp [m_eff, ho2, rm]; exact m_bnd_upd hR.bnd hDA
        · simp only [m_nwr] at h3
          simp only [m_eff]; rw [Function.update_of_ne h3]; exact hR.nfr i h1 h2 (by simpa [m_nwr]) h4
        · simp only [m_fwr, not_exists] at h2
          simp only [m_eff, ho2]; rw [Function.update_of_ne (h2 _)]; exact hR.ffr a h1 (by simpa [m_fwr])
        · simp only [m_outR, m_eff]
          refine ⟨ho1, by rw [Function.update_self, ho2, rm]; simp; ring, ?_⟩
          intro idx hidx
          simp only [List.length_cons] at hidx
          rw [ho2]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hidx with h | rfl
          · rw [Function.update_of_ne, ho3 idx h, List.reverse_cons,
              List.getD_append _ _ _ _ (by simpa using h)]
            intro h'; have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < M) h'; omega
          · rw [Function.update_self, hR.fld s, List.reverse_cons,
              List.getD_append_right _ _ _ _ (by simp)]; simp
    case fd =>
      have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
      simp [m_tr] at c0 c1
      have hout := hR.out
      simp only [m_outR] at hout
      refine ⟨2, _, by norm_num, m_two hR.bnd hpc c0 (by simp) (by simpa [m_eff] using hR.bnd)
        (by simp [m_eff, hpc]) c1, by simp [m_eff] <;> omega, ?_⟩
      refine ⟨hR.nat, hR.fld, hR.bnd, hR.nfr, hR.ffr, hR.nout, ?_⟩
      simp only [m_outR, m_eff]; rw [hR.fld s, hout]; rfl
    case fc =>
      have hinp := hX.inp
      simp only [m_inOK] at hinp
      obtain ⟨-, hOm⟩ := hinp
      have c0 := hc' 0 (by simp [m_tr]); have c1 := hc' 1 (by simp [m_tr])
      have c2 := hc' 2 (by simp [m_tr]); have c3 := hc' 3 (by simp [m_tr])
      have c4 := hc' 4 (by simp [m_tr])
      simp [m_tr] at c0 c1 c2 c3 c4
      have hout := hR.out
      simp only [m_outR] at hout
      obtain ⟨ho1, ho2, ho3⟩ := hout
      have r7 : w.natReg 7 + 1 ≤ B := by omega
      have hs1 : m_fr M c s ≠ 1 := m_fr_ne_one hM hc2
      have hb1 : ∀ i, (m_eff xs w (.input 1 7)).natReg i ≤ B := by simpa [m_eff] using hR.bnd
      have key : ∀ (w' : MachineState F), w'.natReg = Function.update w.natReg 7 (w.natReg 7 + 1)
          ∨ w'.natReg = Function.update (Function.update w.natReg 9 1) 7 (w.natReg 7 + 1) →
          w'.fieldReg = Function.update w.fieldReg 1 (xs.getD (w0.natReg 7 + z.out.length) 0) →
          w'.out = w.out → w'.natOut = w.natOut →
          (w'.natReg 9 = 0 ↔ (w0.natReg 9 = 0 ∧ ∀ t < z.out.length + 1,
            (z.fieldReg s :: z.out).reverse.getD t 0 = xs.getD (w0.natReg 7 + t) 0)) →
          m_Rn M c B .fc xs w0 (m_eff xsub z (.output s)) w' := by
        intro w' hn hf ho hno hflag
        have hn7 : w'.natReg 7 = w.natReg 7 + 1 := by rcases hn with hn | hn <;> rw [hn] <;> simp
        refine ⟨fun j => ?_, fun j => ?_, fun i => ?_, fun i h1 h2 h3 h4 => ?_, fun a h1 h2 => ?_,
          hno.trans hR.nout, ?_⟩
        · rcases hn with hn | hn <;> simp [m_eff, hn] <;> exact hR.nat j
        · rw [hf, Function.update_of_ne (m_fr_ne_one hM hc2)]; exact hR.fld j
        · rcases hn with hn | hn <;> rw [hn]
          · exact m_bnd_upd hR.bnd r7 i
          · exact m_bnd_upd (m_bnd_upd hR.bnd hX.hB1) (by simpa using r7) i
        · simp only [m_nwr, not_or] at h3
          rcases hn with hn | hn <;> rw [hn] <;> simp [h3.1, h3.2] <;> exact hR.nfr i h1 h2 (by simp [m_nwr, h3.1, h3.2]) h4
        · simp only [m_fwr] at h2
          rw [hf, Function.update_of_ne h2]; exact hR.ffr a h1 (by simpa [m_fwr])
        · simp only [m_outR, m_eff]
          refine ⟨ho.trans ho1, by rw [hn7, ho2]; simp; ring, ?_⟩
          simpa using hflag
      have hu := Function.update_of_ne hs1 (xs.getD (w.natReg 7) 0) w.fieldReg
      have hcond : (Function.update w.fieldReg 1 (xs.getD (w.natReg 7) 0) 1 =
          Function.update w.fieldReg 1 (xs.getD (w.natReg 7) 0) (m_fr M c s)) ↔
          (xs.getD (w0.natReg 7 + z.out.length) 0 = z.fieldReg s) := by
        rw [Function.update_self, hu, ho2, hR.fld s]
      by_cases heq : xs.getD (w0.natReg 7 + z.out.length) 0 = z.fieldReg s
      · have hW : (m_eff xs w (.input 1 7)).fieldReg 1 =
            (m_eff xs w (.input 1 7)).fieldReg (m_fr M c s) := by
          simp only [m_eff]; exact hcond.mpr heq
        refine ⟨4, _, by norm_num, m_reach.succ _ hR.bnd (hpc ▸ c0) (by simp)
          (m_reach.succ (.branch 1 (m_fr M c s) (base + 8 * z.pc + 3) (base + 8 * z.pc + 2))
            hb1 (by simpa [m_eff, hpc] using c1) (by simp)
            (m_two ?_ ?_ c3 (by simp) ?_ ?_ c4)), ?_, ?_⟩
        all_goals try rewrite [m_eff_branch_pos hW]
        · simpa [m_eff] using hR.bnd
        · simp [m_eff, hpc]
        · simp [m_eff, r1]; exact m_bnd_upd hR.bnd r7
        · simp [m_eff, hpc]
        · simp [m_eff] <;> omega
        · refine key _ (Or.inl (by simp [m_eff, r1])) (by simp [m_eff, ho2]) rfl rfl ?_
          simp only [m_eff, Function.update_of_ne (show (9:ℕ) ≠ 7 by decide)]
          rw [show z.out.length + 1 = (z.fieldReg s :: z.out).length by simp, m_forall_rev, ho3,
            heq]
          simp
      · have hW : ¬ (m_eff xs w (.input 1 7)).fieldReg 1 =
            (m_eff xs w (.input 1 7)).fieldReg (m_fr M c s) := by
          simp only [m_eff]; exact mt hcond.mp heq
        refine ⟨5, _, by norm_num, m_reach.succ _ hR.bnd (hpc ▸ c0) (by simp)
          (m_reach.succ (.branch 1 (m_fr M c s) (base + 8 * z.pc + 3) (base + 8 * z.pc + 2))
            hb1 (by simpa [m_eff, hpc] using c1) (by simp)
            (m_reach.succ (.addNat 9 1 0) ?_ ?_ (by simp) (m_two ?_ ?_ c3 (by simp) ?_ ?_ c4))),
            ?_, ?_⟩
        all_goals try rewrite [m_eff_branch_neg hW]
        · simpa [m_eff] using hR.bnd
        · simp [m_eff, hpc]; exact c2
        · simp [m_eff, r1, r0]; exact m_bnd_upd hR.bnd hX.hB1
        · simp [m_eff, hpc]
        · simp [m_eff, r1, r0]; exact m_bnd_upd (m_bnd_upd hR.bnd hX.hB1) (by simpa using r7)
        · simp [m_eff, hpc]
        · simp [m_eff] <;> omega
        · refine key _ (Or.inr (by simp [m_eff, r1, r0])) (by simp [m_eff, ho2]) rfl rfl ?_
          simp only [m_eff]
          rw [show z.out.length + 1 = (z.fieldReg s :: z.out).length by simp, m_forall_rev]
          simp [r1, r0]
          intro _ _; exact Ne.symm heq

/-! ### Part LTGMachine5 -/
/-- A whole sub-run is simulated. -/
theorem m_sub_sim {M c B Bs Om : ℕ} {md : m_Mode} {xs xsub : List F} {w0 : MachineState F}
    (hX : m_Ctx M c B Bs Om md xs xsub w0) {P Q : Program F} {base exit : ℕ}
    (hQ : ∀ p ins, P[p]? = some ins → ∀ r < 8,
      Q[base + 8 * p + r]? = (m_blk M c base exit md p ins)[r]?) :
    ∀ t (z w zf : MachineState F), runFrom P [] xsub Bs t z = some zf → zf.out.length ≤ Om →
      w.pc = base + 8 * z.pc → m_Rn M c B md xs w0 z w →
      ∃ n w', n ≤ 8 * t ∧ m_reach Q xs B n w w' ∧ w'.pc = exit ∧ m_Rn M c B md xs w0 zf w' := by
  intro t
  induction t with
  | zero => intro z w zf h; simp [runFrom] at h
  | succ t ih =>
    intro z w zf h hzf hpc hR
    obtain ⟨hzb, ⟨hq, rfl⟩ | ⟨ins, hq, hh, h2⟩⟩ := m_runFrom_succ h
    · have c0 := hQ _ _ hq 0 (by norm_num)
      simp [m_blk, m_pad, m_tr] at c0
      exact ⟨1, _, by omega, m_one hR.bnd hpc c0 (by simp), rfl,
        m_Rn_same hR rfl rfl rfl rfl rfl rfl rfl⟩
    · have hz1 := m_runFrom_bounded h2
      have hO := ((m_runFrom_out t _ zf h2).1).trans hzf
      obtain ⟨n1, w1, hn1, hr1, hpc1, hR1⟩ :=
        m_blk_sim hX hh (hQ _ _ hq) hpc hzb hz1 hO hR
      obtain ⟨n2, w2, hn2, hr2, hpc2, hR2⟩ := ih _ _ zf h2 hzf hpc1 hR1
      exact ⟨n2 + n1, w2, by omega, m_reach_trans hr1 hr2, hpc2, hR2⟩

/-! Program layout. -/

def m_seg (Q : Program F) (b : ℕ) (l : Program F) : Prop := ∀ k < l.length, Q[b + k]? = l[k]?

theorem m_seg_self (Q : Program F) : m_seg Q 0 Q := fun k _ => by simp

theorem m_seg_left {Q : Program F} {b : ℕ} {l1 l2 : Program F} (h : m_seg Q b (l1 ++ l2)) :
    m_seg Q b l1 := fun k hk => by
  rw [h k (by simp; omega), List.getElem?_append_left hk]

theorem m_seg_right {Q : Program F} {b : ℕ} {l1 l2 : Program F} (h : m_seg Q b (l1 ++ l2)) :
    m_seg Q (b + l1.length) l2 := fun k hk => by
  rw [Nat.add_assoc, h _ (by simp; omega), List.getElem?_append_right (by omega)]
  simp

theorem m_flatten_get {α : Type} (L : ℕ) :
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

theorem m_flatten_length {α : Type} (L : ℕ) :
    ∀ (l : List (List α)), (∀ x ∈ l, x.length = L) → l.flatten.length = L * l.length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
    intro hl
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [hl x (by simp), ih (fun y hy => hl y (by simp [hy]))]
    ring

theorem m_seg_flatten {Q : Program F} {b L : ℕ} {l : List (Program F)}
    (h : m_seg Q b l.flatten) (hl : ∀ x ∈ l, x.length = L) (i : ℕ) (hi : i < l.length) :
    m_seg Q (b + L * i) l[i] := by
  intro k hk
  have hL : l[i].length = L := hl _ (List.getElem_mem hi)
  have hlen := m_flatten_length L l hl
  have hlt : L * i + k < l.flatten.length := by
    rw [hlen]
    have : L * i + L ≤ L * l.length := by nlinarith
    omega
  rw [Nat.add_assoc, h _ hlt, m_flatten_get L l hl i k (by omega)]
  simp [List.getElem?_eq_getElem hi]

def m_trP (M c base exit : ℕ) (md : m_Mode) (P : Program F) : Program F :=
  (P.mapIdx (fun p ins => m_blk M c base exit md p ins)).flatten

theorem m_trP_length (M c base exit : ℕ) (md : m_Mode) (P : Program F) :
    (m_trP M c base exit md P).length = 8 * P.length := by
  unfold m_trP
  rw [m_flatten_length 8]
  · simp
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp [m_blk_length]

theorem m_seg_trP {Q : Program F} {M c base exit : ℕ} {md : m_Mode} {P : Program F}
    (h : m_seg Q base (m_trP M c base exit md P)) :
    ∀ p ins, P[p]? = some ins → ∀ r < 8,
      Q[base + 8 * p + r]? = (m_blk M c base exit md p ins)[r]? := by
  intro p ins hp r hr
  have hpl : p < P.length := (List.getElem?_eq_some_iff.mp hp).1
  rw [Nat.add_assoc, h _ (by rw [m_trP_length]; omega)]
  unfold m_trP
  rw [m_flatten_get 8 _ _ p r hr]
  · simp [List.getElem?_mapIdx, hp]
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp [m_blk_length]

theorem m_mapIdx_size (g : ℕ → Instruction F → Program F)
    (hg : ∀ p ins, programSize (g p ins) ≤ 8 * instructionSize ins) :
    ∀ P : Program F, programSize (P.mapIdx g).flatten ≤ 8 * programSize P := by
  intro P
  induction P generalizing g with
  | nil => simp [programSize]
  | cons a P ih =>
    rw [List.mapIdx_cons, List.flatten_cons, m_programSize_append, m_programSize_cons]
    have := ih (fun i => g (i + 1)) (fun p ins => hg (p + 1) ins)
    have := hg 0 a
    omega

theorem m_trP_size (M c base exit : ℕ) (md : m_Mode) (P : Program F) :
    programSize (m_trP M c base exit md P) ≤ 8 * programSize P :=
  m_mapIdx_size _ (fun p ins => m_blk_size M c base exit md p ins) P

/-! ### Part LTGMachine6 -/
/-! The composite programs. -/

def m_chunk (m cb : ℕ) (md : m_Mode) (Pf : Program F) (i : ℕ) : Program F :=
  [.addNat 3 3 1] ++
    m_trP (m + 3) (3 + i) (cb + (8 * Pf.length + 2) * i + 1)
      (cb + (8 * Pf.length + 2) * i + 1 + 8 * Pf.length) md Pf ++ [.addNat 5 5 4]

def m_copies (m cb : ℕ) (md : m_Mode) (Pf : Program F) : Program F :=
  ((List.range m).map (m_chunk m cb md Pf)).flatten

theorem m_chunk_length (m cb : ℕ) (md : m_Mode) (Pf : Program F) (i : ℕ) :
    (m_chunk m cb md Pf i).length = 8 * Pf.length + 2 := by
  simp [m_chunk, m_trP_length] <;> omega

theorem m_seg_chunk {Q : Program F} {m cb : ℕ} {md : m_Mode} {Pf : Program F}
    (h : m_seg Q cb (m_copies m cb md Pf)) (i : ℕ) (hi : i < m) :
    m_seg Q (cb + (8 * Pf.length + 2) * i) (m_chunk m cb md Pf i) := by
  have := m_seg_flatten (L := 8 * Pf.length + 2) h (by
    intro x hx; simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, _, rfl⟩ := hx; exact m_chunk_length m cb md Pf j) i (by simpa using hi)
  simpa using this

theorem m_copies_size (m cb : ℕ) (md : m_Mode) (Pf : Program F) :
    programSize (m_copies m cb md Pf) ≤ m * (8 * programSize Pf + 2) := by
  unfold m_copies
  have hc : ∀ i, programSize (m_chunk m cb md Pf i) ≤ 8 * programSize Pf + 2 := by
    intro i
    simp only [m_chunk, m_programSize_append]
    have := m_trP_size (m + 3) (3 + i) (cb + (8 * Pf.length + 2) * i + 1)
      (cb + (8 * Pf.length + 2) * i + 1 + 8 * Pf.length) md Pf
    simp [programSize, instructionSize] at this ⊢
    omega
  have : ∀ n, programSize ((List.range n).map (m_chunk m cb md Pf)).flatten ≤
      n * (8 * programSize Pf + 2) := by
    intro n
    induction n with
    | zero => simp [programSize]
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.flatten_append, m_programSize_append]
      have := hc n
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil]
      rw [Nat.succ_mul]; omega
  exact this m

def m_cout (k b i : ℕ) (md : m_Mode) (o0 xs : List F) (G : ℕ → List F) (w : MachineState F) :
    Prop :=
  match md with
  | .fd => w.out.reverse = o0.reverse ++ ((List.range i).map G).flatten
  | .fc => w.out = o0 ∧ w.natReg 7 = k + i * b ∧
      (w.natReg 9 = 0 ↔ ∀ j < i, ∀ t < b, (G j).getD t 0 = xs.getD (k + j * b + t) 0)
  | .pc => True

/-- Invariant before copy `i`. -/
structure m_CInv (m s' k b B pc i : ℕ) (md : m_Mode) (o0 xs data : List F) (G : ℕ → List F)
    (w : MachineState F) : Prop where
  pc : w.pc = pc
  r0 : w.natReg 0 = 0
  r1 : w.natReg 1 = 1
  r2 : w.natReg 2 = m + 3
  r3 : w.natReg 3 = 2 + i
  r4 : w.natReg 4 = s'
  r5 : w.natReg 5 = i * s'
  r8 : w.natReg 8 = k
  nz : ∀ j c, 3 + i ≤ c → c < m + 3 → w.natReg (m_nr (m + 3) c j) = 0
  fz : ∀ j c, 3 + i ≤ c → c < m + 3 → w.fieldReg (m_fr (m + 3) c j) = 0
  data : ∀ idx < data.length, w.fieldReg (idx * (m + 3)) = data.getD idx 0
  bnd : ∀ j, w.natReg j ≤ B
  nout : w.natOut = []
  out : m_cout k b i md o0 xs G w

theorem m_copy_step {s b m k s' B Bf Tf cb : ℕ} {md : m_Mode} (hmd : md ≠ .pc)
    {Pf Q : Program F} {xs o0 data : List F} {X G : ℕ → List F} {i : ℕ} (hi : i < m)
    (hs' : s' = s)
    (hseg : m_seg Q (cb + (8 * Pf.length + 2) * i) (m_chunk m cb md Pf i))
    (hrun : ∃ t zf, programSize Pf + t ≤ Tf ∧
      runFrom Pf [] (X i) Bf t initialState = some zf ∧ zf.out.reverse = G i)
    (hG : (G i).length = b)
    (hX : ∀ a < s, data.getD (i * s + a) 0 = (X i).getD a 0)
    (hX0 : ∀ a, s ≤ a → (X i).getD a 0 = 0)
    (hdl : i * s + s ≤ data.length)
    (hB1 : 1 ≤ B) (hBf : Bf ≤ B) (hBa : (Bf + 1) * (m + 3) ≤ B)
    (hIS : m * s * (m + 3) ≤ B) (hIK : k + m * b ≤ B) (hRES : m + 3 ≤ B)
    {w : MachineState F}
    (hw : m_CInv m s' k b B (cb + (8 * Pf.length + 2) * i) i md o0 xs data G w) :
    ∃ n w', n + 8 * programSize Pf ≤ 8 * Tf + 2 ∧ m_reach Q xs B n w w' ∧
      m_CInv m s' k b B (cb + (8 * Pf.length + 2) * (i + 1)) (i + 1) md o0 xs data G w' := by
  obtain ⟨t, zf, htf, hrf, hzo⟩ := hrun
  subst s'
  have hzl : zf.out.length = b := by rw [← List.length_reverse, hzo, hG]
  have hs0 : m_seg Q (cb + (8 * Pf.length + 2) * i) [Instruction.addNat 3 3 1] := m_seg_left (m_seg_left hseg)
  have hstr := m_seg_right (m_seg_left hseg)
  simp only [List.length_singleton] at hstr
  have hsc := m_seg_right hseg
  simp only [List.length_append, List.length_singleton, m_trP_length] at hsc
  have c0 : Q[cb + (8 * Pf.length + 2) * i]? = some (.addNat 3 3 1) := by simpa using hs0 0 (by simp)
  have cE : Q[cb + (8 * Pf.length + 2) * i + (1 + 8 * Pf.length)]? = some (.addNat 5 5 4) := by
    simpa using hsc 0 (by simp)
  have hmpos : 0 < m := by omega
  have hsB : s ≤ B := by
    have : s ≤ m * s * (m + 3) := by
      have h1 : s ≤ m * s := Nat.le_mul_of_pos_left s hmpos
      exact h1.trans (Nat.le_mul_of_pos_right _ (by omega))
    omega
  have hISs : (i * s + s) * (m + 3) ≤ B := by
    have : i * s + s ≤ m * s := by
      have := Nat.mul_le_mul_right s (show i + 1 ≤ m by omega); rw [Nat.succ_mul] at this; exact this
    exact le_trans (Nat.mul_le_mul_right _ this) hIS
  -- step 1
  set wa := m_eff xs w (.addNat 3 3 1) with hwa
  have hra : m_reach Q xs B 1 w wa := m_one hw.bnd hw.pc c0 (by simp)
  have hwan : wa.natReg = Function.update w.natReg 3 (3 + i) := by
    simp only [hwa, m_eff, hw.r3, hw.r1]; congr 1; omega
  have hwaf : wa.fieldReg = w.fieldReg := rfl
  have hwao : wa.out = w.out := rfl
  have hwano : wa.natOut = w.natOut := rfl
  have hwa4 : wa.natReg 4 = s := by rw [hwan]; simp [hw.r4]
  have hwa5 : wa.natReg 5 = i * s := by rw [hwan]; simp [hw.r5]
  have hinp : m_inOK (m + 3) B b xs (X i) wa md := by
    have hd : m_dataOK (m + 3) B (X i) wa := by
      refine ⟨by rw [hwa4]; exact hsB, by rw [hwa4, hwa5]; exact hISs, fun a ha => ?_, ?_⟩
      · rw [hwa4] at ha
        rw [hwaf, hwa5, hw.data _ (by omega), hX a ha]
      · intro a ha; rw [hwa4] at ha; exact hX0 a ha
    cases md
    · exact absurd rfl hmd
    · exact hd
    · have ho := hw.out
      simp only [m_cout] at ho
      refine ⟨hd, ?_⟩
      rw [hwan, Function.update_of_ne (by norm_num), ho.2.1]
      have := Nat.mul_le_mul_right b (show i + 1 ≤ m by omega)
      rw [Nat.succ_mul] at this; omega
  have hctx : m_Ctx (m + 3) (3 + i) B Bf b md xs (X i) wa :=
    { hM := by omega, hc := by omega, hB := hBf, hBa := hBa, hB1 := hB1,
      r0 := by rw [hwan]; simp [hw.r0], r1 := by rw [hwan]; simp [hw.r1],
      rm := by rw [hwan]; simp [hw.r2], rres := by rw [hwan]; simp, inp := hinp }
  have hR0 : m_Rn (m + 3) (3 + i) B md xs wa initialState wa :=
    { nat := fun j => by
        rw [hwan, Function.update_of_ne (by simp)]
        simpa [initialState] using hw.nz j (3 + i) le_rfl (by omega)
      fld := fun j => by rw [hwaf]; simpa [initialState] using hw.fz j (3 + i) le_rfl (by omega)
      bnd := by rw [hwan]; exact m_bnd_upd hw.bnd (by omega)
      nfr := fun _ _ _ _ _ => rfl
      ffr := fun _ _ _ => rfl
      nout := rfl
      out := by cases md <;> first | exact absurd rfl hmd | simp [m_outR, initialState] }
  obtain ⟨n1, wb, hn1, hrb, hpcb, hRb⟩ := m_sub_sim hctx (m_seg_trP hstr) t initialState wa zf
    hrf (by rw [hzl]) (by simp [hwa, m_eff, hw.pc, initialState]) hR0
  -- step 3
  have c' : Q[wb.pc]? = some (.addNat 5 5 4) := by
    rw [hpcb, ← cE]; congr 1; omega
  have hrc : m_reach Q xs B 1 wb (m_eff xs wb (.addNat 5 5 4)) := m_one hRb.bnd rfl c' (by simp)
  have hreg : ∀ j, j < 13 → j ≠ 10 → j ≠ 11 → j ≠ 7 → j ≠ 9 → wb.natReg j = wa.natReg j := by
    intro j h1 h2 h3 h4 h5
    refine m_Rn_reg hRb h1 h2 h3 ?_
    cases md
    · exact absurd rfl hmd
    · simp [m_nwr]
    · simp [m_nwr, h4, h5]
  have hb4 : wb.natReg 4 = s := (hreg 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).trans hwa4
  have hb5 : wb.natReg 5 = i * s := (hreg 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).trans hwa5
  have hwcn : (m_eff xs wb (.addNat 5 5 4)).natReg = Function.update wb.natReg 5 (i * s + s) := by
    simp only [m_eff, hb4, hb5]
  have hnfw : ∀ a, ¬ m_fwr (m + 3) md a ∨ a = 1 := by
    intro a
    by_cases h : a = 1
    · exact Or.inr h
    · left; cases md
      · exact absurd rfl hmd
      · simp [m_fwr]
      · simp [m_fwr, h]
  have hfr_ok : ∀ a, (∀ j, a ≠ m_fr (m + 3) (3 + i) j) → a ≠ 1 → wb.fieldReg a = w.fieldReg a := by
    intro a h1 h2
    rcases hnfw a with h | h
    · exact hRb.ffr a h1 h
    · exact absurd h h2
  refine ⟨1 + (n1 + 1), _, by omega, m_reach_trans (m_reach_trans hra hrb) hrc, ?_⟩
  refine { pc := ?_, r0 := ?_, r1 := ?_, r2 := ?_, r3 := ?_, r4 := ?_, r5 := ?_, r8 := ?_,
           nz := ?_, fz := ?_, data := ?_, bnd := ?_, nout := ?_, out := ?_ }
  · simp only [m_eff, hpcb]; ring
  · rw [hwcn, Function.update_of_ne (by norm_num), hreg 0 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num), hwan]; simp [hw.r0]
  · rw [hwcn, Function.update_of_ne (by norm_num), hreg 1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num), hwan]; simp [hw.r1]
  · rw [hwcn, Function.update_of_ne (by norm_num), hreg 2 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num), hwan]; simp [hw.r2]
  · rw [hwcn, Function.update_of_ne (by norm_num), hreg 3 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num), hwan]; simp; omega
  · rw [hwcn, Function.update_of_ne (by norm_num), hb4]
  · rw [hwcn, Function.update_self]; ring
  · rw [hwcn, Function.update_of_ne (by norm_num), hreg 8 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num), hwan]; simp [hw.r8]
  · intro j c hc1 hc2
    rw [hwcn, Function.update_of_ne (by simp)]
    have hne : ∀ a, m_nr (m + 3) c j ≠ m_nr (m + 3) (3 + i) a := by
      intro a h; unfold m_nr at h
      have := (m_res (M := m + 3) (c' := 3 + i) (j := j) (j' := a) hc2 (by omega) (by omega)).1; omega
    have hge := m_nr_ge (m + 3) c j
    rw [hRb.nfr _ (by omega) (by omega) (by cases md <;> simp [m_nwr] <;> omega) hne, hwan,
      Function.update_of_ne (by simp)]
    exact hw.nz j c (by omega) hc2
  · intro j c hc1 hc2
    show wb.fieldReg _ = 0
    rw [hfr_ok _ (fun a h => by
      have := (m_res (M := m + 3) (c' := 3 + i) (j := j) (j' := a) hc2 (by omega) h).1; omega)
      (m_fr_ne_one hc2 (by omega))]
    exact hw.fz j c (by omega) hc2
  · intro idx hidx
    show wb.fieldReg _ = _
    rw [hfr_ok _ (fun a h => m_fr_ne_data (M := m + 3) (c := 3 + i) (by omega) (by omega) h.symm)]
    · exact hw.data idx hidx
    · intro h
      rcases idx with _ | idx
      · simp at h
      · have : m + 3 ≤ (idx + 1) * (m + 3) := Nat.le_mul_of_pos_left _ (by omega)
        omega
  · rw [hwcn]; exact m_bnd_upd hRb.bnd (by
      have : i * s + s ≤ (i * s + s) * (m + 3) := Nat.le_mul_of_pos_right _ (by omega)
      omega)
  · show wb.natOut = []; rw [hRb.nout, hwano, hw.nout]
  · have hout := hRb.out
    have hwo := hw.out
    cases md
    · exact absurd rfl hmd
    · simp only [m_outR] at hout
      simp only [m_cout] at hwo ⊢
      show wb.out.reverse = _
      rw [hout, List.reverse_append, hzo, hwao, hwo, List.range_succ, List.map_append,
        List.flatten_append]
      simp
    · simp only [m_outR] at hout
      simp only [m_cout] at hwo ⊢
      obtain ⟨ho1, ho2, ho3⟩ := hout
      have h9 : wa.natReg 9 = w.natReg 9 := by rw [hwan]; simp
      have h7 : wa.natReg 7 = w.natReg 7 := by rw [hwan]; simp
      refine ⟨by show wb.out = o0; rw [ho1, hwao, hwo.1], ?_, ?_⟩
      · rw [hwcn, Function.update_of_ne (by norm_num), ho2, hzl, h7, hwo.2.1]; ring
      · rw [hwcn, Function.update_of_ne (by norm_num), ho3, h9, hwo.2.2, hzl, h7, hwo.2.1, hzo]
        constructor
        · rintro ⟨h1, h2⟩ j hj t ht
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact h1 j hj t ht
          · rw [h2 t ht]
        · intro h
          refine ⟨fun j hj t ht => h j (by omega) t ht, fun t ht => ?_⟩
          rw [h i (by omega) t ht]

/-! ### Part LTGMachine7 -/
/-- State before the encoder phase. -/
structure m_Ready (M s' k B pc0 : ℕ) (o0 : List F) (w : MachineState F) : Prop where
  pc : w.pc = pc0
  r0 : w.natReg 0 = 0
  r1 : w.natReg 1 = 1
  r2 : w.natReg 2 = M
  r3 : w.natReg 3 = 2
  r4 : w.natReg 4 = s'
  r5 : w.natReg 5 = 0
  r6 : w.natReg 6 = 0
  r7 : w.natReg 7 = k
  r8 : w.natReg 8 = k
  r9 : w.natReg 9 = 0
  nz : ∀ j c, 2 ≤ c → c < M → w.natReg (m_nr M c j) = 0
  fz : ∀ j c, 2 ≤ c → c < M → w.fieldReg (m_fr M c j) = 0
  bnd : ∀ j, w.natReg j ≤ B
  out : w.out = o0
  nout : w.natOut = []

/-- The encoder phase. -/
theorem m_pc_phase {s m k b s' B BC TC cb0 : ℕ} {md : m_Mode} (hmd : md ≠ .pc)
    {PC Q : Program F} {xs o0 xin data : List F} {G : ℕ → List F}
    (hseg : m_seg Q cb0 (m_trP (m + 3) 2 cb0 (cb0 + 8 * PC.length) .pc PC))
    (hrun : ∃ t zf, programSize PC + t ≤ TC ∧
      runFrom PC [] xin BC t initialState = some zf ∧ zf.out.reverse = data)
    (hdl : data.length = m * s)
    (hxs : ∀ a < k, xs.getD a 0 = xin.getD a 0) (hx0 : ∀ a, k ≤ a → xin.getD a 0 = 0)
    (hB1 : 1 ≤ B) (hBC : BC ≤ B) (hBa : (BC + 1) * (m + 3) ≤ B) (hk : k ≤ B)
    (hD : m * s * (m + 3) ≤ B)
    {w : MachineState F} (hw : m_Ready (m + 3) s' k B cb0 o0 w) :
    ∃ n w', n + 8 * programSize PC ≤ 8 * TC ∧ m_reach Q xs B n w w' ∧
      m_CInv m s' k b B (cb0 + 8 * PC.length) 0 md o0 xs data G w' := by
  obtain ⟨t, zf, htc, hrz, hzo⟩ := hrun
  have hzl : zf.out.length = m * s := by rw [← List.length_reverse, hzo, hdl]
  have hctx : m_Ctx (m + 3) 2 B BC (m * s) .pc xs xin w :=
    { hM := by omega, hc := le_rfl, hB := hBC, hBa := hBa, hB1 := hB1, r0 := hw.r0,
      r1 := hw.r1, rm := hw.r2, rres := hw.r3,
      inp := ⟨by rw [hw.r8]; exact hk, by rw [hw.r8]; exact hxs,
        by rw [hw.r8]; exact hx0, hD⟩ }
  have hR0 : m_Rn (m + 3) 2 B .pc xs w initialState w :=
    { nat := fun j => by simpa [initialState] using hw.nz j 2 le_rfl (by omega)
      fld := fun j => by simpa [initialState] using hw.fz j 2 le_rfl (by omega)
      bnd := hw.bnd
      nfr := fun _ _ _ _ _ => rfl
      ffr := fun _ _ _ => rfl
      nout := rfl
      out := ⟨rfl, by simp [hw.r6, initialState], by simp [initialState]⟩ }
  obtain ⟨n, w1, hn, hr, hpc1, hR⟩ := m_sub_sim hctx (m_seg_trP hseg) t initialState w zf hrz
    (by rw [hzl]) (by simp [hw.pc, initialState]) hR0
  have hreg : ∀ j, j < 13 → j ≠ 10 → j ≠ 11 → j ≠ 6 → w1.natReg j = w.natReg j := by
    intro j h1 h2 h3 h4
    exact m_Rn_reg hR h1 h2 h3 (by simp [m_nwr, h4])
  have hout := hR.out
  simp only [m_outR] at hout
  obtain ⟨ho1, -, ho3⟩ := hout
  refine ⟨n, w1, by omega, hr, ?_⟩
  refine { pc := hpc1, r0 := ?_, r1 := ?_, r2 := ?_, r3 := ?_, r4 := ?_, r5 := ?_, r8 := ?_,
           nz := ?_, fz := ?_, data := ?_, bnd := hR.bnd, nout := ?_, out := ?_ }
  · rw [hreg 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hw.r0]
  · rw [hreg 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hw.r1]
  · rw [hreg 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hw.r2]
  · rw [hreg 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hw.r3]
  · rw [hreg 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hw.r4]
  · rw [hreg 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hw.r5]; simp
  · rw [hreg 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hw.r8]
  · intro j c hc1 hc2
    have hge := m_nr_ge (m + 3) c j
    have hne : ∀ a, m_nr (m + 3) c j ≠ m_nr (m + 3) 2 a := by
      intro a h; unfold m_nr at h
      have := (m_res (M := m + 3) (c' := 2) (j := j) (j' := a) hc2 (by omega) (by omega)).1
      omega
    rw [hR.nfr _ (by omega) (by omega) (by simp [m_nwr] <;> omega) hne]
    exact hw.nz j c (by omega) hc2
  · intro j c hc1 hc2
    rw [hR.ffr _ (fun a h => by
      have := (m_res (M := m + 3) (c' := 2) (j := j) (j' := a) hc2 (by omega) h).1; omega)
      (by simp only [m_fwr, not_exists]; exact fun idx => m_fr_ne_data hc2 (by omega))]
    exact hw.fz j c (by omega) hc2
  · intro idx hidx
    rw [ho3 idx (by omega), hzo]
  · rw [hR.nout, hw.nout]
  · cases md
    · exact absurd rfl hmd
    · simp only [m_cout]; rw [ho1, hw.out]; simp
    · simp only [m_cout]
      refine ⟨by rw [ho1, hw.out], ?_, ?_⟩
      · rw [hreg 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hw.r7]; simp
      · rw [hreg 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hw.r9]; simp

/-- All the copies. -/
theorem m_copies_phase {s b m k s' B Bf Tf cb : ℕ} {md : m_Mode} (hmd : md ≠ .pc)
    {Pf Q : Program F} {xs o0 data : List F} {X G : ℕ → List F}
    (hs' : 0 < m → s' = s)
    (hseg : m_seg Q cb (m_copies m cb md Pf))
    (hrun : ∀ i < m, ∃ t zf, programSize Pf + t ≤ Tf ∧
      runFrom Pf [] (X i) Bf t initialState = some zf ∧ zf.out.reverse = G i)
    (hG : ∀ i < m, (G i).length = b)
    (hX : ∀ i < m, ∀ a < s, data.getD (i * s + a) 0 = (X i).getD a 0)
    (hX0 : ∀ i < m, ∀ a, s ≤ a → (X i).getD a 0 = 0)
    (hdl : m * s ≤ data.length)
    (hB1 : 1 ≤ B) (hBf : Bf ≤ B) (hBa : (Bf + 1) * (m + 3) ≤ B)
    (hIS : m * s * (m + 3) ≤ B) (hIK : k + m * b ≤ B) (hRES : m + 3 ≤ B)
    {w : MachineState F} (hw : m_CInv m s' k b B cb 0 md o0 xs data G w) :
    ∀ i ≤ m, ∃ n w', n + i * (8 * programSize Pf) ≤ i * (8 * Tf + 2) ∧ m_reach Q xs B n w w' ∧
      m_CInv m s' k b B (cb + (8 * Pf.length + 2) * i) i md o0 xs data G w' := by
  intro i
  induction i with
  | zero => intro _; exact ⟨0, w, by simp, m_reach.zero _, by simpa using hw⟩
  | succ i ih =>
    intro hi
    obtain ⟨n, w1, hn, hr, hw1⟩ := ih (by omega)
    have hdl' : i * s + s ≤ data.length := by
      have := Nat.mul_le_mul_right s (show i + 1 ≤ m by omega)
      rw [Nat.succ_mul] at this; omega
    obtain ⟨n2, w2, hn2, hr2, hw2⟩ := m_copy_step hmd (by omega) (hs' (by omega))
      (m_seg_chunk hseg i (by omega)) (hrun i (by omega)) (hG i (by omega)) (hX i (by omega))
      (hX0 i (by omega)) hdl' hB1 hBf hBa hIS hIK hRES hw1
    refine ⟨n2 + n, w2, ?_, m_reach_trans hr hr2, hw2⟩
    have e1 : (i + 1) * (8 * programSize Pf) = i * (8 * programSize Pf) + 8 * programSize Pf := by
      ring
    have e2 : (i + 1) * (8 * Tf + 2) = i * (8 * Tf + 2) + (8 * Tf + 2) := by ring
    rw [e1, e2]; omega

theorem m_blockData_length {s m : ℕ} (y : Blocks F s m) : (blockData y).length = m * s := by
  unfold blockData
  rw [m_flatten_length s]
  · simp; ring
  · intro x hx
    simp only [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [vectorData]

theorem m_blockData_getD {s m : ℕ} (y : Blocks F s m) (i : Fin m) (a : Fin s) :
    (blockData y).getD (i * s + a) 0 = y i a := by
  unfold blockData
  rw [List.getD_eq_getElem?_getD, show (i : ℕ) * s + a = s * i + a by ring,
    m_flatten_get s _ _ i a a.2]
  · simp [vectorData]
  · intro x hx
    simp only [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [vectorData]

theorem m_vectorData_getD {n : ℕ} (v : Vec F n) (a : ℕ) :
    (vectorData v).getD a 0 = if h : a < n then v ⟨a, h⟩ else 0 := by
  unfold vectorData
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · simp [h]

/-! ### Part LTGMachine8 -/
def m_setup (M s' k : ℕ) : Program F :=
  [.literal 1 1, .literal 2 M, .literal 3 2, .literal 4 s', .literal 8 k, .literal 7 k]

def m_loop : Program F := [.branchNat 12 8 11 7, .input 1 12, .output 1, .addNat 12 12 1, .jump 6]

def m_cmpPost (f : ℕ) : Program F :=
  [.branchNat 9 0 (f + 1) (f + 4), .constant 1 1, .output 1, .halt, .constant 1 0, .output 1, .halt]

def m_prog (m s' k : ℕ) (md : m_Mode) (pre : Program F) (post : ℕ → Program F)
    (PC Pf : Program F) : Program F :=
  m_setup (m + 3) s' k ++ (pre ++ (m_trP (m + 3) 2 (6 + pre.length)
    (6 + pre.length + 8 * PC.length) .pc PC ++
    (m_copies m (6 + pre.length + 8 * PC.length) md Pf ++
      post (6 + pre.length + 8 * PC.length + (8 * Pf.length + 2) * m))))

theorem m_copies_length (m cb : ℕ) (md : m_Mode) (Pf : Program F) :
    (m_copies m cb md Pf).length = (8 * Pf.length + 2) * m := by
  unfold m_copies
  rw [m_flatten_length (8 * Pf.length + 2)]
  · simp
  · intro x hx; simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, _, rfl⟩ := hx; exact m_chunk_length m cb md Pf j

/-- The segments of a composite program. -/
theorem m_prog_segs (m s' k : ℕ) (md : m_Mode) (pre : Program F) (post : ℕ → Program F)
    (PC Pf : Program F) :
    let Q := m_prog m s' k md pre post PC Pf
    let cb0 := 6 + pre.length
    let cb := cb0 + 8 * PC.length
    m_seg Q 0 (m_setup (m + 3) s' k) ∧ m_seg Q 6 pre ∧
    m_seg Q cb0 (m_trP (m + 3) 2 cb0 cb .pc PC) ∧ m_seg Q cb (m_copies m cb md Pf) ∧
    m_seg Q (cb + (8 * Pf.length + 2) * m) (post (cb + (8 * Pf.length + 2) * m)) := by
  intro Q cb0 cb
  have h0 : m_seg Q 0 Q := m_seg_self Q
  have h1 := m_seg_right h0
  simp only [m_setup, List.length_cons, List.length_nil] at h1
  have h2 := m_seg_right h1
  have h3 := m_seg_right h2
  rw [m_trP_length] at h3
  have h4 := m_seg_right h3
  rw [m_copies_length] at h4
  refine ⟨m_seg_left h0, m_seg_left h1, m_seg_left h2, m_seg_left h3, ?_⟩
  simpa [cb, cb0, Nat.add_assoc] using h4

theorem m_setup_run {Q : Program F} {xs : List F} {B M s' k : ℕ}
    (hseg : m_seg Q 0 (m_setup M s' k)) (hM : M ≤ B) (hs : s' ≤ B) (hk : k ≤ B) (h2 : 2 ≤ B)
    (hM2 : 2 < M) :
    ∃ w, m_reach Q xs B 6 initialState w ∧ m_Ready M s' k B 6 [] w ∧ w.natReg 12 = 0 := by
  have c := fun r (hr : r < 6) => hseg r (by simpa [m_setup] using hr)
  have c0 : Q[0]? = some (.literal 1 1) := by simpa [m_setup] using c 0 (by norm_num)
  have c1 : Q[1]? = some (.literal 2 M) := by simpa [m_setup] using c 1 (by norm_num)
  have c2 : Q[2]? = some (.literal 3 2) := by simpa [m_setup] using c 2 (by norm_num)
  have c3 : Q[3]? = some (.literal 4 s') := by simpa [m_setup] using c 3 (by norm_num)
  have c4 : Q[4]? = some (.literal 8 k) := by simpa [m_setup] using c 4 (by norm_num)
  have c5 : Q[5]? = some (.literal 7 k) := by simpa [m_setup] using c 5 (by norm_num)
  have hb : ∀ (w : MachineState F), (∀ i, w.natReg i ≤ B) → ∀ d v, v ≤ B →
      ∀ i, (m_eff xs w (.literal d v)).natReg i ≤ B :=
    fun w hw d v hv => by simp only [m_eff]; exact m_bnd_upd hw hv
  have hb0 : ∀ i, (initialState : MachineState F).natReg i ≤ B := by simp [initialState]
  refine ⟨_, m_reach.succ _ hb0 c0 (by simp)
    (m_reach.succ _ (hb _ hb0 _ _ (by omega)) c1 (by simp)
    (m_reach.succ _ (hb _ (hb _ hb0 _ _ (by omega)) _ _ hM) c2 (by simp)
    (m_reach.succ _ (hb _ (hb _ (hb _ hb0 _ _ (by omega)) _ _ hM) _ _ (by omega)) c3 (by simp)
    (m_reach.succ _ (hb _ (hb _ (hb _ (hb _ hb0 _ _ (by omega)) _ _ hM) _ _ (by omega)) _ _ hs)
      c4 (by simp)
    (m_reach.succ _ (hb _ (hb _ (hb _ (hb _ (hb _ hb0 _ _ (by omega)) _ _ hM) _ _ (by omega))
      _ _ hs) _ _ hk) c5 (by simp) (m_reach.zero _)))))), ?_, ?_⟩
  · refine { pc := by simp [m_eff, initialState], r0 := by simp [m_eff, initialState],
             r1 := by simp [m_eff, initialState], r2 := by simp [m_eff, initialState],
             r3 := by simp [m_eff, initialState], r4 := by simp [m_eff, initialState],
             r5 := by simp [m_eff, initialState], r6 := by simp [m_eff, initialState],
             r7 := by simp [m_eff, initialState], r8 := by simp [m_eff, initialState],
             r9 := by simp [m_eff, initialState], nz := ?_, fz := ?_, bnd := ?_,
             out := by simp [m_eff, initialState], nout := by simp [m_eff, initialState] }
    · intro j c _ _; simp [m_eff, initialState]
    · intro j c _ _; simp [m_eff, initialState]
    · exact hb _ (hb _ (hb _ (hb _ (hb _ (hb _ hb0 _ _ (by omega)) _ _ hM) _ _ (by omega))
        _ _ hs) _ _ hk) _ _ hk
  · simp [m_eff, initialState]

theorem m_loop_run {Q : Program F} {xs : List F} {B M s' k : ℕ} (hseg : m_seg Q 6 m_loop)
    (hlen : xs.length = k) (hkB : k ≤ B) (hM : 2 < M)
    {w : MachineState F} (hw : m_Ready M s' k B 6 [] w) (h12 : w.natReg 12 = 0) :
    ∃ n w', n ≤ 5 * k + 1 ∧ m_reach Q xs B n w w' ∧ m_Ready M s' k B 11 xs.reverse w' := by
  have c := fun r (hr : r < 5) => hseg r (by simpa [m_loop] using hr)
  have c0 : Q[6]? = some (.branchNat 12 8 11 7) := by simpa [m_loop] using c 0 (by norm_num)
  have c1 : Q[7]? = some (.input 1 12) := by simpa [m_loop] using c 1 (by norm_num)
  have c2 : Q[8]? = some (.output 1) := by simpa [m_loop] using c 2 (by norm_num)
  have c3 : Q[9]? = some (.addNat 12 12 1) := by simpa [m_loop] using c 3 (by norm_num)
  have c4 : Q[10]? = some (.jump 6) := by simpa [m_loop] using c 4 (by norm_num)
  have inv : ∀ j ≤ k, ∃ n w', n ≤ 5 * j ∧ m_reach Q xs B n w w' ∧ w'.pc = 6 ∧
      w'.natReg = Function.update w.natReg 12 j ∧ (∀ a, a ≠ 1 → w'.fieldReg a = w.fieldReg a) ∧
      w'.out = (xs.take j).reverse ∧ w'.natOut = w.natOut := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨0, w, le_rfl, m_reach.zero _, hw.pc, ?_, fun _ _ => rfl, by simp [hw.out], rfl⟩
      funext i; by_cases hi : i = 12
      · subst hi; simp [h12]
      · simp [hi]
    | succ j ih =>
      intro hj
      obtain ⟨n, w1, hn, hr, hpc, hnr, hfr, hout, hno⟩ := ih (by omega)
      have hb1 : ∀ i, w1.natReg i ≤ B := by rw [hnr]; exact m_bnd_upd hw.bnd (by omega)
      have h8 : w1.natReg 8 = k := by rw [hnr]; simp [hw.r8]
      have h12' : w1.natReg 12 = j := by rw [hnr]; simp
      have h1 : w1.natReg 1 = 1 := by rw [hnr]; simp [hw.r1]
      have hbr : m_eff xs w1 (.branchNat 12 8 11 7) = {w1 with pc := 7} := by
        simp only [m_eff, h8, h12']; rw [if_neg (by omega)]
      refine ⟨5 + n, _, by omega, m_reach_trans hr
        (m_reach.succ _ hb1 (by rw [hpc]; exact c0) (by simp)
        (m_reach.succ (.input 1 12) (by rw [hbr]; exact hb1) (by rw [hbr]; exact c1) (by simp)
        (m_reach.succ (.output 1) (by rw [hbr]; simpa [m_eff] using hb1)
          (by rw [hbr]; simpa [m_eff] using c2) (by simp)
        (m_reach.succ (.addNat 12 12 1) (by rw [hbr]; simpa [m_eff] using hb1)
          (by rw [hbr]; simpa [m_eff] using c3) (by simp)
        (m_reach.succ (.jump 6)
          (by rw [hbr]; simp only [m_eff, h12', h1]; exact m_bnd_upd hb1 (by omega))
          (by rw [hbr]; simpa [m_eff] using c4) (by simp) (m_reach.zero _)))))), ?_, ?_, ?_, ?_, ?_⟩
      all_goals rw [hbr]
      · simp [m_eff]
      · simp only [m_eff, h12', h1, hnr]; funext i; by_cases hi : i = 12
        · subst hi; simp [hw.r1]
        · simp [hi]
      · intro a ha; simp only [m_eff]; rw [Function.update_of_ne ha]; exact hfr a ha
      · simp only [m_eff, hout]
        have hj' : j < xs.length := by omega
        have : (List.take (j + 1) xs).reverse = xs[j] :: (List.take j xs).reverse := by
          rw [List.take_add_one, List.getElem?_eq_getElem hj']; simp
        rw [h12', this, Function.update_self, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hj']; rfl
      · simpa [m_eff] using hno
  obtain ⟨n, w1, hn, hr, hpc, hnr, hfr, hout, hno⟩ := inv k le_rfl
  have hb1 : ∀ i, w1.natReg i ≤ B := by rw [hnr]; exact m_bnd_upd hw.bnd hkB
  have hbr : m_eff xs w1 (.branchNat 12 8 11 7) = {w1 with pc := 11} := by
    simp only [m_eff, hnr]; simp [hw.r8]
  refine ⟨1 + n, _, by omega, m_reach_trans hr (m_reach.succ _ hb1 (by rw [hpc]; exact c0) (by simp)
    (m_reach.zero _)), ?_⟩
  rw [hbr]
  have hr' : ∀ i, i ≠ 12 → w1.natReg i = w.natReg i := fun i hi => by rw [hnr]; simp [hi]
  exact { pc := rfl, r0 := (hr' 0 (by norm_num)).trans hw.r0, r1 := (hr' 1 (by norm_num)).trans hw.r1,
          r2 := (hr' 2 (by norm_num)).trans hw.r2, r3 := (hr' 3 (by norm_num)).trans hw.r3,
          r4 := (hr' 4 (by norm_num)).trans hw.r4, r5 := (hr' 5 (by norm_num)).trans hw.r5,
          r6 := (hr' 6 (by norm_num)).trans hw.r6, r7 := (hr' 7 (by norm_num)).trans hw.r7,
          r8 := (hr' 8 (by norm_num)).trans hw.r8, r9 := (hr' 9 (by norm_num)).trans hw.r9,
          nz := fun j c h1 h2 => (hr' _ (by simp)).trans (hw.nz j c h1 h2),
          fz := fun j c h1 h2 => (hfr _ (m_fr_ne_one h2 h1)).trans (hw.fz j c h1 h2),
          bnd := hb1,
          out := by show w1.out = _; rw [hout, List.take_of_length_le (by omega)],
          nout := hno.trans hw.nout }

theorem m_post_run {Q : Program F} {xs : List F} {B f : ℕ} (hseg : m_seg Q f (m_cmpPost f))
    {w : MachineState F} (hpc : w.pc = f) (hb : ∀ i, w.natReg i ≤ B) (h0 : w.natReg 0 = 0) :
    ∃ w', m_reach Q xs B 3 w w' ∧ Q[w'.pc]? = some .halt ∧ (∀ i, w'.natReg i ≤ B) ∧
      w'.out = (if w.natReg 9 = 0 then 1 else 0) :: w.out ∧ w'.natOut = w.natOut := by
  have c := fun r (hr : r < 7) => hseg r (by simpa [m_cmpPost] using hr)
  have c0 : Q[f]? = some (.branchNat 9 0 (f + 1) (f + 4)) := by
    simpa [m_cmpPost] using c 0 (by norm_num)
  have c1 : Q[f + 1]? = some (.constant 1 1) := by simpa [m_cmpPost] using c 1 (by norm_num)
  have c2 : Q[f + 2]? = some (.output 1) := by simpa [m_cmpPost] using c 2 (by norm_num)
  have c3 : Q[f + 3]? = some .halt := by simpa [m_cmpPost] using c 3 (by norm_num)
  have c4 : Q[f + 4]? = some (.constant 1 0) := by simpa [m_cmpPost] using c 4 (by norm_num)
  have c5 : Q[f + 5]? = some (.output 1) := by simpa [m_cmpPost] using c 5 (by norm_num)
  have c6 : Q[f + 6]? = some .halt := by simpa [m_cmpPost] using c 6 (by norm_num)
  by_cases h9 : w.natReg 9 = 0
  · have hbr : m_eff xs w (.branchNat 9 0 (f + 1) (f + 4)) = {w with pc := f + 1} := by
      simp [m_eff, h9, h0]
    refine ⟨_, m_reach.succ _ hb (by rw [hpc]; exact c0) (by simp)
      (m_reach.succ (.constant 1 1) (by rw [hbr]; exact hb) (by rw [hbr]; exact c1) (by simp)
      (m_reach.succ (.output 1) (by rw [hbr]; simpa [m_eff] using hb)
        (by rw [hbr]; simpa [m_eff] using c2) (by simp) (m_reach.zero _))), ?_, ?_, ?_, ?_⟩
    all_goals rw [hbr]
    · simpa [m_eff] using c3
    · simpa [m_eff] using hb
    · simp [m_eff, h9]
    · simp [m_eff]
  · have hbr : m_eff xs w (.branchNat 9 0 (f + 1) (f + 4)) = {w with pc := f + 4} := by
      simp [m_eff, h9, h0]
    refine ⟨_, m_reach.succ _ hb (by rw [hpc]; exact c0) (by simp)
      (m_reach.succ (.constant 1 0) (by rw [hbr]; exact hb) (by rw [hbr]; exact c4) (by simp)
      (m_reach.succ (.output 1) (by rw [hbr]; simpa [m_eff] using hb)
        (by rw [hbr]; simpa [m_eff] using c5) (by simp) (m_reach.zero _))), ?_, ?_, ?_, ?_⟩
    all_goals rw [hbr]
    · simpa [m_eff] using c6
    · simpa [m_eff] using hb
    · simp [m_eff, h9]
    · simp [m_eff]

/-! ### Part LTGMachine9 -/
def m_X {s m k : ℕ} (E : Vec F k →ₗ[F] Blocks F s m) (x : Vec F k) (i : ℕ) : List F :=
  if h : i < m then vectorData (E x ⟨i, h⟩) else []

def m_G {s b m k : ℕ} (E : Vec F k →ₗ[F] Blocks F s m) (f : Vec F s → Vec F b) (x : Vec F k)
    (i : ℕ) : List F :=
  if h : i < m then vectorData (f (E x ⟨i, h⟩)) else []

theorem m_G_flatten {s b m k : ℕ} (E : Vec F k →ₗ[F] Blocks F s m) (f : Vec F s → Vec F b)
    (x : Vec F k) : ((List.range m).map (m_G E f x)).flatten = blockData (compose E f x) := by
  unfold blockData
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [m_G, h1, compose]

theorem m_core {s b m k Tf TC Bf BC B : ℕ} (E : Vec F k →ₗ[F] Blocks F s m)
    (f : Vec F s → Vec F b) (Pf PC : Program F) (hPf : Evaluates Pf f Tf Bf)
    (hPC : EvaluatesBlocks PC (fun x => E x) TC BC)
    (md : m_Mode) (hmd : md ≠ .pc) (pre : Program F) (post : ℕ → Program F) (x : Vec F k)
    (xs o0 : List F) (hxs : ∀ a < k, xs.getD a 0 = (vectorData x).getD a 0)
    (hB1 : 1 ≤ B) (hBC : BC ≤ B) (hBCa : (BC + 1) * (m + 3) ≤ B) (hBf : Bf ≤ B)
    (hBfa : (Bf + 1) * (m + 3) ≤ B) (hk : k ≤ B) (hD : m * s * (m + 3) ≤ B)
    (hIK : k + m * b ≤ B) (hRES : m + 3 ≤ B)
    {w : MachineState F}
    (hw : m_Ready (m + 3) (if m = 0 then 0 else s) k B (6 + pre.length) o0 w) :
    ∃ n w', n + 8 * programSize PC + m * (8 * programSize Pf) ≤ 8 * TC + m * (8 * Tf + 2) ∧
      m_reach (m_prog m (if m = 0 then 0 else s) k md pre post PC Pf) xs B n w w' ∧
      m_CInv m (if m = 0 then 0 else s) k b B
        (6 + pre.length + 8 * PC.length + (8 * Pf.length + 2) * m) m md o0 xs
        (blockData (E x)) (m_G E f x) w' := by
  obtain ⟨-, -, hsC, hsCp, -⟩ := m_prog_segs m (if m = 0 then 0 else s) k md pre post PC Pf
  obtain ⟨n1, w1, hn1, hr1, hw1⟩ := m_pc_phase (b := b) (G := m_G E f x) hmd hsC
    (by obtain ⟨t, z, h1, h2, h3, -⟩ := hPC x; exact ⟨t, z, h1, h2, h3⟩)
    (m_blockData_length _) hxs
    (fun a ha => by rw [m_vectorData_getD, dif_neg (by omega)]) hB1 hBC hBCa hk hD hw
  obtain ⟨n2, w2, hn2, hr2, hw2⟩ := m_copies_phase (X := m_X E x) hmd
    (fun h => by rw [if_neg (by omega)]) hsCp
    (fun i hi => by
      obtain ⟨t, z, h1, h2, h3, -⟩ := hPf (E x ⟨i, hi⟩)
      exact ⟨t, z, h1, by simpa [m_X, hi] using h2, by simpa [m_G, hi] using h3⟩)
    (fun i hi => by simp [m_G, hi, vectorData])
    (fun i hi a ha => by
      rw [m_X, dif_pos hi, m_vectorData_getD, dif_pos ha]
      exact m_blockData_getD (E x) ⟨i, hi⟩ ⟨a, ha⟩)
    (fun i hi a ha => by rw [m_X, dif_pos hi, m_vectorData_getD, dif_neg (by omega)])
    (by rw [m_blockData_length]) hB1 hBf hBfa hD hIK hRES hw1 m le_rfl
  exact ⟨n2 + n1, w2, by omega, m_reach_trans hr1 hr2, hw2⟩

theorem m_setup_size (M s' k : ℕ) :
    programSize (m_setup (F := F) M s' k) ≤ 14 + M + s' + 2 * k := by
  simp only [m_setup, programSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    instructionSize]
  have h1 := Nat.log2_le_self M
  have h2 := Nat.log2_le_self s'
  have h3 := Nat.log2_le_self k
  have h4 : Nat.log2 1 = 0 := by decide
  have h5 : Nat.log2 2 = 1 := by decide
  omega

theorem m_prog_size (m s' k : ℕ) (md : m_Mode) (pre : Program F) (post : ℕ → Program F)
    (PC Pf : Program F) :
    programSize (m_prog m s' k md pre post PC Pf) ≤ 14 + (m + 3) + s' + 2 * k +
      programSize pre + 8 * programSize PC + m * (8 * programSize Pf + 2) +
      programSize (post (6 + pre.length + 8 * PC.length + (8 * Pf.length + 2) * m)) := by
  simp only [m_prog, m_programSize_append]
  have := m_setup_size (F := F) (m + 3) s' k
  have := m_trP_size (m + 3) 2 (6 + pre.length) (6 + pre.length + 8 * PC.length) .pc PC
  have := m_copies_size m (6 + pre.length + 8 * PC.length) md Pf
  omega

theorem m_finish {Q : Program F} {xs : List F} {B n : ℕ} {w : MachineState F}
    (h : m_reach Q xs B n initialState w) (hq : Q[w.pc]? = some .halt)
    (hb : ∀ i, w.natReg i ≤ B) : runFrom Q [] xs B (n + 1) initialState = some w := by
  rw [m_runFrom_of_reach h 1]; exact m_runFrom_halt hb hq

/-! ### Part LTGMachine -/
theorem m_cmp_iff {F : Type} [Field F] {s b m k : ℕ} (E : Vec F k →ₗ[F] Blocks F s m)
    (f : Vec F s → Vec F b) (x : Vec F k) (y : Blocks F b m) :
    (∀ j < m, ∀ t < b, (m_G E f x j).getD t 0 =
      (vectorData x ++ blockData y).getD (k + j * b + t) 0) ↔ y = compose E f x := by
  have hx : (vectorData x).length = k := by simp [vectorData]
  have key : ∀ j (hj : j < m) t (ht : t < b),
      ((m_G E f x j).getD t 0 = (vectorData x ++ blockData y).getD (k + j * b + t) 0 ↔
        compose E f x ⟨j, hj⟩ ⟨t, ht⟩ = y ⟨j, hj⟩ ⟨t, ht⟩) := by
    intro j hj t ht
    rw [m_G, dif_pos hj, m_vectorData_getD, dif_pos ht,
      List.getD_append_right _ _ _ _ (by omega), hx,
      show k + j * b + t - k = j * b + t by omega]
    rw [show j * b + t = (⟨j, hj⟩ : Fin m) * b + (⟨t, ht⟩ : Fin b) from rfl, m_blockData_getD]
    rfl
  constructor
  · intro h
    funext j t
    exact ((key j j.2 t t.2).mp (h j j.2 t t.2)).symm
  · rintro rfl j hj t ht
    exact (key j hj t ht).mpr rfl

/-- The machine half of Theorem 8: composing an encoder program and a local evaluator. -/
theorem machine : ∃ K : ℕ, 0 < K ∧ ∀ (F : Type) [Field F] (s b m k : ℕ)
    (E : Vec F k →ₗ[F] Blocks F s m) (f : Vec F s → Vec F b)
    (Pf PC : Program F) (Tf TC Bf BC : ℕ), k ≤ s * m →
    Evaluates Pf f Tf Bf → EvaluatesBlocks PC (fun x => E x) TC BC →
    ∃ (Pg PI PM : Program F) (B : ℕ),
      B ≤ (Bf + BC + TC + m*Tf + k + b*m + s*m + 2)^K ∧
      GraphAlgorithms (compose E f) Pg PI PM (K*(TC + m*Tf)) B := by

  refine ⟨100, by norm_num, ?_⟩
  intro F _ s b m k E f Pf PC Tf TC Bf BC hk hPf hPC
  obtain ⟨tC, zC, htC, hrC, hoC, -⟩ := hPC 0
  have hPCpos := m_programSize_pos hrC
  have hmsT : m * s ≤ tC := by
    have := (m_runFrom_out tC _ _ hrC).2
    rw [← List.length_reverse, hoC, m_blockData_length] at this
    simpa [initialState] using this
  obtain ⟨tf, zf, htf, hrf, -, -⟩ := hPf 0
  have hPfpos := m_programSize_pos hrf
  have hTf : 1 ≤ Tf := by omega
  have hTC : 1 + m * s ≤ TC := by omega
  have hmTf : m ≤ m * Tf := Nat.le_mul_of_pos_right m hTf
  have hsm : s * m = m * s := Nat.mul_comm _ _
  have hbm : b * m = m * b := Nat.mul_comm _ _
  have hkms : k ≤ m * s := by rw [← hsm]; exact hk
  set X := Bf + BC + TC + m*Tf + k + b*m + s*m + 2 with hX
  have hX1 : 1 ≤ X := by omega
  have hXX : X ≤ X * X := Nat.le_mul_of_pos_left X (by omega)
  have hM : m + 3 ≤ X := by omega
  have hB1 : 1 ≤ X * X := by omega
  have hB2 : 2 ≤ X * X := by omega
  have hBC : BC ≤ X * X := by omega
  have hBCa : (BC + 1) * (m + 3) ≤ X * X := Nat.mul_le_mul (by omega) hM
  have hBf : Bf ≤ X * X := by omega
  have hBfa : (Bf + 1) * (m + 3) ≤ X * X := Nat.mul_le_mul (by omega) hM
  have hk' : k ≤ X * X := by omega
  have hD : m * s * (m + 3) ≤ X * X := Nat.mul_le_mul (by omega) hM
  have hIK : k + m * b ≤ X * X := by omega
  have hRES : m + 3 ≤ X * X := by omega
  have hs'ms : (if m = 0 then 0 else s) ≤ m * s := by
    split_ifs with h
    · omega
    · exact Nat.le_mul_of_pos_left s (by omega)
  have hs'B : (if m = 0 then 0 else s) ≤ X * X := by omega
  have e1 : m * (8 * programSize Pf + 2) = m * (8 * programSize Pf) + 2 * m := by ring
  have e2 : m * (8 * Tf + 2) = 8 * (m * Tf) + 2 * m := by ring
  have e3 : 100 * (TC + m * Tf) = 100 * TC + 100 * (m * Tf) := by ring
  have hsz := m_prog_size (F := F) m (if m = 0 then 0 else s) k
  refine ⟨m_prog m (if m = 0 then 0 else s) k .fd [] (fun _ => [.halt]) PC Pf,
    m_prog m (if m = 0 then 0 else s) k .fd m_loop (fun _ => [.halt]) PC Pf,
    m_prog m (if m = 0 then 0 else s) k .fc [] m_cmpPost PC Pf, X * X, ?_, ?_⟩
  · calc X * X = X ^ 2 := by ring
      _ ≤ X ^ 100 := Nat.pow_le_pow_right hX1 (by norm_num)
  · unfold GraphAlgorithms
    refine ⟨?_, ?_, ?_⟩
    · intro x
      obtain ⟨hs0, -, -, -, hpost⟩ :=
        m_prog_segs m (if m = 0 then 0 else s) k .fd [] (fun _ => [.halt]) PC Pf
      obtain ⟨w0, hr0, hw0, -⟩ := m_setup_run (xs := vectorData x) hs0 hRES hs'B hk' hB2
        (by omega)
      obtain ⟨n, w1, hn, hr1, hw1⟩ := m_core E f Pf PC hPf hPC .fd (by simp) []
        (fun _ => [.halt]) x (vectorData x) [] (fun a _ => rfl) hB1 hBC hBCa hBf hBfa hk' hD
        hIK hRES (by simpa using hw0)
      refine ⟨n + 6 + 1, w1, ?_, m_finish (m_reach_trans hr0 hr1)
        (by rw [hw1.pc]; simpa using hpost 0 (by simp))
        hw1.bnd, ?_, ?_⟩
      · have := hsz .fd [] (fun _ => [.halt]) PC Pf
        rw [show programSize ([] : Program F) = 0 from rfl,
          show programSize [(Instruction.halt : Instruction F)] = 1 from rfl] at this
        omega
      · have := hw1.out
        simp only [m_cout] at this
        rw [this, m_G_flatten]; simp
      · rw [hw1.nout]; rfl
    · intro x
      obtain ⟨hs0, hpre, -, -, hpost⟩ :=
        m_prog_segs m (if m = 0 then 0 else s) k .fd m_loop (fun _ => [.halt]) PC Pf
      obtain ⟨w0, hr0, hw0, h12⟩ := m_setup_run (xs := vectorData x) hs0 hRES hs'B hk' hB2
        (by omega)
      obtain ⟨nl, wl, hnl, hrl, hwl⟩ := m_loop_run (xs := vectorData x) hpre (by simp [vectorData]) hk' (by omega)
        hw0 h12
      obtain ⟨n, w1, hn, hr1, hw1⟩ := m_core E f Pf PC hPf hPC .fd (by simp) m_loop
        (fun _ => [.halt]) x (vectorData x) (vectorData x).reverse (fun a _ => rfl) hB1 hBC hBCa
        hBf hBfa hk' hD hIK hRES (by simpa [m_loop] using hwl)
      refine ⟨n + (nl + 6) + 1, w1, ?_,
        m_finish (m_reach_trans (m_reach_trans hr0 hrl) hr1)
          (by rw [hw1.pc]; simpa using hpost 0 (by simp))
        hw1.bnd, ?_, ?_⟩
      · have := hsz .fd m_loop (fun _ => [.halt]) PC Pf
        rw [show programSize (m_loop : Program F) = 5 from rfl,
          show programSize [(Instruction.halt : Instruction F)] = 1 from rfl] at this
        omega
      · have := hw1.out
        simp only [m_cout] at this
        rw [this, m_G_flatten]; simp
      · rw [hw1.nout]; rfl
    · intro x y
      obtain ⟨hs0, -, -, -, hpost⟩ :=
        m_prog_segs m (if m = 0 then 0 else s) k .fc [] m_cmpPost PC Pf
      have hxs : ∀ a < k, (vectorData x ++ blockData y).getD a 0 = (vectorData x).getD a 0 :=
        fun a ha => List.getD_append _ _ _ _ (by simpa [vectorData] using ha)
      obtain ⟨w0, hr0, hw0, -⟩ := m_setup_run (xs := vectorData x ++ blockData y) hs0 hRES hs'B
        hk' hB2 (by omega)
      obtain ⟨n, w1, hn, hr1, hw1⟩ := m_core E f Pf PC hPf hPC .fc (by simp) [] m_cmpPost x
        (vectorData x ++ blockData y) [] hxs hB1 hBC hBCa hBf hBfa hk' hD hIK hRES
        (by simpa using hw0)
      obtain ⟨w2, hr2, hq, hb2, hout2, hno2⟩ := m_post_run hpost (by simpa using hw1.pc)
        hw1.bnd hw1.r0
      refine ⟨3 + (n + 6) + 1, w2, ?_,
        m_finish (m_reach_trans (m_reach_trans hr0 hr1) hr2) hq hb2, ?_, ?_⟩
      · have := hsz .fc [] m_cmpPost PC Pf
        rw [show programSize ([] : Program F) = 0 from rfl,
          show ∀ f, programSize (m_cmpPost (F := F) f) = 7 from fun _ => rfl] at this
        omega
      · have ho := hw1.out
        simp only [m_cout] at ho
        rw [hout2, ho.1]
        have hiff := ho.2.2.trans (m_cmp_iff E f x y)
        by_cases h : y = compose E f x
        · rw [if_pos (hiff.mpr h), if_pos h]; rfl
        · rw [if_neg (mt hiff.mp h), if_neg h]; rfl
      · rw [hno2, hw1.nout]; rfl

end SubspaceEvasion312.Explicit.Dev.LTG
end
end

section
set_option autoImplicit false

namespace SubspaceEvasion312.Explicit.Dev.LTGA
open SubspaceEvasion312.Explicit
open scoped ENNReal

/-- A set all of whose finite subsets have at most `L` elements is finite with `ncard ≤ L`. -/
theorem fin_of_finsets {α : Type} (A : Set α) (L : ℕ)
    (h : ∀ T : Finset α, (↑T : Set α) ⊆ A → T.card ≤ L) : A.Finite ∧ A.ncard ≤ L := by
  have hfin : A.Finite := by
    by_contra hinf
    obtain ⟨t, ht, hc⟩ := Set.Infinite.exists_subset_card_eq hinf (L + 1)
    have := h t ht
    omega
  refine ⟨hfin, ?_⟩
  have := h hfin.toFinset (by simp)
  rwa [Set.ncard_eq_toFinset_card A hfin]

theorem injective_of_encoder {F : Type} [Field F] {s m k : ℕ}
    (C : Code F s m) (E : Vec F k →ₗ[F] Blocks F s m) (hE : IsEncoder C E) :
    Function.Injective E := by
  obtain ⟨hk, hr⟩ := hE
  have h1 := LinearMap.finrank_range_add_finrank_ker E
  rw [hr, ← hk, Module.finrank_fin_fun] at h1
  have h2 : Module.finrank F (LinearMap.ker E) = 0 := by omega
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.mp h2

theorem k_le {F : Type} [Field F] {s m k : ℕ}
    (C : Code F s m) (E : Vec F k →ₗ[F] Blocks F s m) (hE : IsEncoder C E) :
    k ≤ s * m := by
  obtain ⟨hk, _⟩ := hE
  have := Submodule.finrank_le C
  have h2 : Module.finrank F (Blocks F s m) = s * m := by
    rw [Module.finrank_pi_fintype]; simp [mul_comm]
  omega

/-- The coordinate map `(x, y) ↦ (E x i, y i)`. -/
noncomputable def coordMap {F : Type} [Field F] {s b m k : ℕ}
    (E : Vec F k →ₗ[F] Blocks F s m) (i : Fin m) :
    (Vec F k × Blocks F b m) →ₗ[F] (Vec F s × Vec F b) :=
  LinearMap.prod ((LinearMap.proj i).comp (E.comp (LinearMap.fst F _ _)))
    ((LinearMap.proj i).comp (LinearMap.snd F _ _))

/-- The codeword map `(x, y) ↦ E x`. -/
noncomputable def cwMap {F : Type} [Field F] {s b m k : ℕ}
    (E : Vec F k →ₗ[F] Blocks F s m) :
    (Vec F k × Blocks F b m) →ₗ[F] Blocks F s m :=
  E.comp (LinearMap.fst F _ _)

theorem evasive_compose {F : Type} [Field F] {s b m k r c L : ℕ}
    (C : Code F s m) (E : Vec F k →ₗ[F] Blocks F s m)
    (f : Vec F s → Vec F b) (hE : IsEncoder C E)
    (hf : Evasive (F := F) (graph f) r c) (hC : ListRecoverable C r 0 c L) :
    Evasive (F := F) (graph (compose E f)) r L := by
  classical
  have hinj := injective_of_encoder C E hE
  intro U hU
  -- the per-coordinate lists
  have hW : ∀ i : Fin m, Module.finrank F (U.map (coordMap (b := b) E i)) ≤ r :=
    fun i => (Submodule.finrank_map_le _ _).trans hU
  have hfi := fun i => hf _ (hW i)
  let S : Fin m → Finset (Vec F s) := fun i => (hfi i).1.toFinset.image Prod.fst
  have hS : ∀ i, (S i).card ≤ c := by
    intro i
    refine (Finset.card_image_le).trans ?_
    rw [← Set.ncard_eq_toFinset_card _ (hfi i).1]
    exact (hfi i).2
  let U' : Submodule F (Blocks F s m) := U.map (cwMap (b := b) E)
  have hU' : Module.finrank F U' ≤ r := (Submodule.finrank_map_le _ _).trans hU
  apply fin_of_finsets
  intro T hT
  have hinjOn : Set.InjOn (cwMap (b := b) E) (↑T : Set _) := by
    intro z hz w hw hzw
    have hz' := (hT hz).1
    have hw' := (hT hw).1
    have h1 : z.1 = w.1 := hinj hzw
    have hz2 : z.2 = compose E f z.1 := hz'
    have hw2 : w.2 = compose E f w.1 := hw'
    exact Prod.ext h1 (by rw [hz2, hw2, h1])
  have hsub : (↑(T.image (cwMap (b := b) E)) : Set _) ⊆ recovered C U' S 0 := by
    intro v hv
    simp only [Finset.coe_image] at hv
    obtain ⟨z, hz, rfl⟩ := hv
    have hzg : z.2 = compose E f z.1 := (hT hz).1
    have hzU : z ∈ U := (hT hz).2
    refine ⟨?_, ?_, cwMap E z, ?_, ?_⟩
    · rw [← hE.2]; exact ⟨z.1, rfl⟩
    · exact ⟨z, hzU, rfl⟩
    · intro i
      simp only [S, Finset.mem_image, Set.Finite.mem_toFinset]
      refine ⟨coordMap E i z, ⟨?_, ⟨z, hzU, rfl⟩⟩, rfl⟩
      show (z.2 i) = f (E z.1 i)
      rw [hzg]; rfl
    · simp [hamming]
  have := hC U' hU' S hS _ hsub
  rw [Finset.card_image_of_injOn hinjOn] at this
  exact_mod_cast this

end SubspaceEvasion312.Explicit.Dev.LTGA

namespace SubspaceEvasion312.Explicit
open scoped ENNReal

theorem chk_local_to_global :
    ∃ K : ℕ, 0 < K ∧
    ∀ (F : Type) [Field F] (s b m k r c L : ℕ)
      (C : Code F s m) (E : Vec F k →ₗ[F] Blocks F s m)
      (f : Vec F s → Vec F b),
      IsEncoder C E → Evasive (F := F) (graph f) r c → ListRecoverable C r 0 c L →
      Function.Injective E ∧ Evasive (F := F) (graph (compose E f)) r L ∧
      (∃ e : Vec F k ≃ graph (compose E f), ∀ x, (e x).val = (x, compose E f x)) ∧
      (∀ [Fintype F], (graph (compose E f)).ncard = (Fintype.card F)^k ∧
        ∀ (Pf PC : Program F) (Tf TC Bf BC : ℕ),
          Evaluates Pf f Tf Bf → EvaluatesBlocks PC (fun x => E x) TC BC →
          ∃ (Pg PI PM : Program F) (B : ℕ),
            B ≤ (Bf + BC + TC + m*Tf + k + b*m + s*m + 2)^K ∧
            GraphAlgorithms (compose E f) Pg PI PM (K*(TC + m*Tf)) B) := by
  obtain ⟨K, hK, hM⟩ := Dev.LTG.machine
  refine ⟨K, hK, ?_⟩
  intro F _ s b m k r c L C E f hE hf hC
  refine ⟨Dev.LTGA.injective_of_encoder C E hE,
    Dev.LTGA.evasive_compose C E f hE hf hC, ⟨graphEquiv (compose E f), fun _ => rfl⟩, ?_⟩
  intro _
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, ← Nat.card_congr (graphEquiv (compose E f))]
    simp
  · intro Pf PC Tf TC Bf BC hPf hPC
    exact hM F s b m k E f Pf PC Tf TC Bf BC (Dev.LTGA.k_le C E hE) hPf hPC

end SubspaceEvasion312.Explicit
end

theorem solution : type_of% @SubspaceEvasion312.Explicit.chk_local_to_global := @SubspaceEvasion312.Explicit.chk_local_to_global

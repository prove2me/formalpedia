-- Prove2me | solution 1 for SmaleNinth.ram_to_bss_quadratic_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T19:14:46.383452+00:00
-- url     : https://prove2.me/submissions/df78fe20-86d9-4d63-8907-be44a3be1f24

import Definitions.Def_SmaleNinth_BSSMachine
import Definitions.Def_SmaleNinth_RealRAM
import Mathlib.Tactic

/-!
# Compiling the real pointer machine to the tape machine with quadratic overhead

For every RAM program `R` we build a tape program `compile R` and a constant
`K` such that whenever `R` decides an input `x` (vanishing on the negative
cells) in `T` steps, `compile R` decides `x` in `K (T+1)²` steps.

Architecture.  The tape is kept in the shape `physZ Z H d r`: the logical
memory `d` of the RAM is stored on the tape, the tape head sits at logical
address `H` (physical cell `0`), and a register zone of `Z` cells
`-1 … -Z` travels with the head (data left of the head is displaced by `Z`
cells).  The zone holds the `k` RAM registers, the `q` pointer registers
(as real numbers), the current head address `H`, and two scratch cells.
Moving the head by one cell is a `shiftL`/`shiftR` followed by `Z` `mov`s
that put the zone back in place (`rightChain`, `leftChain`, cost `2Z+1`).

A `load`/`store` instruction is compiled to a *walk*: a loop that moves the
head from `H` to the pointer value `p` (cost `(2Z+8)|p-H|+5`), then the
memory access, and the zone cell holding `H` is updated to `p`.  All other
RAM instructions compile to `O(1)` zone-register instructions.  Since the
pointers of a `t`-step run are bounded by `K0 + t` (they change by at most
one per step and constants are bounded by `K0`), each simulated step costs
at most `(2Z+8)·2(K0+T) + 4Z+23`, and the whole run costs `≤ K (T+1)²`.

The invariant `Sim R s H c` (program counter at the start of the block of
`s.pc`, tape of the form `physZ Z H s.mem r` with the zone `r` holding the
registers and pointers) is preserved by one RAM step (`sim_step`) and
propagated along the run (`sim_run`); halting is read off the `accept` /
`reject` blocks.
-/

open SmaleNinth

namespace SmaleNinth.BSS


/-- `Reaches P s₁ s₂ b`: from `s₁` the machine reaches `s₂` within `b` steps. -/
def Reaches (P : BSSProgram) (s₁ s₂ : BSSConfig) (b : ℕ) : Prop :=
  ∃ t ≤ b, (BSSStep P)^[t] s₁ = s₂

lemma Reaches.refl (P : BSSProgram) (s : BSSConfig) : Reaches P s s 0 := ⟨0, le_rfl, rfl⟩

lemma Reaches.trans {P : BSSProgram} {s₁ s₂ s₃ : BSSConfig} {b₁ b₂ : ℕ}
    (h₁ : Reaches P s₁ s₂ b₁) (h₂ : Reaches P s₂ s₃ b₂) : Reaches P s₁ s₃ (b₁ + b₂) := by
  obtain ⟨t₁, ht₁, rfl⟩ := h₁
  obtain ⟨t₂, ht₂, rfl⟩ := h₂
  exact ⟨t₂ + t₁, by omega, by rw [Function.iterate_add_apply]⟩

lemma Reaches.mono {P : BSSProgram} {s₁ s₂ : BSSConfig} {b b' : ℕ}
    (h : Reaches P s₁ s₂ b) (hb : b ≤ b') : Reaches P s₁ s₂ b' := by
  obtain ⟨t, ht, h⟩ := h
  exact ⟨t, le_trans ht hb, h⟩

lemma Reaches.single {P : BSSProgram} {s₁ s₂ : BSSConfig} (h : BSSStep P s₁ = s₂) :
    Reaches P s₁ s₂ 1 := ⟨1, le_rfl, by simpa using h⟩

lemma Reaches.cast {P : BSSProgram} {s₁ s₂ s₂' : BSSConfig} {b : ℕ}
    (h : Reaches P s₁ s₂ b) (e : s₂ = s₂') : Reaches P s₁ s₂' b := e ▸ h

/-! ### Single-step lemmas -/

lemma step_const {P : BSSProgram} {pc : ℕ} {dst : ℤ} {c : ℝ}
    (h : P[pc]? = some (.const dst c)) (τ : ℤ → ℝ) :
    BSSStep P ⟨pc, τ⟩ = ⟨pc + 1, Function.update τ dst c⟩ := by
  simp [BSSStep, h]

lemma step_add {P : BSSProgram} {pc : ℕ} {dst i j : ℤ}
    (h : P[pc]? = some (.add dst i j)) (τ : ℤ → ℝ) :
    BSSStep P ⟨pc, τ⟩ = ⟨pc + 1, Function.update τ dst (τ i + τ j)⟩ := by
  simp [BSSStep, h]

lemma step_sub {P : BSSProgram} {pc : ℕ} {dst i j : ℤ}
    (h : P[pc]? = some (.sub dst i j)) (τ : ℤ → ℝ) :
    BSSStep P ⟨pc, τ⟩ = ⟨pc + 1, Function.update τ dst (τ i - τ j)⟩ := by
  simp [BSSStep, h]

lemma step_div {P : BSSProgram} {pc : ℕ} {dst i j : ℤ}
    (h : P[pc]? = some (.div dst i j)) (τ : ℤ → ℝ) :
    BSSStep P ⟨pc, τ⟩ = ⟨pc + 1, Function.update τ dst (τ i / τ j)⟩ := by
  simp [BSSStep, h]

lemma step_shiftL {P : BSSProgram} {pc : ℕ} (h : P[pc]? = some .shiftL) (τ : ℤ → ℝ) :
    BSSStep P ⟨pc, τ⟩ = ⟨pc + 1, fun k => τ (k + 1)⟩ := by
  simp [BSSStep, h]

lemma step_shiftR {P : BSSProgram} {pc : ℕ} (h : P[pc]? = some .shiftR) (τ : ℤ → ℝ) :
    BSSStep P ⟨pc, τ⟩ = ⟨pc + 1, fun k => τ (k - 1)⟩ := by
  simp [BSSStep, h]

lemma step_jle_of_le {P : BSSProgram} {pc : ℕ} {i : ℤ} {target : ℕ}
    (h : P[pc]? = some (.jle i target)) (τ : ℤ → ℝ) (hτ : τ i ≤ 0) :
    BSSStep P ⟨pc, τ⟩ = ⟨target, τ⟩ := by
  simp [BSSStep, h, hτ]

lemma step_jle_of_pos {P : BSSProgram} {pc : ℕ} {i : ℤ} {target : ℕ}
    (h : P[pc]? = some (.jle i target)) (τ : ℤ → ℝ) (hτ : 0 < τ i) :
    BSSStep P ⟨pc, τ⟩ = ⟨pc + 1, τ⟩ := by
  simp [BSSStep, h, not_le.mpr hτ]

/-- A `mov dst ← src` macro: `const dst 0` followed by `add dst dst src`. -/
lemma reaches_mov {P : BSSProgram} {pc : ℕ} {dst src : ℤ}
    (h0 : P[pc]? = some (.const dst 0)) (h1 : P[pc + 1]? = some (.add dst dst src))
    (hne : dst ≠ src) (τ : ℤ → ℝ) :
    Reaches P ⟨pc, τ⟩ ⟨pc + 2, Function.update τ dst (τ src)⟩ 2 := by
  have e1 := step_const h0 τ
  have e2 := step_add h1 (Function.update τ dst 0)
  refine ⟨2, le_rfl, ?_⟩
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  rw [e1, e2]
  congr 1
  rw [Function.update_self, Function.update_of_ne hne.symm, zero_add, Function.update_idem]


end SmaleNinth.BSS

/-! ## Layer: CP_Core -/

namespace SmaleNinth.CP

open SmaleNinth.BSS


/-! ### The physical tape with a zone of width `Z` -/

/-- Physical tape with head at logical `h`, data `d`, zone `r` on cells `-1 … -Z`;
data left of the head is displaced by `Z`. -/
def physZ (Z : ℕ) (h : ℤ) (d r : ℤ → ℝ) : ℤ → ℝ := fun k =>
  if 0 ≤ k then d (h + k) else if -(Z : ℤ) ≤ k then r k else d (h + k + Z)

lemma physZ_nonneg {Z : ℕ} {h : ℤ} {d r : ℤ → ℝ} {k : ℤ} (hk : 0 ≤ k) :
    physZ Z h d r k = d (h + k) := by simp [physZ, hk]

lemma physZ_zero (Z : ℕ) (h : ℤ) (d r : ℤ → ℝ) : physZ Z h d r 0 = d h := by simp [physZ]

lemma physZ_reg {Z : ℕ} {h : ℤ} {d r : ℤ → ℝ} {k : ℤ} (hk1 : -(Z : ℤ) ≤ k) (hk2 : k < 0) :
    physZ Z h d r k = r k := by simp [physZ, hk1, not_le.mpr hk2]

lemma physZ_lt {Z : ℕ} {h : ℤ} {d r : ℤ → ℝ} {k : ℤ} (hk : k < -(Z : ℤ)) :
    physZ Z h d r k = d (h + k + Z) := by
  simp [physZ, show ¬ (0 ≤ k) by omega, show ¬ (-(Z : ℤ) ≤ k) by omega]

lemma update_physZ_reg {Z : ℕ} {h : ℤ} {d r : ℤ → ℝ} {j : ℤ} (hj1 : -(Z : ℤ) ≤ j) (hj2 : j < 0)
    (v : ℝ) : Function.update (physZ Z h d r) j v = physZ Z h d (Function.update r j v) := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [physZ_reg hj1 hj2]
  · rw [Function.update_of_ne hk]
    unfold physZ
    rw [Function.update_of_ne hk]

lemma update_physZ_head {Z : ℕ} {h : ℤ} {d r : ℤ → ℝ} (v : ℝ) :
    Function.update (physZ Z h d r) 0 v = physZ Z h (Function.update d h v) r := by
  funext k
  by_cases hk : k = 0
  · subst hk; simp [physZ]
  · rw [Function.update_of_ne hk]
    unfold physZ
    split_ifs with h1 h2
    · rw [Function.update_of_ne (by omega)]
    · rfl
    · rw [Function.update_of_ne (by omega)]

lemma physZ_ext {Z : ℕ} {h : ℤ} {d r r' : ℤ → ℝ}
    (e : ∀ k, -(Z : ℤ) ≤ k → k < 0 → r k = r' k) : physZ Z h d r = physZ Z h d r' := by
  funext k; unfold physZ
  split_ifs with h1 h2
  · rfl
  · exact e k h2 (by omega)
  · rfl

lemma step_mul' {P : BSSProgram} {pc : ℕ} {dst i j : ℤ}
    (h : P[pc]? = some (.mul dst i j)) (τ : ℤ → ℝ) :
    BSSStep P ⟨pc, τ⟩ = ⟨pc + 1, Function.update τ dst (τ i * τ j)⟩ := by
  simp [BSSStep, h]

/-! ### Register-level instruction lemmas -/

section RegLemmas
variable {P : BSSProgram} {pc : ℕ} {Z : ℕ}

lemma reachesZ_const {j : ℤ} {c : ℝ} (hP : P[pc]? = some (.const j c))
    (hj1 : -(Z : ℤ) ≤ j) (hj2 : j < 0) (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨pc, physZ Z h d r⟩ ⟨pc + 1, physZ Z h d (Function.update r j c)⟩ 1 :=
  Reaches.single (by rw [step_const hP, update_physZ_reg hj1 hj2])

lemma reachesZ_sub {j a b : ℤ} (hP : P[pc]? = some (.sub j a b))
    (hj1 : -(Z : ℤ) ≤ j) (hj2 : j < 0) (ha1 : -(Z : ℤ) ≤ a) (ha2 : a < 0)
    (hb1 : -(Z : ℤ) ≤ b) (hb2 : b < 0) (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨pc, physZ Z h d r⟩ ⟨pc + 1, physZ Z h d (Function.update r j (r a - r b))⟩ 1 :=
  Reaches.single (by
    rw [step_sub hP, physZ_reg ha1 ha2, physZ_reg hb1 hb2, update_physZ_reg hj1 hj2])

lemma reachesZ_add {j a b : ℤ} (hP : P[pc]? = some (.add j a b))
    (hj1 : -(Z : ℤ) ≤ j) (hj2 : j < 0) (ha1 : -(Z : ℤ) ≤ a) (ha2 : a < 0)
    (hb1 : -(Z : ℤ) ≤ b) (hb2 : b < 0) (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨pc, physZ Z h d r⟩ ⟨pc + 1, physZ Z h d (Function.update r j (r a + r b))⟩ 1 :=
  Reaches.single (by
    rw [step_add hP, physZ_reg ha1 ha2, physZ_reg hb1 hb2, update_physZ_reg hj1 hj2])

lemma reachesZ_mul {j a b : ℤ} (hP : P[pc]? = some (.mul j a b))
    (hj1 : -(Z : ℤ) ≤ j) (hj2 : j < 0) (ha1 : -(Z : ℤ) ≤ a) (ha2 : a < 0)
    (hb1 : -(Z : ℤ) ≤ b) (hb2 : b < 0) (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨pc, physZ Z h d r⟩ ⟨pc + 1, physZ Z h d (Function.update r j (r a * r b))⟩ 1 :=
  Reaches.single (by
    rw [step_mul' hP, physZ_reg ha1 ha2, physZ_reg hb1 hb2, update_physZ_reg hj1 hj2])

lemma reachesZ_div {j a b : ℤ} (hP : P[pc]? = some (.div j a b))
    (hj1 : -(Z : ℤ) ≤ j) (hj2 : j < 0) (ha1 : -(Z : ℤ) ≤ a) (ha2 : a < 0)
    (hb1 : -(Z : ℤ) ≤ b) (hb2 : b < 0) (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨pc, physZ Z h d r⟩ ⟨pc + 1, physZ Z h d (Function.update r j (r a / r b))⟩ 1 :=
  Reaches.single (by
    rw [step_div hP, physZ_reg ha1 ha2, physZ_reg hb1 hb2, update_physZ_reg hj1 hj2])

lemma reachesZ_mov_reg {j s : ℤ} (h0 : P[pc]? = some (.const j 0))
    (h1 : P[pc + 1]? = some (.add j j s)) (hj1 : -(Z : ℤ) ≤ j) (hj2 : j < 0)
    (hs1 : -(Z : ℤ) ≤ s) (hs2 : s < 0) (hne : j ≠ s) (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨pc, physZ Z h d r⟩ ⟨pc + 2, physZ Z h d (Function.update r j (r s))⟩ 2 :=
  (reaches_mov h0 h1 hne _).cast (by rw [physZ_reg hs1 hs2, update_physZ_reg hj1 hj2])

lemma reachesZ_mov_head {j : ℤ} (h0 : P[pc]? = some (.const j 0))
    (h1 : P[pc + 1]? = some (.add j j 0)) (hj1 : -(Z : ℤ) ≤ j) (hj2 : j < 0)
    (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨pc, physZ Z h d r⟩ ⟨pc + 2, physZ Z h d (Function.update r j (d h))⟩ 2 :=
  (reaches_mov h0 h1 (by omega) _).cast (by rw [physZ_zero, update_physZ_reg hj1 hj2])

lemma reachesZ_store {s : ℤ} (h0 : P[pc]? = some (.const 0 0))
    (h1 : P[pc + 1]? = some (.add 0 0 s)) (hs1 : -(Z : ℤ) ≤ s) (hs2 : s < 0)
    (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨pc, physZ Z h d r⟩ ⟨pc + 2, physZ Z h (Function.update d h (r s)) r⟩ 2 :=
  (reaches_mov h0 h1 (by omega) _).cast (by rw [physZ_reg hs1 hs2, update_physZ_head])

lemma reachesZ_jle_le {j : ℤ} {target : ℕ} (hP : P[pc]? = some (.jle j target))
    (hj1 : -(Z : ℤ) ≤ j) (hj2 : j < 0) (h : ℤ) (d r : ℤ → ℝ) (hr : r j ≤ 0) :
    Reaches P ⟨pc, physZ Z h d r⟩ ⟨target, physZ Z h d r⟩ 1 :=
  Reaches.single (step_jle_of_le hP _ (by rw [physZ_reg hj1 hj2]; exact hr))

lemma reachesZ_jle_pos {j : ℤ} {target : ℕ} (hP : P[pc]? = some (.jle j target))
    (hj1 : -(Z : ℤ) ≤ j) (hj2 : j < 0) (h : ℤ) (d r : ℤ → ℝ) (hr : 0 < r j) :
    Reaches P ⟨pc, physZ Z h d r⟩ ⟨pc + 1, physZ Z h d r⟩ 1 :=
  Reaches.single (step_jle_of_pos hP _ (by rw [physZ_reg hj1 hj2]; exact hr))

end RegLemmas

/-! ### Code placement -/

/-- `code` sits in `P` starting at address `base`. -/
def codeAt (P : BSSProgram) (base : ℕ) (code : List BSSInstr) : Prop :=
  ∀ i, i < code.length → P[base + i]? = code[i]?

lemma codeAt_nil (P : BSSProgram) (base : ℕ) : codeAt P base [] := fun i hi => by simp at hi

lemma codeAt_cons {P : BSSProgram} {base : ℕ} {ins : BSSInstr} {rest : List BSSInstr}
    (h : codeAt P base (ins :: rest)) : P[base]? = some ins ∧ codeAt P (base + 1) rest := by
  refine ⟨by simpa using h 0 (by simp), fun i hi => ?_⟩
  have := h (i + 1) (by simp; omega)
  rw [show base + (i + 1) = base + 1 + i by omega] at this
  simpa using this

lemma codeAt_append {P : BSSProgram} {base : ℕ} {A B : List BSSInstr}
    (h : codeAt P base (A ++ B)) : codeAt P base A ∧ codeAt P (base + A.length) B := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := h i (by simp; omega)
    rwa [List.getElem?_append_left hi] at this
  · have := h (A.length + i) (by simp; omega)
    rw [show base + (A.length + i) = base + A.length + i by omega] at this
    rwa [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at this

lemma codeAt_of_getElem? {P : BSSProgram} {base : ℕ} {code : List BSSInstr}
    (h : codeAt P base code) {i : ℕ} {ins : BSSInstr} (hi : code[i]? = some ins) :
    P[base + i]? = some ins := by
  have hlen : i < code.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; exact absurd hi (by simp)
  rw [h i hlen, hi]

/-! ### Mov chains -/

/-- `mov a ← b`. -/
def movCode (a b : ℤ) : List BSSInstr := [.const a 0, .add a a b]

/-- A sequence of movs. -/
def movsCode : List (ℤ × ℤ) → List BSSInstr
  | [] => []
  | (a, b) :: ms => movCode a b ++ movsCode ms

lemma movsCode_length (ms : List (ℤ × ℤ)) : (movsCode ms).length = 2 * ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih => obtain ⟨a, b⟩ := m; simp [movsCode, movCode, ih]; ring

lemma movsCode_append (ms ns : List (ℤ × ℤ)) :
    movsCode (ms ++ ns) = movsCode ms ++ movsCode ns := by
  induction ms with
  | nil => rfl
  | cons m ms ih => obtain ⟨a, b⟩ := m; simp [movsCode, ih]

/-- The effect of a sequence of movs on a tape. -/
def applyMovs : List (ℤ × ℤ) → (ℤ → ℝ) → (ℤ → ℝ)
  | [], τ => τ
  | (a, b) :: ms, τ => applyMovs ms (Function.update τ a (τ b))

lemma applyMovs_append (ms ns : List (ℤ × ℤ)) (τ : ℤ → ℝ) :
    applyMovs (ms ++ ns) τ = applyMovs ns (applyMovs ms τ) := by
  induction ms generalizing τ with
  | nil => rfl
  | cons m ms ih => obtain ⟨a, b⟩ := m; simp [applyMovs, ih]

lemma reaches_movs {P : BSSProgram} (ms : List (ℤ × ℤ)) (hne : ∀ m ∈ ms, m.1 ≠ m.2)
    (base : ℕ) (hP : codeAt P base (movsCode ms)) (τ : ℤ → ℝ) :
    Reaches P ⟨base, τ⟩ ⟨base + 2 * ms.length, applyMovs ms τ⟩ (2 * ms.length) := by
  induction ms generalizing base τ with
  | nil =>
    simp only [List.length_nil, mul_zero, add_zero, applyMovs]
    exact Reaches.refl P _
  | cons m ms ih =>
    obtain ⟨a, b⟩ := m
    simp only [movsCode, movCode] at hP
    obtain ⟨h0, hP'⟩ := codeAt_cons hP
    obtain ⟨h1, hP''⟩ := codeAt_cons hP'
    have s1 := reaches_mov h0 h1 (hne (a, b) (by simp)) τ
    have s2 := ih (fun m hm => hne m (by simp [hm])) (base + 2) hP'' (Function.update τ a (τ b))
    have := s1.trans s2
    refine (this.mono (by simp; omega)).cast ?_
    simp only [applyMovs, List.length_cons]
    congr 1; omega

/-! ### The down and up chains -/

/-- `downMovs j = [(-1,-2), (-2,-3), …, (-j, -j-1)]`. -/
def downMovs : ℕ → List (ℤ × ℤ)
  | 0 => []
  | j + 1 => downMovs j ++ [(-((j : ℤ) + 1), -((j : ℤ) + 2))]

/-- `upMovs j = [(-j, -j+1), …, (-1, 0)]`. -/
def upMovs : ℕ → List (ℤ × ℤ)
  | 0 => []
  | j + 1 => (-((j : ℤ) + 1), -(j : ℤ)) :: upMovs j

lemma downMovs_length (j : ℕ) : (downMovs j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [downMovs, ih]

lemma upMovs_length (j : ℕ) : (upMovs j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [upMovs, ih]

lemma downMovs_ne (j : ℕ) : ∀ m ∈ downMovs j, m.1 ≠ m.2 := by
  induction j with
  | zero => simp [downMovs]
  | succ j ih =>
    intro m hm
    simp only [downMovs, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact ih m hm
    · dsimp only; omega

lemma upMovs_ne (j : ℕ) : ∀ m ∈ upMovs j, m.1 ≠ m.2 := by
  induction j with
  | zero => simp [upMovs]
  | succ j ih =>
    intro m hm
    simp only [upMovs, List.mem_cons] at hm
    rcases hm with rfl | hm
    · dsimp only; omega
    · exact ih m hm

lemma applyMovs_downMovs (j : ℕ) (τ : ℤ → ℝ) :
    applyMovs (downMovs j) τ = fun c => if -(j : ℤ) ≤ c ∧ c ≤ -1 then τ (c - 1) else τ c := by
  induction j with
  | zero => funext c; simp [downMovs, applyMovs]; intro h1 h2; omega
  | succ j ih =>
    funext c
    rw [downMovs, applyMovs_append, ih]
    simp only [applyMovs, Function.update_apply]
    push_cast
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

lemma applyMovs_upMovs (j : ℕ) (τ : ℤ → ℝ) :
    applyMovs (upMovs j) τ = fun c => if -(j : ℤ) ≤ c ∧ c ≤ -1 then τ (c + 1) else τ c := by
  induction j generalizing τ with
  | zero => funext c; simp [upMovs, applyMovs]; intro h1 h2; omega
  | succ j ih =>
    funext c
    rw [upMovs, applyMovs, ih]
    simp only [Function.update_apply]
    push_cast
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

/-! ### The right and left chains -/

/-- Right chain: `shiftL`, then push the head cell to the far side, then slide the zone. -/
def rightChain (Z : ℕ) : List BSSInstr :=
  [.shiftL] ++ movsCode ((-((Z : ℤ) + 1), -1) :: downMovs (Z - 1))

/-- Left chain: `shiftR`, slide the zone, then pull the far cell to the head. -/
def leftChain (Z : ℕ) : List BSSInstr :=
  [.shiftR] ++ movsCode (upMovs (Z - 1) ++ [(0, -(Z : ℤ))])

lemma rightChain_length (Z : ℕ) (hZ : 1 ≤ Z) : (rightChain Z).length = 2 * Z + 1 := by
  simp [rightChain, movsCode_length, downMovs_length]; omega

lemma leftChain_length (Z : ℕ) (hZ : 1 ≤ Z) : (leftChain Z).length = 2 * Z + 1 := by
  simp [leftChain, movsCode_length, upMovs_length]; omega

theorem reaches_rightChain {P : BSSProgram} (Z : ℕ) (hZ : 2 ≤ Z) (base : ℕ)
    (hP : codeAt P base (rightChain Z)) (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨base, physZ Z h d r⟩
      ⟨base + (2 * Z + 1), physZ Z (h + 1) d (Function.update r (-(Z : ℤ)) (r (-(Z : ℤ) + 1)))⟩
      (2 * Z + 1) := by
  obtain ⟨Z', rfl⟩ : ∃ Z', Z = Z' + 1 := ⟨Z - 1, by omega⟩
  unfold rightChain at hP
  obtain ⟨h0, hP'⟩ := codeAt_cons hP
  have s1 := Reaches.single (step_shiftL h0 (physZ (Z' + 1) h d r))
  have s2 := reaches_movs _ (by
      intro m hm; simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · dsimp only; omega
      · exact downMovs_ne _ m hm) (base + 1) hP' (fun k => physZ (Z' + 1) h d r (k + 1))
  refine ((s1.trans s2).mono (by simp [downMovs_length]; omega)).cast ?_
  simp only [List.length_cons, downMovs_length, Nat.add_sub_cancel]
  congr 1
  · omega
  · simp only [applyMovs]
    rw [applyMovs_downMovs]
    funext c
    simp only [Function.update_apply]
    push_cast
    rcases lt_trichotomy c (-((Z' : ℤ) + 1 + 1)) with hc | hc | hc
    · -- far left
      rw [if_neg (show ¬ (-(Z' : ℤ) ≤ c ∧ c ≤ -1) by omega),
        if_neg (show ¬ (c = -((Z' : ℤ) + 1 + 1)) by omega),
        physZ_lt (show c + 1 < -((Z' + 1 : ℕ) : ℤ) by push_cast; omega),
        physZ_lt (show c < -((Z' + 1 : ℕ) : ℤ) by push_cast; omega)]
      congr 1; push_cast; ring
    · -- the pushed cell
      subst hc
      rw [if_neg (show ¬ (-(Z' : ℤ) ≤ -((Z' : ℤ) + 1 + 1) ∧ -((Z' : ℤ) + 1 + 1) ≤ -1) by omega),
        if_pos rfl, physZ_lt (show -((Z' : ℤ) + 1 + 1) < -((Z' + 1 : ℕ) : ℤ) by push_cast; omega)]
      simp only [physZ_zero]
      congr 1; push_cast; ring
    · rcases lt_trichotomy c (-((Z' : ℤ) + 1)) with hc2 | hc2 | hc2
      · exact absurd hc2 (not_lt.mpr (by linarith [Int.add_one_le_iff.mpr hc]))
      · -- the scratch cell
        subst hc2
        rw [if_neg (show ¬ (-(Z' : ℤ) ≤ -((Z' : ℤ) + 1) ∧ -((Z' : ℤ) + 1) ≤ -1) by omega),
          if_neg (show ¬ (-((Z' : ℤ) + 1) = -((Z' : ℤ) + 1 + 1)) by omega),
          physZ_reg (show -((Z' + 1 : ℕ) : ℤ) ≤ -((Z' : ℤ) + 1) + 1 by push_cast; omega)
            (by omega),
          physZ_reg (show -((Z' + 1 : ℕ) : ℤ) ≤ -((Z' : ℤ) + 1) by push_cast; omega) (by omega),
          Function.update_self]
      · rcases lt_or_ge c 0 with hc3 | hc3
        · -- zone cell
          rw [if_pos (show -(Z' : ℤ) ≤ c ∧ c ≤ -1 by omega),
            if_neg (show ¬ (c - 1 = -((Z' : ℤ) + 1 + 1)) by omega),
            physZ_reg (show -((Z' + 1 : ℕ) : ℤ) ≤ c - 1 + 1 by push_cast; omega) (by omega),
            physZ_reg (show -((Z' + 1 : ℕ) : ℤ) ≤ c by push_cast; omega) (by omega),
            Function.update_of_ne (show c ≠ -((Z' : ℤ) + 1) by omega)]
          congr 1; ring
        · -- right of the head
          rw [if_neg (show ¬ (-(Z' : ℤ) ≤ c ∧ c ≤ -1) by omega),
            if_neg (show ¬ (c = -((Z' : ℤ) + 1 + 1)) by omega),
            physZ_nonneg (show 0 ≤ c + 1 by omega), physZ_nonneg hc3]
          congr 1; ring

theorem reaches_leftChain {P : BSSProgram} (Z : ℕ) (hZ : 2 ≤ Z) (base : ℕ)
    (hP : codeAt P base (leftChain Z)) (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨base, physZ Z h d r⟩
      ⟨base + (2 * Z + 1), physZ Z (h - 1) d (Function.update r (-(Z : ℤ)) (d (h - 1)))⟩
      (2 * Z + 1) := by
  obtain ⟨Z', rfl⟩ : ∃ Z', Z = Z' + 1 := ⟨Z - 1, by omega⟩
  unfold leftChain at hP
  obtain ⟨h0, hP'⟩ := codeAt_cons hP
  have s1 := Reaches.single (step_shiftR h0 (physZ (Z' + 1) h d r))
  have s2 := reaches_movs _ (by
      intro m hm; simp only [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact upMovs_ne _ m hm
      · dsimp only; omega) (base + 1) hP' (fun k => physZ (Z' + 1) h d r (k - 1))
  refine ((s1.trans s2).mono (by simp [upMovs_length]; omega)).cast ?_
  simp only [List.length_append, List.length_singleton, upMovs_length, Nat.add_sub_cancel]
  congr 1
  · omega
  · rw [applyMovs_append, applyMovs_upMovs]
    simp only [applyMovs]
    funext c
    simp only [Function.update_apply]
    push_cast
    rcases lt_trichotomy c (-((Z' : ℤ) + 1)) with hc | hc | hc
    · -- far left
      rw [if_neg (show ¬ (c = 0) by omega), if_neg (show ¬ (-(Z' : ℤ) ≤ c ∧ c ≤ -1) by omega),
        physZ_lt (show c - 1 < -((Z' + 1 : ℕ) : ℤ) by push_cast; omega),
        physZ_lt (show c < -((Z' + 1 : ℕ) : ℤ) by push_cast; omega)]
      congr 1; push_cast; ring
    · -- the scratch cell receives the pulled data cell
      subst hc
      rw [if_neg (show ¬ (-((Z' : ℤ) + 1) = 0) by omega),
        if_neg (show ¬ (-(Z' : ℤ) ≤ -((Z' : ℤ) + 1) ∧ -((Z' : ℤ) + 1) ≤ -1) by omega),
        physZ_lt (show -((Z' : ℤ) + 1) - 1 < -((Z' + 1 : ℕ) : ℤ) by push_cast; omega),
        physZ_reg (show -((Z' + 1 : ℕ) : ℤ) ≤ -((Z' : ℤ) + 1) by push_cast; omega) (by omega),
        Function.update_self]
      congr 1; push_cast; ring
    · rcases lt_trichotomy c 0 with hc3 | hc3 | hc3
      · -- zone cell
        rw [if_neg (show ¬ (c = 0) by omega), if_pos (show -(Z' : ℤ) ≤ c ∧ c ≤ -1 by omega),
          physZ_reg (show -((Z' + 1 : ℕ) : ℤ) ≤ c + 1 - 1 by push_cast; omega) (by omega),
          physZ_reg (show -((Z' + 1 : ℕ) : ℤ) ≤ c by push_cast; omega) (by omega),
          Function.update_of_ne (show c ≠ -((Z' : ℤ) + 1) by omega)]
        congr 1; ring
      · -- the head receives the far cell
        subst hc3
        rw [if_pos rfl, if_neg (show ¬ (-(Z' : ℤ) ≤ -((Z' : ℤ) + 1) ∧ -((Z' : ℤ) + 1) ≤ -1) by omega),
          physZ_lt (show -((Z' : ℤ) + 1) - 1 < -((Z' + 1 : ℕ) : ℤ) by push_cast; omega),
          physZ_zero]
        congr 1; push_cast; ring
      · -- right of the head
        rw [if_neg (show ¬ (c = 0) by omega), if_neg (show ¬ (-(Z' : ℤ) ≤ c ∧ c ≤ -1) by omega),
          physZ_nonneg (show 0 ≤ c - 1 by omega), physZ_nonneg (show 0 ≤ c by omega)]
        congr 1; ring


/-! ## Layer: CP_Walk -/



/-- Address of the head-position register. -/
def Haddr (Z : ℕ) : ℤ := -((Z : ℤ) - 2)
/-- First scratch cell. -/
def S1 (Z : ℕ) : ℤ := -((Z : ℤ) - 1)
/-- Second scratch cell (absorbs the chain's stale value). -/
def S2 (Z : ℕ) : ℤ := -(Z : ℤ)

/-- Registers other than `H`, `S1`, `S2` are preserved. -/
def Pres (Z : ℕ) (r r' : ℤ → ℝ) : Prop :=
  ∀ j, j ≠ Haddr Z → j ≠ S1 Z → j ≠ S2 Z → r' j = r j

lemma Pres.refl (Z : ℕ) (r : ℤ → ℝ) : Pres Z r r := fun _ _ _ _ => rfl

lemma Pres.trans {Z : ℕ} {r r' r'' : ℤ → ℝ} (h1 : Pres Z r r') (h2 : Pres Z r' r'') :
    Pres Z r r'' := fun j a b c => by rw [h2 j a b c, h1 j a b c]

lemma Pres.update_H {Z : ℕ} {r r' : ℤ → ℝ} (h : Pres Z r r') (v : ℝ) :
    Pres Z r (Function.update r' (Haddr Z) v) := fun j a b c => by
  rw [Function.update_of_ne a]; exact h j a b c

lemma Pres.update_S1 {Z : ℕ} {r r' : ℤ → ℝ} (h : Pres Z r r') (v : ℝ) :
    Pres Z r (Function.update r' (S1 Z) v) := fun j a b c => by
  rw [Function.update_of_ne b]; exact h j a b c

lemma Pres.update_S2 {Z : ℕ} {r r' : ℤ → ℝ} (h : Pres Z r r') (v : ℝ) :
    Pres Z r (Function.update r' (S2 Z) v) := fun j a b c => by
  rw [Function.update_of_ne c]; exact h j a b c

/-- The right walk-loop body (after the loop test). -/
def rBody (Z : ℕ) (base : ℕ) : List BSSInstr :=
  rightChain Z ++ [.const (S2 Z) 1, .add (Haddr Z) (Haddr Z) (S2 Z), .const (S2 Z) 1,
    .sub (S1 Z) (S1 Z) (S2 Z), .const (S2 Z) 0, .jle (S2 Z) (base + 1)]

/-- The left walk-loop body. -/
def lBody (Z : ℕ) (base : ℕ) : List BSSInstr :=
  leftChain Z ++ [.const (S2 Z) 1, .sub (Haddr Z) (Haddr Z) (S2 Z), .const (S2 Z) 1,
    .sub (S1 Z) (S1 Z) (S2 Z), .const (S2 Z) 0, .jle (S2 Z) (base + (2 * Z + 9) + 2)]

/-- The walk block for pointer cell `pq`, placed at `base`. -/
def walkCode (Z : ℕ) (pq : ℤ) (base : ℕ) : List BSSInstr :=
  .sub (S1 Z) pq (Haddr Z) :: .jle (S1 Z) (base + (2 * Z + 9)) ::
    (rBody Z base ++ (.const (S2 Z) 0 :: .sub (S1 Z) (S2 Z) (S1 Z) ::
      .jle (S1 Z) (base + (4 * Z + 19)) :: lBody Z base))

lemma rBody_length (Z : ℕ) (hZ : 1 ≤ Z) (base : ℕ) : (rBody Z base).length = 2 * Z + 7 := by
  rw [rBody, List.length_append, rightChain_length Z hZ]
  simp only [List.length_cons, List.length_nil] <;> omega

lemma lBody_length (Z : ℕ) (hZ : 1 ≤ Z) (base : ℕ) : (lBody Z base).length = 2 * Z + 7 := by
  rw [lBody, List.length_append, leftChain_length Z hZ]
  simp only [List.length_cons, List.length_nil] <;> omega

lemma walkCode_length (Z : ℕ) (hZ : 1 ≤ Z) (pq : ℤ) (base : ℕ) :
    (walkCode Z pq base).length = 4 * Z + 19 := by
  simp only [walkCode, List.length_cons, List.length_append, rBody_length Z hZ base,
    lBody_length Z hZ base]; omega

section Loops

variable {P : BSSProgram} (Z : ℕ)

lemma H_bounds (hZ : 3 ≤ Z) : -(Z : ℤ) ≤ Haddr Z ∧ Haddr Z < 0 := by unfold Haddr; omega
lemma S1_bounds (hZ : 3 ≤ Z) : -(Z : ℤ) ≤ S1 Z ∧ S1 Z < 0 := by unfold S1; omega
lemma S2_bounds (hZ : 3 ≤ Z) : -(Z : ℤ) ≤ S2 Z ∧ S2 Z < 0 := by unfold S2; omega
lemma H_ne_S1 (hZ : 3 ≤ Z) : Haddr Z ≠ S1 Z := by unfold Haddr S1; omega
lemma H_ne_S2 (hZ : 3 ≤ Z) : Haddr Z ≠ S2 Z := by unfold Haddr S2; omega
lemma S1_ne_S2 (hZ : 3 ≤ Z) : S1 Z ≠ S2 Z := by unfold S1 S2; omega

/-- One iteration of the right loop plus the induction: from the loop head with counter `n`. -/
theorem rloop (hZ : 3 ≤ Z) (base : ℕ)
    (hP : codeAt P (base + 1) (.jle (S1 Z) (base + (2 * Z + 9)) :: rBody Z base))
    (d : ℤ → ℝ) : ∀ (n : ℕ) (h : ℤ) (r : ℤ → ℝ), r (S1 Z) = (n : ℝ) → r (Haddr Z) = (h : ℝ) →
    ∃ r', Pres Z r r' ∧ r' (Haddr Z) = ((h + n : ℤ) : ℝ) ∧ r' (S1 Z) = 0 ∧
      Reaches P ⟨base + 1, physZ Z h d r⟩ ⟨base + (2 * Z + 9), physZ Z (h + n) d r'⟩
        ((2 * Z + 8) * n + 1)
  | 0, h, r, hS, hH => by
    obtain ⟨hj, _⟩ := codeAt_cons hP
    refine ⟨r, Pres.refl Z r, by simpa using hH, by simpa using hS, ?_⟩
    have := reachesZ_jle_le hj (S1_bounds Z hZ).1 (S1_bounds Z hZ).2 h d r (by rw [hS]; simp)
    simpa using this
  | n + 1, h, r, hS, hH => by
    obtain ⟨hj, hP'⟩ := codeAt_cons hP
    unfold rBody at hP'
    obtain ⟨hch, hP''⟩ := codeAt_append hP'
    rw [rightChain_length Z (by omega)] at hP''
    obtain ⟨h1, hP3⟩ := codeAt_cons hP''
    obtain ⟨h2, hP4⟩ := codeAt_cons hP3
    obtain ⟨h3, hP5⟩ := codeAt_cons hP4
    obtain ⟨h4, hP6⟩ := codeAt_cons hP5
    obtain ⟨h5, hP7⟩ := codeAt_cons hP6
    obtain ⟨h6, _⟩ := codeAt_cons hP7
    have hSb := S1_bounds Z hZ; have hHb := H_bounds Z hZ; have hS2b := S2_bounds Z hZ
    have s1 := reachesZ_jle_pos hj hSb.1 hSb.2 h d r (by rw [hS]; positivity)
    have s2 := reaches_rightChain Z (by omega) (base + 1 + 1) hch h d r
    set r₁ := Function.update r (-(Z : ℤ)) (r (-(Z : ℤ) + 1)) with hr₁
    have s3 := reachesZ_const h1 hS2b.1 hS2b.2 (h + 1) d r₁
    set r₂ := Function.update r₁ (S2 Z) (1 : ℝ) with hr₂
    have s4 := reachesZ_add h2 hHb.1 hHb.2 hHb.1 hHb.2 hS2b.1 hS2b.2 (h + 1) d r₂
    set r₃ := Function.update r₂ (Haddr Z) (r₂ (Haddr Z) + r₂ (S2 Z)) with hr₃
    have s5 := reachesZ_const h3 hS2b.1 hS2b.2 (h + 1) d r₃
    set r₄ := Function.update r₃ (S2 Z) (1 : ℝ) with hr₄
    have s6 := reachesZ_sub h4 hSb.1 hSb.2 hSb.1 hSb.2 hS2b.1 hS2b.2 (h + 1) d r₄
    set r₅ := Function.update r₄ (S1 Z) (r₄ (S1 Z) - r₄ (S2 Z)) with hr₅
    have s7 := reachesZ_const h5 hS2b.1 hS2b.2 (h + 1) d r₅
    set r₆ := Function.update r₅ (S2 Z) (0 : ℝ) with hr₆
    have s8 := reachesZ_jle_le h6 hS2b.1 hS2b.2 (h + 1) d r₆ (by simp [hr₆])
    have hne1 := H_ne_S1 Z hZ; have hne2 := H_ne_S2 Z hZ; have hne3 := S1_ne_S2 Z hZ
    have hS2eq : S2 Z = -(Z : ℤ) := rfl
    have hS1eq : S1 Z = -(Z : ℤ) + 1 := by unfold S1; ring
    have hr₆S1 : r₆ (S1 Z) = (n : ℝ) := by
      simp only [hr₆, hr₅, hr₄, hr₃, hr₂, hr₁, Function.update_apply, hS2eq]
      simp [hne3.symm, hne1.symm, show S1 Z ≠ -(Z:ℤ) by rw [hS1eq]; omega, hS] <;>
        (push_cast; ring)
    have hr₆H : r₆ (Haddr Z) = ((h + 1 : ℤ) : ℝ) := by
      simp only [hr₆, hr₅, hr₄, hr₃, hr₂, hr₁, Function.update_apply, hS2eq]
      simp [hne1, hne2, show Haddr Z ≠ -(Z:ℤ) by unfold Haddr; omega, hH]
    obtain ⟨r', hpres, hH', hS', s9⟩ := rloop hZ base hP d n (h + 1) r₆ hr₆S1 hr₆H
    refine ⟨r', ?_, ?_, hS', ?_⟩
    · refine Pres.trans ?_ hpres
      intro j ha hb hc
      simp only [hr₆, hr₅, hr₄, hr₃, hr₂, hr₁, Function.update_apply, hS2eq]
      have : j ≠ -(Z : ℤ) := hc
      simp [ha, hb, hc, this]
    · rw [hH']; push_cast; ring
    · have hall := s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans
        (s8.trans s9)))))))
      refine (hall.mono (by ring_nf; omega)).cast ?_
      congr 2; push_cast; ring

/-- The left loop. -/
theorem lloop (hZ : 3 ≤ Z) (base : ℕ)
    (hP : codeAt P (base + (2 * Z + 9) + 2) (.jle (S1 Z) (base + (4 * Z + 19)) :: lBody Z base))
    (d : ℤ → ℝ) : ∀ (n : ℕ) (h : ℤ) (r : ℤ → ℝ), r (S1 Z) = (n : ℝ) → r (Haddr Z) = (h : ℝ) →
    ∃ r', Pres Z r r' ∧ r' (Haddr Z) = ((h - n : ℤ) : ℝ) ∧ r' (S1 Z) = 0 ∧
      Reaches P ⟨base + (2 * Z + 9) + 2, physZ Z h d r⟩ ⟨base + (4 * Z + 19), physZ Z (h - n) d r'⟩
        ((2 * Z + 8) * n + 1)
  | 0, h, r, hS, hH => by
    obtain ⟨hj, _⟩ := codeAt_cons hP
    refine ⟨r, Pres.refl Z r, by simpa using hH, by simpa using hS, ?_⟩
    have := reachesZ_jle_le hj (S1_bounds Z hZ).1 (S1_bounds Z hZ).2 h d r (by rw [hS]; simp)
    simpa using this
  | n + 1, h, r, hS, hH => by
    obtain ⟨hj, hP'⟩ := codeAt_cons hP
    unfold lBody at hP'
    obtain ⟨hch, hP''⟩ := codeAt_append hP'
    rw [leftChain_length Z (by omega)] at hP''
    obtain ⟨h1, hP3⟩ := codeAt_cons hP''
    obtain ⟨h2, hP4⟩ := codeAt_cons hP3
    obtain ⟨h3, hP5⟩ := codeAt_cons hP4
    obtain ⟨h4, hP6⟩ := codeAt_cons hP5
    obtain ⟨h5, hP7⟩ := codeAt_cons hP6
    obtain ⟨h6, _⟩ := codeAt_cons hP7
    have hSb := S1_bounds Z hZ; have hHb := H_bounds Z hZ; have hS2b := S2_bounds Z hZ
    have s1 := reachesZ_jle_pos hj hSb.1 hSb.2 h d r (by rw [hS]; positivity)
    have s2 := reaches_leftChain Z (by omega) (base + (2 * Z + 9) + 2 + 1) hch h d r
    set r₁ := Function.update r (-(Z : ℤ)) (d (h - 1)) with hr₁
    have s3 := reachesZ_const h1 hS2b.1 hS2b.2 (h - 1) d r₁
    set r₂ := Function.update r₁ (S2 Z) (1 : ℝ) with hr₂
    have s4 := reachesZ_sub h2 hHb.1 hHb.2 hHb.1 hHb.2 hS2b.1 hS2b.2 (h - 1) d r₂
    set r₃ := Function.update r₂ (Haddr Z) (r₂ (Haddr Z) - r₂ (S2 Z)) with hr₃
    have s5 := reachesZ_const h3 hS2b.1 hS2b.2 (h - 1) d r₃
    set r₄ := Function.update r₃ (S2 Z) (1 : ℝ) with hr₄
    have s6 := reachesZ_sub h4 hSb.1 hSb.2 hSb.1 hSb.2 hS2b.1 hS2b.2 (h - 1) d r₄
    set r₅ := Function.update r₄ (S1 Z) (r₄ (S1 Z) - r₄ (S2 Z)) with hr₅
    have s7 := reachesZ_const h5 hS2b.1 hS2b.2 (h - 1) d r₅
    set r₆ := Function.update r₅ (S2 Z) (0 : ℝ) with hr₆
    have s8 := reachesZ_jle_le h6 hS2b.1 hS2b.2 (h - 1) d r₆ (by simp [hr₆])
    have hne1 := H_ne_S1 Z hZ; have hne2 := H_ne_S2 Z hZ; have hne3 := S1_ne_S2 Z hZ
    have hS2eq : S2 Z = -(Z : ℤ) := rfl
    have hr₆S1 : r₆ (S1 Z) = (n : ℝ) := by
      simp only [hr₆, hr₅, hr₄, hr₃, hr₂, hr₁, Function.update_apply, hS2eq]
      simp [hne3.symm, hne1.symm, show S1 Z ≠ -(Z:ℤ) by unfold S1; omega, hS] <;>
        (push_cast; ring)
    have hr₆H : r₆ (Haddr Z) = ((h - 1 : ℤ) : ℝ) := by
      simp only [hr₆, hr₅, hr₄, hr₃, hr₂, hr₁, Function.update_apply, hS2eq]
      simp [hne1, hne2, show Haddr Z ≠ -(Z:ℤ) by unfold Haddr; omega, hH]
    obtain ⟨r', hpres, hH', hS', s9⟩ := lloop hZ base hP d n (h - 1) r₆ hr₆S1 hr₆H
    refine ⟨r', ?_, ?_, hS', ?_⟩
    · refine Pres.trans ?_ hpres
      intro j ha hb hc
      simp only [hr₆, hr₅, hr₄, hr₃, hr₂, hr₁, Function.update_apply, hS2eq]
      have : j ≠ -(Z : ℤ) := hc
      simp [ha, hb, hc, this]
    · rw [hH']; push_cast; ring
    · have hall := s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans
        (s8.trans s9)))))))
      refine (hall.mono (by ring_nf; omega)).cast ?_
      congr 2; push_cast; ring

/-- The walk block moves the head to the cell addressed by `pq`. -/
theorem walk (hZ : 3 ≤ Z) (base : ℕ) (pq : ℤ) (hpq1 : -(Z : ℤ) ≤ pq) (hpq2 : pq < 0)
    (hpqH : pq ≠ Haddr Z) (hpqS1 : pq ≠ S1 Z) (hpqS2 : pq ≠ S2 Z)
    (hP : codeAt P base (walkCode Z pq base)) (d : ℤ → ℝ) (h v : ℤ) (r : ℤ → ℝ)
    (hH : r (Haddr Z) = (h : ℝ)) (hv : r pq = (v : ℝ)) :
    ∃ r', Pres Z r r' ∧ r' (Haddr Z) = (v : ℝ) ∧
      Reaches P ⟨base, physZ Z h d r⟩ ⟨base + (4 * Z + 19), physZ Z v d r'⟩
        ((2 * Z + 8) * (v - h).natAbs + 5) := by
  have hSb := S1_bounds Z hZ; have hHb := H_bounds Z hZ; have hS2b := S2_bounds Z hZ
  have hne1 := H_ne_S1 Z hZ; have hne2 := H_ne_S2 Z hZ; have hne3 := S1_ne_S2 Z hZ
  unfold walkCode at hP
  obtain ⟨h0, hP1⟩ := codeAt_cons hP
  rw [← List.cons_append] at hP1
  obtain ⟨hPr, hP2⟩ := codeAt_append hP1
  simp only [List.length_cons, rBody_length Z (by omega) base] at hP2
  rw [show base + 1 + (2 * Z + 7 + 1) = base + (2 * Z + 9) by omega] at hP2
  obtain ⟨hE1, hP3⟩ := codeAt_cons hP2
  obtain ⟨hE2, hP4⟩ := codeAt_cons hP3
  have hPl : codeAt P (base + (2 * Z + 9) + 2)
      (.jle (S1 Z) (base + (4 * Z + 19)) :: lBody Z base) := hP4
  -- step A
  have sA := reachesZ_sub h0 hSb.1 hSb.2 hpq1 hpq2 hHb.1 hHb.2 h d r
  set r₁ := Function.update r (S1 Z) (r pq - r (Haddr Z)) with hr₁
  have hr₁S1 : r₁ (S1 Z) = ((v - h : ℤ) : ℝ) := by simp [hr₁, hv, hH]
  have hr₁H : r₁ (Haddr Z) = (h : ℝ) := by simp [hr₁, hne1, hne1.symm, hH]
  have hpres₁ : Pres Z r r₁ := (Pres.refl Z r).update_S1 _
  rcases le_or_gt h v with hle | hlt
  · -- walk right by `n = v - h`
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = v - h := ⟨(v - h).toNat, by omega⟩
    have hS1n : r₁ (S1 Z) = (n : ℝ) := by rw [hr₁S1, ← hn]; simp
    obtain ⟨r₂, hpres₂, hH₂, hS₂, sR⟩ := rloop Z hZ base hPr d n h r₁ hS1n hr₁H
    -- E: S1 := 0 - S1 = 0 ; F: exit
    have sE1 := reachesZ_const hE1 hS2b.1 hS2b.2 (h + n) d r₂
    set r₃ := Function.update r₂ (S2 Z) (0 : ℝ) with hr₃
    have sE2 := reachesZ_sub hE2 hSb.1 hSb.2 hS2b.1 hS2b.2 hSb.1 hSb.2 (h + n) d r₃
    set r₄ := Function.update r₃ (S1 Z) (r₃ (S2 Z) - r₃ (S1 Z)) with hr₄
    have hr₄S1 : r₄ (S1 Z) = 0 := by simp [hr₄, hr₃, hne3, hne3.symm, hS₂]
    obtain ⟨hF, _⟩ := codeAt_cons hPl
    have sF := reachesZ_jle_le hF hSb.1 hSb.2 (h + n) d r₄ (by rw [hr₄S1])
    refine ⟨r₄, ?_, ?_, ?_⟩
    · exact ((hpres₁.trans hpres₂).update_S2 _).update_S1 _
    · simp [hr₄, hr₃, hne1, hne2, hH₂]; exact_mod_cast (by omega : h + (n : ℤ) = v)
    · have hall := sA.trans (sR.trans (sE1.trans (sE2.trans sF)))
      have hv' : v = h + n := by omega
      have hnat : (v - h).natAbs = n := by omega
      rw [hnat]
      refine (hall.mono (by omega)).cast ?_
      rw [hv']
  · -- walk left by `n = h - v`
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = h - v := ⟨(h - v).toNat, by omega⟩
    obtain ⟨hj, _⟩ := codeAt_cons hPr
    have sR := reachesZ_jle_le hj hSb.1 hSb.2 h d r₁ (by rw [hr₁S1]; exact_mod_cast (by omega : v - h ≤ 0))
    have sE1 := reachesZ_const hE1 hS2b.1 hS2b.2 h d r₁
    set r₂ := Function.update r₁ (S2 Z) (0 : ℝ) with hr₂
    have sE2 := reachesZ_sub hE2 hSb.1 hSb.2 hS2b.1 hS2b.2 hSb.1 hSb.2 h d r₂
    set r₃ := Function.update r₂ (S1 Z) (r₂ (S2 Z) - r₂ (S1 Z)) with hr₃
    have hr₃S1 : r₃ (S1 Z) = (n : ℝ) := by
      simp [hr₃, hr₂, hne3, hne3.symm, hr₁S1]; exact_mod_cast (by omega : h - v = (n : ℤ))
    have hr₃H : r₃ (Haddr Z) = (h : ℝ) := by
      simp [hr₃, hr₂, hne1, hne1.symm, hne2, hne2.symm, hr₁H]
    obtain ⟨r₄, hpres₄, hH₄, _, sL⟩ := lloop Z hZ base hPl d n h r₃ hr₃S1 hr₃H
    refine ⟨r₄, ?_, ?_, ?_⟩
    · exact ((hpres₁.update_S2 _).update_S1 _).trans hpres₄
    · rw [hH₄, hn]; push_cast; ring
    · have hall := sA.trans (sR.trans (sE1.trans (sE2.trans sL)))
      have hv' : v = h - n := by omega
      have hnat : (v - h).natAbs = n := by omega
      rw [hnat]
      refine (hall.mono (by omega)).cast ?_
      rw [hv']

end Loops


/-! ## Layer: CP_Compile -/



/-! ### Indices used by a program -/

/-- Real register indices mentioned by an instruction. -/
def regIdxs : RAMInstr → List ℕ
  | .const dst _ => [dst]
  | .add dst i j => [dst, i, j]
  | .sub dst i j => [dst, i, j]
  | .mul dst i j => [dst, i, j]
  | .div dst i j => [dst, i, j]
  | .load dst _ => [dst]
  | .store _ i => [i]
  | .jle i _ => [i]
  | _ => []

/-- Pointer register indices mentioned by an instruction. -/
def ptrIdxs : RAMInstr → List ℕ
  | .load _ q => [q]
  | .store q _ => [q]
  | .pset q _ => [q]
  | .pcopy q q' => [q, q']
  | .pinc q => [q]
  | .pdec q => [q]
  | .pjle q q' _ => [q, q']
  | _ => []

/-- Pointer constants of an instruction (absolute value). -/
def ptrConsts : RAMInstr → List ℕ
  | .pset _ c => [c.natAbs]
  | _ => []

lemma foldr_max_le {l : List ℕ} {a : ℕ} (ha : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact le_max_of_le_right (ih ha)

/-- Number of real registers. -/
def kOf (R : RAMProgram) : ℕ := (R.flatMap regIdxs).foldr max 0 + 1
/-- Number of pointer registers. -/
def qOf (R : RAMProgram) : ℕ := (R.flatMap ptrIdxs).foldr max 0 + 1
/-- Zone width. -/
def ZOf (R : RAMProgram) : ℕ := kOf R + qOf R + 3
/-- Largest pointer constant. -/
def K0 (R : RAMProgram) : ℕ := (R.flatMap ptrConsts).foldr max 0

lemma reg_lt {R : RAMProgram} {ins : RAMInstr} (hins : ins ∈ R) {i : ℕ} (hi : i ∈ regIdxs ins) :
    i < kOf R := by
  unfold kOf
  have := foldr_max_le (List.mem_flatMap.mpr ⟨ins, hins, hi⟩)
  omega

lemma ptr_lt {R : RAMProgram} {ins : RAMInstr} (hins : ins ∈ R) {j : ℕ} (hj : j ∈ ptrIdxs ins) :
    j < qOf R := by
  unfold qOf
  have := foldr_max_le (List.mem_flatMap.mpr ⟨ins, hins, hj⟩)
  omega

lemma const_le {R : RAMProgram} {q : ℕ} {c : ℤ} (hins : RAMInstr.pset q c ∈ R) :
    c.natAbs ≤ K0 R :=
  foldr_max_le (List.mem_flatMap.mpr ⟨_, hins, by simp [ptrConsts]⟩)

lemma ZOf_ge (R : RAMProgram) : 3 ≤ ZOf R := by unfold ZOf; omega

/-! ### Cell addresses -/

/-- Cell of real register `i`. -/
def regA (i : ℕ) : ℤ := -1 - i
/-- Cell of pointer register `j` (with `k` real registers). -/
def ptrA (k j : ℕ) : ℤ := -(k : ℤ) - 1 - j

lemma regA_inj {i i' : ℕ} : regA i = regA i' ↔ i = i' := by unfold regA; omega
lemma ptrA_inj {k j j' : ℕ} : ptrA k j = ptrA k j' ↔ j = j' := by unfold ptrA; omega
lemma regA_ne_ptrA {k i j : ℕ} (hi : i < k) : regA i ≠ ptrA k j := by unfold regA ptrA; omega

section Addr
variable {R : RAMProgram}

lemma regA_bounds {i : ℕ} (hi : i < kOf R) : -(ZOf R : ℤ) ≤ regA i ∧ regA i < 0 := by
  unfold regA ZOf; omega
lemma ptrA_bounds {j : ℕ} (hj : j < qOf R) :
    -(ZOf R : ℤ) ≤ ptrA (kOf R) j ∧ ptrA (kOf R) j < 0 := by
  unfold ptrA ZOf; omega
lemma regA_ne_H {i : ℕ} (hi : i < kOf R) : regA i ≠ Haddr (ZOf R) := by unfold regA Haddr ZOf; omega
lemma regA_ne_S1 {i : ℕ} (hi : i < kOf R) : regA i ≠ S1 (ZOf R) := by unfold regA S1 ZOf; omega
lemma regA_ne_S2 {i : ℕ} (hi : i < kOf R) : regA i ≠ S2 (ZOf R) := by unfold regA S2 ZOf; omega
lemma ptrA_ne_H {j : ℕ} (hj : j < qOf R) : ptrA (kOf R) j ≠ Haddr (ZOf R) := by
  unfold ptrA Haddr ZOf; omega
lemma ptrA_ne_S1 {j : ℕ} (hj : j < qOf R) : ptrA (kOf R) j ≠ S1 (ZOf R) := by
  unfold ptrA S1 ZOf; omega
lemma ptrA_ne_S2 {j : ℕ} (hj : j < qOf R) : ptrA (kOf R) j ≠ S2 (ZOf R) := by
  unfold ptrA S2 ZOf; omega

end Addr

/-! ### Blocks -/

/-- Length of the block compiled from an instruction. -/
def blen (Z : ℕ) : RAMInstr → ℕ
  | .load _ _ => 4 * Z + 21
  | .store _ _ => 4 * Z + 21
  | .pcopy _ _ => 2
  | .pinc _ => 2
  | .pdec _ => 2
  | .pjle _ _ _ => 2
  | _ => 1

/-- The block compiled from an instruction, placed at `base`, with jump targets given by `st`. -/
noncomputable def block (Z k : ℕ) (st : ℕ → ℕ) (base : ℕ) : RAMInstr → List BSSInstr
  | .const dst c => [.const (regA dst) c]
  | .add dst i j => [.add (regA dst) (regA i) (regA j)]
  | .sub dst i j => [.sub (regA dst) (regA i) (regA j)]
  | .mul dst i j => [.mul (regA dst) (regA i) (regA j)]
  | .div dst i j => [.div (regA dst) (regA i) (regA j)]
  | .load dst q => walkCode Z (ptrA k q) base ++ movCode (regA dst) 0
  | .store q i => walkCode Z (ptrA k q) base ++ movCode 0 (regA i)
  | .pset q c => [.const (ptrA k q) (c : ℝ)]
  | .pcopy q q' => if q = q' then [.const (S2 Z) 0, .const (S2 Z) 0] else movCode (ptrA k q) (ptrA k q')
  | .pinc q => [.const (S2 Z) 1, .add (ptrA k q) (ptrA k q) (S2 Z)]
  | .pdec q => [.const (S2 Z) 1, .sub (ptrA k q) (ptrA k q) (S2 Z)]
  | .jle i target => [.jle (regA i) (st target)]
  | .pjle q q' target => [.sub (S1 Z) (ptrA k q) (ptrA k q'), .jle (S1 Z) (st target)]
  | .accept => [.accept]
  | .reject => [.reject]

lemma block_length (Z k : ℕ) (hZ : 1 ≤ Z) (st : ℕ → ℕ) (base : ℕ) (ins : RAMInstr) :
    (block Z k st base ins).length = blen Z ins := by
  cases ins <;> simp [block, blen, movCode, walkCode_length Z hZ] <;> split_ifs <;> simp [movCode]

/-- Total length of the blocks of a list of instructions. -/
def sumLen (Z : ℕ) (L : List RAMInstr) : ℕ := (L.map (blen Z)).sum

lemma sumLen_nil (Z : ℕ) : sumLen Z [] = 0 := rfl
lemma sumLen_cons (Z : ℕ) (ins : RAMInstr) (L : List RAMInstr) :
    sumLen Z (ins :: L) = blen Z ins + sumLen Z L := by simp [sumLen]

/-- Start address of instruction `j`. -/
def starts (Z : ℕ) (R : RAMProgram) (j : ℕ) : ℕ := sumLen Z (R.take j)

lemma starts_zero (Z : ℕ) (R : RAMProgram) : starts Z R 0 = 0 := by simp [starts, sumLen]

lemma starts_succ (Z : ℕ) (R : RAMProgram) (j : ℕ) (hj : j < R.length) :
    starts Z R (j + 1) = starts Z R j + blen Z R[j] := by
  unfold starts sumLen
  rw [List.take_succ, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append,
    List.sum_append]
  simp

lemma starts_of_le (Z : ℕ) (R : RAMProgram) (j : ℕ) (hj : R.length ≤ j) :
    starts Z R j = sumLen Z R := by
  unfold starts; rw [List.take_of_length_le hj]

/-- Compile a list of instructions starting at address `base`. -/
noncomputable def compileFrom (Z k : ℕ) (st : ℕ → ℕ) : ℕ → List RAMInstr → List BSSInstr
  | _, [] => []
  | base, ins :: rest => block Z k st base ins ++ compileFrom Z k st (base + blen Z ins) rest

lemma compileFrom_length (Z k : ℕ) (hZ : 1 ≤ Z) (st : ℕ → ℕ) (base : ℕ) (L : List RAMInstr) :
    (compileFrom Z k st base L).length = sumLen Z L := by
  induction L generalizing base with
  | nil => rfl
  | cons ins rest ih => simp [compileFrom, block_length Z k hZ, sumLen_cons, ih]

/-- The compiled program. -/
noncomputable def compile (R : RAMProgram) : BSSProgram :=
  compileFrom (ZOf R) (kOf R) (starts (ZOf R) R) 0 R

/-! ### Code placement in the compiled program -/

lemma codeAt_self (code : List BSSInstr) : codeAt code 0 code := fun i _ => by simp

lemma codeAt_append_left {X Y : List BSSInstr} {a : ℕ} {code : List BSSInstr}
    (h : codeAt X a code) : codeAt (X ++ Y) a code := by
  intro i hi
  have hx := h i hi
  have hlt : a + i < X.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hx
    rw [List.getElem?_eq_getElem hi] at hx
    exact absurd hx (by simp)
  rw [List.getElem?_append_left hlt]; exact hx

lemma codeAt_append_right {X Y : List BSSInstr} {a : ℕ} {code : List BSSInstr}
    (h : codeAt Y a code) : codeAt (X ++ Y) (X.length + a) code := by
  intro i hi
  rw [show X.length + a + i = X.length + (a + i) by omega, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left]
  exact h i hi

lemma codeAt_compileFrom (Z k : ℕ) (hZ : 1 ≤ Z) (st : ℕ → ℕ) :
    ∀ (L : List RAMInstr) (base j : ℕ) (hj : j < L.length),
      codeAt (compileFrom Z k st base L) (sumLen Z (L.take j))
        (block Z k st (base + sumLen Z (L.take j)) L[j]) := by
  intro L
  induction L with
  | nil => intro base j hj; simp at hj
  | cons ins rest ih =>
    intro base j hj
    cases j with
    | zero =>
      simp only [List.take_zero, sumLen_nil, add_zero, List.getElem_cons_zero, compileFrom]
      exact codeAt_append_left (codeAt_self _)
    | succ j =>
      simp only [List.take_succ_cons, sumLen_cons, List.getElem_cons_succ, compileFrom]
      have := ih (base + blen Z ins) j (by simpa using hj)
      have h2 := codeAt_append_right (X := block Z k st base ins) this
      rw [block_length Z k hZ] at h2
      rw [show base + (blen Z ins + sumLen Z (rest.take j)) = base + blen Z ins + sumLen Z (rest.take j)
        by omega]
      exact h2

theorem codeAt_compile (R : RAMProgram) (j : ℕ) (hj : j < R.length) :
    codeAt (compile R) (starts (ZOf R) R j)
      (block (ZOf R) (kOf R) (starts (ZOf R) R) (starts (ZOf R) R j) R[j]) := by
  have := codeAt_compileFrom (ZOf R) (kOf R) (by have := ZOf_ge R; omega) (starts (ZOf R) R) R 0 j hj
  simpa [compile, starts] using this

lemma compile_length (R : RAMProgram) : (compile R).length = sumLen (ZOf R) R :=
  compileFrom_length _ _ (by have := ZOf_ge R; omega) _ _ _

lemma compile_getElem?_none (R : RAMProgram) (j : ℕ) (hj : R.length ≤ j) :
    (compile R)[starts (ZOf R) R j]? = none := by
  rw [starts_of_le _ _ _ hj, List.getElem?_eq_none]
  rw [compile_length]


/-! ## Layer: CP_Sim -/



/-- The zone represents the registers, pointers, and head position. -/
def Zone (R : RAMProgram) (regs : ℕ → ℝ) (ptrs : ℕ → ℤ) (H : ℤ) (r : ℤ → ℝ) : Prop :=
  (∀ i, i < kOf R → r (regA i) = regs i) ∧
  (∀ j, j < qOf R → r (ptrA (kOf R) j) = (ptrs j : ℝ)) ∧
  r (Haddr (ZOf R)) = (H : ℝ)

/-- The simulation relation. -/
def Sim (R : RAMProgram) (s : RAMConfig) (H : ℤ) (c : BSSConfig) : Prop :=
  c.pc = starts (ZOf R) R s.pc ∧
  ∃ r : ℤ → ℝ, c.tape = physZ (ZOf R) H s.mem r ∧ Zone R s.regs s.ptrs H r

section ZoneLemmas
variable {R : RAMProgram} {regs : ℕ → ℝ} {ptrs : ℕ → ℤ} {H : ℤ} {r : ℤ → ℝ}

lemma Zone.update_reg (hz : Zone R regs ptrs H r) {dst : ℕ} (hd : dst < kOf R) (v : ℝ) :
    Zone R (Function.update regs dst v) ptrs H (Function.update r (regA dst) v) := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
  · by_cases hid : i = dst
    · subst hid; simp
    · rw [Function.update_of_ne (by rw [Ne, regA_inj]; exact hid),
        Function.update_of_ne hid]; exact h1 i hi
  · rw [Function.update_of_ne (regA_ne_ptrA hd).symm]; exact h2 j hj
  · rw [Function.update_of_ne (regA_ne_H hd).symm]; exact h3

lemma Zone.update_ptr (hz : Zone R regs ptrs H r) {q : ℕ} (hq : q < qOf R) (v : ℤ) :
    Zone R regs (Function.update ptrs q v) H (Function.update r (ptrA (kOf R) q) (v : ℝ)) := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
  · rw [Function.update_of_ne (regA_ne_ptrA hi)]; exact h1 i hi
  · by_cases hjq : j = q
    · subst hjq; simp
    · rw [Function.update_of_ne (by rw [Ne, ptrA_inj]; exact hjq),
        Function.update_of_ne hjq]; exact h2 j hj
  · rw [Function.update_of_ne (ptrA_ne_H hq).symm]; exact h3

lemma Zone.update_S1 (hz : Zone R regs ptrs H r) (v : ℝ) :
    Zone R regs ptrs H (Function.update r (S1 (ZOf R)) v) := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
  · rw [Function.update_of_ne (regA_ne_S1 hi)]; exact h1 i hi
  · rw [Function.update_of_ne (ptrA_ne_S1 hj)]; exact h2 j hj
  · rw [Function.update_of_ne (H_ne_S1 _ (ZOf_ge R))]; exact h3

lemma Zone.update_S2 (hz : Zone R regs ptrs H r) (v : ℝ) :
    Zone R regs ptrs H (Function.update r (S2 (ZOf R)) v) := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
  · rw [Function.update_of_ne (regA_ne_S2 hi)]; exact h1 i hi
  · rw [Function.update_of_ne (ptrA_ne_S2 hj)]; exact h2 j hj
  · rw [Function.update_of_ne (H_ne_S2 _ (ZOf_ge R))]; exact h3

lemma Zone.of_pres (hz : Zone R regs ptrs H r) {r' : ℤ → ℝ} (hp : Pres (ZOf R) r r') {H' : ℤ}
    (hH' : r' (Haddr (ZOf R)) = (H' : ℝ)) : Zone R regs ptrs H' r' := by
  obtain ⟨h1, h2, _⟩ := hz
  refine ⟨fun i hi => ?_, fun j hj => ?_, hH'⟩
  · rw [hp _ (regA_ne_H hi) (regA_ne_S1 hi) (regA_ne_S2 hi)]; exact h1 i hi
  · rw [hp _ (ptrA_ne_H hj) (ptrA_ne_S1 hj) (ptrA_ne_S2 hj)]; exact h2 j hj

end ZoneLemmas

/-- The pointers of a run stay within `K0 + t`. -/
lemma ptr_bound (R : RAMProgram) (x : ℤ → ℝ) : ∀ t j, (RAMRun R x t).ptrs j ≤ K0 R + t ∧
    -((K0 R : ℤ) + t) ≤ (RAMRun R x t).ptrs j := by
  intro t
  induction t with
  | zero => intro j; simp [RAMRun]
  | succ t ih =>
    intro j
    have hstep : RAMRun R x (t + 1) = RAMStep R (RAMRun R x t) := by
      unfold RAMRun; rw [Function.iterate_succ_apply']
    rw [hstep]
    set s := RAMRun R x t with hs
    unfold RAMStep
    rcases h : R[s.pc]? with _ | ins
    · have := ih j; push_cast; constructor <;> linarith [this.1, this.2]
    · have hmem : ins ∈ R := List.mem_of_getElem? h
      cases ins <;> simp only [] <;> try (have := ih j; push_cast; constructor <;> linarith [this.1, this.2])
      · -- pset
        rename_i q c
        simp only [Function.update_apply]
        split_ifs
        · have := const_le hmem; push_cast; constructor <;> omega
        · have := ih j; push_cast; constructor <;> linarith [this.1, this.2]
      · -- pcopy
        rename_i q q'
        simp only [Function.update_apply]
        split_ifs
        · have := ih q'; push_cast; constructor <;> linarith [this.1, this.2]
        · have := ih j; push_cast; constructor <;> linarith [this.1, this.2]
      · -- pinc
        rename_i q
        simp only [Function.update_apply]
        split_ifs
        · have := ih q; push_cast; constructor <;> linarith [this.1, this.2]
        · have := ih j; push_cast; constructor <;> linarith [this.1, this.2]
      · -- pdec
        rename_i q
        simp only [Function.update_apply]
        split_ifs
        · have := ih q; push_cast; constructor <;> linarith [this.1, this.2]
        · have := ih j; push_cast; constructor <;> linarith [this.1, this.2]
      · -- jle
        split_ifs <;> (have := ih j; push_cast; constructor <;> linarith [this.1, this.2])
      · -- pjle
        split_ifs <;> (have := ih j; push_cast; constructor <;> linarith [this.1, this.2])

/-- One step of the pointer machine is simulated by a bounded run. -/
theorem sim_step (R : RAMProgram) (s : RAMConfig) (H : ℤ) (c : BSSConfig) (hs : Sim R s H c) :
    ∃ (c' : BSSConfig) (H' : ℤ), Sim R (RAMStep R s) H' c' ∧
      (H' = H ∨ ∃ j, j < qOf R ∧ H' = s.ptrs j) ∧
      Reaches (compile R) c c'
        ((2 * ZOf R + 8) * (H' - H).natAbs + (4 * ZOf R + 23)) := by
  obtain ⟨hpc, r, htape, hz⟩ := hs
  have hZ3 := ZOf_ge R
  have hc : c = ⟨starts (ZOf R) R s.pc, physZ (ZOf R) H s.mem r⟩ := by
    cases c; simp only [BSSConfig.mk.injEq]; exact ⟨hpc, htape⟩
  subst hc
  have hsame : ∀ b : ℕ, b ≤ (2 * (ZOf R) + 8) * (H - H).natAbs + (4 * (ZOf R) + 23) ↔ b ≤ 4 * (ZOf R) + 23 := by
    intro b; simp
  rcases h : R[s.pc]? with _ | ins
  · -- out of range: both machines are stuck
    refine ⟨⟨starts (ZOf R) R s.pc, physZ (ZOf R) H s.mem r⟩, H, ?_, Or.inl rfl, ?_⟩
    · unfold RAMStep; rw [h]; exact ⟨rfl, r, rfl, hz⟩
    · exact (Reaches.refl (compile R) _).mono ((hsame _).mpr (by omega))
  · have hlt : s.pc < R.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; exact absurd h (by simp)
    have hins : R[s.pc] = ins := by rw [← Option.some_inj, ← List.getElem?_eq_getElem hlt, h]
    have hmem : ins ∈ R := List.mem_of_getElem? h
    have hcode := codeAt_compile R s.pc hlt
    rw [hins] at hcode
    have hnext : starts (ZOf R) R (s.pc + 1) = starts (ZOf R) R s.pc + blen (ZOf R) ins := by
      rw [starts_succ (ZOf R) R s.pc hlt, hins]
    have hz1 := hz.1
    have hz2 := hz.2.1
    have hz3 := hz.2.2
    unfold RAMStep; rw [h]
    cases ins with
    | const dst v =>
      dsimp only
      have hd : dst < (kOf R) := reg_lt hmem (by simp [regIdxs])
      simp only [block] at hcode
      obtain ⟨h0, _⟩ := codeAt_cons hcode
      have hr := reachesZ_const h0 (regA_bounds hd).1 (regA_bounds hd).2 H s.mem r
      refine ⟨_, H, ?_, Or.inl rfl, hr.mono ((hsame _).mpr (by omega))⟩
      exact ⟨by simp [hnext, blen], _, rfl, hz.update_reg hd v⟩
    | add dst i j =>
      dsimp only
      have hd : dst < (kOf R) := reg_lt hmem (by simp [regIdxs])
      have hi : i < (kOf R) := reg_lt hmem (by simp [regIdxs])
      have hj : j < (kOf R) := reg_lt hmem (by simp [regIdxs])
      simp only [block] at hcode
      obtain ⟨h0, _⟩ := codeAt_cons hcode
      have hr := reachesZ_add h0 (regA_bounds hd).1 (regA_bounds hd).2 (regA_bounds hi).1
        (regA_bounds hi).2 (regA_bounds hj).1 (regA_bounds hj).2 H s.mem r
      rw [hz1 i hi, hz1 j hj] at hr
      refine ⟨_, H, ?_, Or.inl rfl, hr.mono ((hsame _).mpr (by omega))⟩
      exact ⟨by simp [hnext, blen], _, rfl, hz.update_reg hd _⟩
    | sub dst i j =>
      dsimp only
      have hd : dst < (kOf R) := reg_lt hmem (by simp [regIdxs])
      have hi : i < (kOf R) := reg_lt hmem (by simp [regIdxs])
      have hj : j < (kOf R) := reg_lt hmem (by simp [regIdxs])
      simp only [block] at hcode
      obtain ⟨h0, _⟩ := codeAt_cons hcode
      have hr := reachesZ_sub h0 (regA_bounds hd).1 (regA_bounds hd).2 (regA_bounds hi).1
        (regA_bounds hi).2 (regA_bounds hj).1 (regA_bounds hj).2 H s.mem r
      rw [hz1 i hi, hz1 j hj] at hr
      refine ⟨_, H, ?_, Or.inl rfl, hr.mono ((hsame _).mpr (by omega))⟩
      exact ⟨by simp [hnext, blen], _, rfl, hz.update_reg hd _⟩
    | mul dst i j =>
      dsimp only
      have hd : dst < (kOf R) := reg_lt hmem (by simp [regIdxs])
      have hi : i < (kOf R) := reg_lt hmem (by simp [regIdxs])
      have hj : j < (kOf R) := reg_lt hmem (by simp [regIdxs])
      simp only [block] at hcode
      obtain ⟨h0, _⟩ := codeAt_cons hcode
      have hr := reachesZ_mul h0 (regA_bounds hd).1 (regA_bounds hd).2 (regA_bounds hi).1
        (regA_bounds hi).2 (regA_bounds hj).1 (regA_bounds hj).2 H s.mem r
      rw [hz1 i hi, hz1 j hj] at hr
      refine ⟨_, H, ?_, Or.inl rfl, hr.mono ((hsame _).mpr (by omega))⟩
      exact ⟨by simp [hnext, blen], _, rfl, hz.update_reg hd _⟩
    | div dst i j =>
      dsimp only
      have hd : dst < (kOf R) := reg_lt hmem (by simp [regIdxs])
      have hi : i < (kOf R) := reg_lt hmem (by simp [regIdxs])
      have hj : j < (kOf R) := reg_lt hmem (by simp [regIdxs])
      simp only [block] at hcode
      obtain ⟨h0, _⟩ := codeAt_cons hcode
      have hr := reachesZ_div h0 (regA_bounds hd).1 (regA_bounds hd).2 (regA_bounds hi).1
        (regA_bounds hi).2 (regA_bounds hj).1 (regA_bounds hj).2 H s.mem r
      rw [hz1 i hi, hz1 j hj] at hr
      refine ⟨_, H, ?_, Or.inl rfl, hr.mono ((hsame _).mpr (by omega))⟩
      exact ⟨by simp [hnext, blen], _, rfl, hz.update_reg hd _⟩
    | load dst q =>
      dsimp only
      have hd : dst < (kOf R) := reg_lt hmem (by simp [regIdxs])
      have hq : q < qOf R := ptr_lt hmem (by simp [ptrIdxs])
      simp only [block] at hcode
      obtain ⟨hw, hm⟩ := codeAt_append hcode
      rw [walkCode_length (ZOf R) (by omega)] at hm
      obtain ⟨hw1, hpqb⟩ := ptrA_bounds hq
      obtain ⟨r₁, hpres, hH₁, sW⟩ := walk (ZOf R) hZ3 (starts (ZOf R) R s.pc) (ptrA (kOf R) q) hw1 hpqb
        (ptrA_ne_H hq) (ptrA_ne_S1 hq) (ptrA_ne_S2 hq) hw s.mem H (s.ptrs q) r hz3 (hz2 q hq)
      simp only [movCode] at hm
      obtain ⟨m0, hm'⟩ := codeAt_cons hm
      obtain ⟨m1, _⟩ := codeAt_cons hm'
      have sM := reachesZ_mov_head m0 m1 (regA_bounds hd).1 (regA_bounds hd).2 (s.ptrs q) s.mem r₁
      have hz' : Zone R s.regs s.ptrs (s.ptrs q) r₁ := hz.of_pres hpres hH₁
      refine ⟨_, s.ptrs q, ?_, Or.inr ⟨q, hq, rfl⟩, (sW.trans sM).mono (by linarith)⟩
      exact ⟨by simp only [hnext, blen]; omega, _, rfl, hz'.update_reg hd _⟩
    | store q i =>
      dsimp only
      have hi : i < (kOf R) := reg_lt hmem (by simp [regIdxs])
      have hq : q < qOf R := ptr_lt hmem (by simp [ptrIdxs])
      simp only [block] at hcode
      obtain ⟨hw, hm⟩ := codeAt_append hcode
      rw [walkCode_length (ZOf R) (by omega)] at hm
      obtain ⟨hw1, hpqb⟩ := ptrA_bounds hq
      obtain ⟨r₁, hpres, hH₁, sW⟩ := walk (ZOf R) hZ3 (starts (ZOf R) R s.pc) (ptrA (kOf R) q) hw1 hpqb
        (ptrA_ne_H hq) (ptrA_ne_S1 hq) (ptrA_ne_S2 hq) hw s.mem H (s.ptrs q) r hz3 (hz2 q hq)
      simp only [movCode] at hm
      obtain ⟨m0, hm'⟩ := codeAt_cons hm
      obtain ⟨m1, _⟩ := codeAt_cons hm'
      have sM := reachesZ_store m0 m1 (regA_bounds hi).1 (regA_bounds hi).2 (s.ptrs q) s.mem r₁
      have hz' : Zone R s.regs s.ptrs (s.ptrs q) r₁ := hz.of_pres hpres hH₁
      rw [hz'.1 i hi] at sM
      refine ⟨_, s.ptrs q, ?_, Or.inr ⟨q, hq, rfl⟩, (sW.trans sM).mono (by linarith)⟩
      exact ⟨by simp only [hnext, blen]; omega, _, rfl, hz'⟩
    | pset q v =>
      dsimp only
      have hq : q < qOf R := ptr_lt hmem (by simp [ptrIdxs])
      simp only [block] at hcode
      obtain ⟨h0, _⟩ := codeAt_cons hcode
      have hr := reachesZ_const h0 (ptrA_bounds hq).1 (ptrA_bounds hq).2 H s.mem r
      refine ⟨_, H, ?_, Or.inl rfl, hr.mono ((hsame _).mpr (by omega))⟩
      exact ⟨by simp [hnext, blen], _, rfl, hz.update_ptr hq v⟩
    | pcopy q q' =>
      dsimp only
      have hq : q < qOf R := ptr_lt hmem (by simp [ptrIdxs])
      have hq' : q' < qOf R := ptr_lt hmem (by simp [ptrIdxs])
      simp only [block] at hcode
      by_cases hqq : q = q'
      · subst hqq
        rw [if_pos rfl] at hcode
        obtain ⟨h0, hcode'⟩ := codeAt_cons hcode
        obtain ⟨h1, _⟩ := codeAt_cons hcode'
        have s1 := reachesZ_const h0 (S2_bounds (ZOf R) hZ3).1 (S2_bounds (ZOf R) hZ3).2 H s.mem r
        have s2 := reachesZ_const h1 (S2_bounds (ZOf R) hZ3).1 (S2_bounds (ZOf R) hZ3).2 H s.mem
          (Function.update r (S2 (ZOf R)) 0)
        refine ⟨_, H, ?_, Or.inl rfl, (s1.trans s2).mono ((hsame _).mpr (by omega))⟩
        refine ⟨by simp [hnext, blen], _, rfl, ?_⟩
        have : Function.update s.ptrs q (s.ptrs q) = s.ptrs := Function.update_eq_self _ _
        rw [this]
        exact (hz.update_S2 _).update_S2 _
      · rw [if_neg hqq] at hcode
        simp only [movCode] at hcode
        obtain ⟨h0, hcode'⟩ := codeAt_cons hcode
        obtain ⟨h1, _⟩ := codeAt_cons hcode'
        have hr := reachesZ_mov_reg h0 h1 (ptrA_bounds hq).1 (ptrA_bounds hq).2 (ptrA_bounds hq').1
          (ptrA_bounds hq').2 (by rw [Ne, ptrA_inj]; exact hqq) H s.mem r
        rw [hz2 q' hq'] at hr
        refine ⟨_, H, ?_, Or.inl rfl, hr.mono ((hsame _).mpr (by omega))⟩
        exact ⟨by simp [hnext, blen], _, rfl, hz.update_ptr hq _⟩
    | pinc q =>
      dsimp only
      have hq : q < qOf R := ptr_lt hmem (by simp [ptrIdxs])
      simp only [block] at hcode
      obtain ⟨h0, hcode'⟩ := codeAt_cons hcode
      obtain ⟨h1, _⟩ := codeAt_cons hcode'
      have s1 := reachesZ_const h0 (S2_bounds (ZOf R) hZ3).1 (S2_bounds (ZOf R) hZ3).2 H s.mem r
      set r₁ := Function.update r (S2 (ZOf R)) (1 : ℝ) with hr₁
      have s2 := reachesZ_add h1 (ptrA_bounds hq).1 (ptrA_bounds hq).2 (ptrA_bounds hq).1
        (ptrA_bounds hq).2 (S2_bounds (ZOf R) hZ3).1 (S2_bounds (ZOf R) hZ3).2 H s.mem r₁
      have hval : r₁ (ptrA (kOf R) q) + r₁ (S2 (ZOf R)) = ((s.ptrs q + 1 : ℤ) : ℝ) := by
        simp [hr₁, ptrA_ne_S2 hq, hz2 q hq]
      rw [hval] at s2
      refine ⟨_, H, ?_, Or.inl rfl, (s1.trans s2).mono ((hsame _).mpr (by omega))⟩
      exact ⟨by simp [hnext, blen], _, rfl, (hz.update_S2 _).update_ptr hq _⟩
    | pdec q =>
      dsimp only
      have hq : q < qOf R := ptr_lt hmem (by simp [ptrIdxs])
      simp only [block] at hcode
      obtain ⟨h0, hcode'⟩ := codeAt_cons hcode
      obtain ⟨h1, _⟩ := codeAt_cons hcode'
      have s1 := reachesZ_const h0 (S2_bounds (ZOf R) hZ3).1 (S2_bounds (ZOf R) hZ3).2 H s.mem r
      set r₁ := Function.update r (S2 (ZOf R)) (1 : ℝ) with hr₁
      have s2 := reachesZ_sub h1 (ptrA_bounds hq).1 (ptrA_bounds hq).2 (ptrA_bounds hq).1
        (ptrA_bounds hq).2 (S2_bounds (ZOf R) hZ3).1 (S2_bounds (ZOf R) hZ3).2 H s.mem r₁
      have hval : r₁ (ptrA (kOf R) q) - r₁ (S2 (ZOf R)) = ((s.ptrs q - 1 : ℤ) : ℝ) := by
        simp [hr₁, ptrA_ne_S2 hq, hz2 q hq]
      rw [hval] at s2
      refine ⟨_, H, ?_, Or.inl rfl, (s1.trans s2).mono ((hsame _).mpr (by omega))⟩
      exact ⟨by simp [hnext, blen], _, rfl, (hz.update_S2 _).update_ptr hq _⟩
    | jle i target =>
      dsimp only
      have hi : i < (kOf R) := reg_lt hmem (by simp [regIdxs])
      simp only [block] at hcode
      obtain ⟨h0, _⟩ := codeAt_cons hcode
      by_cases ht : s.regs i ≤ 0
      · rw [if_pos ht]
        have hr := reachesZ_jle_le h0 (regA_bounds hi).1 (regA_bounds hi).2 H s.mem r
          (by rw [hz1 i hi]; exact ht)
        refine ⟨_, H, ?_, Or.inl rfl, hr.mono ((hsame _).mpr (by omega))⟩
        exact ⟨rfl, r, rfl, hz⟩
      · rw [if_neg ht]
        have hr := reachesZ_jle_pos h0 (regA_bounds hi).1 (regA_bounds hi).2 H s.mem r
          (by rw [hz1 i hi]; exact lt_of_not_ge ht)
        refine ⟨_, H, ?_, Or.inl rfl, hr.mono ((hsame _).mpr (by omega))⟩
        exact ⟨by simp [hnext, blen], r, rfl, hz⟩
    | pjle q q' target =>
      dsimp only
      have hq : q < qOf R := ptr_lt hmem (by simp [ptrIdxs])
      have hq' : q' < qOf R := ptr_lt hmem (by simp [ptrIdxs])
      simp only [block] at hcode
      obtain ⟨h0, hcode'⟩ := codeAt_cons hcode
      obtain ⟨h1, _⟩ := codeAt_cons hcode'
      have s1 := reachesZ_sub h0 (S1_bounds (ZOf R) hZ3).1 (S1_bounds (ZOf R) hZ3).2 (ptrA_bounds hq).1
        (ptrA_bounds hq).2 (ptrA_bounds hq').1 (ptrA_bounds hq').2 H s.mem r
      set r₁ := Function.update r (S1 (ZOf R)) (r (ptrA (kOf R) q) - r (ptrA (kOf R) q')) with hr₁
      have hr₁S : r₁ (S1 (ZOf R)) = ((s.ptrs q - s.ptrs q' : ℤ) : ℝ) := by
        simp [hr₁, hz2 q hq, hz2 q' hq']
      have hz' : Zone R s.regs s.ptrs H r₁ := hz.update_S1 _
      by_cases ht : s.ptrs q ≤ s.ptrs q'
      · rw [if_pos ht]
        have s2 := reachesZ_jle_le h1 (S1_bounds (ZOf R) hZ3).1 (S1_bounds (ZOf R) hZ3).2 H s.mem r₁
          (by rw [hr₁S]; exact_mod_cast (by omega : s.ptrs q - s.ptrs q' ≤ 0))
        refine ⟨_, H, ?_, Or.inl rfl, (s1.trans s2).mono ((hsame _).mpr (by omega))⟩
        exact ⟨rfl, r₁, rfl, hz'⟩
      · rw [if_neg ht]
        have s2 := reachesZ_jle_pos h1 (S1_bounds (ZOf R) hZ3).1 (S1_bounds (ZOf R) hZ3).2 H s.mem r₁
          (by rw [hr₁S]; exact_mod_cast (by omega : 0 < s.ptrs q - s.ptrs q'))
        refine ⟨_, H, ?_, Or.inl rfl, (s1.trans s2).mono ((hsame _).mpr (by omega))⟩
        exact ⟨by simp [hnext, blen], r₁, rfl, hz'⟩
    | accept =>
      dsimp only
      refine ⟨⟨starts (ZOf R) R s.pc, physZ (ZOf R) H s.mem r⟩, H, ⟨rfl, r, rfl, hz⟩, Or.inl rfl, ?_⟩
      exact (Reaches.refl (compile R) _).mono ((hsame _).mpr (by omega))
    | reject =>
      dsimp only
      refine ⟨⟨starts (ZOf R) R s.pc, physZ (ZOf R) H s.mem r⟩, H, ⟨rfl, r, rfl, hz⟩, Or.inl rfl, ?_⟩
      exact (Reaches.refl (compile R) _).mono ((hsame _).mpr (by omega))


/-! ## Layer: CP_Main -/



lemma RAMRun_succ (R : RAMProgram) (x : ℤ → ℝ) (t : ℕ) :
    RAMRun R x (t + 1) = RAMStep R (RAMRun R x t) := by
  unfold RAMRun; rw [Function.iterate_succ_apply']

/-- The initial tape is a zone tape with zero registers when the input vanishes on
negative cells. -/
lemma physZ_init (Z : ℕ) (x : ℤ → ℝ) (hx : ∀ c : ℤ, c < 0 → x c = 0) :
    x = physZ Z 0 x (fun _ => 0) := by
  funext c
  unfold physZ
  split_ifs with h1 h2
  · simp
  · exact hx c (by omega)
  · rw [hx c (by omega), hx _ (by omega)]

/-- The per-step budget for runs of length at most `T`. -/
def stepBudget (R : RAMProgram) (T : ℕ) : ℕ :=
  (2 * ZOf R + 8) * (2 * (K0 R + T)) + (4 * ZOf R + 23)

/-- The whole run is simulated. -/
theorem sim_run (R : RAMProgram) (x : ℤ → ℝ) (hx : ∀ c : ℤ, c < 0 → x c = 0) (T : ℕ) :
    ∀ t ≤ T, ∃ (c : BSSConfig) (H : ℤ), Sim R (RAMRun R x t) H c ∧
      H ≤ K0 R + t ∧ -((K0 R : ℤ) + t) ≤ H ∧
      Reaches (compile R) ⟨0, x⟩ c (t * stepBudget R T) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨⟨0, x⟩, 0, ⟨?_, fun _ => 0, ?_, ?_, ?_, ?_⟩, by simp, by simp, ?_⟩
    · simp [RAMRun, starts_zero]
    · exact physZ_init _ x hx
    · intro i _; simp [RAMRun]
    · intro j _; simp [RAMRun]
    · simp
    · simpa using Reaches.refl (compile R) _
  | succ t ih =>
    intro ht
    obtain ⟨c, H, hsim, hH1, hH2, hreach⟩ := ih (by omega)
    obtain ⟨c', H', hsim', hH', hstep⟩ := sim_step R (RAMRun R x t) H c hsim
    rw [← RAMRun_succ] at hsim'
    have hbound : H' ≤ K0 R + t ∧ -((K0 R : ℤ) + t) ≤ H' := by
      rcases hH' with rfl | ⟨j, _, rfl⟩
      · exact ⟨hH1, hH2⟩
      · exact ptr_bound R x t j
    refine ⟨c', H', hsim', by omega, by omega, ?_⟩
    have hdist : (H' - H).natAbs ≤ 2 * (K0 R + T) := by omega
    have hcost : (2 * ZOf R + 8) * (H' - H).natAbs + (4 * ZOf R + 23) ≤ stepBudget R T := by
      unfold stepBudget
      have := Nat.mul_le_mul_left (2 * ZOf R + 8) hdist
      omega
    have := hreach.trans (hstep.mono hcost)
    refine this.mono ?_
    rw [Nat.succ_mul]

/-- The constant of the compilation theorem. -/
def Kconst (R : RAMProgram) : ℕ := (2 * ZOf R + 8) * (2 * (K0 R + 1)) + (4 * ZOf R + 23)

lemma budget_le (R : RAMProgram) (T : ℕ) : T * stepBudget R T ≤ Kconst R * (T + 1) ^ 2 := by
  unfold stepBudget Kconst
  have h1 : 2 * (K0 R + T) ≤ 2 * (K0 R + 1) * (T + 1) := by nlinarith
  have h2 : (2 * ZOf R + 8) * (2 * (K0 R + T)) ≤ (2 * ZOf R + 8) * (2 * (K0 R + 1)) * (T + 1) := by
    calc (2 * ZOf R + 8) * (2 * (K0 R + T)) ≤ (2 * ZOf R + 8) * (2 * (K0 R + 1) * (T + 1)) :=
          Nat.mul_le_mul_left _ h1
      _ = (2 * ZOf R + 8) * (2 * (K0 R + 1)) * (T + 1) := by ring
  have h3 : 4 * ZOf R + 23 ≤ (4 * ZOf R + 23) * (T + 1) := by nlinarith
  calc T * ((2 * ZOf R + 8) * (2 * (K0 R + T)) + (4 * ZOf R + 23))
      ≤ T * ((2 * ZOf R + 8) * (2 * (K0 R + 1)) * (T + 1) + (4 * ZOf R + 23) * (T + 1)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add h2 h3)
    _ = ((2 * ZOf R + 8) * (2 * (K0 R + 1)) + (4 * ZOf R + 23)) * (T * (T + 1)) := by ring
    _ ≤ ((2 * ZOf R + 8) * (2 * (K0 R + 1)) + (4 * ZOf R + 23)) * (T + 1) ^ 2 := by
        apply Nat.mul_le_mul_left; nlinarith

/-- **Compilation theorem.** -/
theorem ram_to_bss (R : RAMProgram) :
    ∃ (P : BSSProgram) (K : ℕ), ∀ (x : ℤ → ℝ), (∀ c : ℤ, c < 0 → x c = 0) →
      ∀ (T : ℕ) (b : Bool),
        RAMDecidesInTime R x T b → BSSDecidesInTime P x (K * (T + 1) ^ 2) b := by
  refine ⟨compile R, Kconst R, fun x hx T b hdec => ?_⟩
  obtain ⟨t, ht, hhalt⟩ := hdec
  obtain ⟨c, H, ⟨hpc, _⟩, _, _, hreach⟩ := sim_run R x hx T t ht
  unfold RAMHaltedWith at hhalt
  set s := RAMRun R x t with hs
  have hlt : s.pc < R.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hhalt; exact absurd hhalt (by simp)
  have hins : R[s.pc] = if b then RAMInstr.accept else RAMInstr.reject := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem hlt, hhalt]
  have hcode := codeAt_compile R s.pc hlt
  rw [hins] at hcode
  have hP : (compile R)[c.pc]? = some (if b then BSSInstr.accept else BSSInstr.reject) := by
    rw [hpc]
    cases b <;> simp only [block] at hcode <;> exact (codeAt_cons hcode).1
  obtain ⟨t', ht', hrun⟩ := hreach
  refine ⟨t', le_trans ht' ?_, ?_⟩
  · exact le_trans (Nat.mul_le_mul_right _ ht) (budget_le R T)
  · unfold BSSHaltedWith BSSRun
    rw [hrun]; exact hP


end SmaleNinth.CP

theorem solution (R : RAMProgram) :
    ∃ (P : BSSProgram) (K : ℕ), ∀ (x : ℤ → ℝ), (∀ c : ℤ, c < 0 → x c = 0) →
      ∀ (T : ℕ) (b : Bool),
        RAMDecidesInTime R x T b → BSSDecidesInTime P x (K * (T + 1) ^ 2) b :=
  SmaleNinth.CP.ram_to_bss R

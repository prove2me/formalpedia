-- Prove2me | solution 1 for SmaleNinth.bss_decides_one_variable_lp_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T17:27:57.130735+00:00
-- url     : https://prove2.me/submissions/175b9a2e-06d9-4dc4-81cf-a16694f6bfa3

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine
import Mathlib.Tactic

/-!
# One-variable LP feasibility on a BSS machine in quadratic time

A concrete uniform program `prog` (151 instructions) decides the feasibility
of `aᵢ x ≥ bᵢ (i < m)` on the standard encoding within `100 (m+1)²` steps.

Architecture. The tape is kept in the shape `phys h d r`: the logical input
`d` is never modified, the head sits at logical position `h` (physical cell
`0`), and eleven register cells `-1 … -11` (counter, outer counter, `m`, the
current coefficient, `L`, `HL`, `R`, `HR`, `BAD`, two scratch cells) travel
with the head; the data to the left of the head is displaced by eleven
cells. A walk of one cell is `shiftL`/`shiftR` followed by eleven `mov`s
that put the register zone back in place (`effR`/`effL`). For each
constraint the program reads `aᵢ`, walks `m` cells to `bᵢ`, updates the
running interval `[L, R]` with presence flags and the infeasibility flag
(`upd`), and walks `m − 1` cells back to `aᵢ₊₁`. The abstract state
after `i` constraints (`stF`) is characterised by `Spec`, and the verdict
`BAD ≤ 0 ∧ (HL ≤ 0 ∨ HR ≤ 0 ∨ L ≤ R)` is equivalent to feasibility.
-/

/-!
Core machinery for verifying a concrete BSS program: bounded reachability,
single-instruction step lemmas, and the "physical tape" encoding that keeps a
zone of eleven register cells (`-1 … -11`) immediately to the left of the head
while the logical data stays fixed.
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

lemma decides_of_reaches {P : BSSProgram} {x : ℤ → ℝ} {pc : ℕ} {τ : ℤ → ℝ} {b : ℕ}
    {res : Bool} (h : Reaches P ⟨0, x⟩ ⟨pc, τ⟩ b)
    (hpc : P[pc]? = some (if res then BSSInstr.accept else BSSInstr.reject)) :
    BSSDecidesInTime P x b res := by
  obtain ⟨t, ht, e⟩ := h
  exact ⟨t, ht, by unfold BSSHaltedWith BSSRun; rw [e]; exact hpc⟩

/-! ### The physical tape -/

/-- Physical tape with head position `h`, logical data `d`, register zone `r`
(cells `-1 … -11`); the data to the left of the head is displaced by `11`. -/
def phys (h : ℤ) (d r : ℤ → ℝ) : ℤ → ℝ := fun k =>
  if 0 ≤ k then d (h + k) else if -11 ≤ k then r k else d (h + k + 11)

lemma phys_of_nonneg {h : ℤ} {d r : ℤ → ℝ} {k : ℤ} (hk : 0 ≤ k) : phys h d r k = d (h + k) := by
  simp [phys, hk]

lemma phys_zero (h : ℤ) (d r : ℤ → ℝ) : phys h d r 0 = d h := by simp [phys]

lemma phys_reg {h : ℤ} {d r : ℤ → ℝ} {k : ℤ} (hk1 : -11 ≤ k) (hk2 : k < 0) :
    phys h d r k = r k := by
  simp [phys, hk1, not_le.mpr hk2]

lemma phys_of_lt {h : ℤ} {d r : ℤ → ℝ} {k : ℤ} (hk : k < -11) :
    phys h d r k = d (h + k + 11) := by
  simp [phys, show ¬ (0 ≤ k) by omega, show ¬ (-11 ≤ k) by omega]

lemma update_phys_reg {h : ℤ} {d r : ℤ → ℝ} {j : ℤ} (hj1 : -11 ≤ j) (hj2 : j < 0) (v : ℝ) :
    Function.update (phys h d r) j v = phys h d (Function.update r j v) := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [phys_reg hj1 hj2]
  · rw [Function.update_of_ne hk]
    unfold phys
    rw [Function.update_of_ne hk]

lemma phys_ext {h : ℤ} {d r r' : ℤ → ℝ} (e : ∀ k, -11 ≤ k → k < 0 → r k = r' k) :
    phys h d r = phys h d r' := by
  funext k; unfold phys
  split_ifs with h1 h2
  · rfl
  · exact e k h2 (by omega)
  · rfl

/-! ### Register-level instruction lemmas -/

lemma reaches_const_reg {P : BSSProgram} {pc : ℕ} {j : ℤ} {c : ℝ}
    (hP : P[pc]? = some (.const j c)) (hj1 : -11 ≤ j) (hj2 : j < 0)
    (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨pc, phys h d r⟩ ⟨pc + 1, phys h d (Function.update r j c)⟩ 1 :=
  Reaches.single (by rw [step_const hP, update_phys_reg hj1 hj2])

lemma reaches_sub_reg {P : BSSProgram} {pc : ℕ} {j a b : ℤ}
    (hP : P[pc]? = some (.sub j a b)) (hj1 : -11 ≤ j) (hj2 : j < 0)
    (ha1 : -11 ≤ a) (ha2 : a < 0) (hb1 : -11 ≤ b) (hb2 : b < 0)
    (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨pc, phys h d r⟩ ⟨pc + 1, phys h d (Function.update r j (r a - r b))⟩ 1 :=
  Reaches.single (by
    rw [step_sub hP, phys_reg ha1 ha2, phys_reg hb1 hb2, update_phys_reg hj1 hj2])

lemma reaches_div_head_reg {P : BSSProgram} {pc : ℕ} {j b : ℤ}
    (hP : P[pc]? = some (.div j 0 b)) (hj1 : -11 ≤ j) (hj2 : j < 0)
    (hb1 : -11 ≤ b) (hb2 : b < 0) (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨pc, phys h d r⟩ ⟨pc + 1, phys h d (Function.update r j (d h / r b))⟩ 1 :=
  Reaches.single (by
    rw [step_div hP, phys_zero, phys_reg hb1 hb2, update_phys_reg hj1 hj2])

lemma reaches_mov_reg {P : BSSProgram} {pc : ℕ} {j s : ℤ}
    (h0 : P[pc]? = some (.const j 0)) (h1 : P[pc + 1]? = some (.add j j s))
    (hj1 : -11 ≤ j) (hj2 : j < 0) (hs1 : -11 ≤ s) (hs2 : s < 0) (hne : j ≠ s)
    (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨pc, phys h d r⟩ ⟨pc + 2, phys h d (Function.update r j (r s))⟩ 2 :=
  (reaches_mov h0 h1 hne _).cast (by rw [phys_reg hs1 hs2, update_phys_reg hj1 hj2])

lemma reaches_mov_head {P : BSSProgram} {pc : ℕ} {j : ℤ}
    (h0 : P[pc]? = some (.const j 0)) (h1 : P[pc + 1]? = some (.add j j 0))
    (hj1 : -11 ≤ j) (hj2 : j < 0) (h : ℤ) (d r : ℤ → ℝ) :
    Reaches P ⟨pc, phys h d r⟩ ⟨pc + 2, phys h d (Function.update r j (d h))⟩ 2 :=
  (reaches_mov h0 h1 (by omega) _).cast (by rw [phys_zero, update_phys_reg hj1 hj2])

lemma reaches_jle_reg_le {P : BSSProgram} {pc : ℕ} {j : ℤ} {target : ℕ}
    (hP : P[pc]? = some (.jle j target)) (hj1 : -11 ≤ j) (hj2 : j < 0)
    (h : ℤ) (d r : ℤ → ℝ) (hr : r j ≤ 0) :
    Reaches P ⟨pc, phys h d r⟩ ⟨target, phys h d r⟩ 1 :=
  Reaches.single (step_jle_of_le hP _ (by rw [phys_reg hj1 hj2]; exact hr))

lemma reaches_jle_reg_pos {P : BSSProgram} {pc : ℕ} {j : ℤ} {target : ℕ}
    (hP : P[pc]? = some (.jle j target)) (hj1 : -11 ≤ j) (hj2 : j < 0)
    (h : ℤ) (d r : ℤ → ℝ) (hr : 0 < r j) :
    Reaches P ⟨pc, phys h d r⟩ ⟨pc + 1, phys h d r⟩ 1 :=
  Reaches.single (step_jle_of_pos hP _ (by rw [phys_reg hj1 hj2]; exact hr))

lemma reaches_jle_head_le {P : BSSProgram} {pc : ℕ} {target : ℕ}
    (hP : P[pc]? = some (.jle 0 target)) (h : ℤ) (d r : ℤ → ℝ) (hd : d h ≤ 0) :
    Reaches P ⟨pc, phys h d r⟩ ⟨target, phys h d r⟩ 1 :=
  Reaches.single (step_jle_of_le hP _ (by rw [phys_zero]; exact hd))

lemma reaches_jle_head_pos {P : BSSProgram} {pc : ℕ} {target : ℕ}
    (hP : P[pc]? = some (.jle 0 target)) (h : ℤ) (d r : ℤ → ℝ) (hd : 0 < d h) :
    Reaches P ⟨pc, phys h d r⟩ ⟨pc + 1, phys h d r⟩ 1 :=
  Reaches.single (step_jle_of_pos hP _ (by rw [phys_zero]; exact hd))

/-! ### The program -/

/-- The one-variable LP decision program (addresses in comments). -/
noncomputable def prog : BSSProgram := [
  .const (-3) 0,  -- 0
  .add (-3) (-3) (0),  -- 1
  .const (-2) 0,  -- 2
  .add (-2) (-2) (0),  -- 3
  .shiftL,  -- 4
  .const (-12) 0,  -- 5
  .add (-12) (-12) (-1),  -- 6
  .const (-1) 0,  -- 7
  .add (-1) (-1) (-2),  -- 8
  .const (-2) 0,  -- 9
  .add (-2) (-2) (-3),  -- 10
  .const (-3) 0,  -- 11
  .add (-3) (-3) (-4),  -- 12
  .const (-4) 0,  -- 13
  .add (-4) (-4) (-5),  -- 14
  .const (-5) 0,  -- 15
  .add (-5) (-5) (-6),  -- 16
  .const (-6) 0,  -- 17
  .add (-6) (-6) (-7),  -- 18
  .const (-7) 0,  -- 19
  .add (-7) (-7) (-8),  -- 20
  .const (-8) 0,  -- 21
  .add (-8) (-8) (-9),  -- 22
  .const (-9) 0,  -- 23
  .add (-9) (-9) (-10),  -- 24
  .const (-10) 0,  -- 25
  .add (-10) (-10) (-11),  -- 26
  .shiftL,  -- 27
  .const (-12) 0,  -- 28
  .add (-12) (-12) (-1),  -- 29
  .const (-1) 0,  -- 30
  .add (-1) (-1) (-2),  -- 31
  .const (-2) 0,  -- 32
  .add (-2) (-2) (-3),  -- 33
  .const (-3) 0,  -- 34
  .add (-3) (-3) (-4),  -- 35
  .const (-4) 0,  -- 36
  .add (-4) (-4) (-5),  -- 37
  .const (-5) 0,  -- 38
  .add (-5) (-5) (-6),  -- 39
  .const (-6) 0,  -- 40
  .add (-6) (-6) (-7),  -- 41
  .const (-7) 0,  -- 42
  .add (-7) (-7) (-8),  -- 43
  .const (-8) 0,  -- 44
  .add (-8) (-8) (-9),  -- 45
  .const (-9) 0,  -- 46
  .add (-9) (-9) (-10),  -- 47
  .const (-10) 0,  -- 48
  .add (-10) (-10) (-11),  -- 49
  .jle (-2) 143,  -- 50
  .const (-4) 0,  -- 51
  .add (-4) (-4) (0),  -- 52
  .const (-1) 0,  -- 53
  .add (-1) (-1) (-3),  -- 54
  .jle (-1) 83,  -- 55
  .shiftL,  -- 56
  .const (-12) 0,  -- 57
  .add (-12) (-12) (-1),  -- 58
  .const (-1) 0,  -- 59
  .add (-1) (-1) (-2),  -- 60
  .const (-2) 0,  -- 61
  .add (-2) (-2) (-3),  -- 62
  .const (-3) 0,  -- 63
  .add (-3) (-3) (-4),  -- 64
  .const (-4) 0,  -- 65
  .add (-4) (-4) (-5),  -- 66
  .const (-5) 0,  -- 67
  .add (-5) (-5) (-6),  -- 68
  .const (-6) 0,  -- 69
  .add (-6) (-6) (-7),  -- 70
  .const (-7) 0,  -- 71
  .add (-7) (-7) (-8),  -- 72
  .const (-8) 0,  -- 73
  .add (-8) (-8) (-9),  -- 74
  .const (-9) 0,  -- 75
  .add (-9) (-9) (-10),  -- 76
  .const (-10) 0,  -- 77
  .add (-10) (-10) (-11),  -- 78
  .const (-11) 1,  -- 79
  .sub (-1) (-1) (-11),  -- 80
  .const (-11) 0,  -- 81
  .jle (-11) 55,  -- 82
  .jle (-4) 93,  -- 83
  .div (-10) 0 (-4),  -- 84
  .jle (-6) 88,  -- 85
  .sub (-11) (-10) (-5),  -- 86
  .jle (-11) 107,  -- 87
  .const (-5) 0,  -- 88
  .add (-5) (-5) (-10),  -- 89
  .const (-6) 1,  -- 90
  .const (-11) 0,  -- 91
  .jle (-11) 107,  -- 92
  .const (-10) 0,  -- 93
  .sub (-10) (-10) (-4),  -- 94
  .jle (-10) 105,  -- 95
  .div (-10) 0 (-4),  -- 96
  .jle (-8) 100,  -- 97
  .sub (-11) (-7) (-10),  -- 98
  .jle (-11) 107,  -- 99
  .const (-7) 0,  -- 100
  .add (-7) (-7) (-10),  -- 101
  .const (-8) 1,  -- 102
  .const (-11) 0,  -- 103
  .jle (-11) 107,  -- 104
  .jle (0) 107,  -- 105
  .const (-9) 1,  -- 106
  .const (-1) 0,  -- 107
  .add (-1) (-1) (-3),  -- 108
  .const (-11) 1,  -- 109
  .sub (-1) (-1) (-11),  -- 110
  .jle (-1) 139,  -- 111
  .shiftR,  -- 112
  .const (-10) 0,  -- 113
  .add (-10) (-10) (-9),  -- 114
  .const (-9) 0,  -- 115
  .add (-9) (-9) (-8),  -- 116
  .const (-8) 0,  -- 117
  .add (-8) (-8) (-7),  -- 118
  .const (-7) 0,  -- 119
  .add (-7) (-7) (-6),  -- 120
  .const (-6) 0,  -- 121
  .add (-6) (-6) (-5),  -- 122
  .const (-5) 0,  -- 123
  .add (-5) (-5) (-4),  -- 124
  .const (-4) 0,  -- 125
  .add (-4) (-4) (-3),  -- 126
  .const (-3) 0,  -- 127
  .add (-3) (-3) (-2),  -- 128
  .const (-2) 0,  -- 129
  .add (-2) (-2) (-1),  -- 130
  .const (-1) 0,  -- 131
  .add (-1) (-1) (0),  -- 132
  .const (0) 0,  -- 133
  .add (0) (0) (-11),  -- 134
  .const (-11) 1,  -- 135
  .sub (-1) (-1) (-11),  -- 136
  .const (-11) 0,  -- 137
  .jle (-11) 111,  -- 138
  .const (-11) 1,  -- 139
  .sub (-2) (-2) (-11),  -- 140
  .const (-11) 0,  -- 141
  .jle (-11) 50,  -- 142
  .jle (-9) 145,  -- 143
  .reject,  -- 144
  .jle (-6) 150,  -- 145
  .jle (-8) 150,  -- 146
  .sub (-10) (-5) (-7),  -- 147
  .jle (-10) 150,  -- 148
  .reject,  -- 149
  .accept  -- 150
]
/-- address of `OUTER` -/
def pc_OUTER : ℕ := 50
/-- address of `WR` -/
def pc_WR : ℕ := 55
/-- address of `WREXIT` -/
def pc_WREXIT : ℕ := 83
/-- address of `SETL` -/
def pc_SETL : ℕ := 88
/-- address of `NONPOS` -/
def pc_NONPOS : ℕ := 93
/-- address of `SETR` -/
def pc_SETR : ℕ := 100
/-- address of `ZERO` -/
def pc_ZERO : ℕ := 105
/-- address of `DONE` -/
def pc_DONE : ℕ := 107
/-- address of `WL` -/
def pc_WL : ℕ := 111
/-- address of `WLEXIT` -/
def pc_WLEXIT : ℕ := 139
/-- address of `FINAL` -/
def pc_FINAL : ℕ := 143
/-- address of `F1` -/
def pc_F1 : ℕ := 145
/-- address of `ACC` -/
def pc_ACC : ℕ := 150

end SmaleNinth.BSS

/-!
The shift-and-carry chains and the two walk loops of `prog`.
-/

open SmaleNinth

namespace SmaleNinth.BSS

/-! ### Sanity: program lookups are by `rfl` -/

example : prog[4]? = some .shiftL := rfl
example : prog[150]? = some .accept := rfl
example : prog[55]? = some (.jle (-1) 83) := rfl

/-! ### Effect of the right chain (`shiftL` + 11 movs) on an arbitrary tape -/

/-- Result of the right chain on the tape `τ`. -/
def effR (τ : ℤ → ℝ) : ℤ → ℝ := fun k =>
  if 0 ≤ k then τ (k + 1) else if -10 ≤ k then τ k
  else if k = -11 then τ (-10) else if k = -12 then τ 0 else τ (k + 1)

/-- Result of the left chain (`shiftR` + 11 movs) on the tape `τ`. -/
def effL (τ : ℤ → ℝ) : ℤ → ℝ := fun k =>
  if 1 ≤ k then τ (k - 1) else if k = 0 then τ (-12) else if -10 ≤ k then τ k
  else if k = -11 then τ (-12) else τ (k - 1)

lemma effR_phys (h : ℤ) (d r : ℤ → ℝ) :
    effR (phys h d r) = phys (h + 1) d (Function.update r (-11) (r (-10))) := by
  funext k
  unfold effR
  by_cases h0 : 0 ≤ k
  · rw [if_pos h0, phys_of_nonneg h0, phys_of_nonneg (by omega)]; congr 1; ring
  · rw [if_neg h0]
    by_cases h1 : -10 ≤ k
    · rw [if_pos h1, phys_reg (by omega) (by omega), phys_reg (by omega) (by omega),
        Function.update_of_ne (by omega)]
    · rw [if_neg h1]
      by_cases h2 : k = -11
      · subst h2
        rw [if_pos rfl, phys_reg (by norm_num) (by norm_num), phys_reg (by norm_num) (by norm_num),
          Function.update_self]
      · rw [if_neg h2]
        by_cases h3 : k = -12
        · subst h3
          rw [if_pos rfl, phys_zero, phys_of_lt (by norm_num)]; congr 1; ring
        · rw [if_neg h3, phys_of_lt (by omega), phys_of_lt (by omega)]; congr 1; ring

lemma effL_phys (h : ℤ) (d r : ℤ → ℝ) :
    effL (phys h d r) = phys (h - 1) d (Function.update r (-11) (d (h - 1))) := by
  funext k
  unfold effL
  by_cases h0 : 1 ≤ k
  · rw [if_pos h0, phys_of_nonneg (by omega), phys_of_nonneg (by omega)]; congr 1; ring
  · rw [if_neg h0]
    by_cases h1 : k = 0
    · subst h1
      rw [if_pos rfl, phys_of_lt (by norm_num), phys_zero]; congr 1; ring
    · rw [if_neg h1]
      by_cases h2 : -10 ≤ k
      · rw [if_pos h2, phys_reg (by omega) (by omega), phys_reg (by omega) (by omega),
          Function.update_of_ne (by omega)]
      · rw [if_neg h2]
        by_cases h3 : k = -11
        · subst h3
          rw [if_pos rfl, phys_of_lt (by norm_num), phys_reg (by norm_num) (by norm_num),
            Function.update_self]; congr 1; ring
        · rw [if_neg h3, phys_of_lt (by omega), phys_of_lt (by omega)]; congr 1; ring

/-- The right chain as a list of instructions. -/
noncomputable def chainR : List BSSInstr := [.shiftL, .const (-12) 0, .add (-12) (-12) (-1), .const (-1) 0, .add (-1) (-1) (-2), .const (-2) 0, .add (-2) (-2) (-3), .const (-3) 0, .add (-3) (-3) (-4), .const (-4) 0, .add (-4) (-4) (-5), .const (-5) 0, .add (-5) (-5) (-6), .const (-6) 0, .add (-6) (-6) (-7), .const (-7) 0, .add (-7) (-7) (-8), .const (-8) 0, .add (-8) (-8) (-9), .const (-9) 0, .add (-9) (-9) (-10), .const (-10) 0, .add (-10) (-10) (-11)]

/-- The left chain as a list of instructions. -/
noncomputable def chainL : List BSSInstr := [.shiftR, .const (-10) 0, .add (-10) (-10) (-9), .const (-9) 0, .add (-9) (-9) (-8), .const (-8) 0, .add (-8) (-8) (-7), .const (-7) 0, .add (-7) (-7) (-6), .const (-6) 0, .add (-6) (-6) (-5), .const (-5) 0, .add (-5) (-5) (-4), .const (-4) 0, .add (-4) (-4) (-3), .const (-3) 0, .add (-3) (-3) (-2), .const (-2) 0, .add (-2) (-2) (-1), .const (-1) 0, .add (-1) (-1) (0), .const (0) 0, .add (0) (0) (-11)]

lemma reaches_chainR (pc : ℕ) (hP : ∀ k, k < 23 → prog[pc + k]? = chainR[k]?) (τ : ℤ → ℝ) :
    Reaches prog ⟨pc, τ⟩ ⟨pc + 23, effR τ⟩ 23 := by
  have s0 : Reaches prog ⟨pc, τ⟩ ⟨pc + 1, fun k => τ (k + 1)⟩ 1 :=
    Reaches.single (step_shiftL (by simpa [chainR] using hP 0 (by norm_num)) τ)
  set σ : ℤ → ℝ := fun k => τ (k + 1) with hσ
  have m0 : Reaches prog ⟨pc + 1, σ⟩ ⟨pc + 3, Function.update σ (-12) (σ (-1))⟩ 2 :=
    reaches_mov (by simpa [chainR] using hP 1 (by norm_num)) (by simpa [chainR, add_assoc] using hP 2 (by norm_num)) (by norm_num) σ
  set u0 := Function.update σ (-12) (σ (-1)) with hu0
  have m1 : Reaches prog ⟨pc + 3, u0⟩ ⟨pc + 5, Function.update u0 (-1) (u0 (-2))⟩ 2 :=
    reaches_mov (by simpa [chainR] using hP 3 (by norm_num)) (by simpa [chainR, add_assoc] using hP 4 (by norm_num)) (by norm_num) u0
  set u1 := Function.update u0 (-1) (u0 (-2)) with hu1
  have m2 : Reaches prog ⟨pc + 5, u1⟩ ⟨pc + 7, Function.update u1 (-2) (u1 (-3))⟩ 2 :=
    reaches_mov (by simpa [chainR] using hP 5 (by norm_num)) (by simpa [chainR, add_assoc] using hP 6 (by norm_num)) (by norm_num) u1
  set u2 := Function.update u1 (-2) (u1 (-3)) with hu2
  have m3 : Reaches prog ⟨pc + 7, u2⟩ ⟨pc + 9, Function.update u2 (-3) (u2 (-4))⟩ 2 :=
    reaches_mov (by simpa [chainR] using hP 7 (by norm_num)) (by simpa [chainR, add_assoc] using hP 8 (by norm_num)) (by norm_num) u2
  set u3 := Function.update u2 (-3) (u2 (-4)) with hu3
  have m4 : Reaches prog ⟨pc + 9, u3⟩ ⟨pc + 11, Function.update u3 (-4) (u3 (-5))⟩ 2 :=
    reaches_mov (by simpa [chainR] using hP 9 (by norm_num)) (by simpa [chainR, add_assoc] using hP 10 (by norm_num)) (by norm_num) u3
  set u4 := Function.update u3 (-4) (u3 (-5)) with hu4
  have m5 : Reaches prog ⟨pc + 11, u4⟩ ⟨pc + 13, Function.update u4 (-5) (u4 (-6))⟩ 2 :=
    reaches_mov (by simpa [chainR] using hP 11 (by norm_num)) (by simpa [chainR, add_assoc] using hP 12 (by norm_num)) (by norm_num) u4
  set u5 := Function.update u4 (-5) (u4 (-6)) with hu5
  have m6 : Reaches prog ⟨pc + 13, u5⟩ ⟨pc + 15, Function.update u5 (-6) (u5 (-7))⟩ 2 :=
    reaches_mov (by simpa [chainR] using hP 13 (by norm_num)) (by simpa [chainR, add_assoc] using hP 14 (by norm_num)) (by norm_num) u5
  set u6 := Function.update u5 (-6) (u5 (-7)) with hu6
  have m7 : Reaches prog ⟨pc + 15, u6⟩ ⟨pc + 17, Function.update u6 (-7) (u6 (-8))⟩ 2 :=
    reaches_mov (by simpa [chainR] using hP 15 (by norm_num)) (by simpa [chainR, add_assoc] using hP 16 (by norm_num)) (by norm_num) u6
  set u7 := Function.update u6 (-7) (u6 (-8)) with hu7
  have m8 : Reaches prog ⟨pc + 17, u7⟩ ⟨pc + 19, Function.update u7 (-8) (u7 (-9))⟩ 2 :=
    reaches_mov (by simpa [chainR] using hP 17 (by norm_num)) (by simpa [chainR, add_assoc] using hP 18 (by norm_num)) (by norm_num) u7
  set u8 := Function.update u7 (-8) (u7 (-9)) with hu8
  have m9 : Reaches prog ⟨pc + 19, u8⟩ ⟨pc + 21, Function.update u8 (-9) (u8 (-10))⟩ 2 :=
    reaches_mov (by simpa [chainR] using hP 19 (by norm_num)) (by simpa [chainR, add_assoc] using hP 20 (by norm_num)) (by norm_num) u8
  set u9 := Function.update u8 (-9) (u8 (-10)) with hu9
  have m10 : Reaches prog ⟨pc + 21, u9⟩ ⟨pc + 23, Function.update u9 (-10) (u9 (-11))⟩ 2 :=
    reaches_mov (by simpa [chainR] using hP 21 (by norm_num)) (by simpa [chainR, add_assoc] using hP 22 (by norm_num)) (by norm_num) u9
  set u10 := Function.update u9 (-10) (u9 (-11)) with hu10
  have hall := (s0.trans (m0.trans (m1.trans (m2.trans (m3.trans (m4.trans (m5.trans (m6.trans (m7.trans (m8.trans (m9.trans m10)))))))))))
  refine (hall.mono (by norm_num)).cast ?_
  congr 1
  funext k
  simp only [hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1, hu0, hσ, Function.update_apply]
  unfold effR
  rcases (show 0 ≤ k ∨ k = -1 ∨ k = -2 ∨ k = -3 ∨ k = -4 ∨ k = -5 ∨ k = -6 ∨ k = -7 ∨
      k = -8 ∨ k = -9 ∨ k = -10 ∨ k = -11 ∨ k = -12 ∨ k ≤ -13 by omega) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · simp [show k ≠ -1 by omega, show k ≠ -2 by omega, show k ≠ -3 by omega,
      show k ≠ -4 by omega, show k ≠ -5 by omega, show k ≠ -6 by omega, show k ≠ -7 by omega,
      show k ≠ -8 by omega, show k ≠ -9 by omega, show k ≠ -10 by omega,
      show k ≠ -12 by omega, h]
  all_goals try (subst h; norm_num)
  · simp [show k ≠ -1 by omega, show k ≠ -2 by omega, show k ≠ -3 by omega,
      show k ≠ -4 by omega, show k ≠ -5 by omega, show k ≠ -6 by omega, show k ≠ -7 by omega,
      show k ≠ -8 by omega, show k ≠ -9 by omega, show k ≠ -10 by omega, show k ≠ -11 by omega,
      show k ≠ -12 by omega, show ¬ (0 ≤ k) by omega, show ¬ (-10 ≤ k) by omega]

lemma reaches_chainL (pc : ℕ) (hP : ∀ k, k < 23 → prog[pc + k]? = chainL[k]?) (τ : ℤ → ℝ) :
    Reaches prog ⟨pc, τ⟩ ⟨pc + 23, effL τ⟩ 23 := by
  have s0 : Reaches prog ⟨pc, τ⟩ ⟨pc + 1, fun k => τ (k - 1)⟩ 1 :=
    Reaches.single (step_shiftR (by simpa [chainL] using hP 0 (by norm_num)) τ)
  set σ : ℤ → ℝ := fun k => τ (k - 1) with hσ
  have m0 : Reaches prog ⟨pc + 1, σ⟩ ⟨pc + 3, Function.update σ (-10) (σ (-9))⟩ 2 :=
    reaches_mov (by simpa [chainL] using hP 1 (by norm_num)) (by simpa [chainL, add_assoc] using hP 2 (by norm_num)) (by norm_num) σ
  set u0 := Function.update σ (-10) (σ (-9)) with hu0
  have m1 : Reaches prog ⟨pc + 3, u0⟩ ⟨pc + 5, Function.update u0 (-9) (u0 (-8))⟩ 2 :=
    reaches_mov (by simpa [chainL] using hP 3 (by norm_num)) (by simpa [chainL, add_assoc] using hP 4 (by norm_num)) (by norm_num) u0
  set u1 := Function.update u0 (-9) (u0 (-8)) with hu1
  have m2 : Reaches prog ⟨pc + 5, u1⟩ ⟨pc + 7, Function.update u1 (-8) (u1 (-7))⟩ 2 :=
    reaches_mov (by simpa [chainL] using hP 5 (by norm_num)) (by simpa [chainL, add_assoc] using hP 6 (by norm_num)) (by norm_num) u1
  set u2 := Function.update u1 (-8) (u1 (-7)) with hu2
  have m3 : Reaches prog ⟨pc + 7, u2⟩ ⟨pc + 9, Function.update u2 (-7) (u2 (-6))⟩ 2 :=
    reaches_mov (by simpa [chainL] using hP 7 (by norm_num)) (by simpa [chainL, add_assoc] using hP 8 (by norm_num)) (by norm_num) u2
  set u3 := Function.update u2 (-7) (u2 (-6)) with hu3
  have m4 : Reaches prog ⟨pc + 9, u3⟩ ⟨pc + 11, Function.update u3 (-6) (u3 (-5))⟩ 2 :=
    reaches_mov (by simpa [chainL] using hP 9 (by norm_num)) (by simpa [chainL, add_assoc] using hP 10 (by norm_num)) (by norm_num) u3
  set u4 := Function.update u3 (-6) (u3 (-5)) with hu4
  have m5 : Reaches prog ⟨pc + 11, u4⟩ ⟨pc + 13, Function.update u4 (-5) (u4 (-4))⟩ 2 :=
    reaches_mov (by simpa [chainL] using hP 11 (by norm_num)) (by simpa [chainL, add_assoc] using hP 12 (by norm_num)) (by norm_num) u4
  set u5 := Function.update u4 (-5) (u4 (-4)) with hu5
  have m6 : Reaches prog ⟨pc + 13, u5⟩ ⟨pc + 15, Function.update u5 (-4) (u5 (-3))⟩ 2 :=
    reaches_mov (by simpa [chainL] using hP 13 (by norm_num)) (by simpa [chainL, add_assoc] using hP 14 (by norm_num)) (by norm_num) u5
  set u6 := Function.update u5 (-4) (u5 (-3)) with hu6
  have m7 : Reaches prog ⟨pc + 15, u6⟩ ⟨pc + 17, Function.update u6 (-3) (u6 (-2))⟩ 2 :=
    reaches_mov (by simpa [chainL] using hP 15 (by norm_num)) (by simpa [chainL, add_assoc] using hP 16 (by norm_num)) (by norm_num) u6
  set u7 := Function.update u6 (-3) (u6 (-2)) with hu7
  have m8 : Reaches prog ⟨pc + 17, u7⟩ ⟨pc + 19, Function.update u7 (-2) (u7 (-1))⟩ 2 :=
    reaches_mov (by simpa [chainL] using hP 17 (by norm_num)) (by simpa [chainL, add_assoc] using hP 18 (by norm_num)) (by norm_num) u7
  set u8 := Function.update u7 (-2) (u7 (-1)) with hu8
  have m9 : Reaches prog ⟨pc + 19, u8⟩ ⟨pc + 21, Function.update u8 (-1) (u8 (0))⟩ 2 :=
    reaches_mov (by simpa [chainL] using hP 19 (by norm_num)) (by simpa [chainL, add_assoc] using hP 20 (by norm_num)) (by norm_num) u8
  set u9 := Function.update u8 (-1) (u8 (0)) with hu9
  have m10 : Reaches prog ⟨pc + 21, u9⟩ ⟨pc + 23, Function.update u9 (0) (u9 (-11))⟩ 2 :=
    reaches_mov (by simpa [chainL] using hP 21 (by norm_num)) (by simpa [chainL, add_assoc] using hP 22 (by norm_num)) (by norm_num) u9
  set u10 := Function.update u9 (0) (u9 (-11)) with hu10
  have hall := (s0.trans (m0.trans (m1.trans (m2.trans (m3.trans (m4.trans (m5.trans (m6.trans (m7.trans (m8.trans (m9.trans m10)))))))))))
  refine (hall.mono (by norm_num)).cast ?_
  congr 1
  funext k
  simp only [hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2, hu1, hu0, hσ, Function.update_apply]
  unfold effL
  rcases (show 1 ≤ k ∨ k = 0 ∨ k = -1 ∨ k = -2 ∨ k = -3 ∨ k = -4 ∨ k = -5 ∨ k = -6 ∨ k = -7 ∨
      k = -8 ∨ k = -9 ∨ k = -10 ∨ k = -11 ∨ k ≤ -12 by omega) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · simp [show k ≠ 0 by omega, show k ≠ -1 by omega, show k ≠ -2 by omega, show k ≠ -3 by omega,
      show k ≠ -4 by omega, show k ≠ -5 by omega, show k ≠ -6 by omega, show k ≠ -7 by omega,
      show k ≠ -8 by omega, show k ≠ -9 by omega, show k ≠ -10 by omega, h]
  all_goals try (subst h; norm_num)
  · simp [show k ≠ 0 by omega, show k ≠ -1 by omega, show k ≠ -2 by omega, show k ≠ -3 by omega,
      show k ≠ -4 by omega, show k ≠ -5 by omega, show k ≠ -6 by omega, show k ≠ -7 by omega,
      show k ≠ -8 by omega, show k ≠ -9 by omega, show k ≠ -10 by omega, show k ≠ -11 by omega,
      show ¬ (1 ≤ k) by omega, show ¬ (-10 ≤ k) by omega]

/-! ### The walk loops -/

lemma chainR_at (pc : ℕ) (hpc : pc = 4 ∨ pc = 27 ∨ pc = 56) :
    ∀ k, k < 23 → prog[pc + k]? = chainR[k]? := by
  intro k hk
  rcases hpc with rfl | rfl | rfl <;> interval_cases k <;> rfl

lemma chainL_at : ∀ k, k < 23 → prog[112 + k]? = chainL[k]? := by
  intro k hk
  interval_cases k <;> rfl

/-- The walk-right loop at `55`: with counter `c`, the head advances by `c`
cells and the registers `-2 … -10` are preserved. -/
lemma walk_right (d : ℤ → ℝ) : ∀ (c : ℕ) (h : ℤ) (r : ℤ → ℝ), r (-1) = (c : ℝ) →
    ∃ r', (∀ j, -10 ≤ j → j ≤ -2 → r' j = r j) ∧ r' (-1) = 0 ∧
      Reaches prog ⟨55, phys h d r⟩ ⟨83, phys (h + c) d r'⟩ (28 * c + 1)
  | 0, h, r, hr => ⟨r, fun _ _ _ => rfl, by simpa using hr, by
      have := reaches_jle_reg_le (P := prog) (pc := 55) (j := -1) (target := 83) rfl
        (by norm_num) (by norm_num) h d r (by rw [hr]; simp)
      simpa using this⟩
  | c + 1, h, r, hr => by
      have s1 := reaches_jle_reg_pos (P := prog) (pc := 55) (j := -1) (target := 83) rfl
        (by norm_num) (by norm_num) h d r (by rw [hr]; positivity)
      have s2 := reaches_chainR 56 (chainR_at 56 (by norm_num)) (phys h d r)
      rw [effR_phys] at s2
      set r₁ := Function.update r (-11) (r (-10)) with hr₁
      have s3 := reaches_const_reg (P := prog) (pc := 79) (j := -11) (c := 1) rfl
        (by norm_num) (by norm_num) (h + 1) d r₁
      set r₂ := Function.update r₁ (-11) (1 : ℝ) with hr₂
      have s4 := reaches_sub_reg (P := prog) (pc := 80) (j := -1) (a := -1) (b := -11) rfl
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (h + 1) d r₂
      set r₃ := Function.update r₂ (-1) (r₂ (-1) - r₂ (-11)) with hr₃
      have s5 := reaches_const_reg (P := prog) (pc := 81) (j := -11) (c := 0) rfl
        (by norm_num) (by norm_num) (h + 1) d r₃
      set r₄ := Function.update r₃ (-11) (0 : ℝ) with hr₄
      have s6 := reaches_jle_reg_le (P := prog) (pc := 82) (j := -11) (target := 55) rfl
        (by norm_num) (by norm_num) (h + 1) d r₄ (by simp [hr₄])
      have hr₄1 : r₄ (-1) = (c : ℝ) := by
        simp [hr₄, hr₃, hr₂, hr₁, Function.update_apply, hr]
      obtain ⟨r', hpres, hr'1, s7⟩ := walk_right d c (h + 1) r₄ hr₄1
      refine ⟨r', ?_, hr'1, ?_⟩
      · intro j hj1 hj2
        rw [hpres j hj1 hj2]
        simp [hr₄, hr₃, hr₂, hr₁, Function.update_apply, show j ≠ -11 by omega,
          show j ≠ -1 by omega]
      · have hall := s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7)))))
        refine (hall.mono (by omega)).cast ?_
        congr 2
        push_cast; ring

/-- The walk-left loop at `111`: with counter `c`, the head retreats by `c`
cells and the registers `-2 … -10` are preserved. -/
lemma walk_left (d : ℤ → ℝ) : ∀ (c : ℕ) (h : ℤ) (r : ℤ → ℝ), r (-1) = (c : ℝ) →
    ∃ r', (∀ j, -10 ≤ j → j ≤ -2 → r' j = r j) ∧ r' (-1) = 0 ∧
      Reaches prog ⟨111, phys h d r⟩ ⟨139, phys (h - c) d r'⟩ (28 * c + 1)
  | 0, h, r, hr => ⟨r, fun _ _ _ => rfl, by simpa using hr, by
      have := reaches_jle_reg_le (P := prog) (pc := 111) (j := -1) (target := 139) rfl
        (by norm_num) (by norm_num) h d r (by rw [hr]; simp)
      simpa using this⟩
  | c + 1, h, r, hr => by
      have s1 := reaches_jle_reg_pos (P := prog) (pc := 111) (j := -1) (target := 139) rfl
        (by norm_num) (by norm_num) h d r (by rw [hr]; positivity)
      have s2 := reaches_chainL 112 chainL_at (phys h d r)
      rw [effL_phys] at s2
      set r₁ := Function.update r (-11) (d (h - 1)) with hr₁
      have s3 := reaches_const_reg (P := prog) (pc := 135) (j := -11) (c := 1) rfl
        (by norm_num) (by norm_num) (h - 1) d r₁
      set r₂ := Function.update r₁ (-11) (1 : ℝ) with hr₂
      have s4 := reaches_sub_reg (P := prog) (pc := 136) (j := -1) (a := -1) (b := -11) rfl
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (h - 1) d r₂
      set r₃ := Function.update r₂ (-1) (r₂ (-1) - r₂ (-11)) with hr₃
      have s5 := reaches_const_reg (P := prog) (pc := 137) (j := -11) (c := 0) rfl
        (by norm_num) (by norm_num) (h - 1) d r₃
      set r₄ := Function.update r₃ (-11) (0 : ℝ) with hr₄
      have s6 := reaches_jle_reg_le (P := prog) (pc := 138) (j := -11) (target := 111) rfl
        (by norm_num) (by norm_num) (h - 1) d r₄ (by simp [hr₄])
      have hr₄1 : r₄ (-1) = (c : ℝ) := by
        simp [hr₄, hr₃, hr₂, hr₁, Function.update_apply, hr]
      obtain ⟨r', hpres, hr'1, s7⟩ := walk_left d c (h - 1) r₄ hr₄1
      refine ⟨r', ?_, hr'1, ?_⟩
      · intro j hj1 hj2
        rw [hpres j hj1 hj2]
        simp [hr₄, hr₃, hr₂, hr₁, Function.update_apply, show j ≠ -11 by omega,
          show j ≠ -1 by omega]
      · have hall := s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7)))))
        refine (hall.mono (by omega)).cast ?_
        congr 2
        push_cast; ring

/-! ### The initialisation block `0 → 50` -/

lemma init_block (d : ℤ → ℝ) :
    ∃ r', r' (-3) = d 0 ∧ r' (-2) = d 0 ∧ (∀ j, -9 ≤ j → j ≤ -5 → r' j = 0) ∧
      Reaches prog ⟨0, phys 0 d (fun _ => 0)⟩ ⟨50, phys 2 d r'⟩ 50 := by
  have s1 := reaches_mov_head (P := prog) (pc := 0) (j := -3) rfl rfl (by norm_num) (by norm_num)
    0 d (fun _ => 0)
  set r₁ := Function.update (fun _ : ℤ => (0 : ℝ)) (-3) (d 0) with hr₁
  have s2 := reaches_mov_head (P := prog) (pc := 2) (j := -2) rfl rfl (by norm_num) (by norm_num)
    0 d r₁
  set r₂ := Function.update r₁ (-2) (d 0) with hr₂
  have s3 := reaches_chainR 4 (chainR_at 4 (by norm_num)) (phys 0 d r₂)
  rw [effR_phys] at s3
  set r₃ := Function.update r₂ (-11) (r₂ (-10)) with hr₃
  have s4 := reaches_chainR 27 (chainR_at 27 (by norm_num)) (phys (0 + 1) d r₃)
  rw [effR_phys] at s4
  set r₄ := Function.update r₃ (-11) (r₃ (-10)) with hr₄
  refine ⟨r₄, ?_, ?_, ?_, ?_⟩
  · simp [hr₄, hr₃, hr₂, hr₁, Function.update_apply]
  · simp [hr₄, hr₃, hr₂, hr₁, Function.update_apply]
  · intro j hj1 hj2
    simp [hr₄, hr₃, hr₂, hr₁, Function.update_apply, show j ≠ -11 by omega,
      show j ≠ -2 by omega, show j ≠ -3 by omega]
  · have hall := s1.trans (s2.trans (s3.trans s4))
    refine (hall.mono (by norm_num)).cast ?_
    congr 2

end SmaleNinth.BSS

/-!
The update block `83 → 107` of `prog`: it maintains the running interval
`[L, R]` (with presence flags `HL`, `HR`) and the infeasibility flag `BAD`.
-/

open SmaleNinth

namespace SmaleNinth.BSS

/-- The abstract state carried in registers `-5 … -9`. -/
@[ext] structure St where
  L : ℝ
  HL : ℝ
  R : ℝ
  HR : ℝ
  BAD : ℝ

/-- The abstract state read off a register zone. -/
def regs (r : ℤ → ℝ) : St := ⟨r (-5), r (-6), r (-7), r (-8), r (-9)⟩

/-- The abstract update performed by the block on constraint `a·x ≥ b`. -/
noncomputable def upd (s : St) (a b : ℝ) : St :=
  if 0 < a then
    (if s.HL ≤ 0 then ⟨b / a, 1, s.R, s.HR, s.BAD⟩
     else if b / a - s.L ≤ 0 then s else ⟨b / a, 1, s.R, s.HR, s.BAD⟩)
  else if 0 < -a then
    (if s.HR ≤ 0 then ⟨s.L, s.HL, b / a, 1, s.BAD⟩
     else if s.R - b / a ≤ 0 then s else ⟨s.L, s.HL, b / a, 1, s.BAD⟩)
  else if b ≤ 0 then s else ⟨s.L, s.HL, s.R, s.HR, 1⟩

lemma setl_tail (h : ℤ) (d r : ℤ → ℝ) :
    Reaches prog ⟨88, phys h d r⟩
      ⟨107, phys h d (Function.update (Function.update (Function.update r (-5) (r (-10)))
        (-6) 1) (-11) 0)⟩ 5 := by
  have s1 := reaches_mov_reg (P := prog) (pc := 88) (j := -5) (s := -10) rfl rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h d r
  set r₁ := Function.update r (-5) (r (-10)) with hr₁
  have s2 := reaches_const_reg (P := prog) (pc := 90) (j := -6) (c := 1) rfl
    (by norm_num) (by norm_num) h d r₁
  set r₂ := Function.update r₁ (-6) (1 : ℝ) with hr₂
  have s3 := reaches_const_reg (P := prog) (pc := 91) (j := -11) (c := 0) rfl
    (by norm_num) (by norm_num) h d r₂
  set r₃ := Function.update r₂ (-11) (0 : ℝ) with hr₃
  have s4 := reaches_jle_reg_le (P := prog) (pc := 92) (j := -11) (target := 107) rfl
    (by norm_num) (by norm_num) h d r₃ (by simp [hr₃])
  exact (s1.trans (s2.trans (s3.trans s4))).mono (by norm_num)

lemma setr_tail (h : ℤ) (d r : ℤ → ℝ) :
    Reaches prog ⟨100, phys h d r⟩
      ⟨107, phys h d (Function.update (Function.update (Function.update r (-7) (r (-10)))
        (-8) 1) (-11) 0)⟩ 5 := by
  have s1 := reaches_mov_reg (P := prog) (pc := 100) (j := -7) (s := -10) rfl rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h d r
  set r₁ := Function.update r (-7) (r (-10)) with hr₁
  have s2 := reaches_const_reg (P := prog) (pc := 102) (j := -8) (c := 1) rfl
    (by norm_num) (by norm_num) h d r₁
  set r₂ := Function.update r₁ (-8) (1 : ℝ) with hr₂
  have s3 := reaches_const_reg (P := prog) (pc := 103) (j := -11) (c := 0) rfl
    (by norm_num) (by norm_num) h d r₂
  set r₃ := Function.update r₂ (-11) (0 : ℝ) with hr₃
  have s4 := reaches_jle_reg_le (P := prog) (pc := 104) (j := -11) (target := 107) rfl
    (by norm_num) (by norm_num) h d r₃ (by simp [hr₃])
  exact (s1.trans (s2.trans (s3.trans s4))).mono (by norm_num)

/-- The update block: registers `-1 … -4` are preserved and the abstract state
is updated by `upd` with `a = r (-4)` (the coefficient) and `b = d h` (the head cell). -/
lemma update_block (h : ℤ) (d r : ℤ → ℝ) :
    ∃ r', (∀ j, -4 ≤ j → j ≤ -1 → r' j = r j) ∧
      regs r' = upd (regs r) (r (-4)) (d h) ∧
      Reaches prog ⟨83, phys h d r⟩ ⟨107, phys h d r'⟩ 13 := by
  by_cases ha : 0 < r (-4)
  · -- a > 0
    have s1 := reaches_jle_reg_pos (P := prog) (pc := 83) (j := -4) (target := 93) rfl
      (by norm_num) (by norm_num) h d r ha
    have s2 := reaches_div_head_reg (P := prog) (pc := 84) (j := -10) (b := -4) rfl
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) h d r
    set r₁ := Function.update r (-10) (d h / r (-4)) with hr₁
    by_cases hHL : r (-6) ≤ 0
    · have s3 := reaches_jle_reg_le (P := prog) (pc := 85) (j := -6) (target := 88) rfl
        (by norm_num) (by norm_num) h d r₁ (by simp [hr₁]; exact hHL)
      have s4 := setl_tail h d r₁
      refine ⟨_, ?_, ?_, (s1.trans (s2.trans (s3.trans s4))).mono (by norm_num)⟩
      · intro j hj1 hj2
        simp [hr₁, Function.update_apply, show j ≠ -5 by omega, show j ≠ -6 by omega,
          show j ≠ -10 by omega, show j ≠ -11 by omega]
      · simp [regs, upd, hr₁, ha, hHL, Function.update_apply]
    · have hHL' : 0 < r (-6) := lt_of_not_ge hHL
      have s3 := reaches_jle_reg_pos (P := prog) (pc := 85) (j := -6) (target := 88) rfl
        (by norm_num) (by norm_num) h d r₁ (by simp [hr₁]; exact hHL')
      have s4 := reaches_sub_reg (P := prog) (pc := 86) (j := -11) (a := -10) (b := -5) rfl
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        h d r₁
      set r₂ := Function.update r₁ (-11) (r₁ (-10) - r₁ (-5)) with hr₂
      have hr₂v : r₂ (-11) = d h / r (-4) - r (-5) := by simp [hr₂, hr₁]
      by_cases hle : d h / r (-4) - r (-5) ≤ 0
      · have s5 := reaches_jle_reg_le (P := prog) (pc := 87) (j := -11) (target := 107) rfl
          (by norm_num) (by norm_num) h d r₂ (by rw [hr₂v]; exact hle)
        refine ⟨r₂, ?_, ?_, (s1.trans (s2.trans (s3.trans (s4.trans s5)))).mono (by norm_num)⟩
        · intro j hj1 hj2
          simp [hr₂, hr₁, Function.update_apply, show j ≠ -10 by omega, show j ≠ -11 by omega]
        · simp [regs, upd, hr₂, hr₁, ha, hHL, hle, Function.update_apply]
      · have s5 := reaches_jle_reg_pos (P := prog) (pc := 87) (j := -11) (target := 107) rfl
          (by norm_num) (by norm_num) h d r₂ (by rw [hr₂v]; exact lt_of_not_ge hle)
        have s6 := setl_tail h d r₂
        refine ⟨_, ?_, ?_,
          (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans s6))))).mono (by norm_num)⟩
        · intro j hj1 hj2
          simp [hr₂, hr₁, Function.update_apply, show j ≠ -5 by omega, show j ≠ -6 by omega,
            show j ≠ -10 by omega, show j ≠ -11 by omega]
        · simp [regs, upd, hr₂, hr₁, ha, hHL, hle, Function.update_apply]
  · -- a ≤ 0
    have s1 := reaches_jle_reg_le (P := prog) (pc := 83) (j := -4) (target := 93) rfl
      (by norm_num) (by norm_num) h d r (not_lt.mp ha)
    have s2 := reaches_const_reg (P := prog) (pc := 93) (j := -10) (c := 0) rfl
      (by norm_num) (by norm_num) h d r
    set r₁ := Function.update r (-10) (0 : ℝ) with hr₁
    have s3 := reaches_sub_reg (P := prog) (pc := 94) (j := -10) (a := -10) (b := -4) rfl
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      h d r₁
    set r₂ := Function.update r₁ (-10) (r₁ (-10) - r₁ (-4)) with hr₂
    have hr₂v : r₂ (-10) = -r (-4) := by simp [hr₂, hr₁]
    by_cases hneg : 0 < -r (-4)
    · have s4 := reaches_jle_reg_pos (P := prog) (pc := 95) (j := -10) (target := 105) rfl
        (by norm_num) (by norm_num) h d r₂ (by rw [hr₂v]; exact hneg)
      have s5 := reaches_div_head_reg (P := prog) (pc := 96) (j := -10) (b := -4) rfl
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) h d r₂
      set r₃ := Function.update r₂ (-10) (d h / r₂ (-4)) with hr₃
      have hr₃v : r₃ (-10) = d h / r (-4) := by simp [hr₃, hr₂, hr₁]
      by_cases hHR : r (-8) ≤ 0
      · have s6 := reaches_jle_reg_le (P := prog) (pc := 97) (j := -8) (target := 100) rfl
          (by norm_num) (by norm_num) h d r₃ (by simp [hr₃, hr₂, hr₁]; exact hHR)
        have s7 := setr_tail h d r₃
        refine ⟨_, ?_, ?_,
          (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7)))))).mono
            (by norm_num)⟩
        · intro j hj1 hj2
          simp [hr₃, hr₂, hr₁, Function.update_apply, show j ≠ -7 by omega, show j ≠ -8 by omega,
            show j ≠ -10 by omega, show j ≠ -11 by omega]
        · simp [regs, upd, hr₃, hr₂, hr₁, ha, hneg, hHR, Function.update_apply]
      · have hHR' : 0 < r (-8) := lt_of_not_ge hHR
        have s6 := reaches_jle_reg_pos (P := prog) (pc := 97) (j := -8) (target := 100) rfl
          (by norm_num) (by norm_num) h d r₃ (by simp [hr₃, hr₂, hr₁]; exact hHR')
        have s7 := reaches_sub_reg (P := prog) (pc := 98) (j := -11) (a := -7) (b := -10) rfl
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          h d r₃
        set r₄ := Function.update r₃ (-11) (r₃ (-7) - r₃ (-10)) with hr₄
        have hr₄v : r₄ (-11) = r (-7) - d h / r (-4) := by simp [hr₄, hr₃, hr₂, hr₁]
        by_cases hle : r (-7) - d h / r (-4) ≤ 0
        · have s8 := reaches_jle_reg_le (P := prog) (pc := 99) (j := -11) (target := 107) rfl
            (by norm_num) (by norm_num) h d r₄ (by rw [hr₄v]; exact hle)
          refine ⟨r₄, ?_, ?_,
            (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans s8))))))).mono
              (by norm_num)⟩
          · intro j hj1 hj2
            simp [hr₄, hr₃, hr₂, hr₁, Function.update_apply, show j ≠ -10 by omega,
              show j ≠ -11 by omega]
          · simp [regs, upd, hr₄, hr₃, hr₂, hr₁, ha, hneg, hHR, hle, Function.update_apply]
        · have s8 := reaches_jle_reg_pos (P := prog) (pc := 99) (j := -11) (target := 107) rfl
            (by norm_num) (by norm_num) h d r₄ (by rw [hr₄v]; exact lt_of_not_ge hle)
          have s9 := setr_tail h d r₄
          refine ⟨_, ?_, ?_,
            (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans
              (s8.trans s9)))))))).mono (by norm_num)⟩
          · intro j hj1 hj2
            simp [hr₄, hr₃, hr₂, hr₁, Function.update_apply, show j ≠ -7 by omega,
              show j ≠ -8 by omega, show j ≠ -10 by omega, show j ≠ -11 by omega]
          · simp [regs, upd, hr₄, hr₃, hr₂, hr₁, ha, hneg, hHR, hle, Function.update_apply]
    · -- a = 0
      have s4 := reaches_jle_reg_le (P := prog) (pc := 95) (j := -10) (target := 105) rfl
        (by norm_num) (by norm_num) h d r₂ (by rw [hr₂v]; exact not_lt.mp hneg)
      by_cases hb : d h ≤ 0
      · have s5 := reaches_jle_head_le (P := prog) (pc := 105) (target := 107) rfl h d r₂ hb
        refine ⟨r₂, ?_, ?_, (s1.trans (s2.trans (s3.trans (s4.trans s5)))).mono (by norm_num)⟩
        · intro j hj1 hj2
          simp [hr₂, hr₁, Function.update_apply, show j ≠ -10 by omega]
        · simp [regs, upd, hr₂, hr₁, ha, hneg, hb, Function.update_apply]
      · have s5 := reaches_jle_head_pos (P := prog) (pc := 105) (target := 107) rfl h d r₂
          (lt_of_not_ge hb)
        have s6 := reaches_const_reg (P := prog) (pc := 106) (j := -9) (c := 1) rfl
          (by norm_num) (by norm_num) h d r₂
        refine ⟨_, ?_, ?_,
          (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans s6))))).mono (by norm_num)⟩
        · intro j hj1 hj2
          simp [hr₂, hr₁, Function.update_apply, show j ≠ -9 by omega, show j ≠ -10 by omega]
        · simp [regs, upd, hr₂, hr₁, ha, hneg, hb, Function.update_apply]

end SmaleNinth.BSS

/-!
Assembly: the outer loop, the final decision, the semantics of the abstract
state, the input encoding, and the quadratic-time theorem.
-/

open SmaleNinth Matrix LinearOptimization

namespace SmaleNinth.BSS

/-! ### Abstract state along the constraints -/

/-- The abstract state after processing constraints `0 … i-1`. -/
noncomputable def stF (a b : ℕ → ℝ) : ℕ → St
  | 0 => ⟨0, 0, 0, 0, 0⟩
  | i + 1 => upd (stF a b i) (a i) (b i)

/-- The Boolean verdict read off a state. -/
noncomputable def verdict (s : St) : Bool :=
  if s.BAD ≤ 0 ∧ (s.HL ≤ 0 ∨ s.HR ≤ 0 ∨ s.L - s.R ≤ 0) then true else false

/-! ### The outer loop -/

lemma outer_step (d : ℤ → ℝ) (m i : ℕ) (hi : i < m) (r : ℤ → ℝ)
    (hOUT : r (-2) = ((m - i : ℕ) : ℝ)) (hM : r (-3) = (m : ℝ)) :
    ∃ r', r' (-2) = ((m - (i + 1) : ℕ) : ℝ) ∧ r' (-3) = (m : ℝ) ∧
      regs r' = upd (regs r) (d (2 + i)) (d (2 + m + i)) ∧
      Reaches prog ⟨50, phys (2 + i) d r⟩ ⟨50, phys (2 + (i + 1)) d r'⟩ (56 * m) := by
  have hOUTpos : 0 < r (-2) := by
    rw [hOUT]; exact_mod_cast Nat.sub_pos_of_lt hi
  have s1 := reaches_jle_reg_pos (P := prog) (pc := 50) (j := -2) (target := 143) rfl
    (by norm_num) (by norm_num) (2 + i) d r hOUTpos
  have s2 := reaches_mov_head (P := prog) (pc := 51) (j := -4) rfl rfl (by norm_num) (by norm_num)
    (2 + i) d r
  set r₁ := Function.update r (-4) (d (2 + i)) with hr₁
  have s3 := reaches_mov_reg (P := prog) (pc := 53) (j := -1) (s := -3) rfl rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (2 + i) d r₁
  set r₂ := Function.update r₁ (-1) (r₁ (-3)) with hr₂
  have hr₂1 : r₂ (-1) = (m : ℝ) := by simp [hr₂, hr₁, hM]
  obtain ⟨r₃, hp₃, hr₃1, s4⟩ := walk_right d m (2 + i) r₂ hr₂1
  obtain ⟨r₄, hp₄, hregs₄, s5⟩ := update_block (2 + i + m) d r₃
  have s6 := reaches_mov_reg (P := prog) (pc := 107) (j := -1) (s := -3) rfl rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (2 + i + m) d r₄
  set r₅ := Function.update r₄ (-1) (r₄ (-3)) with hr₅
  have s7 := reaches_const_reg (P := prog) (pc := 109) (j := -11) (c := 1) rfl
    (by norm_num) (by norm_num) (2 + i + m) d r₅
  set r₆ := Function.update r₅ (-11) (1 : ℝ) with hr₆
  have s8 := reaches_sub_reg (P := prog) (pc := 110) (j := -1) (a := -1) (b := -11) rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (2 + i + m) d r₆
  set r₇ := Function.update r₆ (-1) (r₆ (-1) - r₆ (-11)) with hr₇
  have hM₄ : r₄ (-3) = (m : ℝ) := by
    rw [hp₄ (-3) (by norm_num) (by norm_num), hp₃ (-3) (by norm_num) (by norm_num)]
    simp [hr₂, hr₁, hM]
  have hr₇1 : r₇ (-1) = ((m - 1 : ℕ) : ℝ) := by
    simp [hr₇, hr₆, hr₅, hM₄]
    rw [Nat.cast_sub (by omega)]; simp
  obtain ⟨r₈, hp₈, hr₈1, s9⟩ := walk_left d (m - 1) (2 + i + m) r₇ hr₇1
  have s10 := reaches_const_reg (P := prog) (pc := 139) (j := -11) (c := 1) rfl
    (by norm_num) (by norm_num) (2 + i + m - ((m - 1 : ℕ) : ℤ)) d r₈
  set r₉ := Function.update r₈ (-11) (1 : ℝ) with hr₉
  have s11 := reaches_sub_reg (P := prog) (pc := 140) (j := -2) (a := -2) (b := -11) rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (2 + i + m - ((m - 1 : ℕ) : ℤ)) d r₉
  set r₁₀ := Function.update r₉ (-2) (r₉ (-2) - r₉ (-11)) with hr₁₀
  have s12 := reaches_const_reg (P := prog) (pc := 141) (j := -11) (c := 0) rfl
    (by norm_num) (by norm_num) (2 + i + m - ((m - 1 : ℕ) : ℤ)) d r₁₀
  set r₁₁ := Function.update r₁₀ (-11) (0 : ℝ) with hr₁₁
  have s13 := reaches_jle_reg_le (P := prog) (pc := 142) (j := -11) (target := 50) rfl
    (by norm_num) (by norm_num) (2 + i + m - ((m - 1 : ℕ) : ℤ)) d r₁₁ (by simp [hr₁₁])
  -- register bookkeeping
  have hOUT₄ : r₄ (-2) = r (-2) := by
    rw [hp₄ (-2) (by norm_num) (by norm_num), hp₃ (-2) (by norm_num) (by norm_num)]
    simp [hr₂, hr₁]
  have hOUT₈ : r₈ (-2) = r (-2) := by
    rw [hp₈ (-2) (by norm_num) (by norm_num)]
    simp [hr₇, hr₆, hr₅, hOUT₄]
  have hM₈ : r₈ (-3) = (m : ℝ) := by
    rw [hp₈ (-3) (by norm_num) (by norm_num)]
    simp [hr₇, hr₆, hr₅, hM₄]
  have hregs₃ : regs r₃ = regs r := by
    simp only [regs]
    rw [hp₃ (-5) (by norm_num) (by norm_num), hp₃ (-6) (by norm_num) (by norm_num),
      hp₃ (-7) (by norm_num) (by norm_num), hp₃ (-8) (by norm_num) (by norm_num),
      hp₃ (-9) (by norm_num) (by norm_num)]
    simp [hr₂, hr₁]
  have hA₃ : r₃ (-4) = d (2 + i) := by
    rw [hp₃ (-4) (by norm_num) (by norm_num)]; simp [hr₂, hr₁]
  have hregs₈ : regs r₈ = regs r₄ := by
    simp only [regs]
    rw [hp₈ (-5) (by norm_num) (by norm_num), hp₈ (-6) (by norm_num) (by norm_num),
      hp₈ (-7) (by norm_num) (by norm_num), hp₈ (-8) (by norm_num) (by norm_num),
      hp₈ (-9) (by norm_num) (by norm_num)]
    simp [hr₇, hr₆, hr₅]
  refine ⟨r₁₁, ?_, ?_, ?_, ?_⟩
  · simp only [hr₁₁, hr₁₀, hr₉, Function.update_apply]
    simp [hOUT₈, hOUT]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  · simp [hr₁₁, hr₁₀, hr₉, hM₈]
  · have : regs r₁₁ = regs r₈ := by simp [regs, hr₁₁, hr₁₀, hr₉]
    rw [this, hregs₈, hregs₄, hregs₃, hA₃]
    congr 1; ring
  · have hall := s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans
      (s8.trans (s9.trans (s10.trans (s11.trans (s12.trans s13)))))))))))
    refine (hall.mono (by omega)).cast ?_
    congr 2
    rw [Nat.cast_sub (by omega)]; push_cast; ring

lemma outer_loop (d : ℤ → ℝ) (m : ℕ) (r₀ : ℤ → ℝ) (h0 : r₀ (-2) = (m : ℝ))
    (hM : r₀ (-3) = (m : ℝ)) (hregs : regs r₀ = ⟨0, 0, 0, 0, 0⟩) :
    ∀ i ≤ m, ∃ r, r (-2) = ((m - i : ℕ) : ℝ) ∧ r (-3) = (m : ℝ) ∧
      regs r = stF (fun j => d (2 + j)) (fun j => d (2 + m + j)) i ∧
      Reaches prog ⟨50, phys 2 d r₀⟩ ⟨50, phys (2 + i) d r⟩ (i * (56 * m)) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨r₀, by simpa using h0, hM, by simpa [stF] using hregs, ?_⟩
    simpa using Reaches.refl prog _
  | succ i ih =>
    intro hi
    obtain ⟨r, hr2, hr3, hregs, hreach⟩ := ih (by omega)
    obtain ⟨r', hr'2, hr'3, hregs', hstep⟩ := outer_step d m i (by omega) r hr2 hr3
    refine ⟨r', hr'2, hr'3, ?_, ?_⟩
    · rw [hregs', hregs]; rfl
    · have := hreach.trans hstep
      refine this.mono (by ring_nf; rfl)

/-! ### The final block -/

lemma final_block (h : ℤ) (d r : ℤ → ℝ) (hOUT : r (-2) ≤ 0) :
    ∃ (pc : ℕ) (τ : ℤ → ℝ), Reaches prog ⟨50, phys h d r⟩ ⟨pc, τ⟩ 6 ∧
      prog[pc]? = some (if verdict (regs r) then BSSInstr.accept else BSSInstr.reject) := by
  have s1 := reaches_jle_reg_le (P := prog) (pc := 50) (j := -2) (target := 143) rfl
    (by norm_num) (by norm_num) h d r hOUT
  by_cases hbad : r (-9) ≤ 0
  · have s2 := reaches_jle_reg_le (P := prog) (pc := 143) (j := -9) (target := 145) rfl
      (by norm_num) (by norm_num) h d r hbad
    by_cases hhl : r (-6) ≤ 0
    · have s3 := reaches_jle_reg_le (P := prog) (pc := 145) (j := -6) (target := 150) rfl
        (by norm_num) (by norm_num) h d r hhl
      refine ⟨150, _, (s1.trans (s2.trans s3)).mono (by norm_num), ?_⟩
      simp [verdict, regs, hbad, hhl]; rfl
    · have s3 := reaches_jle_reg_pos (P := prog) (pc := 145) (j := -6) (target := 150) rfl
        (by norm_num) (by norm_num) h d r (lt_of_not_ge hhl)
      by_cases hhr : r (-8) ≤ 0
      · have s4 := reaches_jle_reg_le (P := prog) (pc := 146) (j := -8) (target := 150) rfl
          (by norm_num) (by norm_num) h d r hhr
        refine ⟨150, _, (s1.trans (s2.trans (s3.trans s4))).mono (by norm_num), ?_⟩
        simp [verdict, regs, hbad, hhl, hhr]; rfl
      · have s4 := reaches_jle_reg_pos (P := prog) (pc := 146) (j := -8) (target := 150) rfl
          (by norm_num) (by norm_num) h d r (lt_of_not_ge hhr)
        have s5 := reaches_sub_reg (P := prog) (pc := 147) (j := -10) (a := -5) (b := -7) rfl
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          h d r
        set r₁ := Function.update r (-10) (r (-5) - r (-7)) with hr₁
        by_cases hlr : r (-5) - r (-7) ≤ 0
        · have s6 := reaches_jle_reg_le (P := prog) (pc := 148) (j := -10) (target := 150) rfl
            (by norm_num) (by norm_num) h d r₁ (by simp [hr₁]; linarith)
          refine ⟨150, _, (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans s6))))).mono
            (by norm_num), ?_⟩
          simp [verdict, regs, hbad, hhl, hhr, hlr]; rfl
        · have s6 := reaches_jle_reg_pos (P := prog) (pc := 148) (j := -10) (target := 150) rfl
            (by norm_num) (by norm_num) h d r₁ (by simp [hr₁]; linarith [lt_of_not_ge hlr])
          refine ⟨149, _, (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans s6))))).mono
            (by norm_num), ?_⟩
          simp [verdict, regs, hbad, hhl, hhr, hlr]; rfl
  · have s2 := reaches_jle_reg_pos (P := prog) (pc := 143) (j := -9) (target := 145) rfl
      (by norm_num) (by norm_num) h d r (lt_of_not_ge hbad)
    refine ⟨144, _, (s1.trans s2).mono (by norm_num), ?_⟩
    simp [verdict, regs, hbad]; rfl

/-! ### Semantics of the abstract state -/

/-- What the abstract state records about the first `i` constraints. -/
structure Spec (a b : ℕ → ℝ) (i : ℕ) (s : St) : Prop where
  hl01 : s.HL = 0 ∨ s.HL = 1
  hl_iff : s.HL = 1 ↔ ∃ j < i, 0 < a j
  l_ub : s.HL = 1 → ∀ j < i, 0 < a j → b j / a j ≤ s.L
  l_att : s.HL = 1 → ∃ j < i, 0 < a j ∧ b j / a j = s.L
  hr01 : s.HR = 0 ∨ s.HR = 1
  hr_iff : s.HR = 1 ↔ ∃ j < i, a j < 0
  r_lb : s.HR = 1 → ∀ j < i, a j < 0 → s.R ≤ b j / a j
  r_att : s.HR = 1 → ∃ j < i, a j < 0 ∧ b j / a j = s.R
  bad01 : s.BAD = 0 ∨ s.BAD = 1
  bad_iff : s.BAD = 1 ↔ ∃ j < i, a j = 0 ∧ 0 < b j

lemma exists_lt_succ' {p : ℕ → Prop} (i : ℕ) :
    (∃ j < i + 1, p j) ↔ (∃ j < i, p j) ∨ p i := by
  constructor
  · rintro ⟨j, hj, hp⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
    · exact Or.inl ⟨j, h, hp⟩
    · exact Or.inr hp
  · rintro (⟨j, hj, hp⟩ | hp)
    · exact ⟨j, by omega, hp⟩
    · exact ⟨i, by omega, hp⟩

lemma spec_stF (a b : ℕ → ℝ) : ∀ i, Spec a b i (stF a b i)
  | 0 => by
    refine ⟨Or.inl rfl, ?_, ?_, ?_, Or.inl rfl, ?_, ?_, ?_, Or.inl rfl, ?_⟩ <;>
      simp [stF]
  | i + 1 => by
    obtain ⟨hl01, hl_iff, l_ub, l_att, hr01, hr_iff, r_lb, r_att, bad01, bad_iff⟩ :=
      spec_stF a b i
    set s := stF a b i with hs
    have hst : stF a b (i + 1) = upd s (a i) (b i) := rfl
    rw [hst]
    unfold upd
    by_cases ha : 0 < a i
    · rw [if_pos ha]
      have hnotneg : ¬ a i < 0 := by linarith
      have hnotzero : ¬ (a i = 0 ∧ 0 < b i) := fun h => by linarith [h.1]
      by_cases hHL : s.HL ≤ 0
      · rw [if_pos hHL]
        have hHL0 : s.HL = 0 := by rcases hl01 with h | h <;> [exact h; linarith]
        have hnone : ¬ ∃ j < i, 0 < a j := by
          rw [← hl_iff]; rw [hHL0]; norm_num
        refine ⟨Or.inr rfl, ?_, ?_, ?_, hr01, ?_, ?_, ?_, bad01, ?_⟩
        · simp only [true_iff]; exact ⟨i, by omega, ha⟩
        · intro _ j hj hj'
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
          · exact absurd ⟨j, h, hj'⟩ hnone
          · exact le_rfl
        · intro _; exact ⟨i, by omega, ha, rfl⟩
        · rw [exists_lt_succ']; simp only [hnotneg, or_false]; exact hr_iff
        · intro h j hj hj'
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
          · exact r_lb h j h' hj'
          · exact absurd hj' hnotneg
        · intro h; obtain ⟨j, hj, hj'⟩ := r_att h; exact ⟨j, by omega, hj'⟩
        · rw [exists_lt_succ']; simp only [hnotzero, or_false]; exact bad_iff
      · rw [if_neg hHL]
        have hHL1 : s.HL = 1 := by rcases hl01 with h | h <;> [linarith; exact h]
        by_cases hle : b i / a i - s.L ≤ 0
        · rw [if_pos hle]
          refine ⟨hl01, ?_, ?_, ?_, hr01, ?_, ?_, ?_, bad01, ?_⟩
          · rw [exists_lt_succ']; constructor
            · intro h; exact Or.inl (hl_iff.mp h)
            · intro _; exact hHL1
          · intro h j hj hj'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
            · exact l_ub h j h' hj'
            · linarith
          · intro h; obtain ⟨j, hj, hj'⟩ := l_att h; exact ⟨j, by omega, hj'⟩
          · rw [exists_lt_succ']; simp only [hnotneg, or_false]; exact hr_iff
          · intro h j hj hj'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
            · exact r_lb h j h' hj'
            · exact absurd hj' hnotneg
          · intro h; obtain ⟨j, hj, hj'⟩ := r_att h; exact ⟨j, by omega, hj'⟩
          · rw [exists_lt_succ']; simp only [hnotzero, or_false]; exact bad_iff
        · rw [if_neg hle]
          refine ⟨Or.inr rfl, ?_, ?_, ?_, hr01, ?_, ?_, ?_, bad01, ?_⟩
          · simp only [true_iff]; exact ⟨i, by omega, ha⟩
          · intro _ j hj hj'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
            · have := l_ub hHL1 j h' hj'; simp only; linarith
            · exact le_rfl
          · intro _; exact ⟨i, by omega, ha, rfl⟩
          · rw [exists_lt_succ']; simp only [hnotneg, or_false]; exact hr_iff
          · intro h j hj hj'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
            · exact r_lb h j h' hj'
            · exact absurd hj' hnotneg
          · intro h; obtain ⟨j, hj, hj'⟩ := r_att h; exact ⟨j, by omega, hj'⟩
          · rw [exists_lt_succ']; simp only [hnotzero, or_false]; exact bad_iff
    · rw [if_neg ha]
      by_cases hneg : 0 < -a i
      · rw [if_pos hneg]
        have ha' : a i < 0 := by linarith
        have hnotpos : ¬ 0 < a i := ha
        have hnotzero : ¬ (a i = 0 ∧ 0 < b i) := fun h => by linarith [h.1]
        by_cases hHR : s.HR ≤ 0
        · rw [if_pos hHR]
          have hHR0 : s.HR = 0 := by rcases hr01 with h | h <;> [exact h; linarith]
          have hnone : ¬ ∃ j < i, a j < 0 := by
            rw [← hr_iff]; rw [hHR0]; norm_num
          refine ⟨hl01, ?_, ?_, ?_, Or.inr rfl, ?_, ?_, ?_, bad01, ?_⟩
          · rw [exists_lt_succ']; simp only [hnotpos, or_false]; exact hl_iff
          · intro h j hj hj'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
            · exact l_ub h j h' hj'
            · exact absurd hj' hnotpos
          · intro h; obtain ⟨j, hj, hj'⟩ := l_att h; exact ⟨j, by omega, hj'⟩
          · simp only [true_iff]; exact ⟨i, by omega, ha'⟩
          · intro _ j hj hj'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
            · exact absurd ⟨j, h', hj'⟩ hnone
            · exact le_rfl
          · intro _; exact ⟨i, by omega, ha', rfl⟩
          · rw [exists_lt_succ']; simp only [hnotzero, or_false]; exact bad_iff
        · rw [if_neg hHR]
          have hHR1 : s.HR = 1 := by rcases hr01 with h | h <;> [linarith; exact h]
          by_cases hle : s.R - b i / a i ≤ 0
          · rw [if_pos hle]
            refine ⟨hl01, ?_, ?_, ?_, hr01, ?_, ?_, ?_, bad01, ?_⟩
            · rw [exists_lt_succ']; simp only [hnotpos, or_false]; exact hl_iff
            · intro h j hj hj'
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
              · exact l_ub h j h' hj'
              · exact absurd hj' hnotpos
            · intro h; obtain ⟨j, hj, hj'⟩ := l_att h; exact ⟨j, by omega, hj'⟩
            · rw [exists_lt_succ']; constructor
              · intro h; exact Or.inl (hr_iff.mp h)
              · intro _; exact hHR1
            · intro h j hj hj'
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
              · exact r_lb h j h' hj'
              · linarith
            · intro h; obtain ⟨j, hj, hj'⟩ := r_att h; exact ⟨j, by omega, hj'⟩
            · rw [exists_lt_succ']; simp only [hnotzero, or_false]; exact bad_iff
          · rw [if_neg hle]
            refine ⟨hl01, ?_, ?_, ?_, Or.inr rfl, ?_, ?_, ?_, bad01, ?_⟩
            · rw [exists_lt_succ']; simp only [hnotpos, or_false]; exact hl_iff
            · intro h j hj hj'
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
              · exact l_ub h j h' hj'
              · exact absurd hj' hnotpos
            · intro h; obtain ⟨j, hj, hj'⟩ := l_att h; exact ⟨j, by omega, hj'⟩
            · simp only [true_iff]; exact ⟨i, by omega, ha'⟩
            · intro _ j hj hj'
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
              · have := r_lb hHR1 j h' hj'; simp only; linarith
              · exact le_rfl
            · intro _; exact ⟨i, by omega, ha', rfl⟩
            · rw [exists_lt_succ']; simp only [hnotzero, or_false]; exact bad_iff
      · rw [if_neg hneg]
        have ha0 : a i = 0 := by linarith
        have hnotpos : ¬ 0 < a i := ha
        have hnotneg : ¬ a i < 0 := by linarith
        by_cases hb : b i ≤ 0
        · rw [if_pos hb]
          have hnotzero : ¬ (a i = 0 ∧ 0 < b i) := fun h => by linarith [h.2]
          refine ⟨hl01, ?_, ?_, ?_, hr01, ?_, ?_, ?_, bad01, ?_⟩
          · rw [exists_lt_succ']; simp only [hnotpos, or_false]; exact hl_iff
          · intro h j hj hj'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
            · exact l_ub h j h' hj'
            · exact absurd hj' hnotpos
          · intro h; obtain ⟨j, hj, hj'⟩ := l_att h; exact ⟨j, by omega, hj'⟩
          · rw [exists_lt_succ']; simp only [hnotneg, or_false]; exact hr_iff
          · intro h j hj hj'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
            · exact r_lb h j h' hj'
            · exact absurd hj' hnotneg
          · intro h; obtain ⟨j, hj, hj'⟩ := r_att h; exact ⟨j, by omega, hj'⟩
          · rw [exists_lt_succ']; simp only [hnotzero, or_false]; exact bad_iff
        · rw [if_neg hb]
          refine ⟨hl01, ?_, ?_, ?_, hr01, ?_, ?_, ?_, Or.inr rfl, ?_⟩
          · rw [exists_lt_succ']; simp only [hnotpos, or_false]; exact hl_iff
          · intro h j hj hj'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
            · exact l_ub h j h' hj'
            · exact absurd hj' hnotpos
          · intro h; obtain ⟨j, hj, hj'⟩ := l_att h; exact ⟨j, by omega, hj'⟩
          · rw [exists_lt_succ']; simp only [hnotneg, or_false]; exact hr_iff
          · intro h j hj hj'
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
            · exact r_lb h j h' hj'
            · exact absurd hj' hnotneg
          · intro h; obtain ⟨j, hj, hj'⟩ := r_att h; exact ⟨j, by omega, hj'⟩
          · simp only [true_iff]; exact ⟨i, by omega, ha0, lt_of_not_ge hb⟩

/-- The verdict is correct: feasibility of the first `m` constraints. -/
lemma verdict_iff (a b : ℕ → ℝ) (m : ℕ) :
    verdict (stF a b m) = true ↔ ∃ t : ℝ, ∀ j < m, b j ≤ a j * t := by
  obtain ⟨hl01, hl_iff, l_ub, l_att, hr01, hr_iff, r_lb, r_att, bad01, bad_iff⟩ :=
    spec_stF a b m
  set s := stF a b m with hs
  unfold verdict
  simp only [Bool.ite_eq_true_distrib, if_true_left, ite_eq_left_iff, Bool.false_eq_true,
    imp_false, not_not]
  constructor
  · rintro ⟨hbad, hcase⟩
    have hbad0 : s.BAD = 0 := by rcases bad01 with h | h <;> [exact h; linarith]
    have hnobad : ¬ ∃ j < m, a j = 0 ∧ 0 < b j := by rw [← bad_iff, hbad0]; norm_num
    -- choose the witness
    by_cases hHL : s.HL = 1
    · refine ⟨s.L, fun j hj => ?_⟩
      rcases lt_trichotomy (a j) 0 with hneg | hzero | hpos
      · have hHR : s.HR = 1 := hr_iff.mpr ⟨j, hj, hneg⟩
        have hLR : s.L ≤ s.R := by
          rcases hcase with h | h | h
          · rw [hHL] at h; norm_num at h
          · rw [hHR] at h; norm_num at h
          · linarith
        have := r_lb hHR j hj hneg
        have h2 : s.L ≤ b j / a j := le_trans hLR this
        rw [le_div_iff_of_neg hneg] at h2; linarith
      · by_contra hcon
        exact hnobad ⟨j, hj, hzero, by rw [hzero] at hcon; simpa using hcon⟩
      · have := l_ub hHL j hj hpos
        rw [div_le_iff₀ hpos] at this; linarith
    · have hHL0 : s.HL = 0 := by rcases hl01 with h | h <;> [exact h; exact absurd h hHL]
      have hnopos : ¬ ∃ j < m, 0 < a j := by rw [← hl_iff]; exact hHL
      by_cases hHR : s.HR = 1
      · refine ⟨s.R, fun j hj => ?_⟩
        rcases lt_trichotomy (a j) 0 with hneg | hzero | hpos
        · have := r_lb hHR j hj hneg
          rw [le_div_iff_of_neg hneg] at this; linarith
        · by_contra hcon
          exact hnobad ⟨j, hj, hzero, by rw [hzero] at hcon; simpa using hcon⟩
        · exact absurd ⟨j, hj, hpos⟩ hnopos
      · have hnoneg : ¬ ∃ j < m, a j < 0 := by rw [← hr_iff]; exact hHR
        refine ⟨0, fun j hj => ?_⟩
        rcases lt_trichotomy (a j) 0 with hneg | hzero | hpos
        · exact absurd ⟨j, hj, hneg⟩ hnoneg
        · by_contra hcon
          exact hnobad ⟨j, hj, hzero, by rw [hzero] at hcon; simpa using hcon⟩
        · exact absurd ⟨j, hj, hpos⟩ hnopos
  · rintro ⟨t, ht⟩
    refine ⟨?_, ?_⟩
    · rcases bad01 with h | h
      · rw [h]
      · exfalso
        obtain ⟨j, hj, hz, hb⟩ := bad_iff.mp h
        have := ht j hj; rw [hz, zero_mul] at this; linarith
    · by_cases hHL : s.HL = 1
      · by_cases hHR : s.HR = 1
        · right; right
          obtain ⟨j, hj, hjpos, hjL⟩ := l_att hHL
          obtain ⟨k, hk, hkneg, hkR⟩ := r_att hHR
          have h1 := ht j hj
          have h2 := ht k hk
          rw [← hjL, ← hkR]
          have e1 : b j / a j ≤ t := by rw [div_le_iff₀ hjpos]; linarith
          have e2 : t ≤ b k / a k := by rw [le_div_iff_of_neg hkneg]; linarith
          linarith
        · right; left
          rcases hr01 with h | h
          · rw [h]
          · exact absurd h hHR
      · left
        rcases hl01 with h | h
        · rw [h]
        · exact absurd h hHL

/-! ### The input encoding -/

lemma encodeLP_neg {m : ℕ} (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ) (k : ℤ) (hk : k < 0) :
    encodeLP A b k = 0 := by
  unfold encodeLP
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_neg (by omega)]

lemma encodeLP_zero {m : ℕ} (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ) :
    encodeLP A b 0 = (m : ℝ) := by
  simp [encodeLP]

lemma encodeLP_a {m : ℕ} (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ) (j : ℕ) (hj : j < m) :
    encodeLP A b (2 + (j : ℤ)) = A ⟨j, hj⟩ 0 := by
  unfold encodeLP
  rw [if_neg (by omega), if_neg (by omega), if_pos (by push_cast; omega)]
  have : ((2 + (j : ℤ)) - 2).toNat = j := by omega
  rw [this]
  unfold matrixEntryRM
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1
  · exact Fin.ext (by simp)
  · exact Subsingleton.elim _ _

lemma encodeLP_b {m : ℕ} (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ) (j : ℕ) (hj : j < m) :
    encodeLP A b (2 + (m : ℤ) + (j : ℤ)) = b ⟨j, hj⟩ := by
  unfold encodeLP
  rw [if_neg (by omega), if_neg (by omega), if_neg (by push_cast; omega),
    dif_pos ⟨by push_cast; omega, by push_cast; omega⟩]
  congr 1
  exact Fin.ext (by simp)

lemma encodeLP_eq_phys {m : ℕ} (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ) :
    encodeLP A b = phys 0 (encodeLP A b) (fun _ => 0) := by
  funext k
  unfold phys
  split_ifs with h1 h2
  · simp
  · exact encodeLP_neg A b k (by omega)
  · rw [encodeLP_neg A b k (by omega), encodeLP_neg A b _ (by omega)]

lemma polyhedron_nonempty_iff {m : ℕ} (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ) :
    (polyhedron A b).Nonempty ↔
      ∃ t : ℝ, ∀ j < m, (if h : j < m then b ⟨j, h⟩ else 0) ≤
        (if h : j < m then A ⟨j, h⟩ 0 else 0) * t := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x 0, fun j hj => ?_⟩
    rw [dif_pos hj, dif_pos hj]
    have := hx ⟨j, hj⟩
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_one] using this
  · rintro ⟨t, ht⟩
    refine ⟨fun _ => t, fun i => ?_⟩
    have := ht i i.isLt
    rw [dif_pos i.isLt, dif_pos i.isLt] at this
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_one] using this

/-! ### The theorem -/

theorem bss_decides_one_variable_lp_quadratic :
    ∃ (P : BSSProgram) (C : ℕ),
      ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          BSSDecidesInTime P (encodeLP A b) (C * (m + 1) ^ 2) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by
  refine ⟨prog, 100, fun m A b => ?_⟩
  set d := encodeLP A b with hd
  set a' : ℕ → ℝ := fun j => if h : j < m then A ⟨j, h⟩ 0 else 0 with ha'
  set b' : ℕ → ℝ := fun j => if h : j < m then b ⟨j, h⟩ else 0 with hb'
  obtain ⟨r₀, hr₀3, hr₀2, hr₀z, hinit⟩ := init_block d
  have hd0 : d 0 = (m : ℝ) := encodeLP_zero A b
  have hregs₀ : regs r₀ = ⟨0, 0, 0, 0, 0⟩ := by
    simp only [regs]
    rw [hr₀z (-5) (by norm_num) (by norm_num), hr₀z (-6) (by norm_num) (by norm_num),
      hr₀z (-7) (by norm_num) (by norm_num), hr₀z (-8) (by norm_num) (by norm_num),
      hr₀z (-9) (by norm_num) (by norm_num)]
  obtain ⟨r, hr2, hr3, hregs, hloop⟩ :=
    outer_loop d m r₀ (by rw [hr₀2, hd0]) (by rw [hr₀3, hd0]) hregs₀ m le_rfl
  have hstate : stF (fun j => d (2 + (j : ℤ))) (fun j => d (2 + (m : ℤ) + (j : ℤ))) m
      = stF a' b' m := by
    have key : ∀ i ≤ m, stF (fun j => d (2 + (j : ℤ))) (fun j => d (2 + (m : ℤ) + (j : ℤ))) i
        = stF a' b' i := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
        intro hi
        simp only [stF]
        rw [ih (by omega), ha', hb']
        simp only [dif_pos (show i < m by omega)]
        rw [hd, encodeLP_a A b i (by omega), encodeLP_b A b i (by omega)]
    exact key m le_rfl
  obtain ⟨pc, τ, hfin, hpc⟩ := final_block (2 + (m : ℤ)) d r (by rw [hr2]; simp)
  refine ⟨verdict (regs r), ?_, ?_⟩
  · have hall := hinit.trans (hloop.trans hfin)
    have hall' : Reaches prog ⟨0, phys 0 d (fun _ => 0)⟩ ⟨pc, τ⟩ (100 * (m + 1) ^ 2) :=
      hall.mono (by nlinarith [Nat.zero_le m])
    have hx : d = phys 0 d (fun _ => 0) := encodeLP_eq_phys A b
    have := decides_of_reaches hall' hpc
    rwa [← hx] at this
  · rw [hregs, hstate, verdict_iff, polyhedron_nonempty_iff]

end SmaleNinth.BSS

open SmaleNinth Matrix LinearOptimization

theorem solution :
    ∃ (P : BSSProgram) (C : ℕ),
      ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          BSSDecidesInTime P (encodeLP A b) (C * (m + 1) ^ 2) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) :=
  SmaleNinth.BSS.bss_decides_one_variable_lp_quadratic

-- Prove2me | solution 1 for SmaleNinth.real_ram_decides_two_variable_lp_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T02:25:14.220815+00:00
-- url     : https://prove2.me/submissions/55f0c6d6-1f0d-4c75-ba2d-0e2f03622722

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine
import Definitions.Def_SmaleNinth_RealRAM
import Theorems.Thm_SmaleNinth_two_variable_lp_fourier_motzkin
import Mathlib.Tactic

/-!
# Two-variable LP feasibility on the real pointer machine in quadratic time

A 90-instruction program of `Def_SmaleNinth_RealRAM` decides the feasibility of
`aᵢx + bᵢy ≥ cᵢ (i < m)` on the encoding `encodeLP` within `100 (m+1)²` steps.

The algorithm fuses Fourier–Motzkin elimination of the second variable with the
one-variable sweep.  The published theorem
`SmaleNinth.two_variable_lp_fourier_motzkin` says that the system is feasible
exactly when the one-variable system consisting of the rows with vanishing
second coefficient and of the combinations of pairs of rows with second
coefficients of opposite signs is feasible.  Instead of materialising that
quadratically large system, the program runs a double loop over ordered pairs
`(k, l)` of rows and feeds the derived constraint `fedA`/`fedB` directly into
the running interval; pairs of the wrong kind are fed `0 ≥ 0`, which the update
leaves invariant, so every pass costs the same bounded number of steps.

The abstract layer (`St`, `upd`, `stF`, `verdict`, `Spec`, `verdict_iff`) is the
machine-independent part of the author's one-variable development, reused
verbatim; `RReaches` and the per-instruction lemmas are its machine calculus.
-/

open SmaleNinth Matrix LinearOptimization Finset

namespace SmaleNinth.RAMLP


/-- The abstract state carried in registers `-5 … -9`. -/
@[ext] structure St where
  L : ℝ
  HL : ℝ
  R : ℝ
  HR : ℝ
  BAD : ℝ


/-- The abstract update performed by the block on constraint `a·x ≥ b`. -/
noncomputable def upd (s : St) (a b : ℝ) : St :=
  if 0 < a then
    (if s.HL ≤ 0 then ⟨b / a, 1, s.R, s.HR, s.BAD⟩
     else if b / a - s.L ≤ 0 then s else ⟨b / a, 1, s.R, s.HR, s.BAD⟩)
  else if 0 < -a then
    (if s.HR ≤ 0 then ⟨s.L, s.HL, b / a, 1, s.BAD⟩
     else if s.R - b / a ≤ 0 then s else ⟨s.L, s.HL, b / a, 1, s.BAD⟩)
  else if b ≤ 0 then s else ⟨s.L, s.HL, s.R, s.HR, 1⟩


/-- The abstract state after processing constraints `0 … i-1`. -/
noncomputable def stF (a b : ℕ → ℝ) : ℕ → St
  | 0 => ⟨0, 0, 0, 0, 0⟩
  | i + 1 => upd (stF a b i) (a i) (b i)

/-- The Boolean verdict read off a state. -/
noncomputable def verdict (s : St) : Bool :=
  if s.BAD ≤ 0 ∧ (s.HL ≤ 0 ∨ s.HR ≤ 0 ∨ s.L - s.R ≤ 0) then true else false


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


/-- `RReaches R s₁ s₂ b`: `s₂` is reached from `s₁` in at most `b` steps. -/
def RReaches (R : RAMProgram) (s₁ s₂ : RAMConfig) (b : ℕ) : Prop :=
  ∃ t ≤ b, (RAMStep R)^[t] s₁ = s₂

lemma RReaches.refl (R : RAMProgram) (s : RAMConfig) : RReaches R s s 0 := ⟨0, le_rfl, rfl⟩

lemma RReaches.trans {R : RAMProgram} {s₁ s₂ s₃ : RAMConfig} {b₁ b₂ : ℕ}
    (h₁ : RReaches R s₁ s₂ b₁) (h₂ : RReaches R s₂ s₃ b₂) : RReaches R s₁ s₃ (b₁ + b₂) := by
  obtain ⟨t₁, ht₁, rfl⟩ := h₁
  obtain ⟨t₂, ht₂, rfl⟩ := h₂
  exact ⟨t₂ + t₁, by omega, by rw [Function.iterate_add_apply]⟩

lemma RReaches.mono {R : RAMProgram} {s₁ s₂ : RAMConfig} {b b' : ℕ}
    (h : RReaches R s₁ s₂ b) (hb : b ≤ b') : RReaches R s₁ s₂ b' := by
  obtain ⟨t, ht, e⟩ := h; exact ⟨t, le_trans ht hb, e⟩

lemma RReaches.single {R : RAMProgram} {s₁ s₂ : RAMConfig} (h : RAMStep R s₁ = s₂) :
    RReaches R s₁ s₂ 1 := ⟨1, le_rfl, by simpa using h⟩

/-! ### One lemma per instruction -/

variable {R : RAMProgram} {pc : ℕ}

lemma r_const {dst : ℕ} {c : ℝ} (h : R[pc]? = some (.const dst c)) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (mem : ℤ → ℝ) :
    RReaches R ⟨pc, g, p, mem⟩ ⟨pc + 1, Function.update g dst c, p, mem⟩ 1 :=
  RReaches.single (by simp [RAMStep, h])

lemma r_add {dst i j : ℕ} (h : R[pc]? = some (.add dst i j)) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (mem : ℤ → ℝ) :
    RReaches R ⟨pc, g, p, mem⟩ ⟨pc + 1, Function.update g dst (g i + g j), p, mem⟩ 1 :=
  RReaches.single (by simp [RAMStep, h])

lemma r_sub {dst i j : ℕ} (h : R[pc]? = some (.sub dst i j)) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (mem : ℤ → ℝ) :
    RReaches R ⟨pc, g, p, mem⟩ ⟨pc + 1, Function.update g dst (g i - g j), p, mem⟩ 1 :=
  RReaches.single (by simp [RAMStep, h])

lemma r_mul {dst i j : ℕ} (h : R[pc]? = some (.mul dst i j)) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (mem : ℤ → ℝ) :
    RReaches R ⟨pc, g, p, mem⟩ ⟨pc + 1, Function.update g dst (g i * g j), p, mem⟩ 1 :=
  RReaches.single (by simp [RAMStep, h])

lemma r_div {dst i j : ℕ} (h : R[pc]? = some (.div dst i j)) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (mem : ℤ → ℝ) :
    RReaches R ⟨pc, g, p, mem⟩ ⟨pc + 1, Function.update g dst (g i / g j), p, mem⟩ 1 :=
  RReaches.single (by simp [RAMStep, h])

lemma r_load {dst q : ℕ} (h : R[pc]? = some (.load dst q)) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (mem : ℤ → ℝ) :
    RReaches R ⟨pc, g, p, mem⟩ ⟨pc + 1, Function.update g dst (mem (p q)), p, mem⟩ 1 :=
  RReaches.single (by simp [RAMStep, h])

lemma r_pset {q : ℕ} {c : ℤ} (h : R[pc]? = some (.pset q c)) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (mem : ℤ → ℝ) :
    RReaches R ⟨pc, g, p, mem⟩ ⟨pc + 1, g, Function.update p q c, mem⟩ 1 :=
  RReaches.single (by simp [RAMStep, h])

lemma r_pcopy {q q' : ℕ} (h : R[pc]? = some (.pcopy q q')) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (mem : ℤ → ℝ) :
    RReaches R ⟨pc, g, p, mem⟩ ⟨pc + 1, g, Function.update p q (p q'), mem⟩ 1 :=
  RReaches.single (by simp [RAMStep, h])

lemma r_pinc {q : ℕ} (h : R[pc]? = some (.pinc q)) (g : ℕ → ℝ) (p : ℕ → ℤ) (mem : ℤ → ℝ) :
    RReaches R ⟨pc, g, p, mem⟩ ⟨pc + 1, g, Function.update p q (p q + 1), mem⟩ 1 :=
  RReaches.single (by simp [RAMStep, h])

lemma r_jle_le {i target : ℕ} (h : R[pc]? = some (.jle i target)) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (mem : ℤ → ℝ) (hg : g i ≤ 0) :
    RReaches R ⟨pc, g, p, mem⟩ ⟨target, g, p, mem⟩ 1 :=
  RReaches.single (by simp [RAMStep, h, hg])

lemma r_jle_pos {i target : ℕ} (h : R[pc]? = some (.jle i target)) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (mem : ℤ → ℝ) (hg : ¬ g i ≤ 0) :
    RReaches R ⟨pc, g, p, mem⟩ ⟨pc + 1, g, p, mem⟩ 1 :=
  RReaches.single (by simp [RAMStep, h, hg])

/-- Reaching a halting instruction decides the input. -/
lemma decides_of_rreaches {R : RAMProgram} {x : ℤ → ℝ} {pc : ℕ} {g : ℕ → ℝ} {p : ℕ → ℤ}
    {n : ℕ} {b : Bool}
    (h : RReaches R ⟨0, fun _ => 0, fun _ => 0, x⟩ ⟨pc, g, p, x⟩ n)
    (hpc : R[pc]? = some (if b then RAMInstr.accept else RAMInstr.reject)) :
    RAMDecidesInTime R x n b := by
  obtain ⟨t, ht, e⟩ := h
  refine ⟨t, ht, ?_⟩
  unfold RAMHaltedWith RAMRun
  rw [e]
  exact hpc


/-- The abstract state read off the register file. -/
def regsOf (g : ℕ → ℝ) : St := ⟨g 0, g 1, g 2, g 3, g 4⟩

lemma cast_sub_pos {m k : ℕ} (h : k < m) : ¬ (((m - k : ℕ) : ℝ) ≤ 0) := by
  have : 0 < m - k := by omega
  exact not_le.mpr (by exact_mod_cast this)

lemma cast_sub_succ {m k : ℕ} (h : k < m) :
    ((m - k : ℕ) : ℝ) - 1 = ((m - (k + 1) : ℕ) : ℝ) := by
  have e : m - k = (m - (k + 1)) + 1 := by omega
  rw [e]; push_cast; ring


/-- Coefficient of the constraint fed at the pair `(k, l)`. -/
noncomputable def fedA (a b : ℕ → ℝ) (k l : ℕ) : ℝ :=
  if 0 < b k ∧ b l < 0 then b k * a l - b l * a k
  else if k = l ∧ b k = 0 then a k
  else 0

/-- Right-hand side of the constraint fed at the pair `(k, l)`. -/
noncomputable def fedB (b cc : ℕ → ℝ) (k l : ℕ) : ℝ :=
  if 0 < b k ∧ b l < 0 then b k * cc l - b l * cc k
  else if k = l ∧ b k = 0 then cc k
  else 0

lemma fed_iff (a b cc : ℕ → ℝ) (m : ℕ) (t : ℝ) :
    (∀ e < m * m, fedB b cc (e / m) (e % m) ≤ fedA a b (e / m) (e % m) * t) ↔
      ((∀ k < m, b k = 0 → cc k ≤ a k * t) ∧
       (∀ k < m, ∀ l < m, 0 < b k → b l < 0 →
          b k * cc l - b l * cc k ≤ (b k * a l - b l * a k) * t)) := by
  constructor
  · intro h
    constructor
    · intro k hk hb
      have hlt : k * m + k < m * m := by nlinarith
      have hthis := h (k * m + k) hlt
      have e1 : (k * m + k) / m = k := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (show 0 < m by omega),
          Nat.div_eq_of_lt hk, Nat.zero_add]
      have e2 : (k * m + k) % m = k := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
      have hne : ¬ (0 < b k ∧ b k < 0) := by
        rintro ⟨h1, -⟩; rw [hb] at h1; exact lt_irrefl 0 h1
      have hfa : fedA a b k k = a k := by simp [fedA, hne, hb]
      have hfb : fedB b cc k k = cc k := by simp [fedB, hne, hb]
      rw [e1, e2, hfa, hfb] at hthis
      exact hthis
    · intro k hk l hl hbk hbl
      have hlt : k * m + l < m * m := by nlinarith
      have hthis := h (k * m + l) hlt
      have e1 : (k * m + l) / m = k := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (show 0 < m by omega),
          Nat.div_eq_of_lt hl, Nat.zero_add]
      have e2 : (k * m + l) % m = l := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
      have hfa : fedA a b k l = b k * a l - b l * a k := by simp [fedA, hbk, hbl]
      have hfb : fedB b cc k l = b k * cc l - b l * cc k := by simp [fedB, hbk, hbl]
      rw [e1, e2, hfa, hfb] at hthis
      exact hthis
  · rintro ⟨hZ, hP⟩ e he
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at he
      · exact h
    have hk : e / m < m := Nat.div_lt_of_lt_mul (by omega)
    have hl : e % m < m := Nat.mod_lt _ hm
    simp only [fedA, fedB]
    split_ifs with h1 h2
    · exact hP _ hk _ hl h1.1 h1.2
    · exact hZ _ hk h2.2
    · simp


/-- The two-variable program. -/
noncomputable def tvprog : RAMProgram :=
[ .pset 4 0            -- 0
, .load 12 4           -- 1   m
, .const 10 1          -- 2
, .const 11 0          -- 3
, .const 0 0           -- 4
, .const 1 0           -- 5
, .const 2 0           -- 6
, .const 3 0           -- 7
, .const 4 0           -- 8
, .pset 5 2            -- 9
, .add 20 12 11        -- 10  scratch := m
, .jle 20 16           -- 11  shift loop head
, .pinc 5              -- 12
, .pinc 5              -- 13
, .sub 20 20 10        -- 14
, .jle 11 11           -- 15
, .pset 0 2            -- 16
, .pcopy 1 5           -- 17
, .add 9 12 11         -- 18  outer counter := m
, .jle 9 82            -- 19  outer head
, .load 14 0           -- 20  a_k
, .pinc 0              -- 21
, .load 15 0           -- 22  b_k
, .pinc 0              -- 23
, .load 16 1           -- 24  c_k
, .pinc 1              -- 25
, .pset 2 2            -- 26
, .pcopy 3 5           -- 27
, .add 13 12 11        -- 28  inner counter := m
, .jle 13 80           -- 29  inner head
, .load 17 2           -- 30  a_l
, .pinc 2              -- 31
, .load 18 2           -- 32  b_l
, .pinc 2              -- 33
, .load 19 3           -- 34  c_l
, .pinc 3              -- 35
, .jle 15 46           -- 36  b_k ≤ 0 → zero-row branch
, .sub 8 11 18         -- 37  -b_l
, .jle 8 58            -- 38  b_l ≥ 0 → vacuous
, .mul 5 15 17         -- 39  b_k * a_l
, .mul 8 18 14         -- 40  b_l * a_k
, .sub 5 5 8           -- 41
, .mul 6 15 19         -- 42  b_k * c_l
, .mul 8 18 16         -- 43  b_l * c_k
, .sub 6 6 8           -- 44
, .jle 11 60           -- 45  → update
, .sub 8 11 15         -- 46  -b_k
, .jle 8 49            -- 47  b_k = 0 → equality test
, .jle 11 58           -- 48  b_k < 0 → vacuous
, .sub 8 9 13          -- 49
, .jle 8 52            -- 50
, .jle 11 58           -- 51  → vacuous
, .sub 8 13 9          -- 52
, .jle 8 55            -- 53  → zero-row feed
, .jle 11 58           -- 54  → vacuous
, .add 5 14 11         -- 55  a_fed := a_k
, .add 6 16 11         -- 56  b_fed := c_k
, .jle 11 60           -- 57  → update
, .const 5 0           -- 58  vacuous feed
, .const 6 0           -- 59
, .div 7 6 5           -- 60  update block
, .jle 5 68            -- 61
, .jle 1 65            -- 62
, .sub 8 7 0           -- 63
, .jle 8 78            -- 64
, .const 1 1           -- 65
, .add 0 7 11          -- 66
, .jle 11 78           -- 67
, .sub 8 11 5          -- 68
, .jle 8 76            -- 69
, .jle 3 73            -- 70
, .sub 8 2 7           -- 71
, .jle 8 78            -- 72
, .const 3 1           -- 73
, .add 2 7 11          -- 74
, .jle 11 78           -- 75
, .jle 6 78            -- 76
, .const 4 1           -- 77
, .sub 13 13 10        -- 78  inner counter -= 1
, .jle 11 29           -- 79
, .sub 9 9 10          -- 80  outer counter -= 1
, .jle 11 19           -- 81
, .jle 4 84            -- 82  final
, .reject              -- 83
, .jle 1 89            -- 84
, .jle 3 89            -- 85
, .sub 8 0 2           -- 86
, .jle 8 89            -- 87
, .reject              -- 88
, .accept ]            -- 89

/-! ### Initialisation -/

lemma tv_shift_step (x : ℤ → ℝ) (m k : ℕ) (hk : k < m) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (h20 : g 20 = ((m - k : ℕ) : ℝ)) (h10 : g 10 = 1) (h11 : g 11 = 0) :
    ∃ (g' : ℕ → ℝ) (p' : ℕ → ℤ),
      regsOf g' = regsOf g ∧
      g' 20 = ((m - (k + 1) : ℕ) : ℝ) ∧ g' 10 = 1 ∧ g' 11 = 0 ∧ g' 12 = g 12 ∧
      p' 5 = p 5 + 2 ∧
      RReaches tvprog ⟨11, g, p, x⟩ ⟨11, g', p', x⟩ 5 := by
  have chain :=
    (r_jle_pos (R := tvprog) (pc := 11) rfl g p x (by rw [h20]; exact cast_sub_pos hk)).trans <|
    (r_pinc (R := tvprog) (pc := 12) rfl _ _ _).trans <|
    (r_pinc (R := tvprog) (pc := 13) rfl _ _ _).trans <|
    (r_sub (R := tvprog) (pc := 14) rfl _ _ _).trans
    (r_jle_le (R := tvprog) (pc := 15) rfl _ _ _ (by simp [Function.update_apply, h11]))
  refine ⟨_, _, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
  · simp [regsOf, Function.update_apply]
  · simp [Function.update_apply, h20, h10, cast_sub_succ hk]
  · simp [Function.update_apply, h10]
  · simp [Function.update_apply, h11]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
    ring

lemma tv_shift_loop (x : ℤ → ℝ) (m : ℕ) (g₀ : ℕ → ℝ) (p₀ : ℕ → ℤ)
    (h20 : g₀ 20 = (m : ℝ)) (h10 : g₀ 10 = 1) (h11 : g₀ 11 = 0) :
    ∀ k ≤ m, ∃ (g : ℕ → ℝ) (p : ℕ → ℤ),
      regsOf g = regsOf g₀ ∧
      g 20 = ((m - k : ℕ) : ℝ) ∧ g 10 = 1 ∧ g 11 = 0 ∧ g 12 = g₀ 12 ∧
      p 5 = p₀ 5 + 2 * k ∧
      RReaches tvprog ⟨11, g₀, p₀, x⟩ ⟨11, g, p, x⟩ (5 * k) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨g₀, p₀, rfl, by simpa using h20, h10, h11, rfl, by simp,
      by simpa using RReaches.refl _ _⟩
  | succ k ih =>
    intro hk
    obtain ⟨g, p, hst, h20', h10', h11', h12', hp5, hreach⟩ := ih (by omega)
    obtain ⟨g', p', hst2, h20'', h10'', h11'', h12'', hp5', hstep⟩ :=
      tv_shift_step x m k (by omega) g p h20' h10' h11'
    exact ⟨g', p', by rw [hst2, hst], h20'', h10'', h11'', by rw [h12'', h12'],
      by rw [hp5', hp5]; push_cast; ring, (hreach.trans hstep).mono (by omega)⟩

lemma tv_init_prefix (x : ℤ → ℝ) (m : ℕ) (hx : x 0 = (m : ℝ)) :
    ∃ (g : ℕ → ℝ) (p : ℕ → ℤ),
      regsOf g = ⟨0, 0, 0, 0, 0⟩ ∧ g 20 = (m : ℝ) ∧ g 10 = 1 ∧ g 11 = 0 ∧ g 12 = (m : ℝ) ∧
      p 5 = 2 ∧
      RReaches tvprog ⟨0, fun _ => 0, fun _ => 0, x⟩ ⟨11, g, p, x⟩ 11 := by
  have chain :=
    (r_pset (R := tvprog) (pc := 0) rfl (fun _ => (0:ℝ)) (fun _ => (0:ℤ)) x).trans <|
    (r_load (R := tvprog) (pc := 1) rfl _ _ _).trans <|
    (r_const (R := tvprog) (pc := 2) rfl _ _ _).trans <|
    (r_const (R := tvprog) (pc := 3) rfl _ _ _).trans <|
    (r_const (R := tvprog) (pc := 4) rfl _ _ _).trans <|
    (r_const (R := tvprog) (pc := 5) rfl _ _ _).trans <|
    (r_const (R := tvprog) (pc := 6) rfl _ _ _).trans <|
    (r_const (R := tvprog) (pc := 7) rfl _ _ _).trans <|
    (r_const (R := tvprog) (pc := 8) rfl _ _ _).trans <|
    (r_pset (R := tvprog) (pc := 9) rfl _ _ _).trans
    (r_add (R := tvprog) (pc := 10) rfl _ _ _)
  refine ⟨_, _, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
  · simp [regsOf, Function.update_apply]
  · simp [Function.update_apply, hx]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply, hx]
  · simp [Function.update_apply]

lemma tv_init (x : ℤ → ℝ) (m : ℕ) (hx : x 0 = (m : ℝ)) :
    ∃ (g : ℕ → ℝ) (p : ℕ → ℤ),
      regsOf g = ⟨0, 0, 0, 0, 0⟩ ∧ g 9 = (m : ℝ) ∧ g 10 = 1 ∧ g 11 = 0 ∧ g 12 = (m : ℝ) ∧
      p 0 = 2 ∧ p 1 = 2 + 2 * (m : ℤ) ∧ p 5 = 2 + 2 * (m : ℤ) ∧
      RReaches tvprog ⟨0, fun _ => 0, fun _ => 0, x⟩ ⟨19, g, p, x⟩ (5 * m + 15) := by
  obtain ⟨g₀, p₀, hst₀, h20₀, h10₀, h11₀, h12₀, hp5₀, hpre⟩ := tv_init_prefix x m hx
  obtain ⟨g, p, hstl, h20, h10, h11, h12, hp5, hloop⟩ :=
    tv_shift_loop x m g₀ p₀ h20₀ h10₀ h11₀ m le_rfl
  have hexit : g 20 ≤ 0 := by rw [h20]; simp
  have chain2 :=
    (r_jle_le (R := tvprog) (pc := 11) rfl g p x hexit).trans <|
    (r_pset (R := tvprog) (pc := 16) rfl _ _ _).trans <|
    (r_pcopy (R := tvprog) (pc := 17) rfl _ _ _).trans
    (r_add (R := tvprog) (pc := 18) rfl _ _ _)
  refine ⟨_, _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ((hpre.trans hloop).trans chain2).mono (by omega)⟩
  · rw [← hst₀, ← hstl]; simp [regsOf, Function.update_apply]
  · simp [Function.update_apply, h12, h12₀, h11]
  · simp [Function.update_apply, h10]
  · simp [Function.update_apply, h11]
  · simp [Function.update_apply, h12, h12₀]
  · simp [Function.update_apply]
  · simp [Function.update_apply, hp5, hp5₀]
  · simp [Function.update_apply, hp5, hp5₀]

/-! ### The update block `60 → 29` -/

lemma tv_upd_block (x : ℤ → ℝ) (a b : ℝ) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (h5 : g 5 = a) (h6 : g 6 = b) (h11 : g 11 = 0) :
    ∃ g' : ℕ → ℝ,
      regsOf g' = upd (regsOf g) a b ∧
      g' 9 = g 9 ∧ g' 10 = g 10 ∧ g' 11 = 0 ∧ g' 12 = g 12 ∧ g' 13 = g 13 - g 10 ∧
      g' 14 = g 14 ∧ g' 15 = g 15 ∧ g' 16 = g 16 ∧
      RReaches tvprog ⟨60, g, p, x⟩ ⟨29, g', p, x⟩ 12 := by
  -- the division comes first; afterwards register 7 holds `b / a`
  have hdiv := r_div (R := tvprog) (pc := 60) rfl g p x
  set g₀ : ℕ → ℝ := Function.update g 7 (g 6 / g 5) with hg₀
  have e5 : g₀ 5 = a := by simp [hg₀, Function.update_apply, h5]
  have e6 : g₀ 6 = b := by simp [hg₀, Function.update_apply, h6]
  have e7 : g₀ 7 = b / a := by simp [hg₀, Function.update_apply, h5, h6]
  have e11 : g₀ 11 = 0 := by simp [hg₀, Function.update_apply, h11]
  have e0 : g₀ 0 = g 0 := by simp [hg₀, Function.update_apply]
  have e1 : g₀ 1 = g 1 := by simp [hg₀, Function.update_apply]
  have e2 : g₀ 2 = g 2 := by simp [hg₀, Function.update_apply]
  have e3 : g₀ 3 = g 3 := by simp [hg₀, Function.update_apply]
  have e4 : g₀ 4 = g 4 := by simp [hg₀, Function.update_apply]
  have ereg : regsOf g₀ = regsOf g := by simp [regsOf, e0, e1, e2, e3, e4]
  have tail : ∀ g₁ : ℕ → ℝ, g₁ 11 = 0 →
      RReaches tvprog ⟨78, g₁, p, x⟩ ⟨29, Function.update g₁ 13 (g₁ 13 - g₁ 10), p, x⟩ 2 := by
    intro g₁ h
    exact ((r_sub (R := tvprog) (pc := 78) rfl g₁ p x).trans
      (r_jle_le (R := tvprog) (pc := 79) rfl _ _ _ (by simp [Function.update_apply, h])))
  by_cases ha : (0 : ℝ) < a
  · have h61 : ¬ g₀ 5 ≤ 0 := by rw [e5]; exact not_le.mpr ha
    by_cases hhl : g₀ 1 ≤ 0
    · have chain :=
        (hdiv.trans <|
        (r_jle_pos (R := tvprog) (pc := 61) rfl g₀ p x h61).trans <|
        (r_jle_le (R := tvprog) (pc := 62) rfl _ _ _ hhl).trans <|
        (r_const (R := tvprog) (pc := 65) rfl _ _ _).trans <|
        (r_add (R := tvprog) (pc := 66) rfl _ _ _).trans
        (r_jle_le (R := tvprog) (pc := 67) rfl _ _ _
          (by simp [Function.update_apply, e11]))).trans
        (tail _ (by simp [Function.update_apply, e11]))
      have hupd : upd (regsOf g) a b = ⟨b / a, 1, g 2, g 3, g 4⟩ := by
        simp [upd, regsOf, ha, e1 ▸ hhl]
      refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
      · rw [hupd]; simp [regsOf, Function.update_apply, e7, e11, e2, e3, e4]
      · simp [hg₀, Function.update_apply]
      · simp [hg₀, Function.update_apply]
      · simp [hg₀, Function.update_apply, h11]
      · simp [hg₀, Function.update_apply]
      · simp [hg₀, Function.update_apply]
      · simp [hg₀, Function.update_apply]
      · simp [hg₀, Function.update_apply]
      · simp [hg₀, Function.update_apply]
    · by_cases hcmp : b / a - g 0 ≤ 0
      · have chain :=
          (hdiv.trans <|
          (r_jle_pos (R := tvprog) (pc := 61) rfl g₀ p x h61).trans <|
          (r_jle_pos (R := tvprog) (pc := 62) rfl _ _ _ hhl).trans <|
          (r_sub (R := tvprog) (pc := 63) rfl _ _ _).trans
          (r_jle_le (R := tvprog) (pc := 64) rfl _ _ _
            (by simp [Function.update_apply, e7, e0]; linarith))).trans
          (tail _ (by simp [Function.update_apply, e11]))
        have hupd : upd (regsOf g) a b = regsOf g := by
          simp [upd, regsOf, ha, e1 ▸ hhl, hcmp]
        refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
        · rw [hupd]; simp [regsOf, Function.update_apply, e0, e1, e2, e3, e4]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply, h11]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
      · have chain :=
          (hdiv.trans <|
          (r_jle_pos (R := tvprog) (pc := 61) rfl g₀ p x h61).trans <|
          (r_jle_pos (R := tvprog) (pc := 62) rfl _ _ _ hhl).trans <|
          (r_sub (R := tvprog) (pc := 63) rfl _ _ _).trans <|
          (r_jle_pos (R := tvprog) (pc := 64) rfl _ _ _
            (by simp [Function.update_apply, e7, e0]; linarith [not_le.mp hcmp])).trans <|
          (r_const (R := tvprog) (pc := 65) rfl _ _ _).trans <|
          (r_add (R := tvprog) (pc := 66) rfl _ _ _).trans
          (r_jle_le (R := tvprog) (pc := 67) rfl _ _ _
            (by simp [Function.update_apply, e11]))).trans
          (tail _ (by simp [Function.update_apply, e11]))
        have hupd : upd (regsOf g) a b = ⟨b / a, 1, g 2, g 3, g 4⟩ := by
          simp [upd, regsOf, ha, e1 ▸ hhl, hcmp]
        refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
        · rw [hupd]; simp [regsOf, Function.update_apply, e7, e11, e2, e3, e4]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply, h11]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
  · have h61 : g₀ 5 ≤ 0 := by rw [e5]; exact not_lt.mp ha
    by_cases hneg : (0 : ℝ) < -a
    · have h69 : ¬ (g₀ 11 - g₀ 5 : ℝ) ≤ 0 := by
        rw [e11, e5]; simpa using not_le.mpr hneg
      by_cases hhr : g₀ 3 ≤ 0
      · have chain :=
          (hdiv.trans <|
          (r_jle_le (R := tvprog) (pc := 61) rfl g₀ p x h61).trans <|
          (r_sub (R := tvprog) (pc := 68) rfl _ _ _).trans <|
          (r_jle_pos (R := tvprog) (pc := 69) rfl _ _ _
            (by simpa [Function.update_apply] using h69)).trans <|
          (r_jle_le (R := tvprog) (pc := 70) rfl _ _ _
            (by simpa [Function.update_apply] using hhr)).trans <|
          (r_const (R := tvprog) (pc := 73) rfl _ _ _).trans <|
          (r_add (R := tvprog) (pc := 74) rfl _ _ _).trans
          (r_jle_le (R := tvprog) (pc := 75) rfl _ _ _
            (by simp [Function.update_apply, e11]))).trans
          (tail _ (by simp [Function.update_apply, e11]))
        have hupd : upd (regsOf g) a b = ⟨g 0, g 1, b / a, 1, g 4⟩ := by
          simp [upd, regsOf, ha, hneg, e3 ▸ hhr]
        refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
        · rw [hupd]; simp [regsOf, Function.update_apply, e7, e11, e0, e1, e4]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply, h11]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
      · by_cases hcmp : g 2 - b / a ≤ 0
        · have chain :=
            (hdiv.trans <|
            (r_jle_le (R := tvprog) (pc := 61) rfl g₀ p x h61).trans <|
            (r_sub (R := tvprog) (pc := 68) rfl _ _ _).trans <|
            (r_jle_pos (R := tvprog) (pc := 69) rfl _ _ _
              (by simpa [Function.update_apply] using h69)).trans <|
            (r_jle_pos (R := tvprog) (pc := 70) rfl _ _ _
              (by simpa [Function.update_apply] using hhr)).trans <|
            (r_sub (R := tvprog) (pc := 71) rfl _ _ _).trans
            (r_jle_le (R := tvprog) (pc := 72) rfl _ _ _
              (by simp [Function.update_apply, e7, e2]; linarith))).trans
            (tail _ (by simp [Function.update_apply, e11]))
          have hupd : upd (regsOf g) a b = regsOf g := by
            simp [upd, regsOf, ha, hneg, e3 ▸ hhr, hcmp]
          refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
          · rw [hupd]; simp [regsOf, Function.update_apply, e0, e1, e2, e3, e4]
          · simp [hg₀, Function.update_apply]
          · simp [hg₀, Function.update_apply]
          · simp [hg₀, Function.update_apply, h11]
          · simp [hg₀, Function.update_apply]
          · simp [hg₀, Function.update_apply]
          · simp [hg₀, Function.update_apply]
          · simp [hg₀, Function.update_apply]
          · simp [hg₀, Function.update_apply]
        · have chain :=
            (hdiv.trans <|
            (r_jle_le (R := tvprog) (pc := 61) rfl g₀ p x h61).trans <|
            (r_sub (R := tvprog) (pc := 68) rfl _ _ _).trans <|
            (r_jle_pos (R := tvprog) (pc := 69) rfl _ _ _
              (by simpa [Function.update_apply] using h69)).trans <|
            (r_jle_pos (R := tvprog) (pc := 70) rfl _ _ _
              (by simpa [Function.update_apply] using hhr)).trans <|
            (r_sub (R := tvprog) (pc := 71) rfl _ _ _).trans <|
            (r_jle_pos (R := tvprog) (pc := 72) rfl _ _ _
              (by simp [Function.update_apply, e7, e2]; linarith [not_le.mp hcmp])).trans <|
            (r_const (R := tvprog) (pc := 73) rfl _ _ _).trans <|
            (r_add (R := tvprog) (pc := 74) rfl _ _ _).trans
            (r_jle_le (R := tvprog) (pc := 75) rfl _ _ _
              (by simp [Function.update_apply, e11]))).trans
            (tail _ (by simp [Function.update_apply, e11]))
          have hupd : upd (regsOf g) a b = ⟨g 0, g 1, b / a, 1, g 4⟩ := by
            simp [upd, regsOf, ha, hneg, e3 ▸ hhr, hcmp]
          refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
          · rw [hupd]; simp [regsOf, Function.update_apply, e7, e11, e0, e1, e4]
          · simp [hg₀, Function.update_apply]
          · simp [hg₀, Function.update_apply]
          · simp [hg₀, Function.update_apply, h11]
          · simp [hg₀, Function.update_apply]
          · simp [hg₀, Function.update_apply]
          · simp [hg₀, Function.update_apply]
          · simp [hg₀, Function.update_apply]
          · simp [hg₀, Function.update_apply]
    · have h69 : (g₀ 11 - g₀ 5 : ℝ) ≤ 0 := by
        rw [e11, e5]; simpa using not_lt.mp hneg
      by_cases hb : b ≤ 0
      · have chain :=
          (hdiv.trans <|
          (r_jle_le (R := tvprog) (pc := 61) rfl g₀ p x h61).trans <|
          (r_sub (R := tvprog) (pc := 68) rfl _ _ _).trans <|
          (r_jle_le (R := tvprog) (pc := 69) rfl _ _ _
            (by simpa [Function.update_apply] using h69)).trans
          (r_jle_le (R := tvprog) (pc := 76) rfl _ _ _
            (by simp [Function.update_apply, e6]; linarith))).trans
          (tail _ (by simp [Function.update_apply, e11]))
        have hupd : upd (regsOf g) a b = regsOf g := by
          simp [upd, regsOf, ha, hneg, hb]
        refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
        · rw [hupd]; simp [regsOf, Function.update_apply, e0, e1, e2, e3, e4]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply, h11]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
      · have chain :=
          (hdiv.trans <|
          (r_jle_le (R := tvprog) (pc := 61) rfl g₀ p x h61).trans <|
          (r_sub (R := tvprog) (pc := 68) rfl _ _ _).trans <|
          (r_jle_le (R := tvprog) (pc := 69) rfl _ _ _
            (by simpa [Function.update_apply] using h69)).trans <|
          (r_jle_pos (R := tvprog) (pc := 76) rfl _ _ _
            (by simp [Function.update_apply, e6]; exact not_le.mp hb)).trans
          (r_const (R := tvprog) (pc := 77) rfl _ _ _)).trans
          (tail _ (by simp [Function.update_apply, e11]))
        have hupd : upd (regsOf g) a b = ⟨g 0, g 1, g 2, g 3, 1⟩ := by
          simp [upd, regsOf, ha, hneg, hb]
        refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
        · rw [hupd]; simp [regsOf, Function.update_apply, e0, e1, e2, e3]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply, h11]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]
        · simp [hg₀, Function.update_apply]


/-! ### Reading a row and choosing the constraint, `29 → 60` -/

/-- The coefficient of the first variable in row `j` of the input. -/
def memA (x : ℤ → ℝ) (j : ℕ) : ℝ := x (2 + 2 * (j : ℤ))
/-- The coefficient of the second variable in row `j` of the input. -/
def memB (x : ℤ → ℝ) (j : ℕ) : ℝ := x (2 + 2 * (j : ℤ) + 1)
/-- The right-hand side of row `j` of the input. -/
def memC (x : ℤ → ℝ) (m j : ℕ) : ℝ := x (2 + 2 * (m : ℤ) + (j : ℤ))

lemma eq_of_diffs {m k l : ℕ} (hk : k < m) (hl : l < m)
    (h1 : ((m - k : ℕ) : ℝ) - ((m - l : ℕ) : ℝ) ≤ 0)
    (h2 : ((m - l : ℕ) : ℝ) - ((m - k : ℕ) : ℝ) ≤ 0) : k = l := by
  have he : ((m - k : ℕ) : ℝ) = ((m - l : ℕ) : ℝ) := by linarith
  have := Nat.cast_inj.mp he
  omega

lemma ne_of_diff_pos {m k l : ℕ}
    (h : ¬ (((m - k : ℕ) : ℝ) - ((m - l : ℕ) : ℝ) ≤ 0)) : k ≠ l := by
  intro hkl; rw [hkl] at h; simp at h

lemma ne_of_diff_pos' {m k l : ℕ}
    (h : ¬ (((m - l : ℕ) : ℝ) - ((m - k : ℕ) : ℝ) ≤ 0)) : k ≠ l := by
  intro hkl; rw [hkl] at h; simp at h

lemma tv_feed_prefix (x : ℤ → ℝ) (m l : ℕ) (hl : l < m) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (h13 : g 13 = ((m - l : ℕ) : ℝ))
    (hp2 : p 2 = 2 + 2 * (l : ℤ)) (hp3 : p 3 = 2 + 2 * (m : ℤ) + (l : ℤ)) :
    ∃ (g₁ : ℕ → ℝ) (p₁ : ℕ → ℤ),
      regsOf g₁ = regsOf g ∧
      g₁ 17 = memA x l ∧ g₁ 18 = memB x l ∧ g₁ 19 = memC x m l ∧
      g₁ 9 = g 9 ∧ g₁ 10 = g 10 ∧ g₁ 11 = g 11 ∧ g₁ 12 = g 12 ∧ g₁ 13 = g 13 ∧
      g₁ 14 = g 14 ∧ g₁ 15 = g 15 ∧ g₁ 16 = g 16 ∧
      p₁ 0 = p 0 ∧ p₁ 1 = p 1 ∧ p₁ 5 = p 5 ∧
      p₁ 2 = 2 + 2 * ((l : ℤ) + 1) ∧ p₁ 3 = 2 + 2 * (m : ℤ) + ((l : ℤ) + 1) ∧
      RReaches tvprog ⟨29, g, p, x⟩ ⟨36, g₁, p₁, x⟩ 7 := by
  have chain :=
    (r_jle_pos (R := tvprog) (pc := 29) rfl g p x (by rw [h13]; exact cast_sub_pos hl)).trans <|
    (r_load (R := tvprog) (pc := 30) rfl _ _ _).trans <|
    (r_pinc (R := tvprog) (pc := 31) rfl _ _ _).trans <|
    (r_load (R := tvprog) (pc := 32) rfl _ _ _).trans <|
    (r_pinc (R := tvprog) (pc := 33) rfl _ _ _).trans <|
    (r_load (R := tvprog) (pc := 34) rfl _ _ _).trans
    (r_pinc (R := tvprog) (pc := 35) rfl _ _ _)
  refine ⟨_, _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    chain.mono (by norm_num)⟩
  · simp [regsOf, Function.update_apply]
  · simp [Function.update_apply, hp2, memA]
  · simp [Function.update_apply, hp2, memB]
  · simp [Function.update_apply, hp3, memC]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply, hp2]; ring
  · simp [Function.update_apply, hp3]; ring

lemma tv_decide (x : ℤ → ℝ) (m k l : ℕ) (hk : k < m) (hl : l < m) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (h9 : g 9 = ((m - k : ℕ) : ℝ)) (h13 : g 13 = ((m - l : ℕ) : ℝ)) (h11 : g 11 = 0)
    (h14 : g 14 = memA x k) (h15 : g 15 = memB x k) (h16 : g 16 = memC x m k)
    (h17 : g 17 = memA x l) (h18 : g 18 = memB x l) (h19 : g 19 = memC x m l) :
    ∃ g' : ℕ → ℝ,
      regsOf g' = regsOf g ∧
      g' 5 = fedA (memA x) (memB x) k l ∧ g' 6 = fedB (memB x) (memC x m) k l ∧
      g' 9 = g 9 ∧ g' 10 = g 10 ∧ g' 11 = 0 ∧ g' 12 = g 12 ∧ g' 13 = g 13 ∧
      g' 14 = g 14 ∧ g' 15 = g 15 ∧ g' 16 = g 16 ∧
      RReaches tvprog ⟨36, g, p, x⟩ ⟨60, g', p, x⟩ 11 := by
  by_cases hbk : g 15 ≤ 0
  · -- `b k ≤ 0`
    have c46 := (r_jle_le (R := tvprog) (pc := 36) rfl g p x hbk).trans
      (r_sub (R := tvprog) (pc := 46) rfl g p x)
    by_cases hbk0 : (g 11 - g 15 : ℝ) ≤ 0
    · -- `b k = 0`
      have hb0 : memB x k = 0 := by rw [← h15]; rw [h11] at hbk0; linarith
      have c49 := (c46.trans (r_jle_le (R := tvprog) (pc := 47) rfl _ _ _
        (by simpa [Function.update_apply] using hbk0))).trans
        (r_sub (R := tvprog) (pc := 49) rfl _ _ _)
      by_cases hd1 : (g 9 - g 13 : ℝ) ≤ 0
      · have c52 := (c49.trans (r_jle_le (R := tvprog) (pc := 50) rfl _ _ _
          (by simpa [Function.update_apply] using hd1))).trans
          (r_sub (R := tvprog) (pc := 52) rfl _ _ _)
        by_cases hd2 : (g 13 - g 9 : ℝ) ≤ 0
        · -- `k = l`: feed the zero row
          have hkl : k = l := eq_of_diffs hk hl (by rw [h9, h13] at hd1; exact hd1)
            (by rw [h9, h13] at hd2; exact hd2)
          have chain := ((c52.trans (r_jle_le (R := tvprog) (pc := 53) rfl _ _ _
            (by simpa [Function.update_apply] using hd2))).trans <|
            (r_add (R := tvprog) (pc := 55) rfl _ _ _).trans <|
            (r_add (R := tvprog) (pc := 56) rfl _ _ _).trans
            (r_jle_le (R := tvprog) (pc := 57) rfl _ _ _
              (by simp [Function.update_apply, h11])))
          have hfa : fedA (memA x) (memB x) k l = memA x k := by
            subst hkl; simp [fedA, hb0]
          have hfb : fedB (memB x) (memC x m) k l = memC x m k := by
            subst hkl; simp [fedB, hb0]
          refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
          · simp [regsOf, Function.update_apply]
          · rw [hfa]; simp [Function.update_apply, h14, h11]
          · rw [hfb]; simp [Function.update_apply, h16, h11]
          all_goals simp [Function.update_apply, h11]
        · -- `k ≠ l`: vacuous
          have hkl : k ≠ l := ne_of_diff_pos' (by rw [h9, h13] at hd2; exact hd2)
          have chain := ((c52.trans (r_jle_pos (R := tvprog) (pc := 53) rfl _ _ _
            (by simpa [Function.update_apply] using hd2))).trans <|
            (r_jle_le (R := tvprog) (pc := 54) rfl _ _ _
              (by simp [Function.update_apply, h11])).trans <|
            (r_const (R := tvprog) (pc := 58) rfl _ _ _).trans
            (r_const (R := tvprog) (pc := 59) rfl _ _ _))
          have hfa : fedA (memA x) (memB x) k l = 0 := by simp [fedA, hb0, hkl]
          have hfb : fedB (memB x) (memC x m) k l = 0 := by simp [fedB, hb0, hkl]
          refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
          · simp [regsOf, Function.update_apply]
          · rw [hfa]; simp [Function.update_apply]
          · rw [hfb]; simp [Function.update_apply]
          all_goals simp [Function.update_apply, h11]
      · -- `k ≠ l`: vacuous
        have hkl : k ≠ l := ne_of_diff_pos (by rw [h9, h13] at hd1; exact hd1)
        have chain := ((c49.trans (r_jle_pos (R := tvprog) (pc := 50) rfl _ _ _
          (by simpa [Function.update_apply] using hd1))).trans <|
          (r_jle_le (R := tvprog) (pc := 51) rfl _ _ _
            (by simp [Function.update_apply, h11])).trans <|
          (r_const (R := tvprog) (pc := 58) rfl _ _ _).trans
          (r_const (R := tvprog) (pc := 59) rfl _ _ _))
        have hfa : fedA (memA x) (memB x) k l = 0 := by simp [fedA, hb0, hkl]
        have hfb : fedB (memB x) (memC x m) k l = 0 := by simp [fedB, hb0, hkl]
        refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
        · simp [regsOf, Function.update_apply]
        · rw [hfa]; simp [Function.update_apply]
        · rw [hfb]; simp [Function.update_apply]
        all_goals simp [Function.update_apply, h11]
    · -- `b k < 0`: vacuous
      have hbneg : memB x k < 0 := by rw [← h15]; rw [h11] at hbk0; linarith [not_le.mp hbk0]
      have chain := ((c46.trans (r_jle_pos (R := tvprog) (pc := 47) rfl _ _ _
        (by simpa [Function.update_apply] using hbk0))).trans <|
        (r_jle_le (R := tvprog) (pc := 48) rfl _ _ _
          (by simp [Function.update_apply, h11])).trans <|
        (r_const (R := tvprog) (pc := 58) rfl _ _ _).trans
        (r_const (R := tvprog) (pc := 59) rfl _ _ _))
      have hfa : fedA (memA x) (memB x) k l = 0 := by
        simp [fedA, not_lt.mpr (le_of_lt hbneg), ne_of_lt hbneg]
      have hfb : fedB (memB x) (memC x m) k l = 0 := by
        simp [fedB, not_lt.mpr (le_of_lt hbneg), ne_of_lt hbneg]
      refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
      · simp [regsOf, Function.update_apply]
      · rw [hfa]; simp [Function.update_apply]
      · rw [hfb]; simp [Function.update_apply]
      all_goals simp [Function.update_apply, h11]
  · -- `b k > 0`
    have hbpos : 0 < memB x k := by rw [← h15]; exact not_le.mp hbk
    have c37 := (r_jle_pos (R := tvprog) (pc := 36) rfl g p x hbk).trans
      (r_sub (R := tvprog) (pc := 37) rfl g p x)
    by_cases hbl : (g 11 - g 18 : ℝ) ≤ 0
    · -- `b l ≥ 0`: vacuous
      have hblnn : ¬ (memB x l < 0) := by
        rw [← h18]; rw [h11] at hbl; linarith
      have chain := ((c37.trans (r_jle_le (R := tvprog) (pc := 38) rfl _ _ _
        (by simpa [Function.update_apply] using hbl))).trans <|
        (r_const (R := tvprog) (pc := 58) rfl _ _ _).trans
        (r_const (R := tvprog) (pc := 59) rfl _ _ _))
      have hfa : fedA (memA x) (memB x) k l = 0 := by
        simp [fedA, hblnn, ne_of_gt hbpos]
      have hfb : fedB (memB x) (memC x m) k l = 0 := by
        simp [fedB, hblnn, ne_of_gt hbpos]
      refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
      · simp [regsOf, Function.update_apply]
      · rw [hfa]; simp [Function.update_apply]
      · rw [hfb]; simp [Function.update_apply]
      all_goals simp [Function.update_apply, h11]
    · -- the pair constraint
      have hblneg : memB x l < 0 := by rw [← h18]; rw [h11] at hbl; linarith [not_le.mp hbl]
      have chain := ((c37.trans (r_jle_pos (R := tvprog) (pc := 38) rfl _ _ _
        (by simpa [Function.update_apply] using hbl))).trans <|
        (r_mul (R := tvprog) (pc := 39) rfl _ _ _).trans <|
        (r_mul (R := tvprog) (pc := 40) rfl _ _ _).trans <|
        (r_sub (R := tvprog) (pc := 41) rfl _ _ _).trans <|
        (r_mul (R := tvprog) (pc := 42) rfl _ _ _).trans <|
        (r_mul (R := tvprog) (pc := 43) rfl _ _ _).trans <|
        (r_sub (R := tvprog) (pc := 44) rfl _ _ _).trans
        (r_jle_le (R := tvprog) (pc := 45) rfl _ _ _
          (by simp [Function.update_apply, h11])))
      have hfa : fedA (memA x) (memB x) k l
          = memB x k * memA x l - memB x l * memA x k := by
        simp [fedA, hbpos, hblneg]
      have hfb : fedB (memB x) (memC x m) k l
          = memB x k * memC x m l - memB x l * memC x m k := by
        simp [fedB, hbpos, hblneg]
      refine ⟨_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
      · simp [regsOf, Function.update_apply]
      · rw [hfa]; simp [Function.update_apply, h14, h15, h17, h18]
      · rw [hfb]; simp [Function.update_apply, h15, h16, h18, h19]
      all_goals simp [Function.update_apply, h11]


/-! ### The loops -/

/-- The linearised sequence of fed coefficients. -/
noncomputable def aSeq (x : ℤ → ℝ) (m : ℕ) : ℕ → ℝ :=
  fun e => fedA (memA x) (memB x) (e / m) (e % m)

/-- The linearised sequence of fed right-hand sides. -/
noncomputable def bSeq (x : ℤ → ℝ) (m : ℕ) : ℕ → ℝ :=
  fun e => fedB (memB x) (memC x m) (e / m) (e % m)

lemma seq_at (x : ℤ → ℝ) (m k l : ℕ) (hl : l < m) :
    aSeq x m (k * m + l) = fedA (memA x) (memB x) k l ∧
    bSeq x m (k * m + l) = fedB (memB x) (memC x m) k l := by
  have e1 : (k * m + l) / m = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (show 0 < m by omega),
      Nat.div_eq_of_lt hl, Nat.zero_add]
  have e2 : (k * m + l) % m = l := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  exact ⟨by simp [aSeq, e1, e2], by simp [bSeq, e1, e2]⟩

lemma tv_inner_step (x : ℤ → ℝ) (m k l : ℕ) (hk : k < m) (hl : l < m) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (h9 : g 9 = ((m - k : ℕ) : ℝ)) (h13 : g 13 = ((m - l : ℕ) : ℝ)) (h10 : g 10 = 1)
    (h11 : g 11 = 0)
    (h14 : g 14 = memA x k) (h15 : g 15 = memB x k) (h16 : g 16 = memC x m k)
    (hp2 : p 2 = 2 + 2 * (l : ℤ)) (hp3 : p 3 = 2 + 2 * (m : ℤ) + (l : ℤ)) :
    ∃ (g' : ℕ → ℝ) (p' : ℕ → ℤ),
      regsOf g' = upd (regsOf g) (aSeq x m (k * m + l)) (bSeq x m (k * m + l)) ∧
      g' 9 = g 9 ∧ g' 10 = g 10 ∧ g' 11 = 0 ∧ g' 12 = g 12 ∧
      g' 13 = ((m - (l + 1) : ℕ) : ℝ) ∧
      g' 14 = g 14 ∧ g' 15 = g 15 ∧ g' 16 = g 16 ∧
      p' 0 = p 0 ∧ p' 1 = p 1 ∧ p' 5 = p 5 ∧
      p' 2 = 2 + 2 * ((l : ℤ) + 1) ∧ p' 3 = 2 + 2 * (m : ℤ) + ((l : ℤ) + 1) ∧
      RReaches tvprog ⟨29, g, p, x⟩ ⟨29, g', p', x⟩ 30 := by
  obtain ⟨g₁, p₁, hst₁, h17, h18, h19, e9, e10, e11, e12, e13, e14, e15, e16,
    q0, q1, q5, q2, q3, hpre⟩ := tv_feed_prefix x m l hl g p h13 hp2 hp3
  obtain ⟨g₂, hst₂, hf5, hf6, f9, f10, f11, f12, f13, f14, f15, f16, hdec⟩ :=
    tv_decide x m k l hk hl g₁ p₁ (by rw [e9, h9]) (by rw [e13, h13]) (by rw [e11, h11])
      (by rw [e14, h14]) (by rw [e15, h15]) (by rw [e16, h16]) h17 h18 h19
  obtain ⟨g₃, hst₃, u9, u10, u11, u12, u13, u14, u15, u16, hupd⟩ :=
    tv_upd_block x _ _ g₂ p₁ hf5 hf6 f11
  obtain ⟨ea, eb⟩ := seq_at x m k l hl
  refine ⟨g₃, p₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ((hpre.trans hdec).trans hupd).mono (by norm_num)⟩
  · rw [hst₃, hst₂, hst₁, ea, eb]
  · rw [u9, f9, e9]
  · rw [u10, f10, e10]
  · exact u11
  · rw [u12, f12, e12]
  · rw [u13, f13, e13, f10, e10, h13, h10, cast_sub_succ hl]
  · rw [u14, f14, e14]
  · rw [u15, f15, e15]
  · rw [u16, f16, e16]
  · exact q0
  · exact q1
  · exact q5
  · exact q2
  · exact q3

lemma tv_inner_loop (x : ℤ → ℝ) (m k : ℕ) (hk : k < m) (g₀ : ℕ → ℝ) (p₀ : ℕ → ℤ)
    (hst : regsOf g₀ = stF (aSeq x m) (bSeq x m) (k * m))
    (h9 : g₀ 9 = ((m - k : ℕ) : ℝ)) (h13 : g₀ 13 = (m : ℝ)) (h10 : g₀ 10 = 1)
    (h11 : g₀ 11 = 0)
    (h14 : g₀ 14 = memA x k) (h15 : g₀ 15 = memB x k) (h16 : g₀ 16 = memC x m k)
    (hp2 : p₀ 2 = 2) (hp3 : p₀ 3 = 2 + 2 * (m : ℤ)) :
    ∀ l ≤ m, ∃ (g : ℕ → ℝ) (p : ℕ → ℤ),
      regsOf g = stF (aSeq x m) (bSeq x m) (k * m + l) ∧
      g 9 = g₀ 9 ∧ g 10 = 1 ∧ g 11 = 0 ∧ g 12 = g₀ 12 ∧ g 13 = ((m - l : ℕ) : ℝ) ∧
      g 14 = g₀ 14 ∧ g 15 = g₀ 15 ∧ g 16 = g₀ 16 ∧
      p 0 = p₀ 0 ∧ p 1 = p₀ 1 ∧ p 5 = p₀ 5 ∧
      p 2 = 2 + 2 * (l : ℤ) ∧ p 3 = 2 + 2 * (m : ℤ) + (l : ℤ) ∧
      RReaches tvprog ⟨29, g₀, p₀, x⟩ ⟨29, g, p, x⟩ (30 * l) := by
  intro l
  induction l with
  | zero =>
    intro _
    exact ⟨g₀, p₀, by simpa using hst, rfl, h10, h11, rfl, by simpa using h13,
      rfl, rfl, rfl, rfl, rfl, rfl, by simpa using hp2, by simpa using hp3,
      by simpa using RReaches.refl _ _⟩
  | succ l ih =>
    intro hlm
    obtain ⟨g, p, hstate, e9, e10, e11, e12, e13, e14, e15, e16, q0, q1, q5, q2, q3, hreach⟩ :=
      ih (by omega)
    obtain ⟨g', p', hst', f9, f10, f11, f12, f13, f14, f15, f16, r0, r1, r5, r2, r3, hstep⟩ :=
      tv_inner_step x m k l hk (by omega) g p (by rw [e9, h9]) e13 e10 e11
        (by rw [e14, h14]) (by rw [e15, h15]) (by rw [e16, h16]) q2 q3
    refine ⟨g', p', ?_, ?_, ?_, ?_, ?_, f13, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (hreach.trans hstep).mono (by omega)⟩
    · rw [hst', hstate, show k * m + (l + 1) = (k * m + l) + 1 from by ring]
      rfl
    · rw [f9, e9]
    · rw [f10, e10]
    · exact f11
    · rw [f12, e12]
    · rw [f14, e14]
    · rw [f15, e15]
    · rw [f16, e16]
    · rw [r0, q0]
    · rw [r1, q1]
    · rw [r5, q5]
    · rw [r2]; push_cast; ring
    · rw [r3]; push_cast; ring

/-! ### The outer loop -/

lemma tv_outer_step (x : ℤ → ℝ) (m k : ℕ) (hk : k < m) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (hst : regsOf g = stF (aSeq x m) (bSeq x m) (k * m))
    (h9 : g 9 = ((m - k : ℕ) : ℝ)) (h10 : g 10 = 1) (h11 : g 11 = 0) (h12 : g 12 = (m : ℝ))
    (hp0 : p 0 = 2 + 2 * (k : ℤ)) (hp1 : p 1 = 2 + 2 * (m : ℤ) + (k : ℤ))
    (hp5 : p 5 = 2 + 2 * (m : ℤ)) :
    ∃ (g' : ℕ → ℝ) (p' : ℕ → ℤ),
      regsOf g' = stF (aSeq x m) (bSeq x m) ((k + 1) * m) ∧
      g' 9 = ((m - (k + 1) : ℕ) : ℝ) ∧ g' 10 = 1 ∧ g' 11 = 0 ∧ g' 12 = (m : ℝ) ∧
      p' 0 = 2 + 2 * ((k : ℤ) + 1) ∧ p' 1 = 2 + 2 * (m : ℤ) + ((k : ℤ) + 1) ∧
      p' 5 = 2 + 2 * (m : ℤ) ∧
      RReaches tvprog ⟨19, g, p, x⟩ ⟨19, g', p', x⟩ (30 * m + 13) := by
  have head :=
    (r_jle_pos (R := tvprog) (pc := 19) rfl g p x (by rw [h9]; exact cast_sub_pos hk)).trans <|
    (r_load (R := tvprog) (pc := 20) rfl _ _ _).trans <|
    (r_pinc (R := tvprog) (pc := 21) rfl _ _ _).trans <|
    (r_load (R := tvprog) (pc := 22) rfl _ _ _).trans <|
    (r_pinc (R := tvprog) (pc := 23) rfl _ _ _).trans <|
    (r_load (R := tvprog) (pc := 24) rfl _ _ _).trans <|
    (r_pinc (R := tvprog) (pc := 25) rfl _ _ _).trans <|
    (r_pset (R := tvprog) (pc := 26) rfl _ _ _).trans <|
    (r_pcopy (R := tvprog) (pc := 27) rfl _ _ _).trans
    (r_add (R := tvprog) (pc := 28) rfl _ _ _)
  obtain ⟨g₁, p₁, hst₁, e9, e10, e11, e12, e13, e14, e15, e16, q2, q3, q0, q1, q5, hpre⟩ :
      ∃ (g₁ : ℕ → ℝ) (p₁ : ℕ → ℤ),
        regsOf g₁ = regsOf g ∧ g₁ 9 = g 9 ∧ g₁ 10 = 1 ∧ g₁ 11 = 0 ∧ g₁ 12 = (m : ℝ) ∧
        g₁ 13 = (m : ℝ) ∧ g₁ 14 = memA x k ∧ g₁ 15 = memB x k ∧ g₁ 16 = memC x m k ∧
        p₁ 2 = 2 ∧ p₁ 3 = 2 + 2 * (m : ℤ) ∧ p₁ 0 = 2 + 2 * ((k : ℤ) + 1) ∧
        p₁ 1 = 2 + 2 * (m : ℤ) + ((k : ℤ) + 1) ∧ p₁ 5 = 2 + 2 * (m : ℤ) ∧
        RReaches tvprog ⟨19, g, p, x⟩ ⟨29, g₁, p₁, x⟩ 10 := by
    refine ⟨_, _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      head.mono (by norm_num)⟩
    · simp [regsOf, Function.update_apply]
    · simp [Function.update_apply]
    · simp [Function.update_apply, h10]
    · simp [Function.update_apply, h11]
    · simp [Function.update_apply, h12]
    · simp [Function.update_apply, h12, h11]
    · simp [Function.update_apply, hp0, memA]
    · simp [Function.update_apply, hp0, memB]
    · simp [Function.update_apply, hp1, memC]
    · simp [Function.update_apply]
    · simp [Function.update_apply, hp5]
    · simp [Function.update_apply, hp0]; ring
    · simp [Function.update_apply, hp1]; ring
    · simp [Function.update_apply, hp5]
  obtain ⟨g₂, p₂, hst₂, f9, f10, f11, f12, f13, f14, f15, f16, s0, s1, s5, s2, s3, hloop⟩ :=
    tv_inner_loop x m k hk g₁ p₁ (by rw [hst₁, hst]) (by rw [e9, h9]) e13 e10 e11 e14 e15 e16
      q2 q3 m le_rfl
  have hexit : g₂ 13 ≤ 0 := by rw [f13]; simp
  have tailc :=
    (r_jle_le (R := tvprog) (pc := 29) rfl g₂ p₂ x hexit).trans <|
    (r_sub (R := tvprog) (pc := 80) rfl _ _ _).trans
    (r_jle_le (R := tvprog) (pc := 81) rfl _ _ _ (by simp [Function.update_apply, f11]))
  refine ⟨_, _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ((hpre.trans hloop).trans tailc).mono (by omega)⟩
  · rw [show (k + 1) * m = k * m + m from by ring]
    simpa [regsOf, Function.update_apply] using hst₂
  · simp only [Function.update_apply]
    norm_num
    rw [f9, e9, h9, f10, cast_sub_succ hk]
  · simp [Function.update_apply, f10]
  · simp [Function.update_apply, f11]
  · simp [Function.update_apply, f12, e12]
  · rw [s0, q0]
  · rw [s1, q1]
  · rw [s5, q5]

/-! ### The outer loop, the verdict, and the theorem -/

lemma tv_outer_loop (x : ℤ → ℝ) (m : ℕ) (g₀ : ℕ → ℝ) (p₀ : ℕ → ℤ)
    (hst : regsOf g₀ = ⟨0, 0, 0, 0, 0⟩) (h9 : g₀ 9 = (m : ℝ)) (h10 : g₀ 10 = 1)
    (h11 : g₀ 11 = 0) (h12 : g₀ 12 = (m : ℝ)) (hp0 : p₀ 0 = 2)
    (hp1 : p₀ 1 = 2 + 2 * (m : ℤ)) (hp5 : p₀ 5 = 2 + 2 * (m : ℤ)) :
    ∀ k ≤ m, ∃ (g : ℕ → ℝ) (p : ℕ → ℤ),
      regsOf g = stF (aSeq x m) (bSeq x m) (k * m) ∧
      g 9 = ((m - k : ℕ) : ℝ) ∧ g 10 = 1 ∧ g 11 = 0 ∧ g 12 = (m : ℝ) ∧
      p 0 = 2 + 2 * (k : ℤ) ∧ p 1 = 2 + 2 * (m : ℤ) + (k : ℤ) ∧ p 5 = 2 + 2 * (m : ℤ) ∧
      RReaches tvprog ⟨19, g₀, p₀, x⟩ ⟨19, g, p, x⟩ ((30 * m + 13) * k) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨g₀, p₀, by rw [Nat.zero_mul]; exact hst, by simpa using h9, h10, h11, h12,
      by simpa using hp0,
      by simpa using hp1, hp5, by simpa using RReaches.refl _ _⟩
  | succ k ih =>
    intro hkm
    obtain ⟨g, p, hstate, e9, e10, e11, e12, q0, q1, q5, hreach⟩ := ih (by omega)
    obtain ⟨g', p', f0, f9, f10, f11, f12, r0, r1, r5, hstep⟩ :=
      tv_outer_step x m k (by omega) g p hstate e9 e10 e11 e12 q0 q1 q5
    refine ⟨g', p', f0, f9, f10, f11, f12, ?_, ?_, r5,
      (hreach.trans hstep).mono (by ring_nf; omega)⟩
    · rw [r0]; push_cast; ring
    · rw [r1]; push_cast; ring

lemma tv_final (x : ℤ → ℝ) (g : ℕ → ℝ) (p : ℕ → ℤ) (h9 : g 9 ≤ 0) :
    ∃ (pc : ℕ) (g' : ℕ → ℝ) (p' : ℕ → ℤ),
      RReaches tvprog ⟨19, g, p, x⟩ ⟨pc, g', p', x⟩ 6 ∧
      tvprog[pc]? = some (if verdict (regsOf g) then RAMInstr.accept else RAMInstr.reject) := by
  have s0 := r_jle_le (R := tvprog) (pc := 19) rfl g p x h9
  by_cases hbad : g 4 ≤ 0
  · have s1 := s0.trans (r_jle_le (R := tvprog) (pc := 82) rfl g p x hbad)
    by_cases hhl : g 1 ≤ 0
    · refine ⟨89, _, _, (s1.trans (r_jle_le (R := tvprog) (pc := 84) rfl g p x hhl)).mono
        (by norm_num), ?_⟩
      have : verdict (regsOf g) = true := by simp [verdict, regsOf, hbad, hhl]
      rw [this]; rfl
    · have s2 := s1.trans (r_jle_pos (R := tvprog) (pc := 84) rfl g p x hhl)
      by_cases hhr : g 3 ≤ 0
      · refine ⟨89, _, _, (s2.trans (r_jle_le (R := tvprog) (pc := 85) rfl g p x hhr)).mono
          (by norm_num), ?_⟩
        have : verdict (regsOf g) = true := by simp [verdict, regsOf, hbad, hhr]
        rw [this]; rfl
      · have s3 := (s2.trans (r_jle_pos (R := tvprog) (pc := 85) rfl g p x hhr)).trans
          (r_sub (R := tvprog) (pc := 86) rfl g p x)
        by_cases hlr : g 0 - g 2 ≤ 0
        · refine ⟨89, _, _, (s3.trans (r_jle_le (R := tvprog) (pc := 87) rfl _ _ _
            (by simp [Function.update_apply]; linarith))).mono (by norm_num), ?_⟩
          have : verdict (regsOf g) = true := by simp [verdict, regsOf, hbad, hlr]
          rw [this]; rfl
        · refine ⟨88, _, _, (s3.trans (r_jle_pos (R := tvprog) (pc := 87) rfl _ _ _
            (by simpa [Function.update_apply] using hlr))).mono (by norm_num), ?_⟩
          have hP : ¬ (g 4 ≤ 0 ∧ (g 1 ≤ 0 ∨ g 3 ≤ 0 ∨ g 0 - g 2 ≤ 0)) := by
            rintro ⟨-, (h | h | h)⟩
            exacts [hhl h, hhr h, hlr h]
          have : verdict (regsOf g) = false := by
            simp only [verdict, regsOf]
            exact if_neg hP
          rw [this]; rfl
  · refine ⟨83, _, _, (s0.trans (r_jle_pos (R := tvprog) (pc := 82) rfl g p x hbad)).mono
      (by norm_num), ?_⟩
    have : verdict (regsOf g) = false := by simp [verdict, regsOf, hbad]
    rw [this]; rfl

/-! ### The input encoding for two variables -/

lemma enc2_zero {m : ℕ} (A : Matrix (Fin m) (Fin 2) ℝ) (b : Fin m → ℝ) :
    encodeLP A b 0 = (m : ℝ) := by simp [encodeLP]

lemma enc2_neg {m : ℕ} (A : Matrix (Fin m) (Fin 2) ℝ) (b : Fin m → ℝ) (k : ℤ) (hk : k < 0) :
    encodeLP A b k = 0 := by
  unfold encodeLP
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_neg (by omega)]

lemma enc2_A {m : ℕ} (A : Matrix (Fin m) (Fin 2) ℝ) (b : Fin m → ℝ) (j : ℕ) (hj : j < m)
    (c : ℕ) (hc : c < 2) :
    encodeLP A b (2 + 2 * (j : ℤ) + (c : ℤ)) = A ⟨j, hj⟩ ⟨c, hc⟩ := by
  have hmn : (2 : ℤ) * m = (m : ℤ) * 2 := by ring
  unfold encodeLP
  rw [if_neg (by omega), if_neg (by omega),
    if_pos (by constructor <;> [omega; (push_cast; nlinarith [hj, hc])])]
  have hidx : ((2 + 2 * (j : ℤ) + (c : ℤ)) - 2).toNat = 2 * j + c := by omega
  rw [hidx]
  unfold matrixEntryRM
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1
  · exact Fin.ext (by simp [Nat.mul_add_div, Nat.div_eq_of_lt hc]; try omega)
  · exact Fin.ext (by simp [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]; try omega)

lemma enc2_b {m : ℕ} (A : Matrix (Fin m) (Fin 2) ℝ) (b : Fin m → ℝ) (j : ℕ) (hj : j < m) :
    encodeLP A b (2 + 2 * (m : ℤ) + (j : ℤ)) = b ⟨j, hj⟩ := by
  unfold encodeLP
  rw [if_neg (by omega), if_neg (by omega), if_neg (by push_cast; omega),
    dif_pos ⟨by push_cast; omega, by push_cast; omega⟩]
  congr 1
  exact Fin.ext (by simp; omega)

/-! ### The theorem -/

theorem tv_main :
    ∃ (R : RAMProgram) (C : ℕ),
      ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 2) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          RAMDecidesInTime R (encodeLP A b) (C * (m + 1) ^ 2) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by
  refine ⟨tvprog, 100, fun m A b => ?_⟩
  set x := encodeLP A b with hx
  have hmemA : ∀ (k : ℕ) (hk : k < m), memA x k = A ⟨k, hk⟩ 0 := by
    intro k hk
    have h := enc2_A A b k hk 0 (by norm_num)
    rw [memA, hx]
    simpa using h
  have hmemB : ∀ (k : ℕ) (hk : k < m), memB x k = A ⟨k, hk⟩ 1 := by
    intro k hk
    have h := enc2_A A b k hk 1 (by norm_num)
    rw [memB, hx]
    simpa using h
  have hmemC : ∀ (k : ℕ) (hk : k < m), memC x m k = b ⟨k, hk⟩ := by
    intro k hk
    have h := enc2_b A b k hk
    rw [memC, hx]
    simpa using h
  obtain ⟨g₀, p₀, hst₀, h9₀, h10₀, h11₀, h12₀, hp0₀, hp1₀, hp5₀, hinit⟩ :=
    tv_init x m (by rw [hx]; exact enc2_zero A b)
  obtain ⟨g, p, hstate, h9, h10, h11, h12, hq0, hq1, hq5, hloop⟩ :=
    tv_outer_loop x m g₀ p₀ hst₀ h9₀ h10₀ h11₀ h12₀ hp0₀ hp1₀ hp5₀ m le_rfl
  obtain ⟨pc, g', p', hfin, hpc⟩ := tv_final x g p (by rw [h9]; simp)
  refine ⟨verdict (regsOf g), ?_, ?_⟩
  · have hall := hinit.trans (hloop.trans hfin)
    exact decides_of_rreaches (hall.mono (by nlinarith)) hpc
  · rw [hstate, verdict_iff, SmaleNinth.two_variable_lp_fourier_motzkin A b]
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨hZ, hP⟩ := (fed_iff (memA x) (memB x) (memC x m) m t).mp ht
      refine ⟨t, ?_, ?_⟩
      · intro i hi0
        have h := hZ i.val i.isLt (by rw [hmemB i.val i.isLt]; simpa using hi0)
        rw [hmemC i.val i.isLt, hmemA i.val i.isLt] at h
        simpa using h
      · intro i j hi hj
        have h := hP i.val i.isLt j.val j.isLt
          (by rw [hmemB i.val i.isLt]; simpa using hi)
          (by rw [hmemB j.val j.isLt]; simpa using hj)
        rw [hmemB i.val i.isLt, hmemB j.val j.isLt, hmemC i.val i.isLt, hmemC j.val j.isLt,
          hmemA i.val i.isLt, hmemA j.val j.isLt] at h
        simpa using h
    · rintro ⟨t, hZ, hP⟩
      refine ⟨t, (fed_iff (memA x) (memB x) (memC x m) m t).mpr ⟨?_, ?_⟩⟩
      · intro k hk hb
        rw [hmemC k hk, hmemA k hk]
        exact hZ ⟨k, hk⟩ (by rw [← hmemB k hk]; exact hb)
      · intro k hk l hl hbk hbl
        rw [hmemB k hk, hmemB l hl, hmemC k hk, hmemC l hl, hmemA k hk, hmemA l hl]
        exact hP ⟨k, hk⟩ ⟨l, hl⟩ (by rw [← hmemB k hk]; exact hbk)
          (by rw [← hmemB l hl]; exact hbl)


end SmaleNinth.RAMLP

open Matrix LinearOptimization

theorem solution :
    ∃ (R : RAMProgram) (C : ℕ),
      ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 2) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          RAMDecidesInTime R (encodeLP A b) (C * (m + 1) ^ 2) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) :=
  SmaleNinth.RAMLP.tv_main

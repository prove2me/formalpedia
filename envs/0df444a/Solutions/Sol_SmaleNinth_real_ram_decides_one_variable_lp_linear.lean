-- Prove2me | solution 1 for SmaleNinth.real_ram_decides_one_variable_lp_linear
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T01:21:05.876912+00:00
-- url     : https://prove2.me/submissions/68dc68a1-14bf-49f0-a57f-9fbcdafa60c8

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine
import Definitions.Def_SmaleNinth_RealRAM
import Mathlib.Tactic

/-!
# One-variable LP feasibility on the real pointer machine in linear time

A single program of the pointer machine of `Def_SmaleNinth_RealRAM` decides
the feasibility of `aᵢ x ≥ bᵢ (i < m)` on the standard encoding `encodeLP`
within `100 (m+1)` steps.

Architecture.  The program has three phases.  *Initialisation* reads `m` from
cell `0` into a register, sets the constant registers `1` and `0`, clears the
abstract state and points both data pointers at cell `2`.  The *shift loop*
advances the second pointer by `m` cells, so that it sits on `b₀`; this costs
`4m` steps and is the only place where the linear budget is spent on
addressing.  The *main loop* then runs once per constraint: it loads `aᵢ` and
`bᵢ` through the two pointers, increments both pointers, and updates the
abstract state `⟨L, HL, R, HR, BAD⟩` — the running lower bound with its
presence flag, the running upper bound with its presence flag and the
infeasibility flag — by a branch on the sign of `aᵢ`.  Every pass costs at
most `17` steps, independently of `m`: this is exactly what indirect
addressing buys, and it is what the fixed-address tape machine provably
cannot do (`SmaleNinth.bss_one_variable_lp_no_linear_program`).

The abstract layer (`St`, `upd`, `stF`, `verdict`, `Spec`, `verdict_iff`) is
the machine-independent part of the author's proof of
`SmaleNinth.bss_decides_one_variable_lp_quadratic` and is reused verbatim; the
machine layer (`RReaches`, the program, the phase lemmas) is new.
-/

open SmaleNinth Matrix LinearOptimization

namespace SmaleNinth.RAMLP

/-- The abstract state maintained along the constraints. -/
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



/-- The program. -/
noncomputable def rprog : RAMProgram :=
[ .pset 2 0            -- 0   p2 := 0
, .load 12 2           -- 1   m
, .const 10 1          -- 2   one := 1
, .const 11 0          -- 3   zero := 0
, .const 0 0           -- 4   L := 0
, .const 1 0           -- 5   HL := 0
, .const 2 0           -- 6   R := 0
, .const 3 0           -- 7   HR := 0
, .const 4 0           -- 8   BAD := 0
, .add 9 12 11         -- 9   cnt := m
, .pset 0 2            -- 10  pa := 2
, .pset 1 2            -- 11  pb := 2
, .jle 9 16            -- 12  shift loop head
, .pinc 1              -- 13
, .sub 9 9 10          -- 14
, .jle 11 12           -- 15  loop
, .add 9 12 11         -- 16  cnt := m
, .jle 9 42            -- 17  main loop head
, .load 5 0            -- 18  a := mem[pa]
, .load 6 1            -- 19  b := mem[pb]
, .pinc 0              -- 20
, .pinc 1              -- 21
, .sub 9 9 10          -- 22  cnt := cnt - 1
, .div 7 6 5           -- 23  q := b / a
, .jle 5 31            -- 24  a ≤ 0 → notpos
, .jle 1 28            -- 25  HL ≤ 0 → setL
, .sub 8 7 0           -- 26  cmp := q - L
, .jle 8 41            -- 27  q ≤ L → cont
, .const 1 1           -- 28  setL: HL := 1
, .add 0 7 11          -- 29  L := q
, .jle 11 41           -- 30  → cont
, .sub 8 11 5          -- 31  notpos: cmp := -a
, .jle 8 39            -- 32  -a ≤ 0 → zero
, .jle 3 36            -- 33  HR ≤ 0 → setR
, .sub 8 2 7           -- 34  cmp := R - q
, .jle 8 41            -- 35  R ≤ q → cont
, .const 3 1           -- 36  setR: HR := 1
, .add 2 7 11          -- 37  R := q
, .jle 11 41           -- 38  → cont
, .jle 6 41            -- 39  zero: b ≤ 0 → cont
, .const 4 1           -- 40  BAD := 1
, .jle 11 17           -- 41  cont: loop
, .jle 4 44            -- 42  final: BAD ≤ 0 → F1
, .reject              -- 43
, .jle 1 49            -- 44  HL ≤ 0 → accept
, .jle 3 49            -- 45  HR ≤ 0 → accept
, .sub 8 0 2           -- 46  cmp := L - R
, .jle 8 49            -- 47
, .reject              -- 48
, .accept ]            -- 49

/-- The abstract state read off the register file. -/
def regsOf (g : ℕ → ℝ) : St := ⟨g 0, g 1, g 2, g 3, g 4⟩

/-! ### Initialisation: `0 → 12` -/

lemma init_block (x : ℤ → ℝ) (m : ℕ) (hx : x 0 = (m : ℝ)) :
    ∃ (g : ℕ → ℝ) (p : ℕ → ℤ),
      regsOf g = ⟨0, 0, 0, 0, 0⟩ ∧ g 9 = (m : ℝ) ∧ g 10 = 1 ∧ g 11 = 0 ∧ g 12 = (m : ℝ) ∧
      p 0 = 2 ∧ p 1 = 2 ∧
      RReaches rprog ⟨0, fun _ => 0, fun _ => 0, x⟩ ⟨12, g, p, x⟩ 12 := by
  have chain :=
    (r_pset (R := rprog) (pc := 0) rfl (fun _ => (0:ℝ)) (fun _ => (0:ℤ)) x).trans <|
    (r_load (R := rprog) (pc := 1) rfl _ _ _).trans <|
    (r_const (R := rprog) (pc := 2) rfl _ _ _).trans <|
    (r_const (R := rprog) (pc := 3) rfl _ _ _).trans <|
    (r_const (R := rprog) (pc := 4) rfl _ _ _).trans <|
    (r_const (R := rprog) (pc := 5) rfl _ _ _).trans <|
    (r_const (R := rprog) (pc := 6) rfl _ _ _).trans <|
    (r_const (R := rprog) (pc := 7) rfl _ _ _).trans <|
    (r_const (R := rprog) (pc := 8) rfl _ _ _).trans <|
    (r_add (R := rprog) (pc := 9) rfl _ _ _).trans <|
    (r_pset (R := rprog) (pc := 10) rfl _ _ _).trans
    (r_pset (R := rprog) (pc := 11) rfl _ _ _)
  refine ⟨_, _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
  · simp [regsOf, Function.update_apply]
  · simp [Function.update_apply, hx]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply, hx]
  · simp [Function.update_apply]
  · simp [Function.update_apply]

/-! ### The pointer-advance loop `12 → 17` -/

lemma cast_sub_pos {m k : ℕ} (h : k < m) : ¬ (((m - k : ℕ) : ℝ) ≤ 0) := by
  have : 0 < m - k := by omega
  exact not_le.mpr (by exact_mod_cast this)

lemma cast_sub_succ {m k : ℕ} (h : k < m) :
    ((m - k : ℕ) : ℝ) - 1 = ((m - (k + 1) : ℕ) : ℝ) := by
  have e : m - k = (m - (k + 1)) + 1 := by omega
  rw [e]; push_cast; ring

lemma shift_step (x : ℤ → ℝ) (m k : ℕ) (hk : k < m) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (h9 : g 9 = ((m - k : ℕ) : ℝ)) (h10 : g 10 = 1) (h11 : g 11 = 0) :
    ∃ (g' : ℕ → ℝ) (p' : ℕ → ℤ),
      regsOf g' = regsOf g ∧ g' 9 = ((m - (k + 1) : ℕ) : ℝ) ∧ g' 10 = 1 ∧ g' 11 = 0 ∧
      g' 12 = g 12 ∧ p' 0 = p 0 ∧ p' 1 = p 1 + 1 ∧
      RReaches rprog ⟨12, g, p, x⟩ ⟨12, g', p', x⟩ 4 := by
  have chain :=
    (r_jle_pos (R := rprog) (pc := 12) rfl g p x (by rw [h9]; exact cast_sub_pos hk)).trans <|
    (r_pinc (R := rprog) (pc := 13) rfl _ _ _).trans <|
    (r_sub (R := rprog) (pc := 14) rfl _ _ _).trans
    (r_jle_le (R := rprog) (pc := 15) rfl _ _ _ (by simp [Function.update_apply, h11]))
  refine ⟨_, _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
  · simp [regsOf, Function.update_apply]
  · simp [Function.update_apply, h9, h10, cast_sub_succ hk]
  · simp [Function.update_apply, h10]
  · simp [Function.update_apply, h11]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]

lemma shift_loop (x : ℤ → ℝ) (m : ℕ) (g₀ : ℕ → ℝ) (p₀ : ℕ → ℤ)
    (h9 : g₀ 9 = (m : ℝ)) (h10 : g₀ 10 = 1) (h11 : g₀ 11 = 0) :
    ∀ k ≤ m, ∃ (g : ℕ → ℝ) (p : ℕ → ℤ),
      regsOf g = regsOf g₀ ∧ g 9 = ((m - k : ℕ) : ℝ) ∧ g 10 = 1 ∧ g 11 = 0 ∧
      g 12 = g₀ 12 ∧ p 0 = p₀ 0 ∧ p 1 = p₀ 1 + k ∧
      RReaches rprog ⟨12, g₀, p₀, x⟩ ⟨12, g, p, x⟩ (4 * k) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨g₀, p₀, rfl, by simpa using h9, h10, h11, rfl, rfl, by simp,
      by simpa using RReaches.refl rprog _⟩
  | succ k ih =>
    intro hk
    obtain ⟨g, p, hst, h9', h10', h11', h12', hp0, hp1, hreach⟩ := ih (by omega)
    obtain ⟨g', p', hst2, h9'', h10'', h11'', h12'', hp0', hp1', hstep⟩ :=
      shift_step x m k (by omega) g p h9' h10' h11'
    exact ⟨g', p', by rw [hst2, hst], h9'', h10'', h11'', by rw [h12'', h12'], by rw [hp0', hp0],
      by rw [hp1', hp1]; push_cast; ring, (hreach.trans hstep).mono (by omega)⟩

/-- After the shift loop the pointer `1` is at `2 + m` and the counter is reset. -/
lemma shift_block (x : ℤ → ℝ) (m : ℕ) (g₀ : ℕ → ℝ) (p₀ : ℕ → ℤ)
    (h9 : g₀ 9 = (m : ℝ)) (h10 : g₀ 10 = 1) (h11 : g₀ 11 = 0) (h12 : g₀ 12 = (m : ℝ))
    (hp0 : p₀ 0 = 2) (hp1 : p₀ 1 = 2) :
    ∃ (g : ℕ → ℝ) (p : ℕ → ℤ),
      regsOf g = regsOf g₀ ∧ g 9 = (m : ℝ) ∧ g 10 = 1 ∧ g 11 = 0 ∧ g 12 = (m : ℝ) ∧
      p 0 = 2 ∧ p 1 = 2 + (m : ℤ) ∧
      RReaches rprog ⟨12, g₀, p₀, x⟩ ⟨17, g, p, x⟩ (4 * m + 2) := by
  obtain ⟨g, p, hst, h9', h10', h11', h12', hq0, hq1, hreach⟩ :=
    shift_loop x m g₀ p₀ h9 h10 h11 m le_rfl
  have hexit : g 9 ≤ 0 := by rw [h9']; simp
  have chain :=
    (r_jle_le (R := rprog) (pc := 12) rfl g p x hexit).trans
    (r_add (R := rprog) (pc := 16) rfl _ _ _)
  refine ⟨_, _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (hreach.trans chain).mono (by omega)⟩
  · rw [← hst]; simp [regsOf, Function.update_apply]
  · simp [Function.update_apply, h12', h12, h11']
  · simp [Function.update_apply, h10']
  · simp [Function.update_apply, h11']
  · simp [Function.update_apply, h12', h12]
  · simpa [hp0] using hq0
  · rw [hq1, hp1]

/-! ### One pass of the main loop -/

/-- Reading the next constraint: `17 → 24`. -/
lemma prefix_step (x : ℤ → ℝ) (m i : ℕ) (hi : i < m) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (h9 : g 9 = ((m - i : ℕ) : ℝ)) (h10 : g 10 = 1) (h11 : g 11 = 0)
    (hp0 : p 0 = 2 + (i : ℤ)) (hp1 : p 1 = 2 + (m : ℤ) + (i : ℤ)) :
    ∃ (g' : ℕ → ℝ) (p' : ℕ → ℤ),
      regsOf g' = regsOf g ∧
      g' 5 = x (2 + (i : ℤ)) ∧ g' 6 = x (2 + (m : ℤ) + (i : ℤ)) ∧
      g' 7 = x (2 + (m : ℤ) + (i : ℤ)) / x (2 + (i : ℤ)) ∧
      g' 9 = ((m - (i + 1) : ℕ) : ℝ) ∧ g' 10 = 1 ∧ g' 11 = 0 ∧ g' 12 = g 12 ∧
      p' 0 = 2 + (i : ℤ) + 1 ∧ p' 1 = 2 + (m : ℤ) + (i : ℤ) + 1 ∧
      RReaches rprog ⟨17, g, p, x⟩ ⟨24, g', p', x⟩ 7 := by
  have chain :=
    (r_jle_pos (R := rprog) (pc := 17) rfl g p x (by rw [h9]; exact cast_sub_pos hi)).trans <|
    (r_load (R := rprog) (pc := 18) rfl _ _ _).trans <|
    (r_load (R := rprog) (pc := 19) rfl _ _ _).trans <|
    (r_pinc (R := rprog) (pc := 20) rfl _ _ _).trans <|
    (r_pinc (R := rprog) (pc := 21) rfl _ _ _).trans <|
    (r_sub (R := rprog) (pc := 22) rfl _ _ _).trans
    (r_div (R := rprog) (pc := 23) rfl _ _ _)
  refine ⟨_, _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
  · simp [regsOf, Function.update_apply]
  · simp [Function.update_apply, hp0]
  · simp [Function.update_apply, hp1]
  · simp [Function.update_apply, hp0, hp1]
  · simp [Function.update_apply, h9, h10, cast_sub_succ hi]
  · simp [Function.update_apply, h10]
  · simp [Function.update_apply, h11]
  · simp [Function.update_apply]
  · simp [Function.update_apply, hp0]
  · simp [Function.update_apply, hp1]

/-- The update block `24 → 17`: it performs `upd` on the abstract state. -/
lemma upd_block (x : ℤ → ℝ) (a b : ℝ) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (h5 : g 5 = a) (h6 : g 6 = b) (h7 : g 7 = b / a) (h11 : g 11 = 0) :
    ∃ g' : ℕ → ℝ,
      regsOf g' = upd (regsOf g) a b ∧
      g' 9 = g 9 ∧ g' 10 = g 10 ∧ g' 11 = 0 ∧ g' 12 = g 12 ∧
      RReaches rprog ⟨24, g, p, x⟩ ⟨17, g', p, x⟩ 10 := by
  by_cases ha : (0 : ℝ) < a
  · -- `0 < a`: the lower bound may move
    have h24 : ¬ g 5 ≤ 0 := by rw [h5]; exact not_le.mpr ha
    by_cases hhl : g 1 ≤ 0
    · have chain :=
        (r_jle_pos (R := rprog) (pc := 24) rfl g p x h24).trans <|
        (r_jle_le (R := rprog) (pc := 25) rfl _ _ _ hhl).trans <|
        (r_const (R := rprog) (pc := 28) rfl _ _ _).trans <|
        (r_add (R := rprog) (pc := 29) rfl _ _ _).trans <|
        (r_jle_le (R := rprog) (pc := 30) rfl _ _ _ (by simp [Function.update_apply, h11])).trans
        (r_jle_le (R := rprog) (pc := 41) rfl _ _ _ (by simp [Function.update_apply, h11]))
      have hupd : upd (regsOf g) a b = ⟨b / a, 1, g 2, g 3, g 4⟩ := by
        simp [upd, regsOf, ha, hhl]
      refine ⟨_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
      · rw [hupd]; simp [regsOf, Function.update_apply, h7, h11]
      · simp [Function.update_apply]
      · simp [Function.update_apply]
      · simp [Function.update_apply, h11]
      · simp [Function.update_apply]
    · by_cases hcmp : b / a - g 0 ≤ 0
      · have chain :=
          (r_jle_pos (R := rprog) (pc := 24) rfl g p x h24).trans <|
          (r_jle_pos (R := rprog) (pc := 25) rfl _ _ _ hhl).trans <|
          (r_sub (R := rprog) (pc := 26) rfl _ _ _).trans <|
          (r_jle_le (R := rprog) (pc := 27) rfl _ _ _
            (by simp [Function.update_apply, h7]; linarith)).trans
          (r_jle_le (R := rprog) (pc := 41) rfl _ _ _ (by simp [Function.update_apply, h11]))
        have hupd : upd (regsOf g) a b = regsOf g := by
          simp [upd, regsOf, ha, hhl, hcmp]
        refine ⟨_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
        · rw [hupd]; simp [regsOf, Function.update_apply]
        · simp [Function.update_apply]
        · simp [Function.update_apply]
        · simp [Function.update_apply, h11]
        · simp [Function.update_apply]
      · have chain :=
          (r_jle_pos (R := rprog) (pc := 24) rfl g p x h24).trans <|
          (r_jle_pos (R := rprog) (pc := 25) rfl _ _ _ hhl).trans <|
          (r_sub (R := rprog) (pc := 26) rfl _ _ _).trans <|
          (r_jle_pos (R := rprog) (pc := 27) rfl _ _ _
            (by simp [Function.update_apply, h7]; linarith [not_le.mp hcmp])).trans <|
          (r_const (R := rprog) (pc := 28) rfl _ _ _).trans <|
          (r_add (R := rprog) (pc := 29) rfl _ _ _).trans <|
          (r_jle_le (R := rprog) (pc := 30) rfl _ _ _ (by simp [Function.update_apply, h11])).trans
          (r_jle_le (R := rprog) (pc := 41) rfl _ _ _ (by simp [Function.update_apply, h11]))
        have hupd : upd (regsOf g) a b = ⟨b / a, 1, g 2, g 3, g 4⟩ := by
          simp [upd, regsOf, ha, hhl, hcmp]
        refine ⟨_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
        · rw [hupd]; simp [regsOf, Function.update_apply, h7, h11]
        · simp [Function.update_apply]
        · simp [Function.update_apply]
        · simp [Function.update_apply, h11]
        · simp [Function.update_apply]
  · -- `a ≤ 0`
    have h24 : g 5 ≤ 0 := by rw [h5]; exact not_lt.mp ha
    by_cases hneg : (0 : ℝ) < -a
    · -- `a < 0`: the upper bound may move
      have h32 : ¬ (g 11 - g 5 : ℝ) ≤ 0 := by rw [h11, h5]; simpa using not_le.mpr hneg
      by_cases hhr : g 3 ≤ 0
      · have chain :=
          (r_jle_le (R := rprog) (pc := 24) rfl g p x h24).trans <|
          (r_sub (R := rprog) (pc := 31) rfl _ _ _).trans <|
          (r_jle_pos (R := rprog) (pc := 32) rfl _ _ _ (by simpa [Function.update_apply] using h32)).trans <|
          (r_jle_le (R := rprog) (pc := 33) rfl _ _ _ (by simpa [Function.update_apply] using hhr)).trans <|
          (r_const (R := rprog) (pc := 36) rfl _ _ _).trans <|
          (r_add (R := rprog) (pc := 37) rfl _ _ _).trans <|
          (r_jle_le (R := rprog) (pc := 38) rfl _ _ _ (by simp [Function.update_apply, h11])).trans
          (r_jle_le (R := rprog) (pc := 41) rfl _ _ _ (by simp [Function.update_apply, h11]))
        have hupd : upd (regsOf g) a b = ⟨g 0, g 1, b / a, 1, g 4⟩ := by
          simp [upd, regsOf, ha, hneg, hhr]
        refine ⟨_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
        · rw [hupd]; simp [regsOf, Function.update_apply, h7, h11]
        · simp [Function.update_apply]
        · simp [Function.update_apply]
        · simp [Function.update_apply, h11]
        · simp [Function.update_apply]
      · by_cases hcmp : g 2 - b / a ≤ 0
        · have chain :=
            (r_jle_le (R := rprog) (pc := 24) rfl g p x h24).trans <|
            (r_sub (R := rprog) (pc := 31) rfl _ _ _).trans <|
            (r_jle_pos (R := rprog) (pc := 32) rfl _ _ _ (by simpa [Function.update_apply] using h32)).trans <|
            (r_jle_pos (R := rprog) (pc := 33) rfl _ _ _ (by simpa [Function.update_apply] using hhr)).trans <|
            (r_sub (R := rprog) (pc := 34) rfl _ _ _).trans <|
            (r_jle_le (R := rprog) (pc := 35) rfl _ _ _
              (by simp [Function.update_apply, h7]; linarith)).trans
            (r_jle_le (R := rprog) (pc := 41) rfl _ _ _ (by simp [Function.update_apply, h11]))
          have hupd : upd (regsOf g) a b = regsOf g := by
            simp [upd, regsOf, ha, hneg, hhr, hcmp]
          refine ⟨_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
          · rw [hupd]; simp [regsOf, Function.update_apply]
          · simp [Function.update_apply]
          · simp [Function.update_apply]
          · simp [Function.update_apply, h11]
          · simp [Function.update_apply]
        · have chain :=
            (r_jle_le (R := rprog) (pc := 24) rfl g p x h24).trans <|
            (r_sub (R := rprog) (pc := 31) rfl _ _ _).trans <|
            (r_jle_pos (R := rprog) (pc := 32) rfl _ _ _ (by simpa [Function.update_apply] using h32)).trans <|
            (r_jle_pos (R := rprog) (pc := 33) rfl _ _ _ (by simpa [Function.update_apply] using hhr)).trans <|
            (r_sub (R := rprog) (pc := 34) rfl _ _ _).trans <|
            (r_jle_pos (R := rprog) (pc := 35) rfl _ _ _
              (by simp [Function.update_apply, h7]; linarith [not_le.mp hcmp])).trans <|
            (r_const (R := rprog) (pc := 36) rfl _ _ _).trans <|
            (r_add (R := rprog) (pc := 37) rfl _ _ _).trans <|
            (r_jle_le (R := rprog) (pc := 38) rfl _ _ _ (by simp [Function.update_apply, h11])).trans
            (r_jle_le (R := rprog) (pc := 41) rfl _ _ _ (by simp [Function.update_apply, h11]))
          have hupd : upd (regsOf g) a b = ⟨g 0, g 1, b / a, 1, g 4⟩ := by
            simp [upd, regsOf, ha, hneg, hhr, hcmp]
          refine ⟨_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
          · rw [hupd]; simp [regsOf, Function.update_apply, h7, h11]
          · simp [Function.update_apply]
          · simp [Function.update_apply]
          · simp [Function.update_apply, h11]
          · simp [Function.update_apply]
    · -- `a = 0`
      have h32 : (g 11 - g 5 : ℝ) ≤ 0 := by rw [h11, h5]; simpa using not_lt.mp hneg
      by_cases hb : b ≤ 0
      · have chain :=
          (r_jle_le (R := rprog) (pc := 24) rfl g p x h24).trans <|
          (r_sub (R := rprog) (pc := 31) rfl _ _ _).trans <|
          (r_jle_le (R := rprog) (pc := 32) rfl _ _ _ (by simpa [Function.update_apply] using h32)).trans <|
          (r_jle_le (R := rprog) (pc := 39) rfl _ _ _
            (by simp [Function.update_apply, h6]; linarith)).trans
          (r_jle_le (R := rprog) (pc := 41) rfl _ _ _ (by simp [Function.update_apply, h11]))
        have hupd : upd (regsOf g) a b = regsOf g := by
          simp [upd, regsOf, ha, hneg, hb]
        refine ⟨_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
        · rw [hupd]; simp [regsOf, Function.update_apply]
        · simp [Function.update_apply]
        · simp [Function.update_apply]
        · simp [Function.update_apply, h11]
        · simp [Function.update_apply]
      · have chain :=
          (r_jle_le (R := rprog) (pc := 24) rfl g p x h24).trans <|
          (r_sub (R := rprog) (pc := 31) rfl _ _ _).trans <|
          (r_jle_le (R := rprog) (pc := 32) rfl _ _ _ (by simpa [Function.update_apply] using h32)).trans <|
          (r_jle_pos (R := rprog) (pc := 39) rfl _ _ _
            (by simp [Function.update_apply, h6]; exact not_le.mp hb)).trans <|
          (r_const (R := rprog) (pc := 40) rfl _ _ _).trans
          (r_jle_le (R := rprog) (pc := 41) rfl _ _ _ (by simp [Function.update_apply, h11]))
        have hupd : upd (regsOf g) a b = ⟨g 0, g 1, g 2, g 3, 1⟩ := by
          simp [upd, regsOf, ha, hneg, hb]
        refine ⟨_, ?_, ?_, ?_, ?_, ?_, chain.mono (by norm_num)⟩
        · rw [hupd]; simp [regsOf, Function.update_apply]
        · simp [Function.update_apply]
        · simp [Function.update_apply]
        · simp [Function.update_apply, h11]
        · simp [Function.update_apply]

/-- One pass of the main loop: `17 → 17`, performing `upd`. -/
lemma main_step (x : ℤ → ℝ) (m i : ℕ) (hi : i < m) (g : ℕ → ℝ) (p : ℕ → ℤ)
    (h9 : g 9 = ((m - i : ℕ) : ℝ)) (h10 : g 10 = 1) (h11 : g 11 = 0)
    (hp0 : p 0 = 2 + (i : ℤ)) (hp1 : p 1 = 2 + (m : ℤ) + (i : ℤ)) :
    ∃ (g' : ℕ → ℝ) (p' : ℕ → ℤ),
      regsOf g' = upd (regsOf g) (x (2 + (i : ℤ))) (x (2 + (m : ℤ) + (i : ℤ))) ∧
      g' 9 = ((m - (i + 1) : ℕ) : ℝ) ∧ g' 10 = 1 ∧ g' 11 = 0 ∧
      p' 0 = 2 + ((i + 1 : ℕ) : ℤ) ∧ p' 1 = 2 + (m : ℤ) + ((i + 1 : ℕ) : ℤ) ∧
      RReaches rprog ⟨17, g, p, x⟩ ⟨17, g', p', x⟩ 17 := by
  obtain ⟨g₁, p₁, hst, h5, h6, h7, h9', h10', h11', _, hq0, hq1, hreach⟩ :=
    prefix_step x m i hi g p h9 h10 h11 hp0 hp1
  obtain ⟨g₂, hst2, h9'', h10'', h11'', _, hstep⟩ :=
    upd_block x (x (2 + (i : ℤ))) (x (2 + (m : ℤ) + (i : ℤ))) g₁ p₁ h5 h6 h7 h11'
  refine ⟨g₂, p₁, by rw [hst2, hst], by rw [h9'', h9'], by rw [h10'', h10'],
    h11'', ?_, ?_, (hreach.trans hstep).mono (by norm_num)⟩
  · rw [hq0]; push_cast; ring
  · rw [hq1]; push_cast; ring

/-- The whole main loop. -/
lemma main_loop (x : ℤ → ℝ) (m : ℕ) (g₀ : ℕ → ℝ) (p₀ : ℕ → ℤ)
    (hst : regsOf g₀ = ⟨0, 0, 0, 0, 0⟩) (h9 : g₀ 9 = (m : ℝ)) (h10 : g₀ 10 = 1)
    (h11 : g₀ 11 = 0) (hp0 : p₀ 0 = 2) (hp1 : p₀ 1 = 2 + (m : ℤ)) :
    ∀ i ≤ m, ∃ (g : ℕ → ℝ) (p : ℕ → ℤ),
      regsOf g = stF (fun j => x (2 + (j : ℤ))) (fun j => x (2 + (m : ℤ) + (j : ℤ))) i ∧
      g 9 = ((m - i : ℕ) : ℝ) ∧ g 10 = 1 ∧ g 11 = 0 ∧
      p 0 = 2 + (i : ℤ) ∧ p 1 = 2 + (m : ℤ) + (i : ℤ) ∧
      RReaches rprog ⟨17, g₀, p₀, x⟩ ⟨17, g, p, x⟩ (17 * i) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨g₀, p₀, by rw [hst]; rfl, by simpa using h9, h10, h11, by simpa using hp0,
      by simpa using hp1, by simpa using RReaches.refl rprog _⟩
  | succ i ih =>
    intro hi
    obtain ⟨g, p, hstate, h9', h10', h11', hq0, hq1, hreach⟩ := ih (by omega)
    obtain ⟨g', p', hst2, h9'', h10'', h11'', hr0, hr1, hstep⟩ :=
      main_step x m i (by omega) g p h9' h10' h11' hq0 hq1
    refine ⟨g', p', ?_, h9'', h10'', h11'', hr0, hr1, (hreach.trans hstep).mono (by omega)⟩
    rw [hst2, hstate]
    rfl

/-! ### The final decision `17 → halt` -/

lemma final_block (x : ℤ → ℝ) (g : ℕ → ℝ) (p : ℕ → ℤ) (h9 : g 9 ≤ 0) :
    ∃ (pc : ℕ) (g' : ℕ → ℝ) (p' : ℕ → ℤ),
      RReaches rprog ⟨17, g, p, x⟩ ⟨pc, g', p', x⟩ 6 ∧
      rprog[pc]? = some (if verdict (regsOf g) then RAMInstr.accept else RAMInstr.reject) := by
  have s0 := r_jle_le (R := rprog) (pc := 17) rfl g p x h9
  by_cases hbad : g 4 ≤ 0
  · have s1 := s0.trans (r_jle_le (R := rprog) (pc := 42) rfl g p x hbad)
    by_cases hhl : g 1 ≤ 0
    · refine ⟨49, _, _, (s1.trans (r_jle_le (R := rprog) (pc := 44) rfl g p x hhl)).mono
        (by norm_num), ?_⟩
      have : verdict (regsOf g) = true := by simp [verdict, regsOf, hbad, hhl]
      rw [this]; rfl
    · have s2 := s1.trans (r_jle_pos (R := rprog) (pc := 44) rfl g p x hhl)
      by_cases hhr : g 3 ≤ 0
      · refine ⟨49, _, _, (s2.trans (r_jle_le (R := rprog) (pc := 45) rfl g p x hhr)).mono
          (by norm_num), ?_⟩
        have : verdict (regsOf g) = true := by simp [verdict, regsOf, hbad, hhr]
        rw [this]; rfl
      · have s3 := (s2.trans (r_jle_pos (R := rprog) (pc := 45) rfl g p x hhr)).trans
          (r_sub (R := rprog) (pc := 46) rfl g p x)
        by_cases hlr : g 0 - g 2 ≤ 0
        · refine ⟨49, _, _, (s3.trans (r_jle_le (R := rprog) (pc := 47) rfl _ _ _
            (by simp [Function.update_apply]; linarith))).mono (by norm_num), ?_⟩
          have : verdict (regsOf g) = true := by simp [verdict, regsOf, hbad, hlr]
          rw [this]; rfl
        · refine ⟨48, _, _, (s3.trans (r_jle_pos (R := rprog) (pc := 47) rfl _ _ _
            (by simpa [Function.update_apply] using hlr))).mono (by norm_num), ?_⟩
          have hP : ¬ (g 4 ≤ 0 ∧ (g 1 ≤ 0 ∨ g 3 ≤ 0 ∨ g 0 - g 2 ≤ 0)) := by
            rintro ⟨-, (h | h | h)⟩
            exacts [hhl h, hhr h, hlr h]
          have : verdict (regsOf g) = false := by
            simp only [verdict, regsOf]
            exact if_neg hP
          rw [this]; rfl
  · refine ⟨43, _, _, (s0.trans (r_jle_pos (R := rprog) (pc := 42) rfl g p x hbad)).mono
      (by norm_num), ?_⟩
    have : verdict (regsOf g) = false := by simp [verdict, regsOf, hbad]
    rw [this]; rfl

/-! ### The theorem -/

/-- **One-variable LP feasibility on the real pointer machine in linear time.** -/
theorem ram_decides_one_variable_lp_linear :
    ∃ (R : RAMProgram) (C : ℕ),
      ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          RAMDecidesInTime R (encodeLP A b) (C * (m + 1)) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by
  refine ⟨rprog, 100, fun m A b => ?_⟩
  set x := encodeLP A b with hx
  set a' : ℕ → ℝ := fun j => if h : j < m then A ⟨j, h⟩ 0 else 0 with ha'
  set b' : ℕ → ℝ := fun j => if h : j < m then b ⟨j, h⟩ else 0 with hb'
  obtain ⟨g₀, p₀, hst₀, h9₀, h10₀, h11₀, h12₀, hp0₀, hp1₀, hinit⟩ :=
    init_block x m (by rw [hx]; exact encodeLP_zero A b)
  obtain ⟨g₁, p₁, hst₁, h9₁, h10₁, h11₁, h12₁, hq0, hq1, hshift⟩ :=
    shift_block x m g₀ p₀ h9₀ h10₀ h11₀ h12₀ hp0₀ hp1₀
  obtain ⟨g, p, hstate, h9, h10, h11, hr0, hr1, hloop⟩ :=
    main_loop x m g₁ p₁ (by rw [hst₁, hst₀]) h9₁ h10₁ h11₁ hq0 hq1 m le_rfl
  obtain ⟨pc, g', p', hfin, hpc⟩ := final_block x g p (by rw [h9]; simp)
  have hconv : stF (fun j => x (2 + (j : ℤ))) (fun j => x (2 + (m : ℤ) + (j : ℤ))) m
      = stF a' b' m := by
    have key : ∀ i ≤ m, stF (fun j => x (2 + (j : ℤ))) (fun j => x (2 + (m : ℤ) + (j : ℤ))) i
        = stF a' b' i := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
        intro hi
        simp only [stF]
        rw [ih (by omega), ha', hb']
        simp only [dif_pos (show i < m by omega)]
        rw [hx, encodeLP_a A b i (by omega), encodeLP_b A b i (by omega)]
    exact key m le_rfl
  refine ⟨verdict (regsOf g), ?_, ?_⟩
  · have hall := hinit.trans (hshift.trans (hloop.trans hfin))
    exact decides_of_rreaches (hall.mono (by omega)) hpc
  · rw [hstate, hconv, verdict_iff, polyhedron_nonempty_iff]


end SmaleNinth.RAMLP

open Matrix LinearOptimization

theorem solution :
    ∃ (R : RAMProgram) (C : ℕ),
      ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 1) ℝ) (b : Fin m → ℝ),
        ∃ result : Bool,
          RAMDecidesInTime R (encodeLP A b) (C * (m + 1)) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) :=
  SmaleNinth.RAMLP.ram_decides_one_variable_lp_linear

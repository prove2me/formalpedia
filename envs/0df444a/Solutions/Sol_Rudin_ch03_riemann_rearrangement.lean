-- Prove2me | solution 1 for Rudin.ch03_riemann_rearrangement
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-13T16:32:22.701588+00:00
-- url     : https://prove2.me/submissions/0730a43f-e1fc-4639-924f-6ce749decd5e

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology


/-!
# The greedy rearrangement machine

This file contains the combinatorial/analytic core of Riemann's rearrangement theorem
(Rudin, *Principles of Mathematical Analysis*, Theorem 3.54), in an abstract form.

We are given the partial sums `Pp` of a divergent series of nonnegative terms (the positive
part of a conditionally convergent series), the partial sums `Qp` of a second such series,
and two real sequences `al t < be t` (approximating the prescribed `liminf` and `limsup`).

The algorithm runs in blocks.  In block `t` it first consumes positive terms until the running
sum exceeds `be t`, then negative terms until the running sum drops below `al t`; then block
`t+1` starts.  Each phase consumes at least one term (the tests are performed *after* the term
has been added), so both series are exhausted.

The main results are `Setup.tendsto_I_atTop`, `Setup.tendsto_J_atTop` (both index counters go
to infinity, which makes the associated rearrangement a bijection) and
`Setup.limsup_sval`, `Setup.liminf_sval` (the running sums have the prescribed upper and
lower limits).
-/

open Filter Topology

namespace Rudin.Rearrange

/-- A state of the greedy rearrangement algorithm: `i` positive terms and `j` negative terms
have been consumed, we are in block `blk`, and `takingPos` records the current phase. -/
structure RState where
  i : ℕ
  j : ℕ
  blk : ℕ
  takingPos : Bool

/-- The data driving the greedy construction. -/
structure Setup where
  /-- partial sums of the nonnegative terms -/
  Pp : ℕ → ℝ
  /-- partial sums of the (negated) negative terms -/
  Qp : ℕ → ℝ
  /-- lower targets -/
  al : ℕ → ℝ
  /-- upper targets -/
  be : ℕ → ℝ
  monoP : Monotone Pp
  monoQ : Monotone Qp
  tendP : Tendsto Pp atTop atTop
  tendQ : Tendsto Qp atTop atTop
  dP : Tendsto (fun k => Pp (k + 1) - Pp k) atTop (nhds 0)
  dQ : Tendsto (fun k => Qp (k + 1) - Qp k) atTop (nhds 0)
  ltab : ∀ t, al t < be t

namespace Setup

variable (S : Setup)

/-- The running sum attached to a state. -/
noncomputable def value (s : RState) : ℝ := S.Pp s.i - S.Qp s.j

open Classical in
/-- One step of the algorithm: consume one term, then decide the phase of the next step. -/
noncomputable def step (s : RState) : RState :=
  if s.takingPos then
    { i := s.i + 1, j := s.j, blk := s.blk,
      takingPos := if S.Pp (s.i + 1) - S.Qp s.j ≤ S.be s.blk then true else false }
  else if S.Pp s.i - S.Qp (s.j + 1) < S.al s.blk then
    { i := s.i, j := s.j + 1, blk := s.blk + 1, takingPos := true }
  else
    { i := s.i, j := s.j + 1, blk := s.blk, takingPos := false }

/-- The state after `n` steps. -/
noncomputable def st (n : ℕ) : RState := S.step^[n] ⟨0, 0, 0, true⟩

/-- Number of nonnegative terms consumed after `n` steps. -/
noncomputable def I (n : ℕ) : ℕ := (S.st n).i

/-- Number of negative terms consumed after `n` steps. -/
noncomputable def J (n : ℕ) : ℕ := (S.st n).j

/-- The block index after `n` steps. -/
noncomputable def blk (n : ℕ) : ℕ := (S.st n).blk

/-- The running sum after `n` steps. -/
noncomputable def sval (n : ℕ) : ℝ := S.value (S.st n)

@[simp] lemma st_zero : S.st 0 = ⟨0, 0, 0, true⟩ := rfl

lemma st_succ (n : ℕ) : S.st (n + 1) = S.step (S.st n) := by
  simp [st, Function.iterate_succ_apply']

@[simp] lemma I_zero : S.I 0 = 0 := rfl
@[simp] lemma J_zero : S.J 0 = 0 := rfl
@[simp] lemma blk_zero : S.blk 0 = 0 := rfl
@[simp] lemma takingPos_zero : (S.st 0).takingPos = true := rfl

lemma sval_eq (n : ℕ) : S.sval n = S.Pp (S.I n) - S.Qp (S.J n) := rfl

section PosStep

variable {S} {n : ℕ}

lemma I_succ_pos (h : (S.st n).takingPos = true) : S.I (n + 1) = S.I n + 1 := by
  simp [I, st_succ, step, h]

lemma J_succ_pos (h : (S.st n).takingPos = true) : S.J (n + 1) = S.J n := by
  simp [J, st_succ, step, h]

lemma blk_succ_pos (h : (S.st n).takingPos = true) : S.blk (n + 1) = S.blk n := by
  simp [blk, st_succ, step, h]

lemma sval_succ_pos (h : (S.st n).takingPos = true) :
    S.sval (n + 1) = S.Pp (S.I n + 1) - S.Qp (S.J n) := by
  rw [sval_eq, I_succ_pos h, J_succ_pos h]

lemma takingPos_succ_pos (h : (S.st n).takingPos = true) :
    (S.st (n + 1)).takingPos = true ↔ S.sval (n + 1) ≤ S.be (S.blk n) := by
  rw [sval_succ_pos h]
  classical
  simp only [st_succ, step, h, if_true]
  by_cases hc : S.Pp ((S.st n).i + 1) - S.Qp (S.st n).j ≤ S.be (S.st n).blk <;>
    simp [hc, I, J, blk]

end PosStep

section NegStep

variable {S} {n : ℕ}

lemma I_succ_neg (h : (S.st n).takingPos = false) : S.I (n + 1) = S.I n := by
  classical
  simp only [I, st_succ, step, h, Bool.false_eq_true, if_false]
  split <;> rfl

lemma J_succ_neg (h : (S.st n).takingPos = false) : S.J (n + 1) = S.J n + 1 := by
  classical
  simp only [J, st_succ, step, h, Bool.false_eq_true, if_false]
  split <;> rfl

lemma sval_succ_neg (h : (S.st n).takingPos = false) :
    S.sval (n + 1) = S.Pp (S.I n) - S.Qp (S.J n + 1) := by
  rw [sval_eq, I_succ_neg h, J_succ_neg h]

lemma takingPos_succ_neg (h : (S.st n).takingPos = false) :
    (S.st (n + 1)).takingPos = true ↔ S.sval (n + 1) < S.al (S.blk n) := by
  rw [sval_succ_neg h]
  classical
  simp only [st_succ, step, h, Bool.false_eq_true, if_false]
  by_cases hc : S.Pp (S.st n).i - S.Qp ((S.st n).j + 1) < S.al (S.st n).blk <;>
    simp [hc, I, J, blk]

lemma blk_succ_neg (h : (S.st n).takingPos = false) :
    S.blk (n + 1) = S.blk n + (if S.sval (n + 1) < S.al (S.blk n) then 1 else 0) := by
  rw [sval_succ_neg h]
  classical
  simp only [blk, st_succ, step, h, Bool.false_eq_true, if_false]
  by_cases hc : S.Pp (S.st n).i - S.Qp ((S.st n).j + 1) < S.al (S.st n).blk <;>
    simp [hc, I, J]

end NegStep

variable {S}

lemma takingPos_cases (S' : Setup) (n : ℕ) :
    (S'.st n).takingPos = false ∨ (S'.st n).takingPos = true := by
  cases h : (S'.st n).takingPos <;> simp

/-- Each step consumes exactly one term. -/
lemma I_add_J (n : ℕ) : S.I n + S.J n = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases takingPos_cases S n with h | h
    · rw [I_succ_neg h, J_succ_neg h]; omega
    · rw [I_succ_pos h, J_succ_pos h]; omega

lemma I_le_I_succ (n : ℕ) : S.I n ≤ S.I (n + 1) := by
  rcases takingPos_cases S n with h | h
  · rw [I_succ_neg h]
  · rw [I_succ_pos h]; omega

lemma J_le_J_succ (n : ℕ) : S.J n ≤ S.J (n + 1) := by
  rcases takingPos_cases S n with h | h
  · rw [J_succ_neg h]; omega
  · rw [J_succ_pos h]

lemma monotone_I : Monotone S.I := monotone_nat_of_le_succ I_le_I_succ

lemma monotone_J : Monotone S.J := monotone_nat_of_le_succ J_le_J_succ

lemma blk_le_blk_succ (n : ℕ) : S.blk n ≤ S.blk (n + 1) := by
  rcases takingPos_cases S n with h | h
  · rw [blk_succ_neg h]; split <;> omega
  · rw [blk_succ_pos h]

lemma monotone_blk : Monotone S.blk := monotone_nat_of_le_succ blk_le_blk_succ

lemma I_succ_le (n : ℕ) : S.I (n + 1) ≤ S.I n + 1 := by
  rcases takingPos_cases S n with h | h
  · rw [I_succ_neg h]; omega
  · rw [I_succ_pos h]

lemma J_succ_le (n : ℕ) : S.J (n + 1) ≤ S.J n + 1 := by
  rcases takingPos_cases S n with h | h
  · rw [J_succ_neg h]
  · rw [J_succ_pos h]; omega

lemma blk_succ_le (n : ℕ) : S.blk (n + 1) ≤ S.blk n + 1 := by
  rcases takingPos_cases S n with h | h
  · rw [blk_succ_neg h]; split <;> omega
  · rw [blk_succ_pos h]; omega

/-- The running sum increases along a positive step. -/
lemma sval_le_sval_succ_pos {n : ℕ} (h : (S.st n).takingPos = true) :
    S.sval n ≤ S.sval (n + 1) := by
  rw [sval_succ_pos h, sval_eq]
  have := S.monoP (Nat.le_succ (S.I n))
  linarith

/-- The running sum decreases along a negative step. -/
lemma sval_succ_le_sval_neg {n : ℕ} (h : (S.st n).takingPos = false) :
    S.sval (n + 1) ≤ S.sval n := by
  rw [sval_succ_neg h, sval_eq]
  have := S.monoQ (Nat.le_succ (S.J n))
  linarith

/-! ### Both counters tend to infinity -/

/-- A general "first switch" lemma: if `P` fails at `m` but holds somewhere later, then
somewhere at or after `m` it switches from false to true. -/
lemma exists_switch {P : ℕ → Prop} [DecidablePred P] {m : ℕ} (hm : ¬ P m)
    (hex : ∃ k, m < k ∧ P k) : ∃ j, m ≤ j ∧ ¬ P j ∧ P (j + 1) := by
  have hex' : ∃ d, P (m + 1 + d) := by
    obtain ⟨k, hmk, hPk⟩ := hex
    exact ⟨k - (m + 1), by rwa [show m + 1 + (k - (m + 1)) = k by omega]⟩
  set d := Nat.find hex' with hd
  refine ⟨m + d, by omega, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, add_zero]; exact hm
    · have hlt : d - 1 < d := by omega
      have := Nat.find_min hex' (m := d - 1) (by omega)
      rwa [show m + 1 + (d - 1) = m + d by omega] at this
  · have := Nat.find_spec hex'
    rwa [show m + 1 + d = m + d + 1 by omega] at this

/-- Positive steps occur arbitrarily late: otherwise `Qp` would be bounded. -/
lemma exists_pos_step (N : ℕ) : ∃ n, N ≤ n ∧ (S.st n).takingPos = true := by
  by_contra hcon
  push_neg at hcon
  have hneg : ∀ n, N ≤ n → (S.st n).takingPos = false := by
    intro n hn
    rcases takingPos_cases S n with h | h
    · exact h
    · exact absurd h (hcon n hn)
  have hstep : ∀ n, N ≤ n → ¬ (S.sval (n + 1) < S.al (S.blk n)) := by
    intro n hn hlt
    have h1 : (S.st (n + 1)).takingPos = true := (takingPos_succ_neg (hneg n hn)).2 hlt
    rw [hneg (n + 1) (by omega)] at h1
    exact Bool.false_ne_true h1
  have hI : ∀ n, N ≤ n → S.I n = S.I N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [I_succ_neg (hneg m hm), ih]
  have hblk : ∀ n, N ≤ n → S.blk n = S.blk N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [blk_succ_neg (hneg m hm), if_neg (hstep m hm), add_zero, ih]
  have hJ : ∀ k, S.J (N + k) = S.J N + k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show N + (k + 1) = (N + k) + 1 by omega, J_succ_neg (hneg (N + k) (by omega)), ih]
      omega
  set M := S.Pp (S.I N) - S.al (S.blk N) with hM
  have hQb : ∀ j, S.Qp j ≤ M := by
    intro j
    have h1 := hstep (N + j) (by omega)
    rw [not_lt, sval_succ_neg (hneg (N + j) (by omega)), hI (N + j) (by omega),
      hblk (N + j) (by omega)] at h1
    have h2 : j ≤ S.J (N + j) + 1 := by rw [hJ j]; omega
    calc S.Qp j ≤ S.Qp (S.J (N + j) + 1) := S.monoQ h2
      _ ≤ M := by rw [hM]; linarith
  obtain ⟨j, hj⟩ := (S.tendQ.eventually_ge_atTop (M + 1)).exists
  linarith [hQb j]

/-- Negative steps occur arbitrarily late: otherwise `Pp` would be bounded. -/
lemma exists_neg_step (N : ℕ) : ∃ n, N ≤ n ∧ (S.st n).takingPos = false := by
  by_contra hcon
  push_neg at hcon
  have hpos : ∀ n, N ≤ n → (S.st n).takingPos = true := by
    intro n hn
    rcases takingPos_cases S n with h | h
    · exact absurd h (hcon n hn)
    · exact h
  have hstep : ∀ n, N ≤ n → S.sval (n + 1) ≤ S.be (S.blk n) := by
    intro n hn
    exact (takingPos_succ_pos (hpos n hn)).1 (hpos (n + 1) (by omega))
  have hJ : ∀ n, N ≤ n → S.J n = S.J N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [J_succ_pos (hpos m hm), ih]
  have hblk : ∀ n, N ≤ n → S.blk n = S.blk N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [blk_succ_pos (hpos m hm), ih]
  have hI : ∀ k, S.I (N + k) = S.I N + k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show N + (k + 1) = (N + k) + 1 by omega, I_succ_pos (hpos (N + k) (by omega)), ih]
      omega
  set M := S.be (S.blk N) + S.Qp (S.J N) with hM
  have hPb : ∀ i, S.Pp i ≤ M := by
    intro i
    have h1 := hstep (N + i) (by omega)
    rw [sval_succ_pos (hpos (N + i) (by omega)), hJ (N + i) (by omega),
      hblk (N + i) (by omega)] at h1
    have h2 : i ≤ S.I (N + i) + 1 := by rw [hI i]; omega
    calc S.Pp i ≤ S.Pp (S.I (N + i) + 1) := S.monoP h2
      _ ≤ M := by rw [hM]; linarith
  obtain ⟨i, hi⟩ := (S.tendP.eventually_ge_atTop (M + 1)).exists
  linarith [hPb i]

lemma tendsto_I_atTop : Tendsto S.I atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone monotone_I ?_
  intro i
  induction i with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm, hpos⟩ := exists_pos_step (S := S) n
    refine ⟨m + 1, ?_⟩
    have h1 : S.I n ≤ S.I m := monotone_I hm
    rw [I_succ_pos hpos]
    omega

lemma tendsto_J_atTop : Tendsto S.J atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone monotone_J ?_
  intro j
  induction j with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm, hneg⟩ := exists_neg_step (S := S) n
    refine ⟨m + 1, ?_⟩
    have h1 : S.J n ≤ S.J m := monotone_J hm
    rw [J_succ_neg hneg]
    omega

/-- A block boundary (a negative step immediately followed by a positive step) occurs
arbitrarily late. -/
lemma exists_neg_to_pos (N : ℕ) :
    ∃ n, N ≤ n ∧ (S.st n).takingPos = false ∧ (S.st (n + 1)).takingPos = true := by
  classical
  obtain ⟨m, hm, hmneg⟩ := exists_neg_step (S := S) N
  obtain ⟨p, hp, hppos⟩ := exists_pos_step (S := S) (m + 1)
  have hmP : ¬ ((S.st m).takingPos = true) := by rw [hmneg]; simp
  obtain ⟨j, hj1, hj2, hj3⟩ :=
    exists_switch (P := fun n => (S.st n).takingPos = true) hmP ⟨p, by omega, hppos⟩
  refine ⟨j, by omega, ?_, hj3⟩
  rcases takingPos_cases S j with h | h
  · exact h
  · exact absurd h hj2

/-- The end of a positive phase (a positive step immediately followed by a negative step)
occurs arbitrarily late. -/
lemma exists_pos_to_neg (N : ℕ) :
    ∃ n, N ≤ n ∧ (S.st n).takingPos = true ∧ (S.st (n + 1)).takingPos = false := by
  classical
  obtain ⟨m, hm, hmpos⟩ := exists_pos_step (S := S) N
  obtain ⟨p, hp, hpneg⟩ := exists_neg_step (S := S) (m + 1)
  have hmP : ¬ ((S.st m).takingPos = false) := by rw [hmpos]; simp
  obtain ⟨j, hj1, hj2, hj3⟩ :=
    exists_switch (P := fun n => (S.st n).takingPos = false) hmP ⟨p, by omega, hpneg⟩
  refine ⟨j, by omega, ?_, hj3⟩
  rcases takingPos_cases S j with h | h
  · exact absurd h hj2
  · exact h

/-! ### The block counter tends to infinity -/

lemma tendsto_blk_atTop : Tendsto S.blk atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone monotone_blk ?_
  intro t
  induction t with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm, hneg, hpos⟩ := exists_neg_to_pos (S := S) n
    refine ⟨m + 1, ?_⟩
    have h1 : S.blk n ≤ S.blk m := monotone_blk hm
    have h2 : S.blk (m + 1) = S.blk m + 1 := by
      rw [blk_succ_neg hneg, if_pos ((takingPos_succ_neg hneg).1 hpos)]
    omega

/-! ### Limit behaviour of the running sums -/

/-- At the end of a block's positive phase the running sum exceeds the upper target. -/
lemma exists_overshoot (N T : ℕ) :
    ∃ n ≥ N, T ≤ S.blk n ∧ S.be (S.blk n) < S.sval (n + 1) := by
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 ((tendsto_atTop.1 (tendsto_blk_atTop (S := S))) T)
  obtain ⟨n, hn, hpos, hnegsucc⟩ := exists_pos_to_neg (S := S) (max N N₂)
  refine ⟨n, le_trans (le_max_left _ _) hn, hN₂ n (le_trans (le_max_right _ _) hn), ?_⟩
  have hnot : ¬ (S.sval (n + 1) ≤ S.be (S.blk n)) := by
    intro h
    have := (takingPos_succ_pos hpos).2 h
    rw [hnegsucc] at this
    exact Bool.false_ne_true this
  exact not_le.1 hnot

/-- At the end of a block's negative phase the running sum is below the lower target. -/
lemma exists_undershoot (N T : ℕ) :
    ∃ n ≥ N, T ≤ S.blk n ∧ S.sval (n + 1) < S.al (S.blk n) := by
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 ((tendsto_atTop.1 (tendsto_blk_atTop (S := S))) T)
  obtain ⟨n, hn, hneg, hpossucc⟩ := exists_neg_to_pos (S := S) (max N N₂)
  exact ⟨n, le_trans (le_max_left _ _) hn, hN₂ n (le_trans (le_max_right _ _) hn),
    (takingPos_succ_neg hneg).1 hpossucc⟩

/-- Eventual upper bound: if the upper targets are eventually `≤ C` and the positive
increments are eventually `≤ ε`, then the running sums are eventually `≤ C + ε`. -/
lemma eventually_sval_le {C ε : ℝ} (hε : 0 < ε)
    (hbe : ∀ᶠ t in atTop, S.be t ≤ C) (hP : ∀ᶠ k in atTop, S.Pp (k + 1) - S.Pp k ≤ ε) :
    ∀ᶠ n in atTop, S.sval n ≤ C + ε := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 hbe
  obtain ⟨K, hK⟩ := eventually_atTop.1 hP
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((tendsto_atTop.1 (tendsto_I_atTop (S := S))) K)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 ((tendsto_atTop.1 (tendsto_blk_atTop (S := S))) T)
  obtain ⟨n₀, hn₀, hn₀neg, hn₀pos⟩ := exists_neg_to_pos (S := S) (max N₁ N₂)
  have hbase : S.sval (n₀ + 1) ≤ C := by
    have h1 : S.sval (n₀ + 1) < S.al (S.blk n₀) := (takingPos_succ_neg hn₀neg).1 hn₀pos
    have h2 : S.al (S.blk n₀) < S.be (S.blk n₀) := S.ltab _
    have h3 : S.be (S.blk n₀) ≤ C := hT _ (hN₂ n₀ (le_trans (le_max_right _ _) hn₀))
    linarith
  have key : ∀ m, n₀ + 1 ≤ m →
      ((S.st m).takingPos = true → S.sval m ≤ C) ∧
      ((S.st m).takingPos = false → S.sval m ≤ C + ε) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact ⟨fun _ => hbase, fun _ => by linarith⟩
    | succ m hm ih =>
      have hmN₁' : N₁ ≤ m := le_trans (le_trans (le_max_left _ _) hn₀) (by omega)
      have hmN₂' : N₂ ≤ m := le_trans (le_trans (le_max_right _ _) hn₀) (by omega)
      have hbeC : S.be (S.blk m) ≤ C := hT _ (hN₂ m hmN₂')
      have halC : S.al (S.blk m) ≤ C := le_of_lt (lt_of_lt_of_le (S.ltab _) hbeC)
      rcases takingPos_cases S m with h | h
      · have h1 : S.sval m ≤ C + ε := ih.2 h
        have h2 : S.sval (m + 1) ≤ S.sval m := sval_succ_le_sval_neg h
        refine ⟨fun hp => ?_, fun _ => by linarith⟩
        have h3 := (takingPos_succ_neg h).1 hp
        linarith
      · have h1 : S.sval m ≤ C := ih.1 h
        have hIK : K ≤ S.I m := hN₁ m hmN₁'
        have h2 : S.sval (m + 1) = S.sval m + (S.Pp (S.I m + 1) - S.Pp (S.I m)) := by
          rw [sval_succ_pos h, sval_eq]; ring
        have h3 : S.Pp (S.I m + 1) - S.Pp (S.I m) ≤ ε := hK _ hIK
        refine ⟨fun hp => ?_, fun _ => by linarith⟩
        have h4 := (takingPos_succ_pos h).1 hp
        linarith
  filter_upwards [eventually_ge_atTop (n₀ + 1)] with m hm
  rcases takingPos_cases S m with h | h
  · exact (key m hm).2 h
  · linarith [(key m hm).1 h]

/-- Eventual lower bound, dual to `Setup.eventually_sval_le`. -/
lemma eventually_le_sval {D ε : ℝ} (hε : 0 < ε)
    (hal : ∀ᶠ t in atTop, D ≤ S.al t) (hQ : ∀ᶠ k in atTop, S.Qp (k + 1) - S.Qp k ≤ ε) :
    ∀ᶠ n in atTop, D - ε ≤ S.sval n := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 hal
  obtain ⟨K, hK⟩ := eventually_atTop.1 hQ
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((tendsto_atTop.1 (tendsto_J_atTop (S := S))) K)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 ((tendsto_atTop.1 (tendsto_blk_atTop (S := S))) T)
  obtain ⟨n₀, hn₀, hn₀pos, hn₀neg⟩ := exists_pos_to_neg (S := S) (max N₁ N₂)
  have hbase : D ≤ S.sval (n₀ + 1) := by
    have hnot : ¬ (S.sval (n₀ + 1) ≤ S.be (S.blk n₀)) := by
      intro h
      have := (takingPos_succ_pos hn₀pos).2 h
      rw [hn₀neg] at this
      exact Bool.false_ne_true this
    have h1 : S.be (S.blk n₀) < S.sval (n₀ + 1) := not_le.1 hnot
    have h2 : S.al (S.blk n₀) < S.be (S.blk n₀) := S.ltab _
    have h3 : D ≤ S.al (S.blk n₀) := hT _ (hN₂ n₀ (le_trans (le_max_right _ _) hn₀))
    linarith
  have key : ∀ m, n₀ + 1 ≤ m →
      ((S.st m).takingPos = false → D ≤ S.sval m) ∧
      ((S.st m).takingPos = true → D - ε ≤ S.sval m) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact ⟨fun _ => hbase, fun _ => by linarith⟩
    | succ m hm ih =>
      have hmN₁' : N₁ ≤ m := le_trans (le_trans (le_max_left _ _) hn₀) (by omega)
      have hmN₂' : N₂ ≤ m := le_trans (le_trans (le_max_right _ _) hn₀) (by omega)
      have hDal : D ≤ S.al (S.blk m) := hT _ (hN₂ m hmN₂')
      have hDbe : D ≤ S.be (S.blk m) := le_of_lt (lt_of_le_of_lt hDal (S.ltab _))
      rcases takingPos_cases S m with h | h
      · have h1 : D ≤ S.sval m := ih.1 h
        have hJK : K ≤ S.J m := hN₁ m hmN₁'
        have h2 : S.sval (m + 1) = S.sval m - (S.Qp (S.J m + 1) - S.Qp (S.J m)) := by
          rw [sval_succ_neg h, sval_eq]; ring
        have h3 : S.Qp (S.J m + 1) - S.Qp (S.J m) ≤ ε := hK _ hJK
        refine ⟨fun hp => ?_, fun _ => by linarith⟩
        have hnot : ¬ (S.sval (m + 1) < S.al (S.blk m)) := by
          intro hlt
          have := (takingPos_succ_neg h).2 hlt
          rw [hp] at this
          exact Bool.false_ne_true this
        have h4 := not_lt.1 hnot
        linarith
      · have h1 : D - ε ≤ S.sval m := ih.2 h
        have h2 : S.sval m ≤ S.sval (m + 1) := sval_le_sval_succ_pos h
        refine ⟨fun hp => ?_, fun _ => by linarith⟩
        have hnot : ¬ (S.sval (m + 1) ≤ S.be (S.blk m)) := by
          intro hle
          have := (takingPos_succ_pos h).2 hle
          rw [hp] at this
          exact Bool.false_ne_true this
        have h4 := not_le.1 hnot
        linarith
  filter_upwards [eventually_ge_atTop (n₀ + 1)] with m hm
  rcases takingPos_cases S m with h | h
  · linarith [(key m hm).1 h]
  · exact (key m hm).2 h

variable {α β : EReal}

theorem limsup_sval (hbe : Tendsto (fun t => ((S.be t : ℝ) : EReal)) atTop (nhds β)) :
    limsup (fun n => ((S.sval n : ℝ) : EReal)) atTop = β := by
  refine le_antisymm ?_ ?_
  · refine EReal.le_of_forall_lt_iff_le.1 ?_
    intro z hz
    obtain ⟨C, hβC, hCz⟩ := EReal.exists_between_coe_real hz
    set ε := (z - C) / 2 with hεdef
    have hCzR : C < z := by exact_mod_cast hCz
    have hε : 0 < ε := by rw [hεdef]; linarith
    have hbeC : ∀ᶠ t in atTop, S.be t ≤ C := by
      have := hbe.eventually_lt_const hβC
      filter_upwards [this] with t ht
      exact le_of_lt (by exact_mod_cast ht)
    have hPε : ∀ᶠ k in atTop, S.Pp (k + 1) - S.Pp k ≤ ε := by
      have := S.dP.eventually_lt_const hε
      filter_upwards [this] with k hk
      exact le_of_lt hk
    have hev := eventually_sval_le (S := S) hε hbeC hPε
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [hev] with n hn
    have : S.sval n ≤ z := by rw [hεdef] at hn; linarith
    exact_mod_cast this
  · refine EReal.ge_of_forall_gt_iff_ge.1 ?_
    intro z hz
    obtain ⟨T, hT⟩ := eventually_atTop.1 (hbe.eventually_const_lt hz)
    refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
    refine frequently_atTop.2 fun N => ?_
    obtain ⟨n, hn, hblkT, hover⟩ := exists_overshoot (S := S) N T
    refine ⟨n + 1, by omega, ?_⟩
    have h1 : (z : EReal) < ((S.be (S.blk n) : ℝ) : EReal) := hT _ hblkT
    have h2 : z < S.be (S.blk n) := by exact_mod_cast h1
    have : z ≤ S.sval (n + 1) := by linarith
    exact_mod_cast this

theorem liminf_sval (hal : Tendsto (fun t => ((S.al t : ℝ) : EReal)) atTop (nhds α)) :
    liminf (fun n => ((S.sval n : ℝ) : EReal)) atTop = α := by
  refine le_antisymm ?_ ?_
  · refine EReal.le_of_forall_lt_iff_le.1 ?_
    intro z hz
    obtain ⟨T, hT⟩ := eventually_atTop.1 (hal.eventually_lt_const hz)
    refine liminf_le_of_frequently_le ?_ (by isBoundedDefault)
    refine frequently_atTop.2 fun N => ?_
    obtain ⟨n, hn, hblkT, hunder⟩ := exists_undershoot (S := S) N T
    refine ⟨n + 1, by omega, ?_⟩
    have h1 : ((S.al (S.blk n) : ℝ) : EReal) < (z : EReal) := hT _ hblkT
    have h2 : S.al (S.blk n) < z := by exact_mod_cast h1
    have : S.sval (n + 1) ≤ z := by linarith
    exact_mod_cast this
  · refine EReal.ge_of_forall_gt_iff_ge.1 ?_
    intro z hz
    obtain ⟨D, hzD, hDα⟩ := EReal.exists_between_coe_real hz
    set ε := (D - z) / 2 with hεdef
    have hzDR : z < D := by exact_mod_cast hzD
    have hε : 0 < ε := by rw [hεdef]; linarith
    have halD : ∀ᶠ t in atTop, D ≤ S.al t := by
      have := hal.eventually_const_lt hDα
      filter_upwards [this] with t ht
      exact le_of_lt (by exact_mod_cast ht)
    have hQε : ∀ᶠ k in atTop, S.Qp (k + 1) - S.Qp k ≤ ε := by
      have := S.dQ.eventually_lt_const hε
      filter_upwards [this] with k hk
      exact le_of_lt hk
    have hev := eventually_le_sval (S := S) hε halD hQε
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hev] with n hn
    have : z ≤ S.sval n := by rw [hεdef] at hn; linarith
    exact_mod_cast this

end Setup

end Rudin.Rearrange


/-!
# Real approximating sequences for a pair of extended reals

Given `α ≤ β` in `EReal` we produce real sequences `al t < be t` with `al t → α` and
`be t → β`.  These are the targets steering the greedy rearrangement.
-/

open Filter Topology

namespace Rudin.Rearrange

/-- `clampR x t` is the real number obtained by truncating `x : EReal` to `[-t, t]`. -/
noncomputable def clampR (x : EReal) (t : ℕ) : ℝ :=
  (max (min x (((t : ℝ) : EReal))) ((-(t : ℝ) : ℝ) : EReal)).toReal

lemma clampR_top (t : ℕ) : clampR ⊤ t = t := by
  have h : ((-(t : ℝ) : ℝ) : EReal) ≤ (((t : ℝ)) : EReal) := by
    rw [EReal.coe_le_coe_iff]
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith
  rw [clampR, min_eq_right le_top, max_eq_left h, EReal.toReal_coe]

lemma clampR_bot (t : ℕ) : clampR ⊥ t = -(t : ℝ) := by
  rw [clampR, min_eq_left bot_le, max_eq_right bot_le, EReal.toReal_coe]

lemma clampR_coe_of_le {r : ℝ} {t : ℕ} (h : |r| ≤ t) : clampR (r : EReal) t = r := by
  have h2 : r ≤ (t : ℝ) := le_trans (le_abs_self r) h
  have h3 : -(t : ℝ) ≤ r := by have := neg_abs_le r; linarith
  have e1 : min ((r : ℝ) : EReal) (((t : ℝ) : EReal)) = ((r : ℝ) : EReal) :=
    min_eq_left (by rwa [EReal.coe_le_coe_iff])
  rw [clampR, e1, max_eq_left (by rwa [EReal.coe_le_coe_iff]), EReal.toReal_coe]

lemma coe_clampR (x : EReal) (t : ℕ) :
    ((clampR x t : ℝ) : EReal) = max (min x (((t : ℝ) : EReal))) ((-(t : ℝ) : ℝ) : EReal) := by
  refine EReal.coe_toReal ?_ ?_
  · refine ne_top_of_le_ne_top (EReal.coe_ne_top ((t : ℝ))) (max_le (min_le_right _ _) ?_)
    rw [EReal.coe_le_coe_iff]
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith
  · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-(t : ℝ))) (le_max_right _ _)

lemma clampR_mono {x y : EReal} (h : x ≤ y) (t : ℕ) : clampR x t ≤ clampR y t := by
  rw [← EReal.coe_le_coe_iff, coe_clampR, coe_clampR]
  exact max_le_max (min_le_min h le_rfl) le_rfl

lemma tendsto_clampR_add_of (x : EReal) (c : ℕ → ℝ) (hc : Tendsto c atTop (nhds 0)) :
    Tendsto (fun t : ℕ => ((clampR x t + c t : ℝ) : EReal)) atTop (nhds x) := by
  have hc1 : ∀ᶠ t in atTop, |c t| ≤ 1 := by
    have := hc.eventually (eventually_abs_sub_lt (0 : ℝ) one_pos)
    simp only [sub_zero] at this
    exact this.mono fun t h => h.le
  induction x using EReal.rec with
  | bot =>
    rw [EReal.tendsto_nhds_bot_iff_real]
    intro r
    filter_upwards [hc1, eventually_ge_atTop (Nat.ceil (|r| + 2))] with t ht htr
    have h1 : |r| + 2 ≤ (t : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast htr)
    have h2 : -|r| ≤ r := neg_abs_le r
    have h4 : c t ≤ 1 := le_trans (le_abs_self _) ht
    rw [clampR_bot, EReal.coe_lt_coe_iff]
    linarith
  | top =>
    rw [EReal.tendsto_nhds_top_iff_real]
    intro r
    filter_upwards [hc1, eventually_ge_atTop (Nat.ceil (|r| + 2))] with t ht htr
    have h1 : |r| + 2 ≤ (t : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast htr)
    have h2 : r ≤ |r| := le_abs_self r
    have h4 : -1 ≤ c t := by have := neg_abs_le (c t); linarith
    rw [clampR_top, EReal.coe_lt_coe_iff]
    linarith
  | coe r =>
    rw [EReal.tendsto_coe]
    have heq : ∀ᶠ t : ℕ in atTop, r + c t = clampR (r : EReal) t + c t := by
      filter_upwards [eventually_ge_atTop (Nat.ceil |r|)] with t ht
      rw [clampR_coe_of_le (le_trans (Nat.le_ceil _) (by exact_mod_cast ht))]
    refine Tendsto.congr' heq ?_
    simpa using (tendsto_const_nhds (x := r) (α := ℕ) (f := atTop)).add hc

lemma tendsto_clampR_sub (x : EReal) :
    Tendsto (fun t : ℕ => ((clampR x t - 1 / (t + 1) : ℝ) : EReal)) atTop (nhds x) := by
  have := tendsto_clampR_add_of x (fun t : ℕ => -(1 / ((t : ℝ) + 1)))
    (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg)
  simpa [sub_eq_add_neg] using this

lemma tendsto_clampR_add (x : EReal) :
    Tendsto (fun t : ℕ => ((clampR x t + 1 / (t + 1) : ℝ) : EReal)) atTop (nhds x) :=
  tendsto_clampR_add_of x _ (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Real target sequences approximating a pair `α ≤ β` of extended reals, with `al t < be t`. -/
theorem exists_approx (α β : EReal) (hαβ : α ≤ β) :
    ∃ al be : ℕ → ℝ, (∀ t, al t < be t) ∧
      Tendsto (fun t => ((al t : ℝ) : EReal)) atTop (nhds α) ∧
      Tendsto (fun t => ((be t : ℝ) : EReal)) atTop (nhds β) := by
  refine ⟨fun t => clampR α t - 1 / (t + 1), fun t => clampR β t + 1 / (t + 1), ?_,
    tendsto_clampR_sub α, tendsto_clampR_add β⟩
  intro t
  have h1 : clampR α t ≤ clampR β t := clampR_mono hαβ t
  have h2 : (0 : ℝ) < 1 / ((t : ℝ) + 1) := by positivity
  linarith

end Rudin.Rearrange


/-!
# Splitting a conditionally convergent series into its positive and negative parts

For a real series `∑ aₙ` which converges but not absolutely we enumerate the indices with
`0 ≤ aₙ` and those with `aₙ < 0`, and record that both index sets are infinite and that both
the series of nonnegative terms and the series of absolute values of the negative terms
diverge to `+∞`.
-/

open Filter Topology

namespace Rudin.Rearrange

variable (a : ℕ → ℝ)

/-- The `k`-th index (in increasing order) at which the term is nonnegative. -/
noncomputable def posIdx (k : ℕ) : ℕ := Nat.nth (fun n => 0 ≤ a n) k

/-- The `k`-th index (in increasing order) at which the term is negative. -/
noncomputable def negIdx (k : ℕ) : ℕ := Nat.nth (fun n => ¬ (0 ≤ a n)) k

/-- Partial sums of the subseries of nonnegative terms. -/
noncomputable def Ppart (i : ℕ) : ℝ := ∑ k ∈ Finset.range i, a (posIdx a k)

/-- Partial sums of the subseries of absolute values of the negative terms. -/
noncomputable def Qpart (j : ℕ) : ℝ := ∑ k ∈ Finset.range j, (-(a (negIdx a k)))

variable {a}

lemma Ppart_succ_sub (k : ℕ) : Ppart a (k + 1) - Ppart a k = a (posIdx a k) := by
  simp [Ppart, Finset.sum_range_succ]

lemma Qpart_succ_sub (k : ℕ) : Qpart a (k + 1) - Qpart a k = -(a (negIdx a k)) := by
  simp [Qpart, Finset.sum_range_succ]

lemma max_self_zero (x : ℝ) : max x 0 = (|x| + x) / 2 := by
  rcases le_or_gt 0 x with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h.le, abs_of_neg h]; ring

lemma max_neg_zero (x : ℝ) : max (-x) 0 = (|x| - x) / 2 := by
  rcases le_or_gt 0 x with h | h
  · rw [max_eq_right (by linarith), abs_of_nonneg h]; ring
  · rw [max_eq_left (by linarith), abs_of_neg h]; ring

section

variable (hconv : SeriesConverges a) (hnabs : ¬ SeriesConvergesAbsolutely a)
include hconv

/-- The terms of a convergent series tend to `0`. -/
lemma tendsto_terms_zero : Tendsto a atTop (nhds 0) := by
  obtain ⟨s, hs⟩ := hconv
  have h1 : Tendsto (fun n => partialSum a (n + 1)) atTop (nhds s) :=
    hs.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => partialSum a (n + 1) - partialSum a n) atTop (nhds (s - s)) :=
    h1.sub hs
  rw [sub_self] at h2
  simpa [partialSum, Finset.sum_range_succ] using h2

include hnabs

omit hconv in
/-- The partial sums of `∑ |aₙ|` tend to `+∞`. -/
lemma tendsto_abs_partialSum_atTop :
    Tendsto (fun N => ∑ n ∈ Finset.range N, |a n|) atTop atTop := by
  have hmono : Monotone (fun N => ∑ n ∈ Finset.range N, |a n|) := by
    refine monotone_nat_of_le_succ fun n => ?_
    simp [Finset.sum_range_succ, abs_nonneg]
  refine tendsto_atTop_atTop_of_monotone' hmono ?_
  intro hbdd
  refine hnabs ⟨⨆ i, ∑ n ∈ Finset.range i, |a n|, ?_⟩
  have heq : partialSum (fun n => ‖a n‖) = fun N => ∑ n ∈ Finset.range N, |a n| := by
    funext N
    simp [partialSum, Real.norm_eq_abs]
  rw [SeriesConvergesTo, heq]
  exact tendsto_atTop_ciSup hmono hbdd

/-- The partial sums of the positive parts tend to `+∞`. -/
lemma tendsto_posPart_atTop :
    Tendsto (fun N => ∑ n ∈ Finset.range N, max (a n) 0) atTop atTop := by
  obtain ⟨s, hs⟩ := id hconv
  have hB := tendsto_abs_partialSum_atTop hnabs
  have key : ∀ N, ∑ n ∈ Finset.range N, max (a n) 0
      = (∑ n ∈ Finset.range N, |a n|) / 2 + (partialSum a N) / 2 := by
    intro N
    calc ∑ n ∈ Finset.range N, max (a n) 0
        = ∑ n ∈ Finset.range N, (|a n| + a n) / 2 :=
          Finset.sum_congr rfl fun n _ => max_self_zero (a n)
      _ = (∑ n ∈ Finset.range N, (|a n| + a n)) / 2 := by rw [← Finset.sum_div]
      _ = ((∑ n ∈ Finset.range N, |a n|) + ∑ n ∈ Finset.range N, a n) / 2 := by
          rw [Finset.sum_add_distrib]
      _ = (∑ n ∈ Finset.range N, |a n|) / 2 + (partialSum a N) / 2 := by
          rw [partialSum]; ring
  simp only [key]
  exact Tendsto.atTop_add (hB.atTop_div_const two_pos) (hs.div_const 2)

/-- The partial sums of the negative parts tend to `+∞`. -/
lemma tendsto_negPart_atTop :
    Tendsto (fun N => ∑ n ∈ Finset.range N, max (-a n) 0) atTop atTop := by
  obtain ⟨s, hs⟩ := id hconv
  have hB := tendsto_abs_partialSum_atTop hnabs
  have key : ∀ N, ∑ n ∈ Finset.range N, max (-a n) 0
      = (∑ n ∈ Finset.range N, |a n|) / 2 + (-(partialSum a N) / 2) := by
    intro N
    calc ∑ n ∈ Finset.range N, max (-a n) 0
        = ∑ n ∈ Finset.range N, (|a n| - a n) / 2 :=
          Finset.sum_congr rfl fun n _ => max_neg_zero (a n)
      _ = (∑ n ∈ Finset.range N, (|a n| - a n)) / 2 := by rw [← Finset.sum_div]
      _ = ((∑ n ∈ Finset.range N, |a n|) - ∑ n ∈ Finset.range N, a n) / 2 := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ n ∈ Finset.range N, |a n|) / 2 + (-(partialSum a N) / 2) := by
          rw [partialSum]; ring
  simp only [key]
  exact Tendsto.atTop_add (hB.atTop_div_const two_pos) ((hs.neg).div_const 2)

/-- Infinitely many terms are nonnegative. -/
lemma posSet_infinite : {n | 0 ≤ a n}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have hzero : ∀ n, N < n → max (a n) 0 = 0 := by
    intro n hn
    have : ¬ (0 ≤ a n) := fun h => absurd (hN (show n ∈ {m | 0 ≤ a m} from h)) (by omega)
    exact max_eq_right (not_le.1 this).le
  have hconst : ∀ M, N + 1 ≤ M →
      ∑ n ∈ Finset.range M, max (a n) 0 = ∑ n ∈ Finset.range (N + 1), max (a n) 0 := by
    intro M hM
    refine (Finset.sum_subset (Finset.range_subset_range.mpr hM) ?_).symm
    intro x hx hx'
    simp only [Finset.mem_range, not_lt] at hx hx'
    exact hzero x (by omega)
  have hdiv := tendsto_posPart_atTop hconv hnabs
  obtain ⟨M, hM1, hM2⟩ :=
    ((hdiv.eventually_ge_atTop (∑ n ∈ Finset.range (N + 1), max (a n) 0 + 1)).and
      (eventually_ge_atTop (N + 1))).exists
  rw [hconst M hM2] at hM1
  linarith

/-- Infinitely many terms are negative. -/
lemma negSet_infinite : {n | ¬ (0 ≤ a n)}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have hzero : ∀ n, N < n → max (-a n) 0 = 0 := by
    intro n hn
    have : 0 ≤ a n := by
      by_contra h
      exact absurd (hN (show n ∈ {m | ¬ (0 ≤ a m)} from h)) (by omega)
    exact max_eq_right (by linarith)
  have hconst : ∀ M, N + 1 ≤ M →
      ∑ n ∈ Finset.range M, max (-a n) 0 = ∑ n ∈ Finset.range (N + 1), max (-a n) 0 := by
    intro M hM
    refine (Finset.sum_subset (Finset.range_subset_range.mpr hM) ?_).symm
    intro x hx hx'
    simp only [Finset.mem_range, not_lt] at hx hx'
    exact hzero x (by omega)
  have hdiv := tendsto_negPart_atTop hconv hnabs
  obtain ⟨M, hM1, hM2⟩ :=
    ((hdiv.eventually_ge_atTop (∑ n ∈ Finset.range (N + 1), max (-a n) 0 + 1)).and
      (eventually_ge_atTop (N + 1))).exists
  rw [hconst M hM2] at hM1
  linarith

end

section

variable (hpos : {n | 0 ≤ a n}.Infinite) (hneg : {n | ¬ (0 ≤ a n)}.Infinite)

include hpos in
lemma strictMono_posIdx : StrictMono (posIdx a) := by
  intro k l hkl
  exact (Nat.nth_lt_nth hpos).2 hkl

include hneg in
lemma strictMono_negIdx : StrictMono (negIdx a) := by
  intro k l hkl
  exact (Nat.nth_lt_nth hneg).2 hkl

include hpos in
lemma nonneg_posIdx (k : ℕ) : 0 ≤ a (posIdx a k) := Nat.nth_mem_of_infinite hpos k

include hneg in
lemma neg_negIdx (k : ℕ) : ¬ (0 ≤ a (negIdx a k)) := Nat.nth_mem_of_infinite hneg k

include hpos hneg in
lemma posIdx_ne_negIdx (k l : ℕ) : posIdx a k ≠ negIdx a l := by
  intro h
  exact neg_negIdx hneg l (h ▸ nonneg_posIdx hpos k)

lemma exists_idx (n : ℕ) : (∃ k, posIdx a k = n) ∨ (∃ k, negIdx a k = n) := by
  classical
  by_cases h : 0 ≤ a n
  · exact Or.inl ⟨Nat.count (fun m => 0 ≤ a m) n, Nat.nth_count h⟩
  · exact Or.inr ⟨Nat.count (fun m => ¬ (0 ≤ a m)) n, Nat.nth_count h⟩

open Classical in
/-- `Ppart` is the reindexed sum of the positive parts. -/
lemma Ppart_count (N : ℕ) :
    Ppart a (Nat.count (fun n => 0 ≤ a n) N) = ∑ n ∈ Finset.range N, max (a n) 0 := by
  classical
  induction N with
  | zero => simp [Ppart]
  | succ N ih =>
    rw [Nat.count_succ, Finset.sum_range_succ, ← ih]
    by_cases h : 0 ≤ a N
    · rw [if_pos h, Ppart, Ppart, Finset.sum_range_succ, posIdx, Nat.nth_count h,
        max_eq_left h]
    · rw [if_neg h, max_eq_right (not_le.1 h).le, add_zero, add_zero]

open Classical in
/-- `Qpart` is the reindexed sum of the negative parts. -/
lemma Qpart_count (N : ℕ) :
    Qpart a (Nat.count (fun n => ¬ (0 ≤ a n)) N) = ∑ n ∈ Finset.range N, max (-a n) 0 := by
  classical
  induction N with
  | zero => simp [Qpart]
  | succ N ih =>
    rw [Nat.count_succ, Finset.sum_range_succ, ← ih]
    by_cases h : 0 ≤ a N
    · rw [if_neg (by simpa using h), max_eq_right (by linarith), add_zero, add_zero]
    · rw [if_pos (by simpa using h), Qpart, Qpart, Finset.sum_range_succ, negIdx,
        Nat.nth_count (by simpa using h), max_eq_left (by
          have := not_le.1 h
          linarith)]

include hpos in
lemma monotone_Ppart : Monotone (Ppart a) := by
  refine monotone_nat_of_le_succ fun i => ?_
  have := nonneg_posIdx (a := a) hpos i
  have h := Ppart_succ_sub (a := a) i
  linarith

include hneg in
lemma monotone_Qpart : Monotone (Qpart a) := by
  refine monotone_nat_of_le_succ fun j => ?_
  have := neg_negIdx (a := a) hneg j
  have h := Qpart_succ_sub (a := a) j
  have : a (negIdx a j) < 0 := not_le.1 this
  linarith

end

section

variable (hconv : SeriesConverges a) (hnabs : ¬ SeriesConvergesAbsolutely a)
include hconv hnabs

lemma tendsto_Ppart_atTop : Tendsto (Ppart a) atTop atTop := by
  classical
  have hpos := posSet_infinite hconv hnabs
  have hmono := monotone_Ppart (a := a) hpos
  refine tendsto_atTop_atTop_of_monotone' hmono ?_
  rintro ⟨M, hM⟩
  have hbound : ∀ N, ∑ n ∈ Finset.range N, max (a n) 0 ≤ M := by
    intro N
    rw [← Ppart_count]
    exact hM (Set.mem_range_self _)
  have hdiv := tendsto_posPart_atTop hconv hnabs
  obtain ⟨N, hN⟩ := (hdiv.eventually_ge_atTop (M + 1)).exists
  linarith [hbound N]

lemma tendsto_Qpart_atTop : Tendsto (Qpart a) atTop atTop := by
  classical
  have hneg := negSet_infinite hconv hnabs
  have hmono := monotone_Qpart (a := a) hneg
  refine tendsto_atTop_atTop_of_monotone' hmono ?_
  rintro ⟨M, hM⟩
  have hbound : ∀ N, ∑ n ∈ Finset.range N, max (-a n) 0 ≤ M := by
    intro N
    rw [← Qpart_count]
    exact hM (Set.mem_range_self _)
  have hdiv := tendsto_negPart_atTop hconv hnabs
  obtain ⟨N, hN⟩ := (hdiv.eventually_ge_atTop (M + 1)).exists
  linarith [hbound N]

lemma tendsto_dPpart_zero :
    Tendsto (fun k => Ppart a (k + 1) - Ppart a k) atTop (nhds 0) := by
  have hpos := posSet_infinite hconv hnabs
  have h := (tendsto_terms_zero hconv).comp (strictMono_posIdx (a := a) hpos).tendsto_atTop
  have heq : (fun k => Ppart a (k + 1) - Ppart a k) = fun k => a (posIdx a k) :=
    funext fun k => Ppart_succ_sub k
  rw [heq]
  simpa [Function.comp_def] using h

lemma tendsto_dQpart_zero :
    Tendsto (fun k => Qpart a (k + 1) - Qpart a k) atTop (nhds 0) := by
  have hneg := negSet_infinite hconv hnabs
  have h := (tendsto_terms_zero hconv).comp (strictMono_negIdx (a := a) hneg).tendsto_atTop
  have h' := h.neg
  rw [neg_zero] at h'
  have heq : (fun k => Qpart a (k + 1) - Qpart a k) = fun k => -(a (negIdx a k)) :=
    funext fun k => Qpart_succ_sub k
  rw [heq]
  simpa [Function.comp_def] using h'

end

end Rudin.Rearrange


/-!
# From the greedy machine to a rearrangement

Given a `Setup` whose two series are the subseries of nonnegative and of negative terms of
a sequence `a`, the order in which the greedy machine consumes indices is a permutation of `ℕ`,
and the partial sums of the rearranged series are exactly the running sums of the machine.
-/

open Filter Topology

namespace Rudin.Rearrange

/-- The index of `a` consumed at step `n` of the machine. -/
noncomputable def idxOf (S : Setup) (f g : ℕ → ℕ) (n : ℕ) : ℕ :=
  if (S.st n).takingPos then f (S.I n) else g (S.J n)

variable {S : Setup} {f g : ℕ → ℕ}

lemma idxOf_pos {n : ℕ} (h : (S.st n).takingPos = true) : idxOf S f g n = f (S.I n) := by
  simp [idxOf, h]

lemma idxOf_neg {n : ℕ} (h : (S.st n).takingPos = false) : idxOf S f g n = g (S.J n) := by
  simp [idxOf, h]

lemma idxOf_injective (hf : StrictMono f) (hg : StrictMono g) (hdisj : ∀ k l, f k ≠ g l) :
    Function.Injective (idxOf S f g) := by
  have key : ∀ n m, n < m → idxOf S f g n ≠ idxOf S f g m := by
    intro n m hnm
    rcases Setup.takingPos_cases S n with hn | hn <;>
      rcases Setup.takingPos_cases S m with hm | hm
    · rw [idxOf_neg hn, idxOf_neg hm]
      have h1 : S.J n < S.J m := by
        have h2 : S.J n + 1 = S.J (n + 1) := (Setup.J_succ_neg hn).symm
        have h3 : S.J (n + 1) ≤ S.J m := Setup.monotone_J (by omega)
        omega
      exact fun h => absurd (hg.injective h) (Nat.ne_of_lt h1)
    · rw [idxOf_neg hn, idxOf_pos hm]
      exact fun h => hdisj _ _ h.symm
    · rw [idxOf_pos hn, idxOf_neg hm]
      exact fun h => hdisj _ _ h
    · rw [idxOf_pos hn, idxOf_pos hm]
      have h1 : S.I n < S.I m := by
        have h2 : S.I n + 1 = S.I (n + 1) := (Setup.I_succ_pos hn).symm
        have h3 : S.I (n + 1) ≤ S.I m := Setup.monotone_I (by omega)
        omega
      exact fun h => absurd (hf.injective h) (Nat.ne_of_lt h1)
  intro n m h
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact absurd h (key n m hlt)
  · exact heq
  · exact absurd h.symm (key m n hgt)

/-- A monotone counter starting at `0`, increasing by at most one at a time and tending to
infinity, takes every value, and does so by a genuine increment. -/
lemma exists_step_at (F : ℕ → ℕ) (h0 : F 0 = 0) (hstep : ∀ n, F (n + 1) ≤ F n + 1)
    (htend : Tendsto F atTop atTop) (k : ℕ) : ∃ p, F p = k ∧ F (p + 1) = k + 1 := by
  classical
  have hex : ∃ n, k + 1 ≤ F n := (htend.eventually_ge_atTop (k + 1)).exists
  have hspec : k + 1 ≤ F (Nat.find hex) := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h, h0] at hspec
    omega
  obtain ⟨p, hp⟩ : ∃ p, Nat.find hex = p + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hmin : ¬ (k + 1 ≤ F p) := Nat.find_min hex (by omega)
  rw [hp] at hspec
  have h2 : F (p + 1) ≤ F p + 1 := hstep p
  exact ⟨p, by omega, by omega⟩

lemma idxOf_surjective (hcover : ∀ n, (∃ k, f k = n) ∨ (∃ k, g k = n)) :
    Function.Surjective (idxOf S f g) := by
  intro N
  rcases hcover N with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨p, hp1, hp2⟩ :=
      exists_step_at S.I (S.I_zero) (fun n => Setup.I_succ_le n) Setup.tendsto_I_atTop k
    have hstep : (S.st p).takingPos = true := by
      rcases Setup.takingPos_cases S p with h | h
      · rw [Setup.I_succ_neg h] at hp2; omega
      · exact h
    exact ⟨p, by rw [idxOf_pos hstep, hp1, hk]⟩
  · obtain ⟨p, hp1, hp2⟩ :=
      exists_step_at S.J (S.J_zero) (fun n => Setup.J_succ_le n) Setup.tendsto_J_atTop k
    have hstep : (S.st p).takingPos = false := by
      rcases Setup.takingPos_cases S p with h | h
      · exact h
      · rw [Setup.J_succ_pos h] at hp2; omega
    exact ⟨p, by rw [idxOf_neg hstep, hp1, hk]⟩

lemma partialSum_idxOf {a : ℕ → ℝ}
    (hP : ∀ i, S.Pp i = ∑ k ∈ Finset.range i, a (f k))
    (hQ : ∀ j, S.Qp j = ∑ k ∈ Finset.range j, -a (g k)) (n : ℕ) :
    partialSum (fun k => a (idxOf S f g k)) n = S.sval n := by
  induction n with
  | zero => simp [partialSum, Setup.sval_eq, hP 0, hQ 0]
  | succ n ih =>
    rw [partialSum, Finset.sum_range_succ, ← partialSum, ih, Setup.sval_eq]
    rcases Setup.takingPos_cases S n with h | h
    · rw [idxOf_neg h, Setup.sval_succ_neg h]
      have hstep : S.Qp (S.J n + 1) = S.Qp (S.J n) + (-a (g (S.J n))) := by
        rw [hQ, hQ, Finset.sum_range_succ]
      rw [hstep]
      ring
    · rw [idxOf_pos h, Setup.sval_succ_pos h]
      have hstep : S.Pp (S.I n + 1) = S.Pp (S.I n) + a (f (S.I n)) := by
        rw [hP, hP, Finset.sum_range_succ]
      rw [hstep]
      ring

/-- The abstract form of Riemann's rearrangement theorem: a greedy machine attached to the
positive/negative splitting of `a` produces a permutation with the prescribed lower and
upper limits. -/
theorem exists_perm_of_setup {a : ℕ → ℝ} {α β : EReal}
    (hf : StrictMono f) (hg : StrictMono g) (hdisj : ∀ k l, f k ≠ g l)
    (hcover : ∀ n, (∃ k, f k = n) ∨ (∃ k, g k = n))
    (hP : ∀ i, S.Pp i = ∑ k ∈ Finset.range i, a (f k))
    (hQ : ∀ j, S.Qp j = ∑ k ∈ Finset.range j, -a (g k))
    (hal : Tendsto (fun t => ((S.al t : ℝ) : EReal)) atTop (nhds α))
    (hbe : Tendsto (fun t => ((S.be t : ℝ) : EReal)) atTop (nhds β)) :
    ∃ σ : Equiv.Perm ℕ,
      liminf (fun n => ((partialSum (fun k => a (σ k)) n : ℝ) : EReal)) atTop = α ∧
      limsup (fun n => ((partialSum (fun k => a (σ k)) n : ℝ) : EReal)) atTop = β := by
  have hbij : Function.Bijective (idxOf S f g) :=
    ⟨idxOf_injective hf hg hdisj, idxOf_surjective hcover⟩
  refine ⟨Equiv.ofBijective _ hbij, ?_, ?_⟩ <;>
  · have hps : ∀ n, partialSum (fun k => a (Equiv.ofBijective _ hbij k)) n = S.sval n := by
      intro n
      simpa [Equiv.ofBijective] using partialSum_idxOf hP hQ n
    simp only [hps]
    first
      | exact S.liminf_sval hal
      | exact S.limsup_sval hbe

end Rudin.Rearrange


/-!
# Rudin, Theorem 3.54 — Riemann's rearrangement theorem
-/

open Filter Topology

open Rudin

/-- Rudin, Theorem 3.54 (Riemann's rearrangement theorem): let `∑ aₙ` be a series of real
numbers which converges but not absolutely, and let `-∞ ≤ α ≤ β ≤ ∞`.  Then there is a
rearrangement `∑ a_{σ(n)}` whose partial sums `sₙ'` satisfy `liminf sₙ' = α` and
`limsup sₙ' = β`. -/
theorem solution (a : ℕ → ℝ)
    (hconv : SeriesConverges a) (hnabs : ¬ SeriesConvergesAbsolutely a)
    (α β : EReal) (hαβ : α ≤ β) :
    ∃ σ : Equiv.Perm ℕ,
      liminf (fun n => ((partialSum (fun k => a (σ k)) n : ℝ) : EReal)) atTop = α ∧
      limsup (fun n => ((partialSum (fun k => a (σ k)) n : ℝ) : EReal)) atTop = β := by
  obtain ⟨al, be, hltab, hal, hbe⟩ := Rearrange.exists_approx α β hαβ
  have hpos := Rearrange.posSet_infinite hconv hnabs
  have hneg := Rearrange.negSet_infinite hconv hnabs
  let S : Rearrange.Setup :=
    { Pp := Rearrange.Ppart a
      Qp := Rearrange.Qpart a
      al := al
      be := be
      monoP := Rearrange.monotone_Ppart hpos
      monoQ := Rearrange.monotone_Qpart hneg
      tendP := Rearrange.tendsto_Ppart_atTop hconv hnabs
      tendQ := Rearrange.tendsto_Qpart_atTop hconv hnabs
      dP := Rearrange.tendsto_dPpart_zero hconv hnabs
      dQ := Rearrange.tendsto_dQpart_zero hconv hnabs
      ltab := hltab }
  exact Rearrange.exists_perm_of_setup (S := S) (a := a)
    (Rearrange.strictMono_posIdx hpos) (Rearrange.strictMono_negIdx hneg)
    (Rearrange.posIdx_ne_negIdx hpos hneg) Rearrange.exists_idx
    (fun _ => rfl) (fun _ => rfl) hal hbe


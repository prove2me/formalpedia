-- Prove2me | solution 1 for SongZipkinFluct.Linear.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T23:34:17.330951+00:00
-- url     : https://prove2.me/submissions/94d86c86-01fb-4594-a458-9841cd4dbfee

import Mathlib
import Definitions.Def_SongZipkinFluct_Linear_Model

namespace Prove2SongZipkinL1Submission

open _root_.SongZipkinFluct.Linear

namespace SongZipkinFluct.Linear.Lead34L1

/-- The uniformization rate dominates every state's total event rate. -/
theorem rate_bound {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (i : I) : M.lam i + -M.Q i i ≤ M.μ := by
  have hq : -M.Q i i ≤ sSup (Set.range fun i => -M.Q i i) :=
    le_csSup M.q_bdd (Set.mem_range_self i)
  have hl : M.lam i ≤ sSup (Set.range M.lam) := le_csSup M.lam_bdd (Set.mem_range_self i)
  linarith [M.μ_bound]

theorem jumpDemandMass_nonneg {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (n : ℕ) : ∀ (i : I) (d : ℕ), 0 ≤ M.jumpDemandMass n i d := by
  induction n with
  | zero =>
    intro _ d
    show (0 : ℝ) ≤ if d = 0 then 1 else 0
    exact ite_nonneg zero_le_one le_rfl
  | succ n ih =>
    intro i d
    have hself : 0 ≤ 1 - (M.lam i + -M.Q i i) / M.μ :=
      sub_nonneg.mpr ((div_le_one M.μ_pos).mpr (rate_bound M i))
    show 0 ≤ M.lam i / M.μ * (if d = 0 then 0 else M.jumpDemandMass n i (d - 1)) +
        (∑' j : {j : I // j ≠ i}, M.Q i j.1 / M.μ * M.jumpDemandMass n j.1 d) +
        (1 - (M.lam i + -M.Q i i) / M.μ) * M.jumpDemandMass n i d
    refine add_nonneg (add_nonneg ?_ ?_) (mul_nonneg hself (ih i d))
    · exact mul_nonneg (div_nonneg (M.lam_nonneg i) M.μ_pos.le)
        (ite_nonneg le_rfl (ih i (d - 1)))
    · exact tsum_nonneg fun j => mul_nonneg
        (div_nonneg (M.Q_off_nonneg i j.1 (Ne.symm j.2)) M.μ_pos.le) (ih j.1 d)

theorem demandMass_nonneg {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (i : I) (d : ℕ) (l : NNReal) : 0 ≤ M.demandMass i d l := by
  unfold Model.demandMass
  exact tsum_nonneg fun n => mul_nonneg (div_nonneg (mul_nonneg (Real.exp_pos _).le
    (pow_nonneg (mul_nonneg M.μ_pos.le (NNReal.coe_nonneg l)) n)) (Nat.cast_nonneg _))
    (jumpDemandMass_nonneg M n i d)

theorem discDemandMass_nonneg {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (i : I) (d : ℕ) : 0 ≤ M.discDemandMass i d := by
  unfold Model.discDemandMass
  exact MeasureTheory.integral_nonneg fun l =>
    mul_nonneg (Real.exp_pos _).le (demandMass_nonneg M i d l)

/-- The forward difference of the inventory cost rate: `-p` below zero, `h` from zero on. -/
theorem rate_succ_sub {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (x : ℤ) : M.inventoryRate (x + 1) - M.inventoryRate x = if x < 0 then -M.p else M.h := by
  unfold Model.inventoryRate
  by_cases hx : x < 0
  · rw [if_pos hx, if_pos hx]
    by_cases hx1 : x + 1 < 0
    · rw [if_pos hx1]
      push_cast
      ring
    · rw [if_neg hx1]
      have hx' : x = -1 := by omega
      subst hx'
      push_cast
      ring
  · have hx1 : ¬x + 1 < 0 := by omega
    rw [if_neg hx, if_neg hx, if_neg hx1]
    push_cast
    ring

theorem rate_conv {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (x : ℤ) : M.inventoryRate (x + 1) - M.inventoryRate x ≤
      M.inventoryRate (x + 2) - M.inventoryRate (x + 1) := by
  have e : x + 2 = x + 1 + 1 := by ring
  have d0 := rate_succ_sub M x
  have d1 := rate_succ_sub M (x + 1)
  rw [← e] at d1
  have hp := M.p_pos
  have hh := M.h_pos
  by_cases h1 : x + 1 < 0
  · rw [if_pos h1] at d1
    rw [if_pos (show x < 0 by omega)] at d0
    linarith
  · rw [if_neg h1] at d1
    by_cases h0 : x < 0
    · rw [if_pos h0] at d0
      linarith
    · rw [if_neg h0] at d0
      linarith

theorem rate_diff_abs {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (x : ℤ) : |M.inventoryRate (x + 1) - M.inventoryRate x| ≤ M.p + M.h := by
  rw [rate_succ_sub M x]
  have hp := M.p_pos
  have hh := M.h_pos
  by_cases hx : x < 0
  · rw [if_pos hx, abs_neg, abs_of_pos hp]
    linarith
  · rw [if_neg hx, abs_of_pos hh]
    linarith

theorem rate_tail {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (x : ℤ) (hx : x ≤ -1) : M.p ≤ M.inventoryRate x := by
  have hx0 : x < 0 := by omega
  have hxr : (x : ℝ) ≤ -1 := by exact_mod_cast hx
  unfold Model.inventoryRate
  rw [if_pos hx0]
  linarith [mul_le_mul_of_nonneg_left hxr M.p_pos.le]

/-- If one shifted cost series converges, the (nonnegative) demand masses are summable: far in
the tail the cost rate exceeds `p`. -/
theorem summable_of_shift {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (g : ℕ → ℝ) (hg : ∀ d, 0 ≤ g d) (s : ℤ)
    (hs : Summable fun d : ℕ => g d * M.inventoryRate (s - d)) : Summable g := by
  have hk : ∀ n : ℕ, s - ((n + (s.toNat + 1) : ℕ) : ℤ) ≤ -1 := by
    intro n
    have := Int.self_le_toNat s
    omega
  rw [← summable_nat_add_iff (s.toNat + 1)]
  refine Summable.of_nonneg_of_le (fun n => hg _) (fun n => ?_)
    (((summable_nat_add_iff (s.toNat + 1)).mpr hs).div_const M.p)
  rw [le_div_iff₀ M.p_pos]
  exact mul_le_mul_of_nonneg_left (rate_tail M _ (hk n)) (hg _)

/-- With summable demand masses, shifting the inventory position by one changes each term by at
most `(p + h)` times its mass, so summability is unchanged. -/
theorem summable_shift_iff {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (g : ℕ → ℝ) (hg : ∀ d, 0 ≤ g d) (hgs : Summable g) (s : ℤ) :
    (Summable fun d : ℕ => g d * M.inventoryRate (s - d)) ↔
      Summable fun d : ℕ => g d * M.inventoryRate (s + 1 - d) := by
  have hb : Summable fun d : ℕ =>
      g d * (M.inventoryRate (s + 1 - d) - M.inventoryRate (s - d)) := by
    refine Summable.of_norm_bounded (hgs.mul_left (M.p + M.h)) (fun d => ?_)
    have e : s + 1 - (d : ℤ) = s - d + 1 := by ring
    rw [e, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg d)]
    linarith [mul_le_mul_of_nonneg_left (rate_diff_abs M (s - d)) (hg d)]
  constructor
  · intro h
    exact (h.add hb).congr fun d => by ring
  · intro h
    exact (h.sub hb).congr fun d => by ring

theorem term_ineq {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (i : I) (y : ℤ) (d : ℕ) :
    M.discDemandMass i d * M.inventoryRate (y + 1 - d) -
        M.discDemandMass i d * M.inventoryRate (y - d) ≤
      M.discDemandMass i d * M.inventoryRate (y + 1 + 1 - d) -
        M.discDemandMass i d * M.inventoryRate (y + 1 - d) := by
  have e1 : y + 1 - (d : ℤ) = y - d + 1 := by ring
  have e2 : y + 1 + 1 - (d : ℤ) = y - d + 2 := by ring
  rw [e1, e2]
  linarith [mul_le_mul_of_nonneg_left (rate_conv M (y - d)) (discDemandMass_nonneg M i d)]

/-- Integer convexity of the expected discounted inventory cost rate. If the three series are
summable the inequality holds termwise; otherwise none is summable and all three sums vanish. -/
theorem C_intConvex {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (i : I) : IntConvex (M.C i) := by
  intro y
  have hg := discDemandMass_nonneg M i
  have e2 : M.C i (y + 2) = M.C i (y + 1 + 1) := congrArg (M.C i) (by ring)
  rw [e2]
  show (∑' d : ℕ, M.discDemandMass i d * M.inventoryRate (y + 1 - d)) -
      (∑' d : ℕ, M.discDemandMass i d * M.inventoryRate (y - d)) ≤
      (∑' d : ℕ, M.discDemandMass i d * M.inventoryRate (y + 1 + 1 - d)) -
      (∑' d : ℕ, M.discDemandMass i d * M.inventoryRate (y + 1 - d))
  by_cases h1 : Summable fun d : ℕ => M.discDemandMass i d * M.inventoryRate (y + 1 - d)
  · have hgs : Summable fun d => M.discDemandMass i d := summable_of_shift M _ hg (y + 1) h1
    have h0 := (summable_shift_iff M _ hg hgs y).mpr h1
    have h2 := (summable_shift_iff M _ hg hgs (y + 1)).mp h1
    linarith [(h1.sub h0).tsum_le_tsum (fun d => term_ineq M i y d) (h2.sub h1),
      h1.tsum_sub h0, h2.tsum_sub h1]
  · have h0 : ¬Summable fun d : ℕ => M.discDemandMass i d * M.inventoryRate (y - d) :=
      fun h0 => h1 ((summable_shift_iff M _ hg (summable_of_shift M _ hg y h0) y).mp h0)
    have h2 : ¬Summable fun d : ℕ => M.discDemandMass i d * M.inventoryRate (y + 1 + 1 - d) :=
      fun h2 => h1 ((summable_shift_iff M _ hg (summable_of_shift M _ hg (y + 1 + 1) h2)
        (y + 1)).mpr h2)
    linarith [tsum_eq_zero_of_not_summable h0, tsum_eq_zero_of_not_summable h1,
      tsum_eq_zero_of_not_summable h2]

/-- The myopic cost adds a linear term and a nonnegative multiple of `C`. -/
theorem Gplus_intConvex {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (i : I) : IntConvex (M.Gplus i) := by
  intro y
  have hC := C_intConvex M i y
  have hβ : 0 ≤ M.beta := (div_pos one_pos (add_pos M.μ_pos M.α_pos)).le
  unfold Model.Gplus
  push_cast
  linarith [mul_le_mul_of_nonneg_left hC hβ]

end SongZipkinFluct.Linear.Lead34L1

namespace SongZipkinFluct.Linear

/-- Song and Zipkin (1993), Lemma 1, p. 355. Convexity is the
monotonicity of integer forward differences, not integer-scaled `ConvexOn`. -/
theorem lemma1 {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) :
    ∀ i : I, IntConvex (M.C i) ∧ IntConvex (M.Gplus i) := by
  intro i
  exact ⟨Lead34L1.C_intConvex M i, Lead34L1.Gplus_intConvex M i⟩

end SongZipkinFluct.Linear

end Prove2SongZipkinL1Submission

open _root_.SongZipkinFluct.Linear

theorem solution {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) :
    ∀ i : I, IntConvex (M.C i) ∧ IntConvex (M.Gplus i) := by
  exact _root_.Prove2SongZipkinL1Submission.SongZipkinFluct.Linear.lemma1 M

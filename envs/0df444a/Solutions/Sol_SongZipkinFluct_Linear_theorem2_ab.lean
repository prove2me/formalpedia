-- Prove2me | solution 1 for SongZipkinFluct.Linear.theorem2_ab
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T13:33:39.896199+00:00
-- url     : https://prove2.me/submissions/3194aecb-0e05-48de-87e9-790e38ca6e88

import Mathlib
import Definitions.Def_SongZipkinFluct_Linear_Dynamics


open scoped ENNReal NNReal
open MeasureTheory

namespace SZLDev

open _root_.SongZipkinFluct.Linear

variable {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)

theorem rate_bound (i : I) : M.lam i + -M.Q i i ≤ M.μ := by
  have hq : -M.Q i i ≤ sSup (Set.range fun i => -M.Q i i) :=
    le_csSup M.q_bdd (Set.mem_range_self i)
  have hl : M.lam i ≤ sSup (Set.range M.lam) := le_csSup M.lam_bdd (Set.mem_range_self i)
  linarith [M.μ_bound]

theorem lam_le (i : I) : M.lam i ≤ sSup (Set.range M.lam) :=
  le_csSup M.lam_bdd (Set.mem_range_self i)

theorem Lam_nonneg : 0 ≤ sSup (Set.range M.lam) := by
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  exact (M.lam_nonneg i).trans (lam_le M i)

theorem qi_nonneg (i : I) : 0 ≤ -M.Q i i := by
  rw [(M.Q_conservative i).2]
  exact tsum_nonneg fun j => M.Q_off_nonneg i j.1 (Ne.symm j.2)

theorem qsum (i : I) : ∑' j : {j : I // j ≠ i}, M.Q i j.1 = -M.Q i i :=
  (M.Q_conservative i).2.symm

theorem qsummable (i : I) : Summable (fun j : {j : I // j ≠ i} => M.Q i j.1) :=
  (M.Q_conservative i).1

theorem Qoff_nonneg (i : I) (j : {j : I // j ≠ i}) : 0 ≤ M.Q i j.1 :=
  M.Q_off_nonneg i j.1 (Ne.symm j.2)

theorem self_nonneg (i : I) : 0 ≤ 1 - (M.lam i + -M.Q i i) / M.μ :=
  sub_nonneg.mpr ((div_le_one M.μ_pos).mpr (rate_bound M i))

theorem self_nonneg' (i : I) : 0 ≤ M.μ - M.lam i + M.Q i i := by
  linarith [rate_bound M i]

/-- Summability of `Q i j * f j` for bounded `f`. -/
theorem summable_Qmul (i : I) {f : {j : I // j ≠ i} → ℝ} {B : ℝ} (hB : ∀ j, |f j| ≤ B) :
    Summable (fun j => M.Q i j.1 * f j) := by
  refine Summable.of_norm_bounded ((qsummable M i).mul_right B) (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Qoff_nonneg M i j)]
  exact mul_le_mul_of_nonneg_left (hB j) (Qoff_nonneg M i j)

theorem jumpDemandMass_nonneg (n : ℕ) : ∀ (i : I) (d : ℕ), 0 ≤ M.jumpDemandMass n i d := by
  induction n with
  | zero =>
    intro _ d
    show (0 : ℝ) ≤ if d = 0 then 1 else 0
    exact ite_nonneg zero_le_one le_rfl
  | succ n ih =>
    intro i d
    show 0 ≤ M.lam i / M.μ * (if d = 0 then 0 else M.jumpDemandMass n i (d - 1)) +
        (∑' j : {j : I // j ≠ i}, M.Q i j.1 / M.μ * M.jumpDemandMass n j.1 d) +
        (1 - (M.lam i + -M.Q i i) / M.μ) * M.jumpDemandMass n i d
    refine add_nonneg (add_nonneg ?_ ?_) (mul_nonneg (self_nonneg M i) (ih i d))
    · exact mul_nonneg (div_nonneg (M.lam_nonneg i) M.μ_pos.le)
        (ite_nonneg le_rfl (ih i (d - 1)))
    · exact tsum_nonneg fun j => mul_nonneg
        (div_nonneg (Qoff_nonneg M i j) M.μ_pos.le) (ih j.1 d)

theorem summable_Qdiv_mul (i : I) {f : {j : I // j ≠ i} → ℝ} {B : ℝ} (hB : ∀ j, |f j| ≤ B) :
    Summable (fun j => M.Q i j.1 / M.μ * f j) := by
  have := (summable_Qmul M i hB).div_const M.μ
  refine this.congr fun j => ?_
  ring

theorem jumpDemandMass_le_one (n : ℕ) : ∀ (i : I) (d : ℕ), M.jumpDemandMass n i d ≤ 1 := by
  induction n with
  | zero =>
    intro _ d
    show (if d = 0 then (1 : ℝ) else 0) ≤ 1
    split_ifs <;> norm_num
  | succ n ih =>
    intro i d
    show M.lam i / M.μ * (if d = 0 then 0 else M.jumpDemandMass n i (d - 1)) +
        (∑' j : {j : I // j ≠ i}, M.Q i j.1 / M.μ * M.jumpDemandMass n j.1 d) +
        (1 - (M.lam i + -M.Q i i) / M.μ) * M.jumpDemandMass n i d ≤ 1
    have hμ := M.μ_pos
    have h1 : M.lam i / M.μ * (if d = 0 then 0 else M.jumpDemandMass n i (d - 1)) ≤
        M.lam i / M.μ := by
      refine mul_le_of_le_one_right (div_nonneg (M.lam_nonneg i) hμ.le) ?_
      split_ifs
      · norm_num
      · exact ih i _
    have hb : ∀ j : {j : I // j ≠ i}, |M.jumpDemandMass n j.1 d| ≤ 1 := fun j => by
      rw [abs_of_nonneg (jumpDemandMass_nonneg M n j.1 d)]; exact ih j.1 d
    have h2 : (∑' j : {j : I // j ≠ i}, M.Q i j.1 / M.μ * M.jumpDemandMass n j.1 d) ≤
        -M.Q i i / M.μ := by
      have hs : Summable (fun j : {j : I // j ≠ i} => M.Q i j.1 / M.μ) :=
        (qsummable M i).div_const M.μ
      calc (∑' j : {j : I // j ≠ i}, M.Q i j.1 / M.μ * M.jumpDemandMass n j.1 d)
          ≤ ∑' j : {j : I // j ≠ i}, M.Q i j.1 / M.μ :=
            (summable_Qdiv_mul M i hb).tsum_le_tsum (fun j => mul_le_of_le_one_right
              (div_nonneg (Qoff_nonneg M i j) hμ.le) (ih j.1 d)) hs
        _ = -M.Q i i / M.μ := by rw [tsum_div_const, qsum]
    have h3 : (1 - (M.lam i + -M.Q i i) / M.μ) * M.jumpDemandMass n i d ≤
        1 - (M.lam i + -M.Q i i) / M.μ :=
      mul_le_of_le_one_right (self_nonneg M i) (ih i d)
    have : M.lam i / M.μ + -M.Q i i / M.μ + (1 - (M.lam i + -M.Q i i) / M.μ) = 1 := by
      field_simp; ring
    linarith

/-! ### ENNReal versions -/

noncomputable def Je (n : ℕ) (i : I) (d : ℕ) : ℝ≥0∞ := ENNReal.ofReal (M.jumpDemandMass n i d)

theorem Je_succ (n : ℕ) (i : I) (d : ℕ) :
    Je M (n + 1) i d = ENNReal.ofReal (M.lam i / M.μ) * (if d = 0 then 0 else Je M n i (d - 1)) +
      (∑' j : {j : I // j ≠ i}, ENNReal.ofReal (M.Q i j.1 / M.μ) * Je M n j.1 d) +
      ENNReal.ofReal (1 - (M.lam i + -M.Q i i) / M.μ) * Je M n i d := by
  have hμ := M.μ_pos
  unfold Je
  have hb : ∀ j : {j : I // j ≠ i}, |M.jumpDemandMass n j.1 d| ≤ 1 := fun j => by
    rw [abs_of_nonneg (jumpDemandMass_nonneg M n j.1 d)]; exact jumpDemandMass_le_one M n j.1 d
  have e : M.jumpDemandMass (n + 1) i d =
      M.lam i / M.μ * (if d = 0 then 0 else M.jumpDemandMass n i (d - 1)) +
        (∑' j : {j : I // j ≠ i}, M.Q i j.1 / M.μ * M.jumpDemandMass n j.1 d) +
        (1 - (M.lam i + -M.Q i i) / M.μ) * M.jumpDemandMass n i d := rfl
  have hl : 0 ≤ M.lam i / M.μ := div_nonneg (M.lam_nonneg i) hμ.le
  have hite : 0 ≤ (if d = 0 then 0 else M.jumpDemandMass n i (d - 1)) :=
    ite_nonneg le_rfl (jumpDemandMass_nonneg M n i _)
  have hT : ∀ j : {j : I // j ≠ i}, 0 ≤ M.Q i j.1 / M.μ * M.jumpDemandMass n j.1 d :=
    fun j => mul_nonneg (div_nonneg (Qoff_nonneg M i j) hμ.le) (jumpDemandMass_nonneg M n j.1 d)
  rw [e, ENNReal.ofReal_add (add_nonneg (mul_nonneg hl hite) (tsum_nonneg hT))
      (mul_nonneg (self_nonneg M i) (jumpDemandMass_nonneg M n i d)),
    ENNReal.ofReal_add (mul_nonneg hl hite) (tsum_nonneg hT),
    ENNReal.ofReal_mul hl, ENNReal.ofReal_mul (self_nonneg M i),
    ENNReal.ofReal_tsum_of_nonneg hT (summable_Qdiv_mul M i hb)]
  congr 2
  · split_ifs <;> simp
  · congr 1; funext j
    rw [ENNReal.ofReal_mul (div_nonneg (Qoff_nonneg M i j) hμ.le)]

theorem ofReal_qsum (i : I) :
    ∑' j : {j : I // j ≠ i}, ENNReal.ofReal (M.Q i j.1 / M.μ) = ENNReal.ofReal (-M.Q i i / M.μ) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => div_nonneg (Qoff_nonneg M i j) M.μ_pos.le)
    ((qsummable M i).div_const M.μ), tsum_div_const, qsum]

theorem prob_sum (i : I) :
    ENNReal.ofReal (M.lam i / M.μ) + ENNReal.ofReal (-M.Q i i / M.μ) +
      ENNReal.ofReal (1 - (M.lam i + -M.Q i i) / M.μ) = 1 := by
  have hμ := M.μ_pos
  rw [← ENNReal.ofReal_add (div_nonneg (M.lam_nonneg i) hμ.le) (div_nonneg (qi_nonneg M i) hμ.le),
    ← ENNReal.ofReal_add (add_nonneg (div_nonneg (M.lam_nonneg i) hμ.le)
      (div_nonneg (qi_nonneg M i) hμ.le)) (self_nonneg M i)]
  have : M.lam i / M.μ + -M.Q i i / M.μ + (1 - (M.lam i + -M.Q i i) / M.μ) = 1 := by
    field_simp; ring
  rw [this, ENNReal.ofReal_one]

theorem shift_sum (f : ℕ → ℝ≥0∞) :
    ∑' d : ℕ, (if d = 0 then 0 else f (d - 1)) = ∑' d, f d := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp

theorem shift_sum_mul (f : ℕ → ℝ≥0∞) :
    ∑' d : ℕ, (d : ℝ≥0∞) * (if d = 0 then 0 else f (d - 1)) = ∑' d : ℕ, ((d : ℝ≥0∞) + 1) * f d := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp

theorem Je_sum (n : ℕ) : ∀ i : I, ∑' d, Je M n i d = 1 := by
  induction n with
  | zero =>
    intro i
    unfold Je
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp [Model.jumpDemandMass]
  | succ n ih =>
    intro i
    simp_rw [Je_succ]
    rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
      shift_sum, ih, ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, ih]
    simp only [mul_one]
    rw [ofReal_qsum, prob_sum]

theorem Je_mean (n : ℕ) : ∀ i : I, ∑' d : ℕ, (d : ℝ≥0∞) * Je M n i d ≤
    (n : ℝ≥0∞) * ENNReal.ofReal (sSup (Set.range M.lam) / M.μ) := by
  set B := ENNReal.ofReal (sSup (Set.range M.lam) / M.μ)
  induction n with
  | zero =>
    intro i
    simp only [CharP.cast_eq_zero, zero_mul, nonpos_iff_eq_zero, ENNReal.tsum_eq_zero]
    intro d
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h]
    · simp [Je, Model.jumpDemandMass, h.ne']
  | succ n ih =>
    intro i
    set a := ENNReal.ofReal (M.lam i / M.μ)
    set c := ENNReal.ofReal (1 - (M.lam i + -M.Q i i) / M.μ)
    have h1 : ∑' d : ℕ, (d : ℝ≥0∞) * (a * (if d = 0 then 0 else Je M n i (d - 1))) =
        a * (∑' d : ℕ, (d : ℝ≥0∞) * Je M n i d + 1) := by
      simp_rw [mul_left_comm (_ : ℝ≥0∞) a]
      rw [ENNReal.tsum_mul_left, shift_sum_mul]
      simp_rw [add_mul, one_mul]
      rw [ENNReal.tsum_add, Je_sum M n i]
    have h2 : ∑' d : ℕ, (d : ℝ≥0∞) *
        (∑' j : {j : I // j ≠ i}, ENNReal.ofReal (M.Q i j.1 / M.μ) * Je M n j.1 d) =
        ∑' j : {j : I // j ≠ i}, ENNReal.ofReal (M.Q i j.1 / M.μ) *
          ∑' d : ℕ, (d : ℝ≥0∞) * Je M n j.1 d := by
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      congr 1; funext j; congr 1; funext d; ring
    have h3 : ∑' d : ℕ, (d : ℝ≥0∞) * (c * Je M n i d) = c * ∑' d : ℕ, (d : ℝ≥0∞) * Je M n i d := by
      simp_rw [mul_left_comm (_ : ℝ≥0∞) c]
      rw [ENNReal.tsum_mul_left]
    simp_rw [Je_succ, mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_add, h1, h2, h3]
    have hb : ∑' j : {j : I // j ≠ i}, ENNReal.ofReal (M.Q i j.1 / M.μ) *
          ∑' d : ℕ, (d : ℝ≥0∞) * Je M n j.1 d ≤
        ENNReal.ofReal (-M.Q i i / M.μ) * ((n : ℝ≥0∞) * B) := by
      rw [← ofReal_qsum, ← ENNReal.tsum_mul_right]
      exact ENNReal.tsum_le_tsum fun j => mul_le_mul_right (ih j.1) _
    have ha : a ≤ B := ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (lam_le M i) M.μ_pos.le)
    have hp := prob_sum M i
    calc a * (∑' d : ℕ, (d : ℝ≥0∞) * Je M n i d + 1) +
          ∑' j : {j : I // j ≠ i}, ENNReal.ofReal (M.Q i j.1 / M.μ) *
            ∑' d : ℕ, (d : ℝ≥0∞) * Je M n j.1 d + c * ∑' d : ℕ, (d : ℝ≥0∞) * Je M n i d
        ≤ a * ((n : ℝ≥0∞) * B + 1) + ENNReal.ofReal (-M.Q i i / M.μ) * ((n : ℝ≥0∞) * B) +
            c * ((n : ℝ≥0∞) * B) := by
          gcongr
          · exact ih i
          · exact ih i
      _ = (a + ENNReal.ofReal (-M.Q i i / M.μ) + c) * ((n : ℝ≥0∞) * B) + a := by ring
      _ = (n : ℝ≥0∞) * B + a := by rw [hp, one_mul]
      _ ≤ (n : ℝ≥0∞) * B + B := by gcongr
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * B := by push_cast; ring

/-! ### Poisson weights -/

theorem hasSum_exp (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp x
  rwa [← Real.exp_eq_exp_ℝ] at h

theorem hasSum_poisson (x : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-x) * x ^ n / (n.factorial : ℝ)) 1 := by
  have h := (hasSum_exp x).mul_left (Real.exp (-x))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  refine h.congr_fun fun n => ?_
  ring

theorem hasSum_poisson_mean (x : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * (Real.exp (-x) * x ^ n / (n.factorial : ℝ))) x := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, zero_mul, sub_zero]
  have h := (hasSum_poisson x).mul_left x
  rw [mul_one] at h
  refine h.congr_fun fun n => ?_
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Poisson weight. -/
noncomputable def Pw (n : ℕ) (l : ℝ≥0) : ℝ :=
  Real.exp (-(M.μ * (l : ℝ))) * (M.μ * (l : ℝ)) ^ n / (n.factorial : ℝ)

theorem Pw_nonneg (n : ℕ) (l : ℝ≥0) : 0 ≤ Pw M n l := by
  unfold Pw
  have : 0 ≤ M.μ * (l : ℝ) := mul_nonneg M.μ_pos.le (NNReal.coe_nonneg l)
  positivity

theorem Pw_meas (n : ℕ) : Measurable (fun l : ℝ≥0 => Pw M n l) := by
  unfold Pw
  apply Continuous.measurable
  fun_prop

noncomputable def fe (i : I) (d : ℕ) (l : ℝ≥0) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (Pw M n l) * Je M n i d

theorem fe_eq (i : I) (d : ℕ) (l : ℝ≥0) : ENNReal.ofReal (M.demandMass i d l) = fe M i d l := by
  unfold Model.demandMass fe
  have hnn : ∀ n : ℕ, 0 ≤ Pw M n l * M.jumpDemandMass n i d := fun n =>
    mul_nonneg (Pw_nonneg M n l) (jumpDemandMass_nonneg M n i d)
  have hs : Summable (fun n : ℕ => Pw M n l * M.jumpDemandMass n i d) :=
    Summable.of_nonneg_of_le hnn (fun n => mul_le_of_le_one_right (Pw_nonneg M n l)
      (jumpDemandMass_le_one M n i d)) (hasSum_poisson (M.μ * (l : ℝ))).summable
  have := ENNReal.ofReal_tsum_of_nonneg hnn hs
  unfold Pw at this
  rw [this]
  congr 1; funext n
  show ENNReal.ofReal (Pw M n l * M.jumpDemandMass n i d) = _
  rw [ENNReal.ofReal_mul (Pw_nonneg M n l)]
  rfl

theorem fe_sum (i : I) (l : ℝ≥0) : ∑' d : ℕ, fe M i d l = 1 := by
  unfold fe
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, Je_sum, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => Pw_nonneg M n l)
    (hasSum_poisson (M.μ * (l : ℝ))).summable]
  unfold Pw
  rw [(hasSum_poisson (M.μ * (l : ℝ))).tsum_eq, ENNReal.ofReal_one]

theorem fe_mean (i : I) (l : ℝ≥0) :
    ∑' d : ℕ, (d : ℝ≥0∞) * fe M i d l ≤ ENNReal.ofReal (sSup (Set.range M.lam) * l) := by
  unfold fe
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  have hB := Lam_nonneg M
  calc ∑' n : ℕ, ∑' d : ℕ, (d : ℝ≥0∞) * (ENNReal.ofReal (Pw M n l) * Je M n i d)
      = ∑' n : ℕ, ENNReal.ofReal (Pw M n l) * ∑' d : ℕ, (d : ℝ≥0∞) * Je M n i d := by
        congr 1; funext n
        rw [← ENNReal.tsum_mul_left]
        congr 1; funext d; ring
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (Pw M n l) *
          ((n : ℝ≥0∞) * ENNReal.ofReal (sSup (Set.range M.lam) / M.μ)) :=
        ENNReal.tsum_le_tsum fun n => mul_le_mul_right (Je_mean M n i) _
    _ = ENNReal.ofReal (sSup (Set.range M.lam) / M.μ) *
          ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * Pw M n l) := by
        rw [← ENNReal.tsum_mul_left]
        congr 1; funext n
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
        ring
    _ = ENNReal.ofReal (sSup (Set.range M.lam) / M.μ) * ENNReal.ofReal (M.μ * l) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (Nat.cast_nonneg n)
          (Pw_nonneg M n l)) (hasSum_poisson_mean (M.μ * (l : ℝ))).summable]
        unfold Pw
        rw [(hasSum_poisson_mean (M.μ * (l : ℝ))).tsum_eq]
    _ = ENNReal.ofReal (sSup (Set.range M.lam) * l) := by
        rw [← ENNReal.ofReal_mul (div_nonneg hB M.μ_pos.le)]
        congr 1
        rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ M.μ_pos.ne']

theorem fe_meas (i : I) (d : ℕ) : Measurable (fun l => fe M i d l) := by
  unfold fe
  exact Measurable.ennreal_tsum fun n =>
    (ENNReal.measurable_ofReal.comp (Pw_meas M n)).mul_const _

theorem fe_le_one (i : I) (d : ℕ) (l : ℝ≥0) : fe M i d l ≤ 1 := by
  rw [← fe_sum M i l]
  exact ENNReal.le_tsum d

theorem demandMass_nonneg (i : I) (d : ℕ) (l : ℝ≥0) : 0 ≤ M.demandMass i d l := by
  unfold Model.demandMass
  exact tsum_nonneg fun n => mul_nonneg (Pw_nonneg M n l) (jumpDemandMass_nonneg M n i d)

theorem demandMass_eq (i : I) (d : ℕ) (l : ℝ≥0) : M.demandMass i d l = (fe M i d l).toReal := by
  rw [← fe_eq, ENNReal.toReal_ofReal (demandMass_nonneg M i d l)]

theorem demandMass_le_one (i : I) (d : ℕ) (l : ℝ≥0) : M.demandMass i d l ≤ 1 := by
  rw [demandMass_eq]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact fe_le_one M i d l)

theorem expα_le_one (l : ℝ≥0) : Real.exp (-M.α * (l : ℝ)) ≤ 1 := by
  rw [Real.exp_le_one_iff, neg_mul]
  have := mul_nonneg M.α_pos.le (NNReal.coe_nonneg l)
  linarith

theorem integrand_integrable (i : I) (d : ℕ) :
    Integrable (fun l : ℝ≥0 => Real.exp (-M.α * (l : ℝ)) * M.demandMass i d l) M.leadLaw := by
  haveI := M.lead_prob
  refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun l => ?_)
  · simp_rw [demandMass_eq]
    exact ((Continuous.measurable (by fun_prop)).mul (fe_meas M i d).ennreal_toReal).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (demandMass_nonneg M i d l))]
    exact mul_le_one₀ (expα_le_one M l) (demandMass_nonneg M i d l) (demandMass_le_one M i d l)

theorem exp_integrable :
    Integrable (fun l : ℝ≥0 => Real.exp (-M.α * (l : ℝ))) M.leadLaw := by
  haveI := M.lead_prob
  refine Integrable.of_bound (Continuous.measurable (by fun_prop)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun l => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact expα_le_one M l

noncomputable def ge (i : I) (d : ℕ) : ℝ≥0∞ := ENNReal.ofReal (M.discDemandMass i d)

theorem discDemandMass_nonneg (i : I) (d : ℕ) : 0 ≤ M.discDemandMass i d :=
  integral_nonneg fun l => mul_nonneg (Real.exp_pos _).le (demandMass_nonneg M i d l)

theorem ge_eq (i : I) (d : ℕ) :
    ge M i d = ∫⁻ l, ENNReal.ofReal (Real.exp (-M.α * (l : ℝ))) * fe M i d l ∂M.leadLaw := by
  unfold ge Model.discDemandMass
  rw [ofReal_integral_eq_lintegral_ofReal (integrand_integrable M i d)
    (Filter.Eventually.of_forall fun l => mul_nonneg (Real.exp_pos _).le (demandMass_nonneg M i d l))]
  congr 1; funext l
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, fe_eq]

theorem leadTransform_eq :
    ENNReal.ofReal M.leadTransform = ∫⁻ l, ENNReal.ofReal (Real.exp (-M.α * (l : ℝ))) ∂M.leadLaw := by
  unfold Model.leadTransform
  exact ofReal_integral_eq_lintegral_ofReal (exp_integrable M)
    (Filter.Eventually.of_forall fun l => (Real.exp_pos _).le)

theorem ge_sum (i : I) : ∑' d : ℕ, ge M i d = ENNReal.ofReal M.leadTransform := by
  simp_rw [ge_eq]
  have hm : ∀ d, AEMeasurable (fun l : ℝ≥0 => ENNReal.ofReal (Real.exp (-M.α * (l : ℝ))) *
      fe M i d l) M.leadLaw := fun d => ((ENNReal.measurable_ofReal.comp
    (Continuous.measurable (by fun_prop))).mul (fe_meas M i d)).aemeasurable
  rw [← lintegral_tsum hm]
  simp_rw [ENNReal.tsum_mul_left, fe_sum, mul_one]
  rw [leadTransform_eq]

theorem exp_mul_le (l : ℝ≥0) : Real.exp (-M.α * (l : ℝ)) * l ≤ 1 / M.α := by
  have hα := M.α_pos
  have h1 : M.α * (l : ℝ) ≤ Real.exp (M.α * (l : ℝ)) := by
    linarith [Real.add_one_le_exp (M.α * (l : ℝ))]
  calc Real.exp (-M.α * (l : ℝ)) * l = (Real.exp (-M.α * (l : ℝ)) * (M.α * l)) / M.α := by
        field_simp
    _ ≤ (Real.exp (-M.α * (l : ℝ)) * Real.exp (M.α * (l : ℝ))) / M.α := by gcongr
    _ = 1 / M.α := by rw [← Real.exp_add]; simp

theorem ge_mean (i : I) : ∑' d : ℕ, (d : ℝ≥0∞) * ge M i d ≤
    ENNReal.ofReal (sSup (Set.range M.lam) / M.α) := by
  haveI := M.lead_prob
  simp_rw [ge_eq]
  have hm : ∀ d : ℕ, AEMeasurable (fun l : ℝ≥0 => (d : ℝ≥0∞) *
      (ENNReal.ofReal (Real.exp (-M.α * (l : ℝ))) * fe M i d l)) M.leadLaw :=
    fun d => (((ENNReal.measurable_ofReal.comp
      (Continuous.measurable (by fun_prop))).mul (fe_meas M i d)).const_mul _).aemeasurable
  simp_rw [← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
  rw [← lintegral_tsum hm]
  · have hB := Lam_nonneg M
    calc ∫⁻ l, ∑' d : ℕ, (d : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp (-M.α * (l : ℝ))) * fe M i d l) ∂M.leadLaw
        = ∫⁻ l, ENNReal.ofReal (Real.exp (-M.α * (l : ℝ))) *
            ∑' d : ℕ, (d : ℝ≥0∞) * fe M i d l ∂M.leadLaw := by
          congr 1; funext l
          rw [← ENNReal.tsum_mul_left]
          congr 1; funext d; ring
      _ ≤ ∫⁻ _l, ENNReal.ofReal (sSup (Set.range M.lam) / M.α) ∂M.leadLaw := by
          refine lintegral_mono fun l => ?_
          calc ENNReal.ofReal (Real.exp (-M.α * (l : ℝ))) * ∑' d : ℕ, (d : ℝ≥0∞) * fe M i d l
              ≤ ENNReal.ofReal (Real.exp (-M.α * (l : ℝ))) *
                  ENNReal.ofReal (sSup (Set.range M.lam) * l) := by
                gcongr; exact fe_mean M i l
            _ = ENNReal.ofReal (sSup (Set.range M.lam) * (Real.exp (-M.α * (l : ℝ)) * l)) := by
                rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]; congr 1; ring
            _ ≤ ENNReal.ofReal (sSup (Set.range M.lam) / M.α) := by
                apply ENNReal.ofReal_le_ofReal
                rw [div_eq_mul_one_div]
                exact mul_le_mul_of_nonneg_left (exp_mul_le M l) hB
      _ = ENNReal.ofReal (sSup (Set.range M.lam) / M.α) := by
          rw [lintegral_const, measure_univ, mul_one]

end SZLDev


open scoped ENNReal NNReal
open MeasureTheory

namespace SZLDev

open _root_.SongZipkinFluct.Linear

variable {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)

theorem phi_pos : 0 < M.leadTransform := by
  haveI := M.lead_prob
  unfold Model.leadTransform
  exact integral_exp_pos (exp_integrable M)

theorem real_of_ennreal_sum {f : ℕ → ℝ} (hf : ∀ d, 0 ≤ f d) {B : ℝ} (hB : 0 ≤ B)
    (h : ∑' d, ENNReal.ofReal (f d) ≤ ENNReal.ofReal B) :
    Summable f ∧ ∑' d, f d ≤ B := by
  have hne : ∑' d, ENNReal.ofReal (f d) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hs : Summable f := by
    have := ENNReal.summable_toReal hne
    refine this.congr fun d => ?_
    rw [ENNReal.toReal_ofReal (hf d)]
  refine ⟨hs, ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg hf hs] at h
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp h

theorem g_summable (i : I) : Summable (M.discDemandMass i) ∧
    ∑' d, M.discDemandMass i d = M.leadTransform := by
  have h := ge_sum M i
  unfold ge at h
  obtain ⟨hs, _⟩ := real_of_ennreal_sum (discDemandMass_nonneg M i) (phi_pos M).le h.le
  refine ⟨hs, ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg (discDemandMass_nonneg M i) hs] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg (discDemandMass_nonneg M i))
    (phi_pos M).le).mp h

theorem gm_summable (i : I) : Summable (fun d : ℕ => M.discDemandMass i d * d) ∧
    ∑' d : ℕ, M.discDemandMass i d * d ≤ sSup (Set.range M.lam) / M.α := by
  have h := ge_mean M i
  unfold ge at h
  refine real_of_ennreal_sum (fun d => mul_nonneg (discDemandMass_nonneg M i d) (Nat.cast_nonneg d))
    (div_nonneg (Lam_nonneg M) M.α_pos.le)
    (le_trans (le_of_eq ?_) h)
  congr 1; funext d
  rw [ENNReal.ofReal_mul (discDemandMass_nonneg M i d), ENNReal.ofReal_natCast, mul_comm]

/-- First moment of discounted demand. -/
noncomputable def m1 (i : I) : ℝ := ∑' d : ℕ, M.discDemandMass i d * d

theorem m1_nonneg (i : I) : 0 ≤ m1 M i :=
  tsum_nonneg fun d => mul_nonneg (discDemandMass_nonneg M i d) (Nat.cast_nonneg d)

theorem m1_le (i : I) : m1 M i ≤ sSup (Set.range M.lam) / M.α := (gm_summable M i).2

/-! ### the inventory rate -/

theorem rate_ge_h (x : ℤ) : M.h * (x : ℝ) ≤ M.inventoryRate x := by
  unfold Model.inventoryRate
  split_ifs with hx
  · have : (x : ℝ) < 0 := by exact_mod_cast hx
    nlinarith [M.h_pos, M.p_pos]
  · exact le_rfl

theorem rate_ge_p (x : ℤ) : -M.p * (x : ℝ) ≤ M.inventoryRate x := by
  unfold Model.inventoryRate
  split_ifs with hx
  · exact le_rfl
  · have : (0 : ℝ) ≤ x := by exact_mod_cast (not_lt.mp hx)
    nlinarith [M.h_pos, M.p_pos]

theorem rate_nonpos_eq (x : ℤ) (hx : x ≤ 0) : M.inventoryRate x = -M.p * (x : ℝ) := by
  unfold Model.inventoryRate
  split_ifs with h
  · rfl
  · have : x = 0 := by omega
    subst this; simp

theorem rate_abs (x : ℤ) : |M.inventoryRate x| ≤ (M.p + M.h) * |(x : ℝ)| := by
  unfold Model.inventoryRate
  have hp := M.p_pos; have hh := M.h_pos
  split_ifs with hx
  · rw [abs_mul, abs_neg, abs_of_pos hp]
    nlinarith [abs_nonneg (x : ℝ)]
  · rw [abs_mul, abs_of_pos hh]
    nlinarith [abs_nonneg (x : ℝ)]

theorem rate_le_pos (y : ℤ) (hy : 0 ≤ y) (d : ℕ) :
    M.inventoryRate (y - d) ≤ M.h * y + M.p * d := by
  unfold Model.inventoryRate
  have hp := M.p_pos; have hh := M.h_pos
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
  split_ifs with hx
  · push_cast
    have : (y : ℝ) - d < 0 := by exact_mod_cast hx
    nlinarith
  · push_cast
    nlinarith

theorem C_summable (i : I) (y : ℤ) :
    Summable (fun d : ℕ => M.discDemandMass i d * M.inventoryRate (y - d)) := by
  have h0 := (g_summable M i).1
  have h1 := (gm_summable M i).1
  refine Summable.of_norm_bounded
    ((h0.mul_left ((M.p + M.h) * |(y : ℝ)|)).add (h1.mul_left (M.p + M.h))) (fun d => ?_)
  have hg := discDemandMass_nonneg M i d
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg]
  have hr := rate_abs M (y - d)
  have : |((y - d : ℤ) : ℝ)| ≤ |(y : ℝ)| + d := by
    push_cast
    calc |(y : ℝ) - d| ≤ |(y : ℝ)| + |(d : ℝ)| := abs_sub _ _
      _ = |(y : ℝ)| + d := by rw [Nat.abs_cast]
  have hph : 0 ≤ M.p + M.h := by linarith [M.p_pos, M.h_pos]
  calc M.discDemandMass i d * |M.inventoryRate (y - d)|
      ≤ M.discDemandMass i d * ((M.p + M.h) * (|(y : ℝ)| + d)) :=
        mul_le_mul_of_nonneg_left (hr.trans (mul_le_mul_of_nonneg_left this hph)) hg
    _ = (M.p + M.h) * |(y : ℝ)| * M.discDemandMass i d + (M.p + M.h) *
          (M.discDemandMass i d * d) := by ring

theorem C_nonpos_eq (i : I) (y : ℤ) (hy : y ≤ 0) :
    M.C i y = M.p * (m1 M i - y * M.leadTransform) := by
  unfold Model.C m1
  have e : ∀ d : ℕ, M.discDemandMass i d * M.inventoryRate (y - d) =
      M.p * (M.discDemandMass i d * d) - (M.p * y) * M.discDemandMass i d := by
    intro d
    rw [rate_nonpos_eq M _ (by omega)]
    push_cast; ring
  simp_rw [e]
  rw [Summable.tsum_sub (((gm_summable M i).1).mul_left _) (((g_summable M i).1).mul_left _),
    tsum_mul_left, tsum_mul_left, (g_summable M i).2]
  ring

theorem C_ge_h (i : I) (y : ℤ) : M.h * (y * M.leadTransform - m1 M i) ≤ M.C i y := by
  unfold Model.C m1
  have hs : Summable (fun d : ℕ => M.h * y * M.discDemandMass i d - M.h * (M.discDemandMass i d * d)) :=
    (((g_summable M i).1).mul_left _).sub (((gm_summable M i).1).mul_left _)
  have : ∑' d : ℕ, (M.h * y * M.discDemandMass i d - M.h * (M.discDemandMass i d * d)) =
      M.h * (y * M.leadTransform - ∑' d : ℕ, M.discDemandMass i d * d) := by
    rw [Summable.tsum_sub (((g_summable M i).1).mul_left _) (((gm_summable M i).1).mul_left _),
      tsum_mul_left, tsum_mul_left, (g_summable M i).2]
    ring
  rw [← this]
  refine hs.tsum_le_tsum (fun d => ?_) (C_summable M i y)
  have := mul_le_mul_of_nonneg_left (rate_ge_h M (y - d)) (discDemandMass_nonneg M i d)
  push_cast at this
  linarith

theorem C_nonneg (i : I) (y : ℤ) : 0 ≤ M.C i y := by
  unfold Model.C
  refine tsum_nonneg fun d => mul_nonneg (discDemandMass_nonneg M i d) ?_
  unfold Model.inventoryRate
  have hp := M.p_pos; have hh := M.h_pos
  split_ifs with hx
  · have : ((y - d : ℤ) : ℝ) < 0 := by exact_mod_cast hx
    nlinarith
  · have : (0 : ℝ) ≤ ((y - d : ℤ) : ℝ) := by exact_mod_cast (not_lt.mp hx)
    nlinarith

theorem C_le_pos (i : I) (y : ℤ) (hy : 0 ≤ y) :
    M.C i y ≤ M.h * y * M.leadTransform + M.p * (sSup (Set.range M.lam) / M.α) := by
  unfold Model.C
  have hs : Summable (fun d : ℕ => M.h * y * M.discDemandMass i d + M.p * (M.discDemandMass i d * d)) :=
    (((g_summable M i).1).mul_left _).add (((gm_summable M i).1).mul_left _)
  calc ∑' d : ℕ, M.discDemandMass i d * M.inventoryRate (y - d)
      ≤ ∑' d : ℕ, (M.h * y * M.discDemandMass i d + M.p * (M.discDemandMass i d * d)) := by
        refine (C_summable M i y).tsum_le_tsum (fun d => ?_) hs
        have := mul_le_mul_of_nonneg_left (rate_le_pos M y hy d) (discDemandMass_nonneg M i d)
        linarith
    _ = M.h * y * M.leadTransform + M.p * m1 M i := by
        rw [Summable.tsum_add (((g_summable M i).1).mul_left _) (((gm_summable M i).1).mul_left _),
          tsum_mul_left, tsum_mul_left, (g_summable M i).2]
        rfl
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (m1_le M i) M.p_pos.le) _

theorem C_delta_neg (i : I) (y : ℤ) (hy : y < 0) :
    M.C i (y + 1) - M.C i y = -M.p * M.leadTransform := by
  rw [C_nonpos_eq M i _ (by omega), C_nonpos_eq M i _ hy.le]
  push_cast; ring

end SZLDev


open scoped ENNReal NNReal
open MeasureTheory

namespace SZLDev

open _root_.SongZipkinFluct.Linear

/-! ### Integer convexity -/

theorem cv_mono {f : ℤ → ℝ} (hf : IntConvex f) {a b : ℤ} (hab : a ≤ b) :
    f (a + 1) - f a ≤ f (b + 1) - f b := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, b = a + t := ⟨(b - a).toNat, by omega⟩
  induction t with
  | zero => simp
  | succ t ih =>
    have h := hf (a + t)
    have e1 : a + ((t + 1 : ℕ) : ℤ) = a + t + 1 := by push_cast; ring
    have e2 : a + (t : ℤ) + 2 = a + t + 1 + 1 := by ring
    rw [e1]; rw [e2] at h
    linarith [ih (by omega)]

theorem cv_right {f : ℤ → ℝ} (hf : IntConvex f) {s : ℤ} (hs : ∀ w, f s ≤ f w) {k : ℤ}
    (hk : s ≤ k) : 0 ≤ f (k + 1) - f k := by
  by_contra hneg
  push_neg at hneg
  have key : ∀ t : ℕ, f (k + 1) < f (k - t) := by
    intro t
    induction t with
    | zero => simp; linarith
    | succ t ih =>
      have hd := cv_mono hf (show k - ((t + 1 : ℕ) : ℤ) ≤ k by omega)
      have e : k - ((t + 1 : ℕ) : ℤ) + 1 = k - t := by push_cast; ring
      rw [e] at hd
      linarith
  have := key (k - s).toNat
  have e : k - ((k - s).toNat : ℤ) = s := by omega
  rw [e] at this
  linarith [hs (k + 1)]

theorem cv_mono_right {f : ℤ → ℝ} (hf : IntConvex f) {s : ℤ} (hs : ∀ w, f s ≤ f w) {x y : ℤ}
    (hx : s ≤ x) (hxy : x ≤ y) : f x ≤ f y := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, y = x + t := ⟨(y - x).toNat, by omega⟩
  induction t with
  | zero => simp
  | succ t ih =>
    have := cv_right hf hs (show s ≤ x + t by omega)
    have e : x + ((t + 1 : ℕ) : ℤ) = x + t + 1 := by push_cast; ring
    rw [e]
    linarith [ih (by omega)]

theorem cv_left_neg {f : ℤ → ℝ} (hf : IntConvex f) {s : ℤ} (hs : SmallestMinimizer f s) {y : ℤ}
    (hy : y < s) : f (y + 1) - f y < 0 := by
  by_contra hneg
  push_neg at hneg
  have hmono : ∀ t : ℕ, f y ≤ f (y + t) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have := cv_mono hf (show y ≤ y + t by omega)
      have e : y + ((t + 1 : ℕ) : ℤ) = y + t + 1 := by push_cast; ring
      rw [e]
      linarith
  have h1 := hmono (s - y).toNat
  have e : y + ((s - y).toNat : ℤ) = s := by omega
  rw [e] at h1
  have hmin : ∀ w, f y ≤ f w := fun w => h1.trans (hs.1 w)
  have := hs.2 hmin
  omega

theorem cv_le_of_delta {g : ℤ → ℝ} (hg : IntConvex g) {s' s : ℤ} (hs' : SmallestMinimizer g s')
    (hd : 0 ≤ g (s + 1) - g s) : s' ≤ s := by
  by_contra h
  push_neg at h
  have := cv_left_neg hg hs' h
  linarith

theorem cv_max_le {f : ℤ → ℝ} (hf : IntConvex f) {s : ℤ} (hs : ∀ w, f s ≤ f w) {x y : ℤ}
    (hxy : x ≤ y) : f (max x s) ≤ f y := by
  rcases le_total s x with h | h
  · rw [max_eq_left h]; exact cv_mono_right hf hs h hxy
  · rw [max_eq_right h]; exact hs y

theorem cv_delta_max {f : ℤ → ℝ} (hf : IntConvex f) {s : ℤ} (hs : ∀ w, f s ≤ f w) (x : ℤ) :
    f (max (x + 1) s) - f (max x s) = if x < s then 0 else f (x + 1) - f x := by
  split_ifs with h
  · rw [max_eq_right (by omega), max_eq_right (by omega)]; ring
  · rw [max_eq_left (by omega), max_eq_left (by omega)]

theorem cv_max_convex {f : ℤ → ℝ} (hf : IntConvex f) {s : ℤ} (hs : ∀ w, f s ≤ f w) :
    IntConvex (fun x => f (max x s)) := by
  intro x
  show f (max (x + 1) s) - f (max x s) ≤ f (max (x + 2) s) - f (max (x + 1) s)
  have e : x + 2 = x + 1 + 1 := by ring
  rw [e, cv_delta_max hf hs, cv_delta_max hf hs]
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact cv_right hf hs (by omega)
  · omega
  · have := hf x; rw [e] at this; exact this

theorem cv_max_delta_nonneg {f : ℤ → ℝ} (hf : IntConvex f) {s : ℤ} (hs : ∀ w, f s ≤ f w)
    (x : ℤ) : 0 ≤ f (max (x + 1) s) - f (max x s) := by
  rw [cv_delta_max hf hs]
  split_ifs with h
  · exact le_rfl
  · exact cv_right hf hs (by omega)

/-! ### Coercivity and minimizers -/

theorem coercive_of_bounds {f : ℤ → ℝ} {a b a' b' : ℝ} (ha : 0 < a) (ha' : 0 < a')
    (h1 : ∀ y : ℤ, 0 ≤ y → a * y - b ≤ f y) (h2 : ∀ y : ℤ, y ≤ 0 → a' * (-(y : ℝ)) - b' ≤ f y) :
    CoerciveInt f := by
  constructor
  · rw [Filter.tendsto_atTop_atTop]
    intro c
    refine ⟨max 0 ⌈(c + b) / a⌉, fun y hy => ?_⟩
    have hy0 : 0 ≤ y := le_trans (le_max_left _ _) hy
    have hy1 : ((c + b) / a) ≤ y := (Int.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hy)
    have := h1 y hy0
    rw [div_le_iff₀ ha] at hy1
    linarith
  · rw [Filter.tendsto_atBot_atTop]
    intro c
    refine ⟨min 0 (-⌈(c + b') / a'⌉), fun y hy => ?_⟩
    have hy0 : y ≤ 0 := le_trans hy (min_le_left _ _)
    have hy1 : ((c + b') / a') ≤ -(y : ℝ) := (Int.le_ceil _).trans (by
      have := le_trans hy (min_le_right _ _)
      have : ⌈(c + b') / a'⌉ ≤ -y := by omega
      exact_mod_cast this)
    have := h2 y hy0
    rw [div_le_iff₀ ha'] at hy1
    linarith

theorem coercive_mono {f g : ℤ → ℝ} (hf : CoerciveInt f) (hfg : ∀ y, f y ≤ g y) :
    CoerciveInt g :=
  ⟨Filter.tendsto_atTop_mono hfg hf.1, Filter.tendsto_atTop_mono hfg hf.2⟩

theorem exists_smallest_minimizer {f : ℤ → ℝ} (hf : CoerciveInt f) :
    ∃ s, SmallestMinimizer f s := by
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (hf.1.eventually_gt_atTop (f 0))
  obtain ⟨N2, hN2⟩ := Filter.eventually_atBot.mp (hf.2.eventually_gt_atTop (f 0))
  have hN1' : 0 < N1 := by
    by_contra h; push_neg at h; have := hN1 0 h; linarith
  have hN2' : N2 < 0 := by
    by_contra h; push_neg at h; have := hN2 0 h; linarith
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.Icc N2 N1) f
    ⟨0, Finset.mem_Icc.mpr ⟨hN2'.le, hN1'.le⟩⟩
  have h0 : f m ≤ f 0 := hmin 0 (Finset.mem_Icc.mpr ⟨hN2'.le, hN1'.le⟩)
  have hglob : ∀ w, f m ≤ f w := by
    intro w
    by_cases hw1 : N1 ≤ w
    · linarith [hN1 w hw1]
    by_cases hw2 : w ≤ N2
    · linarith [hN2 w hw2]
    exact hmin w (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  obtain ⟨lb, hlb, hlbmin⟩ := Int.exists_least_of_bdd (P := fun z => ∀ w, f z ≤ f w)
    ⟨N2, fun z hz => by
      by_contra h; push_neg at h
      have := hN2 z h.le; linarith [hz 0]⟩ ⟨m, hglob⟩
  exact ⟨lb, hlb, fun z hz => hlbmin z hz⟩

theorem smallest_unique {f : ℤ → ℝ} {s t : ℤ} (hs : SmallestMinimizer f s)
    (ht : SmallestMinimizer f t) : s = t :=
  le_antisymm (hs.2 ht.1) (ht.2 hs.1)

theorem smallest_add_const {f : ℤ → ℝ} {s : ℤ} (c : ℝ) (hs : SmallestMinimizer f s) :
    SmallestMinimizer (fun y => f y + c) s := by
  refine ⟨fun w => by simp only; linarith [hs.1 w], fun z hz => hs.2 fun w => ?_⟩
  have := hz w
  simp only at this
  linarith

end SZLDev


open scoped ENNReal NNReal
open MeasureTheory

namespace SZLDev

open _root_.SongZipkinFluct.Linear

variable {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)

theorem beta_pos : 0 < M.beta := by
  unfold Model.beta; exact div_pos one_pos (add_pos M.μ_pos M.α_pos)

theorem one_sub_gamma : 1 - M.gamma = M.α * M.beta := by
  unfold Model.gamma Model.beta
  have : M.μ + M.α ≠ 0 := (add_pos M.μ_pos M.α_pos).ne'
  field_simp; ring

theorem gamma_nonneg : 0 ≤ M.gamma := by
  unfold Model.gamma; exact mul_nonneg (beta_pos M).le M.μ_pos.le

theorem gamma_lt_one : M.gamma < 1 := by
  have := one_sub_gamma M
  have := mul_pos M.α_pos (beta_pos M)
  linarith

theorem c_nonneg : 0 ≤ M.c := by
  unfold Model.c; exact mul_nonneg M.cbar_nonneg (phi_pos M).le

theorem tendsto_top_of_bound {f : ℤ → ℝ} {a b : ℝ} (ha : 0 < a)
    (h1 : ∀ y : ℤ, 0 ≤ y → a * y - b ≤ f y) : Filter.Tendsto f Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro c
  refine ⟨max 0 ⌈(c + b) / a⌉, fun y hy => ?_⟩
  have hy0 : 0 ≤ y := le_trans (le_max_left _ _) hy
  have hy1 : ((c + b) / a) ≤ y :=
    (Int.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hy)
  have := h1 y hy0
  rw [div_le_iff₀ ha] at hy1
  linarith

theorem Gplus_ge_pos (i : I) (y : ℤ) (hy : 0 ≤ y) :
    M.beta * M.h * M.leadTransform * y - M.beta * M.h * (sSup (Set.range M.lam) / M.α) ≤
      M.Gplus i y := by
  unfold Model.Gplus
  have h1 := C_ge_h M i y
  have h2 := m1_le M i
  have hb := beta_pos M
  have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
  have h3 : 0 ≤ (1 - M.gamma) * M.c * (y : ℝ) :=
    mul_nonneg (mul_nonneg (by linarith [gamma_lt_one M]) (c_nonneg M)) hy'
  have h4 : M.beta * (M.h * (y * M.leadTransform - m1 M i)) ≤ M.beta * M.C i y :=
    mul_le_mul_of_nonneg_left h1 hb.le
  have h5 : M.beta * M.h * m1 M i ≤ M.beta * M.h * (sSup (Set.range M.lam) / M.α) :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hb.le M.h_pos.le)
  nlinarith

theorem Gplus_nonpos_eq (i : I) (y : ℤ) (hy : y ≤ 0) :
    M.Gplus i y = M.beta * M.leadTransform * (M.α * M.cbar - M.p) * y + M.beta * M.p * m1 M i := by
  unfold Model.Gplus
  rw [C_nonpos_eq M i y hy, one_sub_gamma]
  unfold Model.c
  ring

theorem C_delta_ge (i : I) (y : ℤ) : -M.p * M.leadTransform ≤ M.C i (y + 1) - M.C i y := by
  unfold Model.C
  rw [← Summable.tsum_sub (C_summable M i (y + 1)) (C_summable M i y), ← (g_summable M i).2,
    ← tsum_mul_left]
  refine (((g_summable M i).1).mul_left _).tsum_le_tsum (fun d => ?_)
    ((C_summable M i (y + 1)).sub (C_summable M i y))
  have e : y + 1 - (d : ℤ) = y - d + 1 := by ring
  rw [e, ← mul_sub]
  have hr := rate_succ_sub' M (y - d)
  rw [mul_comm (-M.p)]
  exact mul_le_mul_of_nonneg_left hr (discDemandMass_nonneg M i d)
where
  rate_succ_sub' (M : Model I) (x : ℤ) : -M.p ≤ M.inventoryRate (x + 1) - M.inventoryRate x := by
    unfold Model.inventoryRate
    have hp := M.p_pos; have hh := M.h_pos
    split_ifs with h1 h2 h2
    · push_cast; linarith
    · omega
    · have : x = -1 := by omega
      subst this; push_cast; linarith
    · push_cast; linarith

theorem Gplus_delta (i : I) (y : ℤ) :
    M.Gplus i (y + 1) - M.Gplus i y = M.α * M.beta * M.c + M.beta * (M.C i (y + 1) - M.C i y) := by
  unfold Model.Gplus
  rw [one_sub_gamma]
  push_cast; ring

theorem Gplus_delta_neg (hA : M.Assumption1) (i : I) (y : ℤ) (hy : y < 0) :
    M.Gplus i (y + 1) - M.Gplus i y < 0 := by
  rw [Gplus_delta, C_delta_neg M i y hy]
  unfold Model.c
  have hb := beta_pos M; have hφ := phi_pos M
  unfold Model.Assumption1 at hA
  have : M.α * M.beta * (M.cbar * M.leadTransform) + M.beta * (-M.p * M.leadTransform) =
      M.beta * M.leadTransform * (M.α * M.cbar - M.p) := by ring
  rw [this]
  exact mul_neg_of_pos_of_neg (mul_pos hb hφ) (by linarith)

theorem Gplus_nonneg (hA : M.Assumption1) (i : I) (y : ℤ) : 0 ≤ M.Gplus i y := by
  rcases le_total 0 y with hy | hy
  · unfold Model.Gplus
    have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
    exact add_nonneg (mul_nonneg (mul_nonneg (by linarith [gamma_lt_one M]) (c_nonneg M)) hy')
      (mul_nonneg (beta_pos M).le (C_nonneg M i y))
  · rw [Gplus_nonpos_eq M i y hy]
    unfold Model.Assumption1 at hA
    have hy' : (y : ℝ) ≤ 0 := by exact_mod_cast hy
    have h1 : 0 ≤ M.beta * M.leadTransform * (M.α * M.cbar - M.p) * y :=
      mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos
        (mul_pos (beta_pos M) (phi_pos M)).le (by linarith)) hy'
    exact add_nonneg h1 (mul_nonneg (mul_nonneg (beta_pos M).le M.p_pos.le) (m1_nonneg M i))

theorem Gplus_coercive (hA : M.Assumption1) (i : I) : CoerciveInt (M.Gplus i) := by
  unfold Model.Assumption1 at hA
  refine coercive_of_bounds (a := M.beta * M.h * M.leadTransform)
    (b := M.beta * M.h * (sSup (Set.range M.lam) / M.α))
    (a' := M.beta * M.leadTransform * (M.p - M.α * M.cbar)) (b' := 0)
    (mul_pos (mul_pos (beta_pos M) M.h_pos) (phi_pos M))
    (mul_pos (mul_pos (beta_pos M) (phi_pos M)) (by linarith))
    (fun y hy => Gplus_ge_pos M i y hy) (fun y hy => ?_)
  rw [Gplus_nonpos_eq M i y hy]
  have := mul_nonneg (mul_nonneg (beta_pos M).le M.p_pos.le) (m1_nonneg M i)
  nlinarith

/-- A uniform (in the world state) linear upper bound on the myopic cost on `y ≥ 0`. -/
theorem Gplus_upper (i : I) (y : ℤ) (hy : 0 ≤ y) :
    M.Gplus i y ≤ M.beta * M.p * (sSup (Set.range M.lam) / M.α) +
      ((1 - M.gamma) * M.c + M.beta * M.h * M.leadTransform) * y := by
  unfold Model.Gplus
  have := C_le_pos M i y hy
  have hb := beta_pos M
  have := mul_le_mul_of_nonneg_left this hb.le
  nlinarith

theorem lemma2_proof : ∀ i : I, CoerciveInt (M.C i) ∧
      Filter.Tendsto (M.Gplus i) Filter.atTop Filter.atTop ∧
      (M.Assumption1 → Filter.Tendsto (M.Gplus i) Filter.atBot Filter.atTop) := by
  intro i
  refine ⟨?_, ?_, fun hA => (Gplus_coercive M hA i).2⟩
  · refine coercive_of_bounds (a := M.h * M.leadTransform)
      (b := M.h * (sSup (Set.range M.lam) / M.α))
      (a' := M.p * M.leadTransform) (b' := 0)
      (mul_pos M.h_pos (phi_pos M)) (mul_pos M.p_pos (phi_pos M))
      (fun y _ => ?_) (fun y hy => ?_)
    · have h1 := C_ge_h M i y
      have h2 := mul_le_mul_of_nonneg_left (m1_le M i) M.h_pos.le
      nlinarith
    · rw [C_nonpos_eq M i y hy]
      have := mul_nonneg M.p_pos.le (m1_nonneg M i)
      nlinarith
  · exact tendsto_top_of_bound (mul_pos (mul_pos (beta_pos M) M.h_pos) (phi_pos M))
      (fun y hy => Gplus_ge_pos M i y hy)

theorem corollary1_proof :
    (M.p ≤ M.α * M.cbar → ∀ i : I, Monotone (M.Gplus i)) ∧
    (M.Assumption1 → ∀ i : I,
      (∃ y : ℤ, SmallestMinimizer (M.Gplus i) y ∧ 0 ≤ y) ∧
      ∀ y : ℤ, 0 ≤ M.Gplus i y) := by
  refine ⟨fun hp i => monotone_int_of_le_succ fun y => ?_, fun hA i => ⟨?_, Gplus_nonneg M hA i⟩⟩
  · have h := Gplus_delta M i y
    have h2 := C_delta_ge M i y
    have hb := beta_pos M
    have h3 := mul_le_mul_of_nonneg_left h2 hb.le
    unfold Model.c at h
    have : 0 ≤ M.beta * M.leadTransform * (M.α * M.cbar - M.p) :=
      mul_nonneg (mul_pos hb (phi_pos M)).le (by linarith)
    nlinarith
  · obtain ⟨s, hs⟩ := exists_smallest_minimizer (Gplus_coercive M hA i)
    refine ⟨s, hs, ?_⟩
    by_contra h
    push_neg at h
    have := Gplus_delta_neg M hA i s h
    linarith [hs.1 (s + 1)]

end SZLDev


open scoped ENNReal NNReal
open MeasureTheory

namespace SZLDev

open _root_.SongZipkinFluct.Linear

variable {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)

/-! ### myopic levels -/

theorem yplus_exists (hA : M.Assumption1) (i : I) :
    ∃ y : ℤ, SmallestMinimizer (M.Gplus i) y ∧ 0 ≤ y := ((corollary1_proof M).2 hA i).1

noncomputable def yplus (hA : M.Assumption1) (i : I) : ℤ := Classical.choose (yplus_exists M hA i)

theorem yplus_spec (hA : M.Assumption1) (i : I) :
    SmallestMinimizer (M.Gplus i) (yplus M hA i) ∧ 0 ≤ yplus M hA i :=
  Classical.choose_spec (yplus_exists M hA i)

theorem ymin_exists (hA : M.Assumption1) : ∃ m : ℤ, IsLeast (Set.range (yplus M hA)) m := by
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  obtain ⟨lb, hlb, hmin⟩ := Int.exists_least_of_bdd (P := fun z => z ∈ Set.range (yplus M hA))
    ⟨0, fun z ⟨j, hj⟩ => hj ▸ (yplus_spec M hA j).2⟩ ⟨_, Set.mem_range_self i⟩
  exact ⟨lb, hlb, fun z hz => hmin z hz⟩

noncomputable def ymin (hA : M.Assumption1) : ℤ := Classical.choose (ymin_exists M hA)

theorem ymin_spec (hA : M.Assumption1) : IsLeast (Set.range (yplus M hA)) (ymin M hA) :=
  Classical.choose_spec (ymin_exists M hA)

theorem ymin_le (hA : M.Assumption1) (i : I) : ymin M hA ≤ yplus M hA i :=
  (ymin_spec M hA).2 (Set.mem_range_self i)

theorem ymin_nonneg (hA : M.Assumption1) : 0 ≤ ymin M hA := by
  obtain ⟨j, hj⟩ := (ymin_spec M hA).1
  rw [← hj]; exact (yplus_spec M hA j).2

theorem rate_succ_sub2 (x : ℤ) : M.inventoryRate (x + 1) - M.inventoryRate x =
    if x < 0 then -M.p else M.h := by
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

theorem C_intConvex (i : I) : IntConvex (M.C i) := by
  intro y
  unfold Model.C
  have e2 : y + 2 = y + 1 + 1 := by ring
  rw [e2]
  rw [← Summable.tsum_sub (C_summable M i (y + 1)) (C_summable M i y),
    ← Summable.tsum_sub (C_summable M i (y + 1 + 1)) (C_summable M i (y + 1))]
  refine ((C_summable M i (y + 1)).sub (C_summable M i y)).tsum_le_tsum (fun d => ?_)
    ((C_summable M i (y + 1 + 1)).sub (C_summable M i (y + 1)))
  rw [← mul_sub, ← mul_sub]
  refine mul_le_mul_of_nonneg_left ?_ (discDemandMass_nonneg M i d)
  have e1 : y + 1 - (d : ℤ) = y - d + 1 := by ring
  have e3 : y + 1 + 1 - (d : ℤ) = y - d + 1 + 1 := by ring
  rw [e1, e3]
  have h0 := rate_succ_sub2 M (y - d)
  have h1 := rate_succ_sub2 M (y - d + 1)
  have hp := M.p_pos; have hh := M.h_pos
  split_ifs at h0 h1 <;> first | (exfalso; omega) | linarith

theorem Gplus_convex (i : I) : IntConvex (M.Gplus i) := by
  intro y
  have hC := C_intConvex M i y
  have hβ : 0 ≤ M.beta := (beta_pos M).le
  unfold Model.Gplus
  push_cast
  linarith [mul_le_mul_of_nonneg_left hC hβ]

theorem Gplus_delta_lt (hA : M.Assumption1) (i : I) (y : ℤ) (hy : y < ymin M hA) :
    M.Gplus i (y + 1) - M.Gplus i y < 0 :=
  cv_left_neg (Gplus_convex M i) (yplus_spec M hA i).1 (lt_of_lt_of_le hy (ymin_le M hA i))


/-! ### the uniform bound -/

noncomputable def Acst : ℝ :=
  M.beta * M.p * (sSup (Set.range M.lam) / M.α) + M.beta * sSup (Set.range M.lam) * M.c

noncomputable def Bcst : ℝ := (1 - M.gamma) * M.c + M.beta * M.h * M.leadTransform

noncomputable def Fb (x : ℤ) : ℝ := (Acst M + Bcst M * (max x 0 : ℤ)) / (1 - M.gamma)

theorem Acst_nonneg : 0 ≤ Acst M := by
  unfold Acst
  have := beta_pos M; have := Lam_nonneg M; have := c_nonneg M; have := M.p_pos; have := M.α_pos
  positivity

theorem Bcst_nonneg : 0 ≤ Bcst M := by
  unfold Bcst
  have := beta_pos M; have := c_nonneg M; have := M.h_pos; have := phi_pos M
  have := gamma_lt_one M
  have : 0 ≤ 1 - M.gamma := by linarith
  positivity

theorem Fb_nonneg (x : ℤ) : 0 ≤ Fb M x := by
  unfold Fb
  have := Acst_nonneg M; have := Bcst_nonneg M
  have : 0 < 1 - M.gamma := by linarith [gamma_lt_one M]
  have : (0 : ℝ) ≤ ((max x 0 : ℤ) : ℝ) := by exact_mod_cast le_max_right x 0
  positivity

theorem Fb_mono : Monotone (Fb M) := by
  intro x y hxy
  unfold Fb
  have : 0 < 1 - M.gamma := by linarith [gamma_lt_one M]
  have h1 : ((max x 0 : ℤ) : ℝ) ≤ ((max y 0 : ℤ) : ℝ) := by exact_mod_cast max_le_max hxy le_rfl
  have := Bcst_nonneg M
  gcongr

theorem Fb_max (x : ℤ) : Fb M (max x 0) = Fb M x := by
  unfold Fb; rw [max_eq_left (le_max_right x 0)]

theorem Fb_fix (x : ℤ) (hx : 0 ≤ x) :
    Acst M + Bcst M * x + M.gamma * Fb M x = Fb M x := by
  unfold Fb
  rw [max_eq_left hx]
  have : 1 - M.gamma ≠ 0 := by linarith [gamma_lt_one M]
  field_simp
  ring

/-! ### the expectation operator -/

/-- The bracket in `contG`. -/
noncomputable def Ex (U : I → ℤ → ℝ) (i : I) (y : ℤ) : ℝ :=
  M.lam i * U i (y - 1) + (∑' j : {j : I // j ≠ i}, M.Q i j.1 * U j.1 y) +
    (M.μ - M.lam i + M.Q i i) * U i y

theorem contG_eq (U : I → ℤ → ℝ) (i : I) (y : ℤ) :
    M.contG U i y = M.Gplus i y + M.beta * M.lam i * M.c + M.beta * Ex M U i y := rfl

theorem summ_of_bdd {U : I → ℤ → ℝ} {y : ℤ} {B : ℝ} (hU : ∀ j, |U j y| ≤ B) (i : I) :
    Summable (fun j : {j : I // j ≠ i} => M.Q i j.1 * U j.1 y) :=
  summable_Qmul M i (fun j => hU j.1)

theorem Ex_nonneg {U : I → ℤ → ℝ} (h0 : ∀ j z, 0 ≤ U j z) (i : I) (y : ℤ) : 0 ≤ Ex M U i y := by
  unfold Ex
  exact add_nonneg (add_nonneg (mul_nonneg (M.lam_nonneg i) (h0 _ _))
    (tsum_nonneg fun j => mul_nonneg (Qoff_nonneg M i j) (h0 _ _)))
    (mul_nonneg (self_nonneg' M i) (h0 _ _))

/-- Monotonicity of the bracket. -/
theorem Ex_mono {U V : I → ℤ → ℝ} {y : ℤ} {B : ℝ} (hU : ∀ j, |U j y| ≤ B) (hV : ∀ j, |V j y| ≤ B)
    (i : I) (h1 : U i (y - 1) ≤ V i (y - 1)) (h2 : ∀ j, U j y ≤ V j y) :
    Ex M U i y ≤ Ex M V i y := by
  unfold Ex
  have h3 : (∑' j : {j : I // j ≠ i}, M.Q i j.1 * U j.1 y) ≤
      ∑' j : {j : I // j ≠ i}, M.Q i j.1 * V j.1 y :=
    (summ_of_bdd M hU i).tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (h2 j.1)
      (Qoff_nonneg M i j)) (summ_of_bdd M hV i)
  have := mul_le_mul_of_nonneg_left h1 (M.lam_nonneg i)
  have := mul_le_mul_of_nonneg_left (h2 i) (self_nonneg' M i)
  linarith

/-- Upper bound of the bracket by a constant bound. -/
theorem Ex_le {U : I → ℤ → ℝ} {y : ℤ} {B : ℝ} (h0 : ∀ j z, 0 ≤ U j z)
    (hU1 : ∀ j, U j y ≤ B) (hU2 : ∀ j, U j (y - 1) ≤ B) (i : I) :
    Ex M U i y ≤ M.μ * B := by
  have hB : 0 ≤ B := (h0 i y).trans (hU1 i)
  have hab : ∀ j, |U j y| ≤ B := fun j => by rw [abs_of_nonneg (h0 _ _)]; exact hU1 j
  have hcon : ∀ j, |(fun (_ : I) (_ : ℤ) => B) j y| ≤ B := fun j => by simp [abs_of_nonneg hB]
  have := Ex_mono M (V := fun _ _ => B) hab hcon i (hU2 i) hU1
  refine this.trans (le_of_eq ?_)
  unfold Ex
  rw [tsum_mul_right, qsum]
  ring

/-- The difference of the bracket. -/
theorem Ex_delta {U : I → ℤ → ℝ} {y : ℤ} {B B' : ℝ} (hU0 : ∀ j, |U j y| ≤ B)
    (hU1 : ∀ j, |U j (y + 1)| ≤ B') (i : I) :
    Ex M U i (y + 1) - Ex M U i y =
      M.lam i * (U i y - U i (y - 1)) +
      (∑' j : {j : I // j ≠ i}, M.Q i j.1 * (U j.1 (y + 1) - U j.1 y)) +
      (M.μ - M.lam i + M.Q i i) * (U i (y + 1) - U i y) := by
  unfold Ex
  simp_rw [mul_sub]
  rw [Summable.tsum_sub (summ_of_bdd M hU1 i) (summ_of_bdd M hU0 i)]
  simp only [add_sub_cancel_right]
  ring

theorem bdd_of_F {W : I → ℤ → ℝ} (h0 : ∀ j z, 0 ≤ W j z) (hF : ∀ j z, W j z ≤ Fb M z) (y : ℤ) :
    ∀ j, |W j y| ≤ Fb M y := fun j => by rw [abs_of_nonneg (h0 _ _)]; exact hF j y

/-! ### the inductive invariant -/

structure Good (hA : M.Assumption1) (W : I → ℤ → ℝ) : Prop where
  nonneg : ∀ i x, 0 ≤ W i x
  bound : ∀ i x, W i x ≤ Fb M x
  convex : ∀ i, IntConvex (W i)
  mono : ∀ i x, 0 ≤ W i (x + 1) - W i x
  flat : ∀ i x, x < ymin M hA → W i (x + 1) - W i x = 0

variable {M}

theorem contG_delta (hA : M.Assumption1) {W : I → ℤ → ℝ} (hW : Good M hA W) (i : I) (y : ℤ) :
    M.contG W i (y + 1) - M.contG W i y =
      (M.Gplus i (y + 1) - M.Gplus i y) + M.beta * (
      M.lam i * (W i y - W i (y - 1)) +
      (∑' j : {j : I // j ≠ i}, M.Q i j.1 * (W j.1 (y + 1) - W j.1 y)) +
      (M.μ - M.lam i + M.Q i i) * (W i (y + 1) - W i y)) := by
  rw [contG_eq, contG_eq, ← Ex_delta M (bdd_of_F M hW.nonneg hW.bound y)
    (bdd_of_F M hW.nonneg hW.bound (y + 1)) i]
  ring

theorem contG_ge (hA : M.Assumption1) {W : I → ℤ → ℝ} (hW : Good M hA W) (i : I) (y : ℤ) :
    M.Gplus i y ≤ M.contG W i y := by
  rw [contG_eq]
  have := Ex_nonneg M hW.nonneg i y
  have := mul_nonneg (mul_nonneg (beta_pos M).le (M.lam_nonneg i)) (c_nonneg M)
  have := mul_nonneg (beta_pos M).le (Ex_nonneg M hW.nonneg i y)
  linarith

theorem contG_nonneg (hA : M.Assumption1) {W : I → ℤ → ℝ} (hW : Good M hA W) (i : I) (y : ℤ) :
    0 ≤ M.contG W i y := (Gplus_nonneg M hA i y).trans (contG_ge hA hW i y)

theorem contG_coercive (hA : M.Assumption1) {W : I → ℤ → ℝ} (hW : Good M hA W) (i : I) :
    CoerciveInt (M.contG W i) := coercive_mono (Gplus_coercive M hA i) (contG_ge hA hW i)

theorem contG_convex (hA : M.Assumption1) {W : I → ℤ → ℝ} (hW : Good M hA W) (i : I) :
    IntConvex (M.contG W i) := by
  intro y
  have e : y + 2 = y + 1 + 1 := by ring
  rw [e, contG_delta hA hW i y, contG_delta hA hW i (y + 1)]
  have hG := Gplus_convex M i y
  rw [e] at hG
  have hb := (beta_pos M).le
  have h1 : W i y - W i (y - 1) ≤ W i (y + 1 - 1 + 1) - W i (y + 1 - 1) := by
    have := hW.convex i (y - 1)
    have e1 : y - 1 + 1 = y := by ring
    have e2 : y - 1 + 2 = y + 1 := by ring
    rw [e1, e2] at this
    simp only [add_sub_cancel_right]; exact this
  simp only [add_sub_cancel_right] at h1 ⊢
  have h2 : ∀ j, W j (y + 1) - W j y ≤ W j (y + 1 + 1) - W j (y + 1) := fun j => by
    have := hW.convex j y; rw [e] at this; exact this
  have hs0 := bdd_of_F M hW.nonneg hW.bound
  have hsum : ∀ z, Summable (fun j : {j : I // j ≠ i} => M.Q i j.1 * (W j.1 (z + 1) - W j.1 z)) :=
    fun z => by
      have : ∀ j : {j : I // j ≠ i}, |W j.1 (z + 1) - W j.1 z| ≤ Fb M (z + 1) + Fb M z := fun j => by
        have := hs0 (z + 1) j.1; have := hs0 z j.1
        calc |W j.1 (z + 1) - W j.1 z| ≤ |W j.1 (z + 1)| + |W j.1 z| := abs_sub _ _
          _ ≤ _ := by linarith
      exact summable_Qmul M i this
  have h3 : (∑' j : {j : I // j ≠ i}, M.Q i j.1 * (W j.1 (y + 1) - W j.1 y)) ≤
      ∑' j : {j : I // j ≠ i}, M.Q i j.1 * (W j.1 (y + 1 + 1) - W j.1 (y + 1)) :=
    (hsum y).tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (h2 j.1) (Qoff_nonneg M i j))
      (hsum (y + 1))
  have h4 := mul_le_mul_of_nonneg_left h1 (M.lam_nonneg i)
  have h5 := mul_le_mul_of_nonneg_left (h2 i) (self_nonneg' M i)
  have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h4 h3) h5) hb
  linarith

theorem contG_flat (hA : M.Assumption1) {W : I → ℤ → ℝ} (hW : Good M hA W) (i : I) (y : ℤ)
    (hy : y < ymin M hA) :
    M.contG W i (y + 1) - M.contG W i y = M.Gplus i (y + 1) - M.Gplus i y := by
  rw [contG_delta hA hW i y]
  have h1 : W i y - W i (y - 1) = 0 := by
    have := hW.flat i (y - 1) (by omega)
    simp only [sub_add_cancel] at this; exact this
  have h2 : ∀ j, W j (y + 1) - W j y = 0 := fun j => hW.flat j y hy
  simp only [h1, h2, mul_zero, tsum_zero, add_zero]

theorem contG_upper (hA : M.Assumption1) {W : I → ℤ → ℝ} (hW : Good M hA W) (i : I) (y : ℤ) :
    M.contG W i y ≤ M.Gplus i y + M.beta * M.lam i * M.c + M.gamma * Fb M y := by
  rw [contG_eq]
  have := Ex_le M hW.nonneg (fun j => hW.bound j y)
    (fun j => (hW.bound j (y - 1)).trans (Fb_mono M (by omega))) i
  have := mul_le_mul_of_nonneg_left this (beta_pos M).le
  have : M.beta * (M.μ * Fb M y) = M.gamma * Fb M y := by unfold Model.gamma; ring
  linarith

/-- Existence of the smallest minimizer of `contG W`, above `ymin`. -/
theorem contG_min (hA : M.Assumption1) {W : I → ℤ → ℝ} (hW : Good M hA W) (i : I) :
    ∃ s, SmallestMinimizer (M.contG W i) s ∧ ymin M hA ≤ s := by
  obtain ⟨s, hs⟩ := exists_smallest_minimizer (contG_coercive hA hW i)
  refine ⟨s, hs, ?_⟩
  by_contra h
  push_neg at h
  have := contG_flat hA hW i s h
  have := Gplus_delta_lt M hA i s h
  linarith [hs.1 (s + 1)]

theorem iInf_eq_max {f : ℤ → ℝ} (hf : IntConvex f) {s : ℤ} (hs : ∀ w, f s ≤ f w) (x : ℤ) :
    (⨅ y : {y : ℤ // x ≤ y}, (0 : ℝ) * delta (y.1 - x) + f y.1) = f (max x s) := by
  simp only [zero_mul, zero_add]
  haveI : Nonempty {y : ℤ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
  apply le_antisymm
  · have hbdd : BddBelow (Set.range fun y : {y : ℤ // x ≤ y} => f y.1) := by
      refine ⟨f s, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact hs y.1
    exact ciInf_le hbdd ⟨max x s, le_max_left _ _⟩
  · exact le_ciInf fun y => cv_max_le hf hs y.2

/-- The successor of a good function is good. -/
theorem good_next (hA : M.Assumption1) {W : I → ℤ → ℝ} (hW : Good M hA W) {s : I → ℤ}
    (hs : ∀ i, SmallestMinimizer (M.contG W i) (s i) ∧ ymin M hA ≤ s i) :
    Good M hA (fun i x => M.contG W i (max x (s i))) where
  nonneg i x := contG_nonneg hA hW i _
  bound i x := by
    have hs0 : 0 ≤ s i := (ymin_nonneg M hA).trans (hs i).2
    have h1 : M.contG W i (max x (s i)) ≤ M.contG W i (max x 0) := by
      rcases le_total (s i) x with h | h
      · rw [max_eq_left h, max_eq_left (hs0.trans h)]
      · rw [max_eq_right h]; exact (hs i).1.1 _
    refine h1.trans ?_
    have hx0 : 0 ≤ max x 0 := le_max_right _ _
    have h2 := contG_upper hA hW i (max x 0)
    have h3 := Gplus_upper M i (max x 0) hx0
    have h4 : M.beta * M.lam i * M.c ≤ M.beta * sSup (Set.range M.lam) * M.c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (lam_le M i) (beta_pos M).le)
        (c_nonneg M)
    have h5 := Fb_fix M (max x 0) hx0
    rw [Fb_max] at h5 h2
    unfold Acst Bcst at h5
    linarith
  convex i := cv_max_convex (contG_convex hA hW i) (hs i).1.1
  mono i x := cv_max_delta_nonneg (contG_convex hA hW i) (hs i).1.1 x
  flat i x hx := by
    show M.contG W i (max (x + 1) (s i)) - M.contG W i (max x (s i)) = 0
    rw [cv_delta_max (contG_convex hA hW i) (hs i).1.1, if_pos (by linarith [(hs i).2])]

theorem good_zero (hA : M.Assumption1) : Good M hA (fun _ _ => 0) where
  nonneg _ _ := le_rfl
  bound _ x := Fb_nonneg M x
  convex _ := fun _ => by simp
  mono _ _ := by simp
  flat _ _ _ := by simp

end SZLDev


open scoped ENNReal NNReal
open MeasureTheory

namespace SZLDev

open _root_.SongZipkinFluct.Linear

variable {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] {M : Model I}

theorem summ_delta (hA : M.Assumption1) {W : I → ℤ → ℝ} (hW : Good M hA W) (i : I) (z : ℤ) :
    Summable (fun j : {j : I // j ≠ i} => M.Q i j.1 * (W j.1 (z + 1) - W j.1 z)) := by
  have hs0 := bdd_of_F M hW.nonneg hW.bound
  have : ∀ j : {j : I // j ≠ i}, |W j.1 (z + 1) - W j.1 z| ≤ Fb M (z + 1) + Fb M z := fun j => by
    have := hs0 (z + 1) j.1; have := hs0 z j.1
    calc |W j.1 (z + 1) - W j.1 z| ≤ |W j.1 (z + 1)| + |W j.1 z| := abs_sub _ _
      _ ≤ _ := by linarith
  exact summable_Qmul M i this

theorem contG_mono (hA : M.Assumption1) {W W' : I → ℤ → ℝ} (hW : Good M hA W) (hW' : Good M hA W')
    (h : ∀ j z, W j z ≤ W' j z) (i : I) (y : ℤ) : M.contG W i y ≤ M.contG W' i y := by
  rw [contG_eq, contG_eq]
  have := Ex_mono M (bdd_of_F M hW.nonneg hW.bound y) (bdd_of_F M hW'.nonneg hW'.bound y) i
    (h i (y - 1)) (fun j => h j y)
  have := mul_le_mul_of_nonneg_left this (beta_pos M).le
  linarith

theorem contG_delta_mono (hA : M.Assumption1) {W W' : I → ℤ → ℝ} (hW : Good M hA W)
    (hW' : Good M hA W') (h : ∀ j z, W j (z + 1) - W j z ≤ W' j (z + 1) - W' j z) (i : I) (y : ℤ) :
    M.contG W i (y + 1) - M.contG W i y ≤ M.contG W' i (y + 1) - M.contG W' i y := by
  rw [contG_delta hA hW, contG_delta hA hW']
  set T := ∑' j : {j : I // j ≠ i}, M.Q i j.1 * (W j.1 (y + 1) - W j.1 y)
  set T' := ∑' j : {j : I // j ≠ i}, M.Q i j.1 * (W' j.1 (y + 1) - W' j.1 y)
  have h3 : T ≤ T' := (summ_delta hA hW i y).tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (h j.1 y)
      (Qoff_nonneg M i j)) (summ_delta hA hW' i y)
  have h1 : W i y - W i (y - 1) ≤ W' i y - W' i (y - 1) := by
    have := h i (y - 1); simp only [sub_add_cancel] at this; exact this
  have h4 := mul_le_mul_of_nonneg_left h1 (M.lam_nonneg i)
  have h5 := mul_le_mul_of_nonneg_left (h i y) (self_nonneg' M i)
  have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h4 h3) h5) (beta_pos M).le
  exact add_le_add_right this _

theorem Glin_succ (n : ℕ) (i : I) (y : ℤ) : M.Glin (n + 1) i y = M.contG (M.Wlin n) i y := by
  simp only [Model.Glin, Model.G, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  rfl

theorem Wlin_succ (n : ℕ) (i : I) (x : ℤ) :
    M.Wlin (n + 1) i x = ⨅ y : {y : ℤ // x ≤ y}, (0 : ℝ) * delta (y.1 - x) +
      M.contG (M.Wlin n) i y.1 := rfl

theorem Wlin_zero (i : I) (x : ℤ) : M.Wlin 0 i x = 0 := rfl

theorem good_Wlin (hA : M.Assumption1) : ∀ n, Good M hA (M.Wlin n) := by
  intro n
  induction n with
  | zero =>
    have : M.Wlin 0 = fun _ _ => 0 := rfl
    rw [this]; exact good_zero hA
  | succ n ih =>
    choose s hs using contG_min hA ih
    have : M.Wlin (n + 1) = fun i x => M.contG (M.Wlin n) i (max x (s i)) := by
      funext i x
      rw [Wlin_succ, iInf_eq_max (contG_convex hA ih i) (hs i).1.1]
    rw [this]
    exact good_next hA ih hs

/-- The finite-stage levels. -/
noncomputable def ys (M : Model I) (n : ℕ) (i : I) : ℤ :=
  Classical.epsilon (fun s => SmallestMinimizer (M.Glin n i) s)

theorem ys_spec (hA : M.Assumption1) (m : ℕ) (i : I) :
    SmallestMinimizer (M.Glin (m + 1) i) (ys M (m + 1) i) ∧ ymin M hA ≤ ys M (m + 1) i := by
  obtain ⟨s, hs, hsm⟩ := contG_min hA (good_Wlin hA m) i
  have e : M.Glin (m + 1) i = M.contG (M.Wlin m) i := funext (Glin_succ m i)
  have hs' : SmallestMinimizer (M.Glin (m + 1) i) s := e ▸ hs
  have h := Classical.epsilon_spec (p := fun s => SmallestMinimizer (M.Glin (m + 1) i) s) ⟨s, hs'⟩
  refine ⟨h, ?_⟩
  calc ymin M hA ≤ s := hsm
    _ = ys M (m + 1) i := (smallest_unique h hs').symm

theorem Glin_convex (hA : M.Assumption1) (m : ℕ) (i : I) : IntConvex (M.Glin (m + 1) i) := by
  have e : M.Glin (m + 1) i = M.contG (M.Wlin m) i := funext (Glin_succ m i)
  rw [e]; exact contG_convex hA (good_Wlin hA m) i

theorem Glin_coercive (hA : M.Assumption1) (m : ℕ) (i : I) : CoerciveInt (M.Glin (m + 1) i) := by
  have e : M.Glin (m + 1) i = M.contG (M.Wlin m) i := funext (Glin_succ m i)
  rw [e]; exact contG_coercive hA (good_Wlin hA m) i

theorem Glin_nonneg (hA : M.Assumption1) (m : ℕ) (i : I) (y : ℤ) : 0 ≤ M.Glin (m + 1) i y := by
  rw [Glin_succ]; exact contG_nonneg hA (good_Wlin hA m) i y

theorem Wlin_eq (hA : M.Assumption1) (m : ℕ) (i : I) (x : ℤ) :
    M.Wlin (m + 1) i x = M.Glin (m + 1) i (max x (ys M (m + 1) i)) := by
  have e : M.Glin (m + 1) i = M.contG (M.Wlin m) i := funext (Glin_succ m i)
  rw [Wlin_succ, ← e, iInf_eq_max (Glin_convex hA m i) (ys_spec hA m i).1.1]

theorem Wlin_le_succ (hA : M.Assumption1) : ∀ m (i : I) (x : ℤ), M.Wlin m i x ≤ M.Wlin (m + 1) i x := by
  intro m
  induction m with
  | zero => intro i x; exact (good_Wlin hA 1).nonneg i x
  | succ m ih =>
    intro i x
    have hG : ∀ y, M.Glin (m + 1) i y ≤ M.Glin (m + 1 + 1) i y := fun y => by
      rw [Glin_succ, Glin_succ]
      exact contG_mono hA (good_Wlin hA m) (good_Wlin hA (m + 1)) ih i y
    rw [Wlin_eq hA m, Wlin_eq hA (m + 1)]
    exact (cv_max_le (Glin_convex hA m i) (ys_spec hA m i).1.1 (le_max_left x _)).trans (hG _)

theorem Glin_le_succ (hA : M.Assumption1) (m : ℕ) (i : I) (y : ℤ) :
    M.Glin (m + 1) i y ≤ M.Glin (m + 1 + 1) i y := by
  rw [Glin_succ, Glin_succ]
  exact contG_mono hA (good_Wlin hA m) (good_Wlin hA (m + 1)) (Wlin_le_succ hA m) i y

theorem dW_eq (hA : M.Assumption1) (m : ℕ) (i : I) (x : ℤ) :
    M.Wlin (m + 1) i (x + 1) - M.Wlin (m + 1) i x =
      if x < ys M (m + 1) i then 0 else M.Glin (m + 1) i (x + 1) - M.Glin (m + 1) i x := by
  rw [Wlin_eq hA m, Wlin_eq hA m]
  exact cv_delta_max (Glin_convex hA m i) (ys_spec hA m i).1.1 x

/-- Monotonicity of the differences and of the levels (Theorem 1(f)-(h)). -/
theorem delta_mono (hA : M.Assumption1) : ∀ m : ℕ,
    (∀ (i : I) (x : ℤ), M.Wlin m i (x + 1) - M.Wlin m i x ≤
      M.Wlin (m + 1) i (x + 1) - M.Wlin (m + 1) i x) := by
  intro m
  induction m with
  | zero =>
    intro i x
    simp only [Wlin_zero, sub_self]
    exact (good_Wlin hA 1).mono i x
  | succ m ih =>
    intro i x
    have hG : ∀ y, M.Glin (m + 1) i (y + 1) - M.Glin (m + 1) i y ≤
        M.Glin (m + 1 + 1) i (y + 1) - M.Glin (m + 1 + 1) i y := fun y => by
      simp only [Glin_succ]
      exact contG_delta_mono hA (good_Wlin hA m) (good_Wlin hA (m + 1)) ih i y
    have hs : ys M (m + 1 + 1) i ≤ ys M (m + 1) i := by
      refine cv_le_of_delta (Glin_convex hA (m + 1) i) (ys_spec hA (m + 1) i).1 ?_
      exact (cv_right (Glin_convex hA m i) (ys_spec hA m i).1.1 le_rfl).trans (hG _)
    rw [dW_eq hA m, dW_eq hA (m + 1)]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact cv_right (Glin_convex hA (m + 1) i) (ys_spec hA (m + 1) i).1.1 (not_lt.mp h2)
    · omega
    · exact hG x

theorem ys_succ_le (hA : M.Assumption1) (m : ℕ) (i : I) : ys M (m + 1 + 1) i ≤ ys M (m + 1) i := by
  have hG : ∀ y, M.Glin (m + 1) i (y + 1) - M.Glin (m + 1) i y ≤
      M.Glin (m + 1 + 1) i (y + 1) - M.Glin (m + 1 + 1) i y := fun y => by
    simp only [Glin_succ]
    exact contG_delta_mono hA (good_Wlin hA m) (good_Wlin hA (m + 1)) (delta_mono hA m) i y
  refine cv_le_of_delta (Glin_convex hA (m + 1) i) (ys_spec hA (m + 1) i).1 ?_
  exact (cv_right (Glin_convex hA m i) (ys_spec hA m i).1.1 le_rfl).trans (hG _)

theorem Glin_flat (hA : M.Assumption1) (m : ℕ) (i : I) (y : ℤ) (hy : y < ymin M hA) :
    M.Glin (m + 1) i (y + 1) - M.Glin (m + 1) i y = M.Gplus i (y + 1) - M.Gplus i y := by
  simp only [Glin_succ]
  exact contG_flat hA (good_Wlin hA m) i y hy

theorem Glin_one (i : I) (y : ℤ) : M.Glin 1 i y = M.Gplus i y + M.beta * M.lam i * M.c := by
  rw [Glin_succ, contG_eq]
  simp [Ex, Wlin_zero]

theorem ys_one (hA : M.Assumption1) (i : I) : ys M 1 i = yplus M hA i := by
  have h := (ys_spec hA 0 i).1
  have e : M.Glin (0 + 1) i = fun y => M.Gplus i y + M.beta * M.lam i * M.c :=
    funext (Glin_one i)
  rw [e] at h
  exact smallest_unique h (smallest_add_const _ (yplus_spec M hA i).1)

end SZLDev


open scoped ENNReal NNReal
open MeasureTheory

namespace SZLDev

open _root_.SongZipkinFluct.Linear

variable {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] {M : Model I}

theorem dG_mono (hA : M.Assumption1) (m : ℕ) (i : I) (y : ℤ) :
    M.Glin (m + 1) i (y + 1) - M.Glin (m + 1) i y ≤
      M.Glin (m + 1 + 1) i (y + 1) - M.Glin (m + 1 + 1) i y := by
  simp only [Glin_succ]
  exact contG_delta_mono hA (good_Wlin hA m) (good_Wlin hA (m + 1)) (delta_mono hA m) i y

theorem ys_antitone (hA : M.Assumption1) (i : I) : Antitone (fun n : ℕ => ys M (n + 1) i) :=
  antitone_nat_of_succ_le fun n => ys_succ_le hA n i

theorem yinf_exists (hA : M.Assumption1) (i : I) :
    ∃ y, IsLeast (Set.range (fun n : ℕ => ys M (n + 1) i)) y := by
  obtain ⟨lb, hlb, hmin⟩ := Int.exists_least_of_bdd
    (P := fun z => z ∈ Set.range (fun n : ℕ => ys M (n + 1) i))
    ⟨ymin M hA, fun z ⟨n, hn⟩ => hn ▸ (ys_spec hA n i).2⟩ ⟨_, Set.mem_range_self 0⟩
  exact ⟨lb, hlb, fun z hz => hmin z hz⟩

noncomputable def yinf (hA : M.Assumption1) (i : I) : ℤ := Classical.choose (yinf_exists hA i)

theorem yinf_spec (hA : M.Assumption1) (i : I) :
    IsLeast (Set.range (fun n : ℕ => ys M (n + 1) i)) (yinf hA i) :=
  Classical.choose_spec (yinf_exists hA i)

theorem yinf_le (hA : M.Assumption1) (n : ℕ) (i : I) : yinf hA i ≤ ys M (n + 1) i :=
  (yinf_spec hA i).2 (Set.mem_range_self n)

theorem yinf_eventually (hA : M.Assumption1) (i : I) :
    ∃ N : ℕ, ∀ n, N ≤ n → ys M (n + 1) i = yinf hA i := by
  obtain ⟨N, hN⟩ := (yinf_spec hA i).1
  refine ⟨N, fun n hn => le_antisymm ?_ (yinf_le hA n i)⟩
  rw [← hN]; exact ys_antitone hA i hn

theorem yinf_tendsto (hA : M.Assumption1) (i : I) :
    Filter.Tendsto (fun n : ℕ => ys M (n + 1) i) Filter.atTop (nhds (yinf hA i)) := by
  obtain ⟨N, hN⟩ := yinf_eventually hA i
  exact tendsto_const_nhds.congr' (Filter.eventually_atTop.mpr ⟨N, fun n hn => (hN n hn).symm⟩)

theorem ymin_le_yinf (hA : M.Assumption1) (i : I) : ymin M hA ≤ yinf hA i := by
  obtain ⟨N, hN⟩ := (yinf_spec hA i).1
  rw [← hN]; exact (ys_spec hA N i).2

theorem ys_le_one (hA : M.Assumption1) (n : ℕ) (i : I) : ys M (n + 1) i ≤ ys M 1 i :=
  ys_antitone hA i (Nat.zero_le n)

/-! ### Assembly of the milestone statements of Theorem 1 and Corollary 2 -/

theorem theorem1_ac_proof (hA : M.Assumption1) :
    ∃ ys : ℕ → I → ℤ,
      (∀ n : ℕ, 1 ≤ n → ∀ i : I,
        IntConvex (M.Glin n i) ∧ CoerciveInt (M.Glin n i) ∧
        SmallestMinimizer (M.Glin n i) (ys n i) ∧
        ∀ x : ℤ, M.Wlin n i x = M.Glin n i (max x (ys n i))) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ i : I, IntConvex (M.Wlin n i) := by
  refine ⟨ys M, fun n hn i => ?_, fun n _ i => (good_Wlin hA n).convex i⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨Glin_convex hA m i, Glin_coercive hA m i, (ys_spec hA m i).1, Wlin_eq hA m i⟩

theorem theorem1_di_proof (hA : M.Assumption1) :
    ∃ (ys : ℕ → I → ℤ) (yplus : I → ℤ) (ymin : ℤ),
      (∀ i : I, SmallestMinimizer (M.Gplus i) (yplus i)) ∧
      IsLeast (Set.range yplus) ymin ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i : I,
        SmallestMinimizer (M.Glin n i) (ys n i)) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i : I, ∀ x : ℤ,
        0 ≤ M.Wlin (n - 1) i x ∧
        M.Wlin (n - 1) i x ≤ M.Wlin n i x ∧
        0 ≤ Delta (M.Wlin (n - 1)) i x ∧
        Delta (M.Wlin (n - 1)) i x ≤ Delta (M.Wlin n) i x) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i : I, ∀ y : ℤ,
        0 ≤ M.Glin n i y ∧
        M.Glin n i y ≤ M.Glin (n + 1) i y ∧
        Delta (M.Glin n) i y ≤ Delta (M.Glin (n + 1)) i y) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i : I, ys (n + 1) i ≤ ys n i) ∧
      0 ≤ ymin ∧
      ∀ n : ℕ, 1 ≤ n → ∀ i : I,
        ymin ≤ ys n i ∧
        ∀ y : ℤ, y < ymin →
          Delta (M.Glin n) i y = Delta M.Gplus i y ∧
          Delta M.Gplus i y < 0 := by
  refine ⟨ys M, yplus M hA, ymin M hA, fun i => (yplus_spec M hA i).1, ymin_spec M hA,
    fun n hn i => ?_, fun n hn i x => ?_, fun n hn i y => ?_, fun n hn i => ?_,
    ymin_nonneg M hA, fun n hn i => ?_⟩ <;>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  · exact (ys_spec hA m i).1
  · simp only [Nat.add_sub_cancel, Delta]
    exact ⟨(good_Wlin hA m).nonneg i x, Wlin_le_succ hA m i x, (good_Wlin hA m).mono i x,
      delta_mono hA m i x⟩
  · simp only [Delta]
    exact ⟨Glin_nonneg hA m i y, Glin_le_succ hA m i y, dG_mono hA m i y⟩
  · exact ys_succ_le hA m i
  · refine ⟨(ys_spec hA m i).2, fun y hy => ?_⟩
    simp only [Delta]
    exact ⟨Glin_flat hA m i y hy, Gplus_delta_lt M hA i y hy⟩

theorem corollary2_proof (hA : M.Assumption1) :
    ∃ (ys : ℕ → I → ℤ) (yplus yinf : I → ℤ) (ymin : ℤ),
      (∀ i : I, SmallestMinimizer (M.Gplus i) (yplus i)) ∧
      IsLeast (Set.range yplus) ymin ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i : I,
        SmallestMinimizer (M.Glin n i) (ys n i)) ∧
      (∀ i : I, Filter.Tendsto (fun n : ℕ => ys (n + 1) i)
        Filter.atTop (nhds (yinf i))) ∧
      0 ≤ ymin ∧
      ∀ n : ℕ, 1 ≤ n → ∀ i : I,
        ymin ≤ yinf i ∧ yinf i ≤ ys n i ∧
        ys n i ≤ ys 1 i ∧ ys 1 i = yplus i := by
  refine ⟨ys M, yplus M hA, yinf hA, ymin M hA, fun i => (yplus_spec M hA i).1, ymin_spec M hA,
    fun n hn i => ?_, yinf_tendsto hA, ymin_nonneg M hA, fun n hn i => ?_⟩ <;>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  · exact (ys_spec hA m i).1
  · exact ⟨ymin_le_yinf hA i, yinf_le hA m i, ys_le_one hA m i, ys_one hA i⟩

end SZLDev


open scoped ENNReal NNReal
open MeasureTheory Filter Topology

namespace SZLDev

open _root_.SongZipkinFluct.Linear

variable {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] {M : Model I}

theorem Wlin_mono_n (hA : M.Assumption1) (i : I) (x : ℤ) : Monotone (fun n => M.Wlin n i x) :=
  monotone_nat_of_le_succ fun n => Wlin_le_succ hA n i x

theorem Wlin_bdd (hA : M.Assumption1) (i : I) (x : ℤ) :
    BddAbove (Set.range (fun n => M.Wlin n i x)) :=
  ⟨Fb M x, by rintro _ ⟨n, rfl⟩; exact (good_Wlin hA n).bound i x⟩

theorem Winf_tendsto (hA : M.Assumption1) (i : I) (x : ℤ) :
    Tendsto (fun n => M.Wlin n i x) atTop (𝓝 (M.Winf i x)) :=
  tendsto_atTop_ciSup (Wlin_mono_n hA i x) (Wlin_bdd hA i x)

theorem Wlin_le_Winf (hA : M.Assumption1) (n : ℕ) (i : I) (x : ℤ) : M.Wlin n i x ≤ M.Winf i x :=
  le_ciSup (Wlin_bdd hA i x) n

theorem good_Winf (hA : M.Assumption1) : Good M hA M.Winf where
  nonneg i x := ((good_Wlin hA 0).nonneg i x).trans (Wlin_le_Winf hA 0 i x)
  bound i x := ciSup_le fun n => (good_Wlin hA n).bound i x
  convex i := fun y => le_of_tendsto_of_tendsto'
    ((Winf_tendsto hA i (y + 1)).sub (Winf_tendsto hA i y))
    ((Winf_tendsto hA i (y + 2)).sub (Winf_tendsto hA i (y + 1)))
    (fun n => (good_Wlin hA n).convex i y)
  mono i x := ge_of_tendsto' ((Winf_tendsto hA i (x + 1)).sub (Winf_tendsto hA i x))
    (fun n => (good_Wlin hA n).mono i x)
  flat i x hx := tendsto_nhds_unique ((Winf_tendsto hA i (x + 1)).sub (Winf_tendsto hA i x))
    (tendsto_const_nhds.congr fun n => ((good_Wlin hA n).flat i x hx).symm)

theorem Glin_mono_n (hA : M.Assumption1) (i : I) (y : ℤ) :
    Monotone (fun n : ℕ => M.Glin (n + 1) i y) :=
  monotone_nat_of_le_succ fun n => Glin_le_succ hA n i y

theorem Glin_bdd (hA : M.Assumption1) (i : I) (y : ℤ) :
    BddAbove (Set.range (fun n : ℕ => M.Glin (n + 1) i y)) :=
  ⟨M.Gplus i y + M.beta * M.lam i * M.c + M.gamma * Fb M y, by
    rintro _ ⟨n, rfl⟩
    simp only [Glin_succ]
    exact contG_upper hA (good_Wlin hA n) i y⟩

theorem Ginf_tendsto (hA : M.Assumption1) (i : I) (y : ℤ) :
    Tendsto (fun n : ℕ => M.Glin (n + 1) i y) atTop (𝓝 (M.Ginf i y)) :=
  tendsto_atTop_ciSup (Glin_mono_n hA i y) (Glin_bdd hA i y)

theorem contG_tendsto (hA : M.Assumption1) (i : I) (y : ℤ) :
    Tendsto (fun n : ℕ => M.contG (M.Wlin n) i y) atTop (𝓝 (M.contG M.Winf i y)) := by
  simp only [contG_eq, Ex]
  refine tendsto_const_nhds.add (Tendsto.const_mul _ ((((Winf_tendsto hA i (y - 1)).const_mul _).add
    ?_).add ((Winf_tendsto hA i y).const_mul _)))
  refine tendsto_tsum_of_dominated_convergence (bound := fun j : {j : I // j ≠ i} =>
    M.Q i j.1 * Fb M y) ((qsummable M i).mul_right _)
    (fun j => (Winf_tendsto hA j.1 y).const_mul _) (Eventually.of_forall fun n j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Qoff_nonneg M i j),
    abs_of_nonneg ((good_Wlin hA n).nonneg _ _)]
  exact mul_le_mul_of_nonneg_left ((good_Wlin hA n).bound _ _) (Qoff_nonneg M i j)

theorem Ginf_eq (hA : M.Assumption1) (i : I) (y : ℤ) : M.Ginf i y = M.contG M.Winf i y :=
  tendsto_nhds_unique (Ginf_tendsto hA i y)
    ((contG_tendsto hA i y).congr fun n => (Glin_succ n i y).symm)

theorem Ginf_eq' (hA : M.Assumption1) (i : I) : M.Ginf i = M.contG M.Winf i :=
  funext (Ginf_eq hA i)

theorem Ginf_convex (hA : M.Assumption1) (i : I) : IntConvex (M.Ginf i) := by
  rw [Ginf_eq' hA]; exact contG_convex hA (good_Winf hA) i

theorem Ginf_coercive (hA : M.Assumption1) (i : I) : CoerciveInt (M.Ginf i) := by
  rw [Ginf_eq' hA]; exact contG_coercive hA (good_Winf hA) i

theorem ystar_exists (hA : M.Assumption1) (i : I) :
    ∃ s, SmallestMinimizer (M.Ginf i) s ∧ ymin M hA ≤ s := by
  rw [Ginf_eq' hA]; exact contG_min hA (good_Winf hA) i

noncomputable def ystar (hA : M.Assumption1) (i : I) : ℤ := Classical.choose (ystar_exists hA i)

theorem ystar_spec (hA : M.Assumption1) (i : I) :
    SmallestMinimizer (M.Ginf i) (ystar hA i) ∧ ymin M hA ≤ ystar hA i :=
  Classical.choose_spec (ystar_exists hA i)

theorem yinf_min (hA : M.Assumption1) (i : I) (y : ℤ) : M.Ginf i (yinf hA i) ≤ M.Ginf i y := by
  obtain ⟨N, hN⟩ := yinf_eventually hA i
  refine le_of_tendsto_of_tendsto (Ginf_tendsto hA i _) (Ginf_tendsto hA i y)
    (eventually_atTop.mpr ⟨N, fun n hn => ?_⟩)
  have := (ys_spec hA n i).1.1 y
  rwa [hN n hn] at this

theorem ystar_le_yinf (hA : M.Assumption1) (i : I) : ystar hA i ≤ yinf hA i :=
  (ystar_spec hA i).1.2 (yinf_min hA i)

theorem yinf_le_yplus (hA : M.Assumption1) (i : I) : yinf hA i ≤ yplus M hA i := by
  rw [← ys_one hA i]; exact yinf_le hA 0 i

theorem Winf_eq_yinf (hA : M.Assumption1) (i : I) (x : ℤ) :
    M.Winf i x = M.Ginf i (max x (yinf hA i)) := by
  obtain ⟨N, hN⟩ := yinf_eventually hA i
  have h1 : Tendsto (fun n => M.Wlin (n + 1) i x) atTop (𝓝 (M.Winf i x)) :=
    (Winf_tendsto hA i x).comp (tendsto_add_atTop_nat 1)
  refine tendsto_nhds_unique h1 ((Ginf_tendsto hA i _).congr' ?_)
  refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  show M.Glin (n + 1) i (max x (yinf hA i)) = M.Wlin (n + 1) i x
  rw [Wlin_eq hA n, hN n hn]

theorem Winf_eq_ystar (hA : M.Assumption1) (i : I) (x : ℤ) :
    M.Winf i x = M.Ginf i (max x (ystar hA i)) := by
  rw [Winf_eq_yinf hA]
  have h1 := ystar_le_yinf hA i
  rcases le_total (yinf hA i) x with h | h
  · rw [max_eq_left h, max_eq_left (h1.trans h)]
  · rw [max_eq_right h]
    apply le_antisymm (yinf_min hA i _)
    exact cv_mono_right (Ginf_convex hA i) (ystar_spec hA i).1.1 (le_max_right _ _)
      (max_le h h1)

theorem Winf_le_Ginf (hA : M.Assumption1) (i : I) (x y : ℤ) (hxy : x ≤ y) :
    M.Winf i x ≤ M.Ginf i y := by
  rw [Winf_eq_ystar hA]
  exact cv_max_le (Ginf_convex hA i) (ystar_spec hA i).1.1 hxy

/-! ### Assembly of Theorem 2 (a), (b), (d) -/

theorem theorem2_ab_proof (hA : M.Assumption1) :
    (∀ i : I, ∀ x : ℤ,
      Filter.Tendsto (fun n : ℕ => M.Wlin n i x) Filter.atTop (nhds (M.Winf i x))) ∧
    (∀ i : I, IntConvex (M.Winf i) ∧
      Filter.Tendsto (M.Winf i) Filter.atTop Filter.atTop) ∧
    (∀ i : I, ∀ y : ℤ,
      Filter.Tendsto (fun n : ℕ => M.Glin (n + 1) i y)
        Filter.atTop (nhds (M.Ginf i y))) ∧
    (∀ i : I, IntConvex (M.Ginf i) ∧ CoerciveInt (M.Ginf i)) ∧
    ∃ ystar : I → ℤ,
      ∀ i : I, SmallestMinimizer (M.Ginf i) (ystar i) := by
  refine ⟨Winf_tendsto hA, fun i => ⟨(good_Winf hA).convex i, ?_⟩, Ginf_tendsto hA,
    fun i => ⟨Ginf_convex hA i, Ginf_coercive hA i⟩, ystar hA, fun i => (ystar_spec hA i).1⟩
  have h1 : Tendsto (fun x => M.Gplus i (max x (ystar hA i))) atTop atTop :=
    ((lemma2_proof M i).2.1).congr' (eventually_atTop.mpr ⟨ystar hA i, fun x hx => by
      show M.Gplus i x = M.Gplus i (max x (ystar hA i))
      rw [max_eq_left hx]⟩)
  refine tendsto_atTop_mono (fun x => ?_) h1
  rw [Winf_eq_ystar hA, Ginf_eq hA]
  exact contG_ge hA (good_Winf hA) i _

theorem theorem2_d_proof (hA : M.Assumption1) :
    ∃ (ys : ℕ → I → ℤ) (ystar yinf : I → ℤ),
      (∀ n : ℕ, 1 ≤ n → ∀ i : I,
        SmallestMinimizer (M.Glin n i) (ys n i)) ∧
      (∀ i : I, Filter.Tendsto (fun n : ℕ => ys (n + 1) i)
        Filter.atTop (nhds (yinf i))) ∧
      (∀ i : I, SmallestMinimizer (M.Ginf i) (ystar i)) ∧
      (∀ i : I, ∀ y : ℤ, M.Ginf i (yinf i) ≤ M.Ginf i y) ∧
      (∀ i : I, ∀ y : ℤ, M.Ginf i y = M.contG M.Winf i y) ∧
      ∀ i : I, ∀ x : ℤ,
        (∀ y : ℤ, x ≤ y → M.Winf i x ≤ M.Ginf i y) ∧
        M.Winf i x = M.Ginf i (max x (ystar i)) ∧
        M.Winf i x = M.Ginf i (max x (yinf i)) := by
  refine ⟨ys M, ystar hA, yinf hA, fun n hn i => ?_, yinf_tendsto hA, fun i => (ystar_spec hA i).1,
    yinf_min hA, Ginf_eq hA, fun i x => ⟨Winf_le_Ginf hA i x, Winf_eq_ystar hA i x,
    Winf_eq_yinf hA i x⟩⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (ys_spec hA m i).1

end SZLDev

open SongZipkinFluct.Linear in
theorem solution {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (hA : M.Assumption1) :
    (∀ i : I, ∀ x : ℤ,
      Filter.Tendsto (fun n : ℕ => M.Wlin n i x) Filter.atTop (nhds (M.Winf i x))) ∧
    (∀ i : I, IntConvex (M.Winf i) ∧
      Filter.Tendsto (M.Winf i) Filter.atTop Filter.atTop) ∧
    (∀ i : I, ∀ y : ℤ,
      Filter.Tendsto (fun n : ℕ => M.Glin (n + 1) i y)
        Filter.atTop (nhds (M.Ginf i y))) ∧
    (∀ i : I, IntConvex (M.Ginf i) ∧ CoerciveInt (M.Ginf i)) ∧
    ∃ ystar : I → ℤ,
      ∀ i : I, SmallestMinimizer (M.Ginf i) (ystar i) :=
  SZLDev.theorem2_ab_proof hA

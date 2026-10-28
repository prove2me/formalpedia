-- Prove2me | solution 1 for TamingMonster.Regret.freedman_inequality
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T06:09:40.441775+00:00
-- url     : https://prove2.me/submissions/25e2d8b2-0e9d-431b-9350-04c0183bc05d

import Mathlib

namespace Prove2SwarmSubmission

/-! ### Part: statement-auditor FreedmanOneStep.lean (verified 57496d02: scalar + one-step) (sha256 57496d02cfdacd625fe2c1acfc06c2522ecd76ae0dfc2c30c0937ef32404efc5) -/
set_option autoImplicit false

namespace TamingMonster.Regret.FreedmanAux

/-- On `[-1, 1]`, compare the exponential series with `y ^ 2 * exp 1` term by term: for `n ≥ 2`,
`y ^ n ≤ |y| ^ n ≤ y ^ 2`. The terms `n = 0, 1` give exactly `1 + y + (e - 2) * y ^ 2`. -/
theorem exp_le_one_add_add_c_sq_of_abs_le_one {y : ℝ} (hy : |y| ≤ 1) :
    Real.exp y ≤ 1 + y + (Real.exp 1 - 2) * y ^ 2 := by
  have hexp : ∀ x : ℝ, HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
    intro x
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have hG : HasSum (fun n : ℕ => (y ^ 2 - y ^ n) / (n.factorial : ℝ))
      (y ^ 2 * Real.exp 1 - Real.exp y) := by
    have hfun : (fun n : ℕ => (y ^ 2 - y ^ n) / (n.factorial : ℝ)) =
        fun n : ℕ => y ^ 2 * ((1 : ℝ) ^ n / (n.factorial : ℝ)) - y ^ n / (n.factorial : ℝ) := by
      funext n
      rw [one_pow]
      ring
    rw [hfun]
    exact ((hexp 1).mul_left (y ^ 2)).sub (hexp y)
  have hle := sum_le_hasSum (Finset.range 2) (fun n hn => ?_) hG
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
      Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, zero_add] at hle
    linarith
  · have hn2 : 2 ≤ n := by
      simp only [Finset.mem_range, not_lt] at hn
      exact hn
    have hpow : y ^ n ≤ y ^ 2 :=
      calc
        y ^ n ≤ |y| ^ n := (le_abs_self (y ^ n)).trans (abs_pow y n).le
        _ ≤ |y| ^ 2 := pow_le_pow_of_le_one (abs_nonneg y) hy hn2
        _ = y ^ 2 := sq_abs y
    exact div_nonneg (sub_nonneg.mpr hpow) (Nat.cast_nonneg _)

/-- `exp y ≤ 1 + y + (e - 2) * y ^ 2` for every `y ≤ 1` (equality at `y = 0` and `y = 1`).
For `y < -1`: `1 + y + (e - 2) y ^ 2 - (e - 2) = (-1 - y) * ((e - 2) * (1 - y) - 1) > 0`, so the
right side exceeds `e - 2 > 0.7 > exp (-1) > exp y`. -/
theorem exp_le_one_add_add_c_sq {y : ℝ} (hy : y ≤ 1) :
    Real.exp y ≤ 1 + y + (Real.exp 1 - 2) * y ^ 2 := by
  by_cases hneg : (-1 : ℝ) ≤ y
  · exact exp_le_one_add_add_c_sq_of_abs_le_one (abs_le.mpr ⟨hneg, hy⟩)
  · have hyneg : y < -1 := lt_of_not_ge hneg
    have he : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have hexp : Real.exp y < 0.37 :=
      lt_trans (Real.exp_lt_exp.mpr hyneg) (lt_trans Real.exp_neg_one_lt_d9 (by norm_num))
    have hA : (0 : ℝ) < -1 - y := by linarith
    have hB0 : (0 : ℝ) < (Real.exp 1 - 2.7) * (1 - y) :=
      mul_pos (by linarith) (by linarith)
    have hB : (0 : ℝ) < (Real.exp 1 - 2) * (1 - y) - 1 := by linarith
    have hAB : (0 : ℝ) < (-1 - y) * ((Real.exp 1 - 2) * (1 - y) - 1) := mul_pos hA hB
    linarith

end TamingMonster.Regret.FreedmanAux


set_option autoImplicit false

namespace FreedmanNativeIntegrability

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The one-sided increment bound suffices; no lower bound on the increment is used. -/
theorem mul_le_one_of_upper_bound {x R lam : ℝ}
    (hR : 0 < R) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1 / R)
    (hx : x ≤ R) : lam * x ≤ 1 := by
  have hprod : lam * R ≤ 1 := (le_div_iff₀ hR).mp hlam1
  exact (mul_le_mul_of_nonneg_left hx hlam0).trans hprod

/-- The precise a.e. one-step exponent bound in the exact lambda range. -/
theorem ae_mul_le_one (P : Measure Ω) {X : Ω → ℝ} {R lam : ℝ}
    (hR : 0 < R) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R)
    (hXle : ∀ᵐ ω ∂P, X ω ≤ R) :
    ∀ᵐ ω ∂P, lam * X ω ≤ 1 := by
  filter_upwards [hXle] with ω hω
  exact mul_le_one_of_upper_bound hR hlam0.le hlam1 hω

/-- A constant upper bound for the nonnegative exponential of an increment. -/
theorem ae_exp_mul_le_exp_one (P : Measure Ω) {X : Ω → ℝ} {R lam : ℝ}
    (hR : 0 < R) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R)
    (hXle : ∀ᵐ ω ∂P, X ω ≤ R) :
    ∀ᵐ ω ∂P, Real.exp (lam * X ω) ≤ Real.exp 1 := by
  filter_upwards [ae_mul_le_one P hR hlam0 hlam1 hXle] with ω hω
  exact Real.exp_le_exp.mpr hω

/-- A measurable exponent bounded above by one has an integrable exponential
on a finite measure space. This does not require the exponent to be integrable. -/
theorem integrable_exp_of_ae_le_one (P : Measure Ω) [IsFiniteMeasure P]
    {Y : Ω → ℝ} (hY : Measurable Y) (hYle : ∀ᵐ ω ∂P, Y ω ≤ 1) :
    Integrable (fun ω => Real.exp (Y ω)) P := by
  refine (integrable_const (Real.exp 1) :
    Integrable (fun _ : Ω => Real.exp 1) P).mono' hY.exp.aestronglyMeasurable ?_
  filter_upwards [hYle] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr hω

/-- Integrability needed before conditional monotonicity: an upper increment
bound controls the positive exponential, even when the negative tail is unbounded. -/
theorem integrable_exp_mul (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Measurable X) {R lam : ℝ}
    (hR : 0 < R) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R)
    (hXle : ∀ᵐ ω ∂P, X ω ≤ R) :
    Integrable (fun ω => Real.exp (lam * X ω)) P := by
  exact integrable_exp_of_ae_le_one P (measurable_const.mul hX)
    (ae_mul_le_one P hR hlam0 hlam1 hXle)

/-- Both moment assumptions are used in the polynomial majorant for the
conditional MGF comparison. The quadratic coefficient may be any real number. -/
theorem integrable_mgf_majorant (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hint : Integrable X P)
    (hint2 : Integrable (fun ω => X ω ^ 2) P) (c lam : ℝ) :
    Integrable (fun ω => 1 + lam * X ω + c * lam ^ 2 * X ω ^ 2) P := by
  exact ((integrable_const (1 : ℝ)).add (hint.const_mul lam)).add
    (hint2.const_mul (c * lam ^ 2))

/-- Subtracting any nonnegative measurable compensation keeps the one-step
exponential bounded and integrable. No boundedness of the compensation is needed. -/
theorem integrable_exp_mul_sub_nonneg (P : Measure Ω) [IsProbabilityMeasure P]
    {X A : Ω → ℝ} (hX : Measurable X) (hA : Measurable A)
    {R lam : ℝ} (hR : 0 < R) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R)
    (hXle : ∀ᵐ ω ∂P, X ω ≤ R) (hAnonneg : ∀ᵐ ω ∂P, 0 ≤ A ω) :
    Integrable (fun ω => Real.exp (lam * X ω - A ω)) P := by
  apply integrable_exp_of_ae_le_one P ((measurable_const.mul hX).sub hA)
  filter_upwards [ae_mul_le_one P hR hlam0 hlam1 hXle, hAnonneg] with ω hω hAω
  exact le_trans (sub_le_self _ hAω) hω

/-- A bounded past weight can multiply an integrable increment exponential. -/
theorem integrable_bounded_weight_mul_exp (P : Measure Ω) [IsProbabilityMeasure P]
    {X H : Ω → ℝ} (hX : Measurable X) (hH : AEStronglyMeasurable H P)
    {R lam C : ℝ} (hR : 0 < R) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R)
    (hXle : ∀ᵐ ω ∂P, X ω ≤ R) (hHbound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ C) :
    Integrable (fun ω => H ω * Real.exp (lam * X ω)) P := by
  exact (integrable_exp_mul P hX hR hlam0 hlam1 hXle).bdd_mul hH hHbound

end FreedmanNativeIntegrability


set_option autoImplicit false

namespace FreedmanNative.ConditionalMGF

open MeasureTheory
open scoped MeasureTheory

variable {Ω : Type*}
variable {m mΩ : MeasurableSpace Ω}
variable {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]

/-- Conditional expectation of the quadratic upper envelope, with its exact
canonical conditional-expectation representatives. -/
theorem condExp_quadratic_envelope {X : Ω → ℝ} {lam c : ℝ}
    (hm : m ≤ mΩ) (hint : Integrable X P)
    (hint2 : Integrable (fun ω => X ω ^ 2) P)
    (hzero : condExp m P X =ᵐ[P] 0) :
    condExp m P (fun ω => 1 + lam * X ω + (c * lam ^ 2) * X ω ^ 2) =ᵐ[P]
      (fun ω => 1 + (c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω) := by
  have hlinInt : Integrable (fun ω => lam * X ω) P := hint.const_mul lam
  have hquadInt : Integrable (fun ω => (c * lam ^ 2) * X ω ^ 2) P :=
    hint2.const_mul (c * lam ^ 2)
  have hadd₁ := condExp_add (μ := P) (integrable_const (1 : ℝ)) hlinInt m
  have hadd₂ := condExp_add (μ := P) ((integrable_const (1 : ℝ)).add hlinInt) hquadInt m
  have hlin := condExp_smul (μ := P) lam X m
  have hquad := condExp_smul (μ := P) (c * lam ^ 2) (fun ω => X ω ^ 2) m
  filter_upwards [hadd₁, hadd₂, hlin, hquad, hzero] with ω h₁ h₂ hL hQ hZ
  change condExp m P (fun u => 1 + lam * X u) ω =
    condExp m P (fun _ : Ω => (1 : ℝ)) ω +
      condExp m P (fun u => lam * X u) ω at h₁
  change condExp m P (fun u => 1 + lam * X u + (c * lam ^ 2) * X u ^ 2) ω =
    condExp m P (fun u => 1 + lam * X u) ω +
      condExp m P (fun u => (c * lam ^ 2) * X u ^ 2) ω at h₂
  change condExp m P (fun u => lam * X u) ω = lam * condExp m P X ω at hL
  change condExp m P (fun u => (c * lam ^ 2) * X u ^ 2) ω =
    (c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω at hQ
  change condExp m P X ω = 0 at hZ
  have hconst : condExp m P (fun _ : Ω => (1 : ℝ)) ω = 1 := by
    rw [condExp_const hm]
  calc
    condExp m P (fun u => 1 + lam * X u + (c * lam ^ 2) * X u ^ 2) ω =
        condExp m P (fun u => 1 + lam * X u) ω +
          condExp m P (fun u => (c * lam ^ 2) * X u ^ 2) ω := h₂
    _ = 1 + (c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω := by
      rw [h₁, hL, hQ, hconst, hZ]
      ring

/-- The conditional MGF step needs integrability of the exponential, not
integrability of its random conditional-variance exponential. -/
theorem condExp_exp_le_exp_of_ae_quadratic {X : Ω → ℝ} {lam c : ℝ}
    (hm : m ≤ mΩ) (hint : Integrable X P)
    (hint2 : Integrable (fun ω => X ω ^ 2) P)
    (hexp : Integrable (fun ω => Real.exp (lam * X ω)) P)
    (hzero : condExp m P X =ᵐ[P] 0)
    (hbound : ∀ᵐ ω ∂P, Real.exp (lam * X ω) ≤
      1 + lam * X ω + (c * lam ^ 2) * X ω ^ 2) :
    ∀ᵐ ω ∂P, condExp m P (fun u => Real.exp (lam * X u)) ω ≤
      Real.exp ((c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω) := by
  have hdomInt : Integrable
      (fun ω => 1 + lam * X ω + (c * lam ^ 2) * X ω ^ 2) P :=
    ((integrable_const (1 : ℝ)).add (hint.const_mul lam)).add
      (hint2.const_mul (c * lam ^ 2))
  have hmono := condExp_mono (m := m) (μ := P) hexp hdomInt hbound
  have henv := condExp_quadratic_envelope (lam := lam) (c := c) hm hint hint2 hzero
  filter_upwards [hmono, henv] with ω hM hE
  calc
    condExp m P (fun u => Real.exp (lam * X u)) ω ≤
        condExp m P (fun u => 1 + lam * X u + (c * lam ^ 2) * X u ^ 2) ω := hM
    _ = 1 + (c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω := hE
    _ ≤ Real.exp ((c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω) := by
      linarith [Real.add_one_le_exp ((c * lam ^ 2) *
        condExp m P (fun u => X u ^ 2) ω)]

/-- A scalar upper-envelope theorem is passed explicitly. This helper does
not treat the scalar Freedman estimate as an unproved theorem. -/
theorem condExp_mgf_from_scalar {X : Ω → ℝ} {lam c : ℝ}
    (hm : m ≤ mΩ) (hint : Integrable X P)
    (hint2 : Integrable (fun ω => X ω ^ 2) P)
    (hexp : Integrable (fun ω => Real.exp (lam * X ω)) P)
    (hzero : condExp m P X =ᵐ[P] 0)
    (hscaled : ∀ᵐ ω ∂P, lam * X ω ≤ 1)
    (hscalar : ∀ y : ℝ, y ≤ 1 → Real.exp y ≤ 1 + y + c * y ^ 2) :
    ∀ᵐ ω ∂P, condExp m P (fun u => Real.exp (lam * X u)) ω ≤
      Real.exp ((c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω) := by
  apply condExp_exp_le_exp_of_ae_quadratic hm hint hint2 hexp hzero
  filter_upwards [hscaled] with ω hω
  calc
    Real.exp (lam * X ω) ≤ 1 + lam * X ω + c * (lam * X ω) ^ 2 :=
      hscalar _ hω
    _ = 1 + lam * X ω + (c * lam ^ 2) * X ω ^ 2 := by ring

end FreedmanNative.ConditionalMGF


set_option autoImplicit false

namespace TamingMonster.Regret.NativeFreedmanRepresentatives

open MeasureTheory
open scoped MeasureTheory

variable {Ω : Type*}

/-- The exact canonical square-moment representative occurring in the target. -/
noncomputable def squareCE (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω) (X : Ω → ℝ) : Ω → ℝ :=
  condExp m P (fun ω => X ω ^ 2)

/-- The compensator uses the same association as the one-step MGF bound. -/
noncomputable def compensator (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (X : Ω → ℝ) (c lam : ℝ) : Ω → ℝ :=
  fun ω => (c * lam ^ 2) * squareCE m P X ω

/-- The bounded factor is defined using the original conditional expectation. -/
noncomputable def decayFactor (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (X : Ω → ℝ) (c lam : ℝ) : Ω → ℝ :=
  fun ω => Real.exp (-compensator m P X c lam ω)

/-- The normalized one-step exponential; no integrability of `exp(compensator)` is needed. -/
noncomputable def compensatedExp (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (X : Ω → ℝ) (c lam : ℝ) : Ω → ℝ :=
  fun ω => Real.exp (lam * X ω - compensator m P X c lam ω)

theorem stronglyMeasurable_squareCE (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω) (X : Ω → ℝ) :
    StronglyMeasurable[m] (squareCE m P X) := by
  exact stronglyMeasurable_condExp

theorem measurable_squareCE (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω) (X : Ω → ℝ) :
    @Measurable Ω ℝ m (borel ℝ) (squareCE m P X) := by
  exact (stronglyMeasurable_squareCE m P X).measurable

theorem integrable_squareCE (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω) (X : Ω → ℝ) :
    Integrable (squareCE m P X) P := by
  exact integrable_condExp

theorem squareCE_ae_nonneg (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω) (X : Ω → ℝ) :
    ∀ᵐ ω ∂P, 0 ≤ squareCE m P X ω := by
  exact condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg (X ω))

theorem squareCE_setIntegral {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hm : m ≤ mΩ)
    (hint2 : Integrable (fun ω => X ω ^ 2) P) {s : Set Ω}
    (hs : MeasurableSet[m] s) :
    ∫ ω in s, squareCE m P X ω ∂P = ∫ ω in s, X ω ^ 2 ∂P := by
  exact setIntegral_condExp hm hint2 hs

theorem squareCE_congr_ae {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω}
    {X Y : Ω → ℝ} (hXY : X =ᵐ[P] Y) :
    squareCE m P X =ᵐ[P] squareCE m P Y := by
  exact condExp_congr_ae (hXY.fun_comp (fun x : ℝ => x ^ 2))

theorem stronglyMeasurable_compensator (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (X : Ω → ℝ) (c lam : ℝ) :
    StronglyMeasurable[m] (compensator m P X c lam) := by
  exact Continuous.comp_stronglyMeasurable
    (g := fun q : ℝ => (c * lam ^ 2) * q) (by fun_prop)
    (stronglyMeasurable_squareCE m P X)

theorem stronglyMeasurable_decayFactor (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (X : Ω → ℝ) (c lam : ℝ) :
    StronglyMeasurable[m] (decayFactor m P X c lam) := by
  exact Continuous.comp_stronglyMeasurable
    (g := fun q : ℝ => Real.exp (-q)) (by fun_prop)
    (stronglyMeasurable_compensator m P X c lam)

theorem compensator_ae_nonneg (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (X : Ω → ℝ) {c : ℝ} (hc : 0 ≤ c) (lam : ℝ) :
    ∀ᵐ ω ∂P, 0 ≤ compensator m P X c lam ω := by
  filter_upwards [squareCE_ae_nonneg m P X] with ω hω
  exact mul_nonneg (mul_nonneg hc (sq_nonneg lam)) hω

theorem decayFactor_pos (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (X : Ω → ℝ) (c lam : ℝ) (ω : Ω) :
    0 < decayFactor m P X c lam ω := by
  exact Real.exp_pos _

theorem decayFactor_ae_le_one (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (X : Ω → ℝ) {c : ℝ} (hc : 0 ≤ c) (lam : ℝ) :
    ∀ᵐ ω ∂P, decayFactor m P X c lam ω ≤ 1 := by
  filter_upwards [compensator_ae_nonneg m P X hc lam] with ω hω
  change Real.exp (-compensator m P X c lam ω) ≤ 1
  calc
    Real.exp (-compensator m P X c lam ω) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr (neg_nonpos.mpr hω)
    _ = 1 := Real.exp_zero

theorem decayFactor_ae_norm_le_one (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (X : Ω → ℝ) {c : ℝ} (hc : 0 ≤ c) (lam : ℝ) :
    ∀ᵐ ω ∂P, ‖decayFactor m P X c lam ω‖ ≤ 1 := by
  filter_upwards [decayFactor_ae_le_one m P X hc lam] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (decayFactor_pos m P X c lam ω)]
  exact hω

theorem integrable_decayFactor {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω}
    [IsFiniteMeasure P] {X : Ω → ℝ} (hm : m ≤ mΩ)
    {c : ℝ} (hc : 0 ≤ c) (lam : ℝ) :
    Integrable (decayFactor m P X c lam) P := by
  exact (integrable_const (1 : ℝ)).mono'
    ((stronglyMeasurable_decayFactor m P X c lam).mono hm).aestronglyMeasurable
    (decayFactor_ae_norm_le_one m P X hc lam)

theorem integrable_decayFactor_mul {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω}
    {X G : Ω → ℝ} (hm : m ≤ mΩ) {c : ℝ} (hc : 0 ≤ c) (lam : ℝ)
    (hG : Integrable G P) :
    Integrable (fun ω => decayFactor m P X c lam ω * G ω) P := by
  exact hG.bdd_mul
    ((stronglyMeasurable_decayFactor m P X c lam).mono hm).aestronglyMeasurable
    (decayFactor_ae_norm_le_one m P X hc lam)

theorem condExp_decayFactor_mul {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω}
    {X G : Ω → ℝ} (hm : m ≤ mΩ) {c : ℝ} (hc : 0 ≤ c) (lam : ℝ)
    (hG : Integrable G P) :
    condExp m P (fun ω => decayFactor m P X c lam ω * G ω) =ᵐ[P]
      fun ω => decayFactor m P X c lam ω * condExp m P G ω := by
  exact condExp_mul_of_stronglyMeasurable_left
    (stronglyMeasurable_decayFactor m P X c lam)
    (integrable_decayFactor_mul hm hc lam hG) hG

/-- Normalize an MGF bound without requiring an integrable positive exponential compensator. -/
theorem condExp_decayFactor_mul_le_one {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω}
    {X G : Ω → ℝ} (hm : m ≤ mΩ) {c : ℝ} (hc : 0 ≤ c) (lam : ℝ)
    (hG : Integrable G P)
    (hMGF : ∀ᵐ ω ∂P,
      condExp m P G ω ≤ Real.exp ((c * lam ^ 2) * squareCE m P X ω)) :
    ∀ᵐ ω ∂P,
      condExp m P (fun u => decayFactor m P X c lam u * G u) ω ≤ 1 := by
  filter_upwards [condExp_decayFactor_mul hm hc lam hG, hMGF] with ω hω hbound
  change condExp m P (fun u => decayFactor m P X c lam u * G u) ω =
    decayFactor m P X c lam ω * condExp m P G ω at hω
  rw [hω]
  calc
    decayFactor m P X c lam ω * condExp m P G ω ≤
        decayFactor m P X c lam ω *
          Real.exp ((c * lam ^ 2) * squareCE m P X ω) :=
      mul_le_mul_of_nonneg_left hbound (le_of_lt (decayFactor_pos m P X c lam ω))
    _ = 1 := by
      dsimp [decayFactor, compensator]
      rw [← Real.exp_add]
      simp

theorem compensatedExp_eq_product (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (X : Ω → ℝ) (c lam : ℝ) :
    compensatedExp m P X c lam =
      fun ω => decayFactor m P X c lam ω * Real.exp (lam * X ω) := by
  funext ω
  dsimp [compensatedExp, decayFactor]
  rw [← Real.exp_add]
  congr 1
  ring

theorem integrable_compensatedExp {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω}
    {X : Ω → ℝ} (hm : m ≤ mΩ) {c : ℝ} (hc : 0 ≤ c) (lam : ℝ)
    (hExp : Integrable (fun ω => Real.exp (lam * X ω)) P) :
    Integrable (compensatedExp m P X c lam) P := by
  rw [compensatedExp_eq_product]
  exact integrable_decayFactor_mul hm hc lam hExp

theorem condExp_compensatedExp_le_one {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω}
    {X : Ω → ℝ} (hm : m ≤ mΩ) {c : ℝ} (hc : 0 ≤ c) (lam : ℝ)
    (hExp : Integrable (fun ω => Real.exp (lam * X ω)) P)
    (hMGF : ∀ᵐ ω ∂P,
      condExp m P (fun u => Real.exp (lam * X u)) ω ≤
        Real.exp ((c * lam ^ 2) * squareCE m P X ω)) :
    ∀ᵐ ω ∂P, condExp m P (compensatedExp m P X c lam) ω ≤ 1 := by
  rw [compensatedExp_eq_product]
  exact condExp_decayFactor_mul_le_one hm hc lam hExp hMGF

/-- The one-step integrability conclusion with all representatives exposed literally. -/
theorem integrable_exp_compensated {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω}
    {X : Ω → ℝ} (hm : m ≤ mΩ) {c : ℝ} (hc : 0 ≤ c) (lam : ℝ)
    (hExp : Integrable (fun ω => Real.exp (lam * X ω)) P) :
    Integrable (fun ω => Real.exp (lam * X ω -
      (c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω)) P := by
  exact integrable_compensatedExp hm hc lam hExp

/-- The exact normalized conditional step, with no change of representatives. -/
theorem condExp_exp_compensated_le_one {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω}
    {X : Ω → ℝ} (hm : m ≤ mΩ) {c : ℝ} (hc : 0 ≤ c) (lam : ℝ)
    (hExp : Integrable (fun ω => Real.exp (lam * X ω)) P)
    (hMGF : ∀ᵐ ω ∂P,
      condExp m P (fun u => Real.exp (lam * X u)) ω ≤
        Real.exp ((c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω)) :
    ∀ᵐ ω ∂P,
      condExp m P (fun u => Real.exp (lam * X u -
        (c * lam ^ 2) * condExp m P (fun v => X v ^ 2) u)) ω ≤ 1 := by
  exact condExp_compensatedExp_le_one hm hc lam hExp hMGF

end TamingMonster.Regret.NativeFreedmanRepresentatives


namespace FreedmanNative.ConditionalMGF

open MeasureTheory
open scoped MeasureTheory

variable {Ω : Type*}
variable {m mΩ : MeasurableSpace Ω}
variable {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]

/-- The exact one-sided bounded-increment hypotheses imply the conditional
MGF estimate once the scalar Freedman upper envelope is supplied. -/
theorem conditional_mgf_step_from_scalar {X : Ω → ℝ} {R lam c : ℝ}
    (hm : m ≤ mΩ) (hmeas : Measurable X) (hint : Integrable X P)
    (hint2 : Integrable (fun ω => X ω ^ 2) P)
    (hR : 0 < R) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R)
    (hle : ∀ᵐ ω ∂P, X ω ≤ R)
    (hmart : condExp m P X =ᵐ[P] 0)
    (hscalar : ∀ y : ℝ, y ≤ 1 → Real.exp y ≤ 1 + y + c * y ^ 2) :
    Integrable (fun ω => Real.exp (lam * X ω)) P ∧
      ∀ᵐ ω ∂P, condExp m P (fun u => Real.exp (lam * X u)) ω ≤
        Real.exp ((c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω) := by
  have hexp : Integrable (fun ω => Real.exp (lam * X ω)) P :=
    FreedmanNativeIntegrability.integrable_exp_mul P hmeas hR hlam0 hlam1 hle
  refine ⟨hexp, ?_⟩
  exact condExp_mgf_from_scalar hm hint hint2 hexp hmart
    (FreedmanNativeIntegrability.ae_mul_le_one P hR hlam0 hlam1 hle) hscalar

end FreedmanNative.ConditionalMGF

namespace FreedmanNative.ConditionalMGF

open MeasureTheory
open scoped MeasureTheory

variable {Ω : Type*}
variable {m mΩ : MeasurableSpace Ω}
variable {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]

/-- The coefficient in the frozen Freedman theorem is nonnegative. -/
theorem freedman_coefficient_nonneg : 0 ≤ Real.exp 1 - 2 := by
  linarith [Real.add_one_le_exp (1 : ℝ)]

/-- The bounded compensator normalizes the one-step MGF without any
integrability assumption on the positive exponential of the variance. -/
theorem conditional_compensated_step_from_scalar {X : Ω → ℝ} {R lam c : ℝ}
    (hm : m ≤ mΩ) (hmeas : Measurable X) (hint : Integrable X P)
    (hint2 : Integrable (fun ω => X ω ^ 2) P)
    (hR : 0 < R) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R)
    (hle : ∀ᵐ ω ∂P, X ω ≤ R)
    (hmart : condExp m P X =ᵐ[P] 0) (hc : 0 ≤ c)
    (hscalar : ∀ y : ℝ, y ≤ 1 → Real.exp y ≤ 1 + y + c * y ^ 2) :
    Integrable (fun ω => Real.exp (lam * X ω -
      (c * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω)) P ∧
    ∀ᵐ ω ∂P, condExp m P (fun u => Real.exp (lam * X u -
      (c * lam ^ 2) * condExp m P (fun z => X z ^ 2) u)) ω ≤ 1 := by
  obtain ⟨hExp, hMGF⟩ := conditional_mgf_step_from_scalar
    hm hmeas hint hint2 hR hlam0 hlam1 hle hmart hscalar
  have hMGF' : ∀ᵐ ω ∂P, condExp m P (fun u => Real.exp (lam * X u)) ω ≤
      Real.exp ((c * lam ^ 2) *
        TamingMonster.Regret.NativeFreedmanRepresentatives.squareCE m P X ω) := by
    simpa [TamingMonster.Regret.NativeFreedmanRepresentatives.squareCE] using hMGF
  constructor
  · exact TamingMonster.Regret.NativeFreedmanRepresentatives.integrable_compensatedExp
      hm hc lam hExp
  · exact TamingMonster.Regret.NativeFreedmanRepresentatives.condExp_compensatedExp_le_one
      hm hc lam hExp hMGF'

/-- The compensated estimate with exactly the coefficient and lambda range
in the frozen statement. Its scalar theorem is the disjoint analysis subtask. -/
theorem conditional_freedman_step_from_scalar {X : Ω → ℝ} {R lam : ℝ}
    (hm : m ≤ mΩ) (hmeas : Measurable X) (hint : Integrable X P)
    (hint2 : Integrable (fun ω => X ω ^ 2) P)
    (hR : 0 < R) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R)
    (hle : ∀ᵐ ω ∂P, X ω ≤ R)
    (hmart : condExp m P X =ᵐ[P] 0)
    (hscalar : ∀ y : ℝ, y ≤ 1 →
      Real.exp y ≤ 1 + y + (Real.exp 1 - 2) * y ^ 2) :
    Integrable (fun ω => Real.exp (lam * X ω -
      ((Real.exp 1 - 2) * lam ^ 2) * condExp m P (fun u => X u ^ 2) ω)) P ∧
    ∀ᵐ ω ∂P, condExp m P (fun u => Real.exp (lam * X u -
      ((Real.exp 1 - 2) * lam ^ 2) * condExp m P (fun z => X z ^ 2) u)) ω ≤ 1 := by
  exact conditional_compensated_step_from_scalar hm hmeas hint hint2
    hR hlam0 hlam1 hle hmart freedman_coefficient_nonneg hscalar

end FreedmanNative.ConditionalMGF

namespace TamingMonster.Regret.FreedmanAux

open MeasureTheory
open scoped MeasureTheory

/-- The finite-measure interface needs only nonnegative lambda and an upper
bound. No positivity of R or upper restriction on lambda is necessary here. -/
theorem integrable_exp_mul {Ω : Type*} {m0 : MeasurableSpace Ω}
    {P : Measure[m0] Ω} [IsFiniteMeasure P] {X : Ω → ℝ} {R lam : ℝ}
    (hX : Measurable[m0] X) (hle : ∀ᵐ ω ∂P, X ω ≤ R) (hlam : 0 ≤ lam) :
    Integrable (fun ω => Real.exp (lam * X ω)) P := by
  refine (integrable_const (Real.exp (lam * R)) :
    Integrable (fun _ : Ω => Real.exp (lam * R)) P).mono'
      (measurable_const.mul hX).exp.aestronglyMeasurable ?_
  filter_upwards [hle] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hlam)

/-- Integrator-facing conditional estimate. The scalar premise is discharged
by analysis-prover's exp_le_one_add_add_c_sq when composing the full source. -/
theorem condExp_exp_mul_le_of_scalar {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (hm : m ≤ m0) {P : Measure[m0] Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {R lam : ℝ} (hR : 0 < R)
    (hX : Measurable[m0] X) (hXi : Integrable X P)
    (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (hle : ∀ᵐ ω ∂P, X ω ≤ R) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R)
    (hmart : condExp m P X =ᵐ[P] 0)
    (hscalar : ∀ y : ℝ, y ≤ 1 →
      Real.exp y ≤ 1 + y + (Real.exp 1 - 2) * y ^ 2) :
    condExp m P (fun ω => Real.exp (lam * X ω)) ≤ᵐ[P]
      fun ω => Real.exp ((Real.exp 1 - 2) * lam ^ 2 *
        condExp m P (fun u => X u ^ 2) ω) := by
  exact (FreedmanNative.ConditionalMGF.conditional_mgf_step_from_scalar
    (mΩ := m0) hm hX hXi hX2 hR hlam0 hlam1 hle hmart hscalar).2

/-- The compensated version uses exactly the same original square-moment
representative and the literal coefficient from the frozen statement. -/
theorem condExp_compensated_exp_le_one_of_scalar {Ω : Type*}
    {m m0 : MeasurableSpace Ω} (hm : m ≤ m0)
    {P : Measure[m0] Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {R lam : ℝ}
    (hR : 0 < R) (hX : Measurable[m0] X) (hXi : Integrable X P)
    (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (hle : ∀ᵐ ω ∂P, X ω ≤ R) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R)
    (hmart : condExp m P X =ᵐ[P] 0)
    (hscalar : ∀ y : ℝ, y ≤ 1 →
      Real.exp y ≤ 1 + y + (Real.exp 1 - 2) * y ^ 2) :
    Integrable (fun ω => Real.exp (lam * X ω -
      (Real.exp 1 - 2) * lam ^ 2 * condExp m P (fun u => X u ^ 2) ω)) P ∧
    ∀ᵐ ω ∂P, condExp m P (fun u => Real.exp (lam * X u -
      (Real.exp 1 - 2) * lam ^ 2 * condExp m P (fun z => X z ^ 2) u)) ω ≤ 1 := by
  exact FreedmanNative.ConditionalMGF.conditional_freedman_step_from_scalar
    (mΩ := m0) hm hX hXi hX2 hR hlam0 hlam1 hle hmart hscalar

end TamingMonster.Regret.FreedmanAux

namespace TamingMonster.Regret.FreedmanAux

open MeasureTheory
open scoped MeasureTheory

/-- Exact integrator interface: the scalar upper envelope is now proved by
the included exp_le_one_add_add_c_sq, not assumed by the caller. -/
theorem condExp_exp_mul_le {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (hm : m ≤ m0) {P : Measure[m0] Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {R lam : ℝ} (hR : 0 < R)
    (hX : Measurable[m0] X) (hXi : Integrable X P)
    (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (hle : ∀ᵐ ω ∂P, X ω ≤ R) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R)
    (hmart : condExp m P X =ᵐ[P] 0) :
    condExp m P (fun ω => Real.exp (lam * X ω)) ≤ᵐ[P]
      fun ω => Real.exp ((Real.exp 1 - 2) * lam ^ 2 *
        condExp m P (fun u => X u ^ 2) ω) := by
  exact condExp_exp_mul_le_of_scalar hm hR hX hXi hX2 hle hlam0 hlam1 hmart
    (fun y hy => exp_le_one_add_add_c_sq hy)

/-- The canonical one-step compensated exponential is integrable and has
conditional expectation at most one, with no scalar estimate left as a premise. -/
theorem integrable_and_condExp_compensated_exp_le_one {Ω : Type*}
    {m m0 : MeasurableSpace Ω} (hm : m ≤ m0)
    {P : Measure[m0] Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {R lam : ℝ}
    (hR : 0 < R) (hX : Measurable[m0] X) (hXi : Integrable X P)
    (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (hle : ∀ᵐ ω ∂P, X ω ≤ R) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R)
    (hmart : condExp m P X =ᵐ[P] 0) :
    Integrable (fun ω => Real.exp (lam * X ω -
      (Real.exp 1 - 2) * lam ^ 2 * condExp m P (fun u => X u ^ 2) ω)) P ∧
    ∀ᵐ ω ∂P, condExp m P (fun u => Real.exp (lam * X u -
      (Real.exp 1 - 2) * lam ^ 2 * condExp m P (fun z => X z ^ 2) u)) ω ≤ 1 := by
  exact condExp_compensated_exp_le_one_of_scalar hm hR hX hXi hX2
    hle hlam0 hlam1 hmart (fun y hy => exp_le_one_add_add_c_sq hy)

end TamingMonster.Regret.FreedmanAux

/-! ### Part: proof-reviewer FreedmanHelpers aef06d9f + integrator exact-hstep fix (sha256 bca65721d5f51fed96182c2ca351a849da5fc56d6844c425a1dfbe0239861e81) -/
namespace NativeFreedmanInduction

open MeasureTheory
open scoped MeasureTheory

set_option autoImplicit false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Integrating a conditional bound. The integrability premise on `Y` is kept explicit
for composition with the process construction; total-integral preservation is unconditional. -/
theorem integral_le_of_condExp_le
    (P : Measure Ω) [IsFiniteMeasure P] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {Y Z : Ω → ℝ}
    (_hY : Integrable Y P) (hZ : Integrable Z P)
    (hstep : P[Y | m] ≤ᵐ[P] Z) :
    (∫ ω, Y ω ∂P) ≤ ∫ ω, Z ω ∂P := by
  calc
    (∫ ω, Y ω ∂P) = ∫ ω, P[Y | m] ω ∂P :=
      (integral_condExp (μ := P) (f := Y) hm).symm
    _ ≤ ∫ ω, Z ω ∂P :=
      integral_mono_ae integrable_condExp hZ hstep

/-- A finite-horizon conditional step decreases the integral at that step. -/
theorem integral_process_step_le
    (P : Measure Ω) [IsFiniteMeasure P]
    (m : ℕ → MeasurableSpace Ω) (process : ℕ → Ω → ℝ)
    (n : ℕ) (hm : m n ≤ mΩ)
    (hnext : Integrable (process (n + 1)) P)
    (hnow : Integrable (process n) P)
    (hstep : P[process (n + 1) | m n] ≤ᵐ[P] process n) :
    (∫ ω, process (n + 1) ω ∂P) ≤ ∫ ω, process n ω ∂P := by
  exact integral_le_of_condExp_le P hm hnext hnow hstep

/-- No adaptedness or monotonicity of `m` is needed once the exact conditional steps
and their integrability have been proved. All premises are exposed to the caller. -/
theorem integral_process_le_one
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ → MeasurableSpace Ω) (process : ℕ → Ω → ℝ)
    (hm : ∀ n, m n ≤ mΩ)
    (hint : ∀ n, Integrable (process n) P)
    (hzero : process 0 =ᵐ[P] fun _ : Ω => (1 : ℝ))
    (hstep : ∀ n, P[process (n + 1) | m n] ≤ᵐ[P] process n)
    (n : ℕ) : (∫ ω, process n ω ∂P) ≤ 1 := by
  induction n with
  | zero =>
      calc
        (∫ ω, process 0 ω ∂P) = ∫ _ : Ω, (1 : ℝ) ∂P :=
          integral_congr_ae hzero
        _ ≤ 1 := by simp
  | succ n ih =>
      exact (integral_process_step_le P m process n (hm n)
        (hint (n + 1)) (hint n) (hstep n)).trans ih

/-- Horizon-restricted form: no assumptions at times beyond `T` are required. -/
theorem integral_process_le_one_finite
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ) (m : ℕ → MeasurableSpace Ω) (process : ℕ → Ω → ℝ)
    (hm : ∀ n, n < T → m n ≤ mΩ)
    (hint : ∀ n, n ≤ T → Integrable (process n) P)
    (hzero : process 0 =ᵐ[P] fun _ : Ω => (1 : ℝ))
    (hstep : ∀ n, n < T → P[process (n + 1) | m n] ≤ᵐ[P] process n) :
    ∀ n, n ≤ T → (∫ ω, process n ω ∂P) ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro _hn
      calc
        (∫ ω, process 0 ω ∂P) = ∫ _ : Ω, (1 : ℝ) ∂P :=
          integral_congr_ae hzero
        _ ≤ 1 := by simp
  | succ n ih =>
      intro hn
      have hnlt : n < T := Nat.lt_of_succ_le hn
      have hnle : n ≤ T := Nat.le_of_lt hnlt
      exact (integral_process_step_le P m process n (hm n hnlt)
        (hint (n + 1) hn) (hint n hnle) (hstep n hnlt)).trans (ih hnle)

/-- The exponential process with exactly the `Icc 1 n` sums from the frozen target.
`past t` is the sigma algebra used to condition the square of increment `t`. -/
noncomputable def freedmanProcess
    (P : Measure Ω) (past : ℕ → MeasurableSpace Ω)
    (Xs : ℕ → Ω → ℝ) (lam : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (lam * (∑ t ∈ Finset.Icc 1 n, Xs t ω) -
    (Real.exp 1 - 2) * lam ^ 2 *
      (∑ t ∈ Finset.Icc 1 n,
        condExp (past t) P (fun ω' => Xs t ω' ^ 2) ω))

@[simp]
theorem freedmanProcess_zero
    (P : Measure Ω) (past : ℕ → MeasurableSpace Ω)
    (Xs : ℕ → Ω → ℝ) (lam : ℝ) (ω : Ω) :
    freedmanProcess P past Xs lam 0 ω = 1 := by
  simp [freedmanProcess]

/-- Compositional exponential-process specialization. The conditioning of the step
`n` to `n+1` is `past (n+1)`. Integrability and the exponential conditional bound
remain explicit proof obligations, rather than consequences asserted here. -/
theorem integral_freedmanProcess_le_one
    (P : Measure Ω) [IsProbabilityMeasure P]
    (past : ℕ → MeasurableSpace Ω) (Xs : ℕ → Ω → ℝ)
    (lam : ℝ) (T : ℕ)
    (hpast : ∀ n, n < T → past (n + 1) ≤ mΩ)
    (hint : ∀ n, n ≤ T → Integrable (freedmanProcess P past Xs lam n) P)
    (hstep : ∀ n, n < T →
      P[freedmanProcess P past Xs lam (n + 1) | past (n + 1)] ≤ᵐ[P]
        freedmanProcess P past Xs lam n) :
    (∫ ω, freedmanProcess P past Xs lam T ω ∂P) ≤ 1 := by
  have hzero : freedmanProcess P past Xs lam 0 =ᵐ[P] fun _ : Ω => (1 : ℝ) :=
    Filter.Eventually.of_forall (fun ω => freedmanProcess_zero P past Xs lam ω)
  exact integral_process_le_one_finite P T (fun n => past (n + 1))
    (freedmanProcess P past Xs lam) hpast hint hzero hstep T le_rfl

end NativeFreedmanInduction


namespace NativeFreedmanStep

open MeasureTheory
open scoped MeasureTheory

set_option autoImplicit false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A conditional exponential bound gives the compensated one-step bound.
All conditional expectations retain their original function representatives. -/
theorem condExp_compensated_step
    (P : Measure Ω) (m : MeasurableSpace Ω)
    (s v x a : Ω → ℝ) (c lam : ℝ)
    (hfactor : StronglyMeasurable[m]
      (fun ω => Real.exp (lam * s ω - c * lam ^ 2 * (v ω + a ω))))
    (hnext : Integrable
      (fun ω => Real.exp (lam * (s ω + x ω) - c * lam ^ 2 * (v ω + a ω))) P)
    (hinc : Integrable (fun ω => Real.exp (lam * x ω)) P)
    (hmgf : condExp m P (fun ω => Real.exp (lam * x ω)) ≤ᵐ[P]
      (fun ω => Real.exp (c * lam ^ 2 * a ω))) :
    condExp m P
      (fun ω => Real.exp (lam * (s ω + x ω) - c * lam ^ 2 * (v ω + a ω))) ≤ᵐ[P]
      (fun ω => Real.exp (lam * s ω - c * lam ^ 2 * v ω)) := by
  let F : Ω → ℝ := fun ω => Real.exp (lam * s ω - c * lam ^ 2 * (v ω + a ω))
  let E : Ω → ℝ := fun ω => Real.exp (lam * x ω)
  have hprod :
      (fun ω => Real.exp (lam * (s ω + x ω) - c * lam ^ 2 * (v ω + a ω))) =
        F * E := by
    funext ω
    change Real.exp _ = Real.exp _ * Real.exp _
    rw [← Real.exp_add]
    congr 1
    ring
  have hprodInt : Integrable (F * E) P := hprod ▸ hnext
  have hpull : condExp m P (F * E) =ᵐ[P] F * condExp m P E :=
    condExp_mul_of_stronglyMeasurable_left hfactor hprodInt hinc
  rw [hprod]
  filter_upwards [hpull, hmgf] with ω hp hm
  calc
    condExp m P (F * E) ω = F ω * condExp m P E ω := hp
    _ ≤ F ω * Real.exp (c * lam ^ 2 * a ω) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = Real.exp (lam * s ω - c * lam ^ 2 * v ω) := by
      dsimp [F]
      rw [← Real.exp_add]
      congr 1
      ring

/-- The polynomial conditional bound is enough; `1 + z ≤ exp z` supplies
the exponential conditional bound used by the transition theorem. -/
theorem condExp_compensated_step_of_linear_mgf
    (P : Measure Ω) (m : MeasurableSpace Ω)
    (s v x a : Ω → ℝ) (c lam : ℝ)
    (hfactor : StronglyMeasurable[m]
      (fun ω => Real.exp (lam * s ω - c * lam ^ 2 * (v ω + a ω))))
    (hnext : Integrable
      (fun ω => Real.exp (lam * (s ω + x ω) - c * lam ^ 2 * (v ω + a ω))) P)
    (hinc : Integrable (fun ω => Real.exp (lam * x ω)) P)
    (hmgf : condExp m P (fun ω => Real.exp (lam * x ω)) ≤ᵐ[P]
      (fun ω => 1 + c * lam ^ 2 * a ω)) :
    condExp m P
      (fun ω => Real.exp (lam * (s ω + x ω) - c * lam ^ 2 * (v ω + a ω))) ≤ᵐ[P]
      (fun ω => Real.exp (lam * s ω - c * lam ^ 2 * v ω)) := by
  apply condExp_compensated_step (mΩ := mΩ) P m s v x a c lam hfactor hnext hinc
  filter_upwards [hmgf] with ω hω
  exact hω.trans (by simpa [add_comm] using Real.add_one_le_exp (c * lam ^ 2 * a ω))

/-- The upper bound is one-sided: negative increments need no absolute bound. -/
theorem integrable_exp_of_upper_bound
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) {R lam : ℝ} (hlam : 0 ≤ lam)
    (hupper : ∀ᵐ ω ∂P, X ω ≤ R) :
    Integrable (fun ω => Real.exp (lam * X ω)) P := by
  apply (integrable_const (Real.exp (lam * R))).mono'
    ((hX.const_mul lam).exp.aestronglyMeasurable)
  filter_upwards [hupper] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hlam))

/-- The index recurrence is proved from membership, without changing the
frozen `Icc 1 n` convention into a different summation convention. -/
theorem sum_Icc_one_succ (f : ℕ → ℝ) (n : ℕ) :
    (∑ t ∈ Finset.Icc 1 (n + 1), f t) =
      (∑ t ∈ Finset.Icc 1 n, f t) + f (n + 1) := by
  have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert hnot]
  ring

/-- Finite-sum form of the compensated transition, ready to instantiate
`A t` by the exact conditional expectation of the squared increment. -/
theorem condExp_sum_process_succ
    (P : Measure Ω) (m : MeasurableSpace Ω)
    (Xs A : ℕ → Ω → ℝ) (c lam : ℝ) (n : ℕ)
    (hfactor : StronglyMeasurable[m]
      (fun ω => Real.exp
        (lam * (∑ t ∈ Finset.Icc 1 n, Xs t ω) - c * lam ^ 2 *
          ((∑ t ∈ Finset.Icc 1 n, A t ω) + A (n + 1) ω))))
    (hnext : Integrable
      (fun ω => Real.exp
        (lam * (∑ t ∈ Finset.Icc 1 (n + 1), Xs t ω) - c * lam ^ 2 *
          (∑ t ∈ Finset.Icc 1 (n + 1), A t ω))) P)
    (hinc : Integrable (fun ω => Real.exp (lam * Xs (n + 1) ω)) P)
    (hmgf : condExp m P (fun ω => Real.exp (lam * Xs (n + 1) ω)) ≤ᵐ[P]
      (fun ω => Real.exp (c * lam ^ 2 * A (n + 1) ω))) :
    condExp m P
      (fun ω => Real.exp
        (lam * (∑ t ∈ Finset.Icc 1 (n + 1), Xs t ω) - c * lam ^ 2 *
          (∑ t ∈ Finset.Icc 1 (n + 1), A t ω))) ≤ᵐ[P]
      (fun ω => Real.exp
        (lam * (∑ t ∈ Finset.Icc 1 n, Xs t ω) - c * lam ^ 2 *
          (∑ t ∈ Finset.Icc 1 n, A t ω))) := by
  have hnext' : Integrable
      (fun ω => Real.exp
        (lam * ((∑ t ∈ Finset.Icc 1 n, Xs t ω) + Xs (n + 1) ω) -
          c * lam ^ 2 * ((∑ t ∈ Finset.Icc 1 n, A t ω) + A (n + 1) ω))) P := by
    simpa only [sum_Icc_one_succ] using hnext
  simpa only [sum_Icc_one_succ] using
    condExp_compensated_step (mΩ := mΩ) P m
      (fun ω => ∑ t ∈ Finset.Icc 1 n, Xs t ω)
      (fun ω => ∑ t ∈ Finset.Icc 1 n, A t ω)
      (Xs (n + 1)) (A (n + 1)) c lam hfactor hnext' hinc hmgf

end NativeFreedmanStep


namespace TamingMonster.Regret.FreedmanAux

open MeasureTheory

set_option autoImplicit false

/-- `Z n = exp(λ S_n − (e−2) λ² V_n)`, with the exact condExp representatives of the target. -/
noncomputable def Zproc {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (F : ℕ → MeasurableSpace Ω) (Xs : ℕ → Ω → ℝ) (lam : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (lam * (∑ t ∈ Finset.Icc 1 n, Xs t ω)
    - (Real.exp 1 - 2) * lam ^ 2 *
      (∑ t ∈ Finset.Icc 1 n, condExp (F t) P (fun ω' => Xs t ω' ^ 2) ω))

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

lemma Zproc_nonneg (P : Measure Ω) (F : ℕ → MeasurableSpace Ω)
    (Xs : ℕ → Ω → ℝ) (lam : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ Zproc P F Xs lam n ω := by
  unfold Zproc
  exact (Real.exp_pos _).le

/-- This sign statement holds for every family of conditioning sigma algebras. -/
lemma conditional_square_sum_nonneg (P : Measure Ω) (F : ℕ → MeasurableSpace Ω)
    (Xs : ℕ → Ω → ℝ) (n : ℕ) :
    ∀ᵐ ω ∂P, 0 ≤ ∑ t ∈ Finset.Icc 1 n,
      condExp (F t) P (fun ω' => Xs t ω' ^ 2) ω := by
  have hall : ∀ᵐ ω ∂P, ∀ t : ℕ,
      0 ≤ condExp (F t) P (fun ω' => Xs t ω' ^ 2) ω :=
    ae_all_iff.2 (fun t => condExp_nonneg
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (Xs t ω))))
  filter_upwards [hall] with ω hω
  exact Finset.sum_nonneg (fun t _ht => hω t)

/-- The one-sided increment bounds alone give a deterministic upper bound in time.
No measurability or order assumptions on `F` are needed for this estimate. -/
theorem Zproc_ae_bounds
    (P : Measure Ω) (F : ℕ → MeasurableSpace Ω) (Xs : ℕ → Ω → ℝ)
    (T : ℕ) {R lam : ℝ}
    (hle : ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, Xs t ω ≤ R)
    (hlam : 0 ≤ lam) (hlamR : lam * R ≤ 1) {n : ℕ} (hn : n ≤ T) :
    ∀ᵐ ω ∂P, 0 ≤ Zproc P F Xs lam n ω ∧
      Zproc P F Xs lam n ω ≤ Real.exp n := by
  have hxall : ∀ᵐ ω ∂P, ∀ t ∈ Finset.Icc 1 T, Xs t ω ≤ R := by
    refine ae_all_iff.2 ?_
    intro t
    by_cases ht : t ∈ Finset.Icc 1 T
    · exact (hle t ht).mono (fun _ω hω => fun _hmem => hω)
    · exact Filter.Eventually.of_forall (fun _ω hmem => False.elim (ht hmem))
  have hcoef : 0 ≤ Real.exp 1 - 2 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  filter_upwards [hxall, conditional_square_sum_nonneg P F Xs n] with ω hx hV
  refine ⟨Zproc_nonneg P F Xs lam n ω, ?_⟩
  have hlinear : lam * (∑ t ∈ Finset.Icc 1 n, Xs t ω) ≤ (n : ℝ) := by
    calc
      lam * (∑ t ∈ Finset.Icc 1 n, Xs t ω) =
          ∑ t ∈ Finset.Icc 1 n, lam * Xs t ω := by rw [Finset.mul_sum]
      _ ≤ ∑ _t ∈ Finset.Icc 1 n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        have htT : t ∈ Finset.Icc 1 T :=
          Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1,
            (Finset.mem_Icc.mp ht).2.trans hn⟩
        exact (mul_le_mul_of_nonneg_left (hx t htT) hlam).trans hlamR
      _ = (n : ℝ) := by simp
  have hpenalty : 0 ≤ (Real.exp 1 - 2) * lam ^ 2 *
      (∑ t ∈ Finset.Icc 1 n, condExp (F t) P (fun ω' => Xs t ω' ^ 2) ω) :=
    mul_nonneg (mul_nonneg hcoef (sq_nonneg lam)) hV
  unfold Zproc
  apply Real.exp_le_exp.mpr
  exact (sub_le_self _ hpenalty).trans hlinear

/-- The exact arbitrary-filtration upper-bound contract used by the integrator. -/
theorem Zproc_ae_le_exp {P : Measure Ω} [IsProbabilityMeasure P]
    (F : ℕ → MeasurableSpace Ω) (Xs : ℕ → Ω → ℝ) (T : ℕ) {R lam : ℝ}
    (hR : 0 < R) (hle : ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, Xs t ω ≤ R)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R) {n : ℕ} (hn : n ≤ T) :
    ∀ᵐ ω ∂P, Zproc P F Xs lam n ω ≤ Real.exp n := by
  have hlamR : lam * R ≤ 1 := (le_div_iff₀ hR).mp hlam1
  exact (Zproc_ae_bounds P F Xs T hle hlam0.le hlamR hn).mono
    (fun _ω hω => hω.2)

/-- Global measurability follows by lifting each conditional square from `F t`
to the ambient sigma algebra. This is distinct from past strong measurability. -/
theorem measurable_Zproc (P : Measure Ω) (F : ℕ → MeasurableSpace Ω)
    (hFle : ∀ t, F t ≤ m0) (Xs : ℕ → Ω → ℝ)
    (hmeas : ∀ t, Measurable (Xs t)) (lam : ℝ) (n : ℕ) :
    Measurable (Zproc P F Xs lam n) := by
  have hcond : ∀ t : ℕ, Measurable (condExp (F t) P (fun ω => Xs t ω ^ 2)) := by
    intro t
    have hstrong : StronglyMeasurable[F t]
        (condExp (F t) P (fun ω => Xs t ω ^ 2)) := stronglyMeasurable_condExp
    exact (hstrong.mono (hFle t)).measurable
  have hS : Measurable (fun ω => ∑ t ∈ Finset.Icc 1 n, Xs t ω) :=
    Finset.measurable_sum _ (fun t _ht => hmeas t)
  have hV : Measurable (fun ω => ∑ t ∈ Finset.Icc 1 n,
      condExp (F t) P (fun ω' => Xs t ω' ^ 2) ω) :=
    Finset.measurable_sum _ (fun t _ht => hcond t)
  unfold Zproc
  exact ((hS.const_mul lam).sub
    (hV.const_mul ((Real.exp 1 - 2) * lam ^ 2))).exp

/-- Global measurability plus the exponential upper bound gives integrability. -/
theorem integrable_Zproc_of_bound {P : Measure Ω} [IsFiniteMeasure P]
    (F : ℕ → MeasurableSpace Ω) (Xs : ℕ → Ω → ℝ) (lam : ℝ) (n : ℕ)
    (hZ : Measurable (Zproc P F Xs lam n))
    (hbound : ∀ᵐ ω ∂P, Zproc P F Xs lam n ω ≤ Real.exp n) :
    Integrable (Zproc P F Xs lam n) P := by
  refine (integrable_const (μ := P) (Real.exp (n : ℝ))).mono'
    hZ.aestronglyMeasurable ?_
  filter_upwards [hbound] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Zproc_nonneg P F Xs lam n ω)] using hω

/-- Every time up to the horizon is integrable from the frozen upper bounds
and the global measurable-space inclusion, with no process-integrability premise. -/
theorem integrable_Zproc {P : Measure Ω} [IsProbabilityMeasure P]
    (F : ℕ → MeasurableSpace Ω) (hFle : ∀ t, F t ≤ m0)
    (Xs : ℕ → Ω → ℝ) (hmeas : ∀ t, Measurable (Xs t))
    (T : ℕ) {R lam : ℝ} (hR : 0 < R)
    (hle : ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, Xs t ω ≤ R)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R) {n : ℕ} (hn : n ≤ T) :
    Integrable (Zproc P F Xs lam n) P := by
  exact integrable_Zproc_of_bound F Xs lam n
    (measurable_Zproc P F hFle Xs hmeas lam n)
    (Zproc_ae_le_exp F Xs T hR hle hlam0 hlam1 hn)

end TamingMonster.Regret.FreedmanAux


set_option autoImplicit false

namespace NativeFreedmanTail

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The strict failure threshold gives a strict lower bound on the exponential.
The coefficient `c` is arbitrary; this step uses only `δ > 0` and `lam > 0`. -/
theorem strict_threshold_implies_exp_gt_inv
    {s v c δ lam : ℝ} (hδ0 : 0 < δ) (hlam0 : 0 < lam)
    (h : c * lam * v + Real.log (1 / δ) / lam < s) :
    1 / δ < Real.exp (lam * s - c * lam ^ 2 * v) := by
  have hdiv : Real.log (1 / δ) / lam < s - c * lam * v := by
    linarith
  have hlog : Real.log (1 / δ) < lam * s - c * lam ^ 2 * v := by
    have hmul := (div_lt_iff₀ hlam0).mp hdiv
    have hrhs : (s - c * lam * v) * lam = lam * s - c * lam ^ 2 * v := by ring
    rw [hrhs] at hmul
    exact hmul
  calc
    1 / δ = Real.exp (Real.log (1 / δ)) :=
      (Real.exp_log (one_div_pos.mpr hδ0)).symm
    _ < Real.exp (lam * s - c * lam ^ 2 * v) := Real.exp_lt_exp.mpr hlog

/-- A strict Markov bound for a nonnegative integrable real process.
The event itself need not be measurable: the conclusion uses the measure's
outer-measure value, and the ENNReal Markov lemma has the same convention. -/
theorem measure_strict_gt_inv_le
    (P : Measure Ω) (Z : Ω → ℝ) (δ : ℝ) (hδ0 : 0 < δ)
    (hZint : Integrable Z P) (hZnonneg : 0 ≤ᵐ[P] Z)
    (hZmean : (∫ ω, Z ω ∂P) ≤ 1) :
    P {ω | 1 / δ < Z ω} ≤ ENNReal.ofReal δ := by
  have hscaledInt : Integrable (fun ω => δ * Z ω) P := hZint.const_mul δ
  have hscaledNonneg : 0 ≤ᵐ[P] (fun ω => δ * Z ω) := by
    filter_upwards [hZnonneg] with ω hω
    exact mul_nonneg hδ0.le hω
  have hscaledMean : (∫ ω, δ * Z ω ∂P) ≤ δ := by
    rw [integral_const_mul]
    calc
      δ * (∫ ω, Z ω ∂P) ≤ δ * 1 := mul_le_mul_of_nonneg_left hZmean hδ0.le
      _ = δ := by ring
  have hlintegral : (∫⁻ ω, ENNReal.ofReal (δ * Z ω) ∂P) ≤ ENNReal.ofReal δ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hscaledInt hscaledNonneg]
    exact ENNReal.ofReal_le_ofReal hscaledMean
  calc
    P {ω | 1 / δ < Z ω} ≤ ∫⁻ ω, ENNReal.ofReal (δ * Z ω) ∂P := by
      refine meas_le_lintegral₀ hscaledInt.aemeasurable.ennreal_ofReal ?_
      intro ω hω
      have hscaled : (1 : ℝ) < δ * Z ω := by
        have hmul := (div_lt_iff₀ hδ0).mp hω
        simpa only [mul_comm] using hmul
      simpa using (ENNReal.ofReal_le_ofReal hscaled.le)
    _ ≤ ENNReal.ofReal δ := hlintegral

/-- Exponential-moment to strict-tail conversion. Integrability of the
exponential already provides the a.e. measurability needed for Markov, so no
measurability of either component process or regularity of `Ω` is added. -/
theorem exponential_moment_to_tail
    (P : Measure Ω) (S V : Ω → ℝ) (c δ lam : ℝ)
    (hδ0 : 0 < δ) (hlam0 : 0 < lam)
    (hZint : Integrable (fun ω => Real.exp (lam * S ω - c * lam ^ 2 * V ω)) P)
    (hZmean : (∫ ω, Real.exp (lam * S ω - c * lam ^ 2 * V ω) ∂P) ≤ 1) :
    P {ω | c * lam * V ω + Real.log (1 / δ) / lam < S ω} ≤ ENNReal.ofReal δ := by
  have hsub :
      {ω | c * lam * V ω + Real.log (1 / δ) / lam < S ω} ⊆
        {ω | 1 / δ < Real.exp (lam * S ω - c * lam ^ 2 * V ω)} := by
    intro ω hω
    exact strict_threshold_implies_exp_gt_inv hδ0 hlam0 hω
  refine le_trans (measure_mono hsub) ?_
  exact measure_strict_gt_inv_le P
    (fun ω => Real.exp (lam * S ω - c * lam ^ 2 * V ω)) δ hδ0 hZint
    (ae_of_all P (fun ω => (Real.exp_pos _).le)) hZmean

/-- The tail conversion with the exact finite sums and original conditional
expectation representatives in the public Freedman statement. The remaining
moment hypotheses are the exponential-process obligation, not a tail bound. -/
theorem freedman_tail_from_exponential_moment
    (P : Measure Ω) (Xs : ℕ → Ω → ℝ) (T : ℕ)
    (δ lam : ℝ) (hδ0 : 0 < δ) (hlam0 : 0 < lam)
    (hZint : Integrable
      (fun ω => Real.exp
        (lam * (∑ t ∈ Finset.Icc 1 T, Xs t ω) -
          (Real.exp 1 - 2) * lam ^ 2 *
            (∑ t ∈ Finset.Icc 1 T,
              condExp (⨆ i ∈ Finset.Icc 1 (t - 1),
                MeasurableSpace.comap (Xs i) inferInstance) P
                  (fun ω' => Xs t ω' ^ 2) ω))) P)
    (hZmean : (∫ ω, Real.exp
        (lam * (∑ t ∈ Finset.Icc 1 T, Xs t ω) -
          (Real.exp 1 - 2) * lam ^ 2 *
            (∑ t ∈ Finset.Icc 1 T,
              condExp (⨆ i ∈ Finset.Icc 1 (t - 1),
                MeasurableSpace.comap (Xs i) inferInstance) P
                  (fun ω' => Xs t ω' ^ 2) ω)) ∂P) ≤ 1) :
    P {ω | (Real.exp 1 - 2) * lam *
            (∑ t ∈ Finset.Icc 1 T,
              condExp (⨆ i ∈ Finset.Icc 1 (t - 1),
                MeasurableSpace.comap (Xs i) inferInstance) P
                  (fun ω' => Xs t ω' ^ 2) ω)
          + Real.log (1 / δ) / lam
        < ∑ t ∈ Finset.Icc 1 T, Xs t ω} ≤ ENNReal.ofReal δ := by
  exact exponential_moment_to_tail P
    (fun ω => ∑ t ∈ Finset.Icc 1 T, Xs t ω)
    (fun ω => ∑ t ∈ Finset.Icc 1 T,
      condExp (⨆ i ∈ Finset.Icc 1 (t - 1),
        MeasurableSpace.comap (Xs i) inferInstance) P
          (fun ω' => Xs t ω' ^ 2) ω)
    (Real.exp 1 - 2) δ lam hδ0 hlam0 hZint hZmean

end NativeFreedmanTail


set_option autoImplicit false

namespace TamingMonster.Regret.FreedmanAux

open MeasureTheory

/-- Markov conversion for the owner's non-strict threshold interface. -/
theorem measure_le_ofReal_of_integral_le_one {Ω : Type*} {m0 : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hZi : Integrable Z P) (hZ1 : ∫ ω, Z ω ∂P ≤ 1) {δ : ℝ} (hδ0 : 0 < δ)
    {A : Set Ω} (hA : A ⊆ {ω | 1 / δ ≤ Z ω}) :
    P A ≤ ENNReal.ofReal δ := by
  by_cases hδ1 : δ < 1
  · clear hδ1
    have hscaledInt : Integrable (fun ω => δ * Z ω) P := hZi.const_mul δ
    have hscaledNonneg : 0 ≤ᵐ[P] (fun ω => δ * Z ω) :=
      ae_of_all P (fun ω => mul_nonneg hδ0.le (hZ0 ω))
    have hscaledMean : (∫ ω, δ * Z ω ∂P) ≤ δ := by
      rw [integral_const_mul]
      calc
        δ * (∫ ω, Z ω ∂P) ≤ δ * 1 := mul_le_mul_of_nonneg_left hZ1 hδ0.le
        _ = δ := by ring
    have hlintegral : (∫⁻ ω, ENNReal.ofReal (δ * Z ω) ∂P) ≤ ENNReal.ofReal δ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hscaledInt hscaledNonneg]
      exact ENNReal.ofReal_le_ofReal hscaledMean
    calc
      P A ≤ ∫⁻ ω, ENNReal.ofReal (δ * Z ω) ∂P := by
        refine meas_le_lintegral₀ hscaledInt.aemeasurable.ennreal_ofReal ?_
        intro ω hω
        have hmul : (1 : ℝ) ≤ Z ω * δ := (div_le_iff₀ hδ0).mp (hA hω)
        have hscaled : (1 : ℝ) ≤ δ * Z ω := by
          simpa only [mul_comm] using hmul
        simpa using (ENNReal.ofReal_le_ofReal hscaled)
      _ ≤ ENNReal.ofReal δ := hlintegral
  · calc
      P A ≤ P Set.univ := measure_mono (Set.subset_univ A)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal δ := by
        simpa using (ENNReal.ofReal_le_ofReal (le_of_not_gt hδ1))

end TamingMonster.Regret.FreedmanAux

namespace TamingMonster.Regret.FreedmanAux

open MeasureTheory

set_option autoImplicit false

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The full past factor in the transition is strongly measurable for the
same conditioning space used by the next increment. -/
theorem stronglyMeasurable_nextWeight
    (P : Measure Ω) (F : ℕ → MeasurableSpace Ω) (hFmono : Monotone F)
    (Xs : ℕ → Ω → ℝ)
    (hXF : ∀ i t, 1 ≤ i → i < t → Measurable[F t] (Xs i))
    (lam : ℝ) (n : ℕ) :
    StronglyMeasurable[F (n + 1)]
      (fun ω => Real.exp
        (lam * (∑ t ∈ Finset.Icc 1 n, Xs t ω) -
          (Real.exp 1 - 2) * lam ^ 2 *
            ((∑ t ∈ Finset.Icc 1 n,
              condExp (F t) P (fun u => Xs t u ^ 2) ω) +
              condExp (F (n + 1)) P (fun u => Xs (n + 1) u ^ 2) ω))) := by
  have hS : Measurable[F (n + 1)]
      (fun ω => ∑ t ∈ Finset.Icc 1 n, Xs t ω) := by
    apply Finset.measurable_sum
    intro t ht
    have hmem := Finset.mem_Icc.mp ht
    exact hXF t (n + 1) hmem.1 (by omega)
  have hV : Measurable[F (n + 1)]
      (fun ω => ∑ t ∈ Finset.Icc 1 n,
        condExp (F t) P (fun u => Xs t u ^ 2) ω) := by
    apply Finset.measurable_sum
    intro t ht
    have htn : t ≤ n + 1 := by
      have hmem := Finset.mem_Icc.mp ht
      omega
    have hCE : StronglyMeasurable[F t]
        (condExp (F t) P (fun u => Xs t u ^ 2)) := stronglyMeasurable_condExp
    exact (hCE.mono (hFmono htn)).measurable
  have hA : Measurable[F (n + 1)]
      (condExp (F (n + 1)) P (fun u => Xs (n + 1) u ^ 2)) :=
    (stronglyMeasurable_condExp : StronglyMeasurable[F (n + 1)]
      (condExp (F (n + 1)) P (fun u => Xs (n + 1) u ^ 2))).measurable
  exact ((hS.const_mul lam).sub
    ((hV.add hA).const_mul ((Real.exp 1 - 2) * lam ^ 2))).exp.stronglyMeasurable

/-- The actual conditional transition for the exact Zproc, with the
one-step conditional MGF theorem exposed as the input from the scalar team. -/
theorem condExp_Zproc_succ_le_of_mgf
    {P : Measure Ω} [IsProbabilityMeasure P]
    (F : ℕ → MeasurableSpace Ω) (hFle : ∀ t, F t ≤ m0)
    (hFmono : Monotone F) (Xs : ℕ → Ω → ℝ)
    (hmeas : ∀ t, Measurable (Xs t))
    (hXF : ∀ i t, 1 ≤ i → i < t → Measurable[F t] (Xs i))
    (T : ℕ) {R lam : ℝ} (hR : 0 < R)
    (hle : ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, Xs t ω ≤ R)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R) (n : ℕ) (hn : n < T)
    (hmgf : condExp (F (n + 1)) P (fun ω => Real.exp (lam * Xs (n + 1) ω)) ≤ᵐ[P]
      fun ω => Real.exp ((Real.exp 1 - 2) * lam ^ 2 *
        condExp (F (n + 1)) P (fun u => Xs (n + 1) u ^ 2) ω)) :
    condExp (F (n + 1)) P (Zproc P F Xs lam (n + 1)) ≤ᵐ[P]
      Zproc P F Xs lam n := by
  have ht : n + 1 ∈ Finset.Icc 1 T :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hnext := integrable_Zproc F hFle Xs hmeas T hR hle hlam0 hlam1
    (show n + 1 ≤ T by omega)
  have hinc : Integrable (fun ω => Real.exp (lam * Xs (n + 1) ω)) P :=
    NativeFreedmanStep.integrable_exp_of_upper_bound P (hmeas (n + 1))
      hlam0.le (hle (n + 1) ht)
  have hstep := NativeFreedmanStep.condExp_sum_process_succ P (F (n + 1)) Xs
    (fun t => condExp (F t) P (fun u => Xs t u ^ 2)) (Real.exp 1 - 2) lam n
    (stronglyMeasurable_nextWeight P F hFmono Xs hXF lam n) hnext hinc hmgf
  -- Integrator fix (v1 diagnostic L1128): simp cannot unfold the unapplied
  -- `Zproc … (n + 1)`; the statement is definitionally the goal.
  exact hstep

/-- Finite-horizon compensated exponential induction. The conditional MGF
input is the exact separate one-step obligation, not a tail-bound premise. -/
theorem integral_Zproc_le_one_of_mgf
    {P : Measure Ω} [IsProbabilityMeasure P]
    (F : ℕ → MeasurableSpace Ω) (hFle : ∀ t, F t ≤ m0)
    (hFmono : Monotone F) (Xs : ℕ → Ω → ℝ) (T : ℕ) {R lam : ℝ} (hR : 0 < R)
    (hmeas : ∀ t, Measurable (Xs t))
    (hXF : ∀ i t, 1 ≤ i → i < t → Measurable[F t] (Xs i))
    (hle : ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, Xs t ω ≤ R)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R)
    (hmgf : ∀ t ∈ Finset.Icc 1 T,
      condExp (F t) P (fun ω => Real.exp (lam * Xs t ω)) ≤ᵐ[P]
        fun ω => Real.exp ((Real.exp 1 - 2) * lam ^ 2 *
          condExp (F t) P (fun u => Xs t u ^ 2) ω)) :
    Integrable (Zproc P F Xs lam T) P ∧ ∫ ω, Zproc P F Xs lam T ω ∂P ≤ 1 := by
  have hintZ : ∀ n, n ≤ T → Integrable (Zproc P F Xs lam n) P := by
    intro n hn
    exact integrable_Zproc F hFle Xs hmeas T hR hle hlam0 hlam1 hn
  have hzero : Zproc P F Xs lam 0 =ᵐ[P] fun _ : Ω => (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro ω
    simp [Zproc]
  have hstep : ∀ n, n < T →
      condExp (F (n + 1)) P (Zproc P F Xs lam (n + 1)) ≤ᵐ[P]
        Zproc P F Xs lam n := by
    intro n hn
    have ht : n + 1 ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact condExp_Zproc_succ_le_of_mgf F hFle hFmono Xs hmeas hXF T hR
      hle hlam0 hlam1 n hn (hmgf (n + 1) ht)
  refine ⟨hintZ T le_rfl, ?_⟩
  exact NativeFreedmanInduction.integral_process_le_one_finite P T
    (fun n => F (n + 1)) (Zproc P F Xs lam)
    (fun n _hn => hFle (n + 1)) hintZ hzero hstep T le_rfl

end TamingMonster.Regret.FreedmanAux

/-! ### Part: verification-planner Integration.lean (sha256 badf562cee2abfdca43d5ca04e40f1c37930337ec4873175d4623dbbab8efccd) -/
/-
Integrator fragment (verification-planner). It is pasted last in the single Mathlib-only
Candidate.lean, after:
  * analysis-prover Scalar.lean (FreedmanAux.exp_le_one_add_add_c_sq),
  * statement-auditor OneStep.lean
    (FreedmanNative.ConditionalMGF.conditional_mgf_step_from_scalar),
  * proof-reviewer FreedmanHelpers.lean (FreedmanAux.Zproc,
    FreedmanAux.integral_Zproc_le_one_of_mgf,
    FreedmanAux.measure_le_ofReal_of_integral_le_one).
It supplies the natural-past facts, the pointwise event inclusion and the frozen theorem.
Uncompiled.
-/

namespace TamingMonster.Regret.FreedmanAux

open MeasureTheory

theorem natPast_le {Ω : Type*} {m0 : MeasurableSpace Ω} {Xs : ℕ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (Xs t)) (t : ℕ) :
    (⨆ i ∈ Finset.Icc 1 (t - 1),
      MeasurableSpace.comap (Xs i) (inferInstance : MeasurableSpace ℝ)) ≤ m0 :=
  iSup_le fun i => iSup_le fun _hi => (hmeas i).comap_le

theorem natPast_mono {Ω : Type*} (Xs : ℕ → Ω → ℝ) :
    Monotone (fun t : ℕ => ⨆ i ∈ Finset.Icc 1 (t - 1),
      MeasurableSpace.comap (Xs i) (inferInstance : MeasurableSpace ℝ)) := by
  intro s t hst
  show (⨆ i ∈ Finset.Icc 1 (s - 1),
      MeasurableSpace.comap (Xs i) (inferInstance : MeasurableSpace ℝ)) ≤
    ⨆ i ∈ Finset.Icc 1 (t - 1),
      MeasurableSpace.comap (Xs i) (inferInstance : MeasurableSpace ℝ)
  refine iSup_le fun i => iSup_le fun hi => ?_
  have hi' := Finset.mem_Icc.mp hi
  have hit : i ∈ Finset.Icc 1 (t - 1) := by
    apply Finset.mem_Icc.mpr
    omega
  exact le_iSup_of_le i (le_iSup_of_le hit le_rfl)

theorem measurable_natPast {Ω : Type*} (Xs : ℕ → Ω → ℝ) {i t : ℕ}
    (hi : 1 ≤ i) (hit : i < t) :
    Measurable[⨆ j ∈ Finset.Icc 1 (t - 1),
      MeasurableSpace.comap (Xs j) (inferInstance : MeasurableSpace ℝ)] (Xs i) := by
  have hmem : i ∈ Finset.Icc 1 (t - 1) := by
    apply Finset.mem_Icc.mpr
    omega
  refine measurable_iff_comap_le.mpr ?_
  exact le_iSup_of_le i (le_iSup_of_le hmem le_rfl)

/-- The strict failure event of the target implies `1/δ ≤ exp(λ S − (e−2) λ² V)`,
pointwise, for the exact functions `S` and `V`. -/
theorem event_subset {Ω : Type*} (S V : Ω → ℝ) {lam δ : ℝ} (hlam0 : 0 < lam) (hδ0 : 0 < δ) :
    {ω | (Real.exp 1 - 2) * lam * V ω + Real.log (1 / δ) / lam < S ω} ⊆
      {ω | 1 / δ ≤ Real.exp (lam * S ω - (Real.exp 1 - 2) * lam ^ 2 * V ω)} := by
  intro ω hω
  -- Set-builder membership is definitional; avoid the deprecated `Set.mem_setOf_eq`.
  have hω' : (Real.exp 1 - 2) * lam * V ω + Real.log (1 / δ) / lam < S ω := hω
  show 1 / δ ≤ Real.exp (lam * S ω - (Real.exp 1 - 2) * lam ^ 2 * V ω)
  have h1 : lam * ((Real.exp 1 - 2) * lam * V ω + Real.log (1 / δ) / lam) < lam * S ω :=
    mul_lt_mul_of_pos_left hω' hlam0
  -- v1 diagnostics (candidates/round-57d17b84): `field_simp` closes this goal by itself.
  have h2 : lam * ((Real.exp 1 - 2) * lam * V ω + Real.log (1 / δ) / lam) =
      (Real.exp 1 - 2) * lam ^ 2 * V ω + Real.log (1 / δ) := by
    field_simp [ne_of_gt hlam0]
  have hkey : Real.log (1 / δ) < lam * S ω - (Real.exp 1 - 2) * lam ^ 2 * V ω := by
    linarith
  have hpos : 0 < 1 / δ := by positivity
  calc
    1 / δ = Real.exp (Real.log (1 / δ)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (lam * S ω - (Real.exp 1 - 2) * lam ^ 2 * V ω) :=
        Real.exp_le_exp.mpr (le_of_lt hkey)

end TamingMonster.Regret.FreedmanAux

namespace TamingMonster.Regret

open MeasureTheory

/-- Lemma 9 (Freedman's inequality, as quoted from Beygelzimer et al. 2011), p. 14.
`Xs 1, …, Xs T` are real random variables with `X_t ≤ R` and `E[X_t | X_1, …, X_{t−1}] = 0`;
`S = ∑_{t=1}^T X_t` and `V = ∑_{t=1}^T E[X_t² | X_1, …, X_{t−1}]`. For `δ ∈ (0,1)` and
`λ ∈ (0, 1/R]`, the event `S > (e − 2)λV + ln(1/δ)/λ` has probability at most `δ`.
The conditioning σ-algebra for round `t` is `σ(X_1, …, X_{t−1})` (trivial for `t = 1`). -/
theorem freedman_inequality {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Xs : ℕ → Ω → ℝ) (T : ℕ) (R : ℝ) (hR : 0 < R)
    (hmeas : ∀ t, Measurable (Xs t))
    (hint : ∀ t, Integrable (Xs t) P)
    (hint2 : ∀ t, Integrable (fun ω => Xs t ω ^ 2) P)
    (hle : ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, Xs t ω ≤ R)
    (hmart : ∀ t ∈ Finset.Icc 1 T,
      condExp (⨆ i ∈ Finset.Icc 1 (t - 1), MeasurableSpace.comap (Xs i) inferInstance) P (Xs t)
        =ᵐ[P] 0)
    (δ lam : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R) :
    P {ω | (Real.exp 1 - 2) * lam *
            (∑ t ∈ Finset.Icc 1 T,
              condExp (⨆ i ∈ Finset.Icc 1 (t - 1), MeasurableSpace.comap (Xs i) inferInstance) P
                (fun ω' => Xs t ω' ^ 2) ω)
          + Real.log (1 / δ) / lam
        < ∑ t ∈ Finset.Icc 1 T, Xs t ω} ≤ ENNReal.ofReal δ := by
  -- `hδ1` is part of the frozen statement; the tail bound holds for every `δ > 0`.
  -- Referenced once by a named `have` (the pattern root's leased check accepted).
  have hδ1_frozen : δ < 1 := hδ1
  have hFle : ∀ t, (⨆ i ∈ Finset.Icc 1 (t - 1),
      MeasurableSpace.comap (Xs i) (inferInstance : MeasurableSpace ℝ)) ≤
        (inferInstance : MeasurableSpace Ω) :=
    fun t => FreedmanAux.natPast_le hmeas t
  have hZ := FreedmanAux.integral_Zproc_le_one_of_mgf (P := P)
    (fun t => ⨆ i ∈ Finset.Icc 1 (t - 1),
      MeasurableSpace.comap (Xs i) (inferInstance : MeasurableSpace ℝ))
    hFle (FreedmanAux.natPast_mono Xs) Xs T hR hmeas
    (fun i t hi hit => FreedmanAux.measurable_natPast Xs hi hit)
    hle hlam0 hlam1
    (fun t ht =>
      (FreedmanNative.ConditionalMGF.conditional_mgf_step_from_scalar (c := Real.exp 1 - 2)
        (hFle t) (hmeas t) (hint t) (hint2 t) hR hlam0 hlam1 (hle t ht) (hmart t ht)
        (fun y hy => FreedmanAux.exp_le_one_add_add_c_sq hy)).2)
  have hsub := FreedmanAux.event_subset
    (fun ω => ∑ t ∈ Finset.Icc 1 T, Xs t ω)
    (fun ω => ∑ t ∈ Finset.Icc 1 T,
      condExp (⨆ i ∈ Finset.Icc 1 (t - 1),
        MeasurableSpace.comap (Xs i) (inferInstance : MeasurableSpace ℝ)) P
        (fun ω' => Xs t ω' ^ 2) ω)
    hlam0 hδ0
  exact FreedmanAux.measure_le_ofReal_of_integral_le_one
    (Z := FreedmanAux.Zproc P
      (fun t => ⨆ i ∈ Finset.Icc 1 (t - 1),
        MeasurableSpace.comap (Xs i) (inferInstance : MeasurableSpace ℝ)) Xs lam T)
    (fun ω => le_of_lt (Real.exp_pos _)) hZ.1 hZ.2 hδ0 hsub

end TamingMonster.Regret

end Prove2SwarmSubmission

open MeasureTheory
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Xs : ℕ → Ω → ℝ) (T : ℕ) (R : ℝ) (hR : 0 < R)
    (hmeas : ∀ t, Measurable (Xs t))
    (hint : ∀ t, Integrable (Xs t) P)
    (hint2 : ∀ t, Integrable (fun ω => Xs t ω ^ 2) P)
    (hle : ∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, Xs t ω ≤ R)
    (hmart : ∀ t ∈ Finset.Icc 1 T,
      condExp (⨆ i ∈ Finset.Icc 1 (t - 1), MeasurableSpace.comap (Xs i) inferInstance) P (Xs t)
        =ᵐ[P] 0)
    (δ lam : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / R) :
    P {ω | (Real.exp 1 - 2) * lam *
            (∑ t ∈ Finset.Icc 1 T,
              condExp (⨆ i ∈ Finset.Icc 1 (t - 1), MeasurableSpace.comap (Xs i) inferInstance) P
                (fun ω' => Xs t ω' ^ 2) ω)
          + Real.log (1 / δ) / lam
        < ∑ t ∈ Finset.Icc 1 T, Xs t ω} ≤ ENNReal.ofReal δ := by
  exact Prove2SwarmSubmission.TamingMonster.Regret.freedman_inequality P Xs T R hR hmeas hint hint2 hle hmart δ lam hδ0 hδ1 hlam0 hlam1

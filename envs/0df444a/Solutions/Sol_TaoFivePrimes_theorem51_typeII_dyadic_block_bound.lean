-- Prove2me | solution 1 for TaoFivePrimes.theorem51_typeII_dyadic_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T17:27:53.162161+00:00
-- url     : https://prove2.me/submissions/37413c71-fbe8-4826-8cff-28228092ec39

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_Theorem51Sums

/-! Standalone exact Type II dyadic envelope for 84c50127-41c8-42e6-9e1f-16e17e78ab14.
Prepared for belinda from completed workspace proofs, without submission.
Only needed completed declaration segments are extracted. Source proof bodies and
existing docstrings are preserved; historical open-status docstrings are historical.
Only the target declaration name changes to top-level solution.
Attribution: included cutoff helper extractions retain marwahaha's accepted-source
provenance from d9c709bd-19ab-4de8-844d-a0efdc9357ed (mass/support),
a9da7ce5-4cc0-4425-b5d1-049e35646bf6 (Fourier L1/L2), and
5307a6ba-1089-4226-a7a7-21b2993ed92e (formula/decay), when present in the manifest.
These earlier accepted implementations are not new workspace contributions.
No target-placeholder, local helper, circular sketch, or Formalization import.
-/
set_option autoImplicit false

section Package_CutoffBridgeMassReuse
open MeasureTheory intervalIntegral
namespace TaoFivePrimes.CutoffBridgeMassReuse

-- BEGIN EXTRACT TaoFivePrimes.CutoffBridgeMassReuse.log_half
lemma log_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
-- END EXTRACT TaoFivePrimes.CutoffBridgeMassReuse.log_half

-- BEGIN EXTRACT TaoFivePrimes.CutoffBridgeMassReuse.eta0_eq_zero_of_le
lemma eta0_eq_zero_of_le {t : ℝ} (ht : t ≤ 1 / 4) : eta0 t = 0 := by
  unfold eta0
  split_ifs with hpos
  · have hlog : Real.log (2 * t) ≤ Real.log (1 / 2 : ℝ) := by
      exact Real.log_le_log (by positivity) (by linarith)
    rw [log_half] at hlog
    have hneg : Real.log 2 ≤ -Real.log (2 * t) := by linarith
    have hcut : Real.log 2 - |Real.log (2 * t)| ≤ 0 :=
      sub_nonpos.mpr (hneg.trans (neg_le_abs (Real.log (2 * t))))
    rw [max_eq_left hcut, mul_zero]
  · rfl
-- END EXTRACT TaoFivePrimes.CutoffBridgeMassReuse.eta0_eq_zero_of_le

-- BEGIN EXTRACT TaoFivePrimes.CutoffBridgeMassReuse.eta0_eq_zero_of_ge
lemma eta0_eq_zero_of_ge {t : ℝ} (ht : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  rw [if_pos (by linarith)]
  have hlog : Real.log 2 ≤ Real.log (2 * t) := by
    exact Real.log_le_log (by norm_num) (by linarith)
  have hcut : Real.log 2 - |Real.log (2 * t)| ≤ 0 :=
    sub_nonpos.mpr (hlog.trans (le_abs_self (Real.log (2 * t))))
  rw [max_eq_left hcut, mul_zero]
-- END EXTRACT TaoFivePrimes.CutoffBridgeMassReuse.eta0_eq_zero_of_ge
end TaoFivePrimes.CutoffBridgeMassReuse
end Package_CutoffBridgeMassReuse

section Package_SmallQCancellationAux
set_option autoImplicit false
open scoped BigOperators ArithmeticFunction.vonMangoldt
open TaoFivePrimes
namespace SmallQCancellationAux

-- BEGIN EXTRACT SmallQCancellationAux.kernel
/-- Actual odd-supported phase and cutoff, without the von Mangoldt coefficient. -/
noncomputable def kernel (x alpha : ℝ) (n : ℕ) : ℂ :=
  if Nat.Coprime n 2 then expCircle (alpha*n) * (eta0 ((n : ℝ)/x) : ℂ) else 0
-- END EXTRACT SmallQCancellationAux.kernel

-- BEGIN EXTRACT SmallQCancellationAux.centered
/-- Centered divisor coefficient g(w), with the strict b>V threshold. -/
noncomputable def centered (V : ℝ) (w : ℕ) : ℝ :=
  (∑ b ∈ w.divisors, if V < (b : ℝ) then (Λ b : ℝ) else 0) - Real.log w / 2
-- END EXTRACT SmallQCancellationAux.centered

-- BEGIN EXTRACT SmallQCancellationAux.kernel_support
/-- It vanishes outside the actual strict cutoff interval, including both endpoints. -/
theorem kernel_support (x alpha : ℝ) (hx : 0 < x) (n : ℕ)
    (hn : (n : ℝ) ≤ x/4 ∨ x ≤ (n : ℝ)) : kernel x alpha n = 0 := by
  have hz : eta0 ((n : ℝ)/x) = 0 := by
    rcases hn with hn | hn
    · apply CutoffBridgeMassReuse.eta0_eq_zero_of_le
      apply (div_le_iff₀ hx).2
      linarith
    · exact CutoffBridgeMassReuse.eta0_eq_zero_of_ge ((le_div_iff₀ hx).2 (by simpa))
  simp [kernel, hz]
-- END EXTRACT SmallQCancellationAux.kernel_support

-- BEGIN EXTRACT SmallQCancellationAux.centered_bound
/-- The divisor coefficient satisfies the genuine half-logarithm bound, even at w=0. -/
theorem centered_bound (V : ℝ) (w : ℕ) : |centered V w| ≤ Real.log w / 2 := by
  have hs : (∑ b ∈ w.divisors, (Λ b : ℝ)) = Real.log w := by
    exact ArithmeticFunction.vonMangoldt_sum
  have hlo : 0 ≤ ∑ b ∈ w.divisors, if V < (b : ℝ) then (Λ b : ℝ) else 0 := by
    apply Finset.sum_nonneg
    intro b hb
    split_ifs <;> positivity
  have hhi : (∑ b ∈ w.divisors, if V < (b : ℝ) then (Λ b : ℝ) else 0) ≤
      Real.log w := by
    rw [← hs]
    apply Finset.sum_le_sum
    intro b hb
    split_ifs
    · rfl
    · exact ArithmeticFunction.vonMangoldt_nonneg
  rw [centered, abs_le]
  constructor <;> linarith
-- END EXTRACT SmallQCancellationAux.centered_bound
end SmallQCancellationAux
end Package_SmallQCancellationAux

section Package_SmallQIdentityAux
set_option autoImplicit false
open scoped BigOperators ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
open TaoFivePrimes SmallQCancellationAux
namespace SmallQIdentityAux

-- BEGIN EXTRACT SmallQIdentityAux.kernel_above_floor
/-- The actual cutoff has the support needed by rectangular reindexing. -/
theorem kernel_above_floor (x alpha : ℝ) (hx : 0 < x) (n : ℕ)
    (hn : ⌊x⌋₊ < n) : kernel x alpha n = 0 := by
  apply kernel_support x alpha hx n (Or.inr _)
  have hh := Nat.lt_floor_add_one x
  have hn' : (⌊x⌋₊ : ℝ)+1 ≤ n := by exact_mod_cast hn
  linarith
-- END EXTRACT SmallQIdentityAux.kernel_above_floor
end SmallQIdentityAux
end Package_SmallQIdentityAux

section Package_Theorem51Interface
set_option autoImplicit false
open TaoFivePrimes SmallQCancellationAux
open scoped BigOperators
namespace Theorem51Interface

-- BEGIN EXTRACT Theorem51Interface.centered_eq
/-- The new filtered divisor coefficient is exactly the existing strict centered coefficient. -/
theorem centered_eq (V : ℝ) (w : ℕ) : theorem51Centered V w = centered V w := by
  classical
  simp [theorem51Centered, centered, Finset.sum_filter]
-- END EXTRACT Theorem51Interface.centered_eq

-- BEGIN EXTRACT Theorem51Interface.termII
/-- One literal Type II summand with all four original strict and odd masks. -/
noncomputable def termII (x alpha U V : ℝ) (d w : ℕ) : ℂ :=
  if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
    (ArithmeticFunction.moebius d : ℂ) * (theorem51Centered V w : ℂ) *
      expCircle (alpha*d*w) * (eta0 ((d : ℝ)*w/x) : ℂ)
  else 0
-- END EXTRACT Theorem51Interface.termII

-- BEGIN EXTRACT Theorem51Interface.termII_kernel
/-- Pointwise identification with the saved odd-supported kernel, with strict masks intact. -/
theorem termII_kernel (x alpha U V : ℝ) (d w : ℕ) :
    termII x alpha U V d w =
      if U < (d : ℝ) ∧ V < (w : ℝ) then
        (ArithmeticFunction.moebius d : ℂ) * (centered V w : ℂ) * kernel x alpha (d*w)
      else 0 := by
  classical
  by_cases hu : U < (d : ℝ) <;> by_cases hv : V < (w : ℝ) <;>
    by_cases hd : d.Coprime 2 <;> by_cases hw : w.Coprime 2 <;>
    simp only [termII, centered_eq, kernel, Nat.coprime_mul_iff_left, Nat.cast_mul,
      hu, hv, hd, hw, mul_assoc, and_self, and_false, false_and, and_true, true_and,
      if_true, if_false, mul_zero]
  simp only [if_pos (show d.Coprime 2 ∧ w.Coprime 2 from ⟨hd, hw⟩)]
-- END EXTRACT Theorem51Interface.termII_kernel

-- BEGIN EXTRACT Theorem51Interface.termII_zero
/-- Zero indices have zero actual Type II term, even without positive U,V. -/
theorem termII_zero (x alpha U V : ℝ) (d w : ℕ) :
    termII x alpha U V 0 w = 0 ∧ termII x alpha U V d 0 = 0 := by
  simp [termII]
-- END EXTRACT Theorem51Interface.termII_zero

-- BEGIN EXTRACT Theorem51Interface.termII_outside
/-- The original Type II summand vanishes outside the finite square. -/
theorem termII_outside (x alpha U V : ℝ) (hx : 0 < x) (d w : ℕ)
    (h : ⌊x⌋₊ < d ∨ ⌊x⌋₊ < w) : termII x alpha U V d w = 0 := by
  by_cases hd : d = 0
  · subst d; exact (termII_zero x alpha U V 0 w).1
  by_cases hw : w = 0
  · subst w; exact (termII_zero x alpha U V d 0).2
  have hp : ⌊x⌋₊ < d*w := by
    rcases h with h | h
    · exact h.trans_le (Nat.le_mul_of_pos_right d (Nat.pos_of_ne_zero hw))
    · exact h.trans_le (Nat.le_mul_of_pos_left w (Nat.pos_of_ne_zero hd))
  rw [termII_kernel]
  simp [SmallQIdentityAux.kernel_above_floor x alpha hx (d*w) hp]
-- END EXTRACT Theorem51Interface.termII_outside

-- BEGIN EXTRACT Theorem51Interface.innerII_finite
/-- Exact finite inner Type II row. -/
theorem innerII_finite (x alpha U V : ℝ) (hx : 0 < x) (d : ℕ) :
    (∑' w : ℕ, termII x alpha U V d w) =
      ∑ w ∈ Finset.range (⌊x⌋₊+1), termII x alpha U V d w := by
  apply tsum_eq_sum
  intro w hw
  exact termII_outside x alpha U V hx d w (Or.inr (by simpa using hw))
-- END EXTRACT Theorem51Interface.innerII_finite

-- BEGIN EXTRACT Theorem51Interface.typeII_finite
/-- Literal Type II is the finite square, preserving both strict thresholds and odd masks. -/
theorem typeII_finite (x alpha U V : ℝ) (hx : 0 < x) :
    theorem51TypeII x alpha U V =
      ‖∑ d ∈ Finset.range (⌊x⌋₊+1), ∑ w ∈ Finset.range (⌊x⌋₊+1),
        termII x alpha U V d w‖ := by
  change ‖∑' d : ℕ, ∑' w : ℕ, termII x alpha U V d w‖ = _
  congr 1
  rw [tsum_eq_sum (s := Finset.range (⌊x⌋₊+1))]
  · exact Finset.sum_congr rfl (fun d _ ↦ innerII_finite x alpha U V hx d)
  · intro d hd
    have hz (w : ℕ) := termII_outside x alpha U V hx d w (Or.inl (by simpa using hd))
    simp only [hz, tsum_zero]
-- END EXTRACT Theorem51Interface.typeII_finite

-- BEGIN EXTRACT Theorem51Interface.typeII_kernel_finite
/-- Same finite Type II square in the already verified kernel interface. -/
theorem typeII_kernel_finite (x alpha U V : ℝ) (hx : 0 < x) :
    theorem51TypeII x alpha U V =
      ‖∑ d ∈ Finset.range (⌊x⌋₊+1), ∑ w ∈ Finset.range (⌊x⌋₊+1),
        if U < (d : ℝ) ∧ V < (w : ℝ) then
          (ArithmeticFunction.moebius d : ℂ)*(centered V w : ℂ)*kernel x alpha (d*w)
        else 0‖ := by
  rw [typeII_finite x alpha U V hx]
  simp_rw [termII_kernel]
-- END EXTRACT Theorem51Interface.typeII_kernel_finite
end Theorem51Interface
end Package_Theorem51Interface

section Package_SmallQTypeIIAux
set_option autoImplicit false
open scoped BigOperators
open TaoFivePrimes SmallQCancellationAux MeasureTheory
namespace SmallQTypeIIAux

-- BEGIN EXTRACT SmallQTypeIIAux.dSet
/-- Odd d in the localized closed interval, above the strict Vaughan cutoff. -/
noncomputable def dSet (x W : ℝ) (q : ℕ) : Finset ℕ :=
  (Finset.range (⌊x⌋₊+1)).filter fun d ↦
    x/(q : ℝ)^2 < (d : ℝ) ∧ Nat.Coprime d 2 ∧ x/(2*W) ≤ d ∧ (d : ℝ) ≤ x/W
-- END EXTRACT SmallQTypeIIAux.dSet

-- BEGIN EXTRACT SmallQTypeIIAux.wSet
/-- Odd w in the localized closed interval, above the strict Vaughan cutoff. -/
noncomputable def wSet (x W : ℝ) (q : ℕ) : Finset ℕ :=
  (Finset.range (⌊x⌋₊+1)).filter fun w ↦
    q < w ∧ Nat.Coprime w 2 ∧ W/2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
-- END EXTRACT SmallQTypeIIAux.wSet

-- BEGIN EXTRACT SmallQTypeIIAux.row
/-- Actual centered Fourier row, with its signed Mobius coefficient. -/
noncomputable def row (x alpha W : ℝ) (q d : ℕ) : ℂ :=
  (ArithmeticFunction.moebius d : ℂ) *
    ∑ w ∈ wSet x W q, (centered q w : ℂ) * expCircle (alpha*(d*w))
-- END EXTRACT SmallQTypeIIAux.row

-- BEGIN EXTRACT SmallQTypeIIAux.box
/-- Localized complex rectangle, before taking absolute values. -/
noncomputable def box (x alpha W : ℝ) (q : ℕ) : ℂ :=
  ∑ d ∈ dSet x W q, row x alpha W q d
-- END EXTRACT SmallQTypeIIAux.box
end SmallQTypeIIAux
end Package_SmallQTypeIIAux

section Package_SmallQSmoothingAux
set_option autoImplicit false
open scoped BigOperators
open TaoFivePrimes SmallQCancellationAux SmallQTypeIIAux MeasureTheory
attribute [local instance] Classical.propDecidable
namespace SmallQSmoothingAux

-- BEGIN EXTRACT SmallQSmoothingAux.window
/-- The four closed multiplicative localization inequalities, without parity or cutoffs. -/
def window (x W : ℝ) (d w : ℕ) : Prop :=
  x/(2*W) ≤ d ∧ (d : ℝ) ≤ x/W ∧ W/2 ≤ w ∧ (w : ℝ) ≤ W
-- END EXTRACT SmallQSmoothingAux.window

-- BEGIN EXTRACT SmallQSmoothingAux.cell
/-- A single reciprocal localization cell, with its original complex coefficient. -/
noncomputable def cell (x alpha W : ℝ) (q d w : ℕ) : ℂ :=
  if x/(q : ℝ)^2 < d ∧ q < w ∧ Nat.Coprime d 2 ∧ Nat.Coprime w 2 then
    if window x W d w then
      (ArithmeticFunction.moebius d : ℂ) * (centered q w : ℂ) *
        expCircle (alpha*(d*w)) / (W : ℂ)
    else 0
  else 0
-- END EXTRACT SmallQSmoothingAux.cell

-- BEGIN EXTRACT SmallQSmoothingAux.window_measurable
/-- The localization set is measurable, including at W=0 (division is total). -/
theorem window_measurable (x : ℝ) (d w : ℕ) :
    MeasurableSet {W : ℝ | window x W d w} := by
  unfold window
  exact ((measurableSet_le (measurable_const.div
    (measurable_const.mul measurable_id)) measurable_const).inter
    ((measurableSet_le measurable_const (measurable_const.div measurable_id)).inter
      ((measurableSet_le (measurable_id.div_const 2) measurable_const).inter
        (measurableSet_le measurable_const measurable_id))))
-- END EXTRACT SmallQSmoothingAux.window_measurable

-- BEGIN EXTRACT SmallQSmoothingAux.ite_integrable
/-- Measurable restriction preserves both sides of interval integrability. -/
theorem ite_integrable {f : ℝ → ℂ} {a b : ℝ} (hi : IntervalIntegrable f volume a b)
    (s : Set ℝ) (hs : MeasurableSet s) :
    IntervalIntegrable (fun W ↦ if W ∈ s then f W else 0) volume a b := by
  classical
  exact ⟨hi.1.indicator hs, hi.2.indicator hs⟩
-- END EXTRACT SmallQSmoothingAux.ite_integrable

-- BEGIN EXTRACT SmallQSmoothingAux.cell_integrable
/-- Each actual cell is integrable on every compact positive interval. -/
theorem cell_integrable (x alpha : ℝ) (q d w : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun W ↦ cell x alpha W q d w) volume a b := by
  classical
  have hi : IntervalIntegrable (fun W : ℝ ↦
      (ArithmeticFunction.moebius d : ℂ) * (centered q w : ℂ) *
        expCircle (alpha*(d*w)) / (W : ℂ)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply continuousOn_const.div (Complex.continuous_ofReal.continuousOn)
    intro W hW
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le ha hW.1))
  unfold cell
  split_ifs with h
  · exact ite_integrable hi _ (window_measurable x d w)
  · exact intervalIntegrable_const
-- END EXTRACT SmallQSmoothingAux.cell_integrable

-- BEGIN EXTRACT SmallQSmoothingAux.box_div_eq_cells
/-- Expand both filtered finite sums without dropping closed endpoints. -/
theorem box_div_eq_cells (x alpha W : ℝ) (q : ℕ) :
    box x alpha W q / (W : ℂ) =
      ∑ d ∈ Finset.range (⌊x⌋₊+1), ∑ w ∈ Finset.range (⌊x⌋₊+1),
        cell x alpha W q d w := by
  classical
  simp only [box, row, dSet, wSet, Finset.sum_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hD : x/(q : ℝ)^2 < d ∧ Nat.Coprime d 2 ∧ x/(2*W) ≤ d ∧ (d : ℝ) ≤ x/W
  · rw [if_pos hD]
    simp only [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hW : q < w ∧ Nat.Coprime w 2 ∧ W/2 ≤ w ∧ (w : ℝ) ≤ W
    · rw [if_pos hW]
      unfold cell
      rw [if_pos ⟨hD.1, hW.1, hD.2.1, hW.2.1⟩,
        if_pos ⟨hD.2.2.1, hD.2.2.2, hW.2.2.1, hW.2.2.2⟩]
      ring
    · rw [if_neg hW, mul_zero, zero_div]
      unfold cell
      split_ifs with hc hwin
      · exact False.elim (hW ⟨hc.2.1, hc.2.2.2, hwin.2.2.1, hwin.2.2.2⟩)
      · rfl
      · rfl
  · rw [if_neg hD, zero_div]
    symm
    apply Finset.sum_eq_zero
    intro w hw
    unfold cell window
    split_ifs with hc hwin
    · exact False.elim (hD ⟨hc.1, hc.2.2.1, hwin.1, hwin.2.1⟩)
    · rfl
    · rfl
-- END EXTRACT SmallQSmoothingAux.box_div_eq_cells

-- BEGIN EXTRACT SmallQSmoothingAux.box_integrable
/-- Actual box/W, not a surrogate envelope, is integrable on every positive interval. -/
theorem box_integrable (x alpha : ℝ) (q : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun W ↦ box x alpha W q / (W : ℂ)) volume a b := by
  simp_rw [box_div_eq_cells]
  simpa only [Finset.sum_fn] using
    IntervalIntegrable.sum (Finset.range (⌊x⌋₊+1)) (fun d _ ↦
      IntervalIntegrable.sum (Finset.range (⌊x⌋₊+1))
        (fun w _ ↦ cell_integrable x alpha q d w a b ha hab))
-- END EXTRACT SmallQSmoothingAux.box_integrable

-- BEGIN EXTRACT SmallQSmoothingAux.integral_box_eq_sum
/-- Finite sum/integral interchange for genuinely integrable complex cells. -/
theorem integral_box_eq_sum (x alpha : ℝ) (q : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ W : ℝ in a..b, box x alpha W q / (W : ℂ)) =
      ∑ d ∈ Finset.range (⌊x⌋₊+1), ∑ w ∈ Finset.range (⌊x⌋₊+1),
        ∫ W : ℝ in a..b, cell x alpha W q d w := by
  simp_rw [box_div_eq_cells]
  have hi (d : ℕ) : IntervalIntegrable
      (fun W ↦ ∑ w ∈ Finset.range (⌊x⌋₊+1), cell x alpha W q d w) volume a b := by
    simpa only [Finset.sum_fn] using
      IntervalIntegrable.sum (Finset.range (⌊x⌋₊+1))
        (fun w _ ↦ cell_integrable x alpha q d w a b ha hab)
  rw [intervalIntegral.integral_finsetSum (fun d _ ↦ hi d)]
  apply Finset.sum_congr rfl
  intro d hd
  exact intervalIntegral.integral_finsetSum
    (fun w _ ↦ cell_integrable x alpha q d w a b ha hab)
-- END EXTRACT SmallQSmoothingAux.integral_box_eq_sum

-- BEGIN EXTRACT SmallQSmoothingAux.window_iff_overlap
/-- For positive d and W, the localization is exactly the overlap of two closed
multiplicative intervals. This includes the two cutoff corners and empty intersections. -/
theorem window_iff_overlap (x W : ℝ) (d w : ℕ) (hd : 0 < d) (hW : 0 < W) :
    window x W d w ↔
      W ∈ Set.Icc (max (w : ℝ) (x/(2*d))) (min (2*w : ℝ) (x/d)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [window, Set.mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨h1,h2,h3,h4⟩
    refine ⟨⟨h4, ?_⟩, ⟨?_, ?_⟩⟩
    · apply (div_le_iff₀ (by positivity : 0 < 2*(d : ℝ))).2
      have := (div_le_iff₀ (by positivity : 0 < 2*W)).1 h1
      nlinarith
    · linarith
    · apply (le_div_iff₀ hdR).2
      have := (le_div_iff₀ hW).1 h2
      nlinarith
  · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    refine ⟨?_, ?_, ?_, h1⟩
    · apply (div_le_iff₀ (by positivity : 0 < 2*W)).2
      have := (div_le_iff₀ (by positivity : 0 < 2*(d : ℝ))).1 h2
      nlinarith
    · apply (le_div_iff₀ hW).2
      have := (le_div_iff₀ hdR).1 h4
      nlinarith
    · linarith
-- END EXTRACT SmallQSmoothingAux.window_iff_overlap

-- BEGIN EXTRACT SmallQSmoothingAux.cell_recovery
/-- One natural-index cell recovers its exact kernel term from a supplied scalar
cutoff integral identity. Zero and even indices are handled without assuming positivity. -/
theorem cell_recovery (x alpha : ℝ) (q d w : ℕ) (hx : 0 < x) (hq : 1 ≤ q)
    (hcut : ∀ d w : ℕ, 0 < d → 0 < w → x/(q : ℝ)^2 < d → q < w →
      eta0 ((d*w : ℕ) / x) =
        4 * ∫ W : ℝ in (q : ℝ)..((q : ℝ)^2),
          if window x W d w then 1/W else 0) :
    (if x/(q : ℝ)^2 < d ∧ q < w then
      (ArithmeticFunction.moebius d : ℂ) * (centered q w : ℂ) * kernel x alpha (d*w)
    else 0) = (4 : ℂ) * ∫ W : ℝ in (q : ℝ)..((q : ℝ)^2), cell x alpha W q d w := by
  classical
  by_cases ht : x/(q : ℝ)^2 < d ∧ q < w
  · rw [if_pos ht]
    by_cases ho : Nat.Coprime d 2 ∧ Nat.Coprime w 2
    · have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hd : 0 < d := by
        exact_mod_cast (lt_trans (div_pos hx (sq_pos_of_pos hqr)) ht.1)
      have hw : 0 < w := by omega
      have he := hcut d w hd hw ht.1 ht.2
      have hc : (fun W : ℝ ↦ cell x alpha W q d w) =
          fun W ↦ ((ArithmeticFunction.moebius d : ℂ) * (centered q w : ℂ) *
            expCircle (alpha*(d*w))) *
              ((if window x W d w then 1/W else 0 : ℝ) : ℂ) := by
        funext W
        unfold cell
        rw [if_pos ⟨ht.1, ht.2, ho.1, ho.2⟩]
        split_ifs <;> push_cast <;> ring
      rw [hc, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
      rw [kernel, if_pos (Nat.coprime_mul_iff_left.mpr ho), he]
      push_cast
      ring
    · have hz : ¬ Nat.Coprime (d*w) 2 := by simpa only [Nat.coprime_mul_iff_left] using ho
      have hc : ∀ W : ℝ, cell x alpha W q d w = 0 := by
        intro W
        unfold cell
        rw [if_neg (fun h ↦ ho ⟨h.2.2.1, h.2.2.2⟩)]
      simp only [kernel, hz, if_false, mul_zero, hc, intervalIntegral.integral_zero]
  · have hc : ∀ W : ℝ, cell x alpha W q d w = 0 := by
      intro W
      unfold cell
      rw [if_neg (fun h ↦ ht ⟨h.1, h.2.1⟩)]
    simp only [ht, if_false, hc, intervalIntegral.integral_zero, mul_zero]
-- END EXTRACT SmallQSmoothingAux.cell_recovery
end SmallQSmoothingAux
end Package_SmallQSmoothingAux

section Package_CutoffBridgeDecayReuse
open MeasureTheory intervalIntegral
namespace TaoFivePrimes.CutoffBridgeDecayReuse

-- BEGIN EXTRACT TaoFivePrimes.CutoffBridgeDecayReuse.log_half_fd
/-- `log (1/2) = -log 2`, used to normalize the cutoff endpoints. -/
lemma log_half_fd : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
-- END EXTRACT TaoFivePrimes.CutoffBridgeDecayReuse.log_half_fd

-- BEGIN EXTRACT TaoFivePrimes.CutoffBridgeDecayReuse.eta0_eq_zero_of_le_fd
lemma eta0_eq_zero_of_le_fd {t : ℝ} (ht : t ≤ 1 / 4) : eta0 t = 0 := by
  unfold eta0
  split_ifs with hpos
  · have hlog : Real.log (2 * t) ≤ Real.log (1 / 2 : ℝ) := by
      exact Real.log_le_log (by positivity) (by linarith)
    rw [log_half_fd] at hlog
    have hneg : Real.log 2 ≤ -Real.log (2 * t) := by linarith
    have hcut : Real.log 2 - |Real.log (2 * t)| ≤ 0 :=
      sub_nonpos.mpr (hneg.trans (neg_le_abs (Real.log (2 * t))))
    rw [max_eq_left hcut, mul_zero]
  · rfl
-- END EXTRACT TaoFivePrimes.CutoffBridgeDecayReuse.eta0_eq_zero_of_le_fd

-- BEGIN EXTRACT TaoFivePrimes.CutoffBridgeDecayReuse.eta0_eq_zero_of_ge_fd
lemma eta0_eq_zero_of_ge_fd {t : ℝ} (ht : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  rw [if_pos (by linarith)]
  have hlog : Real.log 2 ≤ Real.log (2 * t) := by
    exact Real.log_le_log (by norm_num) (by linarith)
  have hcut : Real.log 2 - |Real.log (2 * t)| ≤ 0 :=
    sub_nonpos.mpr (hlog.trans (le_abs_self (Real.log (2 * t))))
  rw [max_eq_left hcut, mul_zero]
-- END EXTRACT TaoFivePrimes.CutoffBridgeDecayReuse.eta0_eq_zero_of_ge_fd

-- BEGIN EXTRACT TaoFivePrimes.CutoffBridgeDecayReuse.eta0_left_formula_fd
lemma eta0_left_formula_fd {t : ℝ} (htlo : 1 / 4 ≤ t) (hthi : t ≤ 1 / 2) :
    eta0 t = 4 * (2 * Real.log 2 + Real.log t) := by
  unfold eta0
  rw [if_pos (by linarith), abs_of_nonpos]
  · rw [max_eq_right]
    · rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : t ≠ 0)]
      ring
    · have hlog : Real.log (1 / 2 : ℝ) ≤ Real.log (2 * t) := by
        exact Real.log_le_log (by norm_num) (by linarith)
      rw [log_half_fd] at hlog
      linarith
  · exact Real.log_nonpos (by positivity) (by linarith)
-- END EXTRACT TaoFivePrimes.CutoffBridgeDecayReuse.eta0_left_formula_fd

-- BEGIN EXTRACT TaoFivePrimes.CutoffBridgeDecayReuse.eta0_right_formula_fd
lemma eta0_right_formula_fd {t : ℝ} (htlo : 1 / 2 ≤ t) (hthi : t ≤ 1) :
    eta0 t = -4 * Real.log t := by
  unfold eta0
  rw [if_pos (by linarith), abs_of_nonneg]
  · rw [max_eq_right]
    · rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : t ≠ 0)]
      ring
    · have hlog : Real.log (2 * t) ≤ Real.log 2 := by
        exact Real.log_le_log (by positivity) (by linarith)
      linarith
  · exact Real.log_nonneg (by linarith)
-- END EXTRACT TaoFivePrimes.CutoffBridgeDecayReuse.eta0_right_formula_fd
end TaoFivePrimes.CutoffBridgeDecayReuse
end Package_CutoffBridgeDecayReuse

section Package_SmallQOverlapAux
set_option autoImplicit false
open scoped BigOperators
open TaoFivePrimes SmallQSmoothingAux MeasureTheory
open TaoFivePrimes.CutoffBridgeDecayReuse
attribute [local instance] Classical.propDecidable
namespace SmallQOverlapAux

-- BEGIN EXTRACT SmallQOverlapAux.reciprocal_Icc
/-- A closed reciprocal window inside a positive ambient interval has the exact
logarithmic integral, including the singleton case. -/
theorem reciprocal_Icc (a b l u : ℝ) (ha : 0 < a) (hal : a ≤ l)
    (hlu : l ≤ u) (hub : u ≤ b) :
    (∫ W : ℝ in a..b, if W ∈ Set.Icc l u then 1/W else 0) =
      Real.log u - Real.log l := by
  let f : ℝ → ℝ := fun W ↦ if W ∈ Set.Icc l u then 1/W else 0
  have hi (c e : ℝ) (hc : 0 < c) (hce : c ≤ e) :
      IntervalIntegrable f volume c e := by
    have hr : IntervalIntegrable (fun W : ℝ ↦ 1/W) volume c e := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hce]
      exact continuousOn_const.div continuousOn_id
        (fun W hW ↦ ne_of_gt (hc.trans_le hW.1))
    have hf : f = (Set.Icc l u).indicator (fun W : ℝ ↦ 1/W) := by
      funext W
      dsimp only [f, Set.indicator]
      split_ifs <;> rfl
    rw [hf]
    exact ⟨hr.1.indicator measurableSet_Icc, hr.2.indicator measurableSet_Icc⟩
  have hz1 : (∫ W : ℝ in a..l, f W) = 0 := by
    calc
      _ = ∫ W : ℝ in a..l, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        intro W hW
        rw [Set.uIoo_of_le hal] at hW
        simp [f, Set.mem_Icc, not_le.mpr hW.2]
      _ = 0 := by simp
  have hz2 : (∫ W : ℝ in u..b, f W) = 0 := by
    calc
      _ = ∫ W : ℝ in u..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        intro W hW
        rw [Set.uIoo_of_le hub] at hW
        simp [f, Set.mem_Icc, not_le.mpr hW.1]
      _ = 0 := by simp
  have hm : (∫ W : ℝ in l..u, f W) = Real.log u - Real.log l := by
    calc
      _ = ∫ W : ℝ in l..u, 1/W := by
        apply intervalIntegral.integral_congr
        intro W hW
        rw [Set.uIcc_of_le hlu] at hW
        exact if_pos hW
      _ = _ := by
        rw [integral_one_div_of_pos (ha.trans_le hal) (ha.trans_le (hal.trans hlu)),
          Real.log_div (ne_of_gt (ha.trans_le (hal.trans hlu))) (ne_of_gt (ha.trans_le hal))]
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hi a l ha hal) (hi l u (ha.trans_le hal) hlu)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hi a u ha (hal.trans hlu)) (hi u b (ha.trans_le (hal.trans hlu)) hub)
  dsimp only [f] at *
  linarith
-- END EXTRACT SmallQOverlapAux.reciprocal_Icc

-- BEGIN EXTRACT SmallQOverlapAux.reciprocal_Icc_empty
/-- Empty reciprocal windows vanish, with no assumptions about the ambient endpoints. -/
theorem reciprocal_Icc_empty (a b l u : ℝ) (hu : u < l) :
    (∫ W : ℝ in a..b, if W ∈ Set.Icc l u then 1/W else 0) = 0 := by
  simp [Set.Icc_eq_empty_of_lt hu]
-- END EXTRACT SmallQOverlapAux.reciprocal_Icc_empty

-- BEGIN EXTRACT SmallQOverlapAux.cutoff_log_overlap
/-- The positive overlap endpoints reproduce the literal logarithmic cutoff.
This is an algebraic evaluation, valid independently of the Vaughan truncation. -/
theorem cutoff_log_overlap (x d w : ℝ) (hx : 0 < x) (hd : 0 < d) (hw : 0 < w) :
    eta0 (d*w/x) = if max w (x/(2*d)) ≤ min (2*w) (x/d) then
      4 * (Real.log (min (2*w) (x/d)) - Real.log (max w (x/(2*d)))) else 0 := by
  have ht : 0 < d*w/x := by positivity
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hw0 : w ≠ 0 := ne_of_gt hw
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hlogt : Real.log (d*w/x) = Real.log d + Real.log w - Real.log x := by
    rw [Real.log_div (by positivity) hx0, Real.log_mul hd0 hw0]
  have hlogxd : Real.log (x/d) = Real.log x - Real.log d := Real.log_div hx0 hd0
  have hlog2w : Real.log (2*w) = Real.log 2 + Real.log w :=
    Real.log_mul (by norm_num) hw0
  have hlogx2d : Real.log (x/(2*d)) = Real.log x - (Real.log 2 + Real.log d) := by
    rw [Real.log_div hx0 (by positivity), Real.log_mul (by norm_num) hd0]
  by_cases hlo : d*w/x < 1/4
  · have hprod : 4*(d*w) < x := by
      have := (div_lt_iff₀ hx).mp hlo
      nlinarith
    have hemp : min (2*w) (x/d) < max w (x/(2*d)) := by
      have hh : 2*w < x/(2*d) := (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
      exact (min_le_left _ _).trans_lt (hh.trans_le (le_max_right _ _))
    rw [if_neg (not_le.mpr hemp), eta0_eq_zero_of_le_fd hlo.le]
  by_cases hhi : 1 < d*w/x
  · have hprod : x < d*w := by simpa using (lt_div_iff₀ hx).mp hhi
    have hemp : min (2*w) (x/d) < max w (x/(2*d)) := by
      have hh : x/d < w := (div_lt_iff₀ hd).mpr (by nlinarith)
      exact (min_le_right _ _).trans_lt (hh.trans_le (le_max_left _ _))
    rw [if_neg (not_le.mpr hemp), eta0_eq_zero_of_ge_fd hhi.le]
  have htl : 1/4 ≤ d*w/x := le_of_not_gt hlo
  have htu : d*w/x ≤ 1 := le_of_not_gt hhi
  have hprodlo : x ≤ 4*(d*w) := by
    have := (le_div_iff₀ hx).mp htl
    nlinarith
  have hprodhi : d*w ≤ x := by
    have := (div_le_iff₀ hx).mp htu
    nlinarith
  by_cases hmid : d*w/x ≤ 1/2
  · have hprodmid : 2*(d*w) ≤ x := by
      have := (div_le_iff₀ hx).mp hmid
      nlinarith
    have hmax : max w (x/(2*d)) = x/(2*d) :=
      max_eq_right ((le_div_iff₀ (by positivity)).mpr (by nlinarith))
    have hmin : min (2*w) (x/d) = 2*w :=
      min_eq_left ((le_div_iff₀ hd).mpr (by nlinarith))
    have hle : x/(2*d) ≤ 2*w := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    rw [hmax, hmin, if_pos hle, eta0_left_formula_fd htl hmid, hlogt, hlog2w, hlogx2d]
    ring
  · have hmid' : 1/2 ≤ d*w/x := (lt_of_not_ge hmid).le
    have hprodmid : x ≤ 2*(d*w) := by
      have := (le_div_iff₀ hx).mp hmid'
      nlinarith
    have hmax : max w (x/(2*d)) = w :=
      max_eq_left ((div_le_iff₀ (by positivity)).mpr (by nlinarith))
    have hmin : min (2*w) (x/d) = x/d :=
      min_eq_right ((div_le_iff₀ hd).mpr (by nlinarith))
    have hle : w ≤ x/d := (le_div_iff₀ hd).mpr (by nlinarith)
    rw [hmax, hmin, if_pos hle, eta0_right_formula_fd hmid' htu, hlogt, hlogxd]
    ring
-- END EXTRACT SmallQOverlapAux.cutoff_log_overlap

-- BEGIN EXTRACT SmallQOverlapAux.cutoff_overlap
/-- Strict Vaughan cutoffs place the entire nonempty overlap inside q..q^2. -/
theorem cutoff_overlap (x : ℝ) (q d w : ℕ)
    (hx : 0 < x) (hq : 1 ≤ q) (hd : 0 < d) (hw : 0 < w)
    (hdu : x/(q : ℝ)^2 < d) (hwq : q < w) :
    eta0 ((d*w : ℕ) / x) =
      4 * ∫ W : ℝ in (q : ℝ)..((q : ℝ)^2),
        if window x W d w then 1/W else 0 := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0 : ℝ) < q := by linarith
  have hqq : (q : ℝ) ≤ (q : ℝ)^2 := by nlinarith
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hwr : (0 : ℝ) < w := by exact_mod_cast hw
  have hal : (q : ℝ) ≤ max (w : ℝ) (x/(2*d)) :=
    (by exact_mod_cast hwq.le : (q : ℝ) ≤ w).trans (le_max_left _ _)
  have hub : min (2*w : ℝ) (x/d) ≤ (q : ℝ)^2 := by
    apply (min_le_right _ _).trans
    apply (div_le_iff₀ hdr).mpr
    have := (div_lt_iff₀ (sq_pos_of_pos hqp)).mp hdu
    nlinarith
  have he : (∫ W : ℝ in (q : ℝ)..((q : ℝ)^2),
      if window x W d w then 1/W else 0) =
      ∫ W : ℝ in (q : ℝ)..((q : ℝ)^2),
        if W ∈ Set.Icc (max (w : ℝ) (x/(2*d))) (min (2*w : ℝ) (x/d)) then 1/W else 0 := by
    apply intervalIntegral.integral_congr
    intro W hW
    rw [Set.uIcc_of_le hqq] at hW
    dsimp only
    rw [window_iff_overlap x W d w hd (hqp.trans_le hW.1)]
    split_ifs <;> rfl
  rw [he]
  push_cast
  rw [cutoff_log_overlap x d w hx hdr hwr]
  split_ifs with h
  · rw [reciprocal_Icc _ _ _ _ hqp hal h hub]
  · rw [reciprocal_Icc_empty _ _ _ _ (lt_of_not_ge h), mul_zero]
-- END EXTRACT SmallQOverlapAux.cutoff_overlap
end SmallQOverlapAux
end Package_SmallQOverlapAux

section Package_Theorem51DyadicDefs
set_option autoImplicit false
open scoped BigOperators
open TaoFivePrimes SmallQSmoothingAux MeasureTheory
attribute [local instance] Classical.propDecidable
namespace Theorem51Dyadic

-- BEGIN EXTRACT Theorem51Dyadic.Hyp
/-- Exact source hypotheses, with no arithmetic bound assumed. -/
def Hyp (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (U V : ℝ) : Prop :=
  4 ≤ q ∧ Nat.Coprime a.natAbs q ∧ 4*alpha = (a : ℝ)/q + beta ∧
  |beta| ≤ 1/(q : ℝ)^2 ∧ 40 ≤ U ∧ 40 ≤ V ∧ U < x ∧ V < x ∧
  U*V ≤ x/4 ∧ x ≤ U*V^2
-- END EXTRACT Theorem51Dyadic.Hyp

-- BEGIN EXTRACT Theorem51Dyadic.term
/-- One actual closed-window term before division by the localization variable. -/
noncomputable def term (x alpha U V W : ℝ) (d w : ℕ) : ℂ :=
  if U < (d : ℝ) ∧ V < (w : ℝ) ∧ Nat.Coprime d 2 ∧ Nat.Coprime w 2 then
    if window x W d w then
      (ArithmeticFunction.moebius d : ℂ) * (theorem51Centered V w : ℂ) *
        expCircle (alpha*(d*w))
    else 0
  else 0
-- END EXTRACT Theorem51Dyadic.term

-- BEGIN EXTRACT Theorem51Dyadic.box
/-- The genuine finite complex dyadic box, with arbitrary real strict cutoffs. -/
noncomputable def box (x alpha U V W : ℝ) : ℂ :=
  ∑ d ∈ Finset.range (⌊x⌋₊+1), ∑ w ∈ Finset.range (⌊x⌋₊+1), term x alpha U V W d w
-- END EXTRACT Theorem51Dyadic.box

-- BEGIN EXTRACT Theorem51Dyadic.G
/-- Explicit closed-support extension of the norm of the genuine complex box. -/
noncomputable def G (x alpha U V W : ℝ) : ℝ :=
  if W ∈ Set.Icc V (x/U) then ‖box x alpha U V W‖ else 0
-- END EXTRACT Theorem51Dyadic.G

-- BEGIN EXTRACT Theorem51Dyadic.cell
/-- An actual reciprocal cell. -/
noncomputable def cell (x alpha U V W : ℝ) (d w : ℕ) : ℂ :=
  term x alpha U V W d w / (W : ℂ)
-- END EXTRACT Theorem51Dyadic.cell
end Theorem51Dyadic
end Package_Theorem51DyadicDefs

section Package_Theorem51DyadicSmoothing
set_option autoImplicit false
open scoped BigOperators
open TaoFivePrimes SmallQCancellationAux SmallQSmoothingAux SmallQOverlapAux MeasureTheory
attribute [local instance] Classical.propDecidable
namespace Theorem51Dyadic

-- BEGIN EXTRACT Theorem51Dyadic.cutoff_overlap
/-- Strict arbitrary-real cutoffs place the overlap inside V..x/U. -/
theorem cutoff_overlap (x U V : ℝ) (d w : ℕ) (hx : 0 < x) (hU : 0 < U)
    (hV : 0 < V) (hVU : V ≤ x/U) (hd : 0 < d) (hw : 0 < w)
    (hdu : U < d) (hwv : V < w) :
    eta0 ((d*w : ℕ)/x) = 4 * ∫ W : ℝ in V..(x/U),
      if window x W d w then 1/W else 0 := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hwr : (0 : ℝ) < w := by exact_mod_cast hw
  have hal : V ≤ max (w : ℝ) (x/(2*d)) := hwv.le.trans (le_max_left _ _)
  have hub : min (2*w : ℝ) (x/d) ≤ x/U :=
    (min_le_right _ _).trans (div_le_div_of_nonneg_left hx.le hU hdu.le)
  have he : (∫ W : ℝ in V..(x/U), if window x W d w then 1/W else 0) =
      ∫ W : ℝ in V..(x/U),
        if W ∈ Set.Icc (max (w : ℝ) (x/(2*d))) (min (2*w : ℝ) (x/d)) then 1/W else 0 := by
    apply intervalIntegral.integral_congr
    intro W hW
    rw [Set.uIcc_of_le hVU] at hW
    dsimp only
    rw [window_iff_overlap x W d w hd (hV.trans_le hW.1)]
    split_ifs <;> rfl
  rw [he]
  push_cast
  rw [cutoff_log_overlap x d w hx hdr hwr]
  split_ifs with h
  · rw [reciprocal_Icc _ _ _ _ hV hal h hub]
  · rw [reciprocal_Icc_empty _ _ _ _ (lt_of_not_ge h), mul_zero]
-- END EXTRACT Theorem51Dyadic.cutoff_overlap

-- BEGIN EXTRACT Theorem51Dyadic.cell_integrable
/-- Genuine reciprocal cells are integrable on positive compact intervals. -/
theorem cell_integrable (x alpha U V : ℝ) (d w : ℕ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun W ↦ cell x alpha U V W d w) volume a b := by
  have hi : IntervalIntegrable (fun W : ℝ ↦
      (ArithmeticFunction.moebius d : ℂ) * (theorem51Centered V w : ℂ) *
        expCircle (alpha*(d*w)) / (W : ℂ)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply continuousOn_const.div Complex.continuous_ofReal.continuousOn
    intro W hW
    exact_mod_cast ne_of_gt (ha.trans_le hW.1)
  unfold cell term
  split_ifs with ht
  · have he : (fun W : ℝ ↦
        (if window x W d w then
          (ArithmeticFunction.moebius d : ℂ) * (theorem51Centered V w : ℂ) *
            expCircle (alpha*(d*w)) else 0) / (W : ℂ)) =
        fun W ↦ if window x W d w then
          (ArithmeticFunction.moebius d : ℂ) * (theorem51Centered V w : ℂ) *
            expCircle (alpha*(d*w)) / (W : ℂ) else 0 := by
      funext W; split_ifs <;> simp
    rw [he]
    exact ite_integrable hi _ (window_measurable x d w)
  · simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (0 : ℂ)) volume a b)
-- END EXTRACT Theorem51Dyadic.cell_integrable

-- BEGIN EXTRACT Theorem51Dyadic.box_div_eq_cells
/-- Division distributes over the actual finite complex box. -/
theorem box_div_eq_cells (x alpha U V W : ℝ) :
    box x alpha U V W / (W : ℂ) =
      ∑ d ∈ Finset.range (⌊x⌋₊+1), ∑ w ∈ Finset.range (⌊x⌋₊+1),
        cell x alpha U V W d w := by
  simp only [box, cell, Finset.sum_div]
-- END EXTRACT Theorem51Dyadic.box_div_eq_cells

-- BEGIN EXTRACT Theorem51Dyadic.box_integrable
/-- The actual box/W is integrable, independently of any envelope estimate. -/
theorem box_integrable (x alpha U V a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun W ↦ box x alpha U V W / (W : ℂ)) volume a b := by
  simp_rw [box_div_eq_cells]
  simpa only [Finset.sum_fn] using
    IntervalIntegrable.sum (Finset.range (⌊x⌋₊+1)) (fun d _ ↦
      IntervalIntegrable.sum (Finset.range (⌊x⌋₊+1))
        (fun w _ ↦ cell_integrable x alpha U V d w a b ha hab))
-- END EXTRACT Theorem51Dyadic.box_integrable

-- BEGIN EXTRACT Theorem51Dyadic.integral_box_eq_sum
/-- Finite interchange uses the actual integrability of each complex cell. -/
theorem integral_box_eq_sum (x alpha U V a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ W : ℝ in a..b, box x alpha U V W / (W : ℂ)) =
      ∑ d ∈ Finset.range (⌊x⌋₊+1), ∑ w ∈ Finset.range (⌊x⌋₊+1),
        ∫ W : ℝ in a..b, cell x alpha U V W d w := by
  simp_rw [box_div_eq_cells]
  have hi (d : ℕ) : IntervalIntegrable
      (fun W ↦ ∑ w ∈ Finset.range (⌊x⌋₊+1), cell x alpha U V W d w) volume a b := by
    simpa only [Finset.sum_fn] using
      IntervalIntegrable.sum (Finset.range (⌊x⌋₊+1))
        (fun w _ ↦ cell_integrable x alpha U V d w a b ha hab)
  rw [intervalIntegral.integral_finsetSum (fun d _ ↦ hi d)]
  apply Finset.sum_congr rfl
  intro d hd
  exact intervalIntegral.integral_finsetSum
    (fun w _ ↦ cell_integrable x alpha U V d w a b ha hab)
-- END EXTRACT Theorem51Dyadic.integral_box_eq_sum

-- BEGIN EXTRACT Theorem51Dyadic.cell_recovery
/-- Recover one exact kernel term, including zero and even indices. -/
theorem cell_recovery (x alpha U V : ℝ) (d w : ℕ) (hx : 0 < x) (hU : 0 < U)
    (hV : 0 < V) (hVU : V ≤ x/U) :
    (if U < (d : ℝ) ∧ V < (w : ℝ) then
      (ArithmeticFunction.moebius d : ℂ) * (centered V w : ℂ) * kernel x alpha (d*w)
    else 0) = (4 : ℂ) * ∫ W : ℝ in V..(x/U), cell x alpha U V W d w := by
  by_cases ht : U < (d : ℝ) ∧ V < (w : ℝ)
  · rw [if_pos ht]
    by_cases ho : Nat.Coprime d 2 ∧ Nat.Coprime w 2
    · have hd : 0 < d := by exact_mod_cast (hU.trans ht.1)
      have hw : 0 < w := by exact_mod_cast (hV.trans ht.2)
      have he := cutoff_overlap x U V d w hx hU hV hVU hd hw ht.1 ht.2
      have hc : (fun W : ℝ ↦ cell x alpha U V W d w) =
          fun W ↦ ((ArithmeticFunction.moebius d : ℂ) * (centered V w : ℂ) *
            expCircle (alpha*(d*w))) *
              ((if window x W d w then 1/W else 0 : ℝ) : ℂ) := by
        funext W
        unfold cell term
        rw [if_pos ⟨ht.1, ht.2, ho.1, ho.2⟩, Theorem51Interface.centered_eq]
        split_ifs <;> push_cast <;> ring
      rw [hc, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
      rw [kernel, if_pos (Nat.coprime_mul_iff_left.mpr ho), he]
      push_cast
      ring
    · have hz : ¬ Nat.Coprime (d*w) 2 := by simpa only [Nat.coprime_mul_iff_left] using ho
      have hc : ∀ W : ℝ, cell x alpha U V W d w = 0 := by
        intro W
        unfold cell term
        rw [if_neg (fun h ↦ ho ⟨h.2.2.1, h.2.2.2⟩), zero_div]
      simp only [kernel, hz, if_false, mul_zero, hc, intervalIntegral.integral_zero]
  · have hc : ∀ W : ℝ, cell x alpha U V W d w = 0 := by
      intro W
      unfold cell term
      rw [if_neg (fun h ↦ ht ⟨h.1, h.2.1⟩), zero_div]
    simp only [ht, if_false, hc, intervalIntegral.integral_zero, mul_zero]
-- END EXTRACT Theorem51Dyadic.cell_recovery

-- BEGIN EXTRACT Theorem51Dyadic.smoothing_identity
/-- The literal infinite Type II norm is exactly the smoothed finite complex integral. -/
theorem smoothing_identity (x alpha U V : ℝ) (hx : 0 < x) (hU : 0 < U)
    (hV : 0 < V) (hVU : V ≤ x/U) :
    theorem51TypeII x alpha U V =
      ‖(4 : ℂ) * ∫ W : ℝ in V..(x/U), box x alpha U V W / (W : ℂ)‖ := by
  rw [Theorem51Interface.typeII_kernel_finite x alpha U V hx,
    integral_box_eq_sum x alpha U V _ _ hV hVU]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro w hw
  exact cell_recovery x alpha U V d w hx hU hV hVU
-- END EXTRACT Theorem51Dyadic.smoothing_identity

-- BEGIN EXTRACT Theorem51Dyadic.G_nonneg
/-- Global nonnegativity of the explicit norm extension. -/
theorem G_nonneg (x alpha U V W : ℝ) : 0 ≤ G x alpha U V W := by
  unfold G; split_ifs <;> positivity
-- END EXTRACT Theorem51Dyadic.G_nonneg

-- BEGIN EXTRACT Theorem51Dyadic.G_support
/-- Global closed support of the explicit norm extension. -/
theorem G_support (x alpha U V W : ℝ) (h : W ∉ Set.Icc V (x/U)) :
    G x alpha U V W = 0 := by simp only [G, if_neg h]
-- END EXTRACT Theorem51Dyadic.G_support

-- BEGIN EXTRACT Theorem51Dyadic.G_on
/-- Inside the source interval the extension is exactly the actual box norm. -/
theorem G_on (x alpha U V W : ℝ) (h : W ∈ Set.Icc V (x/U)) :
    G x alpha U V W = ‖box x alpha U V W‖ := by simp only [G, if_pos h]
-- END EXTRACT Theorem51Dyadic.G_on

-- BEGIN EXTRACT Theorem51Dyadic.norm_box_integrable
/-- Reciprocal norm integrability on the compact source interval. -/
theorem norm_box_integrable (x alpha U V : ℝ) (hV : 0 < V) (hVU : V ≤ x/U) :
    IntervalIntegrable (fun W ↦ ‖box x alpha U V W‖ / W) volume V (x/U) := by
  apply (box_integrable x alpha U V _ _ hV hVU).norm.congr
  intro W hW
  rw [Set.uIoc_of_le hVU] at hW
  dsimp only
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hV.trans hW.1)]
-- END EXTRACT Theorem51Dyadic.norm_box_integrable

-- BEGIN EXTRACT Theorem51Dyadic.G_div_indicator
/-- The Ioi integrand is an indicator of a genuinely integrable compact function. -/
theorem G_div_indicator (x alpha U V : ℝ) :
    (fun W ↦ G x alpha U V W / W) =
      (Set.Icc V (x/U)).indicator (fun W ↦ ‖box x alpha U V W‖ / W) := by
  funext W
  simp only [G, Set.indicator_apply]
  split_ifs <;> simp
-- END EXTRACT Theorem51Dyadic.G_div_indicator

-- BEGIN EXTRACT Theorem51Dyadic.G_integrable
/-- Genuine source Ioi integrability, not a nonintegrable default-zero expression. -/
theorem G_integrable (x alpha U V : ℝ) (hV : 0 < V) (hVU : V ≤ x/U) :
    IntegrableOn (fun W ↦ G x alpha U V W / W) (Set.Ioi 0) := by
  rw [G_div_indicator]
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hVU).mp
    (norm_box_integrable x alpha U V hV hVU)
  exact (hi.integrable_indicator measurableSet_Icc).integrableOn
-- END EXTRACT Theorem51Dyadic.G_integrable

-- BEGIN EXTRACT Theorem51Dyadic.G_integral
/-- The source Ioi integral equals the compact integral with unchanged real variable. -/
theorem G_integral (x alpha U V : ℝ) (hV : 0 < V) (hVU : V ≤ x/U) :
    (∫ W : ℝ in Set.Ioi 0, G x alpha U V W / W) =
      ∫ W : ℝ in V..(x/U), ‖box x alpha U V W‖ / W := by
  have hs : Set.Icc V (x/U) ⊆ Set.Ioi 0 := fun W hW ↦ hV.trans_le hW.1
  rw [G_div_indicator, setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_right.mpr hs, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hVU]
-- END EXTRACT Theorem51Dyadic.G_integral

-- BEGIN EXTRACT Theorem51Dyadic.smoothing_bound
/-- Norm-to-integral smoothing with exact coefficient 4 and no arithmetic hypothesis. -/
theorem smoothing_bound (x alpha U V : ℝ) (hx : 0 < x) (hU : 0 < U)
    (hV : 0 < V) (hVU : V ≤ x/U) :
    theorem51TypeII x alpha U V ≤ 4 * ∫ W : ℝ in Set.Ioi 0, G x alpha U V W / W := by
  rw [smoothing_identity x alpha U V hx hU hV hVU, norm_mul]
  norm_num only [Complex.norm_ofNat]
  rw [G_integral x alpha U V hV hVU]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∫ W : ℝ in V..(x/U), ‖box x alpha U V W / (W : ℂ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hVU
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro W hW
      rw [Set.uIcc_of_le hVU] at hW
      dsimp only
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hV.trans_le hW.1)]
-- END EXTRACT Theorem51Dyadic.smoothing_bound
end Theorem51Dyadic
end Package_Theorem51DyadicSmoothing

section Package_Theorem51DyadicEnergyGate
set_option autoImplicit false
open Theorem51Dyadic
namespace Theorem51DyadicEnergyGate

-- BEGIN EXTRACT Theorem51DyadicEnergyGate.sizes
/-- Exact source guards imply both quantitative rounding-cost guards for every closed W. -/
theorem sizes (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (U V W : ℝ)
    (h : Hyp x alpha beta a q U V) (hW : W ∈ Set.Icc V (x/U)) :
    0 < x ∧ 40 ≤ W ∧ 40 ≤ x/W := by
  rcases h with ⟨hq,haq,ha,hb,hU,hV,hUx,hVx,hUV,hUV2⟩
  fail_if_success have : False := by omega
  fail_if_success have : False := by linarith
  have hWp : 0 < W := by linarith [hW.1]
  refine ⟨by linarith, by linarith [hW.1], ?_⟩
  apply (le_div_iff₀ hWp).2
  have hh := (le_div_iff₀ (show 0 < U by linarith)).mp hW.2
  nlinarith
-- END EXTRACT Theorem51DyadicEnergyGate.sizes
end Theorem51DyadicEnergyGate
end Package_Theorem51DyadicEnergyGate

section Package_SmallQSpacingAux
set_option autoImplicit false
open scoped BigOperators
namespace SmallQSpacingAux

-- BEGIN EXTRACT SmallQSpacingAux.numerator_not_dvd
/-- Multiplication by the literal signed coprime numerator preserves nondivisibility. -/
theorem numerator_not_dvd (a : ℤ) (q : ℕ) (d : ℤ)
    (ha : Nat.Coprime a.natAbs q) (hd : ¬ (q : ℤ) ∣ d) :
    ¬ (q : ℤ) ∣ a*d := by
  intro h
  apply hd
  rw [Int.natCast_dvd] at h ⊢
  rw [Int.natAbs_mul] at h
  exact ha.symm.dvd_mul_left.mp h
-- END EXTRACT SmallQSpacingAux.numerator_not_dvd

-- BEGIN EXTRACT SmallQSpacingAux.rational_gap
/-- Nonzero rational residues stay at distance at least 1/q from every integer. -/
theorem rational_gap (a : ℤ) (q : ℕ) (d k : ℤ)
    (hq : 0 < q) (ha : Nat.Coprime a.natAbs q) (hd : ¬ (q : ℤ) ∣ d) :
    1/(q : ℝ) ≤ |(a : ℝ)*d/q-k| := by
  have hz : a*d-(q : ℤ)*k ≠ 0 := by
    intro h
    exact numerator_not_dvd a q d ha hd ⟨k, by linarith⟩
  have hi := Int.one_le_abs hz
  have hr : (1 : ℝ) ≤ |(a : ℝ)*d-(q : ℝ)*k| := by exact_mod_cast hi
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  rw [show (a : ℝ)*d/q-k = ((a : ℝ)*d-q*k)/q by field_simp <;> ring,
    abs_div, abs_of_pos hqr]
  exact div_le_div_of_nonneg_right hr hqr.le
-- END EXTRACT SmallQSpacingAux.rational_gap

-- BEGIN EXTRACT SmallQSpacingAux.initial_gap
/-- The initial interval has quantitative separation at the original frequency 4 alpha.
This holds for signed d and a, and both endpoints of the beta error interval. -/
theorem initial_gap (alpha beta : ℝ) (a : ℤ) (q : ℕ) (d k : ℤ)
    (hq : 0 < q) (ha : Nat.Coprime a.natAbs q)
    (halpha : 4*alpha = (a : ℝ)/q+beta) (hbeta : |beta| ≤ 1/(q : ℝ)^2)
    (hd : ¬ (q : ℤ) ∣ d) (hsize : |(d : ℝ)| ≤ q/2) :
    1/(2*(q : ℝ)) ≤ |4*(d : ℝ)*alpha-k| := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have he : |(d : ℝ)*beta| ≤ 1/(2*(q : ℝ)) := by
    rw [abs_mul]
    calc
      _ ≤ ((q : ℝ)/2)*(1/(q : ℝ)^2) :=
        mul_le_mul hsize hbeta (abs_nonneg _) (by positivity)
      _ = _ := by field_simp <;> ring
  have ht := abs_sub_le ((a : ℝ)*d/q) (4*(d : ℝ)*alpha) (k : ℝ)
  have hh : (a : ℝ)*d/q-4*(d : ℝ)*alpha = -(d : ℝ)*beta := by
    calc
      _ = (d : ℝ)*((a : ℝ)/q-4*alpha) := by ring
      _ = _ := by rw [halpha]; ring
  rw [hh, abs_mul, abs_neg] at ht
  have hg := rational_gap a q d k hq ha hd
  rw [abs_mul] at he
  have hf : 1/(q : ℝ) = 2*(1/(2*(q : ℝ))) := by field_simp <;> ring
  linarith
-- END EXTRACT SmallQSpacingAux.initial_gap
end SmallQSpacingAux
end Package_SmallQSpacingAux

section Package_SmallQSieveAux
set_option autoImplicit false
open scoped BigOperators
open TaoFivePrimes SmallQCancellationAux SmallQTypeIIAux
namespace SmallQSieveAux

-- BEGIN EXTRACT SmallQSieveAux.odd_card
/-- A finite collection of odd natural numbers in a closed real interval has at most
half the interval length plus one elements. Empty and singleton intervals are retained. -/
theorem odd_card (s : Finset ℕ) (L U : ℝ) (hLU : L ≤ U)
    (hs : ∀ n ∈ s, Nat.Coprime n 2 ∧ L ≤ (n : ℝ) ∧ (n : ℝ) ≤ U) :
    (s.card : ℝ) ≤ (U-L)/2+1 := by
  classical
  induction s using Finset.induction_on_min generalizing L U with
  | empty => simp only [Finset.card_empty, Nat.cast_zero]; linarith
  | @insert a s ha ih =>
    have hna : a ∉ s := fun h ↦ (lt_irrefl a) (ha a h)
    obtain ⟨hao, hLa, haU⟩ := hs a (Finset.mem_insert_self a s)
    have hrest (n : ℕ) (hn : n ∈ s) :
        Nat.Coprime n 2 ∧ (a : ℝ)+2 ≤ n ∧ (n : ℝ) ≤ U := by
      obtain ⟨hno, _, hnU⟩ := hs n (Finset.mem_insert_of_mem hn)
      have hlt := ha n hn
      have hoa := Nat.coprime_two_right.mp hao
      have hon := Nat.coprime_two_right.mp hno
      obtain ⟨i, hi⟩ := hoa
      obtain ⟨j, hj⟩ := hon
      have hh : a+2 ≤ n := by omega
      exact ⟨hno, by exact_mod_cast hh, hnU⟩
    rw [Finset.card_insert_of_notMem hna, Nat.cast_add, Nat.cast_one]
    rcases s.eq_empty_or_nonempty with he | ⟨n, hn⟩
    · simp only [he, Finset.card_empty, Nat.cast_zero]
      linarith
    · have hr := hrest n hn
      have hh := ih ((a : ℝ)+2) U (hr.2.1.trans hr.2.2) hrest
      linarith
-- END EXTRACT SmallQSieveAux.odd_card

-- BEGIN EXTRACT SmallQSieveAux.local_gap
/-- The literal near-rational hypotheses give local odd-lattice separation from every
integer, including signed differences and both beta endpoints. -/
theorem local_gap (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (ha : Nat.Coprime a.natAbs q) (halpha : 4*alpha = (a : ℝ)/q+beta)
    (hb : |beta| ≤ 1/(q : ℝ)^2) (j k : ℤ)
    (hj : j ≠ 0) (hjs : |(j : ℝ)| ≤ q/2) :
    1/(2*(q : ℝ)) ≤ |4*(j : ℝ)*alpha-k| := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hjq : |j| < (q : ℤ) := by exact_mod_cast (show |(j : ℝ)| < q by linarith)
  have hn : ¬ (q : ℤ) ∣ j := by
    intro hd
    have hh := Int.le_abs_of_dvd hj hd
    omega
  exact SmallQSpacingAux.initial_gap alpha beta a q j k hq ha halpha hb hn hjs
-- END EXTRACT SmallQSieveAux.local_gap
end SmallQSieveAux
end Package_SmallQSieveAux

section Package_SmallQTransferAux
set_option autoImplicit false
open scoped BigOperators ArithmeticFunction.vonMangoldt
open TaoFivePrimes
namespace SmallQTransferAux

-- BEGIN EXTRACT SmallQTransferAux.character_norm
/-- The character at a real frequency has complex norm one. -/
theorem character_norm (t : ℝ) : ‖expCircle t‖ = 1 := by
  simp [expCircle, Complex.norm_exp]
-- END EXTRACT SmallQTransferAux.character_norm
end SmallQTransferAux
end Package_SmallQTransferAux

section Package_SmallQSubdivisionAux
set_option autoImplicit false
open scoped BigOperators
open TaoFivePrimes
namespace SmallQSubdivisionAux

-- BEGIN EXTRACT SmallQSubdivisionAux.oddIndex
/-- The integer Fourier coordinate of an odd natural index. -/
def oddIndex (n : ℕ) : ℤ := (n / 2 : ℕ)
-- END EXTRACT SmallQSubdivisionAux.oddIndex

-- BEGIN EXTRACT SmallQSubdivisionAux.odd_recover
/-- Recover the original odd index, including the smallest index one. -/
theorem odd_recover (n : ℕ) (hn : Nat.Coprime n 2) : 2*(n/2)+1 = n := by
  have ho := Nat.odd_iff.mp (Nat.coprime_two_right.mp hn)
  omega
-- END EXTRACT SmallQSubdivisionAux.odd_recover

-- BEGIN EXTRACT SmallQSubdivisionAux.odd_cast
/-- The real form of the exact integer-coordinate recovery. -/
theorem odd_cast (n : ℕ) (hn : Nat.Coprime n 2) :
    (n : ℝ) = 2*(oddIndex n : ℝ)+1 := by
  have h := odd_recover n hn
  simp only [oddIndex, Int.cast_natCast]
  exact_mod_cast h.symm
-- END EXTRACT SmallQSubdivisionAux.odd_cast

-- BEGIN EXTRACT SmallQSubdivisionAux.odd_injective
/-- Integer Fourier coordinates are injective on odd supports. -/
theorem odd_injective (S : Finset ℕ) (hs : ∀ n ∈ S, Nat.Coprime n 2) :
    Set.InjOn oddIndex (S : Set ℕ) := by
  intro n hn m hm he
  change ((n/2 : ℕ) : ℤ) = ((m/2 : ℕ) : ℤ) at he
  have hdiv : n/2 = m/2 := by exact_mod_cast he
  have := odd_recover n (hs n hn)
  have := odd_recover m (hs m hm)
  omega
-- END EXTRACT SmallQSubdivisionAux.odd_injective

-- BEGIN EXTRACT SmallQSubdivisionAux.blockIndex
/-- Half-open real blocks of width q are labeled by a natural floor. -/
noncomputable def blockIndex (L : ℝ) (q n : ℕ) : ℕ := ⌊((n : ℝ)-L)/q⌋₊
-- END EXTRACT SmallQSubdivisionAux.blockIndex

-- BEGIN EXTRACT SmallQSubdivisionAux.block_bounds
/-- Every point above L lies in the half-open block named by its label. -/
theorem block_bounds (L : ℝ) (q n : ℕ) (hq : 0 < q) (hn : L ≤ (n : ℝ)) :
    L+(blockIndex L q n : ℝ)*q ≤ n ∧
    (n : ℝ) < L+((blockIndex L q n : ℝ)+1)*q := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hf := Nat.floor_le (div_nonneg (sub_nonneg.mpr hn) hqr.le)
  have ht := Nat.lt_floor_add_one (((n : ℝ)-L)/q)
  change (blockIndex L q n : ℝ) ≤ ((n : ℝ)-L)/q at hf
  change ((n : ℝ)-L)/q < (blockIndex L q n : ℝ)+1 at ht
  have h1 := (le_div_iff₀ hqr).mp hf
  have h2 := (div_lt_iff₀ hqr).mp ht
  constructor <;> linarith
-- END EXTRACT SmallQSubdivisionAux.block_bounds

-- BEGIN EXTRACT SmallQSubdivisionAux.block_mem
/-- The terminal closed endpoint is retained in the last natural floor block. -/
theorem block_mem (L U : ℝ) (q n : ℕ) (hq : 0 < q) (hn : (n : ℝ) ≤ U) :
    blockIndex L q n ∈ Finset.range (⌊(U-L)/(q : ℝ)⌋₊+1) := by
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) (by positivity))
-- END EXTRACT SmallQSubdivisionAux.block_mem

-- BEGIN EXTRACT SmallQSubdivisionAux.block_count
/-- The number of blocks has exactly the relaxed length/q+1 cost. -/
theorem block_count (L U : ℝ) (q : ℕ) (hq : 0 < q) (hLU : L ≤ U) :
    ((Finset.range (⌊(U-L)/(q : ℝ)⌋₊+1)).card : ℝ) ≤ (U-L)/q+1 := by
  have hn : 0 ≤ (U-L)/(q : ℝ) := div_nonneg (sub_nonneg.mpr hLU) (by positivity)
  simp only [Finset.card_range, Nat.cast_add, Nat.cast_one]
  linarith [Nat.floor_le hn]
-- END EXTRACT SmallQSubdivisionAux.block_count

-- BEGIN EXTRACT SmallQSubdivisionAux.block_difference
/-- Distinct odd indices in one half-open real q-block have a nonzero integer
coordinate difference of absolute value strictly below q/2. -/
theorem block_difference (L : ℝ) (q d e : ℕ) (hq : 0 < q)
    (hd : Nat.Coprime d 2) (he : Nat.Coprime e 2)
    (hLd : L ≤ (d : ℝ)) (hLe : L ≤ (e : ℝ))
    (hb : blockIndex L q d = blockIndex L q e) (hne : d ≠ e) :
    oddIndex d-oddIndex e ≠ 0 ∧
    |((oddIndex d-oddIndex e : ℤ) : ℝ)| < (q : ℝ)/2 := by
  have hdcast := odd_cast d hd
  have hecast := odd_cast e he
  obtain ⟨hdl, hdu⟩ := block_bounds L q d hq hLd
  obtain ⟨hel, heu⟩ := block_bounds L q e hq hLe
  rw [hb] at hdl hdu
  constructor
  · intro hz
    have hz' : (oddIndex d : ℝ) = (oddIndex e : ℝ) := by exact_mod_cast (sub_eq_zero.mp hz)
    have : (d : ℝ) = e := by linarith
    exact hne (by exact_mod_cast this)
  · rw [Int.cast_sub, abs_lt]
    constructor <;> linarith
-- END EXTRACT SmallQSubdivisionAux.block_difference

-- BEGIN EXTRACT SmallQSubdivisionAux.block_gap
/-- The supplied local gap gives actual separated Fourier frequencies inside each
block. No separation between different blocks is claimed. -/
theorem block_gap (L alpha : ℝ) (q : ℕ) (hq : 0 < q)
    (hg : ∀ j k : ℤ, j ≠ 0 → |(j : ℝ)| ≤ q/2 →
      1/(2*(q : ℝ)) ≤ |4*(j : ℝ)*alpha-k|)
    (d e : ℕ) (hd : Nat.Coprime d 2) (he : Nat.Coprime e 2)
    (hLd : L ≤ (d : ℝ)) (hLe : L ≤ (e : ℝ))
    (hb : blockIndex L q d = blockIndex L q e) (hne : d ≠ e) (k : ℤ) :
    1/(2*(q : ℝ)) ≤ |(2*(d : ℝ)*alpha)-(2*(e : ℝ)*alpha)-k| := by
  obtain ⟨hj, hs⟩ := block_difference L q d e hq hd he hLd hLe hb hne
  have h := hg (oddIndex d-oddIndex e) k hj hs.le
  have hdc := odd_cast d hd
  have hec := odd_cast e he
  convert h using 1
  congr 1
  push_cast
  rw [hdc, hec]
  ring
-- END EXTRACT SmallQSubdivisionAux.block_gap

-- BEGIN EXTRACT SmallQSubdivisionAux.character_add
/-- The real-frequency exponential has its literal additive phase law. -/
theorem character_add (s t : ℝ) : expCircle (s+t) = expCircle s*expCircle t := by
  unfold expCircle
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
-- END EXTRACT SmallQSubdivisionAux.character_add

-- BEGIN EXTRACT SmallQSubdivisionAux.row_reindex
/-- Exact odd-column reindexing, including the row's unit-modulus phase factor. -/
theorem row_reindex (S : Finset ℕ) (hs : ∀ w ∈ S, Nat.Coprime w 2)
    (alpha : ℝ) (d : ℕ) (b : ℕ → ℂ) :
    (∑ w ∈ S, b w*expCircle (alpha*(d*w))) =
      expCircle (alpha*d) *
        ∑ j ∈ S.image oddIndex, b (2*j.toNat+1)*expCircle ((2*d*alpha)*(j : ℝ)) := by
  classical
  rw [Finset.sum_image (odd_injective S hs), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hr : 2*(oddIndex w).toNat+1 = w := by
    change 2*(w/2)+1 = w
    exact odd_recover w (hs w hw)
  rw [hr]
  have hp : alpha*((d : ℝ)*w) = alpha*d+(2*d*alpha)*(oddIndex w : ℝ) := by
    rw [odd_cast w (hs w hw)]
    ring
  rw [hp, character_add]
  ring
-- END EXTRACT SmallQSubdivisionAux.row_reindex

-- BEGIN EXTRACT SmallQSubdivisionAux.mass_reindex
/-- Reindexing preserves the actual signed or complex coefficient L2 mass. -/
theorem mass_reindex (S : Finset ℕ) (hs : ∀ w ∈ S, Nat.Coprime w 2) (b : ℕ → ℂ) :
    (∑ j ∈ S.image oddIndex, ‖b (2*j.toNat+1)‖^2) = ∑ w ∈ S, ‖b w‖^2 := by
  classical
  rw [Finset.sum_image (odd_injective S hs)]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [oddIndex, Int.toNat_natCast, odd_recover w (hs w hw)]
-- END EXTRACT SmallQSubdivisionAux.mass_reindex

-- BEGIN EXTRACT SmallQSubdivisionAux.support_reindex
/-- The new integer Fourier support has exactly half the original real interval width. -/
theorem support_reindex (S : Finset ℕ) (L U : ℝ)
    (hs : ∀ w ∈ S, Nat.Coprime w 2 ∧ L ≤ (w : ℝ) ∧ (w : ℝ) ≤ U) :
    ∀ j ∈ S.image oddIndex, (L-1)/2 ≤ (j : ℝ) ∧ (j : ℝ) ≤ (U-1)/2 := by
  classical
  intro j hj
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨ho, hl, hu⟩ := hs w hw
  have := odd_cast w ho
  constructor <;> linarith
-- END EXTRACT SmallQSubdivisionAux.support_reindex

-- BEGIN EXTRACT SmallQSubdivisionAux.FourierBound
/-- The genuinely analytic input: a finite Fourier operator on integer frequencies,
with arbitrary separated sample phases. Delta is in (0,1], including singleton samples;
no oddness, near-rational approximation, or interval subdivision is hidden here. -/
def FourierBound : Prop :=
  ∀ (T : Finset ℕ) (J : Finset ℤ) (theta : ℕ → ℝ) (A B delta : ℝ),
    A ≤ B → 0 < delta → delta ≤ 1 →
    (∀ j ∈ J, A ≤ (j : ℝ) ∧ (j : ℝ) ≤ B) →
    (∀ d ∈ T, ∀ e ∈ T, d ≠ e → ∀ k : ℤ, delta ≤ |theta d-theta e-k|) →
    ∀ v : ℤ → ℂ,
      (∑ d ∈ T, ‖∑ j ∈ J, v j*expCircle (theta d*(j : ℝ))‖^2) ≤
        (B-A+1/delta)*(∑ j ∈ J, ‖v j‖^2)
-- END EXTRACT SmallQSubdivisionAux.FourierBound

-- BEGIN EXTRACT SmallQSubdivisionAux.one_block_operator
/-- Apply the separated Fourier input to one actual half-open block after exact
odd-column reindexing. The unit row phase disappears only after taking the norm. -/
theorem one_block_operator (hf : FourierBound)
    (D S : Finset ℕ) (alpha Ld Lw Uw : ℝ) (q r : ℕ)
    (hq : 2 ≤ q) (hw : Lw ≤ Uw)
    (hD : ∀ d ∈ D, Nat.Coprime d 2 ∧ Ld ≤ (d : ℝ))
    (hS : ∀ w ∈ S, Nat.Coprime w 2 ∧ Lw ≤ (w : ℝ) ∧ (w : ℝ) ≤ Uw)
    (hg : ∀ j k : ℤ, j ≠ 0 → |(j : ℝ)| ≤ q/2 →
      1/(2*(q : ℝ)) ≤ |4*(j : ℝ)*alpha-k|) (b : ℕ → ℂ) :
    (∑ d ∈ D.filter (fun d ↦ blockIndex Ld q d = r),
      ‖∑ w ∈ S, b w*expCircle (alpha*(d*w))‖^2) ≤
      ((Uw-Lw)/2+2*q)*(∑ w ∈ S, ‖b w‖^2) := by
  classical
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hSodd : ∀ w ∈ S, Nat.Coprime w 2 := fun w hw ↦ (hS w hw).1
  have hh := hf (D.filter (fun d ↦ blockIndex Ld q d = r)) (S.image oddIndex)
    (fun d ↦ 2*d*alpha) ((Lw-1)/2) ((Uw-1)/2) (1/(2*q))
    (by linarith) (by positivity) (by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*q)).2
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      linarith)
    (support_reindex S Lw Uw hS) (by
      intro d hd e he hne k
      obtain ⟨hdD, hdr⟩ := Finset.mem_filter.mp hd
      obtain ⟨heD, her⟩ := Finset.mem_filter.mp he
      exact block_gap Ld alpha q (by omega) hg d e (hD d hdD).1 (hD e heD).1
        (hD d hdD).2 (hD e heD).2 (hdr.trans her.symm) hne k)
    (fun j ↦ b (2*j.toNat+1))
  rw [mass_reindex S hSodd b] at hh
  have hconstant : (Uw-1)/2-(Lw-1)/2+1/(1/(2*(q : ℝ))) = (Uw-Lw)/2+2*q := by
    field_simp
    <;> ring
  rw [hconstant] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [row_reindex S hSodd alpha d b, norm_mul, SmallQTransferAux.character_norm, one_mul]
-- END EXTRACT SmallQSubdivisionAux.one_block_operator

-- BEGIN EXTRACT SmallQSubdivisionAux.operator_of_blocks
/-- Sum the genuine squared row bounds over the exact finite floor partition.
The count includes a possible last singleton block at the closed upper endpoint. -/
theorem operator_of_blocks (hf : FourierBound)
    (D S : Finset ℕ) (alpha Ld Ud Lw Uw : ℝ) (q : ℕ)
    (hq : 2 ≤ q) (hd : Ld ≤ Ud) (hw : Lw ≤ Uw)
    (hD : ∀ d ∈ D, Nat.Coprime d 2 ∧ Ld ≤ (d : ℝ) ∧ (d : ℝ) ≤ Ud)
    (hS : ∀ w ∈ S, Nat.Coprime w 2 ∧ Lw ≤ (w : ℝ) ∧ (w : ℝ) ≤ Uw)
    (hg : ∀ j k : ℤ, j ≠ 0 → |(j : ℝ)| ≤ q/2 →
      1/(2*(q : ℝ)) ≤ |4*(j : ℝ)*alpha-k|) (b : ℕ → ℂ) :
    (∑ d ∈ D, ‖∑ w ∈ S, b w*expCircle (alpha*(d*w))‖^2) ≤
      ((Uw-Lw)/2+2*q)*((Ud-Ld)/q+1)*(∑ w ∈ S, ‖b w‖^2) := by
  classical
  let R := Finset.range (⌊(Ud-Ld)/(q : ℝ)⌋₊+1)
  have hmap : ∀ d ∈ D, blockIndex Ld q d ∈ R :=
    fun d hd ↦ block_mem Ld Ud q d (by omega) (hD d hd).2.2
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ r ∈ R, ((Uw-Lw)/2+2*q)*(∑ w ∈ S, ‖b w‖^2) := by
      apply Finset.sum_le_sum
      intro r hr
      exact one_block_operator hf D S alpha Ld Lw Uw q r hq hw
        (fun d hd ↦ ⟨(hD d hd).1, (hD d hd).2.1⟩) hS hg b
    _ = (R.card : ℝ)*(((Uw-Lw)/2+2*q)*(∑ w ∈ S, ‖b w‖^2)) := by
      simp
    _ ≤ ((Ud-Ld)/q+1)*(((Uw-Lw)/2+2*q)*(∑ w ∈ S, ‖b w‖^2)) := by
      apply mul_le_mul_of_nonneg_right (block_count Ld Ud q (by omega) hd)
      have : 0 ≤ Uw-Lw := sub_nonneg.mpr hw
      positivity
    _ = _ := by ring
-- END EXTRACT SmallQSubdivisionAux.operator_of_blocks

-- BEGIN EXTRACT SmallQSubdivisionAux.bilinear_of_operator
/-- Finite complex Cauchy-Schwarz converts the row operator estimate to the requested
bilinear estimate for every complex left vector, with no positivity assumption on it. -/
theorem bilinear_of_operator (D : Finset ℕ) (c f : ℕ → ℂ) (K M : ℝ)
    (h : (∑ d ∈ D, ‖f d‖^2) ≤ K*M) :
    ‖∑ d ∈ D, c d*f d‖^2 ≤ K*(∑ d ∈ D, ‖c d‖^2)*M := by
  have ht : ‖∑ d ∈ D, c d*f d‖ ≤ ∑ d ∈ D, ‖c d‖*‖f d‖ := by
    simpa only [norm_mul] using norm_sum_le D (fun d ↦ c d*f d)
  have hs := Finset.sum_mul_sq_le_sq_mul_sq D (fun d ↦ ‖c d‖) (fun d ↦ ‖f d‖)
  have ht2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
  calc
    _ ≤ (∑ d ∈ D, ‖c d‖^2)*(∑ d ∈ D, ‖f d‖^2) := ht2.trans hs
    _ ≤ (∑ d ∈ D, ‖c d‖^2)*(K*M) :=
      mul_le_mul_of_nonneg_left h (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
    _ = _ := by ring
-- END EXTRACT SmallQSubdivisionAux.bilinear_of_operator
end SmallQSubdivisionAux
end Package_SmallQSubdivisionAux

section Package_Theorem51DyadicEnergy
set_option autoImplicit false
open scoped BigOperators
open TaoFivePrimes SmallQSmoothingAux
attribute [local instance] Classical.propDecidable
namespace Theorem51Dyadic

-- BEGIN EXTRACT Theorem51Dyadic.dSet
/-- Actual odd d indices with strict real U and closed localization. -/
noncomputable def dSet (x U W : ℝ) : Finset ℕ :=
  (Finset.range (⌊x⌋₊+1)).filter fun d ↦
    U < (d : ℝ) ∧ Nat.Coprime d 2 ∧ x/(2*W) ≤ d ∧ (d : ℝ) ≤ x/W
-- END EXTRACT Theorem51Dyadic.dSet

-- BEGIN EXTRACT Theorem51Dyadic.wSet
/-- Actual odd w indices with strict real V and closed localization. -/
noncomputable def wSet (x V W : ℝ) : Finset ℕ :=
  (Finset.range (⌊x⌋₊+1)).filter fun w ↦
    V < (w : ℝ) ∧ Nat.Coprime w 2 ∧ W/2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
-- END EXTRACT Theorem51Dyadic.wSet

-- BEGIN EXTRACT Theorem51Dyadic.row
/-- The genuine Fourier row with the original signed Mobius coefficient. -/
noncomputable def row (x alpha V W : ℝ) (d : ℕ) : ℂ :=
  (ArithmeticFunction.moebius d : ℂ) *
    ∑ w ∈ wSet x V W, (theorem51Centered V w : ℂ) * expCircle (alpha*(d*w))
-- END EXTRACT Theorem51Dyadic.row

-- BEGIN EXTRACT Theorem51Dyadic.energy
/-- Exact Cauchy row energy, including the finite outer cardinality. -/
noncomputable def energy (x alpha U V W : ℝ) : ℝ :=
  ((dSet x U W).card : ℝ) * ∑ d ∈ dSet x U W, ‖row x alpha V W d‖^2
-- END EXTRACT Theorem51Dyadic.energy

-- BEGIN EXTRACT Theorem51Dyadic.box_eq_rows
/-- Reorganize the existing finite square into its exact filtered rows. No support or
smoothing proof is repeated, and no coefficient or closed endpoint is discarded. -/
theorem box_eq_rows (x alpha U V W : ℝ) :
    box x alpha U V W = ∑ d ∈ dSet x U W, row x alpha V W d := by
  symm
  simp only [box, row, dSet, wSet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hD : U < d ∧ Nat.Coprime d 2 ∧ x/(2*W) ≤ d ∧ (d : ℝ) ≤ x/W
  · rw [if_pos hD]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hS : V < w ∧ Nat.Coprime w 2 ∧ W/2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W
    · rw [if_pos hS]
      unfold term
      rw [if_pos ⟨hD.1,hS.1,hD.2.1,hS.2.1⟩,
        if_pos ⟨hD.2.2.1,hD.2.2.2,hS.2.2.1,hS.2.2.2⟩]
      ring
    · rw [if_neg hS, mul_zero]
      unfold term
      split_ifs with hc hwin
      · exact False.elim (hS ⟨hc.2.1,hc.2.2.2,hwin.2.2.1,hwin.2.2.2⟩)
      · rfl
      · rfl
  · rw [if_neg hD]
    symm
    apply Finset.sum_eq_zero
    intro w hw
    unfold term
    split_ifs with hc hwin
    · exact False.elim (hD ⟨hc.1,hc.2.2.1,hwin.1,hwin.2.1⟩)
    · rfl
    · rfl
-- END EXTRACT Theorem51Dyadic.box_eq_rows

-- BEGIN EXTRACT Theorem51Dyadic.box_cauchy
/-- Cauchy for the actual complex finite box, with no sign or frequency assumptions. -/
theorem box_cauchy (x alpha U V W : ℝ) :
    ‖box x alpha U V W‖^2 ≤ energy x alpha U V W := by
  rw [box_eq_rows]
  have h := SmallQSubdivisionAux.bilinear_of_operator (dSet x U W) (fun _ ↦ 1)
    (row x alpha V W) (∑ d ∈ dSet x U W, ‖row x alpha V W d‖^2) 1 (by simp)
  simpa [energy, mul_comm] using h
-- END EXTRACT Theorem51Dyadic.box_cauchy

-- BEGIN EXTRACT Theorem51Dyadic.d_card
/-- Exact odd d count including the additive one for a closed interval. -/
theorem d_card (x U W : ℝ) (hx : 0 ≤ x) (hW : 0 < W) :
    ((dSet x U W).card : ℝ) ≤ x/(4*W)+1 := by
  have hc := SmallQSieveAux.odd_card (dSet x U W) (x/(2*W)) (x/W) (by
    apply div_le_div_of_nonneg_left hx hW
    linarith) (by
      intro d hd
      obtain ⟨_, _, ho, hl, hu⟩ := Finset.mem_filter.mp hd
      exact ⟨ho,hl,hu⟩)
  convert hc using 1 <;> field_simp <;> ring
-- END EXTRACT Theorem51Dyadic.d_card

-- BEGIN EXTRACT Theorem51Dyadic.w_card
/-- Exact odd w count including the additive one for a closed interval. -/
theorem w_card (x V W : ℝ) (hW : 0 ≤ W) :
    ((wSet x V W).card : ℝ) ≤ W/4+1 := by
  have hc := SmallQSieveAux.odd_card (wSet x V W) (W/2) W (by linarith) (by
    intro w hw
    obtain ⟨_, _, ho, hl, hu⟩ := Finset.mem_filter.mp hw
    exact ⟨ho,hl,hu⟩)
  convert hc using 1 <;> ring
-- END EXTRACT Theorem51Dyadic.w_card

-- BEGIN EXTRACT Theorem51Dyadic.coefficient_mass
/-- Actual centered coefficients have the half-log squared mass for every real V. -/
theorem coefficient_mass (x V W : ℝ) (hW : 1 ≤ W) :
    (∑ w ∈ wSet x V W, ‖(theorem51Centered V w : ℂ)‖^2) ≤
      ((wSet x V W).card : ℝ) * (Real.log W)^2 / 4 := by
  have hlog := Real.log_nonneg hW
  calc
    _ ≤ ∑ w ∈ wSet x V W, (Real.log W)^2/4 := by
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨_, _, ho, _, hwW⟩ := Finset.mem_filter.mp hw
      have hwp : (0 : ℝ) < w := by
        have : w ≠ 0 := by intro he; subst w; norm_num at ho
        exact_mod_cast (Nat.pos_of_ne_zero this)
      have hl := Real.log_le_log hwp hwW
      have hb := SmallQCancellationAux.centered_bound V w
      rw [Theorem51Interface.centered_eq, Complex.norm_real, Real.norm_eq_abs]
      have ha : |SmallQCancellationAux.centered V w| ≤ Real.log W/2 := by linarith
      nlinarith [sq_nonneg (|SmallQCancellationAux.centered V w|-Real.log W/2),
        abs_nonneg (SmallQCancellationAux.centered V w)]
    _ = _ := by simp; ring
-- END EXTRACT Theorem51Dyadic.coefficient_mass

-- BEGIN EXTRACT Theorem51Dyadic.remove_moebius
/-- Removing Mobius decreases the genuine row energy; no row cancellation is assumed. -/
theorem remove_moebius (x alpha U V W : ℝ) :
    (∑ d ∈ dSet x U W, ‖row x alpha V W d‖^2) ≤
      ∑ d ∈ dSet x U W,
        ‖∑ w ∈ wSet x V W, (theorem51Centered V w : ℂ)*
          expCircle (alpha*(d*w))‖^2 := by
  apply Finset.sum_le_sum
  intro d hd
  have hm : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  unfold row
  rw [norm_mul]
  apply pow_le_pow_left₀ (by positivity)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hm
    (norm_nonneg (∑ w ∈ wSet x V W,
      (theorem51Centered V w : ℂ)*expCircle (alpha*(d*w))))
-- END EXTRACT Theorem51Dyadic.remove_moebius

-- BEGIN EXTRACT Theorem51Dyadic.rounded_counts
/-- Absorb the two explicit closed-interval rounding costs, valid already at size 40. -/
theorem rounded_counts (x U V W : ℝ) (hx : 0 ≤ x) (hW : 40 ≤ W)
    (hd : 40 ≤ x/W) :
    ((dSet x U W).card : ℝ) ≤ (1.1/4)*(x/W) ∧
    ((wSet x V W).card : ℝ) ≤ (1.1/4)*W := by
  have hdc := d_card x U W hx (by linarith)
  have hwc := w_card x V W (by linarith)
  have he : x/(4*W) = (x/W)/4 := by ring
  rw [he] at hdc
  constructor <;> linarith
-- END EXTRACT Theorem51Dyadic.rounded_counts

-- BEGIN EXTRACT Theorem51Dyadic.coefficient_mass_quantitative
/-- Quantitative L2 mass including the half-log factor and exact rounding allowance. -/
theorem coefficient_mass_quantitative (x V W : ℝ) (hW : 40 ≤ W) :
    (∑ w ∈ wSet x V W, ‖(theorem51Centered V w : ℂ)‖^2) ≤
      (1.1/16)*W*(Real.log W)^2 := by
  have hc := w_card x V W (by linarith)
  have hw : ((wSet x V W).card : ℝ) ≤ (1.1/4)*W := by linarith
  have hm := coefficient_mass x V W (by linarith)
  have hh := mul_le_mul_of_nonneg_right hw (sq_nonneg (Real.log W))
  linarith
-- END EXTRACT Theorem51Dyadic.coefficient_mass_quantitative

-- BEGIN EXTRACT Theorem51Dyadic.energy_of_operator
/-- Conditional arithmetic interface: any proved raw-row operator constant K transfers
to the actual box energy with the precise (1.1/8)^2 coefficient. This does NOT prove K. -/
theorem energy_of_operator (x alpha U V W K : ℝ) (hx : 0 ≤ x) (hW : 40 ≤ W)
    (hd : 40 ≤ x/W) (hK : 0 ≤ K)
    (hop : (∑ d ∈ dSet x U W,
      ‖∑ w ∈ wSet x V W, (theorem51Centered V w : ℂ)*
        expCircle (alpha*(d*w))‖^2) ≤
      K * ∑ w ∈ wSet x V W, ‖(theorem51Centered V w : ℂ)‖^2) :
    energy x alpha U V W ≤ (1.1/8)^2*K*x*(Real.log W)^2 := by
  have hWp : 0 < W := by linarith
  have hda := (rounded_counts x U V W hx hW hd).1
  have hmc := coefficient_mass_quantitative x V W hW
  have hr := (remove_moebius x alpha U V W).trans hop
  have hr' := hr.trans (mul_le_mul_of_nonneg_left hmc hK)
  unfold energy
  calc
    _ ≤ ((dSet x U W).card : ℝ) * (K*((1.1/16)*W*(Real.log W)^2)) :=
      mul_le_mul_of_nonneg_left hr' (by positivity)
    _ ≤ ((1.1/4)*(x/W)) * (K*((1.1/16)*W*(Real.log W)^2)) :=
      mul_le_mul_of_nonneg_right hda (by positivity)
    _ = _ := by field_simp; ring
-- END EXTRACT Theorem51Dyadic.energy_of_operator
end Theorem51Dyadic
end Package_Theorem51DyadicEnergy

section Package_SmallQEnvelopeAux
set_option autoImplicit false
open MeasureTheory
open SmallQTypeIIAux SmallQCancellationAux
namespace SmallQEnvelopeAux

-- BEGIN EXTRACT SmallQEnvelopeAux.sqrt_add
/-- Subadditivity of the square root on nonnegative inputs. -/
theorem sqrt_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a+b) ≤ Real.sqrt a+Real.sqrt b := by
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
-- END EXTRACT SmallQEnvelopeAux.sqrt_add
end SmallQEnvelopeAux
end Package_SmallQEnvelopeAux

section Package_Theorem51DyadicScalar
set_option autoImplicit false
namespace Theorem51Dyadic

-- BEGIN EXTRACT Theorem51Dyadic.operator_scale_expansion
/-- Expand the sharp squared operator scale without enlarging any coefficient. -/
theorem operator_scale_expansion (x W q : ℝ) (hW : 0 < W) (hq : 0 < q) :
    (W/4+2*q)*(x/(2*W*q)+1)*x = x^2/(8*q)+x*W/4+x^2/W+2*x*q := by
  field_simp
  <;> ring
-- END EXTRACT Theorem51Dyadic.operator_scale_expansion

-- BEGIN EXTRACT Theorem51Dyadic.sqrt_expansion
/-- Exact four-term square-root bound for every nonnegative x and positive W,q. -/
theorem sqrt_expansion (x W q : ℝ) (hx : 0 ≤ x) (hW : 0 < W) (hq : 0 < q) :
    Real.sqrt ((W/4+2*q)*(x/(2*W*q)+1)*x) ≤
      (1/(2*Real.sqrt 2))*(x/Real.sqrt q) + (1/2)*Real.sqrt (x*W) +
        x/Real.sqrt W + Real.sqrt 2*Real.sqrt (x*q) := by
  have h1 : Real.sqrt (x^2/(8*q)) = (1/(2*Real.sqrt 2))*(x/Real.sqrt q) := by
    have h8 : Real.sqrt (8 : ℝ) = 2*Real.sqrt 2 := by
      rw [show (8 : ℝ) = 4*2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    rw [Real.sqrt_div (sq_nonneg x), Real.sqrt_sq hx,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8), h8]
    ring
  have h2 : Real.sqrt (x*W/4) = (1/2)*Real.sqrt (x*W) := by
    rw [Real.sqrt_div (mul_nonneg hx hW.le)]
    norm_num
    <;> ring
  have h3 : Real.sqrt (x^2/W) = x/Real.sqrt W := by
    rw [Real.sqrt_div (sq_nonneg x), Real.sqrt_sq hx]
  have h4 : Real.sqrt (2*x*q) = Real.sqrt 2*Real.sqrt (x*q) := by
    rw [mul_assoc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [operator_scale_expansion x W q hW hq]
  have ha := SmallQEnvelopeAux.sqrt_add (x^2/(8*q)+x*W/4+x^2/W) (2*x*q)
    (by positivity) (by positivity)
  have hb := SmallQEnvelopeAux.sqrt_add (x^2/(8*q)+x*W/4) (x^2/W)
    (by positivity) (by positivity)
  have hc := SmallQEnvelopeAux.sqrt_add (x^2/(8*q)) (x*W/4)
    (by positivity) (by positivity)
  rw [h4] at ha
  rw [h3] at hb
  rw [h1,h2] at hc
  linarith
-- END EXTRACT Theorem51Dyadic.sqrt_expansion
end Theorem51Dyadic
end Package_Theorem51DyadicScalar

section Package_SmallQMajorantAux
set_option autoImplicit false
open scoped BigOperators
open TaoFivePrimes
namespace SmallQMajorantAux

-- BEGIN EXTRACT SmallQMajorantAux.kernel
/-- The actual absolutely convergent Fourier series of a summable integer weight. -/
noncomputable def kernel (g : ℤ → ℝ) (t : ℝ) : ℂ :=
  ∑' n : ℤ, (g n : ℂ)*expCircle (t*(n : ℝ))
-- END EXTRACT SmallQMajorantAux.kernel

-- BEGIN EXTRACT SmallQMajorantAux.character_conj
/-- Conjugation reverses the sign of the literal character. -/
theorem character_conj (t : ℝ) :
    (starRingEnd ℂ) (expCircle t) = expCircle (-t) := by
  unfold expCircle
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring
-- END EXTRACT SmallQMajorantAux.character_conj

-- BEGIN EXTRACT SmallQMajorantAux.character_pair
/-- Products of a character and its conjugate use the exact difference phase. -/
theorem character_pair (s t : ℝ) :
    expCircle s * (starRingEnd ℂ) (expCircle t) = expCircle (s-t) := by
  rw [character_conj, ← SmallQSubdivisionAux.character_add, sub_eq_add_neg]
-- END EXTRACT SmallQMajorantAux.character_pair

-- BEGIN EXTRACT SmallQMajorantAux.twisted_summable
/-- Every twisted weight is summable, not a possibly undefined tsum assigned zero. -/
theorem twisted_summable (g : ℤ → ℝ) (hg : Summable g) (t : ℝ) :
    Summable (fun n : ℤ ↦ (g n : ℂ)*expCircle (t*(n : ℝ))) := by
  apply hg.abs.of_norm_bounded
  intro n
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    SmallQTransferAux.character_norm, mul_one, le_refl]
-- END EXTRACT SmallQMajorantAux.twisted_summable

-- BEGIN EXTRACT SmallQMajorantAux.kernel_zero
/-- The diagonal kernel is precisely the genuine total mass of the integer weight. -/
theorem kernel_zero (g : ℤ → ℝ) : kernel g 0 = (∑' n, g n : ℝ) := by
  simp [kernel, expCircle, ← Complex.ofReal_tsum]
-- END EXTRACT SmallQMajorantAux.kernel_zero

-- BEGIN EXTRACT SmallQMajorantAux.gram_pointwise
/-- Pointwise weighted norm expansion into the exact finite Gram matrix. -/
theorem gram_pointwise (T : Finset ℕ) (theta : ℕ → ℝ) (c : ℕ → ℂ)
    (g : ℤ → ℝ) (n : ℤ) :
    (g n : ℂ) * (‖∑ d ∈ T, c d*expCircle (theta d*(n : ℝ))‖ : ℂ)^2 =
      ∑ d ∈ T, ∑ e ∈ T, (c d * (starRingEnd ℂ) (c e)) *
        ((g n : ℂ)*expCircle ((theta d-theta e)*(n : ℝ))) := by
  rw [← Complex.mul_conj']
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have h := character_pair (theta d*(n : ℝ)) (theta e*(n : ℝ))
  rw [← sub_mul] at h
  rw [← h]
  ring
-- END EXTRACT SmallQMajorantAux.gram_pointwise

-- BEGIN EXTRACT SmallQMajorantAux.weighted_gram
/-- Absolute convergence permits the infinite weight sum to pass through both finite
sample sums. No Poisson formula or orthogonality is assumed in this identity. -/
theorem weighted_gram (T : Finset ℕ) (theta : ℕ → ℝ) (c : ℕ → ℂ)
    (g : ℤ → ℝ) (hg : Summable g) :
    (∑' n : ℤ, (g n : ℂ) * (‖∑ d ∈ T, c d*expCircle (theta d*(n : ℝ))‖ : ℂ)^2) =
      ∑ d ∈ T, ∑ e ∈ T, (c d * (starRingEnd ℂ) (c e)) * kernel g (theta d-theta e) := by
  simp_rw [gram_pointwise]
  have hs (d e : ℕ) := (twisted_summable g hg (theta d-theta e)).mul_left
    (c d*(starRingEnd ℂ) (c e))
  rw [Summable.tsum_finsetSum (fun d hd ↦ summable_sum (fun e he ↦ hs d e))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Summable.tsum_finsetSum (fun e he ↦ hs d e)]
  simp only [tsum_mul_left, kernel]
-- END EXTRACT SmallQMajorantAux.weighted_gram

-- BEGIN EXTRACT SmallQMajorantAux.weighted_square_summable
/-- The real weighted square norm also genuinely converges, by a uniform finite
triangle bound and summability of the nonnegative weight. -/
theorem weighted_square_summable (T : Finset ℕ) (theta : ℕ → ℝ) (c : ℕ → ℂ)
    (g : ℤ → ℝ) (hg : Summable g) (hpos : ∀ n, 0 ≤ g n) :
    Summable (fun n : ℤ ↦ g n * ‖∑ d ∈ T, c d*expCircle (theta d*(n : ℝ))‖^2) := by
  apply Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (hpos n) (sq_nonneg _)) _
    (hg.mul_right ((∑ d ∈ T, ‖c d‖)^2))
  intro n
  apply mul_le_mul_of_nonneg_left _ (hpos n)
  apply pow_le_pow_left₀ (norm_nonneg _)
  calc
    _ ≤ ∑ d ∈ T, ‖c d*expCircle (theta d*(n : ℝ))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, SmallQTransferAux.character_norm, mul_one]
-- END EXTRACT SmallQMajorantAux.weighted_square_summable

-- BEGIN EXTRACT SmallQMajorantAux.weighted_orthogonality
/-- Vanishing off-diagonal kernels give an exact weighted Parseval identity on the
sample vectors, with the actual total mass, not an assumed energy inequality. -/
theorem weighted_orthogonality (T : Finset ℕ) (theta : ℕ → ℝ) (c : ℕ → ℂ)
    (g : ℤ → ℝ) (hg : Summable g)
    (hoff : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → kernel g (theta d-theta e) = 0) :
    (∑' n : ℤ, g n * ‖∑ d ∈ T, c d*expCircle (theta d*(n : ℝ))‖^2) =
      (∑' n, g n) * ∑ d ∈ T, ‖c d‖^2 := by
  have hh := weighted_gram T theta c g hg
  have hr : (∑ d ∈ T, ∑ e ∈ T, (c d*(starRingEnd ℂ) (c e))*kernel g (theta d-theta e)) =
      ((∑' n, g n : ℝ) : ℂ) * ∑ d ∈ T, (‖c d‖ : ℂ)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_eq_single d]
    · simp only [sub_self, kernel_zero, Complex.mul_conj']
      ring
    · intro e he hne
      rw [hoff d hd e he (Ne.symm hne), mul_zero]
    · intro hn
      exact (hn hd).elim
  rw [hr] at hh
  have hc : ((∑' n : ℤ, g n * ‖∑ d ∈ T, c d*expCircle (theta d*(n : ℝ))‖^2) : ℂ) =
      (((∑' n, g n) * ∑ d ∈ T, ‖c d‖^2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_sum] using hh
  exact_mod_cast hc
-- END EXTRACT SmallQMajorantAux.weighted_orthogonality

-- BEGIN EXTRACT SmallQMajorantAux.dual_of_weight
/-- A nonnegative summable majorant of a finite frequency set gives the dual finite
Fourier estimate, by exact weighted orthogonality and monotone partial sums. -/
theorem dual_of_weight (T : Finset ℕ) (J : Finset ℤ) (theta : ℕ → ℝ)
    (g : ℤ → ℝ) (hg : Summable g) (hpos : ∀ n, 0 ≤ g n)
    (hJ : ∀ j ∈ J, 1 ≤ g j)
    (hoff : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → kernel g (theta d-theta e) = 0)
    (c : ℕ → ℂ) :
    (∑ j ∈ J, ‖∑ d ∈ T, c d*expCircle (theta d*(j : ℝ))‖^2) ≤
      (∑' n, g n) * ∑ d ∈ T, ‖c d‖^2 := by
  rw [← weighted_orthogonality T theta c g hg hoff]
  calc
    _ ≤ ∑ j ∈ J, g j * ‖∑ d ∈ T, c d*expCircle (theta d*(j : ℝ))‖^2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact le_mul_of_one_le_left (sq_nonneg _) (hJ j hj)
    _ ≤ _ := Summable.sum_le_tsum J (fun n hn ↦ mul_nonneg (hpos n) (sq_nonneg _))
      (weighted_square_summable T theta c g hg hpos)
-- END EXTRACT SmallQMajorantAux.dual_of_weight

-- BEGIN EXTRACT SmallQMajorantAux.fourier_of_dual
/-- Finite duality for the actual integer-frequency matrix. Arbitrary signed and complex
coefficients are retained, and the zero-energy case requires no division. -/
theorem fourier_of_dual (T : Finset ℕ) (J : Finset ℤ) (theta : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hdual : ∀ c : ℕ → ℂ,
      (∑ j ∈ J, ‖∑ d ∈ T, c d*expCircle (theta d*(j : ℝ))‖^2) ≤
        C * ∑ d ∈ T, ‖c d‖^2) (v : ℤ → ℂ) :
    (∑ d ∈ T, ‖∑ j ∈ J, v j*expCircle (theta d*(j : ℝ))‖^2) ≤
      C * ∑ j ∈ J, ‖v j‖^2 := by
  let f : ℕ → ℂ := fun d ↦ ∑ j ∈ J, v j*expCircle (theta d*(j : ℝ))
  let E : ℝ := ∑ d ∈ T, ‖f d‖^2
  let c : ℕ → ℂ := fun d ↦ (starRingEnd ℂ) (f d)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have heq : (∑ j ∈ J, v j*(∑ d ∈ T, c d*expCircle (theta d*(j : ℝ)))) = (E : ℂ) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ d ∈ T, c d * f d := by
        apply Finset.sum_congr rfl
        intro d hd
        simp only [f, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by simp only [c, Complex.conj_mul', E, Complex.ofReal_sum, Complex.ofReal_pow]
  have ht : E^2 ≤ (∑ j ∈ J, ‖v j‖^2) *
      (∑ j ∈ J, ‖∑ d ∈ T, c d*expCircle (theta d*(j : ℝ))‖^2) := by
    calc
      _ = ‖∑ j ∈ J, v j*(∑ d ∈ T, c d*expCircle (theta d*(j : ℝ)))‖^2 := by
        rw [heq, Complex.norm_of_nonneg hE]
      _ ≤ (∑ j ∈ J, ‖v j‖ * ‖∑ d ∈ T, c d*expCircle (theta d*(j : ℝ))‖)^2 := by
        apply pow_le_pow_left₀ (norm_nonneg _)
        simpa only [norm_mul] using norm_sum_le J
          (fun j ↦ v j*(∑ d ∈ T, c d*expCircle (theta d*(j : ℝ))))
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq J _ _
  have hh := hdual c
  have hc : (∑ d ∈ T, ‖c d‖^2) = E := by simp only [c, Complex.norm_conj, E]
  rw [hc] at hh
  have hb := ht.trans (mul_le_mul_of_nonneg_left hh
    (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))
  change E ≤ C * ∑ j ∈ J, ‖v j‖^2
  rcases eq_or_lt_of_le hE with hz | hp
  · rw [← hz]
    exact mul_nonneg hC (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  · apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith [hb]
-- END EXTRACT SmallQMajorantAux.fourier_of_dual

-- BEGIN EXTRACT SmallQMajorantAux.fourier_of_weight
/-- The complete summable-weight adapter, with genuine convergence and no new analytic
assumptions disguised as an operator bound. -/
theorem fourier_of_weight (T : Finset ℕ) (J : Finset ℤ) (theta : ℕ → ℝ)
    (g : ℤ → ℝ) (hg : Summable g) (hpos : ∀ n, 0 ≤ g n)
    (hJ : ∀ j ∈ J, 1 ≤ g j)
    (hoff : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → kernel g (theta d-theta e) = 0)
    (v : ℤ → ℂ) :
    (∑ d ∈ T, ‖∑ j ∈ J, v j*expCircle (theta d*(j : ℝ))‖^2) ≤
      (∑' n, g n) * ∑ j ∈ J, ‖v j‖^2 := by
  exact fourier_of_dual T J theta _ (tsum_nonneg hpos)
    (dual_of_weight T J theta g hg hpos hJ hoff) v
-- END EXTRACT SmallQMajorantAux.fourier_of_weight

-- BEGIN EXTRACT SmallQMajorantAux.Majorant
/-- The precise discrete Selberg certificate: a nonnegative summable majorant of all
integer points in the closed real interval, with sharp mass and vanishing Fourier
series at every phase at distance at least delta from every integer.
This is a property of an actual scalar weight, not a Fourier operator inequality. -/
def Majorant (A B delta : ℝ) (g : ℤ → ℝ) : Prop :=
  Summable g ∧ (∀ n, 0 ≤ g n) ∧
  (∀ n : ℤ, A ≤ (n : ℝ) → (n : ℝ) ≤ B → 1 ≤ g n) ∧
  (∑' n, g n) ≤ B-A+1/delta ∧
  (∀ t : ℝ, (∀ k : ℤ, delta ≤ |t-k|) → kernel g t = 0)
-- END EXTRACT SmallQMajorantAux.Majorant

-- BEGIN EXTRACT SmallQMajorantAux.fourier_of_majorant
/-- A genuine discrete Selberg certificate implies exactly the original finite Fourier
bound, including negative integer frequencies and closed separation endpoints. -/
theorem fourier_of_majorant (T : Finset ℕ) (J : Finset ℤ) (theta : ℕ → ℝ)
    (A B delta : ℝ) (g : ℤ → ℝ) (hm : Majorant A B delta g)
    (hJ : ∀ j ∈ J, A ≤ (j : ℝ) ∧ (j : ℝ) ≤ B)
    (hg : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → ∀ k : ℤ, delta ≤ |theta d-theta e-k|)
    (v : ℤ → ℂ) :
    (∑ d ∈ T, ‖∑ j ∈ J, v j*expCircle (theta d*(j : ℝ))‖^2) ≤
      (B-A+1/delta) * ∑ j ∈ J, ‖v j‖^2 := by
  obtain ⟨hs, hp, hmaj, hmass, hzero⟩ := hm
  exact (fourier_of_weight T J theta g hs hp
    (fun j hj ↦ hmaj j (hJ j hj).1 (hJ j hj).2)
    (fun d hd e he hne ↦ hzero (theta d-theta e) (hg d hd e he hne)) v).trans
      (mul_le_mul_of_nonneg_right hmass (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))
-- END EXTRACT SmallQMajorantAux.fourier_of_majorant
end SmallQMajorantAux
end Package_SmallQMajorantAux

section Package_SmallQPoissonAux
set_option autoImplicit false
open scoped BigOperators FourierTransform
open MeasureTheory Filter Asymptotics TaoFivePrimes
namespace SmallQPoissonAux

-- BEGIN EXTRACT SmallQPoissonAux.modulate
/-- Positive-sign modulation agrees with the character used by the mission. -/
noncomputable def modulate (f : ℝ → ℂ) (t : ℝ) (x : ℝ) : ℂ :=
  f x * expCircle (t*x)
-- END EXTRACT SmallQPoissonAux.modulate

-- BEGIN EXTRACT SmallQPoissonAux.fourier_modulate
/-- The exact Fourier normalization shifts frequency by minus the modulation. -/
theorem fourier_modulate (f : ℝ → ℂ) (t u : ℝ) :
    𝓕 (modulate f t) u = 𝓕 f (u-t) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  unfold modulate expCircle
  rw [mul_comm (f x), ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring
-- END EXTRACT SmallQPoissonAux.fourier_modulate

-- BEGIN EXTRACT SmallQPoissonAux.norm_modulate
/-- Modulation has exactly unit absolute value, so it preserves decay and L1. -/
theorem norm_modulate (f : ℝ → ℂ) (t x : ℝ) : ‖modulate f t x‖ = ‖f x‖ := by
  simp [modulate, norm_mul, SmallQTransferAux.character_norm]
-- END EXTRACT SmallQPoissonAux.norm_modulate

-- BEGIN EXTRACT SmallQPoissonAux.continuous_modulate
/-- Continuity is checked for the literal exponential, not assumed for a formal phase. -/
theorem continuous_modulate {f : ℝ → ℂ} (hf : Continuous f) (t : ℝ) :
    Continuous (modulate f t) := by
  unfold modulate expCircle
  fun_prop
-- END EXTRACT SmallQPoissonAux.continuous_modulate

-- BEGIN EXTRACT SmallQPoissonAux.samples_summable
/-- Polynomial decay implies genuine absolute summability of integer samples. -/
theorem samples_summable {f : ℝ → ℂ} {b : ℝ} (hb : 1 < b)
    (hf : f =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-b))) :
    Summable (fun n : ℤ ↦ f n) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow hb)
    (hf.comp_tendsto Int.tendsto_coe_cofinite)
-- END EXTRACT SmallQPoissonAux.samples_summable

-- BEGIN EXTRACT SmallQPoissonAux.decay_modulate
/-- The decay condition survives every signed real modulation with the same exponent. -/
theorem decay_modulate {f : ℝ → ℂ} {b : ℝ}
    (hf : f =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-b))) (t : ℝ) :
    modulate f t =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-b)) := by
  apply (isBigO_of_le (cocompact ℝ) (fun x ↦ ?_)).trans hf
  simp [norm_modulate]
-- END EXTRACT SmallQPoissonAux.decay_modulate

-- BEGIN EXTRACT SmallQPoissonAux.local_uniform_summable
/-- Decay really supplies the compact-uniform norm summability required by Poisson. -/
theorem local_uniform_summable {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : f =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-b)))
    (K : TopologicalSpace.Compacts ℝ) :
    Summable (fun n : ℤ ↦ ‖ContinuousMap.restrict (K : Set ℝ)
      ((⟨f, hc⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight (n : ℝ)))‖) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow hb)
    ((isBigO_norm_restrict_cocompact ⟨f, hc⟩ (by linarith) hf K).comp_tendsto
      Int.tendsto_coe_cofinite)
-- END EXTRACT SmallQPoissonAux.local_uniform_summable

-- BEGIN EXTRACT SmallQPoissonAux.poisson_zero
/-- Poisson at the origin, retaining its actual Fourier transform and convergence input. -/
theorem poisson_zero {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : f =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-b)))
    (hF : Summable (fun n : ℤ ↦ 𝓕 f n)) :
    (∑' n : ℤ, f n) = ∑' n : ℤ, 𝓕 f n := by
  simpa using Real.tsum_eq_tsum_fourier (local_uniform_summable hc hb hf) hF 0
-- END EXTRACT SmallQPoissonAux.poisson_zero

-- BEGIN EXTRACT SmallQPoissonAux.integer_spectrum_zero
/-- Closed bandlimit at most one kills every nonzero integral Fourier sample. -/
theorem integer_spectrum_zero {f : ℝ → ℂ} {delta : ℝ} (hu : delta ≤ 1)
    (hF : ∀ t : ℝ, delta ≤ |t| → 𝓕 f t = 0) (n : ℤ) (hn : n ≠ 0) :
    𝓕 f n = 0 := by
  apply hF
  have hni : (1 : ℤ) ≤ |n| := by
    have ha := abs_pos.mpr hn
    omega
  have hnr : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hni
  exact hu.trans hnr
-- END EXTRACT SmallQPoissonAux.integer_spectrum_zero

-- BEGIN EXTRACT SmallQPoissonAux.sample_mass
/-- The sum of actual integer samples equals the actual integral under a closed bandlimit.
This is the mass identity, not an assumed normalization of a discrete certificate. -/
theorem sample_mass {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : f =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-b))) {delta : ℝ} (hu : delta ≤ 1)
    (hF : ∀ t : ℝ, delta ≤ |t| → 𝓕 f t = 0) :
    (∑' n : ℤ, f n) = ∫ x : ℝ, f x := by
  have hz := integer_spectrum_zero hu hF
  have hs : Summable (fun n : ℤ ↦ 𝓕 f n) := by
    apply summable_of_hasFiniteSupport
    apply Set.finite_singleton (0 : ℤ) |>.subset
    intro n hn
    by_contra h
    exact hn (hz n (by simpa using h))
  rw [poisson_zero hc hb hf hs, tsum_eq_single 0 (fun n hn ↦ hz n hn)]
  simp [Real.fourier_real_eq_integral_exp_smul]
-- END EXTRACT SmallQPoissonAux.sample_mass

-- BEGIN EXTRACT SmallQPoissonAux.modulated_spectrum_zero
/-- Off-arc separation kills every Fourier sample of the genuinely modulated function,
including equality at either closed support boundary. -/
theorem modulated_spectrum_zero {f : ℝ → ℂ} {delta t : ℝ}
    (hF : ∀ u : ℝ, delta ≤ |u| → 𝓕 f u = 0)
    (ht : ∀ k : ℤ, delta ≤ |t-k|) (n : ℤ) :
    𝓕 (modulate f t) n = 0 := by
  rw [fourier_modulate]
  apply hF
  simpa only [abs_sub_comm] using ht n
-- END EXTRACT SmallQPoissonAux.modulated_spectrum_zero

-- BEGIN EXTRACT SmallQPoissonAux.sampled_kernel_zero
/-- Poisson gives exact off-arc vanishing of the absolutely convergent sampled kernel. -/
theorem sampled_kernel_zero {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : f =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-b))) {delta t : ℝ}
    (hF : ∀ u : ℝ, delta ≤ |u| → 𝓕 f u = 0)
    (ht : ∀ k : ℤ, delta ≤ |t-k|) :
    (∑' n : ℤ, f n * expCircle (t*n)) = 0 := by
  have hz := modulated_spectrum_zero hF ht
  have hs : Summable (fun n : ℤ ↦ 𝓕 (modulate f t) n) := by
    simpa only [hz] using (summable_zero : Summable (fun _ : ℤ ↦ (0 : ℂ)))
  have hp := poisson_zero (continuous_modulate hc t) hb (decay_modulate hf t) hs
  simpa only [modulate, hz, tsum_zero] using hp
-- END EXTRACT SmallQPoissonAux.sampled_kernel_zero

-- BEGIN EXTRACT SmallQPoissonAux.real_samples_summable
/-- Real samples inherit absolute summability from actual polynomial decay. -/
theorem real_samples_summable {f : ℝ → ℝ} {b : ℝ} (hb : 1 < b)
    (hf : (fun x ↦ (f x : ℂ)) =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-b))) :
    Summable (fun n : ℤ ↦ f n) :=
  Complex.summable_ofReal.mp (samples_summable hb hf)
-- END EXTRACT SmallQPoissonAux.real_samples_summable

-- BEGIN EXTRACT SmallQPoissonAux.real_sample_mass
/-- Real sample mass uses Lebesgue integration and the exact real-to-complex cast. -/
theorem real_sample_mass {f : ℝ → ℝ} (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : (fun x ↦ (f x : ℂ)) =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-b)))
    {delta : ℝ} (hu : delta ≤ 1)
    (hF : ∀ t : ℝ, delta ≤ |t| → 𝓕 (fun x ↦ (f x : ℂ)) t = 0) :
    (∑' n : ℤ, f n) = ∫ x : ℝ, f x := by
  have hh := sample_mass (Complex.continuous_ofReal.comp hc) hb hf hu hF
  simp only [Function.comp_def] at hh
  rw [← Complex.ofReal_tsum, integral_complex_ofReal] at hh
  exact Complex.ofReal_injective hh
-- END EXTRACT SmallQPoissonAux.real_sample_mass

-- BEGIN EXTRACT SmallQPoissonAux.ContinuousMajorant
/-- A continuous interval majorant with sharp actual integral, integrability, quadratic
rather than Schwartz decay, and closed Fourier support. These are continuous analytic
properties; neither integer samples nor an operator estimate occur in this definition. -/
def ContinuousMajorant (A B delta : ℝ) (f : ℝ → ℝ) : Prop :=
  Continuous f ∧ Integrable f ∧
  ((fun x ↦ (f x : ℂ)) =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-(2 : ℝ)))) ∧
  (∀ x : ℝ, 0 ≤ f x) ∧ (∀ x : ℝ, A ≤ x → x ≤ B → 1 ≤ f x) ∧
  (∫ x : ℝ, f x) = B-A+1/delta ∧
  (∀ t : ℝ, delta ≤ |t| → 𝓕 (fun x ↦ (f x : ℂ)) t = 0)
-- END EXTRACT SmallQPoissonAux.ContinuousMajorant

-- BEGIN EXTRACT SmallQPoissonAux.discrete_of_continuous
/-- Genuine Poisson sampling converts the continuous data into the precise discrete
certificate, retaining sharp mass, negative integers and both closed band edges. -/
theorem discrete_of_continuous {A B delta : ℝ} {f : ℝ → ℝ} (hu : delta ≤ 1)
    (hf : ContinuousMajorant A B delta f) :
    SmallQMajorantAux.Majorant A B delta (fun n ↦ f n) := by
  obtain ⟨hc, hi, hd, hp, hm, hmass, hF⟩ := hf
  refine ⟨real_samples_summable (by norm_num : (1 : ℝ) < 2) hd,
    (fun n ↦ hp n), (fun n hn hn' ↦ hm n hn hn'), ?_, ?_⟩
  · rw [real_sample_mass hc (by norm_num : (1 : ℝ) < 2) hd hu hF, hmass]
  · intro t ht
    exact sampled_kernel_zero (Complex.continuous_ofReal.comp hc)
      (by norm_num : (1 : ℝ) < 2) hd hF ht
-- END EXTRACT SmallQPoissonAux.discrete_of_continuous
end SmallQPoissonAux
end Package_SmallQPoissonAux

section Package_SmallQSincAux
set_option autoImplicit false
open MeasureTheory Filter Asymptotics
open scoped FourierTransform
namespace SmallQSincAux

-- BEGIN EXTRACT SmallQSincAux.profile
/-- The literal real sinc-squared profile with arbitrary signed center. -/
noncomputable def profile (d m x : ℝ) : ℝ := Real.sinc (Real.pi*d*(x-m))^2
-- END EXTRACT SmallQSincAux.profile

-- BEGIN EXTRACT SmallQSincAux.profile_continuous
theorem profile_continuous (d m : ℝ) : Continuous (profile d m) := by
  unfold profile
  exact (Real.continuous_sinc.comp (by fun_prop)).pow 2
-- END EXTRACT SmallQSincAux.profile_continuous

-- BEGIN EXTRACT SmallQSincAux.profile_nonneg
theorem profile_nonneg (d m x : ℝ) : 0 ≤ profile d m x := sq_nonneg _
-- END EXTRACT SmallQSincAux.profile_nonneg

-- BEGIN EXTRACT SmallQSincAux.sinc_sq_le_one
theorem sinc_sq_le_one (x : ℝ) : Real.sinc x ^ 2 ≤ 1 := by
  have h := Real.abs_sinc_le_one x
  have hh := abs_le.mp h
  nlinarith
-- END EXTRACT SmallQSincAux.sinc_sq_le_one

-- BEGIN EXTRACT SmallQSincAux.sinc_sq_le_inv_sq
/-- A genuine pointwise tail bound, derived from the bounded numerator. -/
theorem sinc_sq_le_inv_sq {x : ℝ} (hx : x ≠ 0) :
    Real.sinc x ^ 2 ≤ (x^2)⁻¹ := by
  rw [Real.sinc_of_ne_zero hx, div_pow]
  have h : Real.sin x ^ 2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.cos x)]
  simpa only [one_div] using (div_le_div_of_nonneg_right h (sq_nonneg x))
-- END EXTRACT SmallQSincAux.sinc_sq_le_inv_sq

-- BEGIN EXTRACT SmallQSincAux.sinc_sq_envelope
/-- A global integrable envelope includes the removable singularity at the origin. -/
theorem sinc_sq_envelope (x : ℝ) : Real.sinc x ^ 2 ≤ 2*(1+x^2)⁻¹ := by
  have hx : 0 < 1+x^2 := by positivity
  apply (le_mul_inv_iff₀ hx).mpr
  by_cases hz : x = 0
  · subst x; norm_num
  · have h₁ := sinc_sq_le_one x
    have h₂ := sinc_sq_le_inv_sq hz
    have h₃ : Real.sinc x ^ 2 * x^2 ≤ 1 :=
      (le_div_iff₀ (sq_pos_of_ne_zero hz)).mp (by simpa only [one_div] using h₂)
    nlinarith
-- END EXTRACT SmallQSincAux.sinc_sq_envelope

-- BEGIN EXTRACT SmallQSincAux.sinc_sq_integrable
/-- Lebesgue integrability is proved independently of any putative Fourier identity. -/
theorem sinc_sq_integrable : Integrable (fun x : ℝ ↦ Real.sinc x ^ 2) := by
  apply (integrable_inv_one_add_sq.const_mul 2).mono'
    (show AEStronglyMeasurable (fun x : ℝ ↦ Real.sinc x ^ 2) from
      (Real.continuous_sinc.pow 2).aestronglyMeasurable)
  filter_upwards with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.sinc x))]
    using sinc_sq_envelope x
-- END EXTRACT SmallQSincAux.sinc_sq_integrable

-- BEGIN EXTRACT SmallQSincAux.profile_integrable
theorem profile_integrable {d : ℝ} (hd : 0 < d) (m : ℝ) : Integrable (profile d m) := by
  have hi := (integrable_comp_mul_left_iff (fun x : ℝ ↦ Real.sinc x ^ 2)
    (mul_ne_zero Real.pi_ne_zero hd.ne')).mpr sinc_sq_integrable
  unfold profile
  simpa only [← sub_eq_add_neg] using hi.comp_add_right (-m)
-- END EXTRACT SmallQSincAux.profile_integrable

-- BEGIN EXTRACT SmallQSincAux.profile_decay
/-- Actual quadratic cocompact decay, including arbitrary nonzero real translation. -/
theorem profile_decay {d : ℝ} (hd : 0 < d) (m : ℝ) :
    (fun x ↦ (profile d m x : ℂ)) =O[cocompact ℝ]
      (fun x : ℝ ↦ |x| ^ (-(2 : ℝ))) := by
  apply isBigO_iff.mpr
  refine ⟨4/(Real.pi*d)^2, ?_⟩
  have hev : ∀ᶠ x : ℝ in cocompact ℝ, 2*|m|+1 ≤ |x| :=
    tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (2*|m|+1))
  filter_upwards [hev] with x hx
  have hxpos : 0 < |x| := by linarith [abs_nonneg m]
  have htri : |x| ≤ |x-m|+|m| := by
    simpa using abs_add_le (x-m) m
  have hxm : 0 < |x-m| := by linarith
  have hxmn : x-m ≠ 0 := abs_pos.mp hxm
  have hp := mul_pos Real.pi_pos hd
  have ht := sinc_sq_le_inv_sq (mul_ne_zero hp.ne' hxmn)
  have hsq : |x|^2 ≤ 4*(x-m)^2 := by
    have h : |x| ≤ 2*|x-m| := by linarith
    nlinarith [sq_abs (x-m)]
  have htail : profile d m x ≤ (4/(Real.pi*d)^2) * (|x|^2)⁻¹ := by
    apply ht.trans
    rw [mul_pow]
    have ha : 0 < (Real.pi*d)^2 := sq_pos_of_pos hp
    have hb : 0 < (x-m)^2 := sq_pos_of_ne_zero hxmn
    have hc : 0 < |x|^2 := sq_pos_of_pos hxpos
    have he : (4/(Real.pi*d)^2) * (|x|^2)⁻¹ =
        4 / ((Real.pi*d)^2 * |x|^2) := by ring
    rw [he, inv_eq_one_div]
    apply (div_le_div_iff₀ (mul_pos ha hb) (mul_pos ha hc)).mpr
    nlinarith
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (profile_nonneg d m x), Real.rpow_neg (abs_nonneg x),
    Real.rpow_two, abs_inv, abs_pow, abs_abs] using htail
-- END EXTRACT SmallQSincAux.profile_decay
end SmallQSincAux
end Package_SmallQSincAux

section Package_CutoffBridgePlancherelReuse
set_option maxHeartbeats 800000
open MeasureTheory intervalIntegral
open scoped FourierTransform ContDiff
namespace TaoFivePrimes.CutoffBridgePlancherelReuse

-- BEGIN EXTRACT TaoFivePrimes.CutoffBridgePlancherelReuse.fourierIntegral_ae_eq_fourierL2
lemma fourierIntegral_ae_eq_fourierL2
    {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    FourierTransform.fourier f =ᵐ[volume]
      ((FourierTransform.fourier hf2.toLp : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
  let F : ℝ → ℂ := FourierTransform.fourier f
  let G : ℝ → ℂ :=
    ((FourierTransform.fourier hf2.toLp : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
  have hFcont : Continuous F := by
    dsimp [F]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf1
  have hFloc : LocallyIntegrable F := hFcont.locallyIntegrable
  have hGloc : LocallyIntegrable G := by
    exact (Lp.memLp
      (FourierTransform.fourier hf2.toLp : Lp ℂ 2 (volume : Measure ℝ))).locallyIntegrable
      (by norm_num)
  apply ae_eq_of_integral_contDiff_smul_eq hFloc hGloc
  intro g hgdiff hgsupp
  let gc : ℝ → ℂ := fun x ↦ (g x : ℂ)
  have hgc_supp : HasCompactSupport gc := by
    have h := hgsupp.comp_left
      (g := fun r : ℝ ↦ (r : ℂ)) (by simp)
    simpa [gc, Function.comp_def] using h
  have hgc_diff : ContDiff ℝ ∞ gc := by
    dsimp [gc]
    exact Complex.ofRealCLM.contDiff.comp hgdiff
  let gs : SchwartzMap ℝ ℂ := hgc_supp.toSchwartzMap hgc_diff
  have hfourier_f (u : ℝ) :
      FourierTransform.fourier f u =
        VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f u := rfl
  have hfourier_gs (u : ℝ) :
      FourierTransform.fourier gs u =
        VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) gs u := rfl
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    exact real_inner_comm u v
  have hswap :
      (∫ ξ : ℝ, (FourierTransform.fourier f ξ) • (gs ξ)) =
        ∫ x : ℝ, (f x) • (FourierTransform.fourier gs x) := by
    simpa only [hfourier_f, hfourier_gs, hflip] using
      (VectorFourier.integral_fourierIntegral_smul_eq_flip
        (e := Real.fourierChar) (L := innerₗ ℝ) (μ := volume) (ν := volume)
        Real.continuous_fourierChar continuous_inner hf1 gs.integrable)
  have hdistr := MeasureTheory.Lp.fourier_toTemperedDistribution_eq hf2.toLp
  have hdistr_apply := congrArg (fun T : TemperedDistribution ℝ ℂ ↦ T gs) hdistr
  simp only [TemperedDistribution.fourier_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply] at hdistr_apply
  calc
    (∫ x : ℝ, g x • F x) = ∫ x : ℝ, (F x) • gs x := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp [F, gs, gc, mul_comm]
    _ = ∫ x : ℝ, f x • (FourierTransform.fourier gs x) := hswap
    _ = ∫ x : ℝ, (FourierTransform.fourier gs x) • f x := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp [mul_comm]
    _ = ∫ x : ℝ, (FourierTransform.fourier gs x) •
          ((hf2.toLp f : Lp ℂ 2 (volume : Measure ℝ)) x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x : ℝ, gs x • G x := hdistr_apply
    _ = ∫ x : ℝ, g x • G x := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp [G, gs, gc]
-- END EXTRACT TaoFivePrimes.CutoffBridgePlancherelReuse.fourierIntegral_ae_eq_fourierL2

-- BEGIN EXTRACT TaoFivePrimes.CutoffBridgePlancherelReuse.integral_norm_sq_eq_norm_toLp_sq
lemma integral_norm_sq_eq_norm_toLp_sq
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫ x : ℝ, ‖f x‖ ^ 2) = ‖hf.toLp f‖ ^ 2 := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := hf.toLp f
  have hinner := congrArg RCLike.re
    (@MeasureTheory.L2.inner_def ℝ ℂ ℂ _ _ _ _ _ F F)
  rw [← integral_re] at hinner
  · simp only [← norm_sq_eq_re_inner] at hinner
    calc
      (∫ x : ℝ, ‖f x‖ ^ 2) = ∫ x : ℝ, ‖F x‖ ^ 2 := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hf.coeFn_toLp] with x hx
        rw [hx]
      _ = ‖F‖ ^ 2 := hinner.symm
      _ = ‖hf.toLp f‖ ^ 2 := rfl
  · exact MeasureTheory.L2.integrable_inner F F
-- END EXTRACT TaoFivePrimes.CutoffBridgePlancherelReuse.integral_norm_sq_eq_norm_toLp_sq

-- BEGIN EXTRACT TaoFivePrimes.CutoffBridgePlancherelReuse.integral_norm_sq_fourier_eq
lemma integral_norm_sq_fourier_eq
    {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (∫ u : ℝ, ‖FourierTransform.fourier f u‖ ^ 2) =
      ∫ t : ℝ, ‖f t‖ ^ 2 := by
  let FL2 : Lp ℂ 2 (volume : Measure ℝ) := FourierTransform.fourier hf2.toLp
  have hae := fourierIntegral_ae_eq_fourierL2 hf1 hf2
  have hF2 : MemLp (FourierTransform.fourier f) 2 := by
    exact (memLp_congr_ae hae).2 (Lp.memLp FL2)
  have hto : hF2.toLp (FourierTransform.fourier f) = FL2 := by
    simpa [FL2] using
      (MemLp.toLp_eq_toLp_iff hF2 (Lp.memLp FL2)).2 hae
  calc
    (∫ u : ℝ, ‖FourierTransform.fourier f u‖ ^ 2) =
        ‖hF2.toLp (FourierTransform.fourier f)‖ ^ 2 :=
      integral_norm_sq_eq_norm_toLp_sq hF2
    _ = ‖FL2‖ ^ 2 := by rw [hto]
    _ = ‖hf2.toLp f‖ ^ 2 := by
      dsimp [FL2]
      rw [MeasureTheory.Lp.norm_fourier_eq]
    _ = ∫ t : ℝ, ‖f t‖ ^ 2 :=
      (integral_norm_sq_eq_norm_toLp_sq hf2).symm
-- END EXTRACT TaoFivePrimes.CutoffBridgePlancherelReuse.integral_norm_sq_fourier_eq
end TaoFivePrimes.CutoffBridgePlancherelReuse
end Package_CutoffBridgePlancherelReuse

section Package_SmallQSincFourier
set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform
open SmallQSincAux TaoFivePrimes.CutoffBridgePlancherelReuse
namespace SmallQSincFourier

-- BEGIN EXTRACT SmallQSincFourier.box
/-- Literal centered frequency box, including its null endpoints. -/
noncomputable def box (d x : ℝ) : ℂ := (Set.Icc (-d/2) (d/2)).indicator (fun _ ↦ 1) x
-- END EXTRACT SmallQSincFourier.box

-- BEGIN EXTRACT SmallQSincFourier.box_memLp
theorem box_memLp (d : ℝ) (p : ENNReal) : MemLp (box d) p := by
  exact memLp_indicator_const p measurableSet_Icc 1 (Or.inr (by simp [Real.volume_Icc]))
-- END EXTRACT SmallQSincFourier.box_memLp

-- BEGIN EXTRACT SmallQSincFourier.box_integrable
theorem box_integrable (d : ℝ) : Integrable (box d) := by
  exact memLp_one_iff_integrable.mp (box_memLp d 1)
-- END EXTRACT SmallQSincFourier.box_integrable

-- BEGIN EXTRACT SmallQSincFourier.box_fourier
/-- Actual Fourier transform, with every pi and factor of two checked in the integral. -/
theorem box_fourier {d : ℝ} (hd : 0 ≤ d) (u : ℝ) :
    𝓕 (box d) u = (d : ℂ) * Real.sinc (Real.pi*d*u) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he : (fun v : ℝ ↦ Complex.exp ((-2*Real.pi*v*u : ℝ)*Complex.I) • box d v) =
      (Set.Icc (-d/2) (d/2)).indicator
        (fun v : ℝ ↦ Complex.exp ((-2*Real.pi*v*u : ℝ)*Complex.I)) := by
    funext v
    by_cases hv : v ∈ Set.Icc (-d/2) (d/2)
    · simp [box, Set.indicator_of_mem hv]
    · simp [box, Set.indicator_of_notMem hv]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -d/2 ≤ d/2)]
  by_cases hu : u = 0
  · subst u
    simp [show d/2- -d/2 = d by ring]
  · let c := -2*Real.pi*u
    have hc : c ≠ 0 := by dsimp [c]; exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hu
    have hfun : (fun v : ℝ ↦ Complex.exp ((-2*Real.pi*v*u : ℝ)*Complex.I)) =
        (fun v : ℝ ↦ Complex.exp (((c*v : ℝ) : ℂ)*Complex.I)) := by
      funext v; congr 2; congr 1; dsimp [c]; ring
    rw [hfun, intervalIntegral.integral_comp_mul_left
      (fun y : ℝ ↦ Complex.exp ((y : ℂ)*Complex.I)) hc]
    have hl : c*(-d/2) = -(c*d/2) := by ring
    have hr : c*(d/2) = c*d/2 := by ring
    rw [hl, hr, integral_exp_mul_I_eq_sinc]
    have hs : c*d/2 = -(Real.pi*d*u) := by dsimp [c]; ring
    rw [hs, Real.sinc_neg]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_neg,
      Complex.ofReal_mul]
    have hcn : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have hrel : (c : ℂ) = -2*Real.pi*(u : ℂ) := by dsimp [c]; push_cast; ring
    field_simp
    rw [hrel]
    ring
-- END EXTRACT SmallQSincFourier.box_fourier

-- BEGIN EXTRACT SmallQSincFourier.box_fourier_norm
/-- The actual squared Fourier norm is the scaled sinc-squared kernel. -/
theorem box_fourier_norm {d : ℝ} (hd : 0 ≤ d) (u : ℝ) :
    ‖𝓕 (box d) u‖^2 = d^2 * profile d 0 u := by
  rw [box_fourier hd, norm_mul, Complex.norm_real, Complex.norm_real]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs, profile, sub_zero]
-- END EXTRACT SmallQSincFourier.box_fourier_norm

-- BEGIN EXTRACT SmallQSincFourier.box_norm_mass
theorem box_norm_mass {d : ℝ} (hd : 0 ≤ d) :
    (∫ x : ℝ, ‖box d x‖^2) = d := by
  have he : (fun x : ℝ ↦ ‖box d x‖^2) =
      (Set.Icc (-d/2) (d/2)).indicator (fun _ : ℝ ↦ (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-d/2) (d/2)
    · simp [box, Set.indicator_of_mem hx]
    · simp [box, Set.indicator_of_notMem hx]
  rw [he, integral_indicator_const 1 measurableSet_Icc]
  simp [Measure.real, Real.volume_Icc, show d/2- -d/2 = d by ring, hd]
-- END EXTRACT SmallQSincFourier.box_norm_mass

-- BEGIN EXTRACT SmallQSincFourier.profile_integral_zero
/-- Exact nonzero Lebesgue mass comes from genuine L2 Plancherel, not an axiom or sample sum. -/
theorem profile_integral_zero {d : ℝ} (hd : 0 < d) :
    (∫ x : ℝ, profile d 0 x) = 1/d := by
  have h := integral_norm_sq_fourier_eq (box_integrable d) (box_memLp d 2)
  simp_rw [box_fourier_norm hd.le] at h
  rw [integral_const_mul, box_norm_mass hd.le] at h
  apply (eq_div_iff hd.ne').mpr
  nlinarith [h]
-- END EXTRACT SmallQSincFourier.profile_integral_zero

-- BEGIN EXTRACT SmallQSincFourier.profile_integral
theorem profile_integral {d : ℝ} (hd : 0 < d) (m : ℝ) :
    (∫ x : ℝ, profile d m x) = 1/d := by
  have he := integral_add_right_eq_self (μ := volume) (profile d 0) (-m)
  simpa only [profile, sub_zero, ← sub_eq_add_neg] using he.trans (profile_integral_zero hd)
-- END EXTRACT SmallQSincFourier.profile_integral
end SmallQSincFourier
end Package_SmallQSincFourier

section Package_SmallQSincSpectrum
set_option autoImplicit false
open MeasureTheory TaoFivePrimes
open scoped FourierTransform
open SmallQSincAux SmallQSincFourier TaoFivePrimes.CutoffBridgePlancherelReuse
namespace SmallQSincSpectrum

-- BEGIN EXTRACT SmallQSincSpectrum.inner_fourier_integral
/-- The already verified L1/L2 comparison transfers the actual sesquilinear integral. -/
theorem inner_fourier_integral {f g : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) (hg : Integrable g) (hg2 : MemLp g 2) :
    (∫ x : ℝ, inner ℂ (𝓕 f x) (𝓕 g x)) = ∫ x : ℝ, inner ℂ (f x) (g x) := by
  have ha := fourierIntegral_ae_eq_fourierL2 hf hf2
  have hb := fourierIntegral_ae_eq_fourierL2 hg hg2
  calc
    (∫ x : ℝ, inner ℂ (𝓕 f x) (𝓕 g x)) =
        ∫ x : ℝ, inner ℂ ((𝓕 hf2.toLp : Lp ℂ 2 volume) x)
          ((𝓕 hg2.toLp : Lp ℂ 2 volume) x) := by
      apply integral_congr_ae
      filter_upwards [ha, hb] with x hx hy
      rw [hx, hy]
    _ = inner ℂ (𝓕 hf2.toLp) (𝓕 hg2.toLp) := (L2.inner_def _ _).symm
    _ = inner ℂ hf2.toLp hg2.toLp := Lp.inner_fourier_eq _ _
    _ = ∫ x : ℝ, inner ℂ (f x) (g x) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp, hg2.coeFn_toLp] with x hx hy
      rw [hx, hy]
-- END EXTRACT SmallQSincSpectrum.inner_fourier_integral

-- BEGIN EXTRACT SmallQSincSpectrum.fourier_translate
/-- Exact Fourier translation with the mission's exponential convention. -/
theorem fourier_translate (f : ℝ → ℂ) (t u : ℝ) :
    𝓕 (fun x ↦ f (x-t)) u = expCircle (-t*u) * 𝓕 f u := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ ℝ) f (-t)) u
  change 𝓕 (fun x ↦ f (x+ -t)) u = _ at h
  change 𝓕 (fun x ↦ f (x+ -t)) u =
    Real.fourierChar ((innerₗ ℝ) (-t) u) • 𝓕 f u at h
  simpa [sub_eq_add_neg, Circle.smul_def, Real.fourierChar_apply,
    RCLike.inner_apply, expCircle, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h
-- END EXTRACT SmallQSincSpectrum.fourier_translate

-- BEGIN EXTRACT SmallQSincSpectrum.translated_box_memLp
/-- A translated frequency box remains a genuine L2 function. -/
theorem translated_box_memLp (d t : ℝ) : MemLp (fun x ↦ box d (x-t)) 2 := by
  have h := (box_memLp d 2).comp_measurePreserving (measurePreserving_add_right volume (-t))
  simpa [Function.comp_def, ← sub_eq_add_neg] using h
-- END EXTRACT SmallQSincSpectrum.translated_box_memLp

-- BEGIN EXTRACT SmallQSincSpectrum.box_correlation_zero
/-- Separated closed frequency boxes have zero correlation even at the support boundary. -/
theorem box_correlation_zero {d : ℝ} (hd : 0 < d) {t : ℝ} (ht : d ≤ |t|) :
    (∫ x : ℝ, inner ℂ (box d x) (box d (x-t))) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [volume.ae_ne (-d/2), volume.ae_ne (d/2)] with x hx₁ hx₂
  by_cases hx : x ∈ Set.Icc (-d/2) (d/2)
  · have hnx : x-t ∉ Set.Icc (-d/2) (d/2) := by
      intro hy
      have hxa : -d/2 < x := lt_of_le_of_ne hx.1 (Ne.symm hx₁)
      have hxb : x < d/2 := lt_of_le_of_ne hx.2 hx₂
      rcases le_abs.mp ht with ht | ht <;> linarith [hy.1, hy.2]
    simp [box, Set.indicator_of_notMem hnx]
  · simp [box, Set.indicator_of_notMem hx]
-- END EXTRACT SmallQSincSpectrum.box_correlation_zero

-- BEGIN EXTRACT SmallQSincSpectrum.profile_fourier_correlation
/-- Fourier of the squared box transform is the actual translated-box correlation. -/
theorem profile_fourier_correlation {d : ℝ} (hd : 0 < d) (t : ℝ) :
    (d : ℂ)^2 * 𝓕 (fun x ↦ (profile d 0 x : ℂ)) t =
      ∫ x : ℝ, inner ℂ (box d x) (box d (x-t)) := by
  have h := inner_fourier_integral (box_integrable d) (box_memLp d 2)
    (by simpa only [← sub_eq_add_neg] using (box_integrable d).comp_add_right (-t))
    (translated_box_memLp d t)
  rw [← h, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [fourier_translate, box_fourier hd.le]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal, profile, sub_zero,
    Complex.ofReal_pow, smul_eq_mul, expCircle]
  have he : (-2*Real.pi*x*t : ℝ) = 2*Real.pi*(-t*x) := by ring
  rw [he]
  push_cast
  ring
-- END EXTRACT SmallQSincSpectrum.profile_fourier_correlation

-- BEGIN EXTRACT SmallQSincSpectrum.profile_spectrum_zero
/-- The literal sinc-squared transform vanishes at both closed band edges and beyond. -/
theorem profile_spectrum_zero {d : ℝ} (hd : 0 < d) {t : ℝ} (ht : d ≤ |t|) :
    𝓕 (fun x ↦ (profile d 0 x : ℂ)) t = 0 := by
  have h := profile_fourier_correlation hd t
  rw [box_correlation_zero hd ht] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 (by exact_mod_cast hd.ne'))
-- END EXTRACT SmallQSincSpectrum.profile_spectrum_zero

-- BEGIN EXTRACT SmallQSincSpectrum.translated_profile_spectrum_zero
/-- Arbitrary signed centers preserve closed spectral support with the exact phase. -/
theorem translated_profile_spectrum_zero {d : ℝ} (hd : 0 < d) (m : ℝ)
    {t : ℝ} (ht : d ≤ |t|) :
    𝓕 (fun x ↦ (profile d m x : ℂ)) t = 0 := by
  have he : (fun x ↦ (profile d m x : ℂ)) =
      (fun x ↦ (profile d 0 (x-m) : ℂ)) := by simp [profile]
  rw [he, fourier_translate (fun x ↦ (profile d 0 x : ℂ)) m t,
    profile_spectrum_zero hd ht, mul_zero]
-- END EXTRACT SmallQSincSpectrum.translated_profile_spectrum_zero
end SmallQSincSpectrum
end Package_SmallQSincSpectrum

section Package_SmallQBeurlingAux
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators FourierTransform
open SmallQSincAux SmallQSincFourier SmallQSincSpectrum SmallQPoissonAux
namespace SmallQBeurlingAux

-- BEGIN EXTRACT SmallQBeurlingAux.K
/-- Unit-band sinc square, with its actual value one at zero. -/
noncomputable def K (x : ℝ) : ℝ := Real.sinc (Real.pi*x)^2
-- END EXTRACT SmallQBeurlingAux.K

-- BEGIN EXTRACT SmallQBeurlingAux.positivePart
/-- The positive-integer part of the cardinal interpolation series. -/
noncomputable def positivePart (x : ℝ) : ℝ := ∑' n : ℕ, K (x-(n+1))
-- END EXTRACT SmallQBeurlingAux.positivePart

-- BEGIN EXTRACT SmallQBeurlingAux.H
/-- Beurling's odd sign approximator, not an opaque choice of an extremal function. -/
noncomputable def H (x : ℝ) : ℝ := positivePart x - positivePart (-x) + 2*x*K x
-- END EXTRACT SmallQBeurlingAux.H

-- BEGIN EXTRACT SmallQBeurlingAux.F
/-- Beurling's sign majorant in Montgomery's convention. -/
noncomputable def F (x : ℝ) : ℝ := H x + K x
-- END EXTRACT SmallQBeurlingAux.F

-- BEGIN EXTRACT SmallQBeurlingAux.K_profile
theorem K_profile (x : ℝ) : K x = profile 1 0 x := by simp [K, profile]
-- END EXTRACT SmallQBeurlingAux.K_profile

-- BEGIN EXTRACT SmallQBeurlingAux.K_nonneg
theorem K_nonneg (x : ℝ) : 0 ≤ K x := sq_nonneg _
-- END EXTRACT SmallQBeurlingAux.K_nonneg

-- BEGIN EXTRACT SmallQBeurlingAux.K_zero
theorem K_zero : K 0 = 1 := by simp [K]
-- END EXTRACT SmallQBeurlingAux.K_zero

-- BEGIN EXTRACT SmallQBeurlingAux.K_neg
theorem K_neg (x : ℝ) : K (-x) = K x := by simp [K, mul_neg, Real.sinc_neg]
-- END EXTRACT SmallQBeurlingAux.K_neg

-- BEGIN EXTRACT SmallQBeurlingAux.K_continuous
theorem K_continuous : Continuous K := by
  unfold K
  fun_prop
-- END EXTRACT SmallQBeurlingAux.K_continuous

-- BEGIN EXTRACT SmallQBeurlingAux.shifted_summable
theorem shifted_summable (x : ℝ) : Summable (fun n : ℤ ↦ K (x-n)) := by
  have h := real_samples_summable (by norm_num : (1 : ℝ) < 2)
    (profile_decay (by norm_num : (0 : ℝ) < 1) x)
  convert h using 1
  funext n
  simp only [profile, mul_one, K]
  rw [show Real.pi*(x-n) = -(Real.pi*((n : ℝ)-x)) by ring, Real.sinc_neg]
-- END EXTRACT SmallQBeurlingAux.shifted_summable

-- BEGIN EXTRACT SmallQBeurlingAux.shifted_mass
/-- Exact partition of unity from actual mass and closed spectral support. -/
theorem shifted_mass (x : ℝ) : (∑' n : ℤ, K (x-n)) = 1 := by
  have h := real_sample_mass (profile_continuous 1 x) (by norm_num : (1 : ℝ) < 2)
    (profile_decay (by norm_num : (0 : ℝ) < 1) x) (le_refl (1 : ℝ))
    (fun t ht ↦ translated_profile_spectrum_zero (by norm_num : (0 : ℝ) < 1) x ht)
  rw [profile_integral (by norm_num : (0 : ℝ) < 1)] at h
  convert h using 1
  · apply tsum_congr; intro n
    simp only [profile, mul_one, K]
    rw [show Real.pi*(x-n) = -(Real.pi*((n : ℝ)-x)) by ring, Real.sinc_neg]
  · norm_num
-- END EXTRACT SmallQBeurlingAux.shifted_mass

-- BEGIN EXTRACT SmallQBeurlingAux.nonnegative_part_summable
theorem nonnegative_part_summable (x : ℝ) : Summable (fun n : ℕ ↦ K (x-n)) := by
  exact (summable_int_iff_summable_nat_and_neg.mp (shifted_summable x)).1
-- END EXTRACT SmallQBeurlingAux.nonnegative_part_summable

-- BEGIN EXTRACT SmallQBeurlingAux.positive_part_summable
theorem positive_part_summable (x : ℝ) : Summable (fun n : ℕ ↦ K (x-(n+1))) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).mpr (nonnegative_part_summable x)
-- END EXTRACT SmallQBeurlingAux.positive_part_summable

-- BEGIN EXTRACT SmallQBeurlingAux.negative_part_summable
theorem negative_part_summable (x : ℝ) : Summable (fun n : ℕ ↦ K (x+(n+1))) := by
  convert positive_part_summable (-x) using 1
  funext n
  rw [show -x-((n : ℝ)+1) = -(x+(n+1)) by ring, K_neg]
-- END EXTRACT SmallQBeurlingAux.negative_part_summable

-- BEGIN EXTRACT SmallQBeurlingAux.positivePart_neg
theorem positivePart_neg (x : ℝ) : positivePart (-x) = ∑' n : ℕ, K (x+(n+1)) := by
  unfold positivePart
  apply tsum_congr; intro n
  rw [show -x-((n : ℝ)+1) = -(x+(n+1)) by ring, K_neg]
-- END EXTRACT SmallQBeurlingAux.positivePart_neg

-- BEGIN EXTRACT SmallQBeurlingAux.partition
/-- Positive, negative and zero cardinal masses exactly exhaust one. -/
theorem partition (x : ℝ) : K x + positivePart x + positivePart (-x) = 1 := by
  have hrec : (fun n : ℤ ↦ K (x-n)) =
      Int.rec (fun n : ℕ ↦ K (x-n)) (fun n : ℕ ↦ K (x+(n+1))) := by
    funext n
    cases n <;> simp
    congr 1; ring
  have h := shifted_mass x
  rw [hrec, tsum_int_rec (nonnegative_part_summable x) (negative_part_summable x),
    (nonnegative_part_summable x).tsum_eq_zero_add] at h
  rw [positivePart_neg]
  simpa [positivePart, Nat.cast_add, Nat.cast_one] using h
-- END EXTRACT SmallQBeurlingAux.partition

-- BEGIN EXTRACT SmallQBeurlingAux.H_neg
theorem H_neg (x : ℝ) : H (-x) = -H x := by simp only [H, neg_neg, K_neg]; ring
-- END EXTRACT SmallQBeurlingAux.H_neg

-- BEGIN EXTRACT SmallQBeurlingAux.H_zero
theorem H_zero : H 0 = 0 := by simp [H]
-- END EXTRACT SmallQBeurlingAux.H_zero

-- BEGIN EXTRACT SmallQBeurlingAux.error_identity
/-- For positive x the sign error is an explicit positive-tail expression. -/
theorem error_identity (x : ℝ) : 1-H x = K x + 2*positivePart (-x) - 2*x*K x := by
  have h := partition x
  unfold H
  linarith
-- END EXTRACT SmallQBeurlingAux.error_identity
end SmallQBeurlingAux
end Package_SmallQBeurlingAux

section Package_SmallQBeurlingTail
set_option autoImplicit false
open Filter
open scoped BigOperators
open SmallQBeurlingAux
namespace SmallQBeurlingTail

-- BEGIN EXTRACT SmallQBeurlingTail.step
/-- The elementary positive reciprocal difference used on both sides of the tail. -/
noncomputable def step (x : ℝ) (n : ℕ) : ℝ := 1/(x+n) - 1/(x+n+1)
-- END EXTRACT SmallQBeurlingTail.step

-- BEGIN EXTRACT SmallQBeurlingTail.step_sum
/-- Exact finite telescoping, before taking any infinite sum. -/
theorem step_sum (x : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, step x n) = 1/x - 1/(x+N) := by
  induction N with
  | zero => simp
  | succ N h => rw [Finset.sum_range_succ, h]; simp only [step, Nat.cast_add,
      Nat.cast_one]; ring
-- END EXTRACT SmallQBeurlingTail.step_sum

-- BEGIN EXTRACT SmallQBeurlingTail.step_nonneg
theorem step_nonneg {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 ≤ step x n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  dsimp [step]
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))
-- END EXTRACT SmallQBeurlingTail.step_nonneg

-- BEGIN EXTRACT SmallQBeurlingTail.step_hasSum
/-- A genuine HasSum, obtained from finite telescoping and the real reciprocal limit. -/
theorem step_hasSum {x : ℝ} (hx : 0 < x) : HasSum (step x) (1/x) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (step_nonneg hx)]
  simp only [step_sum]
  have ht : Tendsto (fun N : ℕ ↦ x+(N : ℝ)) atTop atTop := by
    exact tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp ht
  simpa only [Function.comp_def, ← one_div, sub_zero] using
    (tendsto_const_nhds (x := 1/x)).sub hi
-- END EXTRACT SmallQBeurlingTail.step_hasSum

-- BEGIN EXTRACT SmallQBeurlingTail.tail
/-- Literal reciprocal-square tail, excluding n=0. -/
noncomputable def tail (x : ℝ) : ℝ := ∑' n : ℕ, 1/(x+(n+1))^2
-- END EXTRACT SmallQBeurlingTail.tail

-- BEGIN EXTRACT SmallQBeurlingTail.square_le_step
theorem square_le_step {x : ℝ} (hx : 0 < x) (n : ℕ) :
    1/(x+(n+1))^2 ≤ step x n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha : 0 < x+n := by positivity
  have hb : 0 < x+n+1 := by positivity
  dsimp [step]
  rw [show x+((n : ℝ)+1) = x+n+1 by ring]
  field_simp
  nlinarith
-- END EXTRACT SmallQBeurlingTail.square_le_step

-- BEGIN EXTRACT SmallQBeurlingTail.step_le_square
theorem step_le_square {x : ℝ} (hx : 0 < x) (n : ℕ) :
    step (x+1) n ≤ 1/(x+(n+1))^2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha : 0 < x+1+n := by positivity
  have hb : 0 < x+1+n+1 := by positivity
  dsimp [step]
  rw [show x+((n : ℝ)+1) = x+1+n by ring]
  field_simp
  nlinarith
-- END EXTRACT SmallQBeurlingTail.step_le_square

-- BEGIN EXTRACT SmallQBeurlingTail.tail_summable
theorem tail_summable {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ ↦ 1/(x+(n+1))^2) := by
  exact Summable.of_nonneg_of_le (fun n ↦ by positivity) (square_le_step hx)
    (step_hasSum hx).summable
-- END EXTRACT SmallQBeurlingTail.tail_summable

-- BEGIN EXTRACT SmallQBeurlingTail.tail_bounds
/-- The two inequalities needed by Beurling, without replacing a divergent sum by zero. -/
theorem tail_bounds {x : ℝ} (hx : 0 < x) : 1/(x+1) ≤ tail x ∧ tail x ≤ 1/x := by
  constructor
  · have h := Summable.tsum_le_tsum (step_le_square hx)
      (step_hasSum (by linarith : 0 < x+1)).summable (tail_summable hx)
    simpa only [(step_hasSum (by linarith : 0 < x+1)).tsum_eq, tail] using h
  · have h := Summable.tsum_le_tsum (square_le_step hx)
      (tail_summable hx) (step_hasSum hx).summable
    simpa only [(step_hasSum hx).tsum_eq, tail] using h
-- END EXTRACT SmallQBeurlingTail.tail_bounds

-- BEGIN EXTRACT SmallQBeurlingTail.K_add_nat
/-- Shifted sinc squares are the literal reciprocal-square summands, including positive
integer x where the sine numerator vanishes. No division at an integer pole occurs. -/
theorem K_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    K (x+(n+1)) = x^2*K x * (1/(x+(n+1))^2) := by
  have hn : 0 < x+((n : ℝ)+1) := by positivity
  rw [K, K, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hn.ne'),
    Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx.ne')]
  rw [show Real.pi*(x+((n : ℝ)+1)) = Real.pi*x+((n+1 : ℕ) : ℝ)*Real.pi by push_cast; ring,
    Real.sin_add_nat_mul_pi]
  have hs : ((-1 : ℝ)^(n+1))^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm (n+1) 2, pow_mul, neg_one_sq, one_pow]
  rw [div_pow, mul_pow, hs, one_mul]
  push_cast
  field_simp
  <;> ring
-- END EXTRACT SmallQBeurlingTail.K_add_nat

-- BEGIN EXTRACT SmallQBeurlingTail.positivePart_tail
/-- Exact positive-tail reduction of the genuine convergent cardinal series. -/
theorem positivePart_tail {x : ℝ} (hx : 0 < x) :
    positivePart (-x) = x^2*K x*tail x := by
  rw [positivePart_neg]
  simp only [K_add_nat hx, tsum_mul_left, tail]
-- END EXTRACT SmallQBeurlingTail.positivePart_tail

-- BEGIN EXTRACT SmallQBeurlingTail.error_coefficient
/-- The scalar coefficient really lies between minus one and one for every positive x. -/
theorem error_coefficient {x : ℝ} (hx : 0 < x) :
    -1 ≤ 1+2*x^2*tail x-2*x ∧ 1+2*x^2*tail x-2*x ≤ 1 := by
  have hb := tail_bounds hx
  have hu : x*tail x ≤ 1 := by simpa only [mul_comm] using (le_div_iff₀ hx).mp hb.2
  have hl : 1 ≤ tail x*(x+1) := (div_le_iff₀ (by linarith : 0 < x+1)).mp hb.1
  have hleft : (1+2*x^2*tail x-2*x+1)*(x+1) ≥ 0 := by
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ tail x*(x+1)-1 by linarith)]
  constructor
  · nlinarith [mul_pos (show 0 < x+1 by linarith)
      (show 0 < (1 : ℝ) by norm_num)]
  · nlinarith [mul_nonneg hx.le (show 0 ≤ 1-x*tail x by linarith)]
-- END EXTRACT SmallQBeurlingTail.error_coefficient

-- BEGIN EXTRACT SmallQBeurlingTail.error_positive
/-- Sharp sinc-squared error for the explicit Beurling approximator on the positive axis. -/
theorem error_positive {x : ℝ} (hx : 0 < x) : |1-H x| ≤ K x := by
  rw [error_identity, positivePart_tail hx]
  have hc := error_coefficient hx
  have hk := K_nonneg x
  rw [show K x+2*(x^2*K x*tail x)-2*x*K x = K x*(1+2*x^2*tail x-2*x) by ring]
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hk (show 0 ≤ 1+2*x^2*tail x-2*x+1 by linarith),
    mul_nonneg hk (show 0 ≤ 1-(1+2*x^2*tail x-2*x) by linarith)]
-- END EXTRACT SmallQBeurlingTail.error_positive

-- BEGIN EXTRACT SmallQBeurlingTail.sign_error
/-- The full real sign approximation, including zero and every removable integer pole. -/
theorem sign_error (x : ℝ) : |Real.sign x-H x| ≤ K x := by
  rcases lt_trichotomy 0 x with hx | hx | hx
  · simpa only [Real.sign_of_pos hx] using error_positive hx
  · subst x; simp [H_zero, K_zero]
  · have h := error_positive (neg_pos.mpr hx)
    rw [H_neg, K_neg] at h
    rw [Real.sign_of_neg hx, show -1-H x = -(1-H (-x)) by rw [H_neg]; ring,
      abs_neg, H_neg]
    exact h
-- END EXTRACT SmallQBeurlingTail.sign_error

-- BEGIN EXTRACT SmallQBeurlingTail.sign_bracket
/-- Montgomery's majorant sign convention and its matching lower approximant. -/
theorem sign_bracket (x : ℝ) : H x-K x ≤ Real.sign x ∧ Real.sign x ≤ F x := by
  have h := abs_le.mp (sign_error x)
  unfold F
  constructor <;> linarith
-- END EXTRACT SmallQBeurlingTail.sign_bracket
end SmallQBeurlingTail
end Package_SmallQBeurlingTail

section Package_SmallQBeurlingRegularity
set_option autoImplicit false
open MeasureTheory Filter
open SmallQBeurlingAux SmallQBeurlingTail SmallQPoissonAux SmallQSincAux
namespace SmallQBeurlingRegularity

-- BEGIN EXTRACT SmallQBeurlingRegularity.compact_series_bound
/-- The real cardinal series admits a genuinely summable uniform bound on every compact set.
The bound is inherited from the proved compact-uniform decay estimate, not postulated. -/
theorem compact_series_bound (S : TopologicalSpace.Compacts ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ x ∈ (S : Set ℝ), ‖K (x-(n+1))‖ ≤ u n := by
  let f : C(ℝ, ℂ) := ⟨fun x ↦ (K x : ℂ), Complex.continuous_ofReal.comp K_continuous⟩
  let u : ℤ → ℝ := fun n ↦
    ‖ContinuousMap.restrict (S : Set ℝ) (f.comp (ContinuousMap.addRight (n : ℝ)))‖
  have hs : Summable u := by
    apply local_uniform_summable f.continuous (by norm_num : (1 : ℝ) < 2)
    simpa [f, K, profile] using profile_decay (by norm_num : (0 : ℝ) < 1) 0
  let i : ℕ → ℤ := fun n ↦ -((n : ℤ)+1)
  have hi : Function.Injective i := by intro a b h; dsimp [i] at h; omega
  refine ⟨u ∘ i, hs.comp_injective hi, ?_⟩
  intro n x hx
  have hb := ContinuousMap.norm_coe_le_norm
    (ContinuousMap.restrict (S : Set ℝ) (f.comp (ContinuousMap.addRight (i n : ℝ)))) ⟨x,hx⟩
  change ‖(K (x+(i n : ℝ)) : ℂ)‖ ≤ u (i n) at hb
  simpa [i, Function.comp_def, Complex.norm_real, Int.cast_add, Int.cast_neg,
    Int.cast_natCast, sub_eq_add_neg] using hb
-- END EXTRACT SmallQBeurlingRegularity.compact_series_bound

-- BEGIN EXTRACT SmallQBeurlingRegularity.positivePart_continuous
/-- In particular the sum, not just each filled-in summand, is continuous at every pole. -/
theorem positivePart_continuous : Continuous positivePart := by
  rw [continuous_iff_continuousAt]
  intro x
  let S : TopologicalSpace.Compacts ℝ := ⟨Set.Icc (x-1) (x+1), isCompact_Icc⟩
  obtain ⟨u, hu, hb⟩ := compact_series_bound S
  have hc : ContinuousOn positivePart (S : Set ℝ) := by
    exact continuousOn_tsum (fun n ↦ (K_continuous.comp (by fun_prop)).continuousOn) hu hb
  apply hc.continuousAt
  exact Icc_mem_nhds (by linarith) (by linarith)
-- END EXTRACT SmallQBeurlingRegularity.positivePart_continuous

-- BEGIN EXTRACT SmallQBeurlingRegularity.H_continuous
theorem H_continuous : Continuous H := by
  unfold H
  exact (positivePart_continuous.sub (positivePart_continuous.comp continuous_neg)).add
    ((continuous_const.mul continuous_id).mul K_continuous)
-- END EXTRACT SmallQBeurlingRegularity.H_continuous

-- BEGIN EXTRACT SmallQBeurlingRegularity.F_continuous
theorem F_continuous : Continuous F := H_continuous.add K_continuous
-- END EXTRACT SmallQBeurlingRegularity.F_continuous

-- BEGIN EXTRACT SmallQBeurlingRegularity.F_zero
/-- Montgomery's F takes value one at zero; H takes value zero there. -/
theorem F_zero : F 0 = 1 := by simp [F, H_zero, K_zero]
-- END EXTRACT SmallQBeurlingRegularity.F_zero
end SmallQBeurlingRegularity
end Package_SmallQBeurlingRegularity

section Package_SmallQBeurlingModel
set_option autoImplicit false
open MeasureTheory Filter
open SmallQBeurlingAux SmallQBeurlingTail SmallQBeurlingRegularity
namespace SmallQBeurlingModel

-- BEGIN EXTRACT SmallQBeurlingModel.actual_kernel_mass
/-- The sinc mass reused in the pointwise bound is a genuine positive Lebesgue integral. -/
theorem actual_kernel_mass : Integrable K ∧ (∫ x : ℝ, K x) = 1 := by
  have hf := SmallQSincFourier.profile_integral (by norm_num : (0 : ℝ) < 1) 0
  have hi := SmallQSincAux.profile_integrable (by norm_num : (0 : ℝ) < 1) 0
  have he : K = SmallQSincAux.profile 1 0 := funext K_profile
  rw [he]
  exact ⟨hi, by simpa using hf⟩
-- END EXTRACT SmallQBeurlingModel.actual_kernel_mass
end SmallQBeurlingModel
end Package_SmallQBeurlingModel

section Package_SmallQSelbergAux
set_option autoImplicit false
open MeasureTheory Filter Asymptotics
open SmallQBeurlingAux SmallQBeurlingTail SmallQBeurlingRegularity
open SmallQSincAux SmallQSincFourier
namespace SmallQSelbergAux

-- BEGIN EXTRACT SmallQSelbergAux.G
/-- The actual two-endpoint Selberg function, including singleton intervals. -/
noncomputable def G (A B d x : ℝ) : ℝ := (F (d*(x-A))+F (d*(B-x)))/2
-- END EXTRACT SmallQSelbergAux.G

-- BEGIN EXTRACT SmallQSelbergAux.oddError
/-- The odd signed approximation error, used only through a genuinely integrable bound. -/
noncomputable def oddError (x : ℝ) : ℝ := H x - Real.sign x
-- END EXTRACT SmallQSelbergAux.oddError

-- BEGIN EXTRACT SmallQSelbergAux.error
/-- The nonnegative majorant error. Its integral will be exactly one. -/
noncomputable def error (x : ℝ) : ℝ := F x - Real.sign x
-- END EXTRACT SmallQSelbergAux.error

-- BEGIN EXTRACT SmallQSelbergAux.intervalSign
/-- Half the two signs is the interval indicator away from its endpoints. -/
noncomputable def intervalSign (A B x : ℝ) : ℝ :=
  (Real.sign (x-A)+Real.sign (B-x))/2
-- END EXTRACT SmallQSelbergAux.intervalSign

-- BEGIN EXTRACT SmallQSelbergAux.G_continuous
theorem G_continuous (A B d : ℝ) : Continuous (G A B d) := by
  exact ((F_continuous.comp (by fun_prop)).add
    (F_continuous.comp (by fun_prop))).div_const 2
-- END EXTRACT SmallQSelbergAux.G_continuous

-- BEGIN EXTRACT SmallQSelbergAux.sign_scale
theorem sign_scale {d : ℝ} (hd : 0 < d) (x : ℝ) :
    Real.sign (d*x) = Real.sign x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [Real.sign_of_neg hx, Real.sign_of_neg (mul_neg_of_pos_of_neg hd hx)]
  · simp [hx]
  · rw [Real.sign_of_pos hx, Real.sign_of_pos (mul_pos hd hx)]
-- END EXTRACT SmallQSelbergAux.sign_scale

-- BEGIN EXTRACT SmallQSelbergAux.F_ge_one
theorem F_ge_one {x : ℝ} (hx : 0 ≤ x) : 1 ≤ F x := by
  rcases eq_or_lt_of_le hx with hx | hx
  · rw [← hx, F_zero]
  · simpa only [Real.sign_of_pos hx] using (sign_bracket x).2
-- END EXTRACT SmallQSelbergAux.F_ge_one

-- BEGIN EXTRACT SmallQSelbergAux.intervalSign_nonneg
theorem intervalSign_nonneg {A B : ℝ} (hAB : A ≤ B) (x : ℝ) :
    0 ≤ intervalSign A B x := by
  rcases lt_trichotomy x A with h | h | h
  · have hb : 0 < B-x := by linarith
    simp [intervalSign, Real.sign_of_neg (sub_neg.mpr h), Real.sign_of_pos hb]
  · subst x
    rcases eq_or_lt_of_le hAB with h | h
    · subst B; simp [intervalSign]
    · simp [intervalSign, Real.sign_of_pos (sub_pos.mpr h)]
  · rcases lt_trichotomy x B with hb | hb | hb
    · simp [intervalSign, Real.sign_of_pos (sub_pos.mpr h),
        Real.sign_of_pos (sub_pos.mpr hb)]
    · subst x
      simp [intervalSign, Real.sign_of_pos (sub_pos.mpr h)]
    · simp [intervalSign, Real.sign_of_pos (sub_pos.mpr h),
        Real.sign_of_neg (sub_neg.mpr hb)]
-- END EXTRACT SmallQSelbergAux.intervalSign_nonneg

-- BEGIN EXTRACT SmallQSelbergAux.G_nonneg
/-- Nonnegativity holds globally, not merely inside the interval. -/
theorem G_nonneg {A B d : ℝ} (hAB : A ≤ B) (hd : 0 < d) (x : ℝ) : 0 ≤ G A B d x := by
  have hl := (sign_bracket (d*(x-A))).2
  have hr := (sign_bracket (d*(B-x))).2
  rw [sign_scale hd] at hl hr
  have hi := intervalSign_nonneg hAB x
  dsimp [G, intervalSign] at *
  linarith
-- END EXTRACT SmallQSelbergAux.G_nonneg

-- BEGIN EXTRACT SmallQSelbergAux.G_majorizes
/-- Both closed endpoints are included because F(0)=1, even when A=B. -/
theorem G_majorizes {A B d x : ℝ} (hd : 0 < d) (hx : x ∈ Set.Icc A B) :
    1 ≤ G A B d x := by
  have hl := F_ge_one (mul_nonneg hd.le (sub_nonneg.mpr hx.1))
  have hr := F_ge_one (mul_nonneg hd.le (sub_nonneg.mpr hx.2))
  dsimp [G]
  linarith
-- END EXTRACT SmallQSelbergAux.G_majorizes

-- BEGIN EXTRACT SmallQSelbergAux.oddError_neg
theorem oddError_neg (x : ℝ) : oddError (-x) = -oddError x := by
  simp only [oddError, H_neg, Real.sign_neg]
  ring
-- END EXTRACT SmallQSelbergAux.oddError_neg

-- BEGIN EXTRACT SmallQSelbergAux.oddError_bound
theorem oddError_bound (x : ℝ) : |oddError x| ≤ K x := by
  simpa only [oddError, abs_sub_comm] using sign_error x
-- END EXTRACT SmallQSelbergAux.oddError_bound

-- BEGIN EXTRACT SmallQSelbergAux.error_split
theorem error_split (x : ℝ) : error x = oddError x + K x := by
  dsimp [error, oddError, F]; ring
-- END EXTRACT SmallQSelbergAux.error_split

-- BEGIN EXTRACT SmallQSelbergAux.error_bounds
theorem error_bounds (x : ℝ) : 0 ≤ error x ∧ error x ≤ 2*K x := by
  have h := abs_le.mp (oddError_bound x)
  rw [error_split]
  constructor <;> linarith
-- END EXTRACT SmallQSelbergAux.error_bounds

-- BEGIN EXTRACT SmallQSelbergAux.G_split
theorem G_split {d : ℝ} (hd : 0 < d) (A B x : ℝ) :
    G A B d x = intervalSign A B x + (error (d*(x-A))+error (d*(B-x)))/2 := by
  simp only [G, intervalSign, error, sign_scale hd]
  ring
-- END EXTRACT SmallQSelbergAux.G_split
end SmallQSelbergAux
end Package_SmallQSelbergAux

section Package_SmallQSelbergMass
set_option autoImplicit false
open MeasureTheory Filter
open SmallQSelbergAux SmallQBeurlingAux SmallQBeurlingRegularity
open SmallQSincAux SmallQSincFourier
namespace SmallQSelbergMass

-- BEGIN EXTRACT SmallQSelbergMass.sign_measurable
/-- Sign is measurably piecewise constant; no continuity at its jump is asserted. -/
theorem sign_measurable : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
-- END EXTRACT SmallQSelbergMass.sign_measurable

-- BEGIN EXTRACT SmallQSelbergMass.oddError_integrable
/-- The error is genuinely integrable by the actual mass-one K bound. -/
theorem oddError_integrable : Integrable oddError := by
  apply SmallQBeurlingModel.actual_kernel_mass.1.mono'
    ((H_continuous.measurable.sub sign_measurable).aestronglyMeasurable)
  filter_upwards with x
  simpa only [Real.norm_eq_abs, oddError, Pi.sub_apply] using oddError_bound x
-- END EXTRACT SmallQSelbergMass.oddError_integrable

-- BEGIN EXTRACT SmallQSelbergMass.error_integrable
theorem error_integrable : Integrable error := by
  have he : error = fun x ↦ oddError x+K x := funext error_split
  rw [he]
  exact oddError_integrable.add SmallQBeurlingModel.actual_kernel_mass.1
-- END EXTRACT SmallQSelbergMass.error_integrable

-- BEGIN EXTRACT SmallQSelbergMass.scaled_error_integrable
theorem scaled_error_integrable {d : ℝ} (hd : 0 < d) :
    Integrable (fun x : ℝ ↦ error (d*x)) := by
  exact (integrable_comp_mul_left_iff error hd.ne').mpr error_integrable
-- END EXTRACT SmallQSelbergMass.scaled_error_integrable

-- BEGIN EXTRACT SmallQSelbergMass.scaled_oddError_integral
/-- Odd cancellation is retained under every positive real scale. -/
theorem scaled_oddError_integral (d : ℝ) : (∫ x : ℝ, oddError (d*x)) = 0 := by
  have h := integral_neg_eq_self (fun x : ℝ ↦ oddError (d*x)) volume
  simp_rw [mul_neg, oddError_neg] at h
  rw [integral_neg] at h
  linarith
-- END EXTRACT SmallQSelbergMass.scaled_oddError_integral

-- BEGIN EXTRACT SmallQSelbergMass.scaled_error_integral
/-- Exact scaling mass from the already proved normalized sinc profile. -/
theorem scaled_error_integral {d : ℝ} (hd : 0 < d) :
    (∫ x : ℝ, error (d*x)) = 1/d := by
  have ho := (integrable_comp_mul_left_iff oddError hd.ne').mpr oddError_integrable
  have he : (fun x : ℝ ↦ K (d*x)) = profile d 0 := by
    funext x; simp [K, profile, mul_assoc]
  simp_rw [error_split]
  rw [integral_add ho (by rw [he]; exact profile_integrable hd 0),
    scaled_oddError_integral]
  rw [he, profile_integral hd 0, zero_add]
-- END EXTRACT SmallQSelbergMass.scaled_error_integral

-- BEGIN EXTRACT SmallQSelbergMass.left_error_integrable
theorem left_error_integrable {d : ℝ} (hd : 0 < d) (A : ℝ) :
    Integrable (fun x : ℝ ↦ error (d*(x-A))) :=
  (scaled_error_integrable hd).comp_sub_right A
-- END EXTRACT SmallQSelbergMass.left_error_integrable

-- BEGIN EXTRACT SmallQSelbergMass.right_error_integrable
theorem right_error_integrable {d : ℝ} (hd : 0 < d) (B : ℝ) :
    Integrable (fun x : ℝ ↦ error (d*(B-x))) :=
  (scaled_error_integrable hd).comp_sub_left B
-- END EXTRACT SmallQSelbergMass.right_error_integrable

-- BEGIN EXTRACT SmallQSelbergMass.left_error_integral
theorem left_error_integral {d : ℝ} (hd : 0 < d) (A : ℝ) :
    (∫ x : ℝ, error (d*(x-A))) = 1/d := by
  exact (integral_sub_right_eq_self (μ := volume) (fun x : ℝ ↦ error (d*x)) A).trans
    (scaled_error_integral hd)
-- END EXTRACT SmallQSelbergMass.left_error_integral

-- BEGIN EXTRACT SmallQSelbergMass.right_error_integral
theorem right_error_integral {d : ℝ} (hd : 0 < d) (B : ℝ) :
    (∫ x : ℝ, error (d*(B-x))) = 1/d := by
  exact (integral_sub_left_eq_self (fun x : ℝ ↦ error (d*x)) volume B).trans
    (scaled_error_integral hd)
-- END EXTRACT SmallQSelbergMass.right_error_integral

-- BEGIN EXTRACT SmallQSelbergMass.intervalSign_ae
/-- The half-sign convention differs from the closed indicator only at two null points. -/
theorem intervalSign_ae {A B : ℝ} (hAB : A ≤ B) :
    intervalSign A B =ᵐ[volume] (Set.Icc A B).indicator (fun _ : ℝ ↦ (1 : ℝ)) := by
  have hA : ∀ᵐ x : ℝ, x ≠ A := by simp [ae_iff]
  have hB : ∀ᵐ x : ℝ, x ≠ B := by simp [ae_iff]
  filter_upwards [hA, hB] with x hxA hxB
  by_cases hx : x ∈ Set.Icc A B
  · have hl : 0 < x-A := sub_pos.mpr (lt_of_le_of_ne hx.1 (Ne.symm hxA))
    have hr : 0 < B-x := sub_pos.mpr (lt_of_le_of_ne hx.2 hxB)
    simp [intervalSign, Real.sign_of_pos hl, Real.sign_of_pos hr, hx]
  · rw [Set.indicator_of_notMem hx]
    rcases lt_or_gt_of_ne hxA with hl | hl
    · have hr : 0 < B-x := by linarith
      simp [intervalSign, Real.sign_of_neg (sub_neg.mpr hl), Real.sign_of_pos hr]
    · have hr : B < x := by
        by_contra hn
        exact hx ⟨hl.le, le_of_not_gt hn⟩
      simp [intervalSign, Real.sign_of_pos (sub_pos.mpr hl),
        Real.sign_of_neg (sub_neg.mpr hr)]
-- END EXTRACT SmallQSelbergMass.intervalSign_ae

-- BEGIN EXTRACT SmallQSelbergMass.intervalSign_integrable
theorem intervalSign_integrable {A B : ℝ} (hAB : A ≤ B) :
    Integrable (intervalSign A B) := by
  have hi : Integrable ((Set.Icc A B).indicator (fun _ : ℝ ↦ (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  exact hi.congr (intervalSign_ae hAB).symm
-- END EXTRACT SmallQSelbergMass.intervalSign_integrable

-- BEGIN EXTRACT SmallQSelbergMass.intervalSign_integral
theorem intervalSign_integral {A B : ℝ} (hAB : A ≤ B) :
    (∫ x : ℝ, intervalSign A B x) = B-A := by
  rw [integral_congr_ae (intervalSign_ae hAB), integral_indicator_const 1 measurableSet_Icc]
  simp [Measure.real, Real.volume_Icc, sub_nonneg.mpr hAB]
-- END EXTRACT SmallQSelbergMass.intervalSign_integral

-- BEGIN EXTRACT SmallQSelbergMass.G_integrable
/-- Genuine full-line integrability, valid even for signed and singleton intervals. -/
theorem G_integrable {A B d : ℝ} (hAB : A ≤ B) (hd : 0 < d) :
    Integrable (G A B d) := by
  have he : G A B d = fun x ↦ intervalSign A B x +
      (error (d*(x-A))+error (d*(B-x)))/2 := funext (G_split hd A B)
  rw [he]
  exact (intervalSign_integrable hAB).add
    (((left_error_integrable hd A).add (right_error_integrable hd B)).div_const 2)
-- END EXTRACT SmallQSelbergMass.G_integrable

-- BEGIN EXTRACT SmallQSelbergMass.G_integral
/-- Exact Selberg mass, with the closed interval and all scale factors intact. -/
theorem G_integral {A B d : ℝ} (hAB : A ≤ B) (hd : 0 < d) :
    (∫ x : ℝ, G A B d x) = B-A+1/d := by
  simp_rw [G_split hd]
  have hh : Integrable (fun x : ℝ ↦ (error (d*(x-A))+error (d*(B-x)))/2) :=
    ((left_error_integrable hd A).add (right_error_integrable hd B)).div_const 2
  rw [integral_add (intervalSign_integrable hAB) hh, integral_div,
    integral_add (left_error_integrable hd A) (right_error_integrable hd B),
    intervalSign_integral hAB, left_error_integral hd A, right_error_integral hd B]
  ring
-- END EXTRACT SmallQSelbergMass.G_integral
end SmallQSelbergMass
end Package_SmallQSelbergMass

section Package_SmallQSelbergDecay
set_option autoImplicit false
open MeasureTheory Filter Asymptotics
open SmallQSelbergAux SmallQSelbergMass SmallQBeurlingAux SmallQSincAux
namespace SmallQSelbergDecay

-- BEGIN EXTRACT SmallQSelbergDecay.endpoint_kernels
/-- Both oriented endpoint kernels have the same precise centered profile normalization. -/
theorem endpoint_kernels (A B d x : ℝ) :
    K (d*(x-A)) = profile d A x ∧ K (d*(B-x)) = profile d B x := by
  constructor
  · simp [K, profile, mul_assoc]
  · rw [show d*(B-x) = -(d*(x-B)) by ring, K_neg]
    simp [K, profile, mul_assoc]
-- END EXTRACT SmallQSelbergDecay.endpoint_kernels

-- BEGIN EXTRACT SmallQSelbergDecay.intervalSign_exterior
/-- The two signed terms cancel exactly outside the interval. -/
theorem intervalSign_exterior {A B x : ℝ} (hAB : A ≤ B) (hx : x ∉ Set.Icc A B) :
    intervalSign A B x = 0 := by
  by_cases hl : x < A
  · have hr : 0 < B-x := by linarith
    simp [intervalSign, Real.sign_of_neg (sub_neg.mpr hl), Real.sign_of_pos hr]
  · have hr : B < x := by
      by_contra hn
      exact hx ⟨le_of_not_gt hl, le_of_not_gt hn⟩
    have hl : 0 < x-A := by linarith
    simp [intervalSign, Real.sign_of_pos hl, Real.sign_of_neg (sub_neg.mpr hr)]
-- END EXTRACT SmallQSelbergDecay.intervalSign_exterior

-- BEGIN EXTRACT SmallQSelbergDecay.G_upper
/-- Global upper bound, retaining the half-sign convention at both endpoints. -/
theorem G_upper {d : ℝ} (hd : 0 < d) (A B x : ℝ) :
    G A B d x ≤ intervalSign A B x + profile d A x + profile d B x := by
  have hl := (error_bounds (d*(x-A))).2
  have hr := (error_bounds (d*(B-x))).2
  rw [(endpoint_kernels A B d x).1] at hl
  rw [(endpoint_kernels A B d x).2] at hr
  rw [G_split hd]
  linarith
-- END EXTRACT SmallQSelbergDecay.G_upper

-- BEGIN EXTRACT SmallQSelbergDecay.G_exterior_bound
/-- In the tails no interval-length term survives; two genuine sinc tails dominate. -/
theorem G_exterior_bound {A B d x : ℝ} (hAB : A ≤ B) (hd : 0 < d)
    (hx : x ∉ Set.Icc A B) :
    ‖(G A B d x : ℂ)‖ ≤ profile d A x+profile d B x := by
  have h := G_upper hd A B x
  rw [intervalSign_exterior hAB hx, zero_add] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (G_nonneg hAB hd x)] using h
-- END EXTRACT SmallQSelbergDecay.G_exterior_bound

-- BEGIN EXTRACT SmallQSelbergDecay.eventually_exterior
/-- The pointwise tail estimate applies eventually on the genuine real cocompact filter. -/
theorem eventually_exterior (A B : ℝ) : ∀ᶠ x : ℝ in cocompact ℝ, x ∉ Set.Icc A B := by
  have hev : ∀ᶠ x : ℝ in cocompact ℝ, |A|+|B|+1 ≤ |x| :=
    tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (|A|+|B|+1))
  filter_upwards [hev] with x hx
  intro hmem
  have hb : |x| ≤ |A|+|B| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le A, abs_nonneg B, hmem.1]
    · linarith [le_abs_self B, abs_nonneg A, hmem.2]
  linarith
-- END EXTRACT SmallQSelbergDecay.eventually_exterior

-- BEGIN EXTRACT SmallQSelbergDecay.real_profile_decay
/-- The previously verified complex profile decay also controls the nonnegative real profile. -/
theorem real_profile_decay {d : ℝ} (hd : 0 < d) (A : ℝ) :
    profile d A =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-(2 : ℝ))) := by
  apply (profile_decay hd A).norm_left.congr_left
  intro x
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (profile_nonneg d A x)]
-- END EXTRACT SmallQSelbergDecay.real_profile_decay

-- BEGIN EXTRACT SmallQSelbergDecay.G_decay
/-- Actual quadratic decay of G; no impossible Schwartz condition or assumed Fourier support. -/
theorem G_decay {A B d : ℝ} (hAB : A ≤ B) (hd : 0 < d) :
    (fun x ↦ (G A B d x : ℂ)) =O[cocompact ℝ]
      (fun x : ℝ ↦ |x| ^ (-(2 : ℝ))) := by
  have h : (fun x ↦ (G A B d x : ℂ)) =O[cocompact ℝ]
      (fun x ↦ profile d A x+profile d B x) := by
    apply IsBigO.of_norm_eventuallyLE
    filter_upwards [eventually_exterior A B] with x hx
    exact G_exterior_bound hAB hd hx
  exact h.trans ((real_profile_decay hd A).add (real_profile_decay hd B))
-- END EXTRACT SmallQSelbergDecay.G_decay
end SmallQSelbergDecay
end Package_SmallQSelbergDecay

section Package_SmallQSelbergDifference
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators FourierTransform
open SmallQBeurlingAux SmallQSelbergAux
namespace SmallQSelbergDifference

-- BEGIN EXTRACT SmallQSelbergDifference.S
/-- The signed sinc factor, rather than its square. -/
noncomputable def S (x : ℝ) : ℝ := Real.sinc (Real.pi*x)
-- END EXTRACT SmallQSelbergDifference.S

-- BEGIN EXTRACT SmallQSelbergDifference.cross
/-- The cross product of adjacent sinc translates. -/
noncomputable def cross (x : ℝ) : ℝ := S x * S (x-1)
-- END EXTRACT SmallQSelbergDifference.cross

-- BEGIN EXTRACT SmallQSelbergDifference.positivePart_step
/-- Genuine summability justifies peeling the first positive cardinal term. -/
theorem positivePart_step (x : ℝ) : positivePart (x+1) = K x + positivePart x := by
  have h := (positive_part_summable (x+1)).tsum_eq_zero_add
  convert h using 1
  · unfold positivePart
    apply tsum_congr; intro n
    congr 1
  · congr 1
    · congr 1; norm_num
    · apply tsum_congr; intro n
      congr 1; push_cast; ring
-- END EXTRACT SmallQSelbergDifference.positivePart_step

-- BEGIN EXTRACT SmallQSelbergDifference.cross_identity
/-- The adjacent sinc product is the exact cancellation of the two 1/x tails.
Both removable poles are handled literally, not by division by zero. -/
theorem cross_identity (x : ℝ) : x*K x - (x-1)*K (x-1) = cross x := by
  by_cases hx : x = 0
  · subst x
    norm_num [cross, S, K, Real.sinc_of_ne_zero, Real.pi_ne_zero]
  by_cases hx1 : x = 1
  · subst x
    norm_num [cross, S, K, Real.sinc_of_ne_zero, Real.pi_ne_zero]
  have hx' : x-1 ≠ 0 := sub_ne_zero.mpr hx1
  have hp := Real.pi_ne_zero
  have hs : Real.sin (Real.pi*(x-1)) = -Real.sin (Real.pi*x) := by
    rw [mul_sub, mul_one, Real.sin_sub_pi]
  simp only [cross, S, K, Real.sinc_of_ne_zero (mul_ne_zero hp hx),
    Real.sinc_of_ne_zero (mul_ne_zero hp hx'), hs]
  field_simp
  ring
-- END EXTRACT SmallQSelbergDifference.cross_identity

-- BEGIN EXTRACT SmallQSelbergDifference.H_step
/-- A finite difference of H is a finite sum of genuinely bandlimited products. -/
theorem H_step (x : ℝ) : H x - H (x-1) = K x + K (x-1) + 2*cross x := by
  have hp := positivePart_step (x-1)
  have hn := positivePart_step (-x)
  have he := cross_identity x
  rw [show x-1+1 = x by ring] at hp
  dsimp [H]
  rw [show -(x-1) = -x+1 by ring]
  rw [hp, hn, K_neg]
  nlinarith [he]
-- END EXTRACT SmallQSelbergDifference.H_step

-- BEGIN EXTRACT SmallQSelbergDifference.F_step
/-- F itself is not integrable. Only this exact finite difference will be transformed. -/
theorem F_step (x : ℝ) : F x - F (x-1) = 2*K x + 2*cross x := by
  have h := H_step x
  dsimp [F]
  linarith
-- END EXTRACT SmallQSelbergDifference.F_step

-- BEGIN EXTRACT SmallQSelbergDifference.G_step
/-- The integrable interval function's difference contains only four integrable terms. -/
theorem G_step (A B x : ℝ) :
    G A B 1 x - G A B 1 (x-1) =
      K (x-A) + cross (x-A) - K (B+1-x) - cross (B+1-x) := by
  have hl := F_step (x-A)
  have hr := F_step (B+1-x)
  simp only [G, one_mul]
  rw [show x-1-A = (x-A)-1 by ring,
    show B-(x-1) = B+1-x by ring]
  rw [show B+1-x-1 = B-x by ring] at hr
  linarith
-- END EXTRACT SmallQSelbergDifference.G_step
end SmallQSelbergDifference
end Package_SmallQSelbergDifference

section Package_SmallQSelbergCrossSpectrum
set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform
open SmallQSincAux SmallQSincFourier SmallQSincSpectrum SmallQPoissonAux
open SmallQSelbergDifference TaoFivePrimes
namespace SmallQSelbergCrossSpectrum

-- BEGIN EXTRACT SmallQSelbergCrossSpectrum.modulated_box_memLp
/-- Positive modulation preserves the actual box norm and every Lp condition. -/
theorem modulated_box_memLp (a : ℝ) (p : ENNReal) : MemLp (modulate (box 1) a) p := by
  apply (box_memLp 1 p).congr_norm
  · exact (box_memLp 1 p).aestronglyMeasurable.mul
      (by unfold expCircle; fun_prop : Continuous (fun x : ℝ ↦ expCircle (a*x))).aestronglyMeasurable
  · filter_upwards with x
    exact (norm_modulate (box 1) a x).symm
-- END EXTRACT SmallQSelbergCrossSpectrum.modulated_box_memLp

-- BEGIN EXTRACT SmallQSelbergCrossSpectrum.cross_correlation_zero
/-- The shifted modulated box still has zero overlap at both closed unit band edges. -/
theorem cross_correlation_zero {t : ℝ} (ht : 1 ≤ |t|) :
    (∫ x : ℝ, inner ℂ (box 1 x) (modulate (box 1) 1 (x-t))) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [volume.ae_ne (-1/2), volume.ae_ne (1/2)] with x hx₁ hx₂
  by_cases hx : x ∈ Set.Icc (-1/2 : ℝ) (1/2)
  · have hnx : x-t ∉ Set.Icc (-1/2 : ℝ) (1/2) := by
      intro hy
      have hxa : -1/2 < x := lt_of_le_of_ne hx.1 (Ne.symm hx₁)
      have hxb : x < 1/2 := lt_of_le_of_ne hx.2 hx₂
      rcases le_abs.mp ht with ht | ht <;> linarith [hy.1, hy.2]
    have hz : box 1 (x-t) = 0 := Set.indicator_of_notMem hnx _
    simp only [modulate, hz, zero_mul, inner_zero_right, Pi.zero_apply]
  · have hz : box 1 x = 0 := Set.indicator_of_notMem hx _
    rw [hz, inner_zero_left]
    rfl
-- END EXTRACT SmallQSelbergCrossSpectrum.cross_correlation_zero

-- BEGIN EXTRACT SmallQSelbergCrossSpectrum.cross_integrable
/-- This product is genuinely L1 by Holder applied to the two actual L2 sinc factors. -/
theorem cross_integrable : Integrable cross := by
  have hs : MemLp S 2 := (memLp_two_iff_integrable_sq
    (by unfold S; fun_prop : Continuous S).aestronglyMeasurable).mpr
      SmallQBeurlingModel.actual_kernel_mass.1
  have ht : MemLp (fun x : ℝ ↦ S (x-1)) 2 := by
    simpa only [Function.comp_def, ← sub_eq_add_neg] using
      hs.comp_measurePreserving (measurePreserving_add_right volume (-1))
  exact hs.integrable_mul ht
-- END EXTRACT SmallQSelbergCrossSpectrum.cross_integrable

-- BEGIN EXTRACT SmallQSelbergCrossSpectrum.cross_fourier_correlation
/-- Its ordinary Bochner Fourier transform is the exact L2 box correlation. -/
theorem cross_fourier_correlation (t : ℝ) :
    𝓕 (fun x ↦ (cross x : ℂ)) t =
      ∫ x : ℝ, inner ℂ (box 1 x) (modulate (box 1) 1 (x-t)) := by
  have hi : Integrable (modulate (box 1) 1) :=
    memLp_one_iff_integrable.mp (modulated_box_memLp 1 1)
  have hm : MemLp (fun x : ℝ ↦ modulate (box 1) 1 (x-t)) 2 := by
    simpa only [Function.comp_def, ← sub_eq_add_neg] using
      (modulated_box_memLp 1 2).comp_measurePreserving
        (measurePreserving_add_right volume (-t))
  have h := inner_fourier_integral (box_integrable 1) (box_memLp 1 2)
    (hi.comp_sub_right t) hm
  rw [← h, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  rw [fourier_translate, fourier_modulate,
    box_fourier (by norm_num : (0 : ℝ) ≤ 1),
    box_fourier (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [RCLike.inner_apply, Complex.conj_ofReal, cross, S,
    Complex.ofReal_mul, Complex.ofReal_one, mul_one, one_mul, smul_eq_mul, expCircle]
  have he : ((-2 : ℝ) : ℂ)*Real.pi*x*t*Complex.I =
      2*Real.pi*Complex.I*((-t : ℝ)*x) := by push_cast; ring
  rw [he]
  ring
-- END EXTRACT SmallQSelbergCrossSpectrum.cross_fourier_correlation

-- BEGIN EXTRACT SmallQSelbergCrossSpectrum.cross_spectrum_zero
/-- Both signed unit edges are included without assuming closed boxes disjoint as sets. -/
theorem cross_spectrum_zero {t : ℝ} (ht : 1 ≤ |t|) :
    𝓕 (fun x ↦ (cross x : ℂ)) t = 0 := by
  rw [cross_fourier_correlation, cross_correlation_zero ht]
-- END EXTRACT SmallQSelbergCrossSpectrum.cross_spectrum_zero
end SmallQSelbergCrossSpectrum
end Package_SmallQSelbergCrossSpectrum

section Package_SmallQSelbergFourierAux
set_option autoImplicit false
open MeasureTheory Filter
open scoped FourierTransform
open SmallQPoissonAux SmallQSincSpectrum TaoFivePrimes
namespace SmallQSelbergFourierAux

-- BEGIN EXTRACT SmallQSelbergFourierAux.modulate_integrable
/-- Modulation of a genuine L1 function is still genuinely L1. -/
theorem modulate_integrable {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ) :
    Integrable (modulate f a) := by
  apply hf.norm.mono'
  · exact hf.aestronglyMeasurable.mul
      (by unfold expCircle; fun_prop : Continuous (fun x : ℝ ↦ expCircle (a*x))).aestronglyMeasurable
  · filter_upwards with x
    exact le_of_eq (norm_modulate f a x)
-- END EXTRACT SmallQSelbergFourierAux.modulate_integrable

-- BEGIN EXTRACT SmallQSelbergFourierAux.fourier_integral
/-- Converts the Fourier convention to the actual integrable modulated function. -/
theorem fourier_integral (f : ℝ → ℂ) (t : ℝ) :
    𝓕 f t = ∫ x : ℝ, modulate f (-t) x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  dsimp [modulate, expCircle]
  have he : ((-2*Real.pi*x*t : ℝ) : ℂ)*Complex.I =
      2*Real.pi*Complex.I*((-t : ℝ)*x) := by push_cast; ring
  rw [he, mul_comm]
  push_cast
  rfl
-- END EXTRACT SmallQSelbergFourierAux.fourier_integral

-- BEGIN EXTRACT SmallQSelbergFourierAux.fourier_sub
/-- Subtraction is justified by L1 hypotheses, never default-zero Bochner values. -/
theorem fourier_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    𝓕 (fun x ↦ f x-g x) t = 𝓕 f t - 𝓕 g t := by
  simp only [fourier_integral, modulate, sub_mul]
  exact integral_sub (modulate_integrable hf (-t)) (modulate_integrable hg (-t))
-- END EXTRACT SmallQSelbergFourierAux.fourier_sub

-- BEGIN EXTRACT SmallQSelbergFourierAux.fourier_add
theorem fourier_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    𝓕 (fun x ↦ f x+g x) t = 𝓕 f t + 𝓕 g t := by
  simp only [fourier_integral, modulate, add_mul]
  exact integral_add (modulate_integrable hf (-t)) (modulate_integrable hg (-t))
-- END EXTRACT SmallQSelbergFourierAux.fourier_add

-- BEGIN EXTRACT SmallQSelbergFourierAux.fourier_reflect
/-- Reflection retains the actual sign of the Fourier frequency. -/
theorem fourier_reflect (f : ℝ → ℂ) (t : ℝ) :
    𝓕 (fun x ↦ f (-x)) t = 𝓕 f (-t) := by
  rw [fourier_integral, fourier_integral, neg_neg,
    ← integral_neg_eq_self (modulate f t) volume]
  apply integral_congr_ae
  filter_upwards with x
  simp [modulate, neg_mul, mul_neg]
-- END EXTRACT SmallQSelbergFourierAux.fourier_reflect

-- BEGIN EXTRACT SmallQSelbergFourierAux.fourier_reflect_translate
/-- Endpoint reflection is reflection followed by an exact signed translation. -/
theorem fourier_reflect_translate (f : ℝ → ℂ) (a t : ℝ) :
    𝓕 (fun x ↦ f (a-x)) t = expCircle (-a*t) * 𝓕 f (-t) := by
  have he : (fun x ↦ f (a-x)) = (fun x ↦ (fun y ↦ f (-y)) (x-a)) := by
    funext x; congr 1; ring
  rw [he, fourier_translate (fun y ↦ f (-y)) a t, fourier_reflect]
-- END EXTRACT SmallQSelbergFourierAux.fourier_reflect_translate

-- BEGIN EXTRACT SmallQSelbergFourierAux.fourier_continuous
/-- L1 supplies continuity, including every exceptional integer and band-edge frequency. -/
theorem fourier_continuous {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) := by
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) hf
-- END EXTRACT SmallQSelbergFourierAux.fourier_continuous

-- BEGIN EXTRACT SmallQSelbergFourierAux.fourier_scale
/-- Exact positive dilation, proved by the Haar change of variables on the actual integral. -/
theorem fourier_scale (f : ℝ → ℂ) {d : ℝ} (hd : 0 < d) (t : ℝ) :
    𝓕 (fun x ↦ f (d*x)) t = (d⁻¹ : ℝ) • 𝓕 f (t/d) := by
  rw [fourier_integral, fourier_integral]
  have he : (fun x ↦ modulate (fun y ↦ f (d*y)) (-t) x) =
      (fun x ↦ modulate f (-(t/d)) (d*x)) := by
    funext x
    dsimp [modulate]
    congr 2
    field_simp
  rw [he, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hd)]
-- END EXTRACT SmallQSelbergFourierAux.fourier_scale
end SmallQSelbergFourierAux
end Package_SmallQSelbergFourierAux

section Package_SmallQSelbergSpectrum
set_option autoImplicit false
open MeasureTheory Filter
open scoped FourierTransform
open SmallQSelbergAux SmallQSelbergMass SmallQSelbergDifference SmallQSelbergCrossSpectrum
open SmallQSelbergFourierAux SmallQBeurlingAux SmallQSincSpectrum TaoFivePrimes
namespace SmallQSelbergSpectrum

-- BEGIN EXTRACT SmallQSelbergSpectrum.K_integrable
/-- The actual sinc-square is a genuine L1 function in the present notation. -/
theorem K_integrable : Integrable (fun x ↦ (K x : ℂ)) :=
  SmallQBeurlingModel.actual_kernel_mass.1.ofReal
-- END EXTRACT SmallQSelbergSpectrum.K_integrable

-- BEGIN EXTRACT SmallQSelbergSpectrum.K_spectrum_zero
theorem K_spectrum_zero {t : ℝ} (ht : 1 ≤ |t|) :
    𝓕 (fun x ↦ (K x : ℂ)) t = 0 := by
  simpa only [K_profile] using profile_spectrum_zero (by norm_num : (0 : ℝ) < 1) ht
-- END EXTRACT SmallQSelbergSpectrum.K_spectrum_zero

-- BEGIN EXTRACT SmallQSelbergSpectrum.G_difference_spectrum_zero
/-- No transformation of non-L1 H or F is used: this is the integrable G difference. -/
theorem G_difference_spectrum_zero {A B : ℝ} (hAB : A ≤ B) {t : ℝ} (ht : 1 ≤ |t|) :
    𝓕 (fun x ↦ ((G A B 1 x - G A B 1 (x-1) : ℝ) : ℂ)) t = 0 := by
  have hk := K_integrable
  have hc : Integrable (fun x ↦ (cross x : ℂ)) := cross_integrable.ofReal
  have he : (fun x ↦ ((G A B 1 x - G A B 1 (x-1) : ℝ) : ℂ)) =
      (fun x ↦ ((K (x-A) : ℂ)+(cross (x-A) : ℂ)) -
        ((K (B+1-x) : ℂ)+(cross (B+1-x) : ℂ))) := by
    funext x; rw [G_step]; push_cast; ring
  have hil : Integrable (fun x ↦ (K (x-A) : ℂ)+(cross (x-A) : ℂ)) :=
    (hk.comp_sub_right A).add (hc.comp_sub_right A)
  have hir : Integrable (fun x ↦ (K (B+1-x) : ℂ)+(cross (B+1-x) : ℂ)) :=
    (hk.comp_sub_left (B+1)).add (hc.comp_sub_left (B+1))
  rw [he, fourier_sub hil hir,
    fourier_add (hk.comp_sub_right A) (hc.comp_sub_right A),
    fourier_add (hk.comp_sub_left (B+1)) (hc.comp_sub_left (B+1)),
    fourier_translate (fun x ↦ (K x : ℂ)) A t,
    fourier_translate (fun x ↦ (cross x : ℂ)) A t,
    fourier_reflect_translate (fun x ↦ (K x : ℂ)) (B+1) t,
    fourier_reflect_translate (fun x ↦ (cross x : ℂ)) (B+1) t,
    K_spectrum_zero ht, cross_spectrum_zero ht,
    K_spectrum_zero (by simpa using ht : 1 ≤ |-t|),
    cross_spectrum_zero (by simpa using ht : 1 ≤ |-t|)]
  ring
-- END EXTRACT SmallQSelbergSpectrum.G_difference_spectrum_zero

-- BEGIN EXTRACT SmallQSelbergSpectrum.G_exterior_multiplier
/-- The only possible exterior spectrum is at integral frequencies. -/
theorem G_exterior_multiplier {A B : ℝ} (hAB : A ≤ B) {t : ℝ} (ht : 1 ≤ |t|) :
    (1-expCircle (-t)) * 𝓕 (fun x ↦ (G A B 1 x : ℂ)) t = 0 := by
  have hi : Integrable (fun x ↦ (G A B 1 x : ℂ)) :=
    (G_integrable hAB (by norm_num)).ofReal
  have h := G_difference_spectrum_zero hAB ht
  simp only [Complex.ofReal_sub] at h
  rw [fourier_sub hi (hi.comp_sub_right 1),
    fourier_translate (fun x ↦ (G A B 1 x : ℂ)) 1 t] at h
  simp only [neg_mul, one_mul] at h
  linear_combination h
-- END EXTRACT SmallQSelbergSpectrum.G_exterior_multiplier

-- BEGIN EXTRACT SmallQSelbergSpectrum.irrational_multiplier
/-- Irrational frequencies have a genuinely nonzero translation multiplier. -/
theorem irrational_multiplier {t : ℝ} (ht : Irrational t) : 1-expCircle (-t) ≠ 0 := by
  intro h
  have he : expCircle (-t) = 1 := (sub_eq_zero.mp h).symm
  unfold expCircle at he
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  have hc : (2*Real.pi*Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hr : ((-t : ℝ) : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ hc
    calc
      _ = (n : ℂ)*(2*Real.pi*Complex.I) := hn
      _ = _ := by ring
  have hr' : -t = (n : ℝ) := by exact_mod_cast hr
  apply ht.ne_int (-n)
  push_cast
  linarith
-- END EXTRACT SmallQSelbergSpectrum.irrational_multiplier

-- BEGIN EXTRACT SmallQSelbergSpectrum.closed_support_of_multiplier
/-- A continuous function annihilated by the translation multiplier has no exterior
spectrum at all. Density removes all integral exceptions, then closure adds both edges. -/
theorem closed_support_of_multiplier {f : ℝ → ℂ} (hc : Continuous f)
    (hm : ∀ t, 1 ≤ |t| → (1-expCircle (-t))*f t = 0) :
    ∀ t, 1 ≤ |t| → f t = 0 := by
  have ho : IsOpen {t : ℝ | 1 < |t|} := isOpen_lt continuous_const continuous_abs
  have hz : Set.EqOn f (fun _ ↦ 0) ({t : ℝ | 1 < |t|} ∩ {t | Irrational t}) := by
    intro t ht
    exact (mul_eq_zero.mp (hm t ht.1.le)).resolve_left (irrational_multiplier ht.2)
  have hstrict : ∀ t : ℝ, 1 < |t| → f t = 0 := by
    intro t ht
    apply hz.closure hc continuous_const
    exact ho.inter_closure ⟨ht, dense_irrational t⟩
  have hp : Set.EqOn f (fun _ ↦ 0) (Set.Ioi 1) := by
    intro t ht
    exact hstrict t (lt_of_lt_of_le ht (le_abs_self t))
  have hn : Set.EqOn f (fun _ ↦ 0) (Set.Iio (-1)) := by
    intro t ht
    change t < -1 at ht
    exact hstrict t (lt_of_lt_of_le (by linarith : 1 < -t) (neg_le_abs t))
  have hp' := hp.closure hc continuous_const
  have hn' := hn.closure hc continuous_const
  rw [closure_Ioi] at hp'
  rw [closure_Iio] at hn'
  intro t ht
  rcases le_abs.mp ht with ht | ht
  · exact hp' ht
  · exact hn' (show t ≤ -1 by linarith)
-- END EXTRACT SmallQSelbergSpectrum.closed_support_of_multiplier

-- BEGIN EXTRACT SmallQSelbergSpectrum.G_unit_spectrum_zero
/-- All endpoints and arbitrary signed intervals at unit bandwidth, not only lattice widths. -/
theorem G_unit_spectrum_zero {A B : ℝ} (hAB : A ≤ B) {t : ℝ} (ht : 1 ≤ |t|) :
    𝓕 (fun x ↦ (G A B 1 x : ℂ)) t = 0 := by
  apply closed_support_of_multiplier
    (fourier_continuous ((G_integrable hAB (by norm_num)).ofReal))
    (fun _ ht ↦ G_exterior_multiplier hAB ht) t ht
-- END EXTRACT SmallQSelbergSpectrum.G_unit_spectrum_zero

-- BEGIN EXTRACT SmallQSelbergSpectrum.G_scale
/-- Literal normalization, with both scaled endpoints and no hypothesis on interval width. -/
theorem G_scale (A B d x : ℝ) : G A B d x = G (d*A) (d*B) 1 (d*x) := by
  simp only [G, one_mul, mul_sub]
-- END EXTRACT SmallQSelbergSpectrum.G_scale

-- BEGIN EXTRACT SmallQSelbergSpectrum.G_spectrum_zero
/-- The actual Fourier transform of the concrete Selberg G vanishes at |t|>=d,
including both signed edges, for every real A<=B and d>0. -/
theorem G_spectrum_zero {A B d : ℝ} (hAB : A ≤ B) (hd : 0 < d)
    {t : ℝ} (ht : d ≤ |t|) : 𝓕 (fun x ↦ (G A B d x : ℂ)) t = 0 := by
  have he : (fun x ↦ (G A B d x : ℂ)) =
      (fun x ↦ (G (d*A) (d*B) 1 (d*x) : ℂ)) := by
    funext x; rw [G_scale]
  rw [he, fourier_scale (fun x ↦ (G (d*A) (d*B) 1 x : ℂ)) hd]
  rw [G_unit_spectrum_zero (mul_le_mul_of_nonneg_left hAB hd.le)]
  · simp
  · rw [abs_div, abs_of_pos hd]
    exact (le_div_iff₀ hd).mpr (by simpa using ht)
-- END EXTRACT SmallQSelbergSpectrum.G_spectrum_zero
end SmallQSelbergSpectrum
end Package_SmallQSelbergSpectrum

section Package_Formalization
set_option autoImplicit false
namespace TaoFivePrimes

-- BEGIN EXTRACT TaoFivePrimes.small_q_selberg_continuous_majorant
/-- Continuous Selberg interval-majorant construction, still open. For every closed
real interval and 0<delta<=1, construct a continuous integrable nonnegative real function
majorizing one on the entire interval, with integral exactly B-A+1/delta, quadratic
decay at infinity, and actual Fourier transform zero for |t|>=delta including equality.
There are no discrete sums or operator estimates in this analytic construction input.
A Gaussian is not a witness: its Fourier transform never vanishes. -/
theorem small_q_selberg_continuous_majorant (A B delta : ℝ)
    (hAB : A ≤ B) (hd : 0 < delta) (hu : delta ≤ 1) :
    ∃ f : ℝ → ℝ, SmallQPoissonAux.ContinuousMajorant A B delta f := by
  refine ⟨SmallQSelbergAux.G A B delta, ?_⟩
  exact ⟨SmallQSelbergAux.G_continuous A B delta,
    SmallQSelbergMass.G_integrable hAB hd,
    SmallQSelbergDecay.G_decay hAB hd,
    SmallQSelbergAux.G_nonneg hAB hd,
    fun _ hl hr ↦ SmallQSelbergAux.G_majorizes hd ⟨hl, hr⟩,
    SmallQSelbergMass.G_integral hAB hd,
    fun _ ht ↦ SmallQSelbergSpectrum.G_spectrum_zero hAB hd ht⟩
-- END EXTRACT TaoFivePrimes.small_q_selberg_continuous_majorant

-- BEGIN EXTRACT TaoFivePrimes.small_q_selberg_discrete_majorant
/-- Discrete Selberg majorant existence for every closed real interval and 0<delta<=1.
The weight is nonnegative and summable on all integers, at least one on the interval,
has mass at most B-A+1/delta, and its actual Fourier series vanishes at every phase
whose distance to all integers is at least delta. This is the remaining analytic
construction and Poisson-summation input; no operator estimate is assumed here. -/
theorem small_q_selberg_discrete_majorant (A B delta : ℝ)
    (hAB : A ≤ B) (hd : 0 < delta) (hu : delta ≤ 1) :
    ∃ g : ℤ → ℝ, SmallQMajorantAux.Majorant A B delta g := by
  obtain ⟨f, hf⟩ := small_q_selberg_continuous_majorant A B delta hAB hd hu
  exact ⟨(fun n ↦ f n), SmallQPoissonAux.discrete_of_continuous hu hf⟩
-- END EXTRACT TaoFivePrimes.small_q_selberg_discrete_majorant

-- BEGIN EXTRACT TaoFivePrimes.small_q_separated_fourier_large_sieve
/-- Separated finite Fourier operator inequality on an arbitrary finite integer
frequency support in [A,B]. Distinct sample phases are at least delta apart modulo
all integer translates, with 0<delta<=1. The exact constant is B-A+1/delta.
This is the analytic part of the large sieve, with no odd-lattice or subdivision
hypotheses; those reductions are proved separately in SmallQSubdivisionAux. -/
theorem small_q_separated_fourier_large_sieve
    (T : Finset ℕ) (J : Finset ℤ) (theta : ℕ → ℝ) (A B delta : ℝ)
    (hAB : A ≤ B) (hd : 0 < delta) (hu : delta ≤ 1)
    (hJ : ∀ j ∈ J, A ≤ (j : ℝ) ∧ (j : ℝ) ≤ B)
    (hg : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → ∀ k : ℤ, delta ≤ |theta d-theta e-k|)
    (v : ℤ → ℂ) :
    (∑ d ∈ T, ‖∑ j ∈ J, v j*expCircle (theta d*(j : ℝ))‖^2) ≤
      (B-A+1/delta)*(∑ j ∈ J, ‖v j‖^2) := by
  obtain ⟨g, hm⟩ := small_q_selberg_discrete_majorant A B delta hAB hd hu
  exact SmallQMajorantAux.fourier_of_majorant T J theta A B delta g hm hJ hg v
-- END EXTRACT TaoFivePrimes.small_q_separated_fourier_large_sieve
end TaoFivePrimes

-- BEGIN EXTRACT Theorem51Dyadic.raw_operator
/-- Sharp raw-row operator on the exact arbitrary-real dyadic sets. The completed
Selberg/Fourier theorem supplies the generic analytic input; the source approximation
supplies only local signed separation. Arbitrary complex vectors include the actual
centered coefficients. This does not close the open pointwise arithmetic obligation. -/
theorem Theorem51Dyadic.raw_operator
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (W : ℝ) (hW : W ∈ Set.Icc V (x / U)) (b : ℕ → ℂ) :
    (∑ d ∈ Theorem51Dyadic.dSet x U W,
      ‖∑ w ∈ Theorem51Dyadic.wSet x V W,
        b w * TaoFivePrimes.expCircle (alpha*(d*w))‖^2) ≤
      (W/4+2*q)*(x/(2*W*q)+1) *
        (∑ w ∈ Theorem51Dyadic.wSet x V W, ‖b w‖^2) := by
  classical
  obtain ⟨hx,hW40,hd40⟩ := Theorem51DyadicEnergyGate.sizes x alpha beta a q U V W
    ⟨hq,haq,halpha,hbeta,hU40,hV40,hUx,hVx,hUV,hUV2⟩ hW
  have hWp : 0 < W := by linarith
  have hf : SmallQSubdivisionAux.FourierBound :=
    TaoFivePrimes.small_q_separated_fourier_large_sieve
  have hh := SmallQSubdivisionAux.operator_of_blocks hf
    (Theorem51Dyadic.dSet x U W) (Theorem51Dyadic.wSet x V W)
    alpha (x/(2*W)) (x/W) (W/2) W q (by omega)
    (by apply div_le_div_of_nonneg_left hx.le hWp; linarith) (by linarith)
    (by
      intro d hd
      obtain ⟨_, _, ho, hl, hu⟩ := Finset.mem_filter.mp hd
      exact ⟨ho,hl,hu⟩)
    (by
      intro w hw
      obtain ⟨_, _, ho, hl, hu⟩ := Finset.mem_filter.mp hw
      exact ⟨ho,hl,hu⟩)
    (fun j k hj hs ↦ SmallQSieveAux.local_gap alpha beta a q (by omega)
      haq halpha hbeta j k hj hs) b
  convert hh using 1 <;> ring
-- END EXTRACT Theorem51Dyadic.raw_operator

-- BEGIN EXTRACT Theorem51Dyadic.centered_raw_operator
/-- The sharp raw operator applied to the unchanged actual centered coefficients. -/
theorem Theorem51Dyadic.centered_raw_operator
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (U V W : ℝ)
    (h : Theorem51Dyadic.Hyp x alpha beta a q U V) (hW : W ∈ Set.Icc V (x/U)) :
    (∑ d ∈ Theorem51Dyadic.dSet x U W,
      ‖∑ w ∈ Theorem51Dyadic.wSet x V W,
        (TaoFivePrimes.theorem51Centered V w : ℂ) *
          TaoFivePrimes.expCircle (alpha*(d*w))‖^2) ≤
      (W/4+2*q)*(x/(2*W*q)+1) *
        (∑ w ∈ Theorem51Dyadic.wSet x V W,
          ‖(TaoFivePrimes.theorem51Centered V w : ℂ)‖^2) := by
  rcases h with ⟨hq,haq,ha,hb,hU,hV,hUx,hVx,hUV,hUV2⟩
  exact Theorem51Dyadic.raw_operator x alpha beta a q hq haq ha hb U V hU hV hUx hVx
    hUV hUV2 W hW (fun w ↦ (TaoFivePrimes.theorem51Centered V w : ℂ))
-- END EXTRACT Theorem51Dyadic.centered_raw_operator

-- BEGIN EXTRACT TaoFivePrimes.theorem51_typeII_box_arithmetic
/-- Open arithmetic obligation: the norm of the actual finite complex dyadic box
obeys the explicit source envelope at every W in the closed source interval.
No norm sum, q-specialization, or presumed cancellation replaces this expression. -/
theorem TaoFivePrimes.theorem51_typeII_box_arithmetic
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∀ W ∈ Set.Icc V (x / U),
      ‖Theorem51Dyadic.box x alpha U V W‖ ≤
        (1.1 / 8) * ((1 / (2 * Real.sqrt 2)) * (x / Real.sqrt (q : ℝ))
              + (1 / 2) * Real.sqrt (x * W) + x / Real.sqrt W
              + Real.sqrt 2 * Real.sqrt (x * (q : ℝ))) * Real.log W := by
  intro W hW
  have h : Theorem51Dyadic.Hyp x alpha beta a q U V :=
    ⟨hq,haq,halpha,hbeta,hU40,hV40,hUx,hVx,hUV,hUV2⟩
  obtain ⟨hx,hW40,hd40⟩ := Theorem51DyadicEnergyGate.sizes x alpha beta a q U V W h hW
  have hWp : 0 < W := by linarith
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog : 0 ≤ Real.log W := Real.log_nonneg (by linarith)
  let K : ℝ := (W/4+2*q)*(x/(2*W*q)+1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have he := Theorem51Dyadic.energy_of_operator x alpha U V W K hx.le hW40 hd40 hK
    (Theorem51Dyadic.centered_raw_operator x alpha beta a q U V W h hW)
  have hc := (Theorem51Dyadic.box_cauchy x alpha U V W).trans he
  have hn : ‖Theorem51Dyadic.box x alpha U V W‖ ≤
      (1.1/8)*Real.sqrt (K*x)*Real.log W := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    convert hc using 1
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hK hx.le)]
    ring
  have hs := Theorem51Dyadic.sqrt_expansion x W (q : ℝ) hx.le hWp hqp
  exact hn.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 1.1/8)) hlog)
-- END EXTRACT TaoFivePrimes.theorem51_typeII_box_arithmetic

end Package_Formalization



set_option autoImplicit false
open scoped BigOperators

namespace DyadicBoxTransfer

theorem window_tsum_eq_sum (x U V W : ℝ) (f : ℕ → ℕ → ℂ)
    (hx : 0 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hW : W ∈ Set.Icc V (x / U)) :
    (∑' d : ℕ, ∑' w : ℕ,
      if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 ∧
        x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧
        W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then f d w else 0) =
    ∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ w ∈ Finset.range (⌊x⌋₊ + 1),
      if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 ∧
        x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧
        W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then f d w else 0 := by
  classical
  have hWx : W ≤ x := hW.2.trans (div_le_self hx hU)
  have hdiv : x / W ≤ x := div_le_self hx (hV.trans hW.1)
  have hin (n : ℕ) (hn : (n : ℝ) ≤ x) : n ∈ Finset.range (⌊x⌋₊ + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((Nat.le_floor_iff hx).mpr hn)
  rw [tsum_eq_sum (s := Finset.range (⌊x⌋₊ + 1))]
  · apply Finset.sum_congr rfl
    intro d hd
    apply tsum_eq_sum
    intro w hw
    apply if_neg
    intro h
    exact hw (hin w (h.2.2.2.2.2.2.2.trans hWx))
  · intro d hd
    calc
      _ = ∑' w : ℕ, (0 : ℂ) := by
        apply tsum_congr
        intro w
        apply if_neg
        intro h
        exact hd (hin d (h.2.2.2.2.2.1.trans hdiv))
      _ = 0 := tsum_zero

end DyadicBoxTransfer

namespace DyadicBoxTransfer

-- The actual source window and nested guards, with arbitrary coefficients
-- and phase function. The adapter is stronger than its intended substitution.
theorem window_tsum_eq_nested_box (x alpha U V W : ℝ)
    (c : ℕ → ℕ → ℂ) (E : ℝ → ℂ)
    (hx : 0 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hW : W ∈ Set.Icc V (x / U)) :
    (∑' d : ℕ, ∑' w : ℕ,
      if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 ∧
        x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧
        W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
        c d w * E (alpha * d * w) else 0) =
    ∑ d ∈ Finset.range (⌊x⌋₊ + 1), ∑ w ∈ Finset.range (⌊x⌋₊ + 1),
      if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
        if x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧
          W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
          c d w * E (alpha * ((d * w : ℕ) : ℝ)) else 0
      else 0 := by
  rw [window_tsum_eq_sum x U V W _ hx hU hV hW]
  simp only [Nat.cast_mul, mul_assoc, ← ite_and, and_assoc]

end DyadicBoxTransfer
open scoped BigOperators
theorem solution
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (W : ℝ) (hW : W ∈ Set.Icc V (x / U)) :
    ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖ ≤ (1.1 / 8) * ((1 / (2 * Real.sqrt 2)) * (x / Real.sqrt q)
          + (1 / 2) * Real.sqrt (x * W) + x / Real.sqrt W
          + Real.sqrt 2 * Real.sqrt (x * (q : ℝ))) * Real.log W := by
  have hx : 0 ≤ x := by linarith
  have hsum := DyadicBoxTransfer.window_tsum_eq_nested_box x alpha U V W
    (fun d w => ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)) TaoFivePrimes.expCircle
    hx (by linarith) (by linarith) hW
  have hbox := TaoFivePrimes.theorem51_typeII_box_arithmetic x alpha beta a q
    hq haq halpha hbeta U V hU40 hV40 hUx hVx hUV hUV2 W hW
  rw [hsum]
  apply le_trans (le_of_eq ?_) hbox
  congr 1
  unfold Theorem51Dyadic.box
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro w hw
  unfold Theorem51Dyadic.term SmallQSmoothingAux.window
  simp only [Nat.cast_mul]
  split_ifs <;> rfl
#print axioms solution

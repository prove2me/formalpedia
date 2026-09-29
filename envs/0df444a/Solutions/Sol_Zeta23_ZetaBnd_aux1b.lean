-- Prove2me | solution 1 for Zeta23_ZetaBnd_aux1b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:47:38.679507+00:00
-- url     : https://prove2.me/submissions/32c9a255-5108-498e-a016-f7d992ed991d

import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds

-- from Zeta23.FromPNTPlus.ZetaBounds
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaBounds.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes), redirected intra-project
imports to Zeta23.FromPNTPlus.*, and added a (name := ...) tag to the local notation.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics



lemma div_rpow_eq_rpow_neg (a x s : ℝ) (hx : 0 ≤ x) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, Real.rpow_neg hx]



local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta





-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/




-- Alternative cleaner proof using more direct approach


/- The set should be open so that f'(p) = O(1) for all p ∈ U -/









/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0


-- move near `Real.differentiableAt_rpow_const_of_ne`









lemma ZetaSum_aux1_1' {a b x : ℝ} (apos : 0 < a) (hx : x ∈ Icc a b) : 0 < x :=
  lt_of_lt_of_le apos hx.1

lemma ZetaSum_aux1_1 {a b x : ℝ} (apos : 0 < a) (a_lt_b : a < b) (hx : x ∈ [[a, b]]) : 0 < x :=
  lt_of_lt_of_le apos (uIcc_of_le a_lt_b.le ▸ hx).1

lemma ZetaSum_aux1_2 {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (h : c ≠ 0 ∧ 0 ∉ [[a, b]]) :
    ∫ (x : ℝ) in a..b, 1 / x ^ (c+1) = (a ^ (-c) - b ^ (-c)) / c := by
  rw [(by ring : (a ^ (-c) - b ^ (-c)) / c = (b ^ (-c) - a ^ (-c)) / (-c))]
  have := integral_rpow (a := a) (b := b) (r := -c-1) (Or.inr ⟨by simp [h.1], h.2⟩)
  simp only [sub_add_cancel] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro x hx
  have : 0 ≤ x := (ZetaSum_aux1_1 apos a_lt_b hx).le
  simp [div_rpow_eq_rpow_neg _ _ _ this, sub_eq_add_neg, add_comm]

lemma ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩

lemma ZetaSum_aux1_4' (x : ℝ) (hx : 0 < x) (s : ℂ) :
      ‖(⌊x⌋ + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ (s + 1)‖ =
      ‖⌊x⌋ + 1 / 2 - x‖ / x ^ ((s + 1).re) := by
  simp_rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← norm_real]
  simp

lemma ZetaSum_aux1_4 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
  ∫ (x : ℝ) in a..b, ‖(↑⌊x⌋ + (1 : ℝ) / 2 - ↑x) / (x : ℂ) ^ (s + 1)‖ =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re := by
  apply intervalIntegral.integral_congr
  exact fun x hx ↦ ZetaSum_aux1_4' x (ZetaSum_aux1_1 apos a_lt_b hx) s

lemma ZetaSum_aux1_5a {a b : ℝ} (apos : 0 < a) {s : ℂ} (x : ℝ)
  (h : x ∈ Icc a b) : |↑⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1) := by
  apply div_le_div_of_nonneg_right _ _
  · exact le_trans (ZetaSum_aux1_3 x) (by norm_num)
  · apply Real.rpow_nonneg <| le_of_lt (ZetaSum_aux1_1' apos h)

lemma ZetaSum_aux1_5b {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ 1 / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  refine continuousOn_const.div ?_ ?_ |>.intervalIntegrable_of_Icc (le_of_lt a_lt_b)
  · exact continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt <| ZetaSum_aux1_1' apos hx)
  · exact fun x hx h ↦ by rw [Real.rpow_eq_zero] at h <;> linarith [ZetaSum_aux1_1' apos hx]

open MeasureTheory in
lemma measurable_floor_add_half_sub : Measurable fun (u : ℝ) ↦ ↑⌊u⌋ + 1 / 2 - u := by
  refine Measurable.add ?_ measurable_const |>.sub measurable_id
  exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor

open MeasureTheory in
lemma ZetaSum_aux1_5c {a b : ℝ} {s : ℂ} :
    let g : ℝ → ℝ := fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1);
    AEStronglyMeasurable g
      (Measure.restrict volume (Ι a b)) := by
  intro
  refine (Measurable.div ?_ <| measurable_id.pow_const _).aestronglyMeasurable
  exact _root_.continuous_abs.measurable.comp measurable_floor_add_half_sub

lemma ZetaSum_aux1_5d {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  set g : ℝ → ℝ := (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1))
  apply ZetaSum_aux1_5b apos a_lt_b σpos |>.mono_fun ZetaSum_aux1_5c ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, one_div, norm_inv, abs_div, _root_.abs_abs]
  conv => rw [div_eq_mul_inv, ← one_div]; rhs; rw [← one_mul |x ^ (s.re + 1)|⁻¹]
  refine mul_le_mul ?_ (le_refl _) (by simp) <| by norm_num
  exact le_trans (ZetaSum_aux1_3 x) <| by norm_num

lemma ZetaSum_aux1_5 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤
    ∫ (x : ℝ) in a..b, 1 / x ^ (s.re + 1) := by
  apply intervalIntegral.integral_mono_on (le_of_lt a_lt_b) ?_ ?_
  · exact ZetaSum_aux1_5a apos
  · exact ZetaSum_aux1_5d apos a_lt_b σpos
  · exact ZetaSum_aux1_5b apos a_lt_b σpos

lemma ZetaBnd_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    ∫ x in a..b, ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  calc
    _ = ∫ x in a..b, |(⌊x⌋ + 1 / 2 - x)| / x ^ (s+1).re := ZetaSum_aux1_4 apos a_lt_b
    _ ≤ ∫ x in a..b, 1 / x ^ (s.re + 1) := ZetaSum_aux1_5 apos a_lt_b σpos
    _ = (a ^ (-s.re) - b ^ (-s.re)) / s.re := ?_
  refine ZetaSum_aux1_2 (c := s.re) apos a_lt_b ⟨ne_of_gt σpos, ?_⟩
  exact fun h ↦ (lt_self_iff_false 0).mp <| ZetaSum_aux1_1 apos a_lt_b h







lemma ZetaSum_aux2a : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3


lemma integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply MeasureTheory.Integrable.bdd_mul (c := c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor














-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`





































































-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**


-- **End collaboration 6/20/25**



/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/


-- **Begin collaboration with the Alpha Proof team! 5/29/25**



-- **End collaboration**





open ArithmeticFunction (vonMangoldt)
local notation (name := zb_Lambda) "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients


set_option lang.lemmaCmd true
open Complex Topology Filter Interval Set Asymptotics
open MeasureTheory

theorem solution (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ := by
  apply le_trans (by apply norm_integral_le_integral_norm)
  apply le_of_tendsto (x := atTop (α := ℝ)) (f := fun (t : ℝ) ↦ ∫ (x : ℝ) in N..t,
    ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) ?_ ?_
  · apply intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := atTop) (b := id)
      (f := fun (x : ℝ) ↦ ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) N ?_ ?_ |>.congr' ?_
    · filter_upwards [Filter.mem_atTop ((N : ℝ))]
      intro u hu
      simp only [id_eq, intervalIntegral.integral_of_le hu, norm_div]
      apply setIntegral_congr_fun (by simp)
      intro x hx; beta_reduce
      iterate 2 (rw [norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1])])
      simp
    · apply IntegrableOn.integrable ?_ |>.norm
      convert! integrableOn_of_Zeta0_fun (s := σ + t * I) Npos (by simp [σpos]) using 1
      simp_rw [div_eq_mul_inv, cpow_neg]
    · exact fun ⦃_⦄ a ↦ a
  · filter_upwards [mem_atTop (N + 1 : ℝ)] with t ht
    have : (N ^ (-σ) - t ^ (-σ)) / σ ≤ N ^ (-σ) / σ :=
      div_le_div_iff_of_pos_right σpos |>.mpr (by simp [Real.rpow_nonneg (by linarith)])
    apply le_trans ?_ this
    convert! ZetaBnd_aux1a (a := N) (b := t) (by positivity) (by linarith) ?_ <;> simp [σpos]

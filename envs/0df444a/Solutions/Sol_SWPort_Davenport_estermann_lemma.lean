-- Prove2me | solution 1 for SWPort.Davenport.estermann_lemma
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T20:33:43.593812+00:00
-- url     : https://prove2.me/submissions/ffa53d20-8eb5-4d9a-9a39-4c331ec4d55c

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_SWPort_001
import Theorems.Thm_SWPort_Zeta0EqZeta

section
-- module Solutions.Artin.SW.Thm.div_cpow_eq_cpow_neg
namespace SWPort
/-! Ported from prove2.me: `div_cpow_eq_cpow_neg` (be4966ae-1b30-4d65-bb98-30d03e114c5c, statement by Community (Bot)); proof = accepted direct submission 4d79b4ce-d456-43fa-b61c-9b8af3c06771 by Community (Bot). -/

































set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

theorem _root_.SWPort.div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation "ζ₀" => riemannZeta0

-- move near `Real.differentiableAt_rpow_const_of_ne`

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
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.ZetaSum_aux1_3
namespace SWPort
/-! Ported from prove2.me: `ZetaSum_aux1_3` (a1b51cbf-c548-4043-848b-2a87248b8a13, statement by Community (Bot)); proof = accepted direct submission c0efb14b-19c8-4ab7-95eb-07f9a2add18d by Community (Bot). -/

































set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation "ζ₀" => riemannZeta0

-- move near `Real.differentiableAt_rpow_const_of_ne`

theorem _root_.SWPort.ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩

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
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.ZetaSum_aux2a
namespace SWPort
/-! Ported from prove2.me: `ZetaSum_aux2a` (10812a53-124c-49c3-aad9-ce8f1f62847a, statement by Community (Bot)); proof = accepted sketch submission 47f92735-78e5-480f-903b-3e370224ade0 by Community (Bot). -/


































set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation "ζ₀" => riemannZeta0

-- move near `Real.differentiableAt_rpow_const_of_ne`

theorem _root_.SWPort.ZetaSum_aux2a : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3

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
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.integrableOn_of_Zeta0_fun
namespace SWPort
/-! Ported from prove2.me: `integrableOn_of_Zeta0_fun` (eab5ef5d-667e-4a00-83b9-e5a2f58edcde, statement by Community (Bot)); proof = accepted sketch submission 7b0aeed7-ce04-48a0-912e-bc8f8fe44a3f by Community (Bot). -/


































set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation "ζ₀" => riemannZeta0

-- move near `Real.differentiableAt_rpow_const_of_ne`

theorem _root_.SWPort.integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
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
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.riemannZeta0_apply
namespace SWPort
/-! Ported from prove2.me: `riemannZeta0_apply` (e0b33366-b8d1-4db4-a915-200f9a353b1c, statement by Community (Bot)); proof = accepted sketch submission a0302f4c-2b72-45ca-8811-87f70821e355 by Community (Bot). -/


































set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation "ζ₀" => riemannZeta0

theorem _root_.SWPort.riemannZeta0_apply (N : ℕ) (s : ℂ) : ζ₀ N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [riemannZeta0, div_cpow_eq_cpow_neg]; ring

-- move near `Real.differentiableAt_rpow_const_of_ne`

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
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_riemannZeta_neg_of_lt_one
namespace SWPort
/-! Ported from prove2.me: `Davenport.riemannZeta_neg_of_lt_one` (0c6ea1ff-5232-48a1-83b3-866b42016549, statement by alya); proof = accepted sketch submission b050c9aa-8bd6-400d-960d-8996b7e7aab7 by alya. -/














open Finset DirichletCharacter

namespace DavenportZetaNegAux

/-- The Euler–Maclaurin integrand is (the coercion of) a real-valued function. -/
private lemma pointwise (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-((σ : ℂ) + 1))
      = ((((⌊x⌋ : ℝ) + 1 / 2 - x) * x ^ (-(σ + 1)) : ℝ) : ℂ) := by
  have h1 : (-((σ : ℂ) + 1)) = ((-(σ + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_cpow hx.le]
  push_cast
  ring

/-- The sawtooth function is bounded by `1/2`. -/
private lemma floor_bound (x : ℝ) : |(⌊x⌋ : ℝ) + 1 / 2 - x| ≤ 1 / 2 := by
  rw [abs_le]
  constructor
  · linarith [Int.lt_floor_add_one x]
  · linarith [Int.floor_le x]

end DavenportZetaNegAux

theorem _root_.SWPort.Davenport.riemannZeta_neg_of_lt_one (σ : ℝ) (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
    (riemannZeta σ).im = 0 ∧ (riemannZeta σ).re < 0 := by
  have hσne : (σ : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hσ₀.ne'
  have hne1 : (σ : ℂ) ≠ 1 := by
    simp only [ne_eq, Complex.ofReal_eq_one]
    exact hσ₁.ne
  have hre : (0 : ℝ) < ((σ : ℂ)).re := by simpa using hσ₀
  have hσ0' : σ ≠ 0 := hσ₀.ne'
  set J : ℝ := ∫ x in Set.Ioi (1 : ℝ), (((⌊x⌋ : ℝ) + 1 / 2 - x) * x ^ (-(σ + 1))) with hJdef
  -- The tail integral is real.
  have hIeq : (∫ x in Set.Ioi (1 : ℝ),
        ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-((σ : ℂ) + 1))) = ((J : ℝ) : ℂ) := by
    rw [hJdef, ← integral_complex_ofReal]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    exact DavenportZetaNegAux.pointwise σ (by linarith)
  -- Euler–Maclaurin with N = 1.
  have hkey : riemannZeta (σ : ℂ) = ((1 / 2 - 1 / (1 - σ) + σ * J : ℝ) : ℂ) := by
    rw [← Zeta0EqZeta (N := 1) Nat.one_pos hre hne1, riemannZeta0_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      Complex.zero_cpow hσne, Complex.one_cpow, div_zero, zero_add, div_one]
    rw [hIeq]
    push_cast
    ring
  refine ⟨by rw [hkey]; exact Complex.ofReal_im _, ?_⟩
  rw [hkey, Complex.ofReal_re]
  -- Bound the tail integral.
  have hIntF : MeasureTheory.IntegrableOn
      (fun x : ℝ => ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-((σ : ℂ) + 1)))
      (Set.Ioi (1 : ℝ)) MeasureTheory.volume := by
    have h := integrableOn_of_Zeta0_fun (N := 1) Nat.one_pos hre
    simpa only [Nat.cast_one] using h
  have hIntRpow : MeasureTheory.IntegrableOn (fun x : ℝ => (1 / 2 : ℝ) * x ^ (-(σ + 1)))
      (Set.Ioi (1 : ℝ)) MeasureTheory.volume :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  have hnormle : ∀ x ∈ Set.Ioi (1 : ℝ),
      ‖((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-((σ : ℂ) + 1))‖
        ≤ (1 / 2 : ℝ) * x ^ (-(σ + 1)) := by
    intro x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : (0 : ℝ) < x := by linarith
    rw [DavenportZetaNegAux.pointwise σ hx0, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact mul_le_mul_of_nonneg_right (DavenportZetaNegAux.floor_bound x)
      (Real.rpow_nonneg hx0.le _)
  have hb3 : (∫ x in Set.Ioi (1 : ℝ), (1 / 2 : ℝ) * x ^ (-(σ + 1))) = 1 / (2 * σ) := by
    rw [MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith : -(σ + 1) < -1) one_pos]
    have h : -(σ + 1) + 1 = -σ := by ring
    rw [h, Real.one_rpow]
    field_simp
  have hJabs : |J| ≤ 1 / (2 * σ) := by
    calc |J| = ‖((J : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ = ‖∫ x in Set.Ioi (1 : ℝ),
            ((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-((σ : ℂ) + 1))‖ := by rw [hIeq]
      _ ≤ ∫ x in Set.Ioi (1 : ℝ),
            ‖((⌊x⌋ : ℂ) + 1 / 2 - (x : ℂ)) * (x : ℂ) ^ (-((σ : ℂ) + 1))‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ x in Set.Ioi (1 : ℝ), (1 / 2 : ℝ) * x ^ (-(σ + 1)) :=
          MeasureTheory.setIntegral_mono_on hIntF.norm hIntRpow measurableSet_Ioi hnormle
      _ = 1 / (2 * σ) := hb3
  have hσJ : σ * J ≤ 1 / 2 := by
    have h1 : σ * J ≤ σ * |J| := mul_le_mul_of_nonneg_left (le_abs_self J) hσ₀.le
    have h2 : σ * |J| ≤ σ * (1 / (2 * σ)) := mul_le_mul_of_nonneg_left hJabs hσ₀.le
    have h3 : σ * (1 / (2 * σ)) = 1 / 2 := by field_simp
    linarith
  have hinv : 1 < 1 / (1 - σ) := by
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 1 - σ)]
    linarith
  linarith

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Zeta23_RvM_norm_riemannZeta_le_of_re_pos
alias SWPort.Zeta23.RvM.norm_riemannZeta_le_of_re_pos := SWPort.Z.Zeta23.RvM.norm_riemannZeta_le_of_re_pos
end

section
-- module Solutions.Artin.SW.Thm.Davenport_estermann_lemma
namespace SWPort
/-! Ported from prove2.me: `Davenport.estermann_lemma` (478fdf36-d856-42b6-a465-a4a0d385c671, statement by alya); proof = accepted sketch submission c69ce056-e988-46e0-bf72-1469a42d6e88 by alya. -/












open Finset DirichletCharacter

namespace DavenportAux.Estermann

open Complex Topology Filter
open scoped ComplexOrder

/-! ### The entire completion of `ζ s - 1/(s-1)` -/

private lemma zeta0_of_ne {s : ℂ} (hs : s ≠ 1) : zeta0 s = riemannZeta s - 1 / (s - 1) :=
  Function.update_of_ne hs _ _

private lemma zeta0_differentiable : Differentiable ℂ zeta0 := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have h1 : DifferentiableAt ℂ (fun s : ℂ => riemannZeta s - 1 / (s - 1)) t :=
        (differentiableAt_riemannZeta ht).sub
          ((differentiableAt_const 1).div ((differentiableAt_id).sub (differentiableAt_const 1))
            (sub_ne_zero.mpr ht))
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ne.mem_nhds ht] with u hu
      exact zeta0_of_ne hu
    · rw [zeta0, continuousAt_update_same]
      exact tendsto_riemannZeta_sub_one_div
  · have h1 : DifferentiableAt ℂ (fun s : ℂ => riemannZeta s - 1 / (s - 1)) s :=
      (differentiableAt_riemannZeta hs).sub
        ((differentiableAt_const 1).div ((differentiableAt_id).sub (differentiableAt_const 1))
          (sub_ne_zero.mpr hs))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hs] with u hu
    exact zeta0_of_ne hu

/-! ### The auxiliary function `G` -/

private lemma one_mem_ball : (1 : ℂ) ∈ Metric.ball (2 : ℂ) (3 / 2) := by
  simp only [Metric.mem_ball, Complex.dist_eq]
  norm_num

private lemma G_diff (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.closedBall (2 : ℂ) (3 / 2))) :
    DifferentiableOn ℂ (fun s => zeta0 s * f s + dslope f 1 s)
      (Metric.closedBall (2 : ℂ) (3 / 2)) := by
  have hnhds : Metric.closedBall (2 : ℂ) (3 / 2) ∈ 𝓝 (1 : ℂ) :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds one_mem_ball) Metric.ball_subset_closedBall
  exact (zeta0_differentiable.differentiableOn.mul hf).add
    ((Complex.differentiableOn_dslope hnhds).mpr hf)

private lemma G_eq (f : ℂ → ℂ) {s : ℂ} (hs : s ≠ 1) :
    zeta0 s * f s + dslope f 1 s = riemannZeta s * f s - f 1 / (s - 1) := by
  rw [zeta0_of_ne hs, dslope_of_ne _ hs]
  simp only [slope_def_field]
  field_simp
  ring

private lemma sphere_bound (f : ℂ → ℂ) (M : ℝ)
    (hfM : ∀ s ∈ Metric.closedBall (2 : ℂ) (3 / 2), ‖f s‖ ≤ M)
    {s : ℂ} (hs : s ∈ Metric.sphere (2 : ℂ) (3 / 2)) :
    ‖zeta0 s * f s + dslope f 1 s‖ ≤ 12 * M := by
  have hd : ‖s - 2‖ = 3 / 2 := by
    rw [← Complex.dist_eq]; exact hs
  have hs1 : ‖(1 : ℂ) - s‖ ≥ 1 / 2 := by
    have h1 : ‖s - 2‖ - ‖(1 : ℂ) - 2‖ ≤ ‖s - 1‖ := by
      have := norm_sub_norm_le (s - 2) ((1 : ℂ) - 2)
      simpa using this
    have h2 : ‖(1 : ℂ) - 2‖ = 1 := by norm_num
    rw [h2, hd] at h1
    rw [norm_sub_rev]
    linarith
  have hsne : s ≠ 1 := by
    intro h; rw [h] at hs1; simp at hs1; linarith
  have hre : (1 : ℝ) / 2 ≤ s.re := by
    have h := Complex.abs_re_le_norm (s - 2)
    rw [hd] at h
    simp only [Complex.sub_re, Complex.re_ofNat] at h
    have h' := abs_le.mp h
    linarith [h'.1]
  have hnorm : ‖s‖ ≤ 7 / 2 := by
    have h : ‖s‖ = ‖(s - 2) + 2‖ := by ring_nf
    rw [h]
    calc ‖(s - 2) + 2‖ ≤ ‖s - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 / 2 + 2 := by rw [hd]; norm_num
      _ = 7 / 2 := by norm_num
  have hz : ‖riemannZeta s‖ ≤ 10 := by
    have hb := Zeta23.RvM.norm_riemannZeta_le_of_re_pos (s := s) (by linarith) hsne
    have h1 : 1 / ‖(1 : ℂ) - s‖ ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have h2 : ‖s‖ / s.re ≤ 7 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hfM 2 (Metric.mem_closedBall_self (by norm_num)))
  have hfs : ‖f s‖ ≤ M := hfM s (by
    simp only [Metric.mem_closedBall]
    rw [← Complex.dist_eq] at hd
    exact le_of_eq hd)
  have hf1 : ‖f 1‖ ≤ M := hfM 1 (Metric.ball_subset_closedBall one_mem_ball)
  rw [G_eq f hsne]
  calc ‖riemannZeta s * f s - f 1 / (s - 1)‖
      ≤ ‖riemannZeta s * f s‖ + ‖f 1 / (s - 1)‖ := norm_sub_le _ _
    _ ≤ 10 * M + 2 * M := by
        gcongr
        · rw [norm_mul]
          exact mul_le_mul hz hfs (norm_nonneg _) (by norm_num)
        · rw [norm_div, norm_sub_rev]
          rw [div_le_iff₀ (by linarith)]
          nlinarith
    _ ≤ 12 * M := by linarith

/-! ### Numerical lemmas -/

private lemma log_gt : (0.35 : ℝ) < Real.log (10 / 7) := by
  have h1 : Real.exp 7 < (10 / 7 : ℝ) ^ (20 : ℕ) := by
    have h := Real.exp_one_lt_d9
    have h2 : Real.exp 7 = (Real.exp 1) ^ (7 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    calc (Real.exp 1) ^ (7 : ℕ) < (2.7182818286 : ℝ) ^ (7 : ℕ) :=
          pow_lt_pow_left₀ h (Real.exp_nonneg 1) (by norm_num)
      _ < (10 / 7 : ℝ) ^ (20 : ℕ) := by norm_num
  have h3 : (7 : ℝ) < Real.log ((10 / 7 : ℝ) ^ (20 : ℕ)) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact h1
  rw [Real.log_pow] at h3
  push_cast at h3
  linarith

private lemma rpow_bound : (80 : ℝ) ^ ((1 : ℝ) / 7) ≤ 1.875 := by
  have h : (80 : ℝ) ≤ (1.875 : ℝ) ^ (7 : ℕ) := by norm_num
  have h2 := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 80) h (by norm_num : (0 : ℝ) ≤ 1 / 7)
  calc (80 : ℝ) ^ ((1 : ℝ) / 7) ≤ ((1.875 : ℝ) ^ (7 : ℕ)) ^ ((1 : ℝ) / 7) := h2
    _ = 1.875 := by
        rw [← Real.rpow_natCast (1.875 : ℝ) 7, ← Real.rpow_mul (by norm_num)]
        norm_num

private lemma tail_le (M : ℝ) (hM : 1 ≤ M) (K : ℕ)
    (hK : K = ⌊Real.log (80 * M) / Real.log (10 / 7)⌋₊) :
    40 * M * (7 / 10 : ℝ) ^ (K + 1) ≤ 1 / 2 := by
  set L : ℝ := Real.log (10 / 7) with hL
  have hL0 : (0 : ℝ) < L := lt_trans (by norm_num) log_gt
  have hx : Real.log (80 * M) / L < (K : ℝ) + 1 := by
    rw [hK]; exact Nat.lt_floor_add_one _
  have hlog : Real.log (80 * M) < ((K : ℝ) + 1) * L := by
    rw [div_lt_iff₀ hL0] at hx; exact hx
  have hpow : Real.log ((10 / 7 : ℝ) ^ (K + 1)) = ((K : ℝ) + 1) * L := by
    rw [Real.log_pow]; push_cast; ring
  have hM80 : (0 : ℝ) < 80 * M := by linarith
  have hlt : 80 * M < (10 / 7 : ℝ) ^ (K + 1) := by
    have h1 : Real.log (80 * M) < Real.log ((10 / 7 : ℝ) ^ (K + 1)) := by rw [hpow]; exact hlog
    exact (Real.log_lt_log_iff hM80 (by positivity)).mp h1
  have hinv : (7 / 10 : ℝ) ^ (K + 1) = ((10 / 7 : ℝ) ^ (K + 1))⁻¹ := by
    rw [← inv_pow]; norm_num
  rw [hinv, mul_inv_le_iff₀ (by positivity)]
  nlinarith [pow_pos (show (0 : ℝ) < 10 / 7 by norm_num) (K + 1)]

private lemma pow_le (M : ℝ) (hM : 1 ≤ M) (σ : ℝ) (hσ : 19 / 20 ≤ σ) (hσ₁ : σ < 1) (K : ℕ)
    (hK : K = ⌊Real.log (80 * M) / Real.log (10 / 7)⌋₊) :
    (2 - σ) ^ (K + 1) ≤ 2 * M ^ (3 * (1 - σ)) := by
  set L : ℝ := Real.log (10 / 7) with hL
  have hL0 : (0 : ℝ) < L := lt_trans (by norm_num) log_gt
  have hlog80 : (0 : ℝ) ≤ Real.log (80 * M) := by
    apply Real.log_nonneg; linarith
  have hxnn : (0 : ℝ) ≤ Real.log (80 * M) / L := by positivity
  have hKle : (K : ℝ) ≤ Real.log (80 * M) / L := by
    rw [hK]; exact Nat.floor_le hxnn
  set y : ℝ := (1 - σ) / L with hy
  have hy0 : 0 < y := div_pos (by linarith) hL0
  have hy7 : y ≤ 1 / 7 := by
    rw [hy, div_le_div_iff₀ hL0 (by norm_num)]
    nlinarith [log_gt]
  have hy3 : y ≤ 3 * (1 - σ) := by
    rw [hy, div_le_iff₀ hL0]
    nlinarith [log_gt]
  have h1 : (2 - σ) ^ K ≤ Real.exp ((K : ℝ) * (1 - σ)) := by
    have hbase : (2 - σ) ≤ Real.exp (1 - σ) := by
      have := Real.add_one_le_exp (1 - σ)
      linarith
    calc (2 - σ) ^ K ≤ (Real.exp (1 - σ)) ^ K := pow_le_pow_left₀ (by linarith) hbase K
      _ = Real.exp ((K : ℝ) * (1 - σ)) := by rw [← Real.exp_nat_mul]
  have h2 : Real.exp ((K : ℝ) * (1 - σ)) ≤ (80 * M) ^ y := by
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    rw [hy, show Real.log (80 * M) * ((1 - σ) / L) = (Real.log (80 * M) / L) * (1 - σ) by ring]
    exact mul_le_mul_of_nonneg_right hKle (by linarith)
  have h3 : (80 * M) ^ y ≤ 1.875 * M ^ (3 * (1 - σ)) := by
    rw [Real.mul_rpow (by norm_num) (by linarith)]
    have hA : (80 : ℝ) ^ y ≤ 1.875 :=
      le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hy7) rpow_bound
    have hB : M ^ y ≤ M ^ (3 * (1 - σ)) := Real.rpow_le_rpow_of_exponent_le hM hy3
    have hB0 : (0 : ℝ) < M ^ y := Real.rpow_pos_of_pos (by linarith) y
    nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < 80 by norm_num) y]
  have hMpow : (0 : ℝ) < M ^ (3 * (1 - σ)) := Real.rpow_pos_of_pos (by linarith) _
  calc (2 - σ) ^ (K + 1) = (2 - σ) * (2 - σ) ^ K := by ring
    _ ≤ (21 / 20) * (1.875 * M ^ (3 * (1 - σ))) :=
        mul_le_mul (by linarith) (le_trans h1 (le_trans h2 h3))
          (pow_nonneg (by linarith) K) (by norm_num)
    _ ≤ 2 * M ^ (3 * (1 - σ)) := by nlinarith

end DavenportAux.Estermann

open DavenportAux.Estermann
open Topology
open scoped ComplexOrder

theorem _root_.SWPort.Davenport.estermann_lemma_oai (f : ℂ → ℂ) (M : ℝ) (r : ℕ → ℝ) (hM : 1 ≤ M)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (2 : ℂ) (3 / 2)))
    (hfM : ∀ s ∈ Metric.closedBall (2 : ℂ) (3 / 2), ‖f s‖ ≤ M)
    (hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (r n : ℂ)) s)
    (hF : ∀ s : ℂ, 1 < s.re → riemannZeta s * f s = LSeries (fun n => (r n : ℂ)) s)
    (hr₁ : r 1 = 1) (hr : ∀ n, 0 ≤ r n)
    (σ : ℝ) (hσ : 19 / 20 ≤ σ) (hσ₁ : σ < 1) (hfσ : 0 ≤ (f σ).re) :
    (1 / 4) * (1 - σ) * M ^ (-(3 * (1 - σ))) ≤ (f 1).re := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have h2σ : (0 : ℝ) < 2 - σ := by linarith
  have h2σ' : 2 - σ ≤ 21 / 20 := by linarith
  -- the coefficient sequence
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ, a = fun n => (r n : ℂ) := ⟨_, rfl⟩
  rw [← ha] at hsum hF
  have ha0 : (0 : ℕ → ℂ) ≤ a := by
    intro n
    rw [ha]
    exact Complex.zero_le_real.mpr (hr n)
  have habs : LSeries.abscissaOfAbsConv a ≤ ((1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => hsum (y : ℂ) (by simpa using hy))
  have habs2 : LSeries.abscissaOfAbsConv a < ((2 : ℝ) : EReal) :=
    lt_of_le_of_lt habs (by exact_mod_cast (by norm_num : (1 : ℝ) < 2))
  -- the auxiliary function
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℂ, G = fun s => zeta0 s * f s + dslope f 1 s := ⟨_, rfl⟩
  have hGdiff : DifferentiableOn ℂ G (Metric.closedBall (2 : ℂ) (3 / 2)) := by
    rw [hGdef]; exact G_diff f hf
  have hGsphere : ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G z‖ ≤ 12 * M := by
    intro z hz; rw [hGdef]; exact sphere_bound f M hfM hz
  -- Cauchy estimates
  have hdcc : DiffContOnCl ℂ G (Metric.ball (2 : ℂ) (3 / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rwa [closure_ball _ (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  have hCauchy : ∀ k : ℕ, ‖iteratedDeriv k G 2‖
      ≤ (Nat.factorial k : ℝ) * (12 * M) / (3 / 2) ^ k := fun k =>
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num) hdcc hGsphere
  -- Taylor series
  have hσball : ((σ : ℝ) : ℂ) ∈ Metric.ball (2 : ℂ) (3 / 2) := by
    simp only [Metric.mem_ball, Complex.dist_eq]
    rw [show ((σ : ℂ) - 2) = ((σ - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hTaylor := Complex.hasSum_taylorSeries_on_ball
    (hGdiff.mono Metric.ball_subset_closedBall) hσball
  simp only [smul_eq_mul] at hTaylor
  -- identification of the Taylor coefficients
  have hEq : G =ᶠ[𝓝 (2 : ℂ)] (fun s => LSeries a s - f 1 * (s - 1)⁻¹) := by
    have hmem : Metric.ball (2 : ℂ) 1 ∈ 𝓝 (2 : ℂ) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)
    filter_upwards [hmem] with s hs
    have hd : ‖s - 2‖ < 1 := by rw [← Complex.dist_eq]; exact hs
    have hsre : 1 < s.re := by
      have h := Complex.abs_re_le_norm (s - 2)
      simp only [Complex.sub_re, Complex.re_ofNat] at h
      have h' := abs_lt.mp (lt_of_le_of_lt h hd)
      linarith [h'.1]
    have hsne : s ≠ 1 := by
      intro h; rw [h] at hsre; simp at hsre
    rw [hGdef]
    simp only
    rw [G_eq f hsne, hF s hsre, div_eq_mul_inv]
  have hcoef : ∀ k : ℕ, iteratedDeriv k G 2
      = iteratedDeriv k (LSeries a) 2 - f 1 * ((-1) ^ k * (Nat.factorial k : ℂ)) := by
    intro k
    rw [Filter.EventuallyEq.iteratedDeriv_eq k hEq]
    have h2 : (2 : ℂ) ∈ {s : ℂ | LSeries.abscissaOfAbsConv a < s.re} := by
      simp only [Set.mem_setOf_eq, Complex.re_ofNat]
      refine lt_of_le_of_lt habs ?_
      exact_mod_cast (by norm_num : (1 : ℝ) < 2)
    have hL : ContDiffAt ℂ k (LSeries a) 2 :=
      ((LSeries_analyticOnNhd a) 2 h2).contDiffAt.of_le (by exact_mod_cast le_top)
    have hne : (2 : ℂ) - 1 ≠ 0 := by norm_num
    have hI : ContDiffAt ℂ k (fun s : ℂ => f 1 * (s - 1)⁻¹) 2 :=
      contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv hne)
    rw [iteratedDeriv_fun_sub hL hI]
    congr 1
    rw [iteratedDeriv_const_mul_field]
    congr 1
    have hiter := iter_deriv_inv_linear_sub (𝕜 := ℂ) k 1 1
    simp only [one_mul, one_pow] at hiter
    rw [iteratedDeriv_eq_iterate, hiter]
    norm_num
  -- nonnegativity of the alternating derivatives
  have hcnn : ∀ k : ℕ, (0 : ℂ) ≤ (-1) ^ k * iteratedDeriv k (LSeries a) 2 := by
    intro k
    have h := LSeries.iteratedDeriv_alternating ha0 habs2 k
    simpa using h
  -- the real coefficients
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, b = fun k =>
      ((Nat.factorial k : ℝ))⁻¹ * ((-1 : ℂ) ^ k * iteratedDeriv k (LSeries a) 2).re := ⟨_, rfl⟩
  have hbnn : ∀ k, 0 ≤ b k := by
    intro k
    rw [hb]
    exact mul_nonneg (by positivity) ((Complex.nonneg_iff.mp (hcnn k)).1)
  -- the Taylor terms
  have hterm : ∀ k : ℕ, ((Nat.factorial k : ℂ))⁻¹ * (((σ : ℂ) - 2) ^ k * iteratedDeriv k G 2)
      = (((2 - σ) ^ k : ℝ) : ℂ) * ((b k : ℂ) - f 1) := by
    intro k
    have hfacne : ((Nat.factorial k : ℂ)) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos k).ne'
    have hcre : ((-1 : ℂ) ^ k * iteratedDeriv k (LSeries a) 2)
        = ((((-1 : ℂ) ^ k * iteratedDeriv k (LSeries a) 2).re : ℝ) : ℂ) := by
      have h := Complex.nonneg_iff.mp (hcnn k)
      apply Complex.ext
      · simp
      · simpa using h.2.symm
    have hbk : ((b k : ℝ) : ℂ)
        = ((Nat.factorial k : ℂ))⁻¹ * ((-1 : ℂ) ^ k * iteratedDeriv k (LSeries a) 2) := by
      simp only [hb]
      push_cast
      rw [← hcre]
    have hsgn : ((σ : ℂ) - 2) ^ k = (-1 : ℂ) ^ k * (((2 - σ) ^ k : ℝ) : ℂ) := by
      push_cast
      rw [← mul_pow]
      ring_nf
    have hsq : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
      rw [← mul_pow]; norm_num
    rw [hcoef k, hsgn]
    set c := iteratedDeriv k (LSeries a) 2 with hcdef
    set N := ((Nat.factorial k : ℂ)) with hNdef
    set w := (((2 - σ) ^ k : ℝ) : ℂ) with hwdef
    set u := ((-1 : ℂ) ^ k) with hudef
    have expand : N⁻¹ * (u * w * (c - f 1 * (u * N)))
        = w * (N⁻¹ * (u * c)) - w * f 1 * ((u * u) * (N⁻¹ * N)) := by
      field_simp
    rw [expand, hsq, inv_mul_cancel₀ hfacne, hbk]
    ring
  -- real part of the Taylor series
  have htre : ∀ k : ℕ,
      (((Nat.factorial k : ℂ))⁻¹ * (((σ : ℂ) - 2) ^ k * iteratedDeriv k G 2)).re
      = (2 - σ) ^ k * (b k - (f 1).re) := by
    intro k
    rw [hterm k, Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re]
  have hS : HasSum (fun k : ℕ => (2 - σ) ^ k * (b k - (f 1).re)) (G σ).re := by
    have h := Complex.hasSum_re hTaylor
    refine h.congr_fun ?_
    intro k
    exact (htre k).symm
  -- norm bound on the terms
  have hnormterm : ∀ k : ℕ, |(2 - σ) ^ k * (b k - (f 1).re)| ≤ 12 * M * (7 / 10) ^ k := by
    intro k
    have hfacR : (0 : ℝ) < (Nat.factorial k : ℝ) := by
      exact_mod_cast Nat.factorial_pos k
    have hn2 : ‖((σ : ℂ) - 2) ^ k‖ = (2 - σ) ^ k := by
      rw [norm_pow,
        show ((σ : ℂ) - 2) = ((σ - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      congr 1
      ring
    have hkey : ‖((Nat.factorial k : ℂ))⁻¹ * (((σ : ℂ) - 2) ^ k * iteratedDeriv k G 2)‖
        ≤ 12 * M * (7 / 10) ^ k := by
      rw [norm_mul, norm_mul, hn2, norm_inv, Complex.norm_natCast]
      have hC := hCauchy k
      have hstep : (2 - σ) ^ k * ‖iteratedDeriv k G 2‖
          ≤ (2 - σ) ^ k * ((Nat.factorial k : ℝ) * (12 * M) / (3 / 2) ^ k) := by
        apply mul_le_mul_of_nonneg_left hC (by positivity)
      have hfin : ((Nat.factorial k : ℝ))⁻¹ * ((2 - σ) ^ k *
          ((Nat.factorial k : ℝ) * (12 * M) / (3 / 2) ^ k)) ≤ 12 * M * (7 / 10) ^ k := by
        rw [div_eq_mul_inv]
        have hpow : (2 - σ) ^ k * ((3 / 2 : ℝ) ^ k)⁻¹ ≤ (7 / 10 : ℝ) ^ k := by
          rw [← inv_pow, ← mul_pow]
          apply pow_le_pow_left₀ (by positivity)
          rw [show ((3 / 2 : ℝ))⁻¹ = 2 / 3 by norm_num]
          linarith
        have heq : ((Nat.factorial k : ℝ))⁻¹ * ((2 - σ) ^ k *
            ((Nat.factorial k : ℝ) * (12 * M) * ((3 / 2 : ℝ) ^ k)⁻¹))
            = (12 * M) * ((2 - σ) ^ k * ((3 / 2 : ℝ) ^ k)⁻¹) := by
          field_simp
        rw [heq]
        exact mul_le_mul_of_nonneg_left hpow (by linarith)
      calc ((Nat.factorial k : ℝ))⁻¹ * ((2 - σ) ^ k * ‖iteratedDeriv k G 2‖)
          ≤ ((Nat.factorial k : ℝ))⁻¹ * ((2 - σ) ^ k *
              ((Nat.factorial k : ℝ) * (12 * M) / (3 / 2) ^ k)) := by
            apply mul_le_mul_of_nonneg_left hstep (by positivity)
        _ ≤ 12 * M * (7 / 10) ^ k := hfin
    calc |(2 - σ) ^ k * (b k - (f 1).re)|
        = |(((Nat.factorial k : ℂ))⁻¹ * (((σ : ℂ) - 2) ^ k * iteratedDeriv k G 2)).re| := by
          rw [htre k]
      _ ≤ ‖((Nat.factorial k : ℂ))⁻¹ * (((σ : ℂ) - 2) ^ k * iteratedDeriv k G 2)‖ :=
          Complex.abs_re_le_norm _
      _ ≤ 12 * M * (7 / 10) ^ k := hkey
  -- split the series
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌊Real.log (80 * M) / Real.log (10 / 7)⌋₊ := ⟨_, rfl⟩
  have hsplit : HasSum (fun n : ℕ => (2 - σ) ^ (n + (K + 1)) * (b (n + (K + 1)) - (f 1).re))
      ((G σ).re - ∑ i ∈ Finset.range (K + 1), (2 - σ) ^ i * (b i - (f 1).re)) :=
    (hasSum_nat_add_iff' (K + 1)).mpr hS
  have hgeo : HasSum (fun n : ℕ => -(12 * M * (7 / 10) ^ (K + 1) * (7 / 10 : ℝ) ^ n))
      (-(12 * M * (7 / 10) ^ (K + 1) * (1 - 7 / 10)⁻¹)) :=
    (((hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left
      (12 * M * (7 / 10 : ℝ) ^ (K + 1)))).neg
  have htail : -(12 * M * (7 / 10 : ℝ) ^ (K + 1) * (1 - 7 / 10)⁻¹)
      ≤ (G σ).re - ∑ i ∈ Finset.range (K + 1), (2 - σ) ^ i * (b i - (f 1).re) := by
    refine hasSum_le ?_ hgeo hsplit
    intro n
    have h := hnormterm (n + (K + 1))
    have h' := (abs_le.mp h).1
    calc -(12 * M * (7 / 10 : ℝ) ^ (K + 1) * (7 / 10 : ℝ) ^ n)
        = -(12 * M * (7 / 10 : ℝ) ^ (n + (K + 1))) := by rw [pow_add]; ring
      _ ≤ (2 - σ) ^ (n + (K + 1)) * (b (n + (K + 1)) - (f 1).re) := h'
  have htail2 : 12 * M * (7 / 10 : ℝ) ^ (K + 1) * (1 - 7 / 10)⁻¹ ≤ 1 / 2 := by
    have h := tail_le M hM K hK
    have : (12 : ℝ) * M * (7 / 10 : ℝ) ^ (K + 1) * (1 - 7 / 10)⁻¹
        = 40 * M * (7 / 10 : ℝ) ^ (K + 1) := by
      norm_num; ring
    rw [this]; exact h
  -- lower bound for the partial sum
  have hpart : 1 - (f 1).re * (∑ i ∈ Finset.range (K + 1), (2 - σ) ^ i)
      ≤ ∑ i ∈ Finset.range (K + 1), (2 - σ) ^ i * (b i - (f 1).re) := by
    have hnn : ∀ i ∈ Finset.range (K + 1),
        0 ≤ (2 - σ) ^ i * (b i - (f 1).re) + (f 1).re * (2 - σ) ^ i := by
      intro i _
      have : (2 - σ) ^ i * (b i - (f 1).re) + (f 1).re * (2 - σ) ^ i = (2 - σ) ^ i * b i := by ring
      rw [this]
      exact mul_nonneg (pow_nonneg (by linarith) i) (hbnn i)
    have hsingle := Finset.single_le_sum hnn (Finset.mem_range.mpr (Nat.succ_pos K))
    have hb0 : 1 ≤ b 0 := by
      -- b 0 = (LSeries a 2).re ≥ 1
      have hsum2 : LSeriesSummable a 2 := hsum 2 (by norm_num)
      have hnn2 : ∀ n : ℕ, (0 : ℂ) ≤ LSeries.term a 2 n := by
        intro n
        have := LSeries.term_nonneg (a := a) (n := n) (ha0 n) 2
        simpa using this
      have hle : LSeries.term a 2 1 ≤ LSeries a 2 := hsum2.le_tsum 1 (fun j _ => hnn2 j)
      have hone : LSeries.term a 2 1 = 1 := by
        rw [LSeries.term_of_ne_zero one_ne_zero, ha]
        simp [hr₁]
      rw [hone] at hle
      have hre1 : (1 : ℝ) ≤ (LSeries a 2).re := by
        have := Complex.le_def.mp hle
        simpa using this.1
      rw [hb]
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero, one_mul]
      rw [iteratedDeriv_zero]
      exact hre1
    have hsum_eq : ∑ i ∈ Finset.range (K + 1),
        ((2 - σ) ^ i * (b i - (f 1).re) + (f 1).re * (2 - σ) ^ i)
        = (∑ i ∈ Finset.range (K + 1), (2 - σ) ^ i * (b i - (f 1).re))
          + (f 1).re * (∑ i ∈ Finset.range (K + 1), (2 - σ) ^ i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsum_eq] at hsingle
    simp only [pow_zero, one_mul] at hsingle
    linarith
  -- geometric sum
  have hgeomsum : ∑ i ∈ Finset.range (K + 1), (2 - σ) ^ i
      = ((2 - σ) ^ (K + 1) - 1) / (1 - σ) := by
    rw [geom_sum_eq (by intro h; linarith)]
    congr 1
    ring
  -- the upper bound from the negativity of ζ on (0,1)
  have hσCne : ((σ : ℝ) : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at this
    linarith
  have hSle : (G σ).re ≤ (f 1).re / (1 - σ) := by
    have hGσ : G ((σ : ℝ) : ℂ)
        = riemannZeta ((σ : ℝ) : ℂ) * f ((σ : ℝ) : ℂ) - f 1 / (((σ : ℝ) : ℂ) - 1) := by
      rw [hGdef]; exact G_eq f hσCne
    have hzeta := Davenport.riemannZeta_neg_of_lt_one σ (by linarith) hσ₁
    rw [hGσ]
    have hden : (((σ : ℝ) : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hden]
    simp only [Complex.sub_re, Complex.mul_re, hzeta.1, zero_mul, sub_zero,
      Complex.div_ofReal_re]
    have hX : (riemannZeta ((σ : ℝ) : ℂ)).re * (f ((σ : ℝ) : ℂ)).re ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inr ⟨hzeta.2.le, hfσ⟩)
    have hneg : (f 1).re / (σ - 1) = -((f 1).re / (1 - σ)) := by
      rw [show (σ - 1 : ℝ) = -(1 - σ) by ring, div_neg]
    rw [hneg]
    linarith
  -- combine
  have hσ0 : (0 : ℝ) < 1 - σ := by linarith
  have hQ : (0 : ℝ) < (2 - σ) ^ (K + 1) := pow_pos h2σ _
  have hmain : (1 - σ) / 2 ≤ (f 1).re * (2 - σ) ^ (K + 1) := by
    have h1 : 1 / 2 - (f 1).re * (((2 - σ) ^ (K + 1) - 1) / (1 - σ)) ≤ (G σ).re := by
      rw [← hgeomsum]
      linarith
    have h2 : (f 1).re / (1 - σ) + (f 1).re * (((2 - σ) ^ (K + 1) - 1) / (1 - σ))
        = (f 1).re * (2 - σ) ^ (K + 1) / (1 - σ) := by
      field_simp
      ring
    have h3 : 1 / 2 ≤ (f 1).re * (2 - σ) ^ (K + 1) / (1 - σ) := by
      rw [← h2]; linarith [hSle, h1]
    rw [le_div_iff₀ hσ0] at h3
    linarith
  have hApos : 0 < (f 1).re := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hQ2 : (2 - σ) ^ (K + 1) ≤ 2 * M ^ (3 * (1 - σ)) := pow_le M hM σ hσ hσ₁ K hK
  have hW : (0 : ℝ) < M ^ (3 * (1 - σ)) := Real.rpow_pos_of_pos hM0 _
  have hkey : (1 / 4) * (1 - σ) ≤ (f 1).re * M ^ (3 * (1 - σ)) := by
    nlinarith
  rw [Real.rpow_neg hM0.le]
  calc (1 / 4) * (1 - σ) * (M ^ (3 * (1 - σ)))⁻¹
      ≤ ((f 1).re * M ^ (3 * (1 - σ))) * (M ^ (3 * (1 - σ)))⁻¹ :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = (f 1).re := by field_simp

end SWPort
end

theorem solution : type_of% @SWPort.Davenport.estermann_lemma_oai := @SWPort.Davenport.estermann_lemma_oai

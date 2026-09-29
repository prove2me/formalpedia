-- Prove2me | solution 1 for Zeta23.PrimeSide.tr1Prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:07:12.874429+00:00
-- url     : https://prove2.me/submissions/eaf13ad7-ceab-464e-adec-869f17816c1b

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_PrimeSideB
import Definitions.Def_Zeta23_PrimeSideTemp

-- from Zeta23.PrimeSideB
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# Prime side, part B: [prop:PP] and the assembly of Theorem [thm:traces]

Paper §5 ("The prime side: magnitude"), subsections "Evaluation of 𝓜" and "Summary".

Contents
* §0 glue between the explicit-constant interface shape `EvBound` and Mathlib's `IsBigO`.
* §1 `Zeta23.PaperParams`: elementary facts about the scalar parameters `l, ℓ₁, L, X, λ₁, 𝓔_T`
  of `Defs.lean` (growth, positivity, `𝓔_T → 0`).  Pure real analysis, no hypotheses.
* §2 `Zeta23.PrimeSide.Facts` / `Zeta23.PrimeSide.tracesBounds_of_facts`: the proof of [thm:traces]
  ([eq:tr1], [eq:tr2], [eq:ratio], second forms) from the five sub-results of §5 + [eq:muints] (H-Γ)
  + [eq:RvM] (H-RvM) + [eq:abdef] (Taper), all taken as hypotheses on abstract real functions of `T`.
  This is where the paper's constants `ℓ₁² + L²/3` and `F(λ₁)` are checked.
* §3 [prop:PP]: `𝓜[P_X,P_X] = (T/π) Σ_{n≤X} Λ(n)²/n · g(log n) + O(L² X)` and the sandwich
  `(L−2w)³/6 + O(L²) ≤ Σ a_n² g(y_n) ≤ L³/6 + O(L²)` — over the concrete definitions of `Defs.lean`
  and `Mform`.
-/

noncomputable section

open Real Filter Asymptotics Topology

namespace Zeta23

/-! ## §0.  Explicit-constant ↔ `IsBigO` glue -/

namespace EvBound






/-- An eventual pointwise bound with an explicit constant gives an `EvBound`. -/
lemma of_eventually_le {f g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ T in atTop, |f T| ≤ c * g T) : EvBound f g := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp h
  exact ⟨c, hc, T₀, hT₀⟩

lemma eventually_le {f g : ℝ → ℝ} (h : EvBound f g) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T in atTop, |f T| ≤ C * g T := by
  obtain ⟨C, hC, T₀, hT⟩ := h
  exact ⟨C, hC, eventually_atTop.mpr ⟨T₀, hT⟩⟩







end EvBound

/-! ## §1.  The scalar parameters of `Defs.lean` -/

namespace PaperParams

lemma l_tendsto_atTop : Tendsto l atTop atTop := by
  unfold l
  exact Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))

lemma ell1_eq (T : ℝ) : ell1 T = l T + (2 * Real.log 2 - 1) := by unfold ell1; ring

/-- `2 log 2 − 1 > 0`, so `ℓ₁ > l`. -/
lemma two_log_two_sub_one_pos : 0 < 2 * Real.log 2 - 1 := by
  have := Real.log_two_gt_d9
  linarith

lemma l_lt_ell1 (T : ℝ) : l T < ell1 T := by
  rw [ell1_eq]; linarith [two_log_two_sub_one_pos]


variable (P : Params)

lemma X_pos (T : ℝ) : 0 < P.X T := Real.exp_pos _

/-- `X = (T/2π)^λ` for `T > 0`. -/
lemma X_eq_rpow {T : ℝ} (hT : 0 < T) : P.X T = (T / (2 * π)) ^ P.lam := by
  unfold Params.X Params.L l
  rw [Real.rpow_def_of_pos (div_pos hT (by positivity)), mul_comm]

lemma L_tendsto_atTop (hP : 0 < P.lam) : Tendsto P.L atTop atTop := by
  unfold Params.L
  exact l_tendsto_atTop.const_mul_atTop hP


lemma eventually_l_ge (c : ℝ) : ∀ᶠ T in atTop, c ≤ l T := l_tendsto_atTop.eventually_ge_atTop c


lemma eventually_L_ge (hlam : 0 < P.lam) (c : ℝ) : ∀ᶠ T in atTop, c ≤ P.L T :=
  (L_tendsto_atTop P hlam).eventually_ge_atTop c

lemma l_le_ell1 (T : ℝ) : l T ≤ ell1 T := (l_lt_ell1 T).le



/-- `√X = (T/2π)^{λ/2}`. -/
lemma sqrt_X_eq {T : ℝ} (hT : 0 < T) : Real.sqrt (P.X T) = (T / (2 * π)) ^ (P.lam / 2) := by
  rw [X_eq_rpow P hT, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  ring_nf

/-- `√X ≤ T^{λ/2}` for `T > 0` (as `T/2π ≤ T`). -/
lemma sqrt_X_le_rpow (hlam : 0 < P.lam) {T : ℝ} (hT : 0 < T) :
    Real.sqrt (P.X T) ≤ T ^ (P.lam / 2) := by
  rw [sqrt_X_eq P hT]
  apply Real.rpow_le_rpow (by positivity) _ (by linarith)
  rw [div_le_iff₀ (by positivity)]
  have := Real.pi_gt_three
  nlinarith



lemma rpow_half_sub_one_mul {T : ℝ} (hT : 0 < T) (s : ℝ) : T ^ (s - 1) * T = T ^ s := by
  rw [Real.rpow_sub_one hT.ne', div_mul_cancel₀ _ hT.ne']

variable {P}

/-- each of the three summands of `𝓔_T` is eventually nonnegative -/
lemma calE_summands_nonneg (hlam : 0 < P.lam) (hw : 0 ≤ P.w) :
    ∀ᶠ T in atTop, 0 ≤ P.w / P.L T ∧
      0 ≤ (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T) ∧ 0 ≤ T ^ (P.lam / 2 - 1) := by
  filter_upwards [(L_tendsto_atTop P hlam).eventually_ge_atTop 0,
    l_tendsto_atTop.eventually_ge_atTop 1, eventually_ge_atTop (0:ℝ)] with T hL hl hT
  refine ⟨div_nonneg hw hL, div_nonneg (mul_nonneg (add_nonneg (sq_nonneg _) (X_pos P T).le)
    (Real.log_nonneg hl)) (mul_nonneg hT (by linarith)), Real.rpow_nonneg hT _⟩

/-- `𝓔_T ≥ w / L` for `T` large. -/
lemma calE_ge_w_div_L (hlam : 0 < P.lam) (hw : 0 ≤ P.w) :
    ∀ᶠ T in atTop, P.w / P.L T ≤ P.calE T := by
  filter_upwards [calE_summands_nonneg hlam hw] with T ⟨_, h2, h3⟩
  unfold Params.calE; linarith

/-- `𝓔_T ≥ T^{λ/2-1}` for `T` large. -/
lemma calE_ge_rpow (hlam : 0 < P.lam) (hw : 0 ≤ P.w) :
    ∀ᶠ T in atTop, T ^ (P.lam / 2 - 1) ≤ P.calE T := by
  filter_upwards [calE_summands_nonneg hlam hw] with T ⟨h1, h2, _⟩
  unfold Params.calE; linarith


lemma calE_nonneg_eventually (hlam : 0 < P.lam) (hw : 0 ≤ P.w) :
    ∀ᶠ T in atTop, 0 ≤ P.calE T := by
  filter_upwards [calE_summands_nonneg hlam hw] with T ⟨h1, h2, h3⟩
  unfold Params.calE; linarith


end PaperParams

/-! ## §2.  Assembly of Theorem [thm:traces] from the §5 sub-results

All quantities are real functions of `T` at fixed `P = (ϱ, λ, w)`.  The hypotheses below are exactly
the conclusions of [prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:PP], [prop:cross]
(the paper §5), [eq:muints] (from H-Γ), [eq:RvM] (H-RvM) and [eq:abdef] (Taper), each in the
explicit-constant form `EvBound`. -/

namespace PrimeSide

open PaperParams


variable {P : Params} (D : Data P)


/-! ### The assembly -/

section assembly
variable {D} (h : Facts D)
include h


/-- From [eq:RvM]: eventually `T l /(4π) ≤ N(T,2T)` (and hence `N > 0`). -/
lemma Ncnt_lower : ∀ᶠ T in atTop, T * l T / (4 * π) ≤ D.Ncnt T := by
  obtain ⟨A, hA, hN⟩ := h.rvm.eventually_le
  filter_upwards [hN, eventually_ge_atTop (4 * π * A), eventually_l_ge 0] with T hN hTA hl
  have hπ := Real.pi_pos
  have h1 : -(A * l T) ≤ D.Ncnt T - T * ell1 T / (2 * π) := (abs_le.mp hN).1
  have h2 : T * l T ≤ T * ell1 T := mul_le_mul_of_nonneg_left (l_le_ell1 T) (by nlinarith)
  have h3 : T * l T / (2 * π) ≤ T * ell1 T / (2 * π) := div_le_div_of_nonneg_right h2 (by positivity)
  have h4 : T * l T / (4 * π) = T * l T / (2 * π) - T * l T / (4 * π) := by ring
  have h5 : A * l T ≤ T * l T / (4 * π) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  linarith

/-- eventually `T ≤ 4π N(T,2T)`. -/
lemma T_le_Ncnt : ∀ᶠ T in atTop, T ≤ 4 * π * D.Ncnt T := by
  filter_upwards [Ncnt_lower h, eventually_l_ge 1, eventually_ge_atTop 0] with T hN hl hT
  have hπ := Real.pi_pos
  have : T * l T ≤ 4 * π * D.Ncnt T := by rw [div_le_iff₀ (by positivity)] at hN; linarith
  nlinarith

lemma Ncnt_pos : ∀ᶠ T in atTop, 0 < D.Ncnt T := by
  filter_upwards [Ncnt_lower h, eventually_l_ge 1, eventually_ge_atTop 1] with T hN hl hT
  have hπ := Real.pi_pos
  exact lt_of_lt_of_le (by positivity) (le_trans (by gcongr : T * 1 / (4 * π) ≤ _) hN)
    |> fun h => by simpa using h









end assembly

end PrimeSide

/-! ## §3.  [prop:PP]

Statement over `Mform` and `Defs.lean`'s `PX, PhiR, g`,
via the 𝒟 / 𝒪₁ / 𝒪₂ decomposition [eq:MPP]. -/

end Zeta23

end
open Real Filter Asymptotics Topology
open Zeta23
open PrimeSide
open PaperParams
variable {P : Params} (D : Data P)
variable {D} (h : Facts D)
include h

theorem solution : EvBound (fun T => D.trG T - P.L T * D.Ncnt T)
    (fun T => P.calE T * (P.L T * D.Ncnt T)) := by
  obtain ⟨C₁, hC₁, h1⟩ := h.prop_trace.eventually_le
  have hlam := h.lam_pos
  have hw : 0 ≤ P.w := by linarith [h.one_le_w]
  refine EvBound.of_eventually_le (c := 4 * π * C₁ + 2) (by positivity) ?_
  filter_upwards [h1, h.abdef, calE_ge_w_div_L hlam hw, calE_ge_rpow hlam hw,
    calE_nonneg_eventually hlam hw, T_le_Ncnt h, Ncnt_pos h, eventually_ge_atTop 1,
    eventually_L_ge P hlam 1] with T h1 hab hEw hEr hE0 hTN hN0 hT1 hL1
  obtain ⟨hb1, hba, ha1⟩ := hab
  have hT0 : 0 < T := by linarith
  have hL0 : 0 ≤ P.L T := by linarith
  set N := D.Ncnt T
  set L := P.L T
  set E := P.calE T
  have hLN : 0 ≤ L * N := mul_nonneg hL0 hN0.le
  -- the taper discrepancy (1 - a) L N ≤ (2w/L) L N ≤ 2 E L N
  have hA : |D.aT T * L * N - L * N| ≤ 2 * E * (L * N) := by
    have : D.aT T * L * N - L * N = -((1 - D.aT T) * (L * N)) := by ring
    rw [this, abs_neg, abs_of_nonneg (mul_nonneg (by linarith) hLN)]
    have h2 : 1 - D.aT T ≤ 2 * E := by
      have : 2 * P.w / L = 2 * (P.w / L) := by ring
      linarith
    exact mul_le_mul_of_nonneg_right h2 hLN
  -- the √X term: C₁ L √X ≤ C₁ L T^{λ/2} = C₁ L T^{λ/2-1} T ≤ C₁ L E (4π N)
  have hB : C₁ * (L * Real.sqrt (P.X T)) ≤ 4 * π * C₁ * (E * (L * N)) := by
    have hs : Real.sqrt (P.X T) ≤ T ^ (P.lam / 2 - 1) * T := by
      rw [rpow_half_sub_one_mul hT0]; exact sqrt_X_le_rpow P hlam hT0
    have hs2 : T ^ (P.lam / 2 - 1) * T ≤ E * (4 * π * N) :=
      mul_le_mul hEr hTN hT0.le hE0
    calc C₁ * (L * Real.sqrt (P.X T)) ≤ C₁ * (L * (E * (4 * π * N))) := by
          gcongr; exact hs.trans hs2
      _ = 4 * π * C₁ * (E * (L * N)) := by ring
  calc |D.trG T - L * N|
      ≤ |D.trG T - D.aT T * L * N| + |D.aT T * L * N - L * N| := abs_sub_le _ _ _
    _ ≤ C₁ * (L * Real.sqrt (P.X T)) + 2 * E * (L * N) := add_le_add h1 hA
    _ ≤ 4 * π * C₁ * (E * (L * N)) + 2 * E * (L * N) := by linarith
    _ = (4 * π * C₁ + 2) * (E * (L * N)) := by ring

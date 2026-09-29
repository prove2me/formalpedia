-- Prove2me | solution 1 for Zeta23.PrimeSide.ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:02:21.835348+00:00
-- url     : https://prove2.me/submissions/94f8947e-3e21-406a-9c2d-c90b3906cbaf

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
import Theorems.Thm_Zeta23_PaperParams_calE_tendsto_zero
import Theorems.Thm_Zeta23_PrimeSide_ratio_pointwise
import Theorems.Thm_Zeta23_PrimeSide_tr1Prime
import Theorems.Thm_Zeta23_PrimeSide_tr2

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

lemma log_l_tendsto_atTop : Tendsto (fun T => Real.log (l T)) atTop atTop :=
  Real.tendsto_log_atTop.comp l_tendsto_atTop

lemma eventually_l_ge (c : ℝ) : ∀ᶠ T in atTop, c ≤ l T := l_tendsto_atTop.eventually_ge_atTop c

lemma eventually_log_l_ge (c : ℝ) : ∀ᶠ T in atTop, c ≤ Real.log (l T) :=
  log_l_tendsto_atTop.eventually_ge_atTop c

lemma eventually_L_ge (hlam : 0 < P.lam) (c : ℝ) : ∀ᶠ T in atTop, c ≤ P.L T :=
  (L_tendsto_atTop P hlam).eventually_ge_atTop c

lemma l_le_ell1 (T : ℝ) : l T ≤ ell1 T := (l_lt_ell1 T).le


/-- `L ≤ l` when `λ ≤ 1` and `l ≥ 0`. -/
lemma L_le_l (hlam1 : P.lam ≤ 1) {T : ℝ} (hl : 0 ≤ l T) : P.L T ≤ l T := by
  unfold Params.L; nlinarith



/-- `X ≤ T` eventually (`λ ≤ 1`). -/
lemma eventually_X_le_T (_hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) : ∀ᶠ T in atTop, P.X T ≤ T := by
  filter_upwards [eventually_ge_atTop (2 * π)] with T hT
  have hπ := Real.pi_gt_three
  have hT0 : 0 < T := by linarith
  rw [X_eq_rpow P hT0]
  have h1 : 1 ≤ T / (2 * π) := by rw [le_div_iff₀ (by positivity)]; linarith
  calc (T / (2 * π)) ^ P.lam ≤ (T / (2 * π)) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 hlam1
    _ = T / (2 * π) := Real.rpow_one _
    _ ≤ T := by rw [div_le_iff₀ (by positivity)]; nlinarith

lemma eventually_one_le_X (hlam : 0 < P.lam) : ∀ᶠ T in atTop, 1 ≤ P.X T := by
  filter_upwards [eventually_L_ge P hlam 0] with T hL
  simpa [Params.X] using Real.one_le_exp hL


variable {P}

/-- each of the three summands of `𝓔_T` is eventually nonnegative -/
lemma calE_summands_nonneg (hlam : 0 < P.lam) (hw : 0 ≤ P.w) :
    ∀ᶠ T in atTop, 0 ≤ P.w / P.L T ∧
      0 ≤ (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T) ∧ 0 ≤ T ^ (P.lam / 2 - 1) := by
  filter_upwards [(L_tendsto_atTop P hlam).eventually_ge_atTop 0,
    l_tendsto_atTop.eventually_ge_atTop 1, eventually_ge_atTop (0:ℝ)] with T hL hl hT
  refine ⟨div_nonneg hw hL, div_nonneg (mul_nonneg (add_nonneg (sq_nonneg _) (X_pos P T).le)
    (Real.log_nonneg hl)) (mul_nonneg hT (by linarith)), Real.rpow_nonneg hT _⟩


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


lemma Ncnt_pos : ∀ᶠ T in atTop, 0 < D.Ncnt T := by
  filter_upwards [Ncnt_lower h, eventually_l_ge 1, eventually_ge_atTop 1] with T hN hl hT
  have hπ := Real.pi_pos
  exact lt_of_lt_of_le (by positivity) (le_trans (by gcongr : T * 1 / (4 * π) ≤ _) hN)
    |> fun h => by simpa using h


/-- The common regime `T ≥ 1, l ≥ 1, log l ≥ 1, L ≥ 1, X ≥ 1, L ≤ l, X ≤ T` (eventually). -/
lemma regime : ∀ᶠ T in atTop, 1 ≤ T ∧ 1 ≤ l T ∧ 1 ≤ Real.log (l T) ∧ 1 ≤ P.L T ∧ 1 ≤ P.X T ∧
    P.L T ≤ l T ∧ P.X T ≤ T := by
  have hlam := h.lam_pos
  filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
    eventually_L_ge P hlam 1, eventually_one_le_X P hlam, eventually_X_le_T P hlam h.lam_le_one]
    with T h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, L_le_l P h.lam_le_one (by linarith), h6⟩







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

theorem solution : EvBound (fun T => D.trG T ^ 2 / D.trG2 T - Ffun (P.lam1 T) * D.Ncnt T)
    (fun T => P.calE T * (Ffun (P.lam1 T) * D.Ncnt T)) := by
  have hlam := h.lam_pos
  have hlam1 := h.lam_le_one
  have hw : 0 ≤ P.w := by linarith [h.one_le_w]
  obtain ⟨C₁, hC₁, h1⟩ := (tr1Prime h).eventually_le
  obtain ⟨C₂, hC₂, h2⟩ := (tr2 h).eventually_le
  obtain ⟨A, hA, hN⟩ := h.rvm.eventually_le
  have hcal := calE_tendsto_zero hlam hlam1 hw
  have hs1 : ∀ᶠ T in atTop, C₁ * P.calE T ≤ 1 / 2 := by
    filter_upwards [hcal.eventually (Iio_mem_nhds (show (0:ℝ) < 1 / (2 * C₁) by positivity))]
      with T hT
    rw [lt_div_iff₀ (by positivity)] at hT
    linarith
  have hs2 : ∀ᶠ T in atTop, C₂ * P.calE T ≤ 1 / 2 := by
    filter_upwards [hcal.eventually (Iio_mem_nhds (show (0:ℝ) < 1 / (2 * C₂) by positivity))]
      with T hT
    rw [lt_div_iff₀ (by positivity)] at hT
    linarith
  refine EvBound.of_eventually_le (c := 2 * (2 * π * A + 5 * C₁ + C₂)) (by positivity) ?_
  filter_upwards [h1, h2, hN, hs1, hs2, regime h, calE_ge_rpow hlam hw,
    calE_nonneg_eventually hlam hw, Ncnt_pos h, eventually_ge_atTop (2 * π * A)]
    with T h1 h2 hN hs1 hs2 hreg hEr hE0 hN0 hTA
  obtain ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ := hreg
  have hET : 1 / T ≤ P.calE T := by
    refine le_trans ?_ hEr
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  exact ratio_pointwise T (P.L T) (ell1 T) (l T) (P.calE T) (D.Ncnt T) (D.trG T) (D.trG2 T)
    A C₁ C₂ hT (by linarith) (hl.trans (l_le_ell1 T)) (l_le_ell1 T) hN0 hE0 hET hA.le hC₁.le
    hC₂.le hs1 hs2 hTA h1 h2 hN

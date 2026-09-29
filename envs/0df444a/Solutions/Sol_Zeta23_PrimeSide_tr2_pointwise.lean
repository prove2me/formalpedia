-- Prove2me | solution 1 for Zeta23.PrimeSide.tr2_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:04:26.197279+00:00
-- url     : https://prove2.me/submissions/b9dddb57-a86d-4cbb-8efc-b05acc9ea5ee

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














end EvBound

/-! ## §1.  The scalar parameters of `Defs.lean` -/

namespace PaperParams






variable (P : Params)
















variable {P}







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
omit h

theorem solution (T L ℓ lT X E S I2 b G2 w CR Cμ Cu Cl : ℝ)
    (hT : 1 ≤ T) (hL : 1 ≤ L) (hl : 1 ≤ lT) (hlog : 1 ≤ Real.log lT) (hX : 1 ≤ X)
    (hℓl : lT ≤ ℓ) (hLl : L ≤ lT) (hw : 1 ≤ w) (hL2w : 2 * w ≤ L) (hb1 : 1 - 2 * w / L ≤ b) (hble1 : b ≤ 1)
    (hE0 : 0 ≤ E) (hEw : w / L ≤ E) (hEmid : (lT ^ 2 + X) * Real.log lT / (T * lT) ≤ E)
    (hCR : 0 ≤ CR) (hCμ : 0 ≤ Cμ) (hCu : 0 ≤ Cu) (hCl : 0 ≤ Cl)
    (hR : |G2 - (2 * π * b * L * I2 + T / π * S)| ≤ CR * (L * lT * Real.log lT * (lT ^ 2 + X)))
    (hμ : |I2 - T * ℓ ^ 2 / (4 * π ^ 2)| ≤ Cμ * (T * ℓ ^ 2 / (4 * π ^ 2) / lT ^ 2))
    (hSup : S - L ^ 3 / 6 ≤ Cu * L ^ 2) (hSlo : -(Cl * L ^ 2) ≤ S - (L - 2 * w) ^ 3 / 6) :
    |G2 - T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3)|
      ≤ (2 * π * CR + Cμ + 2 + 6 * (Cu + Cl + 2 * w)) * (E * (T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3))) := by
  have hπ : 0 < π := Real.pi_pos
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < L := by linarith
  have hl0 : 0 < lT := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hlog0 : 0 ≤ Real.log lT := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hb0 : 0 ≤ b := by
    have : 2 * w / L ≤ 1 := by rw [div_le_one hL0]; linarith only [hL2w]
    linarith only [this, hb1]
  -- the main term and its two lower bounds
  set M₂ := T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3) with hM₂def
  have hM : M₂ = T * L * ℓ ^ 2 / (2 * π) + T * L ^ 3 / (6 * π) := by rw [hM₂def]; ring
  have hMa : T * L * ℓ ^ 2 / (2 * π) ≤ M₂ := by
    rw [hM]; linarith only [show 0 ≤ T * L ^ 3 / (6 * π) by positivity]
  have hMb : T * L ^ 3 / (6 * π) ≤ M₂ := by
    rw [hM]; linarith only [show 0 ≤ T * L * ℓ ^ 2 / (2 * π) by positivity]
  have hM0 : 0 ≤ M₂ := le_trans (by positivity) hMb
  have hEM0 : 0 ≤ E * M₂ := mul_nonneg hE0 hM0
  -- 1/L ≤ E and 1/l² ≤ E
  have hE_L : 1 / L ≤ E := le_trans (by gcongr) hEw
  have hE_l2 : 1 / lT ^ 2 ≤ E := by
    refine le_trans ?_ hE_L
    rw [div_le_div_iff₀ (by positivity) hL0, one_mul, one_mul]
    calc L ≤ lT := hLl
      _ = lT * 1 := (mul_one _).symm
      _ ≤ lT * lT := by gcongr
      _ = lT ^ 2 := (sq lT).symm
  -- Piece A: R ≤ 2π E M₂
  have hA : L * lT * Real.log lT * (lT ^ 2 + X) ≤ 2 * π * (E * M₂) := by
    have h1 : (lT ^ 2 + X) * Real.log lT / (T * lT) * (T * L * ℓ ^ 2 / (2 * π)) ≤ E * M₂ :=
      mul_le_mul hEmid hMa (by positivity) hE0
    have h2 : 2 * π * ((lT ^ 2 + X) * Real.log lT / (T * lT) * (T * L * ℓ ^ 2 / (2 * π)))
        = L * Real.log lT * (lT ^ 2 + X) * ℓ ^ 2 / lT := by
      field_simp
    have h3 : L * lT * Real.log lT * (lT ^ 2 + X) ≤ L * Real.log lT * (lT ^ 2 + X) * ℓ ^ 2 / lT := by
      rw [le_div_iff₀ hl0]
      have hll : lT * lT ≤ ℓ ^ 2 := by rw [sq]; exact mul_le_mul hℓl hℓl hl0.le hℓ0.le
      have h0 : 0 ≤ L * Real.log lT * (lT ^ 2 + X) := by positivity
      calc L * lT * Real.log lT * (lT ^ 2 + X) * lT = L * Real.log lT * (lT ^ 2 + X) * (lT * lT) := by
            ring
        _ ≤ L * Real.log lT * (lT ^ 2 + X) * ℓ ^ 2 := by gcongr
    calc L * lT * Real.log lT * (lT ^ 2 + X)
        ≤ L * Real.log lT * (lT ^ 2 + X) * ℓ ^ 2 / lT := h3
      _ = 2 * π * ((lT ^ 2 + X) * Real.log lT / (T * lT) * (T * L * ℓ ^ 2 / (2 * π))) := h2.symm
      _ ≤ 2 * π * (E * M₂) := by gcongr
  -- Piece B1: |2π b L (I2 − Tℓ²/(4π²))| ≤ Cμ E M₂
  have hB1 : |2 * π * b * L * (I2 - T * ℓ ^ 2 / (4 * π ^ 2))| ≤ Cμ * (E * M₂) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * π * b * L)]
    calc 2 * π * b * L * |I2 - T * ℓ ^ 2 / (4 * π ^ 2)|
        ≤ 2 * π * 1 * L * (Cμ * (T * ℓ ^ 2 / (4 * π ^ 2) / lT ^ 2)) := by gcongr
      _ = Cμ * ((1 / lT ^ 2) * (T * L * ℓ ^ 2 / (2 * π))) := by field_simp; ring
      _ ≤ Cμ * (E * M₂) := by gcongr
  -- Piece B2: |(b − 1) T L ℓ²/(2π)| ≤ 2 E M₂
  have hB2 : |(b - 1) * (T * L * ℓ ^ 2 / (2 * π))| ≤ 2 * (E * M₂) := by
    rw [abs_mul, abs_of_nonpos (by linarith only [hble1]), abs_of_nonneg (by positivity)]
    calc -(b - 1) * (T * L * ℓ ^ 2 / (2 * π)) ≤ (2 * w / L) * M₂ := by
          apply mul_le_mul (by linarith only [hb1]) hMa (by positivity) (by positivity)
      _ = 2 * ((w / L) * M₂) := by ring
      _ ≤ 2 * (E * M₂) := by gcongr
  -- Piece B3: |T/π (S − L³/6)| ≤ 6 (Cu + Cl + 2w) E M₂
  have hSlo' : -((Cl + 2 * w) * L ^ 2) ≤ S - L ^ 3 / 6 := by
    have h2 : -(2 * w * L ^ 2) ≤ (L - 2 * w) ^ 3 / 6 - L ^ 3 / 6 := by
      have e : (L - 2 * w) ^ 3 / 6 - L ^ 3 / 6 - (-(2 * w * L ^ 2))
          = w * (L ^ 2 - (4 / 3) * w ^ 2 + 2 * w * L) := by ring
      have hsq : (2 * w) * (2 * w) ≤ L * L := mul_le_mul hL2w hL2w (by linarith only [hw0]) hL0.le
      have : 0 ≤ w * (L ^ 2 - (4 / 3) * w ^ 2 + 2 * w * L) :=
        mul_nonneg hw0 (by linarith only [hsq, mul_nonneg hw0 hL0.le, sq_nonneg w])
      linarith only [e, this]
    linarith only [h2, hSlo]
  have hB3 : |T / π * (S - L ^ 3 / 6)| ≤ 6 * (Cu + Cl + 2 * w) * (E * M₂) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ T / π)]
    have hS : |S - L ^ 3 / 6| ≤ (Cu + Cl + 2 * w) * L ^ 2 := by
      rw [abs_le]
      constructor <;> linarith only [hSlo', hSup, mul_nonneg hCu (sq_nonneg L),
        mul_nonneg hCl (sq_nonneg L), mul_nonneg hw0 (sq_nonneg L)]
    calc T / π * |S - L ^ 3 / 6| ≤ T / π * ((Cu + Cl + 2 * w) * L ^ 2) := by gcongr
      _ = 6 * (Cu + Cl + 2 * w) * ((1 / L) * (T * L ^ 3 / (6 * π))) := by
          field_simp
      _ ≤ 6 * (Cu + Cl + 2 * w) * (E * M₂) := by gcongr
  -- assemble
  have hsplit : (2 * π * b * L * I2 + T / π * S) - M₂
      = 2 * π * b * L * (I2 - T * ℓ ^ 2 / (4 * π ^ 2)) + (b - 1) * (T * L * ℓ ^ 2 / (2 * π))
        + T / π * (S - L ^ 3 / 6) := by
    rw [hM]; field_simp; ring
  calc |G2 - M₂|
      ≤ |G2 - (2 * π * b * L * I2 + T / π * S)| + |(2 * π * b * L * I2 + T / π * S) - M₂| :=
        abs_sub_le _ _ _
    _ ≤ CR * (L * lT * Real.log lT * (lT ^ 2 + X))
        + (|2 * π * b * L * (I2 - T * ℓ ^ 2 / (4 * π ^ 2))| + |(b - 1) * (T * L * ℓ ^ 2 / (2 * π))|
          + |T / π * (S - L ^ 3 / 6)|) := by
        gcongr
        rw [hsplit]; exact abs_add_three _ _ _
    _ ≤ CR * (2 * π * (E * M₂)) + (Cμ * (E * M₂) + 2 * (E * M₂)
          + 6 * (Cu + Cl + 2 * w) * (E * M₂)) := by gcongr
    _ = (2 * π * CR + Cμ + 2 + 6 * (Cu + Cl + 2 * w)) * (E * M₂) := by ring

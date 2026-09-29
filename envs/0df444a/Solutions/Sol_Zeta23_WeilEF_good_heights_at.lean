-- Prove2me | solution 1 for Zeta23.WeilEF.good_heights_at
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:33:58.184951+00:00
-- url     : https://prove2.me/submissions/4ac8ebec-68ed-41a7-8ea9-3104af09363d

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_RvM_LocalCount
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne
import Definitions.Def_Zeta23_ZetaReflect
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count
import Theorems.Thm_Zeta23_Tail_LocalCount_ofWindowCount
import Theorems.Thm_Zeta23_WeilEF_exists_far_point
import Theorems.Thm_Zeta23_WeilEF_sum_mult_six_windows
import Theorems.Thm_Zeta23_WeilEF_zeta_logDeriv_partial_fraction

-- from Zeta23.Tail.Basic
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Basic.lean — shared elementary definitions for prop:tail (the paper §4.2).
-/

noncomputable section

namespace Zeta23
namespace Tail











lemma LocalCount.A₀_pos {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ : ℝ}
    (h : LocalCount γ m A₀) : 0 < A₀ := lt_of_lt_of_le one_pos h.one_le

end Tail
end Zeta23
end
end

-- from Zeta23.Statement
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Statement.lean — the statement layer.

Canonical text: the paper, §1 [Results], [eq:trivialchain], [thm:A], [thm:B], [thm:C].

It (1) defines nontrivial zeros, multiplicity (via analyticOrderAt) and the six counting functions of
§1 directly against Mathlib; (2) packages the "seam" facts needed to view them as an abstract
Zeta23.ZeroConfig (structure ZetaSeam — classical facts about ζ, established from Mathlib elsewhere in
the repository, not paper inputs); (3) states Theorems A, B, C in ε-form (fixed λ ∈ (0,1) with
constant H(λ), F(λ), then the 2/3, 1/2, 3/4 liminf wrappers via λ → 1⁻);
(4) proves the sanity anchors connecting to Mathlib's RiemannHypothesis and [eq:trivialchain].
-/

open scoped BigOperators ComplexConjugate
open Complex Set

noncomputable section

namespace Zeta23

/-! ## 1. Nontrivial zeros and multiplicity, against Mathlib -/










/-! ## 2. The seam: ζ's zeros as an abstract ZeroConfig -/



section seam_rfl
variable (hs : ZetaSeam) (T₁ T₂ : ℝ)

@[simp] lemma zetaZeros_carrier : (zetaZeros hs).carrier = {ρ | IsNontrivialZero ρ} := rfl
@[simp] lemma zetaZeros_mult : (zetaZeros hs).mult = zeroMult := rfl
@[simp] lemma zetaZeros_simple : (zetaZeros hs).simple = {ρ | zeroMult ρ = 1} := rfl

lemma zetaZeros_window : (zetaZeros hs).window T₁ T₂ = zerosIn T₁ T₂ := by
  ext ρ; simp [ZeroConfig.window, zerosIn]

@[simp] lemma zetaZeros_N : (zetaZeros hs).N T₁ T₂ = Ncount T₁ T₂ := by
  simp [ZeroConfig.N, Ncount, zetaZeros_window]
@[simp] lemma zetaZeros_Nd : (zetaZeros hs).Nd T₁ T₂ = Ndist T₁ T₂ := by
  simp [ZeroConfig.Nd, Ndist, zetaZeros_window]
@[simp] lemma zetaZeros_N0 : (zetaZeros hs).N0 T₁ T₂ = N0 T₁ T₂ := by
  simp [ZeroConfig.N0, N0, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_N0star : (zetaZeros hs).N0star T₁ T₂ = N0star T₁ T₂ := by
  simp [ZeroConfig.N0star, N0star, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_N0s : (zetaZeros hs).N0s T₁ T₂ = N0simple T₁ T₂ := by
  simp [ZeroConfig.N0s, N0simple, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_Ns : (zetaZeros hs).Ns T₁ T₂ = Nsimple T₁ T₂ := by
  simp [ZeroConfig.Ns, Nsimple, zetaZeros_window]

end seam_rfl

/-! ## 3. Sanity anchors (connection to Mathlib's existing statement of RH) -/





/-! ## 4. Theorems A, B, C

The headline theorems Zeta23.thmA, thmA_cumulative, thmA_lam, thmB, thmB_cumulative, thmB_lam, thmC,
thmC_cumulative, thmC_lam are proved in Zeta23/Final.lean (their types display the full trust base:
literature explicit formula, Riemann–von Mangoldt, Montgomery–Vaughan, Γ-facts), on top of the
versions Zeta23.thmA_of_traces etc. in Zeta23/Main.lean (thm:traces as an explicit hypothesis). This file
stays light (definitions + anchors) so that it can be read and imported cheaply.

Paper [thm:A], verbatim: "Let 0 < λ ≤ 1 be fixed. There are constants c(λ) > 0 and T₀(λ) such that
for all T ≥ T₀(λ)   N₀*(T,2T) ≥ (H(λ) − c(λ) loglogT/logT) N(T,2T),
and for λ < 1 the factor loglog T may be omitted. In particular
  liminf_{T→∞} N₀*(T,2T)/N(T,2T) ≥ 2/3,   liminf_{T→∞} N₀*(T)/N(T) ≥ 2/3".
Formal target: the ε-forms, for each fixed λ ∈ (0,1) with constant
H(λ) (resp. 2F(λ)−1, F(λ)), which absorb c(λ)/log T; then the 2/3 (resp. 1/2, 3/4) forms via
sup_{λ<1} H(λ) = H(1) = 2/3 etc. The effective c(λ) forms are not stated. -/




end Zeta23
end
end

-- from Zeta23.Statement.SeamClosed
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Statement/SeamClosed.lean — the ζ-seam is closed.
All four fields of Zeta23.ZetaSeam are theorems of Mathlib:
  one_le_mult, finite_window  — Zeta23/Statement/Seam.lean ;
  reflect_zero, mult_reflect  — Zeta23/ZetaReflect.lean (Schwarz reflection
                                 riemannZeta_conj + functional equation at the analyticOrderAt level).
Hence the abstract ZeroConfig of ζ's nontrivial zeros and [eq:trivialchain] are hypothesis-free.
-/

noncomputable section

namespace Zeta23



@[simp] lemma zetaZeroConfig_carrier : zetaZeroConfig.carrier = {ρ | IsNontrivialZero ρ} := rfl
@[simp] lemma zetaZeroConfig_mult : zetaZeroConfig.mult = zeroMult := rfl

@[simp] lemma zetaZeroConfig_N (T₁ T₂ : ℝ) : zetaZeroConfig.N T₁ T₂ = Ncount T₁ T₂ :=
  zetaZeros_N _ _ _
@[simp] lemma zetaZeroConfig_N0star (T₁ T₂ : ℝ) : zetaZeroConfig.N0star T₁ T₂ = N0star T₁ T₂ :=
  zetaZeros_N0star _ _ _
@[simp] lemma zetaZeroConfig_N0s (T₁ T₂ : ℝ) : zetaZeroConfig.N0s T₁ T₂ = N0simple T₁ T₂ :=
  zetaZeros_N0s _ _ _
@[simp] lemma zetaZeroConfig_Nd (T₁ T₂ : ℝ) : zetaZeroConfig.Nd T₁ T₂ = Ndist T₁ T₂ :=
  zetaZeros_Nd _ _ _



end Zeta23
end
end

-- from Zeta23.RvM.LocalCount
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/LocalCount.lean

H-RvM's local count for Mathlib's ζ:  N(t, t+1] ≤ A₀ log(|t| + 3) for all real t
(= Zeta23.RiemannVonMangoldt.local_count at Z := zetaZeroConfig; [Tit86, Thm 9.2]).

Route (never evaluating ζ left of σ = 0.19, so no Stirling is needed):
 * count only zeros with β ≥ 1/2 and double (Zeta23.ZeroConfig.N_le_two_mul_half, Zeta23/RvM/Halving.lean,
   via the ρ ↦ 1−ρ̄ symmetry);
 * Jensen-type zero count on a disc: the ported PNT+ `ZerosBound` (Zeta23/FromPNTPlus/StrongPNTPrefix.lean,
   Apache-2.0) applied to g(w) := ζ(c₀ + 1.9 w)/ζ(c₀), c₀ := 2 + (t+½)i, r = 0.84, R = 0.95:
   the β ≥ 1/2 part of the window lies in ‖w‖ ≤ 0.84 (1.5² + 0.5² ≤ (1.9·0.84)²), the big disc stays in
   σ ≥ 0.195 and at distance ≥ 1 from the pole for |t| ≥ 4;
 * ζ-growth ‖ζ(s)‖ ≤ C(|Im s|+3)^A on σ ≥ 0.15, ‖s−1‖ ≥ 1 and ‖ζ(2+it)‖ ≥ 1/3
   (Zeta23.RvM.zeta_growth_right / zeta_lower_bound_two, Zeta23/RvM/ZetaGrowth.lean);
 * |t| < 4 by the finite constant N(−4, 5].
-/


open Complex Set Filter Topology Metric

noncomputable section

namespace Zeta23.RvM













/-- The same, in H-RvM's vocabulary (Z.N at Z := zetaZeroConfig). -/
theorem zetaZeroConfig_local_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ,
    (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
  simpa only [zetaZeroConfig_N] using zeta_local_zero_count

end Zeta23.RvM
end
end

-- from Zeta23.WeilEF.GoodHeights
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/GoodHeights.lean — good horizontal heights for the EF contour: for every j ≥ 7 a height
R ∈ [j, j+1] avoiding the ordinates of all ζ-zeros near heights ±j by ≥ 1/(2(n+1)) (n ≪ log j of them;
pigeonhole over n+1 cell midpoints), whence on Im s = ±R, 1/2 ≤ Re s ≤ 2:  ζ(s) ≠ 0 and
‖ζ'/ζ(s)‖ ≤ C log²(j+3), by the partial fraction Zeta23.WeilEF.zeta_logDeriv_partial_fraction (with its
multiplicity-sum conjunct) and the proved local zero count Zeta23.RvM.zetaZeroConfig_local_count
(via Zeta23.Tail.LocalCount).  Statement shape (consumed by Contour.lean horizontal_vanish):
j ≥ 7, σ ∈ [1/2, 2], bound in log((j:ℝ)+3).
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Set Filter Finset

/-! ### Gap / pigeonhole lemma -/


/-! ### Elementary facts used below -/

lemma abs_im_sub_le_norm_sub (s ρ : ℂ) : |s.im - ρ.im| ≤ ‖s - ρ‖ := by
  rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _

/-- a zero of ζ in the closed ball of radius r₀ < 2 about 2 + t i is a nontrivial zero. -/
lemma isNontrivialZero_of_mem_closedBall {t r : ℝ} (hr : r < 2) {ρ : ℂ}
    (hρ : ρ ∈ Metric.closedBall (2 + t * I) r) (hz : riemannZeta ρ = 0) : IsNontrivialZero ρ := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hρ
  have hre : |ρ.re - 2| ≤ r := by
    have := Complex.abs_re_le_norm (ρ - (2 + t * I))
    simp at this; linarith
  refine ⟨hz, by rw [abs_le] at hre; linarith, ?_⟩
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz

lemma im_mem_of_mem_closedBall {t r : ℝ} {ρ : ℂ} (hρ : ρ ∈ Metric.closedBall (2 + t * I) r) :
    |ρ.im - t| ≤ r := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hρ
  have := Complex.abs_im_le_norm (ρ - (2 + t * I))
  simp at this; linarith


/-- card ≤ total multiplicity (each nontrivial zero has multiplicity ≥ 1). -/
lemma card_le_sum_mult (F : Finset zetaZeroConfig.carrier) :
    (F.card : ℝ) ≤ ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun ρ _ => ?_
  exact_mod_cast zetaZeroConfig.one_le_mult ρ ρ.2

/-! ### good heights -/




end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex Set Filter Finset

theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 7 ≤ j →
    ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧
    ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ C * (Real.log ((j : ℝ) + 3)) ^ 2 := by
  classical
  obtain ⟨C, hC, hpf⟩ := zeta_logDeriv_partial_fraction
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hLC := Tail.LocalCount.ofWindowCount zetaZeroConfig hA₀ hloc
  refine ⟨2 * C * (48 * A₀ + 3), by positivity, fun j hj => ?_⟩
  have hj7 : (7 : ℝ) ≤ j := by exact_mod_cast hj
  set Lg : ℝ := Real.log ((j : ℝ) + 3) with hLg
  have hLg1 : 1 ≤ Lg := by
    rw [hLg, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hlog2 : Real.log 2 ≤ Lg := by
    rw [hLg]; exact Real.log_le_log (by norm_num) (by linarith)
  -- the two finite families of zeros near height ±j
  set Wp : Set ℂ := zetaZeroConfig.window ((j : ℝ) - 3) ((j : ℝ) + 3) with hWp
  set Wm : Set ℂ := zetaZeroConfig.window (-(j : ℝ) - 4) (-(j : ℝ) + 2) with hWm
  have hWpfin : ((fun ρ : zetaZeroConfig.carrier => (ρ : ℂ)) ⁻¹' Wp).Finite :=
    (zetaZeroConfig.finite_window _ _).preimage Subtype.val_injective.injOn
  have hWmfin : ((fun ρ : zetaZeroConfig.carrier => (ρ : ℂ)) ⁻¹' Wm).Finite :=
    (zetaZeroConfig.finite_window _ _).preimage Subtype.val_injective.injOn
  set Fp : Finset zetaZeroConfig.carrier := hWpfin.toFinset with hFp
  set Fm : Finset zetaZeroConfig.carrier := hWmfin.toFinset with hFm
  have hFp_mem : ∀ ρ : zetaZeroConfig.carrier, ρ ∈ Fp ↔ (ρ : ℂ) ∈ Wp := fun ρ => by
    rw [hFp, Set.Finite.mem_toFinset]; rfl
  have hFm_mem : ∀ ρ : zetaZeroConfig.carrier, ρ ∈ Fm ↔ (ρ : ℂ) ∈ Wm := fun ρ => by
    rw [hFm, Set.Finite.mem_toFinset]; rfl
  set S : Finset ℝ := Fp.image (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).im)
    ∪ Fm.image (fun ρ : zetaZeroConfig.carrier => -(ρ : ℂ).im) with hS
  -- count: |S| ≤ 24 A₀ Lg
  have hcountp : ∑ ρ ∈ Fp, (zetaZeroConfig.mult ρ : ℝ) ≤ 6 * (A₀ * (2 * Lg)) := by
    have h := sum_mult_six_windows hLC (a := (j : ℤ) - 3) Fp (fun ρ hρ => by
      have := ((hFp_mem ρ).mp hρ).2; push_cast; constructor <;> linarith [this.1, this.2])
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hLC.A₀_pos.le)
      (by norm_num))
    · have : |((j : ℤ) - 3 : ℤ)| = (j : ℤ) - 3 := abs_of_nonneg (by omega)
      have habs : |(((j:ℤ) - 3 : ℤ) : ℝ)| = (j : ℝ) - 3 := by
        rw [← Int.cast_abs, this]; push_cast; ring
      rw [habs]
      calc Real.log ((j:ℝ) - 3 + 9) ≤ Real.log (2 * ((j:ℝ) + 3)) :=
            Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 2 + Lg := by rw [Real.log_mul (by norm_num) (by linarith)]
        _ ≤ 2 * Lg := by linarith
  have hcountm : ∑ ρ ∈ Fm, (zetaZeroConfig.mult ρ : ℝ) ≤ 6 * (A₀ * (2 * Lg)) := by
    have h := sum_mult_six_windows hLC (a := -(j : ℤ) - 4) Fm (fun ρ hρ => by
      have := ((hFm_mem ρ).mp hρ).2; push_cast; constructor <;> linarith [this.1, this.2])
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hLC.A₀_pos.le)
      (by norm_num))
    · have : |(-(j : ℤ) - 4 : ℤ)| = (j : ℤ) + 4 := by
        rw [abs_of_nonpos (by omega)]; ring
      have habs : |((-(j:ℤ) - 4 : ℤ) : ℝ)| = (j : ℝ) + 4 := by
        rw [← Int.cast_abs, this]; push_cast; ring
      rw [habs]
      calc Real.log ((j:ℝ) + 4 + 9) ≤ Real.log (((j:ℝ) + 3) ^ 2) := by
            apply Real.log_le_log (by linarith); nlinarith
        _ = 2 * Lg := by rw [Real.log_pow]; push_cast; ring
  have hcard : (S.card : ℝ) ≤ 24 * A₀ * Lg := by
    have h1 : S.card ≤ Fp.card + Fm.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    have h1' : (S.card : ℝ) ≤ Fp.card + Fm.card := by exact_mod_cast h1
    linarith [card_le_sum_mult Fp, card_le_sum_mult Fm]
  -- the good height
  obtain ⟨R, hR1, hR2, hfar⟩ := exists_far_point S j
  set δ : ℝ := 1 / (2 * ((S.card : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδinv : 1 / δ = 2 * ((S.card : ℝ) + 1) := by rw [hδ, one_div_one_div]
  refine ⟨R, hR1, hR2, fun s hs hσ1 hσ2 => ?_⟩
  have hR6 : (6 : ℝ) ≤ |R| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hR6' : (6 : ℝ) ≤ |-R| := by rwa [abs_neg]
  have hlogR : Real.log (|R| + 3) ≤ 2 * Lg := by
    rw [abs_of_nonneg (by linarith)]
    calc Real.log (R + 3) ≤ Real.log (2 * ((j:ℝ) + 3)) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + Lg := by rw [Real.log_mul (by norm_num) (by linarith)]
      _ ≤ 2 * Lg := by linarith
  -- s in the conclusion ball of the partial fraction at t = s.im
  have hsball : s ∈ Metric.closedBall (2 + s.im * I) (3 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : s - (2 + s.im * I) = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  -- every zero in the pf ball at height s.im = ±R has its (signed) ordinate in S
  have hordS : ∀ ρ : ℂ, ρ ∈ Metric.closedBall (2 + s.im * I) (22/25 * (91/50)) →
      riemannZeta ρ = 0 → δ ≤ ‖s - ρ‖ := by
    intro ρ hρ hz
    have hnt := isNontrivialZero_of_mem_closedBall (by norm_num) hρ hz
    have him := im_mem_of_mem_closedBall hρ
    rw [abs_le] at him
    have hρc : ρ ∈ zetaZeroConfig.carrier := by rw [zetaZeroConfig_carrier]; exact hnt
    refine le_trans ?_ (abs_im_sub_le_norm_sub s ρ)
    rcases hs with hsR | hsR
    · -- Im ρ ∈ S via Fp
      have hmem : (⟨ρ, hρc⟩ : zetaZeroConfig.carrier) ∈ Fp := by
        rw [hFp_mem]
        refine ⟨hρc, ?_, ?_⟩ <;> rw [hsR] at him <;> nlinarith
      have : ρ.im ∈ S := by
        rw [hS, Finset.mem_union]; left
        exact Finset.mem_image.mpr ⟨(⟨ρ, hρc⟩ : zetaZeroConfig.carrier), hmem, rfl⟩
      have := hfar _ this
      rwa [hsR]
    · have hmem : (⟨ρ, hρc⟩ : zetaZeroConfig.carrier) ∈ Fm := by
        rw [hFm_mem]
        refine ⟨hρc, ?_, ?_⟩ <;> rw [hsR] at him <;> nlinarith
      have : -ρ.im ∈ S := by
        rw [hS, Finset.mem_union]; right
        exact Finset.mem_image.mpr ⟨(⟨ρ, hρc⟩ : zetaZeroConfig.carrier), hmem, rfl⟩
      have := hfar _ this
      rw [hsR, show |(-R) - ρ.im| = |R - (-ρ.im)| by rw [← abs_neg]; ring_nf]
      exact this
  -- ζ(s) ≠ 0: s itself would be a zero in the ball at distance 0
  have hζ : riemannZeta s ≠ 0 := by
    intro hz
    have h0 := hordS s (Metric.closedBall_subset_closedBall (by norm_num) hsball) hz
    simp at h0; linarith
  refine ⟨hζ, ?_⟩
  -- apply the partial fraction at t := s.im
  have ht6 : (6 : ℝ) ≤ |s.im| := by rcases hs with h | h <;> rw [h] <;> assumption
  obtain ⟨Z, hZ, hZsum, hZpf⟩ := hpf s.im ht6
  have hZpf' := hZpf s hsball hζ
  have hlogt : Real.log (|s.im| + 3) ≤ 2 * Lg := by
    rcases hs with h | h
    · rw [h]; exact hlogR
    · rw [h, abs_neg]; exact hlogR
  -- the sum over Z
  have hZmem : ∀ ρ ∈ Z, ρ ∈ Metric.closedBall (2 + s.im * I) (22/25 * (91/50)) ∧ riemannZeta ρ = 0 := by
    intro ρ hρ
    have : ρ ∈ (↑Z : Set ℂ) := hρ
    rw [hZ] at this
    exact this
  have hsumZ : ‖∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
      ≤ (C * (2 * Lg)) * (1 / δ) := by
    calc ‖∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / δ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          obtain ⟨hρb, hρz⟩ := hZmem ρ hρ
          have hd := hordS ρ hρb hρz
          have hsρ : 0 < ‖s - ρ‖ := lt_of_lt_of_le hδpos hd
          rw [norm_div, Complex.norm_natCast, div_eq_mul_one_div]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact one_div_le_one_div_of_le hδpos hd
      _ = (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) * (1 / δ) := by rw [Finset.sum_mul]
      _ ≤ (C * (2 * Lg)) * (1 / δ) := by
          refine mul_le_mul_of_nonneg_right (hZsum.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left hlogt hC.le
  -- assemble
  have hmain : ‖logDeriv riemannZeta s‖ ≤ C * (2 * Lg) + (C * (2 * Lg)) * (1 / δ) := by
    have h1 : ‖logDeriv riemannZeta s‖
        ≤ ‖logDeriv riemannZeta s - ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
          + ‖∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ := norm_le_norm_sub_add _ _
    have h2 := hZpf'.trans (mul_le_mul_of_nonneg_left hlogt hC.le)
    linarith [hsumZ]
  refine hmain.trans ?_
  rw [hδinv]
  have hc := hcard
  have hA := hLC.A₀_pos.le
  -- C·2Lg·(1 + 2(n+1)) ≤ 2C(48A₀+3) Lg²
  have : C * (2 * Lg) + C * (2 * Lg) * (2 * ((S.card : ℝ) + 1))
      = 2 * C * Lg * (2 * (S.card : ℝ) + 3) := by ring
  rw [this]
  have hn : 2 * (S.card : ℝ) + 3 ≤ (48 * A₀ + 3) * Lg := by nlinarith
  calc 2 * C * Lg * (2 * (S.card : ℝ) + 3) ≤ 2 * C * Lg * ((48 * A₀ + 3) * Lg) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ = 2 * C * (48 * A₀ + 3) * Real.log ((j : ℝ) + 3) ^ 2 := by rw [hLg]; ring

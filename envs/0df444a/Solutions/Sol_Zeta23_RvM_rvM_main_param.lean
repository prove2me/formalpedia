-- Prove2me | solution 1 for Zeta23.RvM.rvM_main_param
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:27:26.476382+00:00
-- url     : https://prove2.me/submissions/2685117d-6383-4743-a2af-d2055f2e1f70

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_Analytic_RectangleLogDeriv
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_BacklundDefs
import Definitions.Def_Zeta23_RvM_Defs
import Definitions.Def_Zeta23_RvM_GammaSide
import Definitions.Def_Zeta23_RvM_LocalCount
import Definitions.Def_Zeta23_RvM_ReZeroCount
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect
import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv
import Theorems.Thm_Zeta23_RvM_exists_goodHeight
import Theorems.Thm_Zeta23_RvM_gamma_side
import Theorems.Thm_Zeta23_RvM_halfContour_completedZeta_split
import Theorems.Thm_Zeta23_RvM_rectangleIntegralPrime_logDeriv_completedZeta_eq_Ncount
import Theorems.Thm_Zeta23_RvM_rectangleIntegral_logDeriv_completedZeta_eq_halfContour

-- from Zeta23.Defs.Counting
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Defs/Counting.lean — elementary counting facts for an abstract ZeroConfig.
[eq:trivialchain] at the abstract level; Statement.lean transfers it to ζ.
-/

open Set

noncomputable section

namespace Zeta23.ZeroConfig

variable (Z : ZeroConfig) (T₁ T₂ : ℝ)

lemma window_finite : (Z.window T₁ T₂).Finite := Z.finite_window T₁ T₂








end Zeta23.ZeroConfig
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


/-- Finiteness of every ordinate window of nontrivial zeros, hypothesis-free. -/
theorem zerosIn_finite (T₁ T₂ : ℝ) : (zerosIn T₁ T₂).Finite := by
  simpa [zetaZeros_window] using (zetaZeros zetaSeam).window_finite T₁ T₂

end Zeta23
end
end

-- from Zeta23.RvM.NcountWindow
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/NcountWindow.lean — window arithmetic for `Ncount`.

These lemmas (window splitting, additivity and monotonicity of the zero count) live here, in the
root `Zeta23` namespace, and are used by the Riemann–von Mangoldt files.
-/

noncomputable section

namespace Zeta23
/-! ## Window arithmetic for Ncount -/

/-- windows split: zerosIn a c = zerosIn a b ∪ zerosIn b c for a ≤ b ≤ c. -/
theorem zerosIn_union {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    zerosIn a c = zerosIn a b ∪ zerosIn b c := by
  ext ρ
  simp only [zerosIn, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨hρ, ha, hb⟩
    rcases le_or_gt ρ.im b with hle | hgt
    · exact Or.inl ⟨hρ, ha, hle⟩
    · exact Or.inr ⟨hρ, hgt, hb⟩
  · rintro (⟨hρ, ha, hb⟩ | ⟨hρ, ha, hb⟩)
    · exact ⟨hρ, ha, le_trans hb h2⟩
    · exact ⟨hρ, lt_of_le_of_lt h1 ha, hb⟩

/-- window additivity: N(a,c] = N(a,b] + N(b,c]. -/
theorem Ncount_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    Ncount a c = Ncount a b + Ncount b c := by
  unfold Ncount
  rw [zerosIn_union h1 h2]
  refine finsum_mem_union ?_ (zerosIn_finite a b) (zerosIn_finite b c)
  rw [Set.disjoint_left]
  rintro ρ ⟨_, _, hb⟩ ⟨_, ha, _⟩
  exact absurd hb (not_le.2 ha)

/-- window monotonicity: (a,b] ⊆ (c,d] ⇒ N(a,b] ≤ N(c,d]. -/
theorem Ncount_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) : Ncount a b ≤ Ncount c d := by
  unfold Ncount
  have hsub : zerosIn a b ⊆ zerosIn c d := by
    rintro ρ ⟨hρ, h1, h2⟩
    exact ⟨hρ, lt_of_le_of_lt hca h1, le_trans h2 hbd⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite a b),
    finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite c d)]
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ ⊢
  exact hsub hρ


end Zeta23

end
end

-- from Zeta23.RvM.Fold
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/Fold.lean — the symmetry fold of the argument-principle rectangle onto its right half
(used for MainTerm.lean's N_eq_halfContour_completedZeta).

With F := Λ'/Λ (Λ = completedRiemannZeta), A_T := ∫_{1/2}^{2} F(σ+iT)dσ, B := ∫_{T₁}^{T₂} F(2+it)dt:
the functional equation Λ(1−w) = Λ(w) and the reflection Λ(w̄) = conj Λ(w) give F(1−s̄) = −conj F(s)
on the right half-path, hence ∫_{−1}^{1/2}F(σ+iT)dσ = −conj A_T, ∫_{T₁}^{T₂}F(−1+it)dt = −conj B, and
    ∮_{∂([−1,2]×[T₁,T₂])} F = (A_{T₁} − conj A_{T₁}) − (A_{T₂} − conj A_{T₂}) + I(B + conj B)
                           = 2i·Im(A_{T₁} + B·i − A_{T₂}) = 2i·Im(halfContour F T₁ T₂).
Combined with Zeta23.RvM.rectangleIntegral'_logDeriv_completedZeta_eq_Ncount (CountByIntegral.lean):
    N(T₁,T₂) = (1/π)·Im(halfContour (logDeriv Λ) T₁ T₂)   for good heights 1 ≤ T₁ < T₂.
The conj-symmetry lemmas for Gammaℝ and Λ'/Λ (section ConjSymmetry) live here rather than in
MainTerm.lean so that both files can use them.
-/

open Complex MeasureTheory Set intervalIntegral

noncomputable section

namespace Zeta23.RvM

section ConjSymmetry







end ConjSymmetry






/-- **N(T₁,T₂) = (1/π)·Im ∫_L Λ'/Λ** for good heights 1 ≤ T₁ < T₂ (this is MainTerm.lean's
N_eq_halfContour_completedZeta). -/
theorem Ncount_eq_im_halfContour {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    (Ncount T₁ T₂ : ℝ)
      = (1 / Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im := by
  have h := rectangleIntegralPrime_logDeriv_completedZeta_eq_Ncount (by linarith) h12.le hg1 hg2
  change (1 / (2 * Real.pi * I)) • RectangleIntegral _ _ _ = _ at h
  rw [rectangleIntegral_logDeriv_completedZeta_eq_halfContour h1 h12 hg1 hg2, smul_eq_mul] at h
  have h' : ((Ncount T₁ T₂ : ℝ) : ℂ)
      = (((1 / Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im : ℝ) : ℂ) := by
    push_cast
    rw [← h]
    field_simp
  exact_mod_cast h'

end Zeta23.RvM
end
end

-- from Zeta23.RvM.MainTerm
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/MainTerm.lean — the main term N(T,2T) = (T/2π)·ell1 T + O(log T).
The statements here are assembled into Zeta23.RvM.riemannVonMangoldt in Zeta23/RvM/Statement.lean.

Inputs (from other files):
 * Zeta23.RvM.zetaZeroConfig_local_count (LocalCount.lean, proved): local count.
 * Zeta23/Analytic/RectangleLogDeriv.lean: ∮_{∂Rect} g·f'/f = 2πi Σ m_ρ g(ρ) (PNT+ RectangleIntegral'
   conventions) — use with g ≡ 1, f = completedRiemannZeta (or riemannZeta·Gammaℝ) on [−1,2]×[T₁,T₂]
   (mind Λ's poles at s = 0, 1: for T₁ > 0 the rectangle avoids them).
 * Zeta23/WeilEF/XiLogDeriv.lean: logDeriv Λ = logDeriv ζ + logDeriv Gammaℝ (Re s > 0, away from
   zeros/pole); conj-symmetry Λ(conj s) = conj Λ(s); Λ(1−s) = Λ(s) (Mathlib completedRiemannZeta_one_sub).
 * Zeta23/RvM/Backlund.lean: backlund_horizontal (∃ C T₀, ∀ T ≥ T₀, GoodHeight T →
   |Im ∫_{1/2}^{2} ζ'/ζ(σ+iT) dσ| ≤ C log T) and vertical_two (|Im ∫_{T₁}^{T₂} ζ'/ζ(2+it)·i dt| ≤ 2 log 3).
 * Zeta23/RvM/GammaSide.lean: gamma_side : 0 < T₁ ≤ T₂ → (1/π)·(halfContour (logDeriv Gammaℝ) T₁ T₂).im
   = ∫ t in T₁..T₂, mu t.
 * GammaFacts.int_mu, GammaFacts.stirling (μ(τ) = (1/2π) log(|τ|/2π) + O(τ⁻²) ⇒ μ ≪ log on [T−1,2T+1]).
The assembly is proved once as the constant-parametric `rvM_main_param`; `rvM_main_aux` /
`rvM_main` are its ∃-corollaries; MainTermExplicit.lean keeps only the numeric inputs and `rvM_main_explicit`.
-/

open Complex MeasureTheory

attribute [-instance] LieAlgebra.ofAssociativeAlgebra

noncomputable section

namespace Zeta23.RvM


/-- (M2)+(M3): the folded argument principle. For zero-free ordinates 1 ≤ T₁ < T₂:
N(T₁,T₂) = (1/π)·Im ∫_L Λ'/Λ ds, L the right half-contour.  [Tit86 §9.3; fold by Λ(1−s̄) = conj Λ(s)] -/
theorem N_eq_halfContour_completedZeta {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    (Ncount T₁ T₂ : ℝ) = (1 / Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im :=
  Ncount_eq_im_halfContour h1 h12 hg1 hg2







/-! (window arithmetic Ncount_add / Ncount_mono: Zeta23/Statement/SeamClosed.lean) -/




end Zeta23.RvM
end
open Complex MeasureTheory
open Zeta23
open Zeta23.RvM
set_option maxHeartbeats 1000000

theorem solution {CB TB A₀ Cμ Tμ CM : ℝ}
    (hB : ∀ T : ℝ, TB ≤ T → (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
      |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ CB * Real.log T)
    (vertical_two : ∀ T₁ T₂ : ℝ,
      |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi)
    (hA₀1 : 1 ≤ A₀) (hA₀ : ∀ t : ℝ, (Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hCμ : ∀ T : ℝ, Tμ ≤ T →
      |(∫ τ in T..(2 * T), mu τ) - T * ell1 T / (2 * Real.pi)| ≤ Cμ / T)
    (hCM0 : 0 < CM) (hCM : ∀ τ : ℝ, 1 ≤ τ → |mu τ| ≤ CM * Real.log (τ + 3))
    (hμc : Continuous mu) :
    ∀ T : ℝ, max (max (TB + 1) (Tμ + 1)) 4 ≤ T →
      |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T|
        ≤ (3 * |CB| + 4 * A₀ + 4 * CM + |Cμ| + 1) * Real.log T := by
  have hA₀0 : 0 ≤ A₀ := by linarith
  intro T hT
  have hT4 : 4 ≤ T := le_trans (le_max_right _ _) hT
  have hTB : TB + 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTμ : Tμ + 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hlogT : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (le_trans (by linarith [Real.exp_one_lt_d9]) le_rfl)
  have hlogT0 : 0 < Real.log T := by linarith
  -- good heights straddling [T, 2T]
  obtain ⟨T₁, hT₁mem, hg1⟩ := exists_goodHeight (T - 1)
  obtain ⟨T₂, hT₂mem, hg2⟩ := exists_goodHeight (2 * T)
  have hT₁a : T - 1 ≤ T₁ := hT₁mem.1
  have hT₁b : T₁ ≤ T := by have := hT₁mem.2; linarith
  have hT₂a : 2 * T ≤ T₂ := hT₂mem.1
  have hT₂b : T₂ ≤ 2 * T + 1 := hT₂mem.2
  have h1T₁ : 1 ≤ T₁ := by linarith
  have h12 : T₁ < T₂ := by linarith
  -- argument principle + split + Γ-side
  have hN := N_eq_halfContour_completedZeta h1T₁ h12 hg1 hg2
  have hsplit := halfContour_completedZeta_split h1T₁ h12 hg1 hg2
  have hgam := gamma_side (T₁ := T₁) (T₂ := T₂) (by linarith) (by linarith)
  -- window arithmetic
  have hadd : (Ncount T₁ T₂ : ℝ)
      = (Ncount T₁ T : ℝ) + (Ncount T (2*T) : ℝ) + (Ncount (2*T) T₂ : ℝ) := by
    have e1 := Zeta23.Ncount_add (a := T₁) (b := T) (c := T₂) hT₁b (by linarith)
    have e2 := Zeta23.Ncount_add (a := T) (b := 2*T) (c := T₂) (by linarith) hT₂a
    rw [e1, e2]
    push_cast
    ring
  -- small windows are O(log T)
  have hlogsq : ∀ x : ℝ, 0 < x → x + 3 ≤ T ^ 2 → Real.log (x + 3) ≤ 2 * Real.log T := by
    intro x hx hxT
    calc Real.log (x + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) hxT
      _ = 2 * Real.log T := by
          rw [Real.log_pow]
          push_cast
          ring
  have hw1 : (Ncount T₁ T : ℝ) ≤ 2 * A₀ * Real.log T := by
    have hsub : Ncount T₁ T ≤ Ncount T₁ (T₁ + 1) :=
      Zeta23.Ncount_mono le_rfl (by linarith)
    calc (Ncount T₁ T : ℝ) ≤ (Ncount T₁ (T₁ + 1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * Real.log (|T₁| + 3) := hA₀ T₁
      _ ≤ A₀ * (2 * Real.log T) := by
          refine mul_le_mul_of_nonneg_left ?_ hA₀0
          rw [abs_of_pos (by linarith : 0 < T₁)]
          exact hlogsq T₁ (by linarith) (by nlinarith)
      _ = 2 * A₀ * Real.log T := by ring
  have hw2 : (Ncount (2*T) T₂ : ℝ) ≤ 2 * A₀ * Real.log T := by
    have hsub : Ncount (2*T) T₂ ≤ Ncount (2*T) (2*T + 1) :=
      Zeta23.Ncount_mono le_rfl hT₂b
    calc (Ncount (2*T) T₂ : ℝ) ≤ (Ncount (2*T) (2*T+1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * Real.log (|2*T| + 3) := hA₀ (2*T)
      _ ≤ A₀ * (2 * Real.log T) := by
          refine mul_le_mul_of_nonneg_left ?_ hA₀0
          rw [abs_of_pos (by linarith : 0 < 2*T)]
          exact hlogsq (2*T) (by linarith) (by nlinarith)
      _ = 2 * A₀ * Real.log T := by ring
  -- the ζ half-contour is O(log T)
  have hbk1 := hB T₁ (by linarith) hg1
  have hbk2 := hB T₂ (by linarith) hg2
  have hvert := vertical_two T₁ T₂
  have hζbound : |(halfContour (logDeriv riemannZeta) T₁ T₂).im|
      ≤ |CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂ := by
    have hlog₁0 : 0 ≤ Real.log T₁ := Real.log_nonneg h1T₁
    have hlog₂0 : 0 ≤ Real.log T₂ := Real.log_nonneg (by linarith)
    unfold halfContour
    have eim : ((∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I))
        + (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I
        - ∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im
        = (∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im
          + ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im
          - (∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im := by
      simp [Complex.add_im, Complex.sub_im]
    rw [eim]
    have hmulI : ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im
        = (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im :=
      congrArg Complex.im (intervalIntegral.integral_mul_const (μ := MeasureTheory.volume) I
        (fun t : ℝ => logDeriv riemannZeta (2 + t * I))).symm
    have h1 : |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im| ≤ |CB| * Real.log T₁ :=
      hbk1.trans (by
        have : CB * Real.log T₁ ≤ |CB| * Real.log T₁ :=
          mul_le_mul_of_nonneg_right (le_abs_self CB) hlog₁0
        linarith)
    have h2 : |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im| ≤ |CB| * Real.log T₂ :=
      hbk2.trans (by
        have : CB * Real.log T₂ ≤ |CB| * Real.log T₂ :=
          mul_le_mul_of_nonneg_right (le_abs_self CB) hlog₂0
        linarith)
    calc |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im
          + ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im
          - (∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im|
        ≤ |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im|
          + |((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im|
          + |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im| := by
          exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂ := by
          rw [hmulI]
          have := hvert
          linarith
  -- μ-integral bookkeeping
  have hμint : ∀ a b : ℝ, IntervalIntegrable mu MeasureTheory.volume a b :=
    fun a b => hμc.intervalIntegrable a b
  have hμsplit : (∫ t in T₁..T₂, mu t)
      = (∫ t in T₁..T, mu t) + (∫ t in T..(2*T), mu t) + ∫ t in (2*T)..T₂, mu t := by
    have e1 : (∫ t in T₁..(2*T), mu t) = (∫ t in T₁..T, mu t) + ∫ t in T..(2*T), mu t :=
      (intervalIntegral.integral_add_adjacent_intervals (hμint T₁ T) (hμint T (2*T))).symm
    have e2 : (∫ t in T₁..T₂, mu t) = (∫ t in T₁..(2*T), mu t) + ∫ t in (2*T)..T₂, mu t :=
      (intervalIntegral.integral_add_adjacent_intervals (hμint T₁ (2*T)) (hμint (2*T) T₂)).symm
    rw [e2, e1]
  have hμwin : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 2*T + 1 → |b - a| ≤ 1 →
      |∫ t in a..b, mu t| ≤ 2 * CM * Real.log T := by
    intro a b ha hab hb hba
    have hbound : ∀ t ∈ Set.uIoc a b, ‖mu t‖ ≤ CM * Real.log (2*T + 4) := by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht1 : 1 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2*T + 1 := le_trans ht.2 hb
      rw [Real.norm_eq_abs]
      refine (hCM t ht1).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCM0.le
      exact Real.log_le_log (by linarith) (by linarith)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs] at this
    have hlog24 : Real.log (2*T + 4) ≤ 2 * Real.log T := by
      calc Real.log (2*T + 4) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
        _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
    calc |∫ t in a..b, mu t| ≤ CM * Real.log (2*T+4) * |b - a| := this
      _ ≤ CM * (2 * Real.log T) * 1 := by
          refine mul_le_mul ?_ hba (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hlog24 hCM0.le
      _ = 2 * CM * Real.log T := by ring
  have hμ1 : |∫ t in T₁..T, mu t| ≤ 2 * CM * Real.log T :=
    hμwin T₁ T h1T₁ hT₁b (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hμ2 : |∫ t in (2*T)..T₂, mu t| ≤ 2 * CM * Real.log T :=
    hμwin (2*T) T₂ (by linarith) hT₂a (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hintmu := hCμ T (by linarith)
  have hT0 : (0:ℝ) < T := by linarith
  have hCμT : Cμ / T ≤ |Cμ| := by
    calc Cμ / T ≤ |Cμ| / T := by gcongr; exact le_abs_self _
      _ ≤ |Cμ| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
          linarith
      _ = |Cμ| := div_one _
  -- final assembly
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ1 : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hkey : (Ncount T (2*T) : ℝ) - T * ell1 T / (2 * Real.pi)
      = (1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
        + ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t)
        + ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)))
        - ((Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ)) := by
    have hΛim : (1/Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im
        = (1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
          + (1/Real.pi) * (halfContour (logDeriv Complex.Gammaℝ) T₁ T₂).im := by
      rw [hsplit, Complex.add_im]
      ring
    have h5 : (Ncount T₁ T₂ : ℝ)
        = (1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
          + ∫ t in T₁..T₂, mu t := by
      rw [hN, hΛim, hgam]
    rw [hμsplit] at h5
    have h6 := hadd
    linarith
  have hlogT₁ : Real.log T₁ ≤ Real.log T := Real.log_le_log (by linarith) hT₁b
  have hlogT₂ : Real.log T₂ ≤ 2 * Real.log T := by
    calc Real.log T₂ ≤ Real.log (T^2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  -- bound each piece
  have hNc1 : (0:ℝ) ≤ (Ncount T₁ T : ℝ) := Nat.cast_nonneg _
  have hNc2 : (0:ℝ) ≤ (Ncount (2*T) T₂ : ℝ) := Nat.cast_nonneg _
  have hA : |(1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im|
      ≤ 3 * |CB| * Real.log T + 1 := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1/Real.pi)]
    have step1 : (1/Real.pi) * |(halfContour (logDeriv riemannZeta) T₁ T₂).im|
        ≤ (1/Real.pi) * (|CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂) := by
      exact mul_le_mul_of_nonneg_left hζbound (by positivity)
    have hfrac : (1:ℝ)/Real.pi ≤ 1 := by
      rw [div_le_one hπ]
      exact hπ1
    have e1 : (1/Real.pi) * (|CB| * Real.log T₁) ≤ |CB| * Real.log T := by
      calc (1/Real.pi) * (|CB| * Real.log T₁) ≤ 1 * (|CB| * Real.log T₁) := by
            apply mul_le_mul_of_nonneg_right hfrac
            exact mul_nonneg (abs_nonneg _) (Real.log_nonneg h1T₁)
        _ = |CB| * Real.log T₁ := one_mul _
        _ ≤ |CB| * Real.log T := mul_le_mul_of_nonneg_left hlogT₁ (abs_nonneg _)
    have e2 : (1/Real.pi) * Real.pi = 1 := by field_simp
    have e3 : (1/Real.pi) * (|CB| * Real.log T₂) ≤ 2 * |CB| * Real.log T := by
      calc (1/Real.pi) * (|CB| * Real.log T₂) ≤ 1 * (|CB| * Real.log T₂) := by
            apply mul_le_mul_of_nonneg_right hfrac
            exact mul_nonneg (abs_nonneg _) (Real.log_nonneg (by linarith))
        _ = |CB| * Real.log T₂ := one_mul _
        _ ≤ |CB| * (2 * Real.log T) := mul_le_mul_of_nonneg_left hlogT₂ (abs_nonneg _)
        _ = 2 * |CB| * Real.log T := by ring
    calc (1/Real.pi) * |(halfContour (logDeriv riemannZeta) T₁ T₂).im|
        ≤ (1/Real.pi) * (|CB| * Real.log T₁) + (1/Real.pi) * Real.pi
          + (1/Real.pi) * (|CB| * Real.log T₂) := by
          rw [← mul_add, ← mul_add]
          exact step1
      _ ≤ |CB| * Real.log T + 1 + 2 * |CB| * Real.log T := by
          rw [e2]
          linarith
      _ = 3 * |CB| * Real.log T + 1 := by ring
  have hD : |(∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)| ≤ |Cμ| * Real.log T := by
    calc |(∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)| ≤ Cμ / T := hintmu
      _ ≤ |Cμ| := hCμT
      _ = |Cμ| * 1 := (mul_one _).symm
      _ ≤ |Cμ| * Real.log T := mul_le_mul_of_nonneg_left hlogT (abs_nonneg _)
  -- put it together
  simp only [zetaZeroConfig_N]
  rw [show T / (2 * Real.pi) * ell1 T = T * ell1 T / (2 * Real.pi) by ring, hkey]
  have htri : |(1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
        + ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t)
        + ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)))
        - ((Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ))|
      ≤ |(1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im|
        + (|∫ t in T₁..T, mu t| + |∫ t in (2*T)..T₂, mu t|
        + |(∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)|)
        + ((Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ)) := by
    have t1 := abs_sub (((1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
        + ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t)
        + ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)))))
      (((Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ)))
    have t2 := abs_add_le ((1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im)
      ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t)
        + ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)))
    have t3 := abs_add_le ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t))
      ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi))
    have t4 := abs_add_le (∫ t in T₁..T, mu t) (∫ t in (2*T)..T₂, mu t)
    have t5 : |(Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ)|
        = (Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ) := abs_of_nonneg (by positivity)
    linarith
  refine htri.trans ?_
  linarith [hA, hμ1, hμ2, hD, hw1, hw2]

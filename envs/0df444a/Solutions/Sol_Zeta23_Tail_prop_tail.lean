-- Prove2me | solution 1 for Zeta23.Tail.prop_tail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-17T23:52:32.932923+00:00
-- url     : https://prove2.me/submissions/291be17c-a802-4ad0-bc54-fe510ce4e6a3

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne
import Theorems.Thm_Zeta23_Tail_TailHyp_traceNorm_smul_Ez_le

-- from Zeta23.Tail.RankOne
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/RankOne.lean — the linear-algebra step of [prop:tail] (the paper §4.2):
eigenvalue bounds for a (possibly infinite) sum of rank-one matrices m_ρ u_ρ u_ρᵀ.


Paper, verbatim (proof of [prop:tail]): "Since E = ∑_{γ∉I'} m_ρ u_ρ u_ρᵀ and
‖uuᵀ‖ = ‖u‖₂², ‖E‖ ≤ ∑_{γ∉I'} m_ρ ‖u_ρ‖₂²  [eq:Enormsum]" … "The trace-norm bound follows
from the same chain, since ‖uuᵀ‖₁ = ‖u‖₂² as well".

Design (avoiding Schatten-norm machinery): the trace norm of a Hermitian
matrix is DEFINED here as traceNorm hE := ∑ᵢ |λᵢ(E)|, and the operator-norm bound is
delivered in the shape RHLinalg.weyl_posIndexAbove_le consumes, namely ∀ i, |λᵢ(E)| ≤ θ.
Both follow from one inequality, traceNorm hE ≤ ∑_ρ c_ρ ‖u_ρ‖₂², proved directly in the
eigenbasis: λᵢ = vᵢ* E vᵢ = ∑_ρ c_ρ ⟨vᵢ,u_ρ⟩⟨v̄ᵢ,u_ρ⟩, |⟨vᵢ,u_ρ⟩⟨v̄ᵢ,u_ρ⟩| ≤ (|⟨vᵢ,u_ρ⟩|² +
|⟨vᵢ,ū_ρ⟩|²)/2, and Parseval ∑ᵢ|⟨vᵢ,w⟩|² = ‖w‖² for the unitary eigenvector matrix.
NOTE u_ρ u_ρᵀ (Matrix.vecMulVec u u), NOT u_ρ u_ρ*: the u_ρ = (φ̂(γ_ρ − τ_k))_k are complex
for off-line zeros and the paper's E is complex-symmetric termwise; Hermitian-ness of the
total (from the ρ ↦ 1−ρ̄ symmetry) is taken as the hypothesis hE.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace Zeta23
namespace Tail

open RHLinalg

variable {n : Type*} [Fintype n] [DecidableEq n]






/-- Every |λᵢ(E)| is at most ‖E‖₁ (so a trace-norm bound is also an operator-norm bound in
the shape RHLinalg.weyl_posIndexAbove_le wants). -/
lemma abs_eigenvalues_le_traceNorm {E : Matrix n n ℂ} (hE : E.IsHermitian) (i : n) :
    |hE.eigenvalues i| ≤ traceNorm hE :=
  single_le_sum (f := fun i => |hE.eigenvalues i|) (fun _ _ => abs_nonneg _) (mem_univ i)




end Tail
end Zeta23
end
end

-- from Zeta23.Tail
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail.lean — Proposition [prop:tail] (the paper §4.2 "The tail"), assembled for the
concrete objects of Zeta23/Defs.lean.

Paper, verbatim: "Proposition [prop:tail]. Let A₀ ≥ 1 be an absolute constant such that
N(t+1)−N(t) ≤ A₀ log(t+3) for all t ≥ 0. Then for T ≥ T₀,
  ‖Ẽ‖ ≤ θ₀ := 4A₀ C₁² X^{1/2} log(4T)/D₀²,   C₁ := ‖φ″‖₁ = 2‖ϱ″‖₁/w,
so that θ₀ ≤ 32A₀‖ϱ″‖₁² l T^{λ/2−1} ≪ l T^{λ/2−1}. Moreover the trace norm satisfies
‖Ê‖₁ ≤ θ₀/(aL) ≤ 2θ₀/L."
Here E := G − A [eq:AE] is the contribution of the zeros with ordinate γ ∉ I' := (T−D₀, 2T+D₀],
D₀ := T^{1/2} [eq:D0] (including all zeros with γ ≤ 0), Ẽ := E/L,
Ê := E/(aL²) [eq:hatunits].

Structure of the proof (sub-files):
* Zeta23/Tail/RankOne.lean — ‖E‖, ‖E‖₁ ≤ ∑ m_ρ ‖u_ρ‖₂² for E = ∑ m_ρ u_ρ u_ρᵀ  [eq:Enormsum];
* Zeta23/Tail/Grid.lean    — ∑_{k<d} |γ−τ_k|⁻⁴ ≤ L·dist(γ,I)⁻³;
* Zeta23/Tail/Count.lean   — ∑_{γ∉I'} m_ρ dist(γ,I)⁻³ ≤ 4A₀ log(4T)/T, and N(I'∖I) ≪ D₀ l;
* this file              — [eq:hfbound] ⇒ ‖u_ρ k‖ ≤ e^{L/4}C₁|γ−τ_k|⁻², summability of the
  zero-side series entrywise, E = (the series over γ ∉ I'), and the two bounds in the exact
  shapes consumed downstream: ∀ i, |λᵢ(Ẽ)| ≤ θ₀ (for RHLinalg.weyl_posIndexAbove_le) and
  traceNorm Ê ≤ θ₀/(aL) (for [prop:zeroside-rank]).

Hypotheses taken (all proved elsewhere in the repository; none are Lean axioms):
* hloc  — PaperInputs.RvM.local (Hypotheses.lean), two-sided unit-window form;
* hdecay — [eq:hfbound] specialised to f = φ, in the exact shape of
  Zeta23.Params.norm_phiHat_sub_I_mul_le (Taper.lean), with C₁ := P.C1 T = ‖φ″‖₁;
* hEt/hEh — Hermitian-ness of Ẽ, Ê (from the ρ ↦ 1−ρ̄ symmetry).
-/

noncomputable section

open Matrix Finset Complex
open scoped ComplexOrder

namespace Zeta23
namespace Tail

open RHLinalg

/-! ### θ₀ and its size -/





/-! ### The local count from PaperInputs.RvM.local -/


/-! ### The vectors u_ρ and their decay from [eq:hfbound] -/

section Concrete

variable (Z : ZeroConfig) (P : Params) (T : ℝ)




variable {P T}




variable {Z}



end Concrete

/-! ### Summability of the zero-side series and E as the series over γ ∉ I' -/

section Series

variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}



namespace TailHyp

variable (H : TailHyp Z P T A₀ C₁)
include H

lemma L_pos : 0 < P.L T := by linarith [H.hL]












end TailHyp

/-! ### Proposition [prop:tail] -/


end Series

/-! ### E is Hermitian (real symmetric) — "since ρ and 1−ρ̄ have the same ordinate, both index
sets are invariant under ρ ↦ 1−ρ̄, so A and E are real symmetric" [eq:AE] -/

section Hermitian




variable {P : Params} {T : ℝ}


variable {Z : ZeroConfig} {A₀ C₁ : ℝ}





end Hermitian

/-! ### Exports in the shapes consumed by Zeta23/Assembly.lean (Assembly.TailInputs) -/

section Export

open Filter

variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}







end Export

end Tail
end Zeta23
end
open Matrix Finset Complex
open scoped ComplexOrder
open Zeta23
open Tail
open RHLinalg
variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}

theorem solution {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ} (H : TailHyp Z P T A₀ C₁)
    (ha : 0 < P.a T)
    (hEt : (P.tilde T (Z.Ez P T)).IsHermitian) (hEh : (P.hat T (Z.Ez P T)).IsHermitian) :
    (∀ i, |hEt.eigenvalues i| ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T) ∧
    traceNorm hEt ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T ∧
    traceNorm hEh ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T / (P.a T * P.L T) := by
  have hL := H.L_pos
  -- tilde: κ = L⁻¹
  have htilde : P.tilde T (Z.Ez P T) = (((P.L T)⁻¹ : ℝ) : ℂ) • Z.Ez P T := by
    unfold Params.tilde; rw [Complex.ofReal_inv]
  have hEt' : ((((P.L T)⁻¹ : ℝ) : ℂ) • Z.Ez P T).IsHermitian := htilde ▸ hEt
  have h1 : traceNorm hEt ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T := by
    have h := H.traceNorm_smul_Ez_le (κ := (P.L T)⁻¹) (by positivity) hEt'
    have e : (P.L T)⁻¹ * (P.L T * theta0 A₀ H.K T) = theta0 A₀ H.K T := by
      field_simp
    rw [e] at h
    convert h using 2; rfl
  -- hat: κ = (a L²)⁻¹
  have hhat : P.hat T (Z.Ez P T) = (((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • Z.Ez P T := by
    unfold Params.hat; push_cast; rfl
  have hEh' : ((((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • Z.Ez P T).IsHermitian := hhat ▸ hEh
  have h2 : traceNorm hEh ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T / (P.a T * P.L T) := by
    have h := H.traceNorm_smul_Ez_le (κ := (P.a T * P.L T ^ 2)⁻¹) (by positivity) hEh'
    have e : (P.a T * P.L T ^ 2)⁻¹ * (P.L T * theta0 A₀ H.K T)
        = theta0 A₀ H.K T / (P.a T * P.L T) := by
      field_simp
    rw [e] at h
    convert h using 2; rfl
  exact ⟨fun i => (abs_eigenvalues_le_traceNorm hEt i).trans h1, h1, h2⟩

-- Prove2me | solution 1 for Zeta23.Tail.TailHyp.Ez_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-17T23:56:56.635202+00:00
-- url     : https://prove2.me/submissions/8a9957fb-2841-4171-ab9c-862b472e3efd

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
import Theorems.Thm_Zeta23_Tail_TailHyp_hasSum_Ez

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



lemma not_mem_sA_iff (ρ : Z.carrier) : ρ ∉ H.sA ↔ InTail T (ρ : ℂ).im := by
  rw [sA, Set.Finite.mem_toFinset]; simp










end TailHyp

/-! ### Proposition [prop:tail] -/


end Series

/-! ### E is Hermitian (real symmetric) — "since ρ and 1−ρ̄ have the same ordinate, both index
sets are invariant under ρ ↦ 1−ρ̄, so A and E are real symmetric" [eq:AE] -/

section Hermitian

lemma reflect_im (ρ : ℂ) : (reflect ρ).im = ρ.im := by simp [reflect]

lemma reflect_reflect (ρ : ℂ) : reflect (reflect ρ) = ρ := by simp [reflect]

lemma gammaOf_reflect (ρ : ℂ) : gammaOf (reflect ρ) = (starRingEnd ℂ) (gammaOf ρ) := by
  apply Complex.ext <;> simp [gammaOf, reflect]; ring

variable {P : Params} {T : ℝ}

/-- conj φ̂(z̄) = φ̂(z) ("since φ̂ is real on ℝ") transports u_ρ to u_{1−ρ̄}:
u_{1−ρ̄} = conj u_ρ. -/
lemma uvec_reflect
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z))
    (ρ : ℂ) (k : Fin (P.d T)) :
    uvec P T (reflect ρ) k = (starRingEnd ℂ) (uvec P T ρ k) := by
  unfold uvec
  rw [gammaOf_reflect, ← hconj, map_sub, Complex.conj_ofReal]

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
variable {P : Params} {T : ℝ}
variable {Z : ZeroConfig} {A₀ C₁ : ℝ}

theorem solution (H : TailHyp Z P T A₀ C₁)
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    (Z.Ez P T).IsHermitian := by
  classical
  -- the involution x ↦ 1 − x̄ on the tail subtype
  have hrefl : ∀ x : {ρ : Z.carrier // ρ ∉ H.sA},
      (⟨reflect ((x : Z.carrier) : ℂ), Z.reflect_mem _ (x : Z.carrier).2⟩ : Z.carrier) ∉ H.sA := by
    intro x
    rw [H.not_mem_sA_iff]
    simp only [reflect_im]
    exact (H.not_mem_sA_iff _).mp x.2
  set σ : {ρ : Z.carrier // ρ ∉ H.sA} → {ρ : Z.carrier // ρ ∉ H.sA} :=
    fun x => ⟨⟨reflect ((x : Z.carrier) : ℂ), Z.reflect_mem _ (x : Z.carrier).2⟩, hrefl x⟩ with hσdef
  have hσ : Function.Involutive σ := fun x => by
    apply Subtype.ext; apply Subtype.ext
    simp only [hσdef, reflect_reflect]
  set f : {ρ : Z.carrier // ρ ∉ H.sA} → Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
    fun x => ((Z.mult (x : Z.carrier) : ℝ) : ℂ) •
      vecMulVec (uvec P T (x : Z.carrier)) (uvec P T (x : Z.carrier)) with hfdef
  have hf : HasSum f (Z.Ez P T) := H.hasSum_Ez
  have hfH : HasSum (fun x => (f x)ᴴ) (Z.Ez P T)ᴴ := hf.matrix_conjTranspose
  have hfσ : ∀ x, (f x)ᴴ = f (σ x) := by
    intro x
    ext k l
    have hm : Z.mult (reflect ((x : Z.carrier) : ℂ)) = Z.mult ((x : Z.carrier) : ℂ) :=
      Z.mult_reflect _ (x : Z.carrier).2
    simp only [hfdef, hσdef, conjTranspose_apply, Matrix.smul_apply, vecMulVec_apply,
      smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal, uvec_reflect hconj, hm]
    ring
  have h2 : HasSum (f ∘ (hσ.toPerm σ)) (Z.Ez P T)ᴴ := by
    have : (f ∘ (hσ.toPerm σ)) = fun x => (f x)ᴴ := by
      funext x; simp [Function.comp, hfσ]
    rw [this]; exact hfH
  rw [Equiv.hasSum_iff] at h2
  exact h2.unique hf

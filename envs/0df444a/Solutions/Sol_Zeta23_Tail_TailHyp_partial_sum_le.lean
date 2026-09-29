-- Prove2me | solution 1 for Zeta23.Tail.TailHyp.partial_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-17T23:59:19.616819+00:00
-- url     : https://prove2.me/submissions/f509769d-2860-4720-a341-1ef41c09bb61

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
import Theorems.Thm_Zeta23_Tail_LocalCount_ofWindowCount
import Theorems.Thm_Zeta23_Tail_norm_sq_uvec_le
import Theorems.Thm_Zeta23_Tail_tail_count_sum_le

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


lemma not_mem_sA_iff (ρ : Z.carrier) : ρ ∉ H.sA ↔ InTail T (ρ : ℂ).im := by
  rw [sA, Set.Finite.mem_toFinset]; simp










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
open TailHyp
variable (H : TailHyp Z P T A₀ C₁)
include H

theorem solution (u : Finset {ρ : Z.carrier // ρ ∉ H.sA}) :
    ∑ x ∈ u, (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖uvec P T (x : Z.carrier) k‖ ^ 2
      ≤ P.L T * theta0 A₀ H.K T := by
  classical
  have hLC := LocalCount.ofWindowCount Z H.hA₀ H.hloc
  -- push u forward to a Finset of the carrier; all its elements are tail zeros
  set s : Finset Z.carrier := u.map (Function.Embedding.subtype _) with hs
  have hs_tail : ∀ ρ ∈ s, InTail T ((fun ρ : Z.carrier => (ρ : ℂ).im) ρ) := by
    intro ρ hρ
    rw [hs, Finset.mem_map] at hρ
    obtain ⟨x, _, rfl⟩ := hρ
    exact (H.not_mem_sA_iff _).mp x.2
  have hcount := tail_count_sum_le hLC H.hT s hs_tail
  have hterm : ∀ x ∈ u,
      (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖uvec P T (x : Z.carrier) k‖ ^ 2
        ≤ H.K ^ 2 * P.L T *
          ((Z.mult (x : Z.carrier) : ℝ) * ((distI T ((x : Z.carrier) : ℂ).im) ^ 3)⁻¹) := by
    intro x _
    have hx : InTail T ((x : Z.carrier) : ℂ).im := (H.not_mem_sA_iff _).mp x.2
    have h := norm_sq_uvec_le H.hT H.hL H.hC₁ H.hdecay (x : Z.carrier).2 hx
    have hm : (0:ℝ) ≤ Z.mult (x : Z.carrier) := Nat.cast_nonneg _
    calc _ ≤ (Z.mult (x : Z.carrier) : ℝ) * (H.K ^ 2 * P.L T * ((distI T ((x : Z.carrier) : ℂ).im) ^ 3)⁻¹) :=
          mul_le_mul_of_nonneg_left h hm
      _ = _ := by ring
  calc _ ≤ ∑ x ∈ u, H.K ^ 2 * P.L T *
          ((Z.mult (x : Z.carrier) : ℝ) * ((distI T ((x : Z.carrier) : ℂ).im) ^ 3)⁻¹) :=
        sum_le_sum hterm
    _ = H.K ^ 2 * P.L T *
          ∑ ρ ∈ s, (Z.mult ρ : ℝ) * ((distI T (ρ : ℂ).im) ^ 3)⁻¹ := by
        rw [← mul_sum, hs, Finset.sum_map]; rfl
    _ ≤ H.K ^ 2 * P.L T * (4 * A₀ * Real.log (4 * T) / T) :=
        mul_le_mul_of_nonneg_left hcount (by have := H.L_pos; positivity)
    _ = P.L T * theta0 A₀ H.K T := by unfold theta0; ring

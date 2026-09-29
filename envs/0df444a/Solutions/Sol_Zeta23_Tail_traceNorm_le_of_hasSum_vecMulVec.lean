-- Prove2me | solution 1 for Zeta23.Tail.traceNorm_le_of_hasSum_vecMulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-17T23:56:00.205313+00:00
-- url     : https://prove2.me/submissions/551daa03-e268-470c-9fe2-b33cd581c5b6

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_Tail_RankOne
import Theorems.Thm_RHLinalg_hermForm_specMap

-- from Zeta23.LinAlg.Sylvester
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper, by the
paper's authors, and are incorporated here unchanged; they have no upstream outside this project (see README
§ Provenance and attribution).
-/

/-!
# Sylvester's law of inertia for Hermitian matrices (subspace bound)

We prove the key inequality: any subspace `W ⊆ 𝕜ⁿ` on which the Hermitian
form `x ↦ Re(xᴴAx)` is positive definite has dimension at most
`posIndex hA`.

The proof is short: `A = A₊ − A₋` with both parts PSD (`HermitianPosPart`).
If `A₊ · x = 0` for `x ∈ W ∖ {0}`, then `xᴴAx = −xᴴA₋x ≤ 0`, contradicting
positive-definiteness on `W`. So `(A₊ *ᵥ ·)|_W` is injective, hence
`dim W ≤ rank A₊ = posIndex hA`.

This is the engine behind `lem:inertia`: pulling back a Hermitian form
cannot increase its positive index.
-/

noncomputable section

open Matrix Finset Submodule
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]









/-- `hermForm I x = ∑ᵢ ‖xᵢ‖²` (the squared `ℓ²` norm). -/
lemma hermForm_one (x : n → 𝕜) :
    hermForm (1 : Matrix n n 𝕜) x = ∑ i, ‖x i‖ ^ 2 := by
  unfold hermForm
  simp only [one_mulVec, dotProduct, Pi.star_apply, RCLike.star_def, map_sum,
    RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- `∑ᵢ ‖cᵢ‖²` is preserved by the unitary change of variables `c = Uᴴx`. -/
lemma sum_normSq_unitary_mulVec {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (x : n → 𝕜) :
    ∑ i, ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2
      = ∑ i, ‖x i‖ ^ 2 := by
  have h := hermForm_specMap hA 1 x
  simp only [Pi.one_apply, one_mul] at h
  rw [← h, ← hermForm_one x]
  unfold hermForm
  rw [show specMap hA 1 = (1 : Matrix n n 𝕜) by unfold specMap; simp]






end RHLinalg
end
end

-- from Zeta23.Tail.RankOne
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







/-- ab ≤ (a² + b²)/2. -/
lemma mul_le_half_sq_add_sq (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]



end Tail
end Zeta23
end
open Matrix Finset
open scoped ComplexOrder
open Zeta23
open Tail
open RHLinalg
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem solution {ι : Type*} {E : Matrix n n ℂ}
    (hE : E.IsHermitian) (c : ι → ℝ) (hc : ∀ ρ, 0 ≤ c ρ) (u : ι → n → ℂ) {S : ℝ}
    (hS : HasSum (fun ρ => c ρ * ∑ k, ‖u ρ k‖ ^ 2) S)
    (hEsum : HasSum (fun ρ => ((c ρ : ℝ) : ℂ) • vecMulVec (u ρ) (u ρ)) E) :
    traceNorm hE ≤ S := by
  set U : Matrix n n ℂ := (hE.eigenvectorUnitary : Matrix n n ℂ) with hU
  -- coordinates of u_ρ and ū_ρ in the eigenbasis
  set α : n → ι → ℂ := fun i ρ => (star U *ᵥ u ρ) i with hα
  set β : n → ι → ℂ := fun i ρ => (star U *ᵥ star (u ρ)) i with hβ
  -- Step 1: entrywise HasSum for E.
  have hEkl : ∀ k l, HasSum (fun ρ => ((c ρ : ℝ) : ℂ) * (u ρ k * u ρ l)) (E k l) := by
    intro k l
    have := (Pi.hasSum.mp (Pi.hasSum.mp hEsum k)) l
    simpa only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul] using this
  -- Step 2: λᵢ = vᵢ* E vᵢ = ∑_ρ c_ρ αᵢρ · conj(βᵢρ), vᵢ = i-th column of U.
  have hlam : ∀ i, HasSum (fun ρ => ((c ρ : ℝ) : ℂ) * (α i ρ * star (β i ρ)))
      ((hE.eigenvalues i : ℝ) : ℂ) := by
    intro i
    have hv : (fun k => U k i) = (hE.eigenvectorBasis i).ofLp := by
      funext k; exact hE.eigenvectorUnitary_apply k i
    have hEv : E *ᵥ (fun k => U k i) = ((hE.eigenvalues i : ℝ) : ℂ) • (fun k => U k i) := by
      have h := hE.mulVec_eigenvectorBasis i
      rw [← hv] at h
      rw [h]
      funext k
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    have hvv : star (fun k => U k i) ⬝ᵥ (fun k => U k i) = 1 := by
      have h1 := Matrix.UnitaryGroup.star_mul_self hE.eigenvectorUnitary
      have := congrFun (congrFun h1 i) i
      simpa [hU, Matrix.mul_apply, Matrix.star_apply, dotProduct] using this
    have hquad : star (fun k => U k i) ⬝ᵥ (E *ᵥ fun k => U k i)
        = ((hE.eigenvalues i : ℝ) : ℂ) := by
      rw [hEv, dotProduct_smul, hvv, smul_eq_mul, mul_one]
    have hexp : star (fun k => U k i) ⬝ᵥ (E *ᵥ fun k => U k i)
        = ∑ k, star (U k i) * ∑ l, E k l * U l i := by
      simp only [dotProduct, mulVec, Pi.star_apply]
    have h2 : HasSum (fun ρ => ∑ k, star (U k i) *
        ∑ l, (((c ρ : ℝ) : ℂ) * (u ρ k * u ρ l)) * U l i)
        (∑ k, star (U k i) * ∑ l, E k l * U l i) := by
      apply hasSum_sum; intro k _
      apply HasSum.mul_left
      apply hasSum_sum; intro l _
      exact (hEkl k l).mul_right _
    rw [← hexp, hquad] at h2
    convert h2 using 1
    funext ρ
    simp only [hα, hβ, mulVec, dotProduct, Matrix.star_apply, Pi.star_apply, star_sum, star_mul',
      star_star]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  -- Step 3: the majorant Fᵢρ := c_ρ (|αᵢρ|² + |βᵢρ|²)/2, with ∑ᵢ Fᵢρ = c_ρ ‖u_ρ‖² (Parseval).
  set F : n → ι → ℝ := fun i ρ => c ρ * ((‖α i ρ‖ ^ 2 + ‖β i ρ‖ ^ 2) / 2) with hF
  have hF_sum : ∀ ρ, ∑ i, F i ρ = c ρ * ∑ k, ‖u ρ k‖ ^ 2 := by
    intro ρ
    simp only [hF, hα, hβ]
    rw [← mul_sum, ← sum_div, sum_add_distrib, sum_normSq_unitary_mulVec hE (u ρ),
      sum_normSq_unitary_mulVec hE (star (u ρ))]
    congr 1
    simp only [Pi.star_apply, norm_star]
    ring
  have hF_nonneg : ∀ i ρ, 0 ≤ F i ρ := fun i ρ => by
    have := hc ρ; simp only [hF]; positivity
  have hF_summable : ∀ i, Summable (F i) := by
    intro i
    refine Summable.of_nonneg_of_le (hF_nonneg i) (fun ρ => ?_) hS.summable
    rw [← hF_sum ρ]
    exact single_le_sum (f := fun j => F j ρ) (fun j _ => hF_nonneg j ρ) (mem_univ i)
  -- Step 4: |λᵢ| ≤ ∑' ρ, Fᵢρ.
  have hbound : ∀ i, |hE.eigenvalues i| ≤ ∑' ρ, F i ρ := by
    intro i
    have h := HasSum.norm_le_of_bounded (hlam i) (hF_summable i).hasSum (fun ρ => ?_)
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using h
    · rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (hc ρ)]
      simp only [hF]
      exact mul_le_mul_of_nonneg_left (mul_le_half_sq_add_sq _ _) (hc ρ)
  -- Step 5: sum over i and swap the finite sum with the series.
  calc traceNorm hE = ∑ i, |hE.eigenvalues i| := rfl
    _ ≤ ∑ i, ∑' ρ, F i ρ := sum_le_sum fun i _ => hbound i
    _ = ∑' ρ, ∑ i, F i ρ := (Summable.tsum_finsetSum (fun i _ => hF_summable i)).symm
    _ = ∑' ρ, c ρ * ∑ k, ‖u ρ k‖ ^ 2 := tsum_congr hF_sum
    _ = S := hS.tsum_eq

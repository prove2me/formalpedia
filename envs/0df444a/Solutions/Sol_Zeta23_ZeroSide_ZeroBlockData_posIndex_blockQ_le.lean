-- Prove2me | solution 1 for Zeta23.ZeroSide.ZeroBlockData.posIndex_blockQ_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:09:01.060469+00:00
-- url     : https://prove2.me/submissions/5294db25-49ae-426d-8b88-8b35adb0a9f6

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_ZeroSide
import Theorems.Thm_RHLinalg_posDefOn_range_hermPosPart
import Theorems.Thm_RHLinalg_posIndex_add_le
import Theorems.Thm_RHLinalg_rank_specMap
import Theorems.Thm_Zeta23_ZeroSide_ZeroBlockData_sum_split
import Theorems.Thm_Zeta23_ZeroSide_posIndex_smul_pos

-- from Zeta23.LinAlg.PosIndex
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
# Positive index of a Hermitian matrix

For a Hermitian matrix `A` over `𝕜 = ℝ` or `ℂ`, the *positive index*
`n₊(A)` is the number of strictly positive eigenvalues. By Sylvester's law
of inertia this equals the maximal dimension of a subspace on which the
Hermitian form `x ↦ xᴴ A x` is positive definite.

This file defines `posIndex` via the eigenvalue count, together with the
real-valued trace `rtrace` and squared Frobenius norm `frobSq` needed for
the rank–trace inequality (paper §3, `lem:ranktrace`).
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]





/-- For a PSD Hermitian matrix the positive index is the rank (every nonzero
eigenvalue is positive). -/
lemma posIndex_eq_rank_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    posIndex hA.isHermitian = A.rank := by
  rw [hA.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  unfold posIndex
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq]
  exact ⟨fun h => h.ne', fun h => (hA.eigenvalues_nonneg i).lt_of_ne' h⟩




section Reindex

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)





end Reindex


end RHLinalg
end
end

-- from Zeta23.LinAlg.HermitianPosPart
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
# Positive and negative parts of a Hermitian matrix

For a Hermitian matrix `Q` with spectral decomposition `Q = U diag(λ) Uᴴ`,
define `Q₊ := U diag(λ⁺) Uᴴ` and `Q₋ := U diag(λ⁻) Uᴴ` where
`λ⁺ = max(λ,0)`, `λ⁻ = max(−λ,0)`.

Then `Q = Q₊ − Q₋`, both are PSD, `Q₊ Q₋ = 0`, and `rank Q₊ = n₊(Q)`.

This is equivalent to the CFC `Q⁺`/`Q⁻` via `Matrix.IsHermitian.cfc_eq`, but
the direct spectral construction keeps the eigenvalue bookkeeping explicit,
which is what the rank–trace proof needs.
-/

noncomputable section

open Matrix Finset Unitary
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]












section PosNegPart

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)









lemma rank_hermPosPart : (hermPosPart hA).rank = posIndex hA := by
  unfold hermPosPart posIndex
  rw [rank_specMap]
  congr 1; ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq, posPart_eq_zero, not_le]






end PosNegPart

end RHLinalg
end
end

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






omit [DecidableEq n] in
/-- `hermForm A x ≥ 0` when `A` is PSD. -/
lemma hermForm_nonneg_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (x : n → 𝕜) : 0 ≤ hermForm A x :=
  hA.re_dotProduct_nonneg x








/-- The dimension of `range A₊` is `posIndex hA`. -/
lemma finrank_range_hermPosPart {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Module.finrank 𝕜 (LinearMap.range (hermPosPart hA).mulVecLin) = posIndex hA := by
  rw [← rank_hermPosPart hA]; rfl

/-- **Sylvester's law of inertia (subspace characterization)**. -/
theorem posIndex_eq_max_finrank_posDefOn {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ W : Submodule 𝕜 (n → 𝕜), PosDefOn A W ∧
      Module.finrank 𝕜 W = posIndex hA :=
  ⟨_, posDefOn_range_hermPosPart hA, finrank_range_hermPosPart hA⟩

end RHLinalg
end
end

-- from Zeta23.ZeroSide
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ZeroSide.lean — paper §4 "The zero side: signature and rank", Block structure + prop:block.
Builds on the §3 formalization (Zeta23.LinAlg, namespace RHLinalg): posIndex, posIndex_add_le
(subadditivity, the corollary of lem:inertia), Sylvester's subspace characterization,
posIndex_eq_rank_of_posSemidef.

Reference text: the paper, labels [eq:AE], [eq:Ncount], [eq:hatunits], [prop:block].

Design: this file is ζ-free. Section 1 is generic Hermitian-matrix
lemmas missing from Mathlib/RHLinalg. Section 2 proves prop:block for an ABSTRACT finite
zero configuration `ZeroBlockData` (distinct points z with explicit multiplicities m z ≥ 1,
the involution σ = (ρ ↦ 1 − conj ρ) with m ∘ σ = m, and evaluation vectors v z = (φ̂(γ_z − τ_k))_k with
v (σ z) = conj ∘ v z). Section 3 instantiates from Defs.lean's ZeroConfig, φ̂, τ_k, a, L and
lem:poisson.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide

/-! ## Section 1. Generic lemmas on rank and positive index -/

section Generic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- `rank (A + B) ≤ rank A + rank B` for matrices (Mathlib has this only for linear maps). -/
lemma rank_add_le (A B : Matrix n n 𝕜) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  refine le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  rintro _ ⟨x, rfl⟩
  simp only [mulVecLin_apply, add_mulVec]
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

omit [DecidableEq n] in
/-- Rank of a finite sum is at most the sum of given rank bounds. -/
lemma rank_sum_le {α : Type*} (s : Finset α) (f : α → Matrix n n 𝕜) (b : α → ℕ)
    (h : ∀ a ∈ s, (f a).rank ≤ b a) : (∑ a ∈ s, f a).rank ≤ ∑ a ∈ s, b a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (rank_add_le _ _).trans
      (Nat.add_le_add (h a (mem_insert_self a s)) (ih fun x hx => h x (mem_insert_of_mem hx)))

omit [DecidableEq n] in
/-- A scalar multiple of a rank-one matrix `w vᵀ` has rank at most one. -/
lemma rank_smul_vecMulVec_le (c : 𝕜) (w v : n → 𝕜) :
    (c • vecMulVec w v).rank ≤ 1 := by
  rw [← smul_vecMulVec]
  exact rank_vecMulVec_le _ _



/-- If the Hermitian form of `A` is nonpositive everywhere then `n₊(A) = 0`. -/
lemma posIndex_eq_zero_of_hermForm_nonpos {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (h : ∀ x, hermForm A x ≤ 0) : posIndex hA = 0 := by
  obtain ⟨W, hW, hdim⟩ := posIndex_eq_max_finrank_posDefOn hA
  rw [← hdim, Submodule.finrank_eq_zero]
  by_contra hne
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).mp hne
  exact absurd (hW x hxW hx0) (not_lt.mpr (h x))

/-- `n₊(−N) = 0` for `N ⪰ 0`. -/
lemma posIndex_neg_eq_zero_of_posSemidef {N : Matrix n n 𝕜} (hN : N.PosSemidef) :
    posIndex hN.isHermitian.neg = 0 := by
  refine posIndex_eq_zero_of_hermForm_nonpos _ fun x => ?_
  have : hermForm (-N) x = - hermForm N x := by
    unfold hermForm; rw [neg_mulVec, dotProduct_neg, map_neg]
  rw [this, neg_nonpos]
  exact hermForm_nonneg_of_posSemidef hN x

/-- `n₊(P − N) ≤ rank P` for `P, N ⪰ 0`: subadditivity (lem:inertia) plus `n₊(P) = rank P`, `n₊(−N) = 0`. -/
lemma posIndex_sub_le_rank {P N : Matrix n n 𝕜} (hP : P.PosSemidef) (hN : N.PosSemidef) :
    posIndex (hP.isHermitian.sub hN.isHermitian) ≤ P.rank := by
  have h := posIndex_add_le hP.isHermitian hN.isHermitian.neg
  rw [posIndex_eq_rank_of_posSemidef hP, posIndex_neg_eq_zero_of_posSemidef hN, add_zero] at h
  convert h using 2; exact (sub_eq_add_neg P N)



end Generic

/-! ## Section 2. The abstract block structure (paper §4: [eq:AE], Block structure, [eq:Ncount], [prop:block])

Paper §4, Block structure, verbatim: "Let 𝒵(I') be the set of distinct zeros with γ ∈ I'. Classify its
points as follows: 𝒮₁: β = ½ and m_ρ = 1 (simple zeros on the line); s₁ := #𝒮₁; 𝒮₂: β = ½ and
m_ρ ≥ 2; s₂ := #𝒮₂; 𝒫: unordered pairs {ρ, 1−ρ̄} with β ≠ ½ (both members lie in 𝒵(I'), they are
distinct points, and m_{1−ρ̄} = m_ρ); p := #𝒫. Thus #𝒵(I') = s₁+s₂+2p and, counting with
multiplicity, N(I') = Σ_{𝒮₁} 1 + Σ_{𝒮₂} m_ρ + Σ_{𝒫} 2m_ρ ≥ s₁+2s₂+2p. [eq:Ncount]
Write N_on(I') := Σ_{ρ∈𝒮₁∪𝒮₂} m_ρ, so that also N(I') ≥ N_on(I') + 2p."

We encode 𝒵(I') as a finite index type ι, the grid {0,…,d−1} as a finite type d, and carry:
multiplicities m (≥ 1, explicit — zeros are DISTINCT points), the involution σ = (ρ ↦ 1−ρ̄)
restricted to 𝒵(I') (it preserves the ordinate, hence 𝒵(I')), and the evaluation vectors
u_ρ = (φ̂(γ_ρ − τ_k))_{k<d} ∈ ℂ^d with u_{1−ρ̄} = conj u_ρ (from γ_{1−ρ̄} = conj γ_ρ, τ_k ∈ ℝ, and
conj φ̂(z̄) = φ̂(z) [subsec:family after eq:fk]). On-line ⟺ β = ½ ⟺ σ ρ = ρ.
-/

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]


namespace ZeroBlockData

variable (D : ZeroBlockData ι d)









variable {D}



variable (D) (P : D.PairReps)











/-! ### The matrix A [eq:AE] and its decomposition -/








omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
lemma star_xv (z : ι) : star (D.xv z) = D.xv z := by
  funext k; simp [xv]
omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
lemma star_yv (z : ι) : star (D.yv z) = D.yv z := by
  funext k; simp [yv]

omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
/-- The pair block: m(u uᵀ + ū ūᵀ) = 2m(x xᵀ − y yᵀ) for u = x + iy. -/
lemma pair_term (z : ι) :
    (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)
      + (D.m (D.σ z) : ℂ) • vecMulVec (D.v (D.σ z)) (D.v (D.σ z))
      = ((2 * D.m z : ℝ) : ℂ) • vecMulVec (D.xv z) (D.xv z)
        - ((2 * D.m z : ℝ) : ℂ) • vecMulVec (D.yv z) (D.yv z) := by
  rw [D.m_σ, D.v_σ]
  ext k l
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
    Pi.star_apply, smul_eq_mul, xv, yv, RCLike.star_def]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring


/-- A = (on-line part) + (Σ_𝒫 2m x xᵀ − Σ_𝒫 2m y yᵀ). -/
lemma blockA_decomp : D.blockA = D.onPart + (D.rePart P - D.imPart P) := by
  unfold blockA onPart rePart imPart
  rw [D.sum_split P, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun z _ => D.pair_term z



lemma rePart_posSemidef : (D.rePart P).PosSemidef := by
  unfold rePart
  exact posSemidef_sum _ fun z _ => posSemidef_smul_vecMulVec (D.star_xv z) (by positivity)

lemma imPart_posSemidef : (D.imPart P).PosSemidef := by
  unfold imPart
  exact posSemidef_sum _ fun z _ => posSemidef_smul_vecMulVec (D.star_yv z) (by positivity)


lemma rank_rePart_le : (D.rePart P).rank ≤ P.p := by
  unfold rePart PairReps.p
  refine (rank_sum_le _ _ (fun _ => 1) fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp


lemma posIndex_congr {A B : Matrix d d ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    posIndex hA = posIndex hB := by
  subst h; rfl




/-! ### prop:block (ii): Â = P + Q in the units [eq:hatunits] -/




lemma blockQ_eq (c : ℝ) : D.blockQ c = ((c⁻¹ : ℝ) : ℂ) • (D.rePart P - D.imPart P) := by
  unfold blockQ; congr 1
  rw [D.blockA_decomp P, add_sub_cancel_left]










end ZeroBlockData

end Block

/-! ## Section 3. Instantiation against Zeta23.Defs: 𝒵(I') ⊂ ZeroConfig, A = Z.Az P T  [eq:AE]

Here ι := 𝒵(I') = Z.ZIprime T (finite by ZeroConfig.finite_window), d := Fin (P.d T),
m := Z.mult, σ := reflect = (ρ ↦ 1 − conj ρ), v ρ k := φ̂(γ_ρ − τ_k) with γ_ρ = gammaOf ρ, τ_k = P.tau T k.
The analytic inputs are explicit hypotheses of this section (discharged elsewhere in the
repository from Zeta23.Taper / Zeta23.Poisson: Params.phiHat_conj, Params.phiHat_ofReal,
Params.hasSum_phiHatR_sq):
  hconj : ∀ z, φ̂(conj z) = conj φ̂(z)                       [subsec:family, after eq:fk]
  hreal : ∀ r : ℝ, φ̂(r) = φ̂_ℝ(r) (φ̂ real on ℝ)
  hPois : ∀ γ : ℝ, HasSum (k ↦ φ̂(γ − τ_k)²) (aL²)            [lem:poisson, "in particular"]
-/

section Inst

open Zeta23 Classical

variable (Z : ZeroConfig) (T : ℝ)













section mk
variable {d : Type*} [Fintype d] [DecidableEq d] (v : ZI Z T → d → ℂ)
    (hv : ∀ z : ZI Z T, v ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (v z))

@[simp] lemma mkData_m (z : ZI Z T) : (mkData Z T v hv).m z = Z.mult z := rfl
@[simp] lemma mkData_v : (mkData Z T v hv).v = v := rfl














end mk







/-! ### The matrix A = Z.Az P T and prop:block for Ã := P.tilde T A, Â := P.hat T A -/

variable (P : Params)



variable {Z T P}


variable (Z T P)






















end Inst

/-! ## Section 4. Packaging for Assembly: `Zeta23.Assembly.BlockInputs` -/

section Package

open Zeta23


/-! ### The export for Main.lean: eventually-in-T form with only the genuinely external inputs left

hconj / hreal are discharged here from Zeta23.GzGp.phiHat_conj / phiHat_ofReal
(φ real and even); 0 < L eventually since L = λ·log(T/2π) → ∞. What remains as hypotheses, both in
∀ᶠ form: positivity of a [eq:abdef] (Main has it from Taper: 1 − 2w/L ≤ b ≤ a) and lem:poisson
(Zeta23.Poisson: Params.hasSum_phiHatR_sq). Zeta23/ZeroSide/Final.lean discharges those two as well. -/



end Package

end Zeta23.ZeroSide
end
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23
open Zeta23.ZeroSide
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
open ZeroBlockData
variable (D : ZeroBlockData ι d)
variable {D}
variable (D) (P : D.PairReps)

theorem solution {c : ℝ} (hc : 0 < c) :
    posIndex (D.blockQ_isHermitian c) ≤ P.p := by
  have hRe := D.rePart_posSemidef P
  have hIm := D.imPart_posSemidef P
  have hH := hRe.isHermitian.sub hIm.isHermitian
  rw [posIndex_congr (D.blockQ_isHermitian c) (isHermitian_real_smul hH c⁻¹) (D.blockQ_eq P c)]
  have key : posIndex (isHermitian_real_smul hH c⁻¹) = posIndex hH :=
    posIndex_smul_pos hH (inv_pos.mpr hc) _
  rw [key]
  exact (posIndex_sub_le_rank hRe hIm).trans (D.rank_rePart_le P)

-- Prove2me | solution 1 for RHLinalg.vonNeumann_trace_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:44:15.474558+00:00
-- url     : https://prove2.me/submissions/e4b68952-c5e4-4810-bf4b-c43ecd6434ed

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Theorems.Thm_RHLinalg_bilinear_doublyStochastic_le_of_monovary
import Theorems.Thm_RHLinalg_normSqMatrix_mem_doublyStochastic_of_unitary
import Theorems.Thm_RHLinalg_re_trace_mul_eq_eigenvalue_bilinear

-- from Zeta23.LinAlg.VonNeumann
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
# Von Neumann's trace inequality

For Hermitian `A, B` with eigenvalues sorted in decreasing order
`a₀ ≥ a₁ ≥ …` and `b₀ ≥ b₁ ≥ …`,

  `Re tr(AB) ≤ ∑ᵢ aᵢ bᵢ`.

## Proof outline

Diagonalise `A = Uₐ Dₐ Uₐᴴ` and `B = Uᵦ Dᵦ Uᵦᴴ`. Setting `W := Uₐᴴ Uᵦ`
(unitary), a direct calculation gives

  `tr(AB) = tr(Dₐ W Dᵦ Wᴴ) = ∑ₖₗ aₖ · ‖Wₖₗ‖² · bₗ`.

The matrix `Sₖₗ := ‖Wₖₗ‖²` is doubly stochastic over `ℝ` (rows and columns
of a unitary matrix are unit vectors). By **Birkhoff–von Neumann**
(`exists_eq_sum_perm_of_mem_doublyStochastic`) every doubly stochastic
matrix is a convex combination of permutation matrices: `S = ∑_σ w_σ P_σ`.
For each permutation `σ`, `∑ₖ aₖ b_{σ k} ≤ ∑ₖ aₖ bₖ` by the **rearrangement
inequality** (`Monovary.sum_mul_comp_perm_le_sum_mul`), since both `a` and
`b` are antitone (hence monovary). Averaging over `σ` with weights `w_σ`
gives the result.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]


section Bilinear



end Bilinear

section Rearrangement

/-- Two antitone functions on a linear order monovary. -/
lemma _root_.Antitone.monovary_antitone {ι α : Type*} [LinearOrder ι] [Preorder α]
    {f g : ι → α} (hf : Antitone f) (hg : Antitone g) : Monovary f g :=
  fun _ _ hgij => hf (not_lt.mp fun hij => hgij.not_ge (hg hij.le))


end Rearrangement


end RHLinalg
end
open Matrix Finset
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem solution {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (A * B).trace
      ≤ ∑ i, hA.eigenvalues₀ i * hB.eigenvalues₀ i := by
  -- Step 1: express `Re tr(AB)` via the bilinear form in `normSqMatrix W`.
  rw [re_trace_mul_eq_eigenvalue_bilinear hA hB]
  set W := star (hA.eigenvectorUnitary : Matrix n n 𝕜) *
    (hB.eigenvectorUnitary : Matrix n n 𝕜)
  have hW : W ∈ Matrix.unitaryGroup n 𝕜 :=
    mul_mem (Unitary.star_mem hA.eigenvectorUnitary.2) hB.eigenvectorUnitary.2
  have hDS := normSqMatrix_mem_doublyStochastic_of_unitary hW
  -- Step 2: reindex `n → Fin (card n)` via the canonical equivalence `e`,
  -- under which `eigenvalues (e k) = eigenvalues₀ k`.
  set e : Fin (Fintype.card n) ≃ n :=
    Fintype.equivOfCardEq (Fintype.card_fin _) with he_def
  have hevA : ∀ k, hA.eigenvalues (e k) = hA.eigenvalues₀ k := by
    intro k; simp [Matrix.IsHermitian.eigenvalues, he_def]
  have hevB : ∀ k, hB.eigenvalues (e k) = hB.eigenvalues₀ k := by
    intro k; simp [Matrix.IsHermitian.eigenvalues, he_def]
  -- Reindex both sums by `e`.
  have hre : ∑ k, ∑ l, hA.eigenvalues k * normSqMatrix W k l * hB.eigenvalues l
      = ∑ k, ∑ l, hA.eigenvalues₀ k * normSqMatrix W (e k) (e l) * hB.eigenvalues₀ l := by
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← e.sum_comp]
    simp only [hevA, hevB]
  rw [hre]
  -- Step 3: apply the doubly-stochastic bilinear bound.
  refine bilinear_doublyStochastic_le_of_monovary ?_ ?_
  · exact hA.eigenvalues₀_antitone.monovary_antitone hB.eigenvalues₀_antitone
  · -- Reindexed `normSqMatrix W` is still doubly stochastic.
    exact reindex_mem_doublyStochastic (e₁ := e.symm) (e₂ := e.symm) hDS

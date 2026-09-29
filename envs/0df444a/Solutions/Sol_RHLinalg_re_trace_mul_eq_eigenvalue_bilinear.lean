-- Prove2me | solution 1 for RHLinalg.re_trace_mul_eq_eigenvalue_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:44:59.32867+00:00
-- url     : https://prove2.me/submissions/7c849bf5-8ac0-4acd-97fe-5cdf93dfa525

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_VonNeumann

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
    RCLike.re (A * B).trace =
      ∑ k, ∑ l, hA.eigenvalues k *
        normSqMatrix (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *
          (hB.eigenvectorUnitary : Matrix n n 𝕜)) k l * hB.eigenvalues l := by
  set Ua : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary
  set Ub : Matrix n n 𝕜 := ↑hB.eigenvectorUnitary
  set Da : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  set Db : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hB.eigenvalues)
  set W := star Ua * Ub
  have hUaUa : Ua * star Ua = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hUaUa' : star Ua * Ua = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  -- Step 1: `tr(AB) = tr(Dₐ W Dᵦ Wᴴ)` by spectral theorem + trace cycling.
  have hstarW : star Ub * Ua = star W := by
    show star Ub * Ua = star (star Ua * Ub); rw [StarMul.star_mul, star_star]
  have hAB : (A * B).trace = (Da * W * Db * star W).trace := by
    -- `Ua (Da W Db Wᴴ) Uaᴴ = (Ua Da Uaᴴ)(Ub Db Ubᴴ)` since `Ua Uaᴴ = 1`.
    have key : Ua * (Da * W * Db * star W) * star Ua
        = Ua * Da * star Ua * (Ub * Db * star Ub) := by
      have step : Ua * (Da * W * Db * star W) * star Ua
          = Ua * Da * star Ua * (Ub * Db * star Ub) * (Ua * star Ua) := by
        rw [← hstarW]
        show Ua * (Da * (star Ua * Ub) * Db * (star Ub * Ua)) * star Ua = _
        noncomm_ring
      rw [step, hUaUa, mul_one]
    conv_lhs => rw [hA.spectral_theorem, hB.spectral_theorem,
      Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply, ← key,
      trace_mul_comm, ← mul_assoc, hUaUa', one_mul]
  -- Step 2: compute `tr(Dₐ W Dᵦ Wᴴ) = ∑ₖₗ aₖ Wₖₗ bₗ W̄ₖₗ`.
  -- Use `diagonal_mul`/`mul_diagonal` to evaluate entries of `Dₐ W Dᵦ`.
  have hentry : (Da * W * Db * star W).trace
      = ∑ k, ∑ l, (hA.eigenvalues k : 𝕜) * (hB.eigenvalues l : 𝕜)
          * (W k l * starRingEnd 𝕜 (W k l)) := by
    unfold Matrix.trace
    simp only [diag_apply]
    refine sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_apply]
    refine sum_congr rfl fun l _ => ?_
    rw [mul_diagonal, diagonal_mul, star_apply, RCLike.star_def]
    simp only [Function.comp_apply]; ring
  rw [hAB, hentry]
  -- Step 3: take `Re`; identify `z · conj z = ‖z‖²` and push reals.
  simp only [RCLike.mul_conj, map_sum, normSqMatrix, Matrix.of_apply]
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  rw [show ((hA.eigenvalues k : 𝕜) * hB.eigenvalues l * (‖W k l‖ : 𝕜) ^ 2 : 𝕜)
        = ((hA.eigenvalues k * hB.eigenvalues l * ‖W k l‖ ^ 2 : ℝ) : 𝕜) by push_cast; ring,
    RCLike.ofReal_re]
  ring

-- Prove2me | solution 1 for RHLinalg.rank_specMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:51:42.437773+00:00
-- url     : https://prove2.me/submissions/2478fbca-c445-4bb3-940f-869c14461b34

import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex

-- from Zeta23.LinAlg.HermitianPosPart
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















end PosNegPart

end RHLinalg
end
open Matrix Finset Unitary
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem solution {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (specMap hA f).rank = #{i | f (hA.eigenvalues i) ≠ 0} := by
  have hdet : IsUnit (hA.eigenvectorUnitary : Matrix n n 𝕜).det :=
    Matrix.UnitaryGroup.det_isUnit hA.eigenvectorUnitary
  have hdet' : IsUnit (star (hA.eigenvectorUnitary : Matrix n n 𝕜)).det := by
    rw [show star (hA.eigenvectorUnitary : Matrix n n 𝕜)
        = (hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ from rfl, det_conjTranspose]
    exact hdet.star
  unfold specMap
  rw [conjStarAlgAut_apply,
    rank_mul_eq_left_of_isUnit_det _ _ hdet',
    rank_mul_eq_right_of_isUnit_det _ _ hdet,
    rank_diagonal]
  simp only [ne_eq, RCLike.ofReal_eq_zero, Fintype.card_subtype]

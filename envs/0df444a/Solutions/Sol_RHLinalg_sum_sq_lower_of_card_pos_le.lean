-- Prove2me | solution 1 for RHLinalg.sum_sq_lower_of_card_pos_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:46:34.332965+00:00
-- url     : https://prove2.me/submissions/eb1c45ce-89bd-471f-af5a-9f31fa948975

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_VonNeumann

-- from Zeta23.LinAlg.RankTrace
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
# The rank–trace inequality (paper §3, `lem:ranktrace`)

Let `P, Q` be Hermitian `d × d` matrices with `P ⪰ 0`, `rank P ≤ r`, and
`n₊(Q) ≤ b`. Then for every `c > 0`,

  `‖P+Q‖_F² ≥ c · tr P − (c²/4) · r + 2c · tr Q − c² · b`.

## Proof structure (the paper's proof of [lem:ranktrace], §3)

Decompose `Q = Q₊ − Q₋` (spectral positive/negative parts). Expand
`‖P+Q‖_F² = ‖P‖_F² + 2 tr(PQ₊) − 2 tr(PQ₋) + ‖Q₊‖_F² + ‖Q₋‖_F²` (using
`Q₊Q₋ = 0`). Drop `tr(PQ₊) ≥ 0`. By von Neumann,
`‖P‖_F² − 2 tr(PQ₋) + ‖Q₋‖_F² ≥ ∑(pᵢ−nᵢ)²`. The two elementary estimates
`sum_sq_diff_lower` and `sum_sq_lower_of_card_pos_le` bound the remaining
pieces, and `linarith` assembles.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Elementary real-sequence estimates -/

section Elementary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-- Elementary scalar inequality `x² ≥ 2c·x − c²`, i.e. `(x − c)² ≥ 0`. -/
lemma sq_ge_linear' (x c : ℝ) : 2 * c * x - c ^ 2 ≤ x ^ 2 := by
  nlinarith [sq_nonneg (x - c)]



end Elementary

/-! ### Trace and Frobenius-norm identities -/






/-! ### The main theorem -/



end RHLinalg
end
open Matrix Finset
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution {q : ι → ℝ}
    {b : ℕ} (hb : #{i | q i ≠ 0} ≤ b) (c : ℝ) :
    2 * c * (∑ i, q i) - c ^ 2 * b ≤ ∑ i, (q i) ^ 2 := by
  classical
  set s : Finset ι := {i | q i ≠ 0} with hs_def
  have hptwise : ∀ i ∈ (univ : Finset ι),
      2 * c * q i - (if i ∈ s then c ^ 2 else 0) ≤ (q i) ^ 2 := by
    intro i _
    rcases eq_or_ne (q i) 0 with hi | hi
    · have his : i ∉ s := by simp [hs_def, mem_filter, hi]
      rw [if_neg his, hi]; simp
    · have his : i ∈ s := by simp [hs_def, mem_filter, hi]
      rw [if_pos his]; exact sq_ge_linear' (q i) c
  have hsum := sum_le_sum hptwise
  simp only [sum_sub_distrib, ← mul_sum, sum_ite_mem, univ_inter, sum_const,
    nsmul_eq_mul] at hsum
  have hcard : (#s : ℝ) * c ^ 2 ≤ b * c ^ 2 :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hb) (sq_nonneg c)
  linarith

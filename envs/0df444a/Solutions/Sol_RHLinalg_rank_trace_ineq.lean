-- Prove2me | solution 1 for RHLinalg.rank_trace_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:43:13.960936+00:00
-- url     : https://prove2.me/submissions/7c9ce128-f56e-404f-950c-9a59cfa96e48

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Theorems.Thm_RHLinalg_rank_specMap
import Theorems.Thm_RHLinalg_sum_sq_diff_lower
import Theorems.Thm_RHLinalg_sum_sq_lower_of_card_pos_le
import Theorems.Thm_RHLinalg_trace_mul_nonneg_of_posSemidef
import Theorems.Thm_RHLinalg_vonNeumann_trace_ineq

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








lemma rtrace_eq_sum_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    rtrace A = ∑ i, hA.eigenvalues i := by
  unfold rtrace
  rw [hA.trace_eq_sum_eigenvalues]
  simp

section Reindex

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)


lemma eigenvalues_eigEquiv (k : Fin (Fintype.card n)) :
    hA.eigenvalues (eigEquiv (n := n) k) = hA.eigenvalues₀ k := by
  simp [Matrix.IsHermitian.eigenvalues, eigEquiv]

/-- Any sum over `n` of a function of the eigenvalues equals the corresponding
sum over `Fin (card n)` of the function applied to `eigenvalues₀`. -/
lemma sum_eigenvalues_reindex {α : Type*} [AddCommMonoid α] (g : ℝ → α) :
    ∑ i, g (hA.eigenvalues i) = ∑ k, g (hA.eigenvalues₀ k) := by
  rw [← (eigEquiv (n := n)).sum_comp]
  simp only [eigenvalues_eigEquiv]

lemma card_eigenvalues_reindex (p : ℝ → Prop) [DecidablePred p] :
    #{i | p (hA.eigenvalues i)} = #{k | p (hA.eigenvalues₀ k)} := by
  apply Finset.card_nbij' (eigEquiv (n := n)).symm (eigEquiv (n := n))
  · intro i hi
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hi ⊢
    rwa [← eigenvalues_eigEquiv hA, Equiv.apply_symm_apply]
  · intro k hk
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hk ⊢
    rwa [eigenvalues_eigEquiv hA]
  · exact fun i _ => Equiv.apply_symm_apply _ i
  · exact fun k _ => Equiv.symm_apply_apply _ k

end Reindex

open Unitary in
/-- For a Hermitian matrix, `‖A‖_F² = ∑ᵢ λᵢ²` (sum of squared eigenvalues). -/
lemma frobSq_hermitian_eq_sum_sq_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    frobSq A = ∑ i, (hA.eigenvalues i) ^ 2 := by
  -- A = U D Uᴴ ⟹ AᴴA = A² = U D² Uᴴ ⟹ tr(AᴴA) = ∑ λᵢ²
  unfold frobSq
  rw [hA.eq]
  conv_lhs => rw [hA.spectral_theorem, ← map_mul, conjStarAlgAut_apply,
    trace_mul_cycle, coe_star_mul_self, one_mul,
    diagonal_mul_diagonal, trace_diagonal]
  simp [sq]

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


lemma specMap_isHermitian {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (specMap hA f).IsHermitian := by
  unfold specMap
  rw [conjStarAlgAut_apply]
  refine isHermitian_mul_mul_conjTranspose _ ?_
  exact isHermitian_diagonal_of_self_adjoint _ (funext fun i => by simp [RCLike.star_def])

lemma specMap_id {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    specMap hA id = A := by
  conv_rhs => rw [hA.spectral_theorem]
  rfl

lemma specMap_sub {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    specMap hA (f - g) = specMap hA f - specMap hA g := by
  unfold specMap
  rw [← map_sub]
  congr 1
  simp only [← diagonal_sub, Pi.sub_apply, RCLike.ofReal_sub]

lemma specMap_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    specMap hA (f * g) = specMap hA f * specMap hA g := by
  unfold specMap
  rw [← map_mul, diagonal_mul_diagonal]
  simp only [Pi.mul_apply, RCLike.ofReal_mul]

lemma specMap_zero {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    specMap hA 0 = 0 := by
  unfold specMap; simp


/-- The real-valued trace of `specMap hA f` is `∑ᵢ f(λᵢ)`. -/
lemma rtrace_specMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    rtrace (specMap hA f) = ∑ i, f (hA.eigenvalues i) := by
  unfold specMap rtrace
  rw [conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul,
    trace_diagonal]
  simp

/-- The squared Frobenius norm of `specMap hA f` is `∑ᵢ f(λᵢ)²`. -/
lemma frobSq_specMap {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    frobSq (specMap hA f) = ∑ i, (f (hA.eigenvalues i)) ^ 2 := by
  unfold frobSq
  rw [(specMap_isHermitian hA f).eq, ← specMap_mul,
    show (f * f : ℝ → ℝ) = fun x => (f x) ^ 2 from funext fun x => by
      simp only [Pi.mul_apply, sq]]
  exact rtrace_specMap hA _


/-- `specMap hA f` is PSD whenever `f(λᵢ) ≥ 0` for all `i`. -/
lemma specMap_posSemidef {A : Matrix n n 𝕜} (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) :
    (specMap hA f).PosSemidef := by
  unfold specMap
  rw [conjStarAlgAut_apply]
  refine (PosSemidef.diagonal ?_).mul_mul_conjTranspose_same _
  intro i
  exact RCLike.ofReal_nonneg (K := 𝕜) |>.mpr (hf i)

section PosNegPart

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)



lemma hermPosPart_sub_hermNegPart : hermPosPart hA - hermNegPart hA = A := by
  unfold hermPosPart hermNegPart
  rw [← specMap_sub, show ((·⁺) - (·⁻) : ℝ → ℝ) = id from
    funext fun x => posPart_sub_negPart x, specMap_id]

lemma hermPosPart_posSemidef : (hermPosPart hA).PosSemidef :=
  specMap_posSemidef hA fun _ => posPart_nonneg _

lemma hermNegPart_posSemidef : (hermNegPart hA).PosSemidef :=
  specMap_posSemidef hA fun _ => negPart_nonneg _

lemma real_posPart_mul_negPart (x : ℝ) : x⁺ * x⁻ = 0 := by
  rcases le_total 0 x with h | h
  · simp [negPart_eq_zero.mpr h]
  · simp [posPart_eq_zero.mpr h]

lemma hermPosPart_mul_hermNegPart : hermPosPart hA * hermNegPart hA = 0 := by
  unfold hermPosPart hermNegPart
  rw [← specMap_mul, show ((·⁺) * (·⁻) : ℝ → ℝ) = 0 from
    funext fun x => real_posPart_mul_negPart x, specMap_zero]

lemma hermNegPart_mul_hermPosPart : hermNegPart hA * hermPosPart hA = 0 := by
  unfold hermPosPart hermNegPart
  rw [← specMap_mul, show ((·⁻) * (·⁺) : ℝ → ℝ) = 0 from
    funext fun x => by rw [Pi.mul_apply, mul_comm]; exact real_posPart_mul_negPart x,
    specMap_zero]

lemma rank_hermPosPart : (hermPosPart hA).rank = posIndex hA := by
  unfold hermPosPart posIndex
  rw [rank_specMap]
  congr 1; ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq, posPart_eq_zero, not_le]

lemma rtrace_hermPosPart : rtrace (hermPosPart hA) = ∑ i, (hA.eigenvalues i)⁺ :=
  rtrace_specMap hA _



lemma frobSq_hermPosPart : frobSq (hermPosPart hA) = ∑ i, ((hA.eigenvalues i)⁺) ^ 2 :=
  frobSq_specMap hA _


end PosNegPart

end RHLinalg
end
end

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





end Elementary

/-! ### Trace and Frobenius-norm identities -/


omit [DecidableEq n] in
/-- For Hermitian `A, B`: `Re tr(BA) = Re tr(AB)`. (In fact `tr(BA) = tr(AB)`.) -/
lemma re_trace_mul_comm (A B : Matrix n n 𝕜) :
    RCLike.re (B * A).trace = RCLike.re (A * B).trace := by
  rw [trace_mul_comm]

omit [DecidableEq n] in
/-- Frobenius-norm expansion for a sum of two Hermitian matrices. -/
lemma frobSq_add_hermitian {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    frobSq (A + B) = frobSq A + 2 * RCLike.re (A * B).trace + frobSq B := by
  unfold frobSq
  rw [(hA.add hB).eq, hA.eq, hB.eq, add_mul, mul_add, mul_add,
    trace_add, trace_add, trace_add, map_add, map_add, map_add,
    re_trace_mul_comm B A]
  ring


omit [DecidableEq n] in
lemma rtrace_sub (A B : Matrix n n 𝕜) : rtrace (A - B) = rtrace A - rtrace B := by
  simp [rtrace, trace_sub, map_sub]

/-! ### The main theorem -/



end RHLinalg
end
open Matrix Finset
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem solution {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace P - c ^ 2 / 4 * r + 2 * c * rtrace Q - c ^ 2 * b
      ≤ frobSq (P + Q) := by
  classical
  -- Positive/negative parts of `Q`.
  set Qp := hermPosPart hQ with hQp_def
  set Qm := hermNegPart hQ with hQm_def
  have hQdec : Q = Qp - Qm := (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQpQm : Qp * Qm = 0 := hermPosPart_mul_hermNegPart hQ
  have hQmQp : Qm * Qp = 0 := hermNegPart_mul_hermPosPart hQ
  have hrkQp : Qp.rank ≤ b := by
    rw [hQp_def, rank_hermPosPart hQ]; exact hb
  -- Sorted eigenvalues on `Fin d`.
  set d := Fintype.card n
  set p : Fin d → ℝ := hP.isHermitian.eigenvalues₀
  set m : Fin d → ℝ := hQm_psd.isHermitian.eigenvalues₀
  have hp_nn : ∀ k, 0 ≤ p k := fun k => by
    rw [show p k = hP.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hP.isHermitian k).symm]
    exact hP.eigenvalues_nonneg _
  have hm_nn : ∀ k, 0 ≤ m k := fun k => by
    rw [show m k = hQm_psd.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hQm_psd.isHermitian k).symm]
    exact hQm_psd.eigenvalues_nonneg _
  -- `#{k : pₖ ≠ 0} = rank P ≤ r`.
  have hp_card : #{k | p k ≠ 0} ≤ r := by
    calc #{k | p k ≠ 0}
        = #{i | hP.isHermitian.eigenvalues i ≠ 0} :=
          (card_eigenvalues_reindex hP.isHermitian (· ≠ 0)).symm
      _ = P.rank := by
          rw [hP.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
      _ ≤ r := hr
  -- Trace/frobSq identities reindexed to `Fin d`.
  have htraceP : rtrace P = ∑ k, p k := by
    rw [rtrace_eq_sum_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian id
  have htraceQm : rtrace Qm = ∑ k, m k := by
    rw [rtrace_eq_sum_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian id
  have hfrobP : frobSq P = ∑ k, (p k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian (· ^ 2)
  have hfrobQm : frobSq Qm = ∑ k, (m k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian (· ^ 2)
  -- Step 1: Frobenius expansion.
  have hexpand : frobSq (P + Q)
      = frobSq P + 2 * RCLike.re (P * Qp).trace - 2 * RCLike.re (P * Qm).trace
        + frobSq Qp + frobSq Qm := by
    have h1 : frobSq (-Qm) = frobSq Qm := by
      unfold frobSq; rw [conjTranspose_neg, neg_mul_neg]
    have h2 : RCLike.re (Qp * -Qm).trace = 0 := by
      rw [mul_neg, hQpQm]; simp
    rw [hQdec, frobSq_add_hermitian hP.isHermitian
        (hQp_psd.isHermitian.sub hQm_psd.isHermitian),
      sub_eq_add_neg Qp Qm,
      frobSq_add_hermitian hQp_psd.isHermitian hQm_psd.isHermitian.neg,
      h1, h2, mul_add, mul_neg, trace_add, trace_neg, map_add, map_neg]
    ring
  -- Step 2: drop `tr(PQ₊) ≥ 0`.
  have hPQp : 0 ≤ RCLike.re (P * Qp).trace := trace_mul_nonneg_of_posSemidef hP hQp_psd
  -- Step 3: von Neumann on `P, Q₋`.
  have hvN : RCLike.re (P * Qm).trace ≤ ∑ k, p k * m k :=
    vonNeumann_trace_ineq hP.isHermitian hQm_psd.isHermitian
  -- Step 4: the von Neumann step gives `frobSq P − 2 tr(PQ₋) + frobSq Q₋ ≥ ∑(pₖ−mₖ)²`.
  have hstep4 : ∑ k, (p k - m k) ^ 2
      ≤ frobSq P - 2 * RCLike.re (P * Qm).trace + frobSq Qm := by
    have hsplit : ∑ k, (p k - m k) ^ 2
        = ∑ k, (p k)^2 - 2 * ∑ k, p k * m k + ∑ k, (m k)^2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hsplit, hfrobP, hfrobQm]; linarith
  -- Step 5: elementary estimate A.
  have hstep5 : c * rtrace P - c^2/4 * r - 2 * c * rtrace Qm
      ≤ ∑ k, (p k - m k) ^ 2 := by
    rw [htraceP, htraceQm]
    exact sum_sq_diff_lower hm_nn hp_card hc.le
  -- Step 6: elementary estimate B on `Q₊`.
  have hstep6 : 2 * c * rtrace Qp - c^2 * b ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    refine sum_sq_lower_of_card_pos_le ?_ c
    calc #{i | (hQ.eigenvalues i)⁺ ≠ 0}
        = #{i | 0 < hQ.eigenvalues i} := by
          congr 1; ext i; simp [posPart_eq_zero, not_le]
      _ ≤ b := hb
  -- Step 7: combine. `rtrace Q = rtrace Qp − rtrace Qm`.
  have htraceQ : 2 * c * rtrace Q = 2 * c * rtrace Qp - 2 * c * rtrace Qm := by
    rw [hQdec, rtrace_sub]; ring
  linarith [hstep4, hstep5, hstep6, hPQp, hexpand, htraceQ]

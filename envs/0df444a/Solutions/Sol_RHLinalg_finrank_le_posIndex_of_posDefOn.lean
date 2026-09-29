-- Prove2me | solution 1 for RHLinalg.finrank_le_posIndex_of_posDefOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:50:58.341741+00:00
-- url     : https://prove2.me/submissions/3964d094-ab3f-4c42-a73e-da22c97b7716

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Theorems.Thm_RHLinalg_rank_specMap

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


lemma hermNegPart_posSemidef : (hermNegPart hA).PosSemidef :=
  specMap_posSemidef hA fun _ => negPart_nonneg _




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
lemma hermForm_sub (A B : Matrix n n 𝕜) (x : n → 𝕜) :
    hermForm (A - B) x = hermForm A x - hermForm B x := by
  unfold hermForm
  simp [sub_mulVec, dotProduct_sub, map_sub]

omit [DecidableEq n] in
/-- `hermForm A x ≥ 0` when `A` is PSD. -/
lemma hermForm_nonneg_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (x : n → 𝕜) : 0 ≤ hermForm A x :=
  hA.re_dotProduct_nonneg x










end RHLinalg
end
open Matrix Finset Submodule
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem solution {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {W : Submodule 𝕜 (n → 𝕜)} (hW : PosDefOn A W) :
    Module.finrank 𝕜 W ≤ posIndex hA := by
  -- `A₊ *ᵥ ·` is injective on `W`: kernel element has `xᴴAx = −xᴴA₋x ≤ 0`.
  set L : (n → 𝕜) →ₗ[𝕜] (n → 𝕜) := (hermPosPart hA).mulVecLin
  have hinj : Function.Injective (L.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxW⟩ hxL
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxL
    -- `hxL : L ⟨x, hxW⟩ = 0`, i.e. `hermPosPart hA *ᵥ x = 0`.
    have hxL' : hermPosPart hA *ᵥ x = 0 := hxL
    simp only [mem_bot]
    by_contra hne
    have hne' : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hAx : hermForm A x ≤ 0 := by
      rw [← hermPosPart_sub_hermNegPart hA, hermForm_sub]
      have h1 : hermForm (hermPosPart hA) x = 0 := by
        unfold hermForm; rw [hxL']; simp
      have h2 : 0 ≤ hermForm (hermNegPart hA) x :=
        hermForm_nonneg_of_posSemidef (hermNegPart_posSemidef hA) x
      linarith
    exact absurd (hW x hxW hne') (not_lt.mpr hAx)
  -- `dim W = dim range(L|_W) ≤ dim range(L) = rank A₊ = posIndex hA`.
  calc Module.finrank 𝕜 W
      = Module.finrank 𝕜 (LinearMap.range (L.domRestrict W)) :=
        (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank 𝕜 (LinearMap.range L) := by
        apply Submodule.finrank_mono
        rintro y ⟨⟨x, hxW⟩, rfl⟩
        exact ⟨x, rfl⟩
    _ = (hermPosPart hA).rank := rfl
    _ = posIndex hA := rank_hermPosPart hA

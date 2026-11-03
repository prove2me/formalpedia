-- Prove2me | solution 1 for PermLimits.Existence.convergences_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T20:12:43.519021+00:00
-- url     : https://prove2.me/submissions/688abf86-5833-4d01-b101-950eb0018424

import Theorems.Thm_PermLimits_Cauchy_convergences_equivalent

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_LimitConvergence
open PermLimits
open PermLimits.Shared


open unitInterval

/-- **Lemma 5.3** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2, p. 16).
Let `Z, Z₁, Z₂, …` be limit permutations. The three notions of convergence of Definition 5.2 are
equivalent: `Z_n ⇒ Z ⟺ Z_n →□ Z ⟺ Z_n →ᵗ Z`.

**Formalization Note.** The chain of equivalences is the conjunction of two `↔`. -/
theorem solution (Zs : ℕ → I → I → ℝ) (Z : I → I → ℝ)
    (hZs : ∀ n, IsLimitPerm (Zs n)) (hZ : IsLimitPerm Z) :
    (WeakConv Zs Z ↔ RectConv Zs Z) ∧ (RectConv Zs Z ↔ DensityConv Zs Z) :=
  PermLimits.Cauchy.convergences_equivalent Zs Z hZs hZ
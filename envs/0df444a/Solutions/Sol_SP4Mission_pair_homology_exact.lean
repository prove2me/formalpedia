-- Prove2me | solution 1 for SP4Mission.pair_homology_exact
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-12T22:20:57.128205+00:00
-- url     : https://prove2.me/submissions/b9d6dead-4d1a-4855-bcba-8b7766745b26

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4Homology
import Definitions.Def_SP4HomologyMap
import Definitions.Def_SP4RelHomology

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission CategoryTheory Limits

/-!
# The long exact sequence of a pair (Hatcher, Theorem 2.16)

For an injective `ι : V → M`, the short exact sequence of singular chain complexes
`0 → C_•(V) → C_•(M) → C_•(M, V) → 0` (`SP4Homology.relShortComplex_shortExact`) induces, by the
snake lemma in the abelian category of chain complexes of `ℤ`-modules (Mathlib's
`ShortComplex.ShortExact.homology_exact₁/₂/₃`), the exactness of

`H_{k+1}(M, V) → H_k(V) → H_k(M) → H_k(M, V) → H_{k-1}(V)`

at each of its three interior terms.
-/

/-- The target theorem. -/
theorem solution {V M : Type} [TopologicalSpace V] [TopologicalSpace M]
    (ι : C(V, M)) (hι : Function.Injective ι) (k : ℕ) :
    (ShortComplex.mk (SP4Homology.map k ι) (SP4Homology.toRel k ι)
      (SP4Homology.map_toRel k ι)).Exact ∧
    (ShortComplex.mk (SP4Homology.toRel (k + 1) ι) (SP4Homology.relδ k ι hι)
      (SP4Homology.toRel_relδ k ι hι)).Exact ∧
    (ShortComplex.mk (SP4Homology.relδ k ι hι) (SP4Homology.map k ι)
      (SP4Homology.relδ_map k ι hι)).Exact := by
  have hS := SP4Homology.relShortComplex_shortExact ι hι
  exact ⟨hS.homology_exact₂ k, hS.homology_exact₃ (k + 1) k rfl, hS.homology_exact₁ (k + 1) k rfl⟩

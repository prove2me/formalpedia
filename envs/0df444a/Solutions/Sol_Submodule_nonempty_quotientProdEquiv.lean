-- Prove2me | solution 1 for Submodule.nonempty_quotientProdEquiv
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-09T22:37:35.047172+00:00
-- url     : https://prove2.me/submissions/43a36ac3-1b8c-421e-bcdb-2769227a3681

import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_submodule_quotientProdEquiv

theorem solution {R M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (p : Submodule R M) (q : Submodule R N) :
    Nonempty (((M × N) ⧸ p.prod q) ≃ₗ[R] (M ⧸ p) × (N ⧸ q)) :=
  ⟨Submodule.quotientProdEquiv p q⟩

-- Prove2me | solution 1 for Submodule.nonempty_prodEquiv
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-09T22:37:34.378335+00:00
-- url     : https://prove2.me/submissions/3e53ac4e-b38a-440b-a039-f993e741e018

import Mathlib.LinearAlgebra.Prod
import Definitions.Def_submodule_prodEquiv

theorem solution {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : Submodule R M) (q : Submodule R N) :
    Nonempty (p.prod q ≃ₗ[R] p × q) :=
  ⟨Submodule.prodEquiv p q⟩

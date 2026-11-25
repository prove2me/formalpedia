-- Prove2me | solution 1 for SZ.continuum_le_mk_witnesses_sqrtThree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:30:27.977206+00:00
-- url     : https://prove2.me/submissions/489c0c62-acbd-4957-9c49-01fc71292c24

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_continuum_le_mk_witnessSet

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution :
    Cardinal.continuum ≤
      Cardinal.mk {ξ : ℝ | 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → Even ⌊ξ * Real.sqrt 3 ^ n⌋} :=
  continuum_le_mk_witnessSet
end SZ

-- Prove2me | solution 1 for SZ.mk_nat_arrow_bool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:00.103678+00:00
-- url     : https://prove2.me/submissions/acd4893e-6e86-4961-8e69-20db662e47b4

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution : Cardinal.mk (ℕ → Bool) = Cardinal.continuum := by
  rw [Cardinal.mk_arrow]
  simp [Cardinal.two_power_aleph0]
end SZ

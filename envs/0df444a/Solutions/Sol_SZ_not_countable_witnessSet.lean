-- Prove2me | solution 1 for SZ.not_countable_witnessSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:30:27.587557+00:00
-- url     : https://prove2.me/submissions/03a52ea6-243d-4e8e-9eb2-bb94631006ad

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_continuum_le_mk_witnessSet

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution : ¬ witnessSet.Countable := by
  intro hc
  have h1 : Cardinal.mk witnessSet ≤ Cardinal.aleph0 :=
    Cardinal.le_aleph0_iff_set_countable.mpr hc
  exact absurd (continuum_le_mk_witnessSet.trans h1) (not_le.mpr Cardinal.aleph0_lt_continuum)
end SZ

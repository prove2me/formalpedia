-- Prove2me | solution 1 for SZ.treeXi_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:39.579566+00:00
-- url     : https://prove2.me/submissions/dd3abb29-b5ee-4618-a479-0eb9402ff737

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_runXi_treeDigit_injective

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution : Function.Injective treeXi := runXi_treeDigit_injective
end SZ

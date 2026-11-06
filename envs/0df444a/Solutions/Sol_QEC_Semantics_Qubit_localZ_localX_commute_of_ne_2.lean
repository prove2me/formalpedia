-- Prove2me | solution 2 for QEC.Semantics.Qubit.localZ_localX_commute_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:57:03.661686+00:00
-- url     : https://prove2.me/submissions/7bf28c34-ffed-4089-bfd9-5c97ca910428

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_localX_localZ_commute_of_ne

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Qubit
theorem _root_.solution {i j : ι} (h : i ≠ j) :
    localZ i * localX j = localX j * localZ i := by
  exact (localX_localZ_commute_of_ne (i := j) (j := i) h.symm).symm
end QEC.Semantics.Qubit

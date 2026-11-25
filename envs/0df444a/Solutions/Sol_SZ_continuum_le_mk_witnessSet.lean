-- Prove2me | solution 1 for SZ.continuum_le_mk_witnessSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:25:44.757166+00:00
-- url     : https://prove2.me/submissions/65f4394e-a345-4cf9-928d-294b697b1dbf

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_treeXi_mem
import Theorems.Thm_SZ_treeXi_injective
import Theorems.Thm_SZ_mk_nat_arrow_bool

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution :
    Cardinal.continuum ≤ Cardinal.mk witnessSet := by
  have hinj : Function.Injective
      (fun β : ℕ → Bool => (⟨treeXi β, treeXi_mem β⟩ : witnessSet)) := by
    intro β β' h
    exact treeXi_injective (congrArg Subtype.val h)
  have h := Cardinal.mk_le_of_injective hinj
  rwa [mk_nat_arrow_bool] at h
end SZ

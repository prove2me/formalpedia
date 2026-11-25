-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.h3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:37:30.41768+00:00
-- url     : https://prove2.me/submissions/173a00bb-8e7e-4f7e-bde3-25894330d052

import Definitions.Def_ReciprocityTheory_DualLattices_SubgroupFreenessStatement
import Definitions.Def_ReciprocityTheory_DualLattices_HasColengthEqPowMulPow
import Definitions.Def_ReciprocityTheory_DualLattices_ImportsBis
import Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_coset_basis
import Theorems.Thm_ReciprocityTheory_PGsh_L2_hasColength_eq_pow_mul_pow
import Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_of_restrictToSubgroup_eq_zero
import Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_sup_of_restrictToSubgroup_mem_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (C R : Type) [Field C] [CommRing R] [Algebra R C] :
    SubgroupFreenessStatement (C := C) (R := R) := by
  intro hC hC0 v hv N _ _ _ K _ _ _ AA
  haveI := hC
  haveI := hC0
  exact ⟨exists_coset_basis hv AA K, mem_of_restrictToSubgroup_eq_zero hv AA K, hasColength_eq_pow_mul_pow hv AA K, mem_sup_of_restrictToSubgroup_mem_sq hv AA K⟩
end ReciprocityTheory.PGsh.L2

-- Prove2me | solution 1 for ReciprocityTheory.PGsh.qExpansion_monoW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:52:01.257952+00:00
-- url     : https://prove2.me/submissions/0e0b749e-166f-432e-bb30-3a89051c70f5

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Eisenstein4CoeffBound
import Definitions.Def_ReciprocityTheory_DualLattices_QExpansionMonoWCoeffZero
import Theorems.Thm_ReciprocityTheory_PGsh_monoIdx_wt
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_qExpansion_E__eq_23abd34fd0e1
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_qExpansion_E__eq_3ba1083836b3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open UpperHalfPlane hiding I
open Complex ModularForm ModularFormClass MatrixGroups EisensteinSeries
namespace ReciprocityTheory.PGsh
theorem _root_.solution {w a : ℕ} (h : a ∈ monoIdx w) :
    qExpansion 1 (monoW w a) =
      PowerSeries.map (Int.castRingHom ℂ) (e4Z ^ a * e6Z ^ monoB w a) := by
  simp only [monoW, monoIdx_wt h, dite_true, ModularForm.qExpansion_mcast]
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, qExpansion_E₄_eq,
    qExpansion_E₆_eq, map_mul, map_pow, map_pow]
end ReciprocityTheory.PGsh

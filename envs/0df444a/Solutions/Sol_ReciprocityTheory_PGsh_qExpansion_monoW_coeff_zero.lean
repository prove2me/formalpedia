-- Prove2me | solution 1 for ReciprocityTheory.PGsh.qExpansion_monoW_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:38.780798+00:00
-- url     : https://prove2.me/submissions/0b5b277a-1d89-4fe4-8da0-6b8cec740f79

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Eisenstein4CoeffBound
import Definitions.Def_ReciprocityTheory_DualLattices_QExpansionMonoWCoeffZero
import Theorems.Thm_ReciprocityTheory_PGsh_qExpansion_monoW

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
    (qExpansion 1 (monoW w a)).coeff 0 = 1 := by
  have h4 : PowerSeries.constantCoeff e4Z = 1 := by simp [e4Z]
  have h6 : PowerSeries.constantCoeff e6Z = 1 := by simp [e6Z]
  rw [qExpansion_monoW h, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, map_pow, map_pow, h4, h6]
  simp
end ReciprocityTheory.PGsh

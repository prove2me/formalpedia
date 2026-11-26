-- Prove2me | solution 1 for TunnellMap.preferred_half_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:58.810019+00:00
-- url     : https://prove2.me/submissions/1179120c-0df8-485e-b740-98af206eb2cf

import Definitions.Def_TunnellMap_MidpointRecord
import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_QuadraticRoots
import Definitions.Def_TunnellMap_TauLattice
import Definitions.Def_TunnellMap_GeneratorRecovery
import Theorems.Thm_TunnellMap_isHalfSum_unique
import Theorems.Thm_TunnellMap_midpoint_parity
import Theorems.Thm_TunnellMap_odd_third_ne_zero
import Theorems.Thm_TunnellMap_qForm_halfSum_add_halfDiff
import Theorems.Thm_TunnellMap_qForm_pos_of_ne_zero
import Theorems.Thm_TunnellMap_qForm_vsmul
attribute [local simp] TunnellMap.qForm_vsmul



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : Odd n)
    {s : BResidual n} {t : AResidual n} (R : PreferredMidpointRecord s t) :
    R.multiplier ^ 2 * qForm R.direction < n := by
  obtain ⟨hPlus, hMinus, hPlusEq, _hPlusOdd, hMinusEq, hMinusOdd⟩ :=
    midpoint_parity hn s.1 R.target.1
  have hPlusEqRecord : hPlus = R.half :=
    isHalfSum_unique hPlusEq R.half_sum
  subst hPlus
  have hsum := qForm_halfSum_add_halfDiff s R.target R.half hMinus
    R.half_sum hMinusEq
  have hminusPos : 0 < qForm hMinus :=
    qForm_pos_of_ne_zero (odd_third_ne_zero hMinusOdd)
  have hhalfNorm : qForm R.half = R.multiplier ^ 2 * qForm R.direction := by
    rw [R.half_decomposition, qForm_vsmul]
  nlinarith
end TunnellMap

-- Prove2me | solution 1 for TunnellMap.plus_minus_directions_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:06.58772+00:00
-- url     : https://prove2.me/submissions/1da5f492-dc36-4082-8b20-702bd897c88c

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
import Theorems.Thm_TunnellMap_qForm_pos_of_ne_zero
import Theorems.Thm_TunnellMap_qBilinear_vsmul_vsmul
import Theorems.Thm_TunnellMap_plusVector_ne_zero
import Theorems.Thm_TunnellMap_minusVector_ne_zero
import Theorems.Thm_TunnellMap_plus_minus_orthogonal
import Theorems.Thm_TunnellMap_directionScale_ne_zero
import Theorems.Thm_TunnellMap_direction_decomposition
import Theorems.Thm_TunnellMap_primitiveDirection_ne_zero


set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (s : BResidual n) (t : AResidual n) :
    primitiveDirection (plusVector s t) ≠ primitiveDirection (minusVector s t) := by
  intro hdir
  let d := primitiveDirection (plusVector s t)
  let a := directionScale (plusVector s t)
  let b := directionScale (minusVector s t)
  have hplus : plusVector s t = vsmul a d := direction_decomposition _
  have hminus : minusVector s t = vsmul b d := by
    rw [direction_decomposition (minusVector s t), ← hdir]
  have ha : a ≠ 0 := directionScale_ne_zero (plusVector_ne_zero s t)
  have hb : b ≠ 0 := directionScale_ne_zero (minusVector_ne_zero s t)
  have hd : d ≠ ⟨0, 0, 0⟩ := primitiveDirection_ne_zero (plusVector_ne_zero s t)
  have horth := plus_minus_orthogonal s t
  rw [hplus, hminus, qBilinear_vsmul_vsmul] at horth
  have hq : qForm d ≠ 0 := ne_of_gt (qForm_pos_of_ne_zero hd)
  rcases mul_eq_zero.mp horth with hab | hq0
  · exact (mul_ne_zero ha hb) hab
  · exact hq hq0
end TunnellMap

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_dvd_of_map_dvd_1e28fee41c49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:44:59.355413+00:00
-- url     : https://prove2.me/submissions/a644f863-005a-4b7c-86e9-edcf0dc150dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_mem_of_map_mem_d2fb0cf9bb94
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coeff_coordPoly_539797cde10d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_C_mul_map_9d8219af7fc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_mem_of_mem_map_75eab8a0118b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_sum_8ff9631ad41f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_incidenceIdeal_map_8d93a5362789
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_mem_zeroLocus_incidenceIdeal_a3506a649f6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_radical_map_eq_9ece7ec07417
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_sum_coordPoly_903079f12110
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_vanishes_incidence_iff_796d408552b0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk conePts)
open ChowFormExtend (incidenceIdeal coordPoly coeff_coordPoly coordPoly_C_mul_map coordPoly_mem_of_mem_map
  mem_zeroLocus_incidenceIdeal vanishes_incidence_iff incidenceIdeal_map radical_map_eq coordSupport
  sum_coordPoly coordPoly_sum)
open GroundTheory.Heights₂.Heights.ObjectsChow.ComplexChowFormToChowForm
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Y : Type*}
namespace GroundTheory.Heights₂.Heights.ObjectsChow.ComplexChowFormToChowForm
theorem _root_.solution {f h : MvPolynomial Y K}
    (hd : map (algebraMap K L) f ∣ map (algebraMap K L) h) : f ∣ h := by
  rw [← Ideal.mem_span_singleton] at hd ⊢
  apply mem_of_map_mem (L := L)
  rwa [Ideal.map_span, Set.image_singleton]
end GroundTheory.Heights₂.Heights.ObjectsChow.ComplexChowFormToChowForm

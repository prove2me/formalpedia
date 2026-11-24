-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_mem_of_map_mem_d2fb0cf9bb94
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:45.721994+00:00
-- url     : https://prove2.me/submissions/0bbfe070-f0a9-4b9d-b8ba-eaeb9dd8c1f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_AevalGenericIdealIff
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
theorem _root_.solution (T : Ideal (MvPolynomial Y K)) {x : MvPolynomial Y K}
    (hx : map (algebraMap K L) x ∈ T.map (map (algebraMap K L))) : x ∈ T := by
  classical
  let b := Module.Basis.ofVectorSpace K L
  obtain ⟨c, hc⟩ : ∃ c, b.coord c 1 ≠ 0 := by
    by_contra! h
    have h0 : b.repr 1 = 0 := Finsupp.ext fun c => by rw [← Module.Basis.coord_apply]; exact h c
    exact one_ne_zero (b.repr.map_eq_zero_iff.mp h0)
  have hmem := coordPoly_mem_of_mem_map b T hx c
  have e := coordPoly_C_mul_map (b.coord c) (1 : L) x
  rw [C_1, one_mul] at e
  rw [e] at hmem
  have := T.mul_mem_left (C (b.coord c 1)⁻¹) hmem
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul] at this
end GroundTheory.Heights₂.Heights.ObjectsChow.ComplexChowFormToChowForm

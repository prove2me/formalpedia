-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_aeval_genericIdeal_iff_fb99c4bb003f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:44:58.649919+00:00
-- url     : https://prove2.me/submissions/ae49ad30-2145-4a4f-aea0-8cff34b19490

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
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow.ComplexChowFormToChowForm
theorem _root_.solution (P : Ideal (MRing (PBlk n))) (x : Fin n → ℂ) :
    (∀ q ∈ (genericIdeal P).map (map (algebraMap ℚ ℂ)), aeval x q = 0) ↔
      ∀ h ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P, eval x (map (Int.castRingHom ℂ) h) = 0 := by
  have hc : (map (algebraMap ℚ ℂ)).comp (map (Int.castRingHom ℚ)) =
      (map (Int.castRingHom ℂ) : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℂ) :=
    RingHom.ext fun p => by rw [RingHom.comp_apply, map_map]; congr 1
  rw [genericIdeal, Ideal.map_map, hc]
  constructor
  · intro H h hh
    exact H _ (Ideal.mem_map_of_mem _ hh)
  · intro H q hq
    have hle : (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map (map (Int.castRingHom ℂ)) ≤
        RingHom.ker (eval x) := by
      rw [Ideal.map_le_iff_le_comap]
      intro h hh
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact H h hh
    exact RingHom.mem_ker.mp (hle hq)
end GroundTheory.Heights₂.Heights.ObjectsChow.ComplexChowFormToChowForm

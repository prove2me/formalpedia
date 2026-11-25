-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_ComplexChowFormToChowForm_vanishes_zero_iff_dvd_e8d9621446a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:01.754787+00:00
-- url     : https://prove2.me/submissions/eb493cea-fc31-455e-8ca3-c9ccedd71333

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
theorem _root_.solution {σ : Type*} [Finite σ] {g p : MvPolynomial σ ℂ} (hg : Squarefree g) :
    (∀ v, eval v g = 0 → eval v p = 0) ↔ g ∣ p := by
  have hrad : (Ideal.span {g}).radical = Ideal.span {g} :=
    (isRadical_iff_span_singleton.mp hg.isRadical).radical
  rw [← Ideal.mem_span_singleton, ← hrad, ← vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  simp only [mem_vanishingIdeal_iff, mem_zeroLocus_iff, aeval_eq_eval]
  constructor
  · intro h v hv
    exact h v (hv g (Ideal.mem_span_singleton_self g))
  · intro h v hv
    refine h v fun q hq => ?_
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hq
    rw [map_mul, hv, zero_mul]
end GroundTheory.Heights₂.Heights.ObjectsChow.ComplexChowFormToChowForm

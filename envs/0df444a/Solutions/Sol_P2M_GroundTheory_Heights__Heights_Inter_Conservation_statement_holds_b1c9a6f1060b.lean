-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Conservation_statement_holds_b1c9a6f1060b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:33:23.388344+00:00
-- url     : https://prove2.me/submissions/c4661ae6-3a96-4bf5-893a-e4619d289830

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_ptsIntegral_const_3a0dc5282453
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_C_not_mem_17885ec104a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_isMultiHomog_C_402bc878fee5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Conservation_not_horizontal_d25330750319
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isMultiHomog_C_8aa21e557757


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
namespace GroundTheory.Heights₂.Heights.Inter
namespace Conservation
theorem _root_.solution : Conservation.Statement := by
  unfold Conservation.Statement ConservationStatement
  intro K _ ι _ I hI P n L p hP hL hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hA : IsSmoothHerm (constLine (ι := ι) (-Real.log p)) := contDiffOn_const
  have ha : ∀ k, (constLine (ι := ι) (-Real.log p)).a k = ((0 : K → ℕ) k : ℤ) := fun _ => rfl
  have hpot : (fun j z => Real.log ((L j).h z)) = pot L := rfl
  constructor
  · rw [hI.2.2 P n L _ (C (p : ℤ)) 0 hP hL hA ha (Conservation.isMultiHomog_C _)
      (Conservation.C_not_mem hP.2.2.1 (by exact_mod_cast hp.ne_zero))]
    have hlog : logNorm (constLine (ι := ι) (-Real.log p)) (C (p : ℤ)) = fun _ => 0 := by
      funext z
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (C (p : ℤ)))‖ / Real.exp (-(-Real.log p))) = 0
      rw [map_C, eval_C, neg_neg, Real.exp_log hp0]
      simp [hp0.ne']
    unfold recR vertR arInt
    rw [hlog, Conservation.ptsIntegral_const, zero_mul, sub_zero]
    refine finsum_mem_congr rfl fun W hW => ?_
    rw [if_neg (Conservation.not_horizontal hp hW), if_neg (Conservation.not_horizontal hp hW)]
  · rw [hI.2.2 P n L _ (C 1) 0 hP hL hA ha (Conservation.isMultiHomog_C _)
      (Conservation.C_not_mem hP.2.2.1 one_ne_zero)]
    have hlog : logNorm (constLine (ι := ι) (-Real.log p)) (C 1) = fun _ => -Real.log p := by
      funext z
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (C 1))‖ / Real.exp (-(-Real.log p))) = _
      rw [map_C, eval_C, neg_neg, Real.exp_log hp0]
      simp [Real.log_inv]
    have hempty : divSupp P (C 1 : MRing ι) = ∅ := by
      ext W
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hW
      have hle := hW.1.1.2
      rw [C_1, Ideal.span_singleton_one, sup_top_eq, top_le_iff] at hle
      exact hW.1.1.1.ne_top hle
    unfold recR arInt
    rw [hempty, finsum_mem_empty, hlog, Conservation.ptsIntegral_const, hpot]
    ring
end Conservation
end GroundTheory.Heights₂.Heights.Inter

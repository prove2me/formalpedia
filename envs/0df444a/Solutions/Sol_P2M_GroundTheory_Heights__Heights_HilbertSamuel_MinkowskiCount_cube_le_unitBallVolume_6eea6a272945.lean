-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_cube_le_unitBallVolume_6eea6a272945
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:55:24.884234+00:00
-- url     : https://prove2.me/submissions/bfe15a26-90f1-4dbc-b35e-1141e516e3a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMinkowskiCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Module Metric
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
theorem _root_.solution (R : ℕ) : (2 / Real.sqrt R) ^ R ≤ unitBallVolume R := by
  set a := 1 / Real.sqrt R with ha_def
  have ha : 0 ≤ a := by positivity
  have hsub : (WithLp.ofLp : EuclideanSpace ℝ (Fin R) → Fin R → ℝ) ⁻¹'
      (Set.univ.pi fun _ => Set.Ioo (-a) a) ⊆ ball 0 1 := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ioo] at hx
    rw [mem_ball_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_lt' one_pos, one_pow]
    rcases Nat.eq_zero_or_pos R with rfl | hR
    · simp
    · calc ∑ i, ‖x i‖ ^ 2 < ∑ _i : Fin R, a ^ 2 :=
            Finset.sum_lt_sum_of_nonempty ⟨⟨0, hR⟩, Finset.mem_univ _⟩ fun i _ => by
              rw [Real.norm_eq_abs, sq_abs]
              exact sq_lt_sq' (hx i).1 (hx i).2
        _ = 1 := by
          have hR' : (0 : ℝ) < R := by exact_mod_cast hR
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ha_def,
            div_pow, one_pow, Real.sq_sqrt hR'.le]
          field_simp
  have hvol := measure_mono (μ := volume) hsub
  rw [(PiLp.volume_preserving_ofLp (Fin R)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    at hvol
  simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hvol
  have h := ENNReal.toReal_mono measure_ball_lt_top.ne hvol
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at h
  have h2 : 2 / Real.sqrt R = a + a := by rw [ha_def]; ring
  rw [h2]
  exact h
end GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount

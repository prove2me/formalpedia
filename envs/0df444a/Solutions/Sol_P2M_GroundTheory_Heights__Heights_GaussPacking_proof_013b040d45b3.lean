-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussPacking_proof_013b040d45b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:58.366194+00:00
-- url     : https://prove2.me/submissions/27272625-fea9-446c-94bc-bf356c37082b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussPacking
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussPacking_pairwiseDisjoint_balls_5423df6c962a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussPacking_biUnion_balls_subset_3ea7d0494d82

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Metric
open PGaussPacking
namespace GroundTheory.Heights₂.Heights
namespace GaussPacking
theorem _root_.solution : GaussPacking.Statement := by
  intro n s δ r hδ hr hsep hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : s.card ≤ 1 := Finset.card_le_one.2 (fun a _ b _ => Subsingleton.elim a b)
    have h1' : (s.card : ℝ) ≤ 1 := by exact_mod_cast h1
    simpa using h1'
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
  have hδ2 : 0 < δ / 2 := by positivity
  have hR : 0 ≤ r + δ / 2 := by positivity
  have hmeas : ∑ x ∈ s, (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x (δ / 2)) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) (r + δ / 2)) := by
    rw [← measure_biUnion_finset (pairwiseDisjoint_balls s hsep) (fun x _ => measurableSet_ball)]
    exact measure_mono (biUnion_balls_subset s hs)
  simp only [Measure.addHaar_ball _ _ hδ2.le, Measure.addHaar_ball _ _ hR,
    finrank_euclideanSpace_fin, Finset.sum_const, nsmul_eq_mul] at hmeas
  have hc0 : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ 0 :=
    (measure_ball_pos _ _ one_pos).ne'
  have hct : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  rw [← mul_assoc] at hmeas
  have h2 := (ENNReal.mul_le_mul_iff_left hc0 hct).1 hmeas
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have hp : 0 < (δ / 2) ^ n := pow_pos hδ2 n
  have key : (1 + 2 * r / δ) ^ n = (r + δ / 2) ^ n / (δ / 2) ^ n := by
    rw [← div_pow]
    congr 1
    field_simp
    ring
  rw [key, le_div_iff₀ hp]
  exact h2
end GaussPacking
end GroundTheory.Heights₂.Heights

-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.momentumKernel_representation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:37:41.755289+00:00
-- url     : https://prove2.me/submissions/e56524dc-a58c-4999-979f-cfe35a3cc2cb

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

theorem _root_.solution (d : CollisionData) (F : TransverseFrames)
    (r : MomentumKernel) (P Pprime : Momentum) (h : KernelDomain d F r P Pprime) :
    collisionKernel d F r P Pprime =
      (∫ Q, quantumGain d F P Pprime Q * r (P - Q) (Pprime - Q)) -
        (((collisionLossRate d F P + collisionLossRate d F Pprime) / 2 : ℝ) : ℂ) * r P Pprime := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hin : ∀ᵐ Q : Momentum, ∫ k, lindbladIntegrand d F r P Pprime Q k =
      quantumGain d F P Pprime Q * r (P - Q) (Pprime - Q) -
        (((outgoingIntensity d F P Q + outgoingIntensity d F Pprime Q) / 2 : ℝ) : ℂ) * r P Pprime := by
    filter_upwards [h1, h2, h3] with Q a1 a2 a3
    have e : (fun k => lindbladIntegrand d F r P Pprime Q k) = fun k =>
        collisionCoefficient d (F.map Q k) (P - Q) Q *
          star (collisionCoefficient d (F.map Q k) (Pprime - Q) Q) * r (P - Q) (Pprime - Q) -
        ((((Complex.normSq (collisionCoefficient d (F.map Q k) P Q) +
          Complex.normSq (collisionCoefficient d (F.map Q k) Pprime Q)) / 2 : ℝ) : ℂ)) * r P Pprime := by
      funext k; unfold lindbladIntegrand; ring
    rw [e, integral_sub (a1.mul_const _) ?_, integral_mul_const,
      integral_mul_const, integral_complex_ofReal]
    · unfold quantumGain outgoingIntensity
      rw [integral_div, integral_add a2 a3]
    · exact (((a2.add a3).div_const 2).ofReal).mul_const _
  unfold collisionKernel
  rw [integral_congr_ae hin, integral_sub h4 ?_, integral_mul_const, integral_complex_ofReal]
  · unfold collisionLossRate
    rw [integral_div, integral_add h5 h6]
  · exact (((h5.add h6).div_const 2).ofReal).mul_const _

end QAlgorithms.Papers.Independent.Intake100.P64

end

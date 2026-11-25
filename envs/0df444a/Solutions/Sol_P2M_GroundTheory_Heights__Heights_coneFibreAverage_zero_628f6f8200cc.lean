-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_coneFibreAverage_zero_628f6f8200cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:19.100235+00:00
-- url     : https://prove2.me/submissions/5c75eb72-1aab-40df-a4f7-661f69410cc5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFibreAverage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_smul_mem_zeroSet_ab37cf5939d2


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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : IsProjPrime J)
    (hfib : ∀ᵐ π : Fin 0 → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 0), fibreCount h J π w ≠ ⊤) :
    ∫⁻ π : Fin 0 → Fin n → ℂ, matGauss π *
        ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin 0)) 1, (fibreCount h J π w : ℝ≥0∞) =
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin 0)) 1) *
        Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J} := by
  have : (volume : Measure (Fin 0 → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (ae (volume : Measure (Fin 0 → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
  have : (ae (volume : Measure (EuclideanSpace ℂ (Fin 0)))).NeBot := ae_neBot.2 (NeZero.ne _)
  have hcount : ∀ (π : Fin 0 → Fin n → ℂ) (w : EuclideanSpace ℂ (Fin 0)),
      fibreCount h J π w = (coneSet h J).encard := by
    intro π w
    rw [fibreCount]
    congr 1
    ext y
    simp [Subsingleton.elim (linProj π y) w]
  obtain ⟨π₀, hπ₀⟩ := hfib.exists
  obtain ⟨w₀, hw₀⟩ := hπ₀.exists
  rw [hcount] at hw₀
  have hsub : coneSet h J ⊆ {0} := by
    intro y hy
    by_contra hy0
    rw [Set.mem_singleton_iff] at hy0
    have hinf : (Set.range fun t : ℂ => t • y).Infinite :=
      Set.infinite_range_of_injective (smul_left_injective ℂ hy0)
    have hsub' : (Set.range fun t : ℂ => t • y) ⊆ coneSet h J := by
      rintro _ ⟨t, rfl⟩ q hq
      rw [HermNorm.pointOf_smul']
      exact PointLine.smul_mem_zeroSet hJ.isHomog hy t q hq
    exact hw₀ (hinf.mono hsub').encard_eq
  have hset : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J} = coneSet h J := by
    ext y
    refine ⟨fun hy => hy.2, fun hy => ⟨?_, hy⟩⟩
    rw [Set.mem_singleton_iff.1 (hsub hy)]
    simp
  have hmass : Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ) (coneSet h J) =
      ((coneSet h J).encard : ℝ≥0∞) := by
    rcases Set.subset_singleton_iff_eq.1 hsub with h0 | h0
    · rw [h0]
      simp
    · rw [h0, Nat.mul_zero, Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton,
        Set.encard_singleton]
      simp
  have hgauss : ∀ π : Fin 0 → Fin n → ℂ, matGauss π = 1 := by
    intro π
    simp [matGauss]
  have huniv : (volume : Measure (Fin 0 → Fin n → ℂ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  simp_rw [hgauss, hcount, one_mul, setLIntegral_const]
  rw [lintegral_const, huniv, mul_one, hset, hmass, mul_comm]
end GroundTheory.Heights₂.Heights

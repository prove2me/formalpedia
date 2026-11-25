-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_coneMass_of_fibre_zero_5619f5cadf5c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:21.845152+00:00
-- url     : https://prove2.me/submissions/97e7052f-06e5-4a8f-8402-a1861e1edc5e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
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
theorem _root_.solution {n δ : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : IsProjPrime J)
    (hfib : ∀ᵐ π : Fin 0 → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 0), fibreCount h J π w = δ) :
    Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf y) q = 0} =
      (δ : ℝ≥0∞) * Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, 0 ≤ (j : ℕ) → y j = 0} := by
  have : (volume : Measure (Fin 0 → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (ae (volume : Measure (Fin 0 → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
  have : (ae (volume : Measure (EuclideanSpace ℂ (Fin 0)))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨π, hπ⟩ := hfib.exists
  obtain ⟨w, hw⟩ := hπ.exists
  have hC : (coneSet h J).encard = δ := by
    rw [← hw, fibreCount]
    congr 1
    ext y
    simp [Subsingleton.elim (linProj π y) w]
  have hsub : coneSet h J ⊆ {0} := by
    intro y hy
    by_contra hy0
    rw [Set.mem_singleton_iff] at hy0
    have hinf : (Set.range fun t : ℂ => t • y).Infinite :=
      Set.infinite_range_of_injective (smul_left_injective ℂ hy0)
    have hsub' : (Set.range fun t : ℂ => t • y) ⊆ coneSet h J := by
      rintro _ ⟨t, rfl⟩ q hq
      have hpt : h.pointOf (t • y) = t • h.pointOf y := by
        simp only [HermNorm.pointOf]
        rw [← Matrix.mulVec_smul]
        rfl
      rw [hpt]
      exact PointLine.smul_mem_zeroSet hJ.isHomog hy t q hq
    have htop := (hinf.mono hsub').encard_eq
    rw [hC] at htop
    exact ENat.natCast_ne_top δ htop
  have hset1 : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf y) q = 0} =
      coneSet h J := by
    ext y
    constructor
    · exact fun hy => hy.2
    · intro hy
      refine ⟨?_, hy⟩
      rw [Set.mem_singleton_iff.1 (hsub hy)]
      simp
  have hset2 : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, 0 ≤ (j : ℕ) → y j = 0} =
      {0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, zero_le, forall_const]
    constructor
    · rintro ⟨-, hy⟩
      ext j
      simp [hy j]
    · rintro rfl
      simp
  rw [hset1, hset2, Nat.mul_zero, Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton, mul_one]
  rcases Set.subset_singleton_iff_eq.1 hsub with h0 | h0
  · rw [h0, Set.encard_empty] at hC
    have hδ : δ = 0 := by exact_mod_cast hC.symm
    rw [h0, hδ]
    simp
  · rw [h0, Set.encard_singleton] at hC
    have hδ : δ = 1 := by exact_mod_cast hC.symm
    rw [h0, hδ, Measure.hausdorffMeasure_zero_singleton]
    simp
end GroundTheory.Heights₂.Heights

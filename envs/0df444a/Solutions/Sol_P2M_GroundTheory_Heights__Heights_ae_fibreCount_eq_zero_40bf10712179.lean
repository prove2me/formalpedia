-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ae_fibreCount_eq_zero_40bf10712179
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:51.888343+00:00
-- url     : https://prove2.me/submissions/19b3f999-f067-4d18-b9aa-e55e8c62474c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass

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
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n m : ℕ} (hnm : n < m) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (π : Fin m → Fin n → ℂ) :
    ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w = 0 := by
  set R := (LinearMap.range (linProjₗ π)).restrictScalars ℝ
  have hR : R ≠ ⊤ := by
    intro hT
    rw [Submodule.restrictScalars_eq_top_iff] at hT
    have h1 := LinearMap.finrank_range_le (linProjₗ π)
    rw [hT, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h1
    omega
  have h0 : volume (R : Set (EuclideanSpace ℂ (Fin m))) = 0 := Measure.addHaar_submodule _ R hR
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with w hw
  rw [fibreCount, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro y ⟨-, rfl⟩
  exact hw ⟨y, rfl⟩
end GroundTheory.Heights₂.Heights

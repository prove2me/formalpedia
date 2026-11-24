-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.mM_nM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:49.59432+00:00
-- url     : https://prove2.me/submissions/b084bc0f-d589-4aec-a461-58fe30207231

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_ParAlg
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_pm_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}
variable (s : K →+* K) (J : Matrix (Fin M) (Fin M) K)
variable {s J}
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (hs : ∀ x, s (s x) = x) (a : Kˣ) (w : Fin M → K) (z : K) :
    pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1 * nM s J w z =
      nM s J (s a • w) (a * s a * z) * pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1 := by
  have e : (s : K → K) ∘ (s a • w) = (a : K) • (s ∘ w) := by funext i; simp [hs]
  have h : s a * s (a⁻¹ : Kˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  simp only [nM, pm_mul, e, smul_vecMul]
  congr 1
  · simp
  · simp only [mul_zero, zero_dotProduct, dotProduct_zero, add_zero, zero_add, zero_mul]
    linear_combination (-(a * z)) * h
  · simp
  · simp
  · simp [smul_smul, mul_comm (s (a⁻¹ : Kˣ)), h]
end PositivityTheory.PlacePermOperatorBicommutantSpan

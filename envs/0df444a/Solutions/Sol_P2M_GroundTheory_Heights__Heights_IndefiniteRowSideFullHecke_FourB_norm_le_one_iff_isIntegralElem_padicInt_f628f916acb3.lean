-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_norm_le_one_iff_isIntegralElem_padicInt_f628f916acb3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:54:23.053636+00:00
-- url     : https://prove2.me/submissions/4c0c5834-1951-4a80-bac1-160472064c5b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open IsDedekindDomain NumberField Polynomial Rat.HeightOneSpectrum
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
theorem _root_.solution (p : ℕ) [Fact p.Prime] {K : Type*}
    [NormedField K] [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] (x : K) :
    ‖x‖ ≤ 1 ↔ ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).IsIntegralElem x := by
  have hx : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p] x, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic hx)]
  let : Algebra ℤ_[p] K := ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  have : IsScalarTower ℤ_[p] ℚ_[p] K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  constructor
  · intro h
    have hl : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hmon⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hx)
    refine ⟨q, hmon, ?_⟩
    have h0 : eval₂ (algebraMap ℚ_[p] K) x (q.map (algebraMap ℤ_[p] ℚ_[p])) = 0 := by
      rw [hq]; exact minpoly.aeval ℚ_[p] x
    rwa [eval₂_map] at h0
  · intro h n
    have hxZ : IsIntegral ℤ_[p] x := h
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hxZ, coeff_map,
      PadicInt.algebraMap_apply]
    exact PadicInt.norm_le_one _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

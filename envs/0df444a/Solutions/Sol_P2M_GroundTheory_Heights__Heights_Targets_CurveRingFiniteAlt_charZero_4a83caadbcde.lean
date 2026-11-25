-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_charZero_4a83caadbcde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:20:42.482249+00:00
-- url     : https://prove2.me/submissions/14ae6d6e-ad9a-4b5e-b14b-4f97d1974191

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveRingFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexAt_algebraMap_apply_de37bb391a59


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveRingFiniteAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.CurveRingFiniteAlt
theorem _root_.solution {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (hy : IsHorizontal (mCoordIdeal y)) :
    CharZero Ω := by
  refine charZero_of_injective_algebraMap (R := ℤ) ((injective_iff_map_eq_zero _).mpr fun m hm => ?_)
  have h : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_C,
      MvPolynomial.algebraMap_apply, hm, C_0]
  rwa [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hy, Ideal.mem_bot] at h
end GroundTheory.Heights₂.Heights.Targets.CurveRingFiniteAlt

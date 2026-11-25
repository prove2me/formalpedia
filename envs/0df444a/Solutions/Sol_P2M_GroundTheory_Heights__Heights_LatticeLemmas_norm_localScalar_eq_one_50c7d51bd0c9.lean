-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_norm_localScalar_eq_one_50c7d51bd0c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:38.090859+00:00
-- url     : https://prove2.me/submissions/232af4af-5b8f-490a-b84e-d59461f139b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K} (hv : b ∉ v.asIdeal) :
    ‖localScalar v b‖ = 1 := by
  rw [localScalar_eq]
  exact (FinitePlace.norm_eq_one_iff_notMem K v b).mpr hv
end GroundTheory.Heights₂.Heights.LatticeLemmas

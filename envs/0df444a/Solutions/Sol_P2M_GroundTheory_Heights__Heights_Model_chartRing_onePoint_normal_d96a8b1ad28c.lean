-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_chartRing_onePoint_normal_d96a8b1ad28c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:15.817587+00:00
-- url     : https://prove2.me/submissions/0e5a328b-18e3-4982-8f57-02eaf47f8fbc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_chartRing_onePoint_d03e9839999f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution :
    IsNoetherianRing (chartRing ℤ onePoint ()) ∧ IsIntegrallyClosed (chartRing ℤ onePoint ()) := by
  have e : ℤ ≃+* chartRing ℤ onePoint () :=
    (Algebra.botEquivOfInjective (R := ℤ) (A := ℚ) Int.cast_injective).symm.toRingEquiv.trans
      (Subalgebra.equivOfEq _ _ (chartRing_onePoint ℤ).symm).toRingEquiv
  exact ⟨isNoetherianRing_of_ringEquiv ℤ e, (IsIntegrallyClosed.of_equiv e)⟩
end GroundTheory.Heights₂.Heights.Model

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_projectiveLine_dim_b502498be087
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:42.20511+00:00
-- url     : https://prove2.me/submissions/9519c4db-9104-44b8-8a61-d14286b4dd94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements

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
    ringKrullDim (MRing (fun _ : Unit => Fin 2) ℚ ⧸ (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ))) =
      ((1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (MRing (fun _ : Unit => Fin 2) ℚ)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field ℚ]
  have hc : Nat.card ((_ : Unit) × Fin 2) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp
  rw [hc, Fintype.card_unit]
  norm_num
end GroundTheory.Heights₂.Heights.Model

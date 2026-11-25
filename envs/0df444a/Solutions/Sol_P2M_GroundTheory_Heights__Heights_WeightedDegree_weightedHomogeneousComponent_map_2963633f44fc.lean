-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_WeightedDegree_weightedHomogeneousComponent_map_2963633f44fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:24:52.964072+00:00
-- url     : https://prove2.me/submissions/6315d8d1-0512-4bca-a2fd-a2a33e254120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConservationOfNumberLE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericCycleCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_WeightedHomogeneousComponentMap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumbersDVR
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.WeightedDegree
variable {K : Type} {ι : K → Type} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (M₀ : Submonoid R) [IsLocalization M₀ R']
namespace GroundTheory.Heights₂.Heights.WeightedDegree
theorem _root_.solution [DecidableEq K] (b : K → ℕ) (y : MRing ι R) :
    weightedHomogeneousComponent (blockWeight ι) b (map (algebraMap R R') y) =
      map (algebraMap R R') (weightedHomogeneousComponent (blockWeight ι) b y) := by
  classical
  ext d
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.WeightedDegree

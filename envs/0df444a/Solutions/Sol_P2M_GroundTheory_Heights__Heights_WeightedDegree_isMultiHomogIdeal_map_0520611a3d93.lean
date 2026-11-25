-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_WeightedDegree_isMultiHomogIdeal_map_0520611a3d93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:21.67206+00:00
-- url     : https://prove2.me/submissions/841b3b01-0a6e-46ab-bbd7-7f2cb58e0558

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConservationOfNumberLE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericCycleCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_WeightedHomogeneousComponentMap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_WeightedDegree_weightedHomogeneousComponent_map_2963633f44fc

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
open MvPolynomial NumbersDVR
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.WeightedDegree
variable {K : Type} {ι : K → Type} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (M₀ : Submonoid R) [IsLocalization M₀ R']
include M₀
namespace GroundTheory.Heights₂.Heights.WeightedDegree
theorem _root_.solution [DecidableEq K] {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    IsMultiHomogIdeal (I.map (algebraMap (MRing ι R) (MRing ι R'))) := by
  classical
  intro z hz b
  obtain ⟨⟨x, m⟩, hxm⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M₀.map (C (σ := Σ k, ι k))) (MRing ι R')).mp hz
  obtain ⟨r, hr, hrm⟩ := Submonoid.mem_map.mp m.2
  have hu : IsUnit (C (algebraMap R R' r) : MRing ι R') :=
    (IsLocalization.map_units R' (⟨r, hr⟩ : M₀)).map C
  have hm : algebraMap (MRing ι R) (MRing ι R') (m : MRing ι R) = C (algebraMap R R' r) := by
    rw [← hrm]
    exact map_C _ _
  rw [← Ideal.mul_unit_mem_iff_mem _ hu, mul_comm, ← weightedHomogeneousComponent_C_mul, mul_comm,
    ← hm, hxm]
  change weightedHomogeneousComponent _ b (map (algebraMap R R') (x : MRing ι R)) ∈ _
  rw [weightedHomogeneousComponent_map]
  exact Ideal.mem_map_of_mem _ (hI x x.2 b)
end GroundTheory.Heights₂.Heights.WeightedDegree

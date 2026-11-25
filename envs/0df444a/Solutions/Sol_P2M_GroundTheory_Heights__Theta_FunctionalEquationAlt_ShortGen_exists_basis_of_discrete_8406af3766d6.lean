-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_basis_of_discrete_8406af3766d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:45.981183+00:00
-- url     : https://prove2.me/submissions/be4fbe4b-8931-44ab-b864-4c566b061bb7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_linearIndependent_real_of_int_75b3dfee45d3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
open Module Submodule Matrix
open scoped RealInnerProductSpace
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
namespace GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
theorem _root_.solution (L : Submodule ℤ W) [DiscreteTopology L] :
    ∃ (n : ℕ) (c : Fin n → W), LinearIndependent ℝ c ∧ span ℤ (Set.range c) = L := by
  let b := Module.finBasis ℤ L
  have hspan : span ℤ (Set.range fun i => (b i : W)) = L := by
    rw [show (Set.range fun i => (b i : W)) = L.subtype '' Set.range b by
      rw [← Set.range_comp]; rfl]
    rw [← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hZ : LinearIndependent ℤ fun i => (b i : W) :=
    b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  refine ⟨_, fun i => (b i : W), linearIndependent_real_of_int hZ ?_, hspan⟩
  rw [hspan]
  infer_instance
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen

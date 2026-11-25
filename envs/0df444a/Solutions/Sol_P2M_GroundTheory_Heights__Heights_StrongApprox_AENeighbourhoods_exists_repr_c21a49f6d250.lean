-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_AENeighbourhoods_exists_repr_c21a49f6d250
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:19:36.07645+00:00
-- url     : https://prove2.me/submissions/13260549-8aeb-404a-964c-3700d902d56b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PAENeighbourhoods
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods
theorem _root_.solution (a : AE F E) :
    ∃ X : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F,
      a = ∑ l, X l ⊗ₜ[F] intBasis E l := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x y =>
    refine ⟨fun l => algebraMap ℚ F ((integralBasis E).repr y l) • x, ?_⟩
    conv_lhs => rw [← (integralBasis E).sum_repr y]
    rw [tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integralBasis_apply, ← IsScalarTower.algebraMap_smul F, tmul_smul, smul_tmul']
    rfl
  | add x y hx hy =>
    obtain ⟨X₁, rfl⟩ := hx
    obtain ⟨X₂, rfl⟩ := hy
    exact ⟨X₁ + X₂, by simp [add_tmul, Finset.sum_add_distrib]⟩
end GroundTheory.Heights₂.Heights.StrongApprox.AENeighbourhoods

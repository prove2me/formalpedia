-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_sum_projC___11ca3dfecaad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:48.709722+00:00
-- url     : https://prove2.me/submissions/a3d04ee5-0cd0-4552-83af-8a6f45b67348

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PFreeSheafBasis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis___projC_ac457d736909

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
universe u
open GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
variable {C : Type*} [Category C] [Preadditive C] (A : C) (n : ℕ)
  [HasCoproduct (fun _ : ULift.{u} (Fin n) => A)]
namespace GroundTheory.Heights₂.Heights.Model.FreeSheafBasis
theorem _root_.solution :
    ∑ j : Fin n, projC A n j ≫ Sigma.ι (fun _ : ULift.{u} (Fin n) => A) (ULift.up j) = 𝟙 _ := by
  refine Sigma.hom_ext _ _ (fun ⟨i⟩ => ?_)
  simp only [Preadditive.comp_sum, ← Category.assoc, ι_projC, Category.comp_id]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp
end GroundTheory.Heights₂.Heights.Model.FreeSheafBasis

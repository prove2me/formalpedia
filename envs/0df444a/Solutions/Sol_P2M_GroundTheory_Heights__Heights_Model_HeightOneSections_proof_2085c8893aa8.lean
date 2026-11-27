-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_proof_2085c8893aa8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:03:41.954798+00:00
-- url     : https://prove2.me/submissions/6f6d662b-982d-4c40-9465-bdf9dee2a708

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsHeightOneSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PHeightOneIntersection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PHeightOneSectionsLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PHeightOneSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_proof_015c0bbe7ac1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneIntersection_proof_f7da7b6d131d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_exists_section_of_isBasisOn_7245198a65b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_genericPoint_mem_02612281dbe5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_VectorBundleRestrict_proof_7423c8d31f2c


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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace GroundTheory.Heights₂.Heights.Model
namespace HeightOneSections
theorem _root_.solution (h₁ : GenericGermInjective.Statement) :
    HeightOneSections.Statement := by
  intro X _ _ hN E hE U hU v hv
  have inj := h₁ X E hE

  have loc : ∀ x : U, ∃ (V : X.Opens) (_ : V ≤ U) (_ : (x : X) ∈ V) (σ : Γ(E, V)),
      ∀ hη : genericPoint X ∈ V, E.presheaf.germ V _ hη σ = v := by
    rintro ⟨x, hx⟩
    obtain ⟨W, -, hxW, n, s, hs⟩ := hE x
    obtain ⟨V, hVa, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ W ⊓ U from ⟨hxW, hx⟩)
    have hη := HeightOneSections.genericPoint_mem hxV
    obtain ⟨σ, hσ⟩ := HeightOneSections.exists_section_of_isBasisOn HeightOneIntersection.proof
      hN E hVa hη (hs.restrict (hVle.trans inf_le_left)) v
      (fun y hy hy1 => hv y (hVle hy).2 hy1)
    exact ⟨V, hVle.trans inf_le_right, hxV, σ, fun _ => hσ⟩
  choose V hVU hxV σ hσ using loc

  have hcomp : TopCat.Presheaf.IsCompatible E.presheaf V σ := by
    intro i j
    refine BundlesAgree.section_ext E inj fun hη => ?_
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hσ, hσ]
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨E.presheaf, E.isSheaf⟩ V U
    (fun x => homOfLE (hVU x)) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩) σ hcomp
  refine ⟨t, ?_⟩
  let x : U := ⟨genericPoint X, hU⟩
  have hη := HeightOneSections.genericPoint_mem (hxV x)
  have hx : E.presheaf.map (homOfLE (hVU x)).op t = σ x := ht x
  rw [← hσ x hη, ← hx, TopCat.Presheaf.germ_res_apply]
end HeightOneSections
end GroundTheory.Heights₂.Heights.Model

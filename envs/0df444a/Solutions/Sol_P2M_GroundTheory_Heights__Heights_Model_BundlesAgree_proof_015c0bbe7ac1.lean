-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_proof_015c0bbe7ac1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:07:05.552811+00:00
-- url     : https://prove2.me/submissions/a9a011bc-537f-456d-9c2a-da9b232fcd4d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsHeightOneSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBundlesAgree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_germ_homOfGeneric_app_ae35dc9a743d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_hom_ext_of_germ_e9a54a5bbb2d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_germ_app_eq_stalk_95beff67d4e5

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
open BundlesAgree
namespace GroundTheory.Heights₂.Heights.Model
namespace BundlesAgree
theorem _root_.solution (h₁ : GenericGermInjective.Statement)
    (h₂ : HeightOneSections.Statement) : BundlesAgree.Statement := by
  intro X _ _ hN E E' hE hE' φ hφ
  have inj := h₁ X E hE
  have inj' := h₁ X E' hE'
  have mem : ∀ (F : X.Modules) (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(F, U)) (x : X)
      (hx : x ∈ U), F.presheaf.germ U (genericPoint X) hU s ∈ genericImage F x :=
    fun F U hU s x hx => ⟨F.presheaf.germ U x hx s,
      TopCat.Presheaf.germ_stalkSpecializes_apply F.presheaf hx (genericPoint_specializes x) s⟩
  have hex : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)), ∃ t : Γ(E', U),
      E'.presheaf.germ U (genericPoint X) hU t = φ.toLinearMap (E.presheaf.germ U _ hU s) :=
    fun U hU s => h₂ X hN E' hE' U hU _ fun x hx hx1 => by
      rw [← hφ x hx1]
      exact AddSubgroup.mem_map.mpr ⟨_, mem E U hU s x hx, rfl⟩
  have hex' : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E', U)), ∃ t : Γ(E, U),
      E.presheaf.germ U (genericPoint X) hU t = φ.symm.toLinearMap (E'.presheaf.germ U _ hU s) :=
    fun U hU s => h₂ X hN E hE U hU _ fun x hx hx1 => by
      have h := mem E' U hU s x hx
      rw [← hφ x hx1] at h
      obtain ⟨a, ha, he⟩ := AddSubgroup.mem_map.mp h
      have : φ.symm (E'.presheaf.germ U (genericPoint X) hU s) = a := by
        rw [← he]
        exact φ.symm_apply_apply a
      exact this ▸ ha
  let f := homOfGeneric E E' φ.toLinearMap hex inj'
  let g := homOfGeneric E' E φ.symm.toLinearMap hex' inj
  have hf := germ_homOfGeneric_app E E' φ.toLinearMap hex inj'
  have hg := germ_homOfGeneric_app E' E φ.symm.toLinearMap hex' inj
  refine ⟨⟨f, g, ?_, ?_⟩, ?_, ?_⟩
  · refine hom_ext_of_germ E E inj fun U hU s => ?_
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, ConcreteCategory.comp_apply, hg,
      hf]
    simp
  · refine hom_ext_of_germ E' E' inj' fun U hU s => ?_
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, ConcreteCategory.comp_apply, hf,
      hg]
    simp
  · intro v
    obtain ⟨U, hU, s, rfl⟩ := E.presheaf.exists_germ_eq v
    rw [← germ_app_eq_stalk]
    exact hf U hU s
  · intro ψ hψ
    refine Iso.ext (hom_ext_of_germ E E' inj' fun U hU s => ?_)
    rw [germ_app_eq_stalk]
    exact (hψ _).trans (hf U hU s).symm
end BundlesAgree
end GroundTheory.Heights₂.Heights.Model

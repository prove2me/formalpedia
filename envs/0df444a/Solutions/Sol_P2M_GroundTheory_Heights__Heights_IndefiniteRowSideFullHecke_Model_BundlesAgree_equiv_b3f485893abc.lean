-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BundlesAgree_equiv_b3f485893abc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:04:59.682804+00:00
-- url     : https://prove2.me/submissions/8a0f4281-faf0-4adb-b029-6faafeb1e324

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GenericImageEqGermImage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isNormalScheme_iff_model_c6464ab74628
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericImage_eq_germImage_a39dd64e4122
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_stalkMap_eq_iff_germ_581138d9864c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace BundlesAgree
theorem _root_.solution :
    GroundTheory.Heights₂.Heights.Model.BundlesAgree.Statement ↔ BundlesAgree.Statement := by
  constructor
  · intro h X _ hN _ E E' hE hE' φ hφ
    obtain ⟨ψ, hψ, huniq⟩ := h X ((isNormalScheme_iff_model X).2 hN) E E' hE hE' φ.toLinearEquiv
      (fun x hx => SetLike.coe_injective (by
        rw [AddSubgroup.coe_map, genericImage_eq_germImage, genericImage_eq_germImage]
        exact hφ x hx))
    exact ⟨ψ, (stalkMap_eq_iff_germ ψ _).1 hψ,
      fun ψ' h' => huniq ψ' ((stalkMap_eq_iff_germ ψ' _).2 h')⟩
  · intro h X _ _ hN E E' hE hE' φ hφ
    have := (isNormalScheme_iff_model X).1 hN
    obtain ⟨ψ, hψ, huniq⟩ := h X E E' hE hE' (GenericStalkIso.ofLinearEquiv φ)
      (fun x hx => by
        have := congrArg SetLike.coe (hφ x hx)
        simp only [AddSubgroup.coe_map, genericImage_eq_germImage] at this
        exact this)
    exact ⟨ψ, (stalkMap_eq_iff_germ ψ _).2 hψ,
      fun ψ' h' => huniq ψ' ((stalkMap_eq_iff_germ ψ' _).1 h')⟩
end BundlesAgree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

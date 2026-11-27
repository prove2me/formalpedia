-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadIso_proof_f705025862c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:04:30.912688+00:00
-- url     : https://prove2.me/submissions/2a37f7fc-4429-47d6-b0ec-6868df2877cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadIso
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackHomAlong_comp_612936c62fe2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackHomAlong_id_26d3a2af4c2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackIsoAlong_hom_ed4907f849de


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
open CategoryTheory AlgebraicGeometry
namespace GroundTheory.Heights₂.Heights.Model
namespace SpreadIso
theorem _root_.solution (h₁ : SpreadHom.Statement) (h₂ : SpreadHomInj.Statement) :
    SpreadIso.Statement := by
  intro X f _ _ a ha F G hF hG α
  obtain ⟨m₁, hm₁, H₁⟩ := h₁ X f a ha F G hF hG α.hom
  obtain ⟨m₂, hm₂, H₂⟩ := h₁ X f a ha G F hG hF α.inv
  obtain ⟨m₃, hm₃, I₃⟩ := h₂ X f a ha F F hF hF
  obtain ⟨m₄, hm₄, I₄⟩ := h₂ X f a ha G G hG hG
  obtain ⟨n, hn_def⟩ : ∃ n, n = m₁ * m₂ * m₃ * m₄ := ⟨_, rfl⟩
  have hn : 0 < n := by rw [hn_def]; positivity
  obtain ⟨ψ₁, e₁⟩ := H₁ n hn (Dvd.intro (m₂ * m₃ * m₄) (by rw [hn_def]; ring))
  obtain ⟨ψ₂, e₂⟩ := H₂ n hn (Dvd.intro (m₁ * m₃ * m₄) (by rw [hn_def]; ring))
  have k₁ : ψ₁ ≫ ψ₂ = 𝟙 _ := I₃ n hn (Dvd.intro (m₁ * m₂ * m₄) (by rw [hn_def]; ring)) _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₁, e₂, Iso.hom_inv_id])
  have k₂ : ψ₂ ≫ ψ₁ = 𝟙 _ := I₄ n hn (Dvd.intro (m₁ * m₂ * m₃) (by rw [hn_def]; ring)) _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₂, e₁, Iso.inv_hom_id])
  refine ⟨n, hn, ⟨ψ₁, ψ₂, k₁, k₂⟩, Iso.ext ?_⟩
  rw [pullbackIsoAlong_hom]
  exact e₁
end SpreadIso
end GroundTheory.Heights₂.Heights.Model

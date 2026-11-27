-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadIsoLoc_proof_4699cfa9c8b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:04:13.286306+00:00
-- url     : https://prove2.me/submissions/433fbf7d-9b3f-4003-a631-06cdbeb95bf0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadIsoLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomInjLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadIsoLoc
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
namespace SpreadIsoLoc
theorem _root_.solution (h₁ : SpreadHomLoc.Statement) (h₂ : SpreadHomInjLoc.Statement) :
    SpreadIsoLoc.Statement := by
  intro X f _ _ p U F G hF hG β
  obtain ⟨m₁, hm₁, hp₁, H₁⟩ := h₁ X f p U F G hF hG β.hom
  obtain ⟨m₂, hm₂, hp₂, H₂⟩ := h₁ X f p U G F hG hF β.inv
  obtain ⟨m₃, hm₃, hp₃, I₃⟩ := h₂ X f p U F F hF hF
  obtain ⟨m₄, hm₄, hp₄, I₄⟩ := h₂ X f p U G G hG hG
  obtain ⟨n, hn_def⟩ : ∃ n, n = m₁ * m₂ * m₃ * m₄ := ⟨_, rfl⟩
  have hn : 0 < n := by rw [hn_def]; positivity
  have hpn : ¬ (p : ℕ) ∣ n := by
    rw [hn_def]
    simp only [Nat.Prime.dvd_mul p.2]
    tauto
  obtain ⟨ψ₁, e₁⟩ := H₁ n hn (Dvd.intro (m₂ * m₃ * m₄) (by rw [hn_def]; ring)) hpn
  obtain ⟨ψ₂, e₂⟩ := H₂ n hn (Dvd.intro (m₁ * m₃ * m₄) (by rw [hn_def]; ring)) hpn
  have k₁ : ψ₁ ≫ ψ₂ = 𝟙 _ := I₃ n hn (Dvd.intro (m₁ * m₂ * m₄) (by rw [hn_def]; ring)) hpn _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₁, e₂, ← pullbackHomAlong_comp,
      Iso.hom_inv_id, pullbackHomAlong_id])
  have k₂ : ψ₂ ≫ ψ₁ = 𝟙 _ := I₄ n hn (Dvd.intro (m₁ * m₂ * m₃) (by rw [hn_def]; ring)) hpn _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₂, e₁, ← pullbackHomAlong_comp,
      Iso.inv_hom_id, pullbackHomAlong_id])
  refine ⟨n, hn, hpn, ⟨ψ₁, ψ₂, k₁, k₂⟩, Iso.ext ?_⟩
  rw [pullbackIsoAlong_hom, pullbackIsoAlong_hom]
  exact e₁
end SpreadIsoLoc
end GroundTheory.Heights₂.Heights.Model

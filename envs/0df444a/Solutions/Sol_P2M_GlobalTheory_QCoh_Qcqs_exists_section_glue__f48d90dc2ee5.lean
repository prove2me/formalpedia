-- Prove2me | solution 1 for P2M_GlobalTheory_QCoh_Qcqs_exists_section_glue__f48d90dc2ee5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:02.365881+00:00
-- url     : https://prove2.me/submissions/ba50de21-74b5-4401-8682-2ab93769b015

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Theorems.Thm_GlobalTheory_QCoh_res_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh GlobalTheory.QCoh.Qcqs
variable {X : Scheme.{u}} (F : X.Modules) {V₁ V₂ W : X.Opens}
namespace GlobalTheory.QCoh.Qcqs
theorem _root_.solution (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : W ≤ V₁ ⊔ V₂) (s₁ : Γ(F, V₁))
    (s₂ : Γ(F, V₂))
    (e : F.presheaf.map (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op s₁ =
      F.presheaf.map (homOfLE inf_le_right).op s₂) :
    ∃ s : Γ(F, W), F.presheaf.map (homOfLE h₁).op s = s₁ ∧
      F.presheaf.map (homOfLE h₂).op s = s₂ := by
  let 𝒰 : Bool → X.Opens := fun b ↦ Bool.rec V₁ V₂ b
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (C := Ab.{u}) ⟨F.presheaf, F.isSheaf⟩
    𝒰 W (fun b ↦ Bool.rec (homOfLE h₁) (homOfLE h₂) b)
    (h.trans (sup_le (le_iSup 𝒰 false) (le_iSup 𝒰 true)))
    (fun b ↦ Bool.rec s₁ s₂ b) (by
      rintro (_ | _) (_ | _)
      · rfl
      · exact e
      · have := congr(F.presheaf.map (homOfLE (inf_comm V₂ V₁).le).op $e)
        rw [res_res, res_res] at this
        exact this.symm
      · rfl)
  exact ⟨s, hs false, hs true⟩
end GlobalTheory.QCoh.Qcqs

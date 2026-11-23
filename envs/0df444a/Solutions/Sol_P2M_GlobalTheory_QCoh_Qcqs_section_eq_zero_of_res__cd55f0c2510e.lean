-- Prove2me | solution 1 for P2M_GlobalTheory_QCoh_Qcqs_section_eq_zero_of_res__cd55f0c2510e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:15.816968+00:00
-- url     : https://prove2.me/submissions/99e6c789-0923-44d1-9f4a-69ec07d1814b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated

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
theorem _root_.solution (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W) (h : W ≤ V₁ ⊔ V₂) (s : Γ(F, W))
    (e₁ : F.presheaf.map (homOfLE h₁).op s = 0) (e₂ : F.presheaf.map (homOfLE h₂).op s = 0) :
    s = 0 :=
  TopCat.Sheaf.eq_of_locally_eq₂ (C := Ab.{u}) ⟨F.presheaf, F.isSheaf⟩ (homOfLE h₁) (homOfLE h₂)
    h s 0 (e₁.trans (map_zero _).symm) (e₂.trans (map_zero _).symm)
end GlobalTheory.QCoh.Qcqs

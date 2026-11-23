-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.evaluation_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:39.988358+00:00
-- url     : https://prove2.me/submissions/9d695fe7-5b2f-4889-9d7d-cd0e1622947b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
variable {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ))
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {U V : S.Opens} (h : V ≤ U) (f : Γ(S, U)) (x : S) (hx : x ∈ V) :
    S.evaluation V x hx (S.presheaf.map (homOfLE h).op f) = S.evaluation U x (h hx) f := by
  have key : S.presheaf.map (homOfLE h).op ≫ S.evaluation V x hx = S.evaluation U x (h hx) := by
    simp only [Scheme.evaluation, TopCat.Presheaf.germ_res_assoc]
  rw [← key]
  rfl
end ReciprocityTheory.AnForm.R

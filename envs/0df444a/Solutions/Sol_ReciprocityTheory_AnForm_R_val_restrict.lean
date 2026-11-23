-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.val_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:09.854241+00:00
-- url     : https://prove2.me/submissions/9b39511b-d7c2-43bb-b226-cf14e2899b3b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Theorems.Thm_ReciprocityTheory_AnForm_R_evaluation_res

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
theorem _root_.solution {U V : S.Opens} (hVU : V ≤ U) (f : Γ(S, U)) (x : S) (hx : x ∈ V) :
    val s (S.presheaf.map (homOfLE hVU).op f) x hx = val s f x (hVU hx) := by
  unfold val
  rw [evaluation_res hVU f x hx]
end ReciprocityTheory.AnForm.R

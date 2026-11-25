-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.val_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:43:15.539801+00:00
-- url     : https://prove2.me/submissions/3a309d54-b90c-4839-8d3a-bb3ec2bb8a1b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Theorems.Thm_ReciprocityTheory_AnForm_R_valHom_spec
import Theorems.Thm_ReciprocityTheory_AnForm_R_valHom_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_evaluation_res
import Theorems.Thm_ReciprocityTheory_AnForm_R_constSec_res

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
theorem _root_.solution [LocallyOfFiniteType s] (U : S.Opens) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) (c : ℂ) : val s (constSec s U c) x hx = c := by
  unfold val
  rw [constSec_res s U c, evaluation_res le_top _ x hx, valHom_eq s x hc]
  exact DFunLike.congr_fun (valHom_spec s x hc) c
end ReciprocityTheory.AnForm.R

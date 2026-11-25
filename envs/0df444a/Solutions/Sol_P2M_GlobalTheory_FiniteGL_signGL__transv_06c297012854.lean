-- Prove2me | solution 1 for P2M_GlobalTheory_FiniteGL_signGL__transv_06c297012854
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:38.731028+00:00
-- url     : https://prove2.me/submissions/34958c42-36c2-47bc-a7b8-1c75c452a976

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Theorems.Thm_GlobalTheory_FiniteGL_genericLine_apply
import Theorems.Thm_GlobalTheory_FiniteGL_mirabInduced_apply
import Theorems.Thm_GlobalTheory_FiniteGL_restrictMirab_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FiniteGL.genericLine_apply
attribute [local simp] GlobalTheory.FiniteGL.mirabInduced_apply
attribute [local simp] GlobalTheory.FiniteGL.restrictMirab_apply

set_option autoImplicit false
noncomputable section
open Matrix Formalism.EigenvalueLevelCeiling Formalism.L2.Indef.Tree
open GlobalTheory GlobalTheory.FiniteGL
namespace GlobalTheory.FiniteGL
theorem _root_.solution : signGL₂ transvGL₂ = -1 := by
  have h : Equiv.Perm.sign (MulAction.toPerm transvGL₂ : Equiv.Perm (Fin 2 → ZMod 2)) = -1 := by
    decide
  simp [signGL₂, h]
end GlobalTheory.FiniteGL

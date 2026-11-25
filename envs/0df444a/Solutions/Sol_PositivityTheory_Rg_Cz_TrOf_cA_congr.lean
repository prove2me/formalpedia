-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TrOf.cA_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:42.836686+00:00
-- url     : https://prove2.me/submissions/ea3c0e78-9a28-440d-8c0a-0c6e9998cd6e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransOf
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TrOf
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
namespace PositivityTheory.Rg.Cz.TrOf
theorem _root_.solution {C C' : Type} [DecidableEq C] [DecidableEq C'] (c1 : Q → C) (c2 : Q → C')
    (h : ∀ p q, c1 p = c1 q ↔ c2 p = c2 q) (b : Q → Fin n) : (cA c1 b : TV n M Q →ₗ[ℂ] M) = cA c2 b := by
  have : colG c1 = colG c2 := by
    ext σ
    simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and, h]
  simp only [cA, this]
end PositivityTheory.Rg.Cz.TrOf

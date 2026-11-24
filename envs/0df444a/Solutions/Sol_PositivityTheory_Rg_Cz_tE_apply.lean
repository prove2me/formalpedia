-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.tE_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:28.195924+00:00
-- url     : https://prove2.me/submissions/e8dd3ed5-1ec0-4683-9d03-5b5d8af5e3ce

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_eAt_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply

set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
omit [Fintype P]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (S : Finset P) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) (I : P → Fin n) :
    tE S E a b f I = E a b (f I) + ∑ p ∈ S, if I p = a then f (Function.update I p b) else 0 := by
  simp only [tE, LinearMap.add_apply, Pi.add_apply, lift_apply, LinearMap.sum_apply, Finset.sum_apply, eAt_apply]
end PositivityTheory.Rg.Cz

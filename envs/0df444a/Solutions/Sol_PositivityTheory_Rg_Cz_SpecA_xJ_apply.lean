-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SpecA.xJ_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:45.476397+00:00
-- url     : https://prove2.me/submissions/b82c2a96-bdcd-44d0-8e14-8bb6550d9d20

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
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
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SpecA
variable {n : ℕ}
namespace PositivityTheory.Rg.Cz.SpecA
theorem _root_.solution {m : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m)
    (f : TV n M (Fin m)) (I : Fin m → Fin n) :
    xJ E j f I = ∑ a, E a (I j) (f (Function.update I j a)) +
      ∑ i ∈ Finset.univ.filter (· < j), f (I ∘ Equiv.swap i j) := by
  simp [xJ, Om, lift, eAt, pm, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (I j)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp
end PositivityTheory.Rg.Cz.SpecA

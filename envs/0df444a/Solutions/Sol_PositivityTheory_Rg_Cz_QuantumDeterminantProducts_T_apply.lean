-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QuantumDeterminantProducts.T_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:23.311963+00:00
-- url     : https://prove2.me/submissions/47ea5a11-6014-4c96-8c15-ff09e4e9cba0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
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
open PositivityTheory.Rg.Cz.QuantumDeterminantProducts
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.QuantumDeterminantProducts
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (k : Fin n) (h : TV n M (Fin n)) (I : Fin n → Fin n) :
    T E u k h I = ∑ a, Tm E (u - (k : ℂ)) a (I k) (h (Function.update I k a)) := by
  simp [T, Om, lift, eAt, Tm, Finset.sum_add_distrib, LinearMap.add_apply]
  congr 1
  · rw [Finset.sum_eq_single (I k)]
    · simp [sub_smul]
    · intro b _ hb
      simp [hb]
    · simp
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (I k)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
end PositivityTheory.Rg.Cz.QuantumDeterminantProducts

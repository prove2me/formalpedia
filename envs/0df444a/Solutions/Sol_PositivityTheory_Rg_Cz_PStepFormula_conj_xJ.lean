-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.PStepFormula.conj_xJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:36:27.205351+00:00
-- url     : https://prove2.me/submissions/b3d74a4a-2bb2-43a4-8011-729a2316d53c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_mul
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.PStepFormula
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.PStepFormula
theorem _root_.solution {N : ℕ} (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E)
    (σ : Equiv.Perm (Fin N)) (k : Fin N) :
    (pm σ * xJ E k * pm σ⁻¹ : Module.End ℂ (TV n M (Fin N))) =
      Om E (σ k) + ∑ i ∈ Finset.univ.filter (· < k), pm (Equiv.swap (σ i) (σ k)) := by
  have h4 := (hT n M (Fin N) E hE Finset.univ).2.2.2
  have hinv : (pm σ * pm σ⁻¹ : Module.End ℂ (TV n M (Fin N))) = 1 := by rw [← pm_mul, mul_inv_cancel, pm_one]
  rw [xJ, mul_add, add_mul, h4, mul_assoc, hinv, mul_one, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pm_mul, ← pm_mul, Equiv.swap_apply_apply]
end PositivityTheory.Rg.Cz.PStepFormula

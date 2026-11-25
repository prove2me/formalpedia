-- Prove2me | solution 1 for QmCapCommW.rep_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:15.586082+00:00
-- url     : https://prove2.me/submissions/3accc5f1-de79-4835-8ed6-07cb2134e362

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open QmCapCommW
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace QmCapCommW
theorem _root_.solution {ι : Type*} [Fintype ι] (c : ι → ℂ) {F : ι → Mx k r → E} {x : ι → SS k r i D E}
    (h : ∀ j, Rep (F j) (x j).1) : Rep (fun g => ∑ j, c j • F j g) (∑ j, c j • x j).1 := by
  unfold Rep at h ⊢
  intro g hg
  show ∑ j, c j • F j g = _
  rw [Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, h j g hg]
end QmCapCommW

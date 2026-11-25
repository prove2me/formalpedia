-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.inG_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:45.29052+00:00
-- url     : https://prove2.me/submissions/61243c78-695b-4211-9afa-03f829d52d18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_GlGeneratedTransvectionsDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Matrix
variable {A : Type} [CommRing A] {k : ℕ}
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution (d : Fin k → A) (hd : ∀ i, IsUnit (d i)) : InG (diagonal d) := by
  let g : GL (Fin k) A :=
    ⟨diagonal d, diagonal (fun i => ((hd i).unit⁻¹ : Aˣ)),
      by rw [diagonal_mul_diagonal]; convert diagonal_one with i; exact (hd i).mul_val_inv,
      by rw [diagonal_mul_diagonal]; convert diagonal_one with i; exact (hd i).val_inv_mul⟩
  exact ⟨g, Subgroup.subset_closure (Or.inr ⟨d, rfl⟩), rfl⟩
end PI.VolSemiDirect.W.Cj

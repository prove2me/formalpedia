-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.inG_transvection
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:35.649974+00:00
-- url     : https://prove2.me/submissions/2aeaefec-1439-4fb2-8565-89a79157b021

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
theorem _root_.solution {i j : Fin k} (hij : i ≠ j) (c : A) : InG (transvection i j c) := by
  let g : GL (Fin k) A :=
    ⟨transvection i j c, transvection i j (-c),
      by rw [transvection_mul_transvection_same i j hij, add_neg_cancel, transvection_zero],
      by rw [transvection_mul_transvection_same i j hij, neg_add_cancel, transvection_zero]⟩
  exact ⟨g, Subgroup.subset_closure (Or.inl ⟨i, j, c, hij, rfl⟩), rfl⟩
end PI.VolSemiDirect.W.Cj

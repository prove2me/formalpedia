-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FdegScale.fdegHC_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:33.114835+00:00
-- url     : https://prove2.me/submissions/3c18fbe1-f50e-41a1-b0e9-a349a7e8a504

import Definitions.Def_Formalism_PeriodIntegrals_FdegScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeScaling_FdegScaleOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FdegScale
open PI PI.UpqRep MeasureTheory Finset
open scoped InnerProductSpace
namespace PI.UnitaryGroupMassFormula.FdegScale
theorem _root_.solution {n : ℕ} {lam : Fin n → ℝ} (h : IsHCParam lam) : 0 < fdegHC lam := by
  unfold fdegHC
  apply div_pos
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr (h.1.injective.ne (ne_of_lt hab)))
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    have h' : (a : ℕ) < (b : ℕ) := hab
    rw [sub_pos]
    exact_mod_cast h'
end PI.UnitaryGroupMassFormula.FdegScale

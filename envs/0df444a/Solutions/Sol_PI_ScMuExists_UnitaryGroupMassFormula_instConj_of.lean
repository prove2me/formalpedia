-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.instConj_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:57:21.516004+00:00
-- url     : https://prove2.me/submissions/2be712be-edb0-4111-8a03-512b3d427933

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstLeftInvMuInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (hm : GenModOne) (hd : InstDecomp) (h4 : SubFacts) : InstConj := by
  intro I r e f z hfr N H hN hNset hHset h hh
  obtain ⟨N', H', hN', hH', -, -, hnorm'⟩ := h4 I r e f z
  have hmemN : ∀ x, x ∈ N ↔ x ∈ N' := fun x => by
    rw [← SetLike.mem_coe, hNset, ← hN', SetLike.mem_coe]
  have hmemH : ∀ x, x ∈ H ↔ x ∈ Hset I (frameSet I e f z) := fun x => by
    rw [← SetLike.mem_coe, hHset]
  have hmemH' : ∀ x, x ∈ H ↔ x ∈ H' := fun x => by
    rw [hmemH, ← hH', SetLike.mem_coe]
  refine hm I.Ginf N H hN ?_ ?_ h hh
  · intro g hg x hx
    exact (hmemN _).mpr (hnorm' g ((hmemH' g).mp hg) x ((hmemN x).mp hx))
  · intro g hg
    obtain ⟨k, hk, p, hp, σ, hσ, hkp, hσp, C, hC⟩ := hd I r e f z hfr g ((hmemH g).mp hg)
    exact ⟨k, (hmemH k).mpr hk, p, (hmemH p).mpr hp, σ, (hmemH σ).mpr hσ, hkp, hσp, C, hC⟩
end PI.ScMuExists.UnitaryGroupMassFormula

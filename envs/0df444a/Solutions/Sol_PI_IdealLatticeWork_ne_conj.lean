-- Prove2me | solution 1 for PI.IdealLatticeWork.ne_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:00.007536+00:00
-- url     : https://prove2.me/submissions/8d777314-f8a9-43f4-9be9-b1a86c37e3d5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdealLatticeBasis_IdealBasisAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdealLatticeBasis_OKArea

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.IdealLatticeWork
namespace PI.IdealLatticeWork
theorem _root_.solution {K : Type} [Field K] (φ : K →+* ℂ) (hnr : IsEmpty (K →+* ℝ)) :
    φ ≠ (starRingEnd ℂ).comp φ := by
  intro h
  have hr : NumberField.ComplexEmbedding.IsReal φ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := congrArg (fun f : K →+* ℂ => f x) h
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this.symm
  exact hnr.false hr.embedding
end PI.IdealLatticeWork

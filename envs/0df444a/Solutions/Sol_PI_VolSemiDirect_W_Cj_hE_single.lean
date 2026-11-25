-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.hE_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:00:06.262807+00:00
-- url     : https://prove2.me/submissions/929d57dd-f193-4dee-9d2e-434996d7f295

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_TraceGramNondegenerate

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x : Fin M → E) (j : Fin M) (c : E) :
    hE σ J x (Pi.single j c) = (∑ i, σ (x i) * J i j) * c := by
  simp [hE, Formalism.UG.hform, Pi.single_apply, Finset.sum_mul]
end PI.VolSemiDirect.W.Cj

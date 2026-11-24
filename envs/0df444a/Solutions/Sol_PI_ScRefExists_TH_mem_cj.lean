-- Prove2me | solution 1 for PI.ScRefExists.TH.mem_cj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:20:16.786687+00:00
-- url     : https://prove2.me/submissions/028540b8-7d03-4edf-8a44-4b60bfc4708a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.TH
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.TH
theorem _root_.solution (P : HeightOneSpectrum (𝓞 I.E)) (x : 𝓞 I.E) : x ∈ (cj I P).asIdeal ↔ sg I x ∈ P.asIdeal :=
  Ideal.mem_comap
end PI.ScRefExists.TH

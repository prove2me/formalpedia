-- Prove2me | solution 1 for PI.TwNormLat.W.qE_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:05.032803+00:00
-- url     : https://prove2.me/submissions/22503518-8658-4f45-bc10-90ef27efde8a

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwNormLat PI.TwNormLat.W
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwNormLat.W
theorem _root_.solution (hp : (Ideal.absNorm P.asIdeal).Prime) : qE P ≠ 0 := by
  show ((Ideal.absNorm P.asIdeal : ℕ) : E) ≠ 0
  exact Nat.cast_ne_zero.mpr hp.ne_zero
end PI.TwNormLat.W

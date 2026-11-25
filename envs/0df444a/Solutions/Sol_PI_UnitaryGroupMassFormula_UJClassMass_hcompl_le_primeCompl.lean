-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.hcompl_le_primeCompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:04.146584+00:00
-- url     : https://prove2.me/submissions/cf081f74-3829-4a91-a5f2-08230b9b6ec1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjSk
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (p : Ideal (𝓞 E)) [p.IsPrime] : hcompl (K := E) p ≤ p.primeCompl := by
  refine Submonoid.closure_le.2 fun s hs => ?_
  exact Ideal.mem_primeCompl_iff.2 hs.1
end PI.UnitaryGroupMassFormula.UJClassMass

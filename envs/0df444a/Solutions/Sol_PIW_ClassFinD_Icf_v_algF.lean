-- Prove2me | solution 1 for PIW.ClassFinD.Icf.v_algF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:29:08.491063+00:00
-- url     : https://prove2.me/submissions/33fb37a7-d328-4348-83f0-f994b210639c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_ExistsNeZeroMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD PIW.ClassFinD.Icf
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
namespace PIW.ClassFinD.Icf
theorem _root_.solution (f : F) (w : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) f) w) = w.valuation F f :=
  valuedAdicCompletion_eq_valuation' w f
end PIW.ClassFinD.Icf

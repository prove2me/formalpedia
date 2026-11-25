-- Prove2me | solution 1 for P2M_Formalism_IndefR_Fin_Four_smul_finsum__d1458f58bfdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:36.382868+00:00
-- url     : https://prove2.me/submissions/7352fc49-0d10-4fcf-8ec9-12dd492c1396

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {α M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (c : ℂ) {f : α → M} (hf : (Function.support f).Finite) :
    c • ∑ᶠ i, f i = ∑ᶠ i, c • f i := by
  exact map_finsum (DistribMulAction.toAddMonoidHom M c) hf
end Formalism.IndefR.Fin.Four

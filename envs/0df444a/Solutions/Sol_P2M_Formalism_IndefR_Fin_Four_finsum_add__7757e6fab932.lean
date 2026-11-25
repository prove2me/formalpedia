-- Prove2me | solution 1 for P2M_Formalism_IndefR_Fin_Four_finsum_add__7757e6fab932
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:35.395702+00:00
-- url     : https://prove2.me/submissions/07f83c17-8090-49b5-b5ec-845bb3e16f39

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
theorem _root_.solution {f g : α → M} (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    ∑ᶠ i, (f i + g i) = ∑ᶠ i, f i + ∑ᶠ i, g i := by
  exact finsum_add_distrib hf hg
end Formalism.IndefR.Fin.Four

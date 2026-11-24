-- Prove2me | solution 1 for P2M_Formalism_IndefR_Fin_Four_map_finsum__3c600d0ebc52
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:37.861771+00:00
-- url     : https://prove2.me/submissions/2f65862a-1903-4da9-87e1-ef2d00ac81e3

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
theorem _root_.solution (φ : M →ₗ[ℂ] M') {f : α → M} (hf : (Function.support f).Finite) :
    φ (∑ᶠ i, f i) = ∑ᶠ i, φ (f i) := by
  exact map_finsum φ hf
end Formalism.IndefR.Fin.Four

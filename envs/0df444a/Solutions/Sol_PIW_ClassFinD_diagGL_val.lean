-- Prove2me | solution 1 for PIW.ClassFinD.diagGL_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:15.021695+00:00
-- url     : https://prove2.me/submissions/7d849496-9b73-43bc-8157-03625b4c0aa5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD
open NumberField IsDedekindDomain
namespace PIW.ClassFinD
theorem _root_.solution {R : Type} [CommRing R] (n : ℕ) (τ : Fin n → Rˣ) :
    (diagGL n τ).val = Matrix.diagonal fun i => (τ i : R) := rfl
end PIW.ClassFinD

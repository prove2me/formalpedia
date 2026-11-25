-- Prove2me | solution 1 for PI.IsoFunVW.minY_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:53.841667+00:00
-- url     : https://prove2.me/submissions/a602f999-bdac-469f-9a84-423cabbaf154

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoFunV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_InstFintypeOE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MvPolynomial
noncomputable section
open PI PI.IsoFunVW
open PI.IsoFunV
namespace PI.IsoFunVW
theorem _root_.solution {Lt k k' : Type} [Fintype Lt] [CommRing k] [CommRing k'] (f : k →+* k')
    (N : ℕ) (nu : Lt → YoungDiagram) (J : ColChoice N nu) (y : Lt → Fin N → ℕ → k) :
    f (minY N nu J y) = minY N nu J (fun z a j => f (y z a j)) := by
  simp only [minY, map_prod, RingHom.map_det]
  rfl
end PI.IsoFunVW

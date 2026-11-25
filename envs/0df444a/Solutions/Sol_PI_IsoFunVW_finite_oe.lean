-- Prove2me | solution 1 for PI.IsoFunVW.finite_oe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:47:06.867072+00:00
-- url     : https://prove2.me/submissions/a5b9fcc7-ec94-4b3c-88ad-fb86cea7b7ac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Equiv
open PI PI.IsoFunVW
namespace PI.IsoFunVW
theorem _root_.solution (m n : ℕ) : Finite (Fin m ↪o Fin n) :=
  Finite.of_injective (fun e : Fin m ↪o Fin n => (e : Fin m → Fin n))
    (fun _ _ h => RelEmbedding.ext (congrFun h))
end PI.IsoFunVW

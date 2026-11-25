-- Prove2me | solution 1 for PI.IsoFunVW.prod_sum_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:05:15.221143+00:00
-- url     : https://prove2.me/submissions/90b689bb-b8f6-4700-a704-7e8d140b8c37

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
theorem _root_.solution {Lt : Type} [Fintype Lt] [DecidableEq Lt] {R : Type} [CommRing R] (N : ℕ)
    (nu : Lt → YoungDiagram)
    (F : ∀ (z : Lt) (c : Fin ((nu z).rowLen 0)), (Fin ((nu z).colLen c) ↪o Fin N) → R) :
    ∏ z, ∏ c, ∑ Jc, F z c Jc = ∑ J : ColChoice N nu, ∏ z, ∏ c, F z c (J z c) := by
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)
end PI.IsoFunVW

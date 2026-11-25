-- Prove2me | solution 1 for PI.IsoFunVW.AOp_hv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:18:29.779033+00:00
-- url     : https://prove2.me/submissions/81876db1-f761-4ab0-a85e-6e644ac4c4d5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoFunV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_InstFintypeOE
import Theorems.Thm_PI_IsoFunVW_applyAt0_eq
import Theorems.Thm_PI_IsoFunVW_key_id

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
theorem _root_.solution {Lt T : Type} [Fintype Lt] [DecidableEq Lt] [Fintype T] (tp : Lt → T) {N N' : ℕ}
    (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ) (x : Lt → Fin N → ℕ → ℂ) :
    AOp tp nu s Θ (hvC N nu x) = fun I => linW (wTh Θ) (minY N' nu I (yfr tp s x)) := by
  funext I
  rw [AOp_eq, ← key_id, map_sum]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [applyAt0_eq, mul_comm (PIJ tp nu s I J), ← MvPolynomial.smul_eq_C_mul, map_smul,
    smul_eq_mul, mul_comm]
  rfl
end PI.IsoFunVW

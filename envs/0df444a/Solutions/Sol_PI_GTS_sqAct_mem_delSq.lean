-- Prove2me | solution 1 for PI.GTS.sqAct_mem_delSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:24.460934+00:00
-- url     : https://prove2.me/submissions/bba10bb8-d7db-4592-bad6-a1ec8c7e7d0f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTScale
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitPowerNormScale_NormUnitsZpowSq
import Theorems.Thm_Formalism_UG_P_wlocal_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GTS
open Formalism.BasicNotions MvPolynomial
namespace PI.GTS
theorem _root_.solution (N : ℕ) (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ delSq ℂ N lam) : sqAct ℂ N lam g f ∈ delSq ℂ N lam := by
  unfold sqAct delSq at *
  refine Submodule.smul_mem _ _ ?_
  exact Formalism.UG.P.wlocal_main le_rfl lam.natW N 0 (zero_add N) ((g : Matrix (Fin N) (Fin N) ℂ).transpose)
    ((g⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose
    (by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one])
    (fun i j hj => absurd hj (Nat.not_lt_zero _)) f hf
end PI.GTS

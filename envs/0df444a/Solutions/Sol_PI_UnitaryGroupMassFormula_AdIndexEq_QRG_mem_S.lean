-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.QRG.mem_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:25.398904+00:00
-- url     : https://prove2.me/submissions/1058a9ea-5d41-4cfd-8200-124f3d5a4c16

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.QRG
open Matrix Formalism.UG
variable {K : Type} [Field K] {n : ℕ}
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
namespace PI.UnitaryGroupMassFormula.AdIndexEq.QRG
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (hdet : J.det ≠ 0) (h2 : (2 : K) ≠ 0)
    (g : UJ σ J) : g ∈ S σ J := by exact main σ J hσ hJ hdet h2 n 0 Fin.elim0 (by simp) (fun i => i.elim0) (fun i => i.elim0) g (fun i => i.elim0)
end PI.UnitaryGroupMassFormula.AdIndexEq.QRG

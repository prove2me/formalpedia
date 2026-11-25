-- Prove2me | solution 1 for PI.WMI.pe_unitary_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:50.731625+00:00
-- url     : https://prove2.me/submissions/d298045f-0b44-4f51-b2da-42a80ca17778

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_PolyExtLem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
namespace PI.WMI
theorem _root_.solution {N : ℕ} (u : Matrix (Fin N) (Fin N) ℂ) (hu : uᴴ * u = 1) : u ∈ Kset (allPos N) := by
  have hJ : Jm (allPos N) = 1 := by
    unfold Jm allPos
    simp
  refine ⟨?_, by rw [hJ]; simp⟩
  rw [Matrix.mem_unitaryGroup_iff']
  exact hu
end PI.WMI

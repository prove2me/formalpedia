-- Prove2me | solution 1 for PI.ExpIntWProof.norm_p
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:43.69291+00:00
-- url     : https://prove2.me/submissions/b76c5f57-e30d-4ad8-90b1-32948c90f5b0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof
open PI
namespace PI.ExpIntWProof
theorem _root_.solution (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have e : (p : ℂ_[p]) = ((algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) := by
    simp
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
  first
  | exact Padic.norm_p
  | simp [Padic.norm_p]
end PI.ExpIntWProof

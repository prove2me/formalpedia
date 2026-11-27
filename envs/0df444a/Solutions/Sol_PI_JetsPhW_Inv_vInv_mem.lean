-- Prove2me | solution 1 for PI.JetsPhW.Inv.vInv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:15:42.765088+00:00
-- url     : https://prove2.me/submissions/96b8329f-85a6-4b38-9adb-6b9f131fcee9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InverseOmegaHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_InvOmega
import Theorems.Thm_PI_JetsPhW_Inv_wq_mem
import Theorems.Thm_PI_JetsPhW_Inv_X_mem_serS
import Theorems.Thm_PI_JetsPhW_Inv_C_mem_serS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.JetsPhW PI.JetsPhW.Inv
variable {p : ℕ} [Fact p.Prime]
namespace PI.JetsPhW.Inv
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : IsIntP W.a₁) (h2 : IsIntP W.a₂) (h3 : IsIntP W.a₃) (h4 : IsIntP W.a₄) (h6 : IsIntP W.a₆)
    (h : IsWq W wq) : vInv W wq ∈ serS (intS p) := by
  have hw : wq ∈ serS (intS p) := wq_mem (S := intS p) h1 h2 h3 h4 h6 h
  have hX := X_mem_serS (intS p)
  have c1 := C_mem_serS (S := intS p) h1
  have c2 := C_mem_serS (S := intS p) h2
  have c3 := C_mem_serS (S := intS p) h3
  have c4 := C_mem_serS (S := intS p) h4
  have c6 := C_mem_serS (S := intS p) h6
  have t2 : (2 : PowerSeries ℂ_[p]) ∈ serS (intS p) := by
    exact_mod_cast natCast_mem (serS (intS p)) 2
  have t3 : (3 : PowerSeries ℂ_[p]) ∈ serS (intS p) := by
    exact_mod_cast natCast_mem (serS (intS p)) 3
  have hw3 : PowerSeries.X ^ 3 * wq ∈ serS (intS p) := Subring.mul_mem _ (Subring.pow_mem _ hX 3) hw
  simp only [vInv]
  refine Subring.sub_mem _ (Subring.one_mem _) ?_
  refine Subring.add_mem _ (Subring.add_mem _ (Subring.add_mem _ (Subring.add_mem _ ?_ ?_) ?_) ?_) ?_
  · exact Subring.mul_mem _ c1 hX
  · exact Subring.mul_mem _ c2 (Subring.pow_mem _ hX 2)
  · exact Subring.mul_mem _ (Subring.mul_mem _ t2 c3) hw3
  · exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ t2 c4) hX) hw3
  · exact Subring.mul_mem _ (Subring.mul_mem _ t3 c6) (Subring.pow_mem _ hw3 2)
end PI.JetsPhW.Inv

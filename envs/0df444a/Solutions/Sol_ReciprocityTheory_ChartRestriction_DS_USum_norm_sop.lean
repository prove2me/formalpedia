-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.USum.norm_sop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:14:24.926243+00:00
-- url     : https://prove2.me/submissions/ac3a6647-b3e8-491c-a633-0948c40a84cd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix WithLp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.USum
variable {n : ℕ}
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
namespace ReciprocityTheory.ChartRestriction.DS.USum
theorem _root_.solution {A : H₁ →L[ℂ] H₁} {B : H₂ →L[ℂ] H₂} (hA : ∀ v, ‖A v‖ = ‖v‖)
    (hB : ∀ v, ‖B v‖ = ‖v‖) (x : WithLp 2 (H₁ × H₂)) : ‖sop A B x‖ = ‖x‖ := by
  rw [WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
  show √(‖A (ofLp x).1‖ ^ 2 + ‖B (ofLp x).2‖ ^ 2) = √(‖(ofLp x).1‖ ^ 2 + ‖(ofLp x).2‖ ^ 2)
  rw [hA, hB]
end ReciprocityTheory.ChartRestriction.DS.USum

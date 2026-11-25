-- Prove2me | solution 1 for PI.FJMP.noVar_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:40.561511+00:00
-- url     : https://prove2.me/submissions/f5ff3a0c-0127-4e5c-b50c-2cd9bafec3a4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM
variable {σ : Type*}
namespace PI.FJMP
theorem _root_.solution {P : MvPolynomial σ ℂ} {v : σ} (h : NoVar P v) (u : σ) : NoVar (pderiv u P) v := by
  classical
  intro f hf
  rw [P.as_sum, map_sum] at hf
  obtain ⟨e, he, hfe⟩ := Finset.mem_biUnion.mp (support_sum hf)
  rw [pderiv_monomial] at hfe
  obtain rfl := Finset.mem_singleton.mp (support_monomial_subset hfe)
  simp [h e he]
end PI.FJMP

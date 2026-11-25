-- Prove2me | solution 1 for PI.ProdFormulaE.TrIntP.norm_le_one_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:05:49.942802+00:00
-- url     : https://prove2.me/submissions/d5dc08b9-eb13-4336-9f10-231e2c2df2c0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormTraceLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ProdFormulaE PI.ProdFormulaE.TrIntP
namespace PI.ProdFormulaE.TrIntP
theorem _root_.solution {ℓ : ℕ} [Fact ℓ.Prime] {t : ℚ_[ℓ]} (ht : IsIntegral ℤ t) :
    ‖t‖ ≤ 1 := by
  have ht' : IsIntegral ℤ_[ℓ] t := ht.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 ht'
  rw [← hy]
  exact y.norm_le_one
end PI.ProdFormulaE.TrIntP

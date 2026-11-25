-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_F_Homog_wEta_basis__9ee8d3c65504
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:53:00.596356+00:00
-- url     : https://prove2.me/submissions/a0794bee-e21a-4577-a7c0-1149fe2a093f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Homog
variable (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)
namespace Formalism.L2.Th1.F.Homog
theorem _root_.solution (L : PeriodPair) : wEta L L.ω₂ = 2 * wZeta L (L.ω₂ / 2) := by
  have hb : L.basis 1 = L.ω₂ := by
    first
      | exact L.basis_one
      | simp [PeriodPair.basis]
  have h1 := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 1
  rw [hb] at h1
  simpa [wEta] using h1
end Formalism.L2.Th1.F.Homog

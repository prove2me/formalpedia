-- Prove2me | solution 1 for PI.IsoFunVW.isoFunV_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:23.721809+00:00
-- url     : https://prove2.me/submissions/23b6739a-6b58-48e8-a21d-89680f991a55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoFunV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_InstFintypeOE
import Theorems.Thm_PI_IsoFunVW_AOp_hv
import Theorems.Thm_PI_IsoFunVW_mem_Vnu_poly

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
theorem _root_.solution : IsoFunV := by
  intro Lt T _ _ _ tp N N' nu s Θ φ hφ
  have hle : Vnu N nu ≤ (Vnu N' nu).comap (AOpLin tp nu s Θ) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    show AOp tp nu s Θ (hvC N nu x) ∈ Vnu N' nu
    rw [AOp_hv]
    exact mem_Vnu_poly N' nu _ _
  exact hle hφ
end PI.IsoFunVW

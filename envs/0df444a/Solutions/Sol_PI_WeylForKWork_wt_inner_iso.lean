-- Prove2me | solution 1 for PI.WeylForKWork.wt_inner_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:15:34.536001+00:00
-- url     : https://prove2.me/submissions/c6fdb413-46d3-4198-9579-d801efb2a71d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
import Definitions.Def_Lemmata_GeneralBFactLeftVariant_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Weights

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix
open scoped InnerProductSpace
namespace PI.WeylForKWork
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (x y : H) : ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(T : H →ₗ[ℂ] H), hT⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y
end PI.WeylForKWork

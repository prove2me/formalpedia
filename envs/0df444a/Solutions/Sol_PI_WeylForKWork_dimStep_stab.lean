-- Prove2me | solution 1 for PI.WeylForKWork.dimStep_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:13:20.528348+00:00
-- url     : https://prove2.me/submissions/9fcc8dff-0381-454e-b8bd-f3e84254e33f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStep

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
open PI PI.UpqRep Matrix DimensionInduction
namespace PI.WeylForKWork
theorem _root_.solution {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {W : Submodule ℂ H} :
    IsKStableOn (allPos n) σ W ↔ Stab (fun g : Kset (allPos n) => σ g.1) W :=
  ⟨fun h g v hv => h g.1 g.2 v hv, fun h g hg v hv => h ⟨g, hg⟩ v hv⟩
end PI.WeylForKWork

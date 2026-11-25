-- Prove2me | solution 1 for PI.WeylForKWork.isUnitaryRepOn_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:34.407722+00:00
-- url     : https://prove2.me/submissions/cf07547e-7386-4ae6-aef6-dedffbeb5d3d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks

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
variable {N : ℕ}
namespace PI.WeylForKWork
theorem _root_.solution {n : ℕ} (ε : Fin N → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (ι : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin N) (Fin N) ℂ)
    (h1 : ι 1 = 1) (hmul : ∀ a b, ι (a * b) = ι a * ι b) (hmem : ∀ h ∈ Kset (allPos n), ι h ∈ Kset ε)
    (hcont : Continuous ι) (hσ : IsURepOn (Kset ε) σ) : IsURepOn (Kset (allPos n)) (fun h => σ (ι h)) := by
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => hσ.2.1 (ι g) (hmem g hg) v, fun v => ?_⟩
  · show σ (ι 1) = 1
    rw [h1]
    exact hσ.1.1
  · show σ (ι (a * b)) = (σ (ι a)).comp (σ (ι b))
    rw [hmul]
    exact hσ.1.2 _ (hmem a ha) _ (hmem b hb)
  · exact (hσ.2.2 v).comp hcont.continuousOn hmem
end PI.WeylForKWork

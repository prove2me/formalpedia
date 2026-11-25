-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.vol_arc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:26.357256+00:00
-- url     : https://prove2.me/submissions/9a08c126-f0d5-45c5-91b5-fc6cdb3530ba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_ContinuousLmulM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology Set Real
open scoped ENNReal
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution {ρ : ℝ} (hρ : ρ ≤ π) :
    volume (((↑) : ℝ → AddCircle (2 * π)) '' Ioo (-ρ) ρ) = ENNReal.ofReal (2 * ρ) := by
  have hopen : IsOpen (((↑) : ℝ → AddCircle (2 * π)) '' Ioo (-ρ) ρ) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  rw [AddCircle.add_projection_respects_measure (2 * π) (-π) hopen.measurableSet]
  have hsub : Ioo (-ρ) ρ ⊆ Ioc (-π) (-π + 2 * π) := by
    intro θ hθ; constructor <;> linarith [hθ.1, hθ.2]
  have : ((↑) : ℝ → AddCircle (2 * π)) ⁻¹' (((↑) : ℝ → AddCircle (2 * π)) '' Ioo (-ρ) ρ) ∩
      Ioc (-π) (-π + 2 * π) = Ioo (-ρ) ρ := by
    ext θ
    constructor
    · rintro ⟨⟨θ', h1, he⟩, h3⟩
      rw [AddCircle.coe_eq_coe_iff_of_mem_Ioc (hsub h1) h3] at he
      exact he ▸ h1
    · intro h
      exact ⟨⟨θ, h, rfl⟩, hsub h⟩
  rw [this, Real.volume_Ioo]
  congr 1; ring
end PI.ExistsGaugeMeasureForEachRank.W

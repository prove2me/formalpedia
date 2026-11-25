-- Prove2me | solution 1 for PIW.HCFdeg.unimod_of_modChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:20:19.551831+00:00
-- url     : https://prove2.me/submissions/5e0f3dc8-b9fb-40d1-8cdd-a0bf6238bc30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory PI.UpqRep Matrix
open scoped MatrixOrder NNReal ENNReal ComplexOrder Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PIW.HCFdeg
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular]
    (h : ∀ g : G, Measure.modularCharacter g = 1) :
    μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  have hR : μ.IsMulRightInvariant :=
    ⟨fun g => by
      rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g]
      have : Measure.modularCharacterFun g = 1 := h g
      rw [this, one_smul]⟩
  refine ⟨hR, ⟨?_⟩⟩
  let c : ℝ≥0∞ := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul_of_innerRegular μ.inv μ
  have h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]
end PIW.HCFdeg

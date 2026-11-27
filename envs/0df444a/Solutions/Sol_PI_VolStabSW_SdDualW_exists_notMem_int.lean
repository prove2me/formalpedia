-- Prove2me | solution 1 for PI.VolStabSW.SdDualW.exists_notMem_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:17:49.075442+00:00
-- url     : https://prove2.me/submissions/e3bccb92-2220-4947-a5cc-96f5a0d22bb7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW.SdDualW
theorem _root_.solution : ∃ c : Fv F v, c ∉ v.adicCompletionIntegers F := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨((π⁻¹ : F) : Fv F v), ?_⟩
  rw [HeightOneSpectrum.notMem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ]
  simp only [← WithZero.exp_neg, neg_neg]
  rw [← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.2 one_pos
end PI.VolStabSW.SdDualW

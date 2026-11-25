-- Prove2me | solution 1 for PI.VolStabW.TopoMeas.measurable_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:12.664016+00:00
-- url     : https://prove2.me/submissions/4b551087-3921-4c5f-8015-1fff88cfb7c7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_MeasOrbSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMeas
import Theorems.Thm_PI_VolStabW_TopoMeas_measurable_finprod
import Theorems.Thm_PI_VolStabW_TopoMeas_continuous_projV
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_continuous_projFin
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_continuous_projInf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.TopoMeas
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Filter Topology PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
namespace PI.VolStabW.TopoMeas
theorem _root_.solution {M a : ℕ} (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ) (hΦ : IsAdm F E Φ) :
    Measurable Φ := by
  obtain ⟨d, b, Φinf, Φf, Φv, hc, -, ⟨hSB, -, hprod⟩, hIF⟩ := hΦ
  have e1 : Φ = fun X => Φinf (projInf X) * Φf (projFin X) := funext hIF
  have e2 : Φf = fun Y => ∏ᶠ v, Φv v (projV v Y) := funext hprod
  have hf : Measurable Φf := by
    rw [e2]
    exact measurable_finprod _ fun v =>
      ((hSB v).1.continuous.comp (continuous_projV b v)).measurable
  rw [e1]
  exact ((hc.comp (PI.VolStabW.PositiveNearLattice.continuous_projInf b)).measurable).mul
    (hf.comp (PI.VolStabW.PositiveNearLattice.continuous_projFin b).measurable)
end PI.VolStabW.TopoMeas

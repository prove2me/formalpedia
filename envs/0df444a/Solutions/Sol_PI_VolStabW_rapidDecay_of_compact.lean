-- Prove2me | solution 1 for PI.VolStabW.rapidDecay_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:42.20077+00:00
-- url     : https://prove2.me/submissions/90cb3778-c3d4-4220-8f17-3bad77ca6406

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SWeqOm
import Theorems.Thm_PI_VolStabW_continuous_sizeTup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace PI.VolStabW
theorem _root_.solution {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    RapidDecay b Φ := by
  intro N
  have hcont : Continuous fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N :=
    (continuous_norm.comp hc).mul ((continuous_const.add (continuous_sizeTup b)).pow N)
  have hsupp : HasCompactSupport fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N :=
    hs.norm.mul_right
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  exact ⟨C, fun X => le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hC X)⟩
end PI.VolStabW

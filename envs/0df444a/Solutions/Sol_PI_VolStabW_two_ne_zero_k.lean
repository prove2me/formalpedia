-- Prove2me | solution 1 for PI.VolStabW.two_ne_zero_k
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:13:27.018305+00:00
-- url     : https://prove2.me/submissions/fda286e4-c2fd-4d4f-822c-d6fed490a463

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCnt
import Theorems.Thm_PI_VolStabW_v_iO_lt_iff


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
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {σ : E →ₐ[F] E} (A : AntiB F E σ)
namespace PI.VolStabW
theorem _root_.solution (h2 : Valued.v (algebraMap F (Fv F v) 2) = 1) :
    (2 : 𝓞 F ⧸ v.asIdeal) ≠ 0 := by
  intro h
  have h' : Ideal.Quotient.mk v.asIdeal (2 : 𝓞 F) = 0 := by rw [map_ofNat]; exact h
  rw [Ideal.Quotient.eq_zero_iff_mem, ← v_iO_lt_iff] at h'
  simp only [iO, map_ofNat] at h' h2
  rw [h2] at h'
  exact lt_irrefl _ h'
end PI.VolStabW

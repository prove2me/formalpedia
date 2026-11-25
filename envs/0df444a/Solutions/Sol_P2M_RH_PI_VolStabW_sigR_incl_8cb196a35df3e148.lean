-- Prove2me | solution 1 for P2M_RH_PI_VolStabW_sigR_incl_8cb196a35df3e148
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:07:37.027378+00:00
-- url     : https://prove2.me/submissions/ed4d0679-4cb1-4825-86ee-df5d1579f297

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCnt

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
theorem _root_.solution (e : E) : sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := by
  show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ ((1 : Fv F v) ⊗ₜ e) =
    (1 : Fv F v) ⊗ₜ σ e
  simp [Algebra.TensorProduct.map_tmul]
end PI.VolStabW

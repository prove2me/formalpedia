-- Prove2me | solution 1 for PI.VolStabSW.SdUniqW.singleV_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:11:27.453875+00:00
-- url     : https://prove2.me/submissions/06303f14-fbbc-4374-9925-4461f5ee156c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq

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
open PI.VolStabSW.SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
open Classical
namespace PI.VolStabSW.SdUniqW
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    singleV F v (r + s) = singleV F v r + singleV F v s := by
  apply Subtype.ext
  exact Pi.single_add v r s
end PI.VolStabSW.SdUniqW

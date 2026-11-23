-- Prove2me | solution 1 for PI.DiffGenLoc.UnitaryGroupMassFormula.val_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:13.54062+00:00
-- url     : https://prove2.me/submissions/ce5859ae-d888-4506-aa48-2a8e9aee32ec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiffGenLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDifferentGenerators_DiffExistsMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DiffGenLoc PI.DiffGenLoc.UnitaryGroupMassFormula
open NumberField IsDedekindDomain WithZero
namespace PI.DiffGenLoc.UnitaryGroupMassFormula
theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    Valued.v (algebraMap F (Fv F v) (x : F)) = v.intValuation x := by
  first
    | exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)).trans
        (HeightOneSpectrum.valuation_of_algebraMap v x)
    | (rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]; rfl)
    | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
    | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap]
    | (rw [HeightOneSpectrum.adicCompletion.algebraMap_eq_coe, HeightOneSpectrum.valuedAdicCompletion_eq_valuation,
        HeightOneSpectrum.valuation_of_algebraMap])
end PI.DiffGenLoc.UnitaryGroupMassFormula

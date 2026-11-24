-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.Gl.val_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:38:17.350854+00:00
-- url     : https://prove2.me/submissions/f6e79a92-c967-4db6-966d-692deb51d648

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Theorems.Thm_Formalism_UG_P_levelaf_valued_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.Gl
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists PI.UnitaryGroupMassFormula.AdIndexEq
namespace PI.UnitaryGroupMassFormula.ScXuExists.Gl
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (h : (N : 𝓞 F) ∉ v.asIdeal) : Valued.v ((N : v.adicCompletion F)) = 1 := by
  rw [← map_natCast (algebraMap F (v.adicCompletion F)) N, Formalism.UG.P.levelaf_valued_algebraMap,
    ← map_natCast (algebraMap (𝓞 F) F) N, HeightOneSpectrum.valuation_eq_one_iff_notMem]
  exact h
end PI.UnitaryGroupMassFormula.ScXuExists.Gl

-- Prove2me | solution 1 for PIW.AdelClassFin.DictRing.val_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:23:08.311707+00:00
-- url     : https://prove2.me/submissions/4e1034db-cafc-4def-b987-3a81344c62f1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_DedekindLFunctions
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Theorems.Thm_PIW_AdelClassFin_DictRing_val_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictRing
variable {F : Type} [Field F] [NumberField F]
namespace PIW.AdelClassFin.DictRing
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = v.valuation F (algebraMap (𝓞 F) F r) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), val_alg]
end PIW.AdelClassFin.DictRing

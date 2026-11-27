-- Prove2me | solution 1 for PI.InvTopW.continuous_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:17:04.272926+00:00
-- url     : https://prove2.me/submissions/72588416-c20f-4579-b638-55e80a32abc2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LinearIndependentOneBeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
variable (I : AutInst)
namespace PI.InvTopW
theorem _root_.solution (k : Fin 2) : Continuous (coord I k) := by
  haveI : Module.Finite (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) := Module.Finite.of_basis (basisT I)
  exact IsModuleTopology.continuous_of_linearMap (coord I k)
end PI.InvTopW

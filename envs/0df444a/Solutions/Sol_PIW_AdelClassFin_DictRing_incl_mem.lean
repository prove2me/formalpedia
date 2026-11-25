-- Prove2me | solution 1 for PIW.AdelClassFin.DictRing.incl_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:20:38.420357+00:00
-- url     : https://prove2.me/submissions/ad550964-93a1-436f-9a4e-c69efad9edda

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_DedekindLFunctions
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing

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
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace PIW.AdelClassFin.DictRing
theorem _root_.solution (a : 𝓞 E) : Formalism.UG.inclE (F := F) (Af F) (a : E) ∈ IntAf F E :=
  Subring.subset_closure (Or.inl ⟨⟨(a : E), a, rfl⟩, rfl⟩)
end PIW.AdelClassFin.DictRing

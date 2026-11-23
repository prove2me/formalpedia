-- Prove2me | solution 1 for PI.Dv.ProjGramW.algebraMap_ne_zero_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:21.543902+00:00
-- url     : https://prove2.me/submissions/d398cb9d-e3cb-456b-8365-cc07befd4ee5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  intro h0
  apply hs
  have : s = 0 := (IsFractionRing.injective (𝓞 K) K) (h0.trans (map_zero _).symm)
  rw [this]
  exact w.asIdeal.zero_mem
end PI.Dv.ProjGramW

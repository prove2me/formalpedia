-- Prove2me | solution 1 for PI.Dv.ProjGramW.sum_smul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:22.395125+00:00
-- url     : https://prove2.me/submissions/4a7845fe-a043-4d7b-939a-b87608199df4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet

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
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution {d : ℕ} (r : Fin d → 𝓞 K) (u : Fin d → (Fin d →₀ K)) (i : Fin d) :
    (∑ k, r k • u k) i = ∑ k, r k • u k i := by
  rw [Finsupp.finsetSum_apply]
  rfl
end PI.Dv.ProjGramW

-- Prove2me | solution 1 for PI.KLW.Ind.unitary_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:03.423029+00:00
-- url     : https://prove2.me/submissions/b307b008-cc0e-4c34-ac2e-615ed181819d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.Ind
open PI.KLW
namespace PI.KLW.Ind
theorem _root_.solution {K : Type} [Field K] {c : K →+* K} {ι : Type} [Fintype ι]
    {u : (ι → K) ≃ₗ[K] (ι → K)} (hu : IsUnitary c u) : IsUnitary c u.symm := fun v w => by
  rw [← hu (u.symm v) (u.symm w), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
end PI.KLW.Ind

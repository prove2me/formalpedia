-- Prove2me | solution 1 for PI.DvRows.mem_comap_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:36:22.33249+00:00
-- url     : https://prove2.me/submissions/2a4bc75a-7338-443f-905f-19d262c45c84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows
theorem _root_.solution (I : Ideal (𝓞 K)) (n : ℕ) (a : 𝓞 K) :
    a ∈ (I.comap (starO K)) ^ n ↔ starO K a ∈ I ^ n := by
  have e : (I.comap (starO K)) ^ n = (I ^ n).comap (starO K) := by
    rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]
  rw [e, Ideal.mem_comap]
end PI.DvRows

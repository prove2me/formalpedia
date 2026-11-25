-- Prove2me | solution 1 for PI.OmLocU.CntFF.exists_tr_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:01:05.463866+00:00
-- url     : https://prove2.me/submissions/2229572a-6ff1-462f-a9de-69eab42aff2b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_FFInert2Holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmLocU PI.OmLocU.CntFF
open Module PI.VolStabSW PI.VolStabSW.FFHS
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.OmLocU.CntFF
theorem _root_.solution {k K : Type} [Field k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (hne : σ ≠ AlgEquiv.refl) : ∃ z : K, z + (σ : K →+* K) z ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hne
  ext z
  have h1 : (1 : K) + 1 = 0 := by
    have h1' := hall 1
    change (1 : K) + σ 1 = 0 at h1'
    rwa [map_one] at h1'
  have h2' : z + σ z = 0 := hall z
  show σ z = z
  linear_combination h2' - z * h1
end PI.OmLocU.CntFF
